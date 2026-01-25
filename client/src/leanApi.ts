/**
 * Utility for making independent RPC calls to the Lean server via lean4monaco.
 * This manages a separate virtual document for Blockly code, independent of the Monaco editor.
 */
import { LeanMonaco } from 'lean4monaco';
import type { InteractiveGoals, LeanFileProgressProcessingInfo } from '@leanprover/infoview-api';
import type { RpcConnected } from '@leanprover/infoview-api';

// Virtual document for Blockly code
const BLOCKLY_DOC_URI = 'file:///blockly/Blockly.lean';

// State for the Blockly document
let documentVersion = 0;
let documentOpen = false;
let currentSessionId: string | null = null;
let lastDocumentContent: string | null = null;

// Request tracking for staleness detection
let currentRequestId = 0;

// For tracking when processing is complete
let processingResolvers: Array<() => void> = [];

/**
 * Get the current request ID. Use this to check if a response is stale.
 */
export function getCurrentRequestId(): number {
  return currentRequestId;
}

/**
 * Get the active LeanClient from lean4monaco.
 * TODO: this is a bad use of global state, I should be passing in the LSP client from the outside.
 */
function getActiveClient() {
  const leanMonaco = LeanMonaco.activeInstance;
  if (!leanMonaco) {
    console.warn('[leanApi] No active LeanMonaco instance');
    return null;
  }

  const clientProvider = leanMonaco.clientProvider;
  if (!clientProvider) {
    console.warn('[leanApi] No clientProvider available');
    return null;
  }

  const client = clientProvider.getActiveClient();
  if (!client) {
    console.warn('[leanApi] No active client');
    return null;
  }

  return client;
}

/**
 * Set up progress listener to track when processing is complete.
 */
let progressListenerSetup = false;
function ensureProgressListener() {
  if (progressListenerSetup) return;

  const client = getActiveClient();
  if (!client) return;

  client.progressChanged((event: [string, LeanFileProgressProcessingInfo[]]) => {
    const [uri, processing] = event;
    if (uri === BLOCKLY_DOC_URI && processing.length === 0) {
      // Processing complete for our document
      console.log('[leanApi] Processing complete for Blockly document');
      const resolvers = processingResolvers;
      processingResolvers = [];
      resolvers.forEach(resolve => resolve());
    }
  });

  progressListenerSetup = true;
  console.log('[leanApi] Progress listener set up');
}

/**
 * Wait for the Blockly document to finish processing.
 */
function waitForProcessingComplete(): Promise<void> {
  return new Promise(resolve => {
    processingResolvers.push(resolve);
  });
}

/**
 * Open or update the virtual Blockly document on the Lean server.
 * Returns true if the document was actually updated, false if skipped or failed.
 */
async function updateBlocklyDocument(code: string): Promise<{ updated: boolean; changed: boolean }> {
  const client = getActiveClient();
  if (!client) return { updated: false, changed: false };

  // Check if content actually changed
  if (documentOpen && code === lastDocumentContent) {
    console.log('[leanApi] Document content unchanged, skipping update');
    return { updated: true, changed: false };
  }

  ensureProgressListener();

  try {
    if (!documentOpen) {
      // Open the document for the first time
      await client.sendNotification('textDocument/didOpen', {
        textDocument: {
          uri: BLOCKLY_DOC_URI,
          languageId: 'lean4',
          version: ++documentVersion,
          text: code,
        },
      });
      documentOpen = true;
      lastDocumentContent = code;
      console.log('[leanApi] Opened Blockly document');
    } else {
      // Update existing document
      await client.sendNotification('textDocument/didChange', {
        textDocument: {
          uri: BLOCKLY_DOC_URI,
          version: ++documentVersion,
        },
        contentChanges: [{ text: code }],
      });
      lastDocumentContent = code;
      // Invalidate RPC session - it's tied to the document state
      currentSessionId = null;
      console.log('[leanApi] Updated Blockly document, version:', documentVersion, '(session invalidated)');
    }
    return { updated: true, changed: true };
  } catch (err) {
    console.error('[leanApi] Failed to update document:', err);
    return { updated: false, changed: false };
  }
}

/**
 * Create or reuse an RPC session for the Blockly document.
 */
async function ensureRpcSession(): Promise<string | null> {
  const client = getActiveClient();
  if (!client) return null;

  if (currentSessionId) {
    return currentSessionId;
  }

  try {
    const result = await client.sendRequest('$/lean/rpc/connect', {
      uri: BLOCKLY_DOC_URI
    }) as RpcConnected;
    currentSessionId = result.sessionId;
    console.log('[leanApi] Created RPC session:', currentSessionId);
    return currentSessionId;
  } catch (err) {
    console.error('[leanApi] Failed to create RPC session:', err);
    return null;
  }
}

/**
 * Fetch interactive goals at a given position in the Blockly document.
 * Automatically retries once with a fresh session if the session is stale.
 */
async function fetchGoals(line: number, character: number, isRetry = false): Promise<InteractiveGoals | null> {
  const client = getActiveClient();
  if (!client) return null;

  const sessionId = await ensureRpcSession();
  if (!sessionId) return null;

  try {
    const result = await client.sendRequest('$/lean/rpc/call', {
      textDocument: { uri: BLOCKLY_DOC_URI },
      position: { line, character },
      sessionId,
      method: 'Lean.Widget.getInteractiveGoals',
      params: {
        textDocument: { uri: BLOCKLY_DOC_URI },
        position: { line, character },
      },
    });
    return result as InteractiveGoals;
  } catch (err: any) {
    console.error('[leanApi] Failed to get interactive goals:', err);
    // Session might be stale, clear it and retry once
    currentSessionId = null;
    if (!isRetry && err?.message?.includes('Outdated RPC session')) {
      console.log('[leanApi] Retrying with fresh session...');
      return fetchGoals(line, character, true);
    }
    return null;
  }
}

/**
 * Result of a goal request, includes request ID for staleness checking.
 */
export type GoalRequestResult = {
  requestId: number;
  goals: InteractiveGoals | null;
};

/**
 * Submit code to the Lean server and get interactive goals.
 * This is the main entry point - it handles document updates, waits for processing,
 * and fetches goals.
 *
 * @param code - The full Lean code to process
 * @param line - Line number to get goals at (0-indexed)
 * @param character - Character position (0-indexed)
 * @returns Promise resolving to GoalRequestResult with request ID for staleness checking
 */
export async function getGoalsForCode(
  code: string,
  line: number,
  character: number
): Promise<GoalRequestResult> {
  const requestId = ++currentRequestId;
  console.log('[leanApi] getGoalsForCode called, requestId:', requestId, 'line:', line, 'char:', character);

  // Update the document (only if content changed)
  const { updated, changed } = await updateBlocklyDocument(code);
  if (!updated) {
    console.warn('[leanApi] Failed to update document');
    return { requestId, goals: null };
  }

  // Only wait for processing if the document actually changed
  if (changed) {
    console.log('[leanApi] Waiting for processing to complete...');
    await waitForProcessingComplete();
    console.log('[leanApi] Processing complete');
  }

  // Check if this request is still current before fetching goals
  if (requestId !== currentRequestId) {
    console.log('[leanApi] Request', requestId, 'superseded by', currentRequestId, ', aborting');
    return { requestId, goals: null };
  }

  // Fetch and return goals
  console.log('[leanApi] Fetching goals for request', requestId);
  const goals = await fetchGoals(line, character);
  console.log('[leanApi] Goals for request', requestId, ':', goals);
  return { requestId, goals };
}
