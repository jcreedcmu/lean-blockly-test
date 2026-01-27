/**
 * Manages RPC sessions with the Lean server, including keepalives.
 *
 * Based on lean4monaco's RpcSessionAtPos pattern.
 */
import { LeanMonaco } from 'lean4monaco';
import type {
  InteractiveGoals,
  InteractiveGoal,
  InteractiveDiagnostic,
  TaggedText,
  MsgEmbed,
  LeanFileProgressProcessingInfo,
  RpcConnected,
} from '@leanprover/infoview-api';
import type { Diagnostic } from 'vscode-languageserver-protocol';

const KEEPALIVE_PERIOD_MS = 10000; // 10 seconds, matching lean4monaco

type LeanClient = ReturnType<typeof getActiveClient>;

/**
 * Extract goals embedded in a TaggedText<MsgEmbed> structure.
 * Goals are embedded within diagnostic messages via the MsgEmbed.goal variant.
 */
function extractGoalsFromTaggedText(tt: TaggedText<MsgEmbed>): InteractiveGoal[] {
  const goals: InteractiveGoal[] = [];

  function traverse(node: TaggedText<MsgEmbed>) {
    if ('text' in node) {
      return; // Plain text, no goals
    }
    if ('append' in node) {
      node.append.forEach(traverse);
      return;
    }
    if ('tag' in node) {
      const [embed, content] = node.tag;
      if ('goal' in embed) {
        goals.push(embed.goal);
      }
      traverse(content);
    }
  }

  traverse(tt);
  return goals;
}

/**
 * Extract all goals from an array of interactive diagnostics.
 * Returns them in InteractiveGoals format for compatibility with existing UI.
 */
function extractGoalsFromDiagnostics(diagnostics: InteractiveDiagnostic[]): InteractiveGoals {
  const allGoals: InteractiveGoal[] = [];
  for (const diag of diagnostics) {
    allGoals.push(...extractGoalsFromTaggedText(diag.message));
  }
  return { goals: allGoals };
}

function getActiveClient() {
  const leanMonaco = LeanMonaco.activeInstance;
  if (!leanMonaco) return null;
  const clientProvider = leanMonaco.clientProvider;
  if (!clientProvider) return null;
  return clientProvider.getActiveClient();
}

export class RpcSessionManager {
  private uri: string;
  private sessionId: string | null = null;
  private keepAliveInterval: ReturnType<typeof setInterval> | null = null;
  private client: LeanClient = null;

  // Document state
  private documentOpen = false;
  private documentVersion = 0;
  private lastDocumentContent: string | null = null;

  // Processing state
  private processingResolvers: Array<() => void> = [];
  private progressListenerSetup = false;

  // Diagnostics state
  private currentDiagnostics: Diagnostic[] = [];
  private diagnosticsListenerSetup = false;
  private onDiagnosticsChange?: (diagnostics: Diagnostic[]) => void;

  constructor(uri: string) {
    this.uri = uri;
  }

  /**
   * Initialize the session manager. Call this after the Lean client is available.
   */
  async initialize(): Promise<boolean> {
    this.client = getActiveClient();
    if (!this.client) {
      console.warn('[RpcSessionManager] No active client');
      return false;
    }

    this.ensureProgressListener();
    this.ensureDiagnosticsListener();
    return true;
  }

  /**
   * Connect to an RPC session if not already connected.
   */
  async connect(): Promise<string | null> {
    if (this.sessionId) {
      return this.sessionId;
    }

    if (!this.client) {
      this.client = getActiveClient();
      if (!this.client) {
        console.warn('[RpcSessionManager] No active client');
        return null;
      }
    }

    try {
      const result = await this.client.sendRequest('$/lean/rpc/connect', {
        uri: this.uri
      }) as RpcConnected;

      this.sessionId = result.sessionId;
      console.log('[RpcSessionManager] Connected, sessionId:', this.sessionId);

      this.startKeepalive();
      return this.sessionId;
    } catch (err: any) {
      console.error('[RpcSessionManager] Failed to connect:', err);

      // If the file is closed, reset document state so next updateDocument will reopen it
      if (err?.message?.includes('closed file')) {
        console.log('[RpcSessionManager] File was closed, resetting document state for retry...');
        this.documentOpen = false;
        this.lastDocumentContent = null;
      }

      return null;
    }
  }

  /**
   * Disconnect and clean up the session.
   */
  disconnect(): void {
    this.stopKeepalive();
    this.sessionId = null;
    console.log('[RpcSessionManager] Disconnected');
  }

  private startKeepalive(): void {
    if (this.keepAliveInterval) return;

    this.keepAliveInterval = setInterval(async () => {
      if (!this.client || !this.sessionId) {
        this.stopKeepalive();
        return;
      }

      try {
        await this.client.sendNotification('$/lean/rpc/keepAlive', {
          uri: this.uri,
          sessionId: this.sessionId,
        });
        console.log('[RpcSessionManager] Keepalive sent');
      } catch (err) {
        console.error('[RpcSessionManager] Keepalive failed:', err);
        this.stopKeepalive();
        this.sessionId = null;
      }
    }, KEEPALIVE_PERIOD_MS);

    console.log('[RpcSessionManager] Keepalive started');
  }

  private stopKeepalive(): void {
    if (this.keepAliveInterval) {
      clearInterval(this.keepAliveInterval);
      this.keepAliveInterval = null;
      console.log('[RpcSessionManager] Keepalive stopped');
    }
  }

  private ensureProgressListener(): void {
    if (this.progressListenerSetup || !this.client) return;

    this.client.progressChanged((event: [string, LeanFileProgressProcessingInfo[]]) => {
      const [uri, processing] = event;
      if (uri === this.uri && processing.length === 0) {
        console.log('[RpcSessionManager] Processing complete for', uri);
        const resolvers = this.processingResolvers;
        this.processingResolvers = [];
        resolvers.forEach(resolve => resolve());
      }
    });

    this.progressListenerSetup = true;
    console.log('[RpcSessionManager] Progress listener set up');
  }

  private ensureDiagnosticsListener(): void {
    if (this.diagnosticsListenerSetup || !this.client) return;

    this.client.diagnostics((event: { uri: string; diagnostics: Diagnostic[] }) => {
      const { uri, diagnostics } = event;
      if (uri === this.uri) {
        console.log('[RpcSessionManager] Diagnostics changed for', uri, ':', diagnostics.length, 'items');
        this.currentDiagnostics = diagnostics;
        if (this.onDiagnosticsChange) {
          this.onDiagnosticsChange(diagnostics);
        }
      }
    });

    this.diagnosticsListenerSetup = true;
    console.log('[RpcSessionManager] Diagnostics listener set up');
  }

  /**
   * Set a callback to be notified when diagnostics change.
   */
  setDiagnosticsCallback(callback: (diagnostics: Diagnostic[]) => void): void {
    this.onDiagnosticsChange = callback;
  }

  /**
   * Get current diagnostics for this document.
   */
  getDiagnostics(): Diagnostic[] {
    return this.currentDiagnostics;
  }

  /**
   * Check if there are any error-level diagnostics.
   */
  hasErrors(): boolean {
    // DiagnosticSeverity.Error = 1
    return this.currentDiagnostics.some(d => d.severity === 1);
  }

  private waitForProcessingComplete(): Promise<void> {
    return new Promise(resolve => {
      this.processingResolvers.push(resolve);
    });
  }

  /**
   * Update the document content on the server.
   * Returns whether the content actually changed.
   */
  async updateDocument(code: string): Promise<{ success: boolean; changed: boolean }> {
    if (!this.client) {
      this.client = getActiveClient();
      if (!this.client) {
        return { success: false, changed: false };
      }
    }

    // Check if content actually changed
    if (this.documentOpen && code === this.lastDocumentContent) {
      console.log('[RpcSessionManager] Document unchanged, skipping update');
      return { success: true, changed: false };
    }

    this.ensureProgressListener();

    try {
      if (!this.documentOpen) {
        await this.client.sendNotification('textDocument/didOpen', {
          textDocument: {
            uri: this.uri,
            languageId: 'lean4',
            version: ++this.documentVersion,
            text: code,
          },
        });
        this.documentOpen = true;
        console.log('[RpcSessionManager] Document opened');
      } else {
        await this.client.sendNotification('textDocument/didChange', {
          textDocument: {
            uri: this.uri,
            version: ++this.documentVersion,
          },
          contentChanges: [{ text: code }],
        });
        console.log('[RpcSessionManager] Document updated, version:', this.documentVersion);
      }

      this.lastDocumentContent = code;

      return { success: true, changed: true };
    } catch (err) {
      console.error('[RpcSessionManager] Failed to update document:', err);
      return { success: false, changed: false };
    }
  }

  private async callRpc(sessionId: string): Promise<InteractiveDiagnostic[]> {
    return await this.client!.sendRequest('$/lean/rpc/call', {
      textDocument: { uri: this.uri },
      position: { line: 0, character: 0 }, // Position still required for session
      sessionId,
      method: 'Lean.Widget.getInteractiveDiagnostics',
      params: {
        textDocument: { uri: this.uri },
      },
    }) as InteractiveDiagnostic[];
  }

  /**
   * Get interactive goals for the entire file.
   * Extracts goals from diagnostic messages using getInteractiveDiagnostics.
   * Handles document updates, processing wait, and session management.
   */
  async getGoals(code: string): Promise<InteractiveGoals | null> {
    console.log('[RpcSessionManager] getGoals called');

    for (let attempt = 0; attempt < 2; attempt++) {
      const { success, changed } = await this.updateDocument(code);
      if (!success) {
        console.warn('[RpcSessionManager] Failed to update document');
        return null;
      }

      if (changed) {
        console.log('[RpcSessionManager] Waiting for processing...');
        await this.waitForProcessingComplete();
        console.log('[RpcSessionManager] Processing complete');
      }

      const sessionId = await this.connect();
      if (!sessionId) {
        console.warn('[RpcSessionManager] Failed to connect');
        if (attempt === 0 && !this.documentOpen) {
          console.log('[RpcSessionManager] Retrying after document state reset...');
          continue;
        }
        return null;
      }

      try {
        const diagnostics = await this.callRpc(sessionId);
        console.log('[RpcSessionManager] Diagnostics received:', diagnostics);
        const goals = extractGoalsFromDiagnostics(diagnostics);
        console.log('[RpcSessionManager] Goals extracted:', goals);
        return goals;
      } catch (err: any) {
        console.error('[RpcSessionManager] Failed to get diagnostics:', err);
        if (err?.message?.includes('Outdated RPC session') && attempt === 0) {
          console.log('[RpcSessionManager] Session outdated, reconnecting...');
          this.disconnect();
          continue;
        }
        return null;
      }
    }
    return null;
  }

  /**
   * Dispose of all resources.
   */
  dispose(): void {
    this.disconnect();
    this.processingResolvers = [];
  }
}
