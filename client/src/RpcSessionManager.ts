/**
 * Manages RPC sessions with the Lean server, including keepalives.
 *
 * Based on lean4monaco's RpcSessionAtPos pattern.
 */
import { LeanMonaco } from 'lean4monaco';
import type { InteractiveGoals, LeanFileProgressProcessingInfo } from '@leanprover/infoview-api';
import type { RpcConnected } from '@leanprover/infoview-api';

const KEEPALIVE_PERIOD_MS = 10000; // 10 seconds, matching lean4monaco

type LeanClient = ReturnType<typeof getActiveClient>;

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
    } catch (err) {
      console.error('[RpcSessionManager] Failed to connect:', err);
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

  /**
   * Get interactive goals at a position.
   * Handles document updates, processing wait, and session management.
   */
  async getGoals(code: string, line: number, character: number): Promise<InteractiveGoals | null> {
    console.log('[RpcSessionManager] getGoals called, line:', line, 'char:', character);

    // Update document if needed
    const { success, changed } = await this.updateDocument(code);
    if (!success) {
      console.warn('[RpcSessionManager] Failed to update document');
      return null;
    }

    // Wait for processing if document changed
    if (changed) {
      console.log('[RpcSessionManager] Waiting for processing...');
      await this.waitForProcessingComplete();
      console.log('[RpcSessionManager] Processing complete');
    }

    // Ensure we have a session
    const sessionId = await this.connect();
    if (!sessionId) {
      console.warn('[RpcSessionManager] Failed to connect');
      return null;
    }

    // Fetch goals
    try {
      const result = await this.client!.sendRequest('$/lean/rpc/call', {
        textDocument: { uri: this.uri },
        position: { line, character },
        sessionId,
        method: 'Lean.Widget.getInteractiveGoals',
        params: {
          textDocument: { uri: this.uri },
          position: { line, character },
        },
      });
      console.log('[RpcSessionManager] Goals received:', result);
      return result as InteractiveGoals;
    } catch (err: any) {
      console.error('[RpcSessionManager] Failed to get goals:', err);

      // If session is outdated, disconnect and retry once
      if (err?.message?.includes('Outdated RPC session')) {
        console.log('[RpcSessionManager] Session outdated, reconnecting...');
        this.disconnect();
        const newSessionId = await this.connect();
        if (newSessionId) {
          try {
            const result = await this.client!.sendRequest('$/lean/rpc/call', {
              textDocument: { uri: this.uri },
              position: { line, character },
              sessionId: newSessionId,
              method: 'Lean.Widget.getInteractiveGoals',
              params: {
                textDocument: { uri: this.uri },
                position: { line, character },
              },
            });
            return result as InteractiveGoals;
          } catch (retryErr) {
            console.error('[RpcSessionManager] Retry failed:', retryErr);
          }
        }
      }

      return null;
    }
  }

  /**
   * Dispose of all resources.
   */
  dispose(): void {
    this.disconnect();
    this.processingResolvers = [];
  }
}
