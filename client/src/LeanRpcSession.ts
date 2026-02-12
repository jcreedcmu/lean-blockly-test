/**
 * Lean-specific RPC session built on a vscode-jsonrpc MessageConnection.
 *
 * Manages the document lifecycle, file-progress tracking, diagnostics,
 * RPC session connect/keepalive, and interactive-goal extraction —
 * all without lean4monaco or Monaco.
 */
import type { MessageConnection } from './LeanLspClient';
import type {
  InteractiveGoals,
  InteractiveGoal,
  InteractiveDiagnostic,
  TaggedText,
  MsgEmbed,
} from '@leanprover/infoview-api';

const KEEPALIVE_PERIOD_MS = 10_000;

// ── helpers ──────────────────────────────────────────────────────────

function extractGoalsFromTaggedText(tt: TaggedText<MsgEmbed>): InteractiveGoal[] {
  const goals: InteractiveGoal[] = [];

  function traverse(node: TaggedText<MsgEmbed>) {
    if ('text' in node) return;
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

function extractGoalsFromDiagnostics(diagnostics: InteractiveDiagnostic[]): InteractiveGoals {
  const allGoals: InteractiveGoal[] = [];
  for (const diag of diagnostics) {
    allGoals.push(...extractGoalsFromTaggedText(diag.message));
  }
  return { goals: allGoals };
}

// ── Diagnostic type (minimal, from LSP) ─────────────────────────────

export interface LspDiagnostic {
  range: { start: { line: number; character: number }; end: { line: number; character: number } };
  severity?: number;
  message: string;
  [key: string]: unknown;
}

// ── LeanRpcSession ──────────────────────────────────────────────────

export class LeanRpcSession {
  private connection: MessageConnection;
  private uri: string;

  // document state
  private documentOpen = false;
  private documentVersion = 0;
  private lastDocumentContent: string | null = null;

  // processing state
  private processingResolvers: Array<() => void> = [];

  // diagnostics state
  private currentDiagnostics: LspDiagnostic[] = [];
  private onDiagnosticsChange?: (diagnostics: LspDiagnostic[]) => void;

  // RPC session state
  private sessionId: string | null = null;
  private keepAliveInterval: ReturnType<typeof setInterval> | null = null;

  // notification listener disposables
  private disposables: Array<{ dispose(): void }> = [];

  constructor(connection: MessageConnection, uri: string) {
    this.connection = connection;
    this.uri = uri;

    // listen for file-progress notifications
    this.disposables.push(
      connection.onNotification('$/lean/fileProgress', (params: any) => {
        if (params.textDocument?.uri === this.uri && params.processing?.length === 0) {
          const resolvers = this.processingResolvers;
          this.processingResolvers = [];
          resolvers.forEach((r) => r());
        }
      }),
    );

    // listen for publishDiagnostics
    this.disposables.push(
      connection.onNotification('textDocument/publishDiagnostics', (params: any) => {
        if (params.uri === this.uri) {
          this.currentDiagnostics = params.diagnostics ?? [];
          this.onDiagnosticsChange?.(this.currentDiagnostics);
        }
      }),
    );
  }

  // ── document management ─────────────────────────────────────────

  /**
   * Send didOpen or didChange for the given code.
   * Returns whether the content actually changed.
   */
  async updateDocument(code: string): Promise<{ success: boolean; changed: boolean }> {
    if (this.documentOpen && code === this.lastDocumentContent) {
      return { success: true, changed: false };
    }

    try {
      if (!this.documentOpen) {
        await this.connection.sendNotification('textDocument/didOpen', {
          textDocument: {
            uri: this.uri,
            languageId: 'lean4',
            version: ++this.documentVersion,
            text: code,
          },
        });
        this.documentOpen = true;
      } else {
        await this.connection.sendNotification('textDocument/didChange', {
          textDocument: {
            uri: this.uri,
            version: ++this.documentVersion,
          },
          contentChanges: [{ text: code }],
        });
      }

      this.lastDocumentContent = code;
      return { success: true, changed: true };
    } catch (err) {
      console.error('[LeanRpcSession] Failed to update document:', err);
      return { success: false, changed: false };
    }
  }

  // ── processing ──────────────────────────────────────────────────

  /** Resolves when `$/lean/fileProgress` reports `processing: []`. */
  waitForProcessing(): Promise<void> {
    return new Promise((resolve) => {
      this.processingResolvers.push(resolve);
    });
  }

  // ── RPC session ─────────────────────────────────────────────────

  /**
   * Send `$/lean/rpc/connect`, start keepalive, return sessionId.
   * No-ops if already connected.
   */
  async connect(): Promise<string | null> {
    if (this.sessionId) return this.sessionId;

    try {
      const result: any = await this.connection.sendRequest('$/lean/rpc/connect', {
        uri: this.uri,
      });
      this.sessionId = result.sessionId;
      this.startKeepalive();
      return this.sessionId;
    } catch (err: any) {
      console.error('[LeanRpcSession] connect failed:', err);
      if (err?.message?.includes('closed file')) {
        this.documentOpen = false;
        this.lastDocumentContent = null;
      }
      return null;
    }
  }

  /** Stop keepalive, clear sessionId. */
  disconnect(): void {
    this.stopKeepalive();
    this.sessionId = null;
  }

  private startKeepalive(): void {
    if (this.keepAliveInterval) return;

    this.keepAliveInterval = setInterval(async () => {
      if (!this.sessionId) {
        this.stopKeepalive();
        return;
      }
      try {
        await this.connection.sendNotification('$/lean/rpc/keepAlive', {
          uri: this.uri,
          sessionId: this.sessionId,
        });
      } catch {
        this.stopKeepalive();
        this.sessionId = null;
      }
    }, KEEPALIVE_PERIOD_MS);
  }

  private stopKeepalive(): void {
    if (this.keepAliveInterval) {
      clearInterval(this.keepAliveInterval);
      this.keepAliveInterval = null;
    }
  }

  // ── diagnostics ─────────────────────────────────────────────────

  getDiagnostics(): LspDiagnostic[] {
    return this.currentDiagnostics;
  }

  hasErrors(): boolean {
    // DiagnosticSeverity.Error = 1
    return this.currentDiagnostics.some((d) => d.severity === 1);
  }

  setDiagnosticsCallback(callback: (diagnostics: LspDiagnostic[]) => void): void {
    this.onDiagnosticsChange = callback;
  }

  // ── interactive diagnostics / goals ─────────────────────────────

  async getInteractiveDiagnostics(): Promise<InteractiveDiagnostic[]> {
    if (!this.sessionId) throw new Error('No active RPC session');

    return await this.connection.sendRequest('$/lean/rpc/call', {
      textDocument: { uri: this.uri },
      position: { line: 0, character: 0 },
      sessionId: this.sessionId,
      method: 'Lean.Widget.getInteractiveDiagnostics',
      params: { textDocument: { uri: this.uri } },
    });
  }

  /**
   * High-level: update document → wait for processing → connect RPC →
   * fetch interactive diagnostics → extract goals.
   */
  async getGoals(code: string): Promise<InteractiveGoals | null> {
    for (let attempt = 0; attempt < 2; attempt++) {
      const { success, changed } = await this.updateDocument(code);
      if (!success) return null;

      if (changed) await this.waitForProcessing();

      const sessionId = await this.connect();
      if (!sessionId) {
        if (attempt === 0 && !this.documentOpen) continue;
        return null;
      }

      try {
        const diagnostics = await this.getInteractiveDiagnostics();
        return extractGoalsFromDiagnostics(diagnostics);
      } catch (err: any) {
        console.error('[LeanRpcSession] getGoals failed:', err);
        if (err?.message?.includes('Outdated RPC session') && attempt === 0) {
          this.disconnect();
          continue;
        }
        return null;
      }
    }
    return null;
  }

  // ── cleanup ─────────────────────────────────────────────────────

  dispose(): void {
    this.disconnect();
    this.processingResolvers = [];
    for (const d of this.disposables) d.dispose();
    this.disposables = [];
  }
}
