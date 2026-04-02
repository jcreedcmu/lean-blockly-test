/**
 * Module-level Lean session singleton.
 *
 * Created once at import time (before React mounts) so that `lake serve`
 * starts and Mathlib begins importing as early as possible. The session
 * survives React StrictMode double-mounting, navigation between levels,
 * and component re-renders.
 *
 * Components access it via getLeanSession().
 */
import { connect as lspConnect } from './LeanLspClient';
import { LeanRpcSession, type GoalsWithHypKinds, type LspDiagnostic } from './LeanRpcSession';
import { log, logError } from './log';

const BLOCKLY_DOC_URI = 'file:///blockly/Blockly.lean';
const TAG = 'LeanSession';

type ReadyCallback = (session: LeanRpcSession) => void;
type DiagnosticsCallback = (diagnostics: LspDiagnostic[]) => void;

class LeanSessionManager {
  private session: LeanRpcSession | null = null;
  private connecting = false;
  private readyCallbacks: ReadyCallback[] = [];
  private diagnosticsCallback: DiagnosticsCallback | null = null;

  /** Start the connection immediately. */
  start() {
    if (this.session || this.connecting) return;
    this.connecting = true;

    const wsProto = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
    const wsUrl = `${wsProto}//${window.location.host}/websocket/MathlibDemo`;

    log(TAG, 'Connecting to Lean server...');

    lspConnect(wsUrl).then((conn) => {
      const session = new LeanRpcSession(conn, BLOCKLY_DOC_URI);
      this.session = session;
      this.connecting = false;

      session.setDiagnosticsCallback((diags) => {
        this.diagnosticsCallback?.(diags);
      });

      log(TAG, 'Session ready');

      // Notify anyone waiting
      for (const cb of this.readyCallbacks) cb(session);
      this.readyCallbacks = [];
    }).catch((err) => {
      this.connecting = false;
      logError(TAG, 'Connection failed:', err);
    });
  }

  /** Get the session if ready, or null. */
  getSession(): LeanRpcSession | null {
    return this.session;
  }

  /** Wait for the session to be ready. Resolves immediately if already ready. */
  whenReady(): Promise<LeanRpcSession> {
    if (this.session) return Promise.resolve(this.session);
    return new Promise((resolve) => {
      this.readyCallbacks.push(resolve);
    });
  }

  /** Set the diagnostics callback. Only one at a time (last caller wins). */
  setDiagnosticsCallback(cb: DiagnosticsCallback | null) {
    this.diagnosticsCallback = cb;
  }
}

/** The global singleton. */
export const leanSession = new LeanSessionManager();

// Start immediately on import — this runs before React mounts.
leanSession.start();
