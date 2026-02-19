import { useCallback, useEffect, useRef, useState } from 'react'
import * as React from 'react'

// Local imports
import { Blockly, BlocklyHandle, BlocklyState } from './Blockly.tsx';
import type { WorkspaceToLeanResult, SourceInfo } from './workspaceToLean';
import { Goals } from './infoview';
import './infoview/infoview.css';
import type { InteractiveGoals } from '@leanprover/infoview-api';
import { connect as lspConnect } from './LeanLspClient';
import { LeanRpcSession, LspDiagnostic } from './LeanRpcSession';
import type { ProofStatus } from './FieldProofStatus';
import { gameData, parseHash, navToHash } from './gameData';
import type { NavigationState } from './gameData';
import { WorldOverview3D } from './WorldOverview3D';

// CSS
import './css/App.css'

// Virtual document URI for Blockly code
const BLOCKLY_DOC_URI = 'file:///blockly/Blockly.lean';

function App() {
  const [goals, setGoals] = useState<InteractiveGoals | null>(null);
  const [goalsLoading, setGoalsLoading] = useState(false);
  const [proofComplete, setProofComplete] = useState<boolean | null>(false); // null = checking, true = complete, false = incomplete
  const [diagnostics, setDiagnostics] = useState<Array<{ severity?: number; message: string }>>([]);
  const blocklyRef = useRef<BlocklyHandle>(null);
  const [nav, setNav] = useState<NavigationState>(() => parseHash(location.hash));
  const navRef = useRef(nav);
  navRef.current = nav;
  const [levelStates, setLevelStates] = useState<Record<string, BlocklyState[]>>(
    () => Object.fromEntries(
      gameData.worlds.map(w => [w.id, w.levels.map(l => l.initial)])
    )
  );

  // RPC session for Blockly code
  const rpcSessionRef = useRef<LeanRpcSession | null>(null);
  const [rpcManagerReady, setRpcManagerReady] = useState(false);

  // Track latest goals so diagnostics callback can reference them
  const latestGoalsRef = useRef<InteractiveGoals | null>(null);

  // Track latest source info for matching diagnostics to blocks
  const latestSourceInfoRef = useRef<SourceInfo[]>([]);

  const prelude = `import Mathlib

def FunLimAt (f : ℝ → ℝ) (L : ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ≠ c, |x - c| < δ → |f x - L| < ε

`;

  // Called from the diagnostics callback — computes per-block proof statuses
  // from diagnostics + source info, and also demotes overall proof status on errors.
  const onDiagnosticsUpdate = useCallback((diags: LspDiagnostic[]) => {
    if (!rpcSessionRef.current) return;
    if (rpcSessionRef.current.hasErrors()) {
      setProofComplete(false);
    }

    // Compute per-block proof statuses
    const sourceInfo = latestSourceInfoRef.current;
    if (sourceInfo.length === 0 || !blocklyRef.current) return;

    const preludeLines = prelude.split('\n').length - 1;
    const errorDiags = diags.filter(d => d.severity === 1);

    const statuses = new Map<string, ProofStatus>();
    for (const si of sourceInfo) {
      const blockStartLine = si.startLineCol[0] + preludeLines;
      const blockEndLine = si.endLineCol[0] + preludeLines;

      const hasError = errorDiags.some(d => {
        const diagStartLine = d.range.start.line;
        const diagEndLine = d.range.end.line;
        return diagStartLine <= blockEndLine && diagEndLine >= blockStartLine;
      });

      statuses.set(si.id, hasError ? 'incomplete' : 'complete');
    }

    blocklyRef.current.updateProofStatuses(statuses);
  }, []);

  // Initialize standalone LSP connection + RPC session
  useEffect(() => {
    let disposed = false;

    const wsProto = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
    const wsUrl = `${wsProto}//${window.location.host}/websocket/MathlibDemo`;

    lspConnect(wsUrl).then((conn) => {
      if (disposed) { conn.dispose(); return; }

      const session = new LeanRpcSession(conn, BLOCKLY_DOC_URI);
      rpcSessionRef.current = session;

      session.setDiagnosticsCallback((diags) => {
        console.log('[App] Diagnostics changed:', diags.length, 'items');
        setDiagnostics(diags);
        onDiagnosticsUpdate(diags);
      });

      setRpcManagerReady(true);
      console.log('[App] LeanRpcSession ready');
    }).catch((err) => {
      console.error('[App] LSP connection failed:', err);
    });

    return () => {
      disposed = true;
      rpcSessionRef.current?.dispose();
      rpcSessionRef.current = null;
      setRpcManagerReady(false);
    };
  }, [onDiagnosticsUpdate]);

  const levelStatesRef = useRef(levelStates);
  levelStatesRef.current = levelStates;

  // Handle hash changes (browser back/forward, link navigation, programmatic)
  useEffect(() => {
    function onHashChange() {
      const newNav = parseHash(location.hash);
      const oldNav = navRef.current;

      // No-op if unchanged
      if (oldNav.kind === newNav.kind
        && (newNav.kind === 'worldOverview'
          || (oldNav.kind === 'playing' && newNav.kind === 'playing'
            && oldNav.worldId === newNav.worldId
            && oldNav.levelIndex === newNav.levelIndex))) return;

      // Save workspace if leaving a playing state
      if (oldNav.kind === 'playing') {
        const ws = blocklyRef.current?.saveWorkspace();
        if (ws) {
          const { worldId, levelIndex } = oldNav;
          setLevelStates(prev => {
            const states = [...prev[worldId]];
            states[levelIndex] = ws;
            return { ...prev, [worldId]: states };
          });
        }
      }

      // Load workspace if Blockly is already mounted (playing → playing)
      if (newNav.kind === 'playing' && oldNav.kind === 'playing') {
        blocklyRef.current?.loadWorkspace(
          levelStatesRef.current[newNav.worldId][newNav.levelIndex]
        );
      }

      setNav(newNav);
    }

    window.addEventListener('hashchange', onHashChange);
    return () => window.removeEventListener('hashchange', onHashChange);
  }, []);

  function enterLevel(worldId: string, levelIndex: number) {
    location.hash = navToHash({ kind: 'playing', worldId, levelIndex });
  }

  function goBack() {
    location.hash = navToHash({ kind: 'worldOverview' });
  }

  function resetCurrentLevel() {
    if (nav.kind !== 'playing') return;
    const { worldId, levelIndex } = nav;
    const world = gameData.worlds.find(w => w.id === worldId);
    if (!world) return;
    const initialState = world.levels[levelIndex].initial;
    blocklyRef.current?.loadWorkspace(initialState);
    setLevelStates(prev => {
      const worldStates = [...prev[worldId]];
      worldStates[levelIndex] = initialState;
      return { ...prev, [worldId]: worldStates };
    });
  }

  function onBlocklyChange(result: WorkspaceToLeanResult) {
    const { leanCode, sourceInfo } = result;

    // Store source info for diagnostics matching
    latestSourceInfoRef.current = sourceInfo;

    // Skip proof checking when Blockly hasn't produced any tactic code yet
    // (e.g. during initial render before blocks are loaded)
    if (!leanCode.trim() || !rpcSessionRef.current) return;

    // Clear per-block statuses while Lean re-checks
    blocklyRef.current?.clearProofStatuses();

    const fullCode = prelude + leanCode;
    setProofComplete(null); // Set to "checking" state

    console.log('[onBlocklyChange] Fetching goals for file');

    (async () => {
      try {
        const goals = await rpcSessionRef.current!.getGoals(fullCode);
        console.log('[onBlocklyChange] Goals:', goals);

        latestGoalsRef.current = goals;
        setGoals(goals);

        // Determine proof status: complete only if no goals AND no errors
        const session = rpcSessionRef.current;
        if (goals && session) {
          const noGoals = goals.goals.length === 0;
          const isComplete = noGoals && !session.hasErrors();
          setProofComplete(isComplete);
        }
      } catch (err) {
        console.error('[onBlocklyChange] Error checking proof status:', err);
        setProofComplete(false);
      }
    })();
  }

  async function onRequestGoals(
    blockId: string,
    leanCode: string,
    _sourceInfo: SourceInfo[],
    _blockSourceInfo: SourceInfo | undefined
  ) {
    console.log('[onRequestGoals] ========================================');
    console.log('[onRequestGoals] Block ID:', blockId);

    if (!rpcSessionRef.current) {
      console.log('[onRequestGoals] RPC session not initialized');
      return;
    }

    const fullCode = prelude + leanCode;
    console.log('[onRequestGoals] Full code being sent:');
    console.log('---BEGIN CODE---');
    console.log(fullCode);
    console.log('---END CODE---');

    setGoalsLoading(true);
    try {
      console.log('[onRequestGoals] Fetching goals via LeanRpcSession...');
      const goals = await rpcSessionRef.current.getGoals(fullCode);
      console.log('[onRequestGoals] Goals received:', goals);

      if (goals) {
        console.log('[onRequestGoals] Setting goals');
        setGoals(goals);
      } else {
        console.log('[onRequestGoals] No goals returned');
      }
    } catch (err) {
      console.error('[onRequestGoals] Error fetching goals:', err);
    } finally {
      setGoalsLoading(false);
    }
  }

  if (nav.kind === 'worldOverview') {
    return <div className="app-root">
      <WorldOverview3D worlds={gameData.worlds} onSelectWorld={enterLevel} />
    </div>;
  }

  const currentWorld = gameData.worlds.find(w => w.id === nav.worldId)!;
  const currentLevel = currentWorld.levels[nav.levelIndex];

  return <div className="app-root">
    <div className="navbar">
      <div className="navbar-left">
        <button className="navbar-btn" onClick={goBack} title="Back to worlds">&#x25C0;</button>
        <button className="navbar-btn" onClick={resetCurrentLevel} title="Reset level">&#x21BB;</button>
        <span className="navbar-level-label">
          {currentWorld.name} &mdash; {currentLevel.name} ({nav.levelIndex + 1}/{currentWorld.levels.length})
        </span>
      </div>
      <div className="navbar-right">
        <button
          className="navbar-btn"
          disabled={nav.levelIndex === 0}
          onClick={() => enterLevel(nav.worldId, nav.levelIndex - 1)}
        >&#x2190;</button>
        <button
          className="navbar-btn"
          disabled={nav.levelIndex === currentWorld.levels.length - 1}
          onClick={() => enterLevel(nav.worldId, nav.levelIndex + 1)}
        >&#x2192;</button>
      </div>
    </div>
    <div className="game-area">
      <Blockly
        ref={blocklyRef}
        style={{ flexGrow: 1 }}
        onBlocklyChange={onBlocklyChange}
        onRequestGoals={onRequestGoals}
        initialData={levelStates[nav.worldId][nav.levelIndex]}
        allowedBlocks={currentLevel.allowedBlocks}
      />
      <div className="goals-panel">
        <div className="proof-status">
          {proofComplete === null ? (
            <span className="proof-checking">Checking...</span>
          ) : proofComplete ? (
            <span className="proof-complete">Proof complete!</span>
          ) : (
            <span className="proof-incomplete">Proof incomplete</span>
          )}
        </div>
        {goalsLoading ? (
          <div className="goals-loading">
            <div className="spinner" />
            <span>Loading goals...</span>
          </div>
        ) : (
          <Goals goals={goals} />
        )}
        {diagnostics.length > 0 && (
          <div className="diagnostics">
            {diagnostics.map((d, i) => (
              <div key={i} className={`diagnostic severity-${d.severity ?? 1}`}>
                {d.message}
              </div>
            ))}
          </div>
        )}
      </div>
    </div>
  </div>;
}

export default App
