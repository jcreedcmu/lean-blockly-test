import { useCallback, useEffect, useRef, useState, useLayoutEffect } from 'react'
import * as React from 'react'

// Local imports
import { Blockly, BlocklyHandle, BlocklyState } from './Blockly.tsx';
import type { WorkspaceToLeanResult, SourceInfo } from './workspaceToLean';
import { workspaceToLean } from './workspaceToLean';
import { Goals } from './infoview';
import { log } from './log';
import './infoview/infoview.css';
import type { InteractiveGoals } from '@leanprover/infoview-api';
import { LspDiagnostic, type HypKindMap } from './LeanRpcSession';
import { leanSession } from './LeanSession';
import type { ProofStatus } from './FieldProofStatus';
import { gameData, parseHash, navToHash } from './gameData';
import type { NavigationState } from './gameData';
import { WorldOverview3D } from './WorldOverview3D';

// CSS
import './css/App.css'


function App() {
  const [goals, setGoals] = useState<InteractiveGoals | null>(null);
  const [hypKindMap, setHypKindMap] = useState<HypKindMap>(new Map());
  const [goalsLoading, setGoalsLoading] = useState(false);
  const [proofComplete, setProofComplete] = useState<boolean | null>(false); // null = checking, true = complete, false = incomplete
  const [diagnostics, setDiagnostics] = useState<Array<{ severity?: number; message: string }>>([]);
  const blocklyRef = useRef<BlocklyHandle>(null);
  const [goalsPanelWidth, setGoalsPanelWidth] = useState(300);
  const gameAreaRef = useRef<HTMLDivElement>(null);
  const [nav, setNav] = useState<NavigationState>(() => parseHash(location.hash));
  const navRef = useRef(nav);
  navRef.current = nav;
  const [levelStates, setLevelStates] = useState<Record<string, BlocklyState[]>>(
    () => Object.fromEntries(
      gameData.worlds.map(w => [w.id, w.levels.map(l => l.initial)])
    )
  );

  // True once the initial Lean round-trip has completed for the current level
  const [leanReady, setLeanReady] = useState(false);

  // Track latest goals so diagnostics callback can reference them
  const latestGoalsRef = useRef<InteractiveGoals | null>(null);

  // Track latest source info for matching diagnostics to blocks
  const latestSourceInfoRef = useRef<SourceInfo[]>([]);

  const prelude = `import Mathlib

def FunLimAt (f : ℝ → ℝ) (L : ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ≠ c, |x - c| < δ → |f x - L| < ε

open Lean Server Widget Elab in
structure HypIsAssumption where
  fvarId : String
  isAssumption : Bool
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure GoalHypKinds where
  mvarId : String
  hyps : Array HypIsAssumption
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure HypKindResult where
  goals : Array GoalHypKinds
  deriving FromJson, ToJson

open Lean Server Widget Elab in
structure HypKindParams where
  ctx : WithRpcRef ContextInfo
  mvarId : String
  deriving RpcEncodable

open Lean Server Widget Elab Meta in
def parseLeanName (s : String) : Name :=
  s.splitOn "." |>.foldl (fun acc part =>
    match part.toNat? with
    | some n => Name.mkNum acc n
    | none => Name.mkStr acc part
  ) Name.anonymous

open Lean Server Widget Elab Meta in
@[server_rpc_method]
def getHypKinds (p : HypKindParams) :
    RequestM (RequestTask HypKindResult) :=
  RequestM.pureTask do
    let ci := p.ctx.val
    ci.runMetaM {} do
      let mvarId := MVarId.mk (parseLeanName p.mvarId)
      let mctx ← getMCtx
      let some mvarDecl := mctx.findDecl? mvarId
        | return { goals := #[] }
      withLCtx mvarDecl.lctx mvarDecl.localInstances do
        let mut hyps : Array HypIsAssumption := #[]
        for decl in ← getLCtx do
          if decl.isAuxDecl then continue
          let typeOfType ← inferType decl.type
          hyps := hyps.push {
            fvarId := toString decl.fvarId.name
            isAssumption := typeOfType.isProp
          }
        return { goals := #[{ mvarId := p.mvarId, hyps }] }

`;

  // Called from the diagnostics callback — computes per-block proof statuses
  // from diagnostics + source info, and also demotes overall proof status on errors.
  const onDiagnosticsUpdate = useCallback((diags: LspDiagnostic[]) => {
    if (!leanSession.getSession()) return;
    if (leanSession.getSession().hasErrors()) {
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

  // Send the initial code for a level and wait for the full round-trip.
  async function sendInitialCode(session: import('./LeanRpcSession').LeanRpcSession, worldId: string, levelIndex: number) {
    const initialState = levelStatesRef.current[worldId][levelIndex];
    const { leanCode, sourceInfo } = workspaceToLean(initialState);
    latestSourceInfoRef.current = sourceInfo;
    const preludeLineCount = prelude.split('\n').length - 1;
    const fullCode = prelude + leanCode;

    try {
      const result = await session.getGoals(fullCode, preludeLineCount);
      if (result) {
        latestGoalsRef.current = result.goals;
        setGoals(result.goals);
        setHypKindMap(result.hypKindMap);
        const noGoals = result.goals.goals.length === 0;
        setProofComplete(noGoals && !session.hasErrors());
      }
      log('App', 'Initial Lean round-trip complete');
    } catch (err) {
      console.error('[App] Initial goals check failed:', err);
    }
    setLeanReady(true);
  }

  // Hook into the global Lean session (created before React mounts)
  useEffect(() => {
    // Wire up diagnostics callback
    leanSession.setDiagnosticsCallback((diags) => {
      console.log('[App] Diagnostics changed:', diags.length, 'items');
      setDiagnostics(diags);
      onDiagnosticsUpdate(diags);
    });

    // As soon as the session is ready, send code to start Mathlib loading.
    // If we're already on a level, send the full code and wait for the round-trip.
    // If we're on the world overview, send just the preamble to warm up.
    leanSession.whenReady().then(async (session) => {
      const currentNav = navRef.current;
      if (currentNav.kind === 'playing') {
        log('App', 'Session ready, sending initial level code...');
        await sendInitialCode(session, currentNav.worldId, currentNav.levelIndex);
      } else {
        // Warm up: send preamble so Mathlib starts importing
        log('App', 'Session ready (world overview), warming up with preamble...');
        const preludeLineCount = prelude.split('\n').length - 1;
        await session.getGoals(prelude + '\n', preludeLineCount);
        log('App', 'Preamble warm-up complete');
      }
    });

    return () => {
      leanSession.setDiagnosticsCallback(null);
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

    // If the session is already ready (warmed up from world overview),
    // start checking the level's code immediately.
    const session = leanSession.getSession();
    if (session && !leanReady) {
      sendInitialCode(session, worldId, levelIndex);
    }
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

    // Skip proof checking when Blockly hasn't produced any tactic code yet,
    // or when the initial Lean round-trip hasn't completed yet
    if (!leanCode.trim() || !leanSession.getSession() || !leanReady) return;

    // Clear per-block statuses while Lean re-checks
    blocklyRef.current?.clearProofStatuses();

    const fullCode = prelude + leanCode;
    setProofComplete(null); // Set to "checking" state

    console.log('[onBlocklyChange] Fetching goals for file');

    const preludeLineCount = prelude.split('\n').length - 1;

    (async () => {
      try {
        const result = await leanSession.getSession()!.getGoals(fullCode, preludeLineCount);
        console.log('[onBlocklyChange] Goals:', result);

        if (result) {
          latestGoalsRef.current = result.goals;
          setGoals(result.goals);
          setHypKindMap(result.hypKindMap);

          // Determine proof status: complete only if no goals AND no errors
          const session = leanSession.getSession();
          if (session) {
            const noGoals = result.goals.goals.length === 0;
            const isComplete = noGoals && !session.hasErrors();
            setProofComplete(isComplete);
          }
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

    if (!leanSession.getSession()) {
      console.log('[onRequestGoals] RPC session not initialized');
      return;
    }

    const fullCode = prelude + leanCode;
    const preludeLineCount = prelude.split('\n').length - 1;
    console.log('[onRequestGoals] Full code being sent:');
    console.log('---BEGIN CODE---');
    console.log(fullCode);
    console.log('---END CODE---');

    setGoalsLoading(true);
    try {
      console.log('[onRequestGoals] Fetching goals via LeanRpcSession...');
      const result = await leanSession.getSession().getGoals(fullCode, preludeLineCount);
      console.log('[onRequestGoals] Goals received:', result);

      if (result) {
        console.log('[onRequestGoals] Setting goals');
        setGoals(result.goals);
        setHypKindMap(result.hypKindMap);
      } else {
        console.log('[onRequestGoals] No goals returned');
      }
    } catch (err) {
      console.error('[onRequestGoals] Error fetching goals:', err);
    } finally {
      setGoalsLoading(false);
    }
  }

  function onDividerMouseDown(e: React.MouseEvent) {
    e.preventDefault();
    const startX = e.clientX;
    const startWidth = goalsPanelWidth;

    function onMouseMove(ev: MouseEvent) {
      const delta = startX - ev.clientX;
      const newWidth = Math.max(150, Math.min(800, startWidth + delta));
      setGoalsPanelWidth(newWidth);
    }

    function onMouseUp() {
      document.removeEventListener('mousemove', onMouseMove);
      document.removeEventListener('mouseup', onMouseUp);
    }

    document.addEventListener('mousemove', onMouseMove);
    document.addEventListener('mouseup', onMouseUp);
  }

  if (nav.kind === 'worldOverview') {
    return <div className="app-root">
      <WorldOverview3D worlds={gameData.worlds} onSelectWorld={enterLevel} />
    </div>;
  }

  const currentWorld = gameData.worlds.find(w => w.id === nav.worldId)!;
  const currentLevel = currentWorld.levels[nav.levelIndex];

  if (!leanReady) {
    return <div className="app-root">
      <div className="loading-screen">
        <div className="spinner" />
        <span>Loading Lean and Mathlib...</span>
      </div>
    </div>;
  }

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
      <div className="panel-divider" onMouseDown={onDividerMouseDown} />
      <div className="goals-panel" style={{ width: goalsPanelWidth }}>
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
          <Goals
            goals={goals}
            hypKindMap={hypKindMap}
            onHypDragStart={(name, e, mode) => blocklyRef.current?.startHypDrag(name, e, mode)}
          />
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
