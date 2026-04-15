import { useCallback, useEffect, useRef, useState } from 'react'
import * as React from 'react'

// Local imports
import { Blockly, BlocklyHandle, BlocklyState } from './Blockly.tsx';
import type { WorkspaceToLeanResult, SourceInfo } from './workspaceToLean';
import { workspaceToLean } from './workspaceToLean';
import { Goals } from './infoview';
import { log } from './log';
import './infoview/infoview.css';
import type { InteractiveGoals } from '@leanprover/infoview-api';
import { leanSession } from './LeanSession';
import { LevelEvaluator, type EvaluationResult } from './LevelEvaluator';
import type { ProofStatus } from './FieldProofStatus';
import ReactMarkdown from 'react-markdown';
import { gameData, parseHash, navToHash } from './gameData';
import type { NavigationState } from './gameData';
import { WorldOverview3D } from './WorldOverview3D';

// CSS
import './css/App.css'


function App() {
  // The single source of truth for "what does Lean say about the current proof".
  // null = not yet evaluated; otherwise the latest non-stale evaluation result.
  const [evaluation, setEvaluation] = useState<EvaluationResult | null>(null);
  // True while an evaluation is in flight (used to render the "Checking..." state).
  const [evaluating, setEvaluating] = useState(false);
  // True once the initial Lean round-trip has completed for the current level.
  const [leanReady, setLeanReady] = useState(false);
  // Whether the introduction-commentary popup is visible.
  const [showIntro, setShowIntro] = useState(false);
  // Whether the "Copied!" toast is visible.
  const [showCopiedToast, setShowCopiedToast] = useState(false);

  const blocklyRef = useRef<BlocklyHandle>(null);
  const [goalsPanelWidth, setGoalsPanelWidth] = useState(300);
  const [nav, setNav] = useState<NavigationState>(() => parseHash(location.hash));
  const navRef = useRef(nav);
  navRef.current = nav;
  const [levelStates, setLevelStates] = useState<Record<string, BlocklyState[]>>(
    () => Object.fromEntries(
      gameData.worlds.map(w => [w.id, w.levels.map(l => l.initial)])
    )
  );

  // The evaluator is constructed lazily once the Lean session is ready.
  const evaluatorRef = useRef<LevelEvaluator | null>(null);

  // Cancel-in-flight: each evaluate() call gets a sequence number.
  // When it resolves, we drop the result if a newer call has been issued.
  const evalSeqRef = useRef(0);

  // Source info from the most recent workspace-to-Lean conversion.
  // Used to map evaluation diagnostics back to individual blocks.
  const latestSourceInfoRef = useRef<SourceInfo[]>([]);

  // Run an evaluation, guarding against stale completions.
  // sourceInfo is captured per-call so that the per-block status update
  // uses the source info that matches the contribution being evaluated.
  const runEvaluation = useCallback(async (
    contribution: string,
    sourceInfo: SourceInfo[],
  ) => {
    const evaluator = evaluatorRef.current;
    if (!evaluator) return;

    const seq = ++evalSeqRef.current;
    setEvaluating(true);
    blocklyRef.current?.clearProofStatuses();

    let result: EvaluationResult | null = null;
    try {
      result = await evaluator.evaluate(contribution);
    } catch (err) {
      console.error('[App] evaluate threw:', err);
    }

    // Drop the result if a newer evaluation has been kicked off.
    if (seq !== evalSeqRef.current) {
      log('App', `Dropping stale evaluation result (seq ${seq} < ${evalSeqRef.current})`);
      return;
    }

    setEvaluating(false);
    setEvaluation(result);

    // Map diagnostics back to per-block proof statuses.
    if (result && sourceInfo.length > 0 && blocklyRef.current) {
      const errorDiags = result.diagnostics.filter(d => d.severity === 1);
      const statuses = new Map<string, ProofStatus>();
      for (const si of sourceInfo) {
        const blockStartLine = si.startLineCol[0];
        const blockEndLine = si.endLineCol[0];
        const hasError = errorDiags.some(d =>
          d.range.start.line <= blockEndLine && d.range.end.line >= blockStartLine,
        );
        statuses.set(si.id, hasError ? 'incomplete' : 'complete');
      }
      blocklyRef.current.updateProofStatuses(statuses);
    }
  }, []);

  // Pending code to evaluate once the Lean session becomes ready.
  const pendingEvalRef = useRef<{ leanCode: string; sourceInfo: SourceInfo[] } | null>(null);

  // Send the initial code for a level and wait for the full round-trip.
  const sendInitialCode = useCallback(async (worldId: string, levelIndex: number) => {
    const initialState = levelStatesRef.current[worldId][levelIndex];
    const { leanCode, sourceInfo } = workspaceToLean(initialState);
    latestSourceInfoRef.current = sourceInfo;
    // If user has already edited blocks, use their latest code instead.
    const pending = pendingEvalRef.current;
    if (pending) {
      pendingEvalRef.current = null;
      await runEvaluation(pending.leanCode, pending.sourceInfo);
    } else {
      await runEvaluation(leanCode, sourceInfo);
    }
    log('App', 'Initial Lean round-trip complete');
    setLeanReady(true);
  }, [runEvaluation]);

  // Wire up the evaluator once the session is ready, and kick off the
  // initial round-trip (or warm up Mathlib if we're on the world overview).
  useEffect(() => {
    leanSession.whenReady().then(async (manager) => {
      if (!evaluatorRef.current) {
        evaluatorRef.current = new LevelEvaluator(manager);
      }
      const currentNav = navRef.current;
      if (currentNav.kind === 'playing') {
        log('App', 'Session ready, sending initial level code...');
        await sendInitialCode(currentNav.worldId, currentNav.levelIndex);
      } else {
        // Warm up: run an empty contribution so Mathlib starts importing.
        log('App', 'Session ready (world overview), warming up with empty contribution...');
        await evaluatorRef.current.evaluate('');
        log('App', 'Warm-up complete');
      }
    });
  }, [sendInitialCode]);

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
    if (evaluatorRef.current && !leanReady) {
      sendInitialCode(worldId, levelIndex);
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

  async function copyStandaloneSource() {
    const ws = blocklyRef.current?.saveWorkspace();
    if (!ws || !evaluatorRef.current) return;
    const { leanCode } = workspaceToLean(ws);
    const fullSource = evaluatorRef.current.assembleStandaloneSource(leanCode);
    try {
      await navigator.clipboard.writeText(fullSource);
      setShowCopiedToast(true);
      setTimeout(() => setShowCopiedToast(false), 1500);
    } catch (err) {
      console.error('[App] clipboard write failed:', err);
    }
  }

  function onBlocklyChange(result: WorkspaceToLeanResult) {
    const { leanCode, sourceInfo } = result;
    latestSourceInfoRef.current = sourceInfo;

    if (!leanCode.trim()) return;

    // If the Lean session isn't ready yet, queue the latest code so it
    // gets evaluated as soon as loading finishes.
    if (!evaluatorRef.current || !leanReady) {
      pendingEvalRef.current = { leanCode, sourceInfo };
      return;
    }

    runEvaluation(leanCode, sourceInfo);
  }

  function onRequestGoals(
    _blockId: string,
    leanCode: string,
    sourceInfo: SourceInfo[],
    _blockSourceInfo: SourceInfo | undefined
  ) {
    if (!evaluatorRef.current) return;
    runEvaluation(leanCode, sourceInfo);
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

  // Derive view-friendly shapes from the single evaluation result.
  const goalsForView: InteractiveGoals | null = evaluation
    ? { goals: evaluation.leafGoals.map(lg => lg.goal) }
    : null;
  const hypKindMap = evaluation?.hypKindMap ?? new Map();
  const diagnostics = evaluation?.diagnostics ?? [];
  // proofComplete: null while checking, true on success, false otherwise.
  const proofComplete: boolean | null = evaluating
    ? null
    : evaluation?.complete ?? false;

  return <div className="app-root">
    <div className="navbar">
      <div className="navbar-left">
        <button className="navbar-btn" onClick={goBack} title="Back to worlds">&#x25C0;</button>
        <button className="navbar-btn" onClick={resetCurrentLevel} title="Reset level">&#x21BB;</button>
        <button
          className="navbar-btn"
          onClick={() => setShowIntro(true)}
          disabled={!currentLevel.introduction}
          title={currentLevel.introduction ? 'Show introduction' : 'No introduction for this level'}
        >&#x2139;</button>
        <button
          className="navbar-btn"
          onClick={copyStandaloneSource}
          title="Copy standalone Lean source to clipboard"
        >&#x1F41B;</button>
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
          {!leanReady ? (
            <span className="proof-checking">Loading Lean...</span>
          ) : proofComplete === null ? (
            <span className="proof-checking">Checking...</span>
          ) : proofComplete ? (
            <span className="proof-complete">Proof complete!</span>
          ) : (
            <span className="proof-incomplete">Proof incomplete</span>
          )}
        </div>
        {!leanReady ? (
          <div className="goals-loading">
            <div className="spinner" />
          </div>
        ) : evaluating && !evaluation ? (
          <div className="goals-loading">
            <div className="spinner" />
            <span>Loading goals...</span>
          </div>
        ) : (
          <Goals
            goals={goalsForView}
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
    {showCopiedToast && (
      <div className="toast">Copied!</div>
    )}
    {showIntro && currentLevel.introduction && (
      <div className="modal-backdrop" onClick={() => setShowIntro(false)}>
        <div className="modal" onClick={(e) => e.stopPropagation()}>
          <button
            className="modal-close"
            onClick={() => setShowIntro(false)}
            title="Close"
          >&times;</button>
          <div className="modal-body markdown-body">
            <ReactMarkdown>{currentLevel.introduction}</ReactMarkdown>
          </div>
        </div>
      </div>
    )}
  </div>;
}

export default App
