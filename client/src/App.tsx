import { useCallback, useEffect, useRef, useState } from 'react'
import * as React from 'react'

// Local imports
import { Blockly, BlocklyHandle, BlocklyState } from './Blockly.tsx';
import type { WorkspaceToLeanResult, SourceInfo } from './workspaceToLean';
import { Goals } from './infoview';
import './infoview/infoview.css';
import type { InteractiveGoals } from '@leanprover/infoview-api';
import { connect as lspConnect } from './LeanLspClient';
import { LeanRpcSession } from './LeanRpcSession';
import { example as example1 } from './examples/example-1.ts';
import { example as example2 } from './examples/example-2.ts';
import { example as example3 } from './examples/example-3.ts';
import { example as example4 } from './examples/example-4.ts';

type LevelDefinition = {
  name: string;
  initial: BlocklyState;
  allowedBlocks?: string[];  // If undefined, all blocks are available
};

const levelDefinitions: LevelDefinition[] = [
  {
    name: "Use Hypothesis",
    initial: example1,
    allowedBlocks: ['tactic_apply', 'prop'],
  },
  {
    name: "Reflexivity",
    initial: example2,
    allowedBlocks: ['tactic_refl'],
  },
  {
    name: "Rewrite",
    initial: example3,
    allowedBlocks: ['tactic_rw', 'prop'],
  },
  {
    name: "Limit Example",
    initial: example4,
  },
];

// CSS
import './css/App.css'

// Virtual document URI for Blockly code
const BLOCKLY_DOC_URI = 'file:///blockly/Blockly.lean';

function App() {
  const [goals, setGoals] = useState<InteractiveGoals | null>(null);
  const [goalsLoading, setGoalsLoading] = useState(false);
  const [proofComplete, setProofComplete] = useState<boolean | null>(null); // null = checking, true = complete, false = incomplete
  const blocklyRef = useRef<BlocklyHandle>(null);
  const [currentLevelIndex, setCurrentLevelIndex] = useState(0);
  const [levelStates, setLevelStates] = useState<BlocklyState[]>(
    () => levelDefinitions.map(ex => ex.initial)
  );

  // RPC session for Blockly code
  const rpcSessionRef = useRef<LeanRpcSession | null>(null);
  const [rpcManagerReady, setRpcManagerReady] = useState(false);

  // Track latest goals for proof status updates
  const latestGoalsRef = useRef<InteractiveGoals | null>(null);

  // Function to update proof status based on current goals and diagnostics
  const updateProofStatus = useCallback(() => {
    if (!rpcSessionRef.current) return;

    const hasErrors = rpcSessionRef.current.hasErrors();
    const diagnostics = rpcSessionRef.current.getDiagnostics();
    const currentGoals = latestGoalsRef.current;

    console.log('[updateProofStatus] Has errors:', hasErrors, 'Goals:', currentGoals?.goals?.length ?? 'null');
    console.log('[updateProofStatus] Diagnostics:', diagnostics);

    // Don't update status if we don't have goals data yet (still checking)
    if (currentGoals === null) return;

    // Proof is complete only if there are no goals AND no errors
    const noGoals = currentGoals.goals.length === 0;
    const isComplete = noGoals && !hasErrors;
    setProofComplete(isComplete);
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

      session.setDiagnosticsCallback((diagnostics) => {
        console.log('[App] Diagnostics changed:', diagnostics.length, 'items');
        updateProofStatus();
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
  }, [updateProofStatus]);

  function switchToLevel(newIndex: number) {
    if (newIndex === currentLevelIndex) return;

    // Save current workspace state
    const currentState = blocklyRef.current?.saveWorkspace();
    if (currentState) {
      setLevelStates(prev => {
        const updated = [...prev];
        updated[currentLevelIndex] = currentState;
        return updated;
      });
    }

    // Load the new level
    blocklyRef.current?.loadWorkspace(levelStates[newIndex]);
    setCurrentLevelIndex(newIndex);
  }

  function resetCurrentLevel() {
    const initialState = levelDefinitions[currentLevelIndex].initial;
    blocklyRef.current?.loadWorkspace(initialState);
    setLevelStates(prev => {
      const updated = [...prev];
      updated[currentLevelIndex] = initialState;
      return updated;
    });
  }

  function onBlocklyChange(result: WorkspaceToLeanResult) {
    const { leanCode } = result;
    const fullCode = prelude + leanCode;

    // Check proof status by fetching goals for the entire file
    if (rpcSessionRef.current) {
      setProofComplete(null); // Set to "checking" state

      console.log('[onBlocklyChange] Fetching goals for file');

      (async () => {
        try {
          const goals = await rpcSessionRef.current!.getGoals(fullCode);
          console.log('[onBlocklyChange] Goals:', goals);

          // Store goals for later reference (diagnostics callback can update status)
          latestGoalsRef.current = goals;

          // Also update displayed goals
          setGoals(goals);

          // Update proof status based on current goals and diagnostics
          updateProofStatus();
        } catch (err) {
          console.error('[onBlocklyChange] Error checking proof status:', err);
          setProofComplete(false);
        }
      })();
    }
  }

  const prelude = `import Mathlib

def FunLimAt (f : ℝ → ℝ) (L : ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ≠ c, |x - c| < δ → |f x - L| < ε

`;

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

  const myStyle: React.CSSProperties = {
    position: 'absolute',
    top: 0, left: 0, right: 0, bottom: 0,
    overflow: 'hidden',
  };
  const kid1: React.CSSProperties = {
    display: 'flex',
    flexDirection: 'row',
    overflow: 'hidden',
    height: '100%',
  };
  const blocklyContainer: React.CSSProperties = {
    flexGrow: 1,
  };

  return <div style={myStyle}>
    <div style={kid1}>
      <div className="buttons">
        {levelDefinitions.map((ex, i) => (
          <button
            key={i}
            onClick={() => switchToLevel(i)}
            style={{ fontWeight: i === currentLevelIndex ? 'bold' : 'normal' }}
          >
            {i + 1}
          </button>
        ))}
        <button onClick={resetCurrentLevel}>Reset</button>
        <button onClick={() => {
          const state = blocklyRef.current?.saveWorkspace();
          if (state) {
            navigator.clipboard.writeText(JSON.stringify(state, null, 2));
            console.log('Workspace copied to clipboard');
          }
        }}>Copy</button>
      </div>
      <Blockly
        ref={blocklyRef}
        style={blocklyContainer}
        onBlocklyChange={onBlocklyChange}
        onRequestGoals={onRequestGoals}
        initialData={levelDefinitions[0].initial}
        allowedBlocks={levelDefinitions[currentLevelIndex].allowedBlocks}
      />
      <div style={{ width: '300px', padding: '0.5em', borderLeft: '1px solid #ccc', overflow: 'auto' }}>
        <div className="proof-status">
          {proofComplete === null ? (
            <span className="proof-checking">Checking...</span>
          ) : proofComplete ? (
            <span className="proof-complete">✓ Proof complete!</span>
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
      </div>
    </div>
  </div>;
}

export default App
