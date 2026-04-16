import { useEffect, useRef, forwardRef, useImperativeHandle } from 'react'
import * as React from 'react'
import * as blockly from 'blockly'
import type { ContextMenuRegistry, BlockSvg } from 'blockly'
import * as blocks from './blocks'
import { toolbox as defaultToolbox, filterToolbox } from './toolbox'
import { workspaceToLean, WorkspaceToLeanResult, SourceInfo } from './workspaceToLean'
import { FieldProofStatus, ProofStatus } from './FieldProofStatus'
import type { Affordance } from './LevelEvaluator'

export type BlocklyState = object;

// Callback type for requesting goals for a specific block
export type GoalRequestHandler = (
  blockId: string,
  leanCode: string,
  sourceInfo: SourceInfo[],
  blockSourceInfo: SourceInfo | undefined
) => void;

export type BlocklyHandle = {
  loadWorkspace: (data: BlocklyState) => void;
  saveWorkspace: () => BlocklyState | null;
  updateProofStatuses: (statuses: Map<string, ProofStatus>) => void;
  clearProofStatuses: () => void;
  /** Start a drag originating from a hypothesis. If `affordance` is
   * omitted, drags a bare `prop` block carrying the hyp name. Otherwise
   * wraps the hyp name in the tactic block corresponding to the
   * affordance's `kind`. */
  startHypDrag: (name: string, e: React.MouseEvent, affordance?: Affordance) => void;
  /** Start a drag originating from the goal target. Unlike hypotheses
   * there's no bare-drag mode here — the only drag surfaces are the
   * affordance buttons — so `affordance` is required. */
  startGoalDrag: (e: React.MouseEvent, affordance: Affordance) => void;
};

function useBlockly(
  ref: React.RefObject<HTMLDivElement>,
  wsRef: React.MutableRefObject<blockly.WorkspaceSvg | null>,
  initialData: BlocklyState | undefined,
  onBlocklyChange?: BlocklyChangeHandler,
  onRequestGoals?: GoalRequestHandler,
  allowedBlocks?: string[],
) {
  const handlerRef = useRef<BlocklyChangeHandler | undefined>(onBlocklyChange);
  const goalHandlerRef = useRef<GoalRequestHandler | undefined>(onRequestGoals);

  useEffect(() => {
    handlerRef.current = onBlocklyChange;
  }, [onBlocklyChange]);

  useEffect(() => {
    goalHandlerRef.current = onRequestGoals;
  }, [onRequestGoals]);

  // Update toolbox when allowedBlocks changes
  useEffect(() => {
    if (!wsRef.current) return;
    const toolbox = allowedBlocks ? filterToolbox(allowedBlocks) : defaultToolbox;
    wsRef.current.updateToolbox(toolbox);
  }, [allowedBlocks]);

  useEffect(() => {
    if (!ref.current) return;

    blocks.defineBlocks();
    const toolbox = allowedBlocks ? filterToolbox(allowedBlocks) : defaultToolbox;

    const ws = blockly.inject(ref.current, {
      toolbox: toolbox,
      scrollbars: false,
      renderer: 'zelos',
      theme: blockly.Themes.Zelos,
      grid: { spacing: 64, colour: '#ccc', length: 5 },
      move: { drag: true, scrollbars: true, wheel: true }
    });
    wsRef.current = ws;
    if (initialData) {
      blockly.serialization.workspaces.load(initialData, ws);
    }

    // DEBUGGING LOAD AND SAVE
    (window as any).workspace = ws;
    (window as any).saveWorkspace = () => {
      const state = blockly.serialization.workspaces.save(ws);
      (window as any).currentState = JSON.stringify(state);
      localStorage.setItem('workspace-state', JSON.stringify(state));
    };
    (window as any).loadWorkspace = () => {
      const state = JSON.parse(localStorage.getItem('workspace-state'));
      blockly.serialization.workspaces.load(state, ws);
    };

    // Register context menu item for showing goal state
    const showGoalsMenuItem: ContextMenuRegistry.RegistryItem = {
      displayText: 'Show Goal State',
      preconditionFn: () => 'enabled',
      callback: (scope) => {
        const block = scope.block as BlockSvg | undefined;
        if (!block) {
          console.log('[ShowGoals] No block in scope');
          return;
        }

        const blockId = block.id;
        console.log('[ShowGoals] Block clicked:', blockId);
        console.log('[ShowGoals] Block type:', block.type);

        // Get current workspace state and convert to Lean
        const state = blockly.serialization.workspaces.save(ws);
        const { leanCode, sourceInfo } = workspaceToLean(state);

        console.log('[ShowGoals] Generated Lean code:');
        console.log(leanCode);
        console.log('[ShowGoals] Source info:', sourceInfo);

        // Find source info for this block
        const blockSourceInfo = sourceInfo.find(s => s.id === blockId);
        console.log('[ShowGoals] Block source info:', blockSourceInfo);

        if (blockSourceInfo) {
          console.log('[ShowGoals] Block position - start:', blockSourceInfo.startLineCol, 'end:', blockSourceInfo.endLineCol);
        } else {
          console.log('[ShowGoals] No source info found for block', blockId);
        }

        // Call the handler if provided
        if (goalHandlerRef.current) {
          goalHandlerRef.current(blockId, leanCode, sourceInfo, blockSourceInfo);
        }
      },
      scopeType: blockly.ContextMenuRegistry.ScopeType.BLOCK,
      id: 'showGoalState',
      weight: 100,
    };

    blockly.ContextMenuRegistry.registry.register(showGoalsMenuItem);

    function changeListener(e: blockly.Events.Abstract) {
      // Only re-evaluate when block content actually changes, not on
      // UI events like selections, flyout toggles, or viewport changes.
      if (!e.isUiEvent && handlerRef.current !== undefined) {
        const state = blockly.serialization.workspaces.save(ws);
        handlerRef.current(workspaceToLean(state));
      }
    }
    ws.addChangeListener(changeListener);

    return () => {
      ws.removeChangeListener(changeListener);
      blockly.ContextMenuRegistry.registry.unregister('showGoalState');
      ws.dispose();
      wsRef.current = null;
    };
  }, []);

}

export type BlocklyChangeHandler = (result: WorkspaceToLeanResult) => void;

export type BlocklyProps = {
  style: React.CSSProperties;
  initialData?: BlocklyState;
  onBlocklyChange?: BlocklyChangeHandler;
  onRequestGoals?: GoalRequestHandler;
  allowedBlocks?: string[];
};

export const Blockly = forwardRef<BlocklyHandle, BlocklyProps>((props, ref) => {
  const blocklyRef = useRef<HTMLDivElement>(null);
  const wsRef = useRef<blockly.WorkspaceSvg | null>(null);

  useImperativeHandle(ref, () => ({
    loadWorkspace: (data: BlocklyState) => {
      if (wsRef.current) {
        blockly.serialization.workspaces.load(data, wsRef.current);
      }
    },
    saveWorkspace: () => {
      if (wsRef.current) {
        return blockly.serialization.workspaces.save(wsRef.current);
      }
      return null;
    },
    updateProofStatuses: (statuses: Map<string, ProofStatus>) => {
      if (!wsRef.current) return;
      for (const [blockId, status] of statuses) {
        const block = wsRef.current.getBlockById(blockId);
        if (!block) continue;
        for (const input of block.inputList) {
          for (const field of input.fieldRow) {
            if (field instanceof FieldProofStatus) {
              field.setStatus(status);
            }
          }
        }
      }
    },
    clearProofStatuses: () => {
      if (!wsRef.current) return;
      for (const block of wsRef.current.getAllBlocks(false)) {
        for (const input of block.inputList) {
          for (const field of input.fieldRow) {
            if (field instanceof FieldProofStatus) {
              field.setStatus('unknown');
            }
          }
        }
      }
    },
    startHypDrag: (name: string, e: React.MouseEvent, affordance?: Affordance) => {
      startBlockDrag(e, (ws) => {
        // Helper: a fully-initialized `prop` block with a name field.
        const propWithName = (propName: string): BlockSvg => {
          const b = ws.newBlock('prop') as BlockSvg;
          b.setFieldValue(propName, 'PROP_NAME');
          b.initSvg();
          b.render();
          return b;
        };
        // Helper: wrap one inner prop on a named input of an outer tactic.
        const wrapSingle = (tacticType: string, inputName: string): BlockSvg => {
          const outer = ws.newBlock(tacticType) as BlockSvg;
          outer.getInput(inputName)!.connection!.connect(
            propWithName(name).outputConnection!);
          outer.initSvg();
          outer.render();
          return outer;
        };

        if (!affordance) return propWithName(name);

        switch (affordance.kind) {
          case 'apply':   return wrapSingle('tactic_apply', 'ARG');
          case 'rewrite': return wrapSingle('tactic_rewrite', 'REWRITE_SOURCE');
          case 'choose': {
            // tactic_choose has two inputs: CHOSEN (new variable names)
            // and SOURCE (the hypothesis being destructed). Mathlib's
            // `choose` on `h : ∃ c, P c` introduces *two* binders — the
            // witness `c` and the proof `P c` — so we seed CHOSEN with
            // both, using `<c> h<c>` (e.g. `c hc`) as a sensible default.
            const v = affordance.suggestedName;
            const outer = ws.newBlock('tactic_choose') as BlockSvg;
            outer.getInput('CHOSEN')!.connection!.connect(
              propWithName(`${v} h${v}`).outputConnection!);
            outer.getInput('SOURCE')!.connection!.connect(
              propWithName(name).outputConnection!);
            outer.initSvg();
            outer.render();
            return outer;
          }
          case 'use':
            // 'use' is a target-side affordance, not applicable to a hyp
            // drag — fall through to a bare prop so we never crash if
            // something mis-wired reaches us.
            return propWithName(name);
        }
      });
    },
    startGoalDrag: (e: React.MouseEvent, affordance: Affordance) => {
      startBlockDrag(e, (ws) => {
        switch (affordance.kind) {
          case 'use': {
            const block = ws.newBlock('tactic_use') as BlockSvg;
            block.initSvg();
            block.render();
            return block;
          }
          case 'apply':
          case 'rewrite':
          case 'choose': {
            // These are hyp-side affordances; they have no goal-side
            // rendering today. Fall through to a no-op `prop` block
            // rather than crash if something mis-wired reaches us.
            const block = ws.newBlock('prop') as BlockSvg;
            block.initSvg();
            block.render();
            return block;
          }
        }
      });
    },
  }), []);

  /**
   * Shared machinery for starting a drag of a newly-created block, used
   * by the infoview affordances (drag-from-hypothesis, drag-from-goal).
   * The caller supplies a function that creates and initializes the block;
   * this wrapper handles positioning, overflow/scroll hacks, and the
   * Dragger lifecycle.
   */
  function startBlockDrag(
    e: React.MouseEvent,
    createBlock: (ws: blockly.WorkspaceSvg) => BlockSvg,
  ) {
    const ws = wsRef.current;
    if (!ws) return;

    // Suppress Blockly's auto-scroll that fires when the new block
    // receives focus during startDrag → moveToDragLayer → focusNode.
    const origScroll = ws.scrollBoundsIntoView.bind(ws);
    ws.scrollBoundsIntoView = () => {};

    // Allow the drag surface SVG to render outside the Blockly pane
    // by temporarily removing overflow clipping and raising z-index.
    const injectionDiv = ws.getInjectionDiv() as HTMLElement;
    const container = blocklyRef.current!;
    const gameArea = container.closest('.game-area') as HTMLElement | null;
    const saved = {
      injOverflow: injectionDiv.style.overflow,
      contZIndex: container.style.zIndex,
      contPosition: container.style.position,
      gameOverflow: gameArea?.style.overflow ?? '',
    };
    injectionDiv.style.overflow = 'visible';
    container.style.zIndex = '10';
    container.style.position = 'relative';
    if (gameArea) gameArea.style.overflow = 'visible';

    // Convert screen position to workspace coordinates
    const screenCoord = new blockly.utils.Coordinate(e.clientX, e.clientY);
    const wsCoord = blockly.utils.svgMath.screenToWsCoordinates(ws, screenCoord);

    const dragBlock = createBlock(ws);

    const size = dragBlock.getHeightWidth();
    dragBlock.moveTo(new blockly.utils.Coordinate(
      wsCoord.x - size.width / 2,
      wsCoord.y - size.height / 2,
    ));

    // Create a Blockly Dragger and start the drag
    const dragger = new blockly.dragging.Dragger(dragBlock, ws);
    const nativeEvent = e.nativeEvent as PointerEvent;
    dragger.onDragStart(nativeEvent);

    const startX = e.clientX;
    const startY = e.clientY;

    function onPointerMove(ev: PointerEvent) {
      const delta = new blockly.utils.Coordinate(ev.clientX - startX, ev.clientY - startY);
      dragger.onDrag(ev, delta);
    }

    function cleanup() {
      document.removeEventListener('pointermove', onPointerMove);
      document.removeEventListener('pointerup', onPointerUp);
      // Restore scroll behaviour and overflow/z-index
      ws.scrollBoundsIntoView = origScroll;
      injectionDiv.style.overflow = saved.injOverflow;
      container.style.zIndex = saved.contZIndex;
      container.style.position = saved.contPosition;
      if (gameArea) gameArea.style.overflow = saved.gameOverflow;
    }

    function onPointerUp(ev: PointerEvent) {
      dragger.onDragEnd(ev);
      cleanup();
    }

    document.addEventListener('pointermove', onPointerMove);
    document.addEventListener('pointerup', onPointerUp);
  }

  useBlockly(blocklyRef, wsRef, props.initialData, props.onBlocklyChange, props.onRequestGoals, props.allowedBlocks);

  return <div style={props.style} ref={blocklyRef}></div>;
});
