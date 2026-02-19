import { useEffect, useRef, forwardRef, useImperativeHandle } from 'react'
import * as React from 'react'
import * as blockly from 'blockly'
import type { ContextMenuRegistry, BlockSvg } from 'blockly'
import * as blocks from './blocks'
import { toolbox as defaultToolbox, filterToolbox } from './toolbox'
import { workspaceToLean, WorkspaceToLeanResult, SourceInfo } from './workspaceToLean'
import { FieldProofStatus, ProofStatus } from './FieldProofStatus'

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
  startHypDrag: (name: string, e: React.MouseEvent) => void;
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

    function changeListener() {
      if (handlerRef.current !== undefined) {
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
    startHypDrag: (name: string, e: React.MouseEvent) => {
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

      // Create a prop block with the hypothesis name
      const block = ws.newBlock('prop') as BlockSvg;
      block.setFieldValue(name, 'PROP_NAME');
      block.initSvg();
      block.render();
      block.moveTo(wsCoord);

      // Create a Blockly Dragger and start the drag
      const dragger = new blockly.dragging.Dragger(block, ws);
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
    },
  }), []);

  useBlockly(blocklyRef, wsRef, props.initialData, props.onBlocklyChange, props.onRequestGoals, props.allowedBlocks);

  return <div style={props.style} ref={blocklyRef}></div>;
});
