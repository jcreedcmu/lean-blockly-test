import { useEffect, useRef, forwardRef, useImperativeHandle } from 'react'
import * as React from 'react'
import * as blockly from 'blockly'
import type { ContextMenuRegistry, BlockSvg } from 'blockly'
import * as blocks from './blocks'
import { FieldTheoremStatement } from './blocks'
import { toolbox as defaultToolbox, filterToolbox } from './toolbox'
import { workspaceToLean, WorkspaceToLeanResult, SourceInfo } from './workspaceToLean'
import { resolveMarkerLocation, MarkerLocation } from './markerResolve'
import { FieldProofStatus } from './FieldProofStatus'
import type { Pill, PillStatus, DiagnosticSource } from './proofStatusResolve'
import './FieldGoalMarker'
import { setMarkerClickHandler, isGoalPositionMarker } from './goalMarker'
import { CUSTOM_RENDERER_NAME } from './customRenderer'
import type { Affordance } from './LevelEvaluator'

export type BlocklyState = object;

export type TheoremBlockDisplay = string | null;

// Callback type for requesting goals for a specific block
export type GoalRequestHandler = (
  blockId: string,
  leanCode: string,
  sourceInfo: SourceInfo[],
  blockSourceInfo: SourceInfo | undefined
) => void;

// Fired when a goal-position marker pill is clicked. `location` is the
// resolved (contribution-relative) source range for the selected position,
// or undefined if it couldn't be resolved.
export type MarkerSelectHandler = (
  location: MarkerLocation | undefined,
  blockId: string,
  target: string,
) => void;

export type BlocklyHandle = {
  loadWorkspace: (data: BlocklyState) => void;
  saveWorkspace: () => BlocklyState | null;
  /** Enumerate the live proof-status pills (block id + governed target).
   * Read from the live workspace because pill fields aren't serialized. */
  getProofStatusPills: () => Pill[];
  /** Apply per-pill statuses, addressing each pill by (blockId, target). */
  updateProofStatuses: (statuses: PillStatus[]) => void;
  clearProofStatuses: () => void;
  /** Briefly flash the source a diagnostic was attributed to — either a
   * specific status pill or (fallback) a whole block. */
  flashDiagnosticSource: (source: DiagnosticSource) => void;
  /** For each entry, look up the lemma block whose THEOREM_NAME matches
   * the key and set its THEOREM_DECLARATION field's display override.
   * The override can be a multi-line string (rendered with tspans).
   * Pass `null` to restore the original serialized declaration text. */
  setTheoremDisplays: (displays: Map<string, TheoremBlockDisplay>) => void;
  /** Start a drag originating from a hypothesis. If `affordance` is
   * omitted, drags a bare `prop` block carrying the hyp name. Otherwise
   * wraps the hyp name in the tactic block corresponding to the
   * affordance's `kind`. */
  startHypDrag: (name: string, e: React.MouseEvent, affordance?: Affordance) => void;
  /** Start a drag originating from the goal target. Unlike hypotheses
   * there's no bare-drag mode here — the only drag surfaces are the
   * affordance buttons — so `affordance` is required. */
  startGoalDrag: (e: React.MouseEvent, affordance: Affordance) => void;
  /** Start a drag of a `conv` block containing an `enter` block pre-populated
   * with the given `enter` args (e.g. `['1', 'c']`), originating from a goal
   * subexpression. */
  startConvDrag: (enterArgs: string[], e: React.MouseEvent) => void;
  /** True if the user is currently dragging a block. */
  isDragging: () => boolean;
  /** Select a toolbox category by display name, opening its flyout. */
  openToolboxCategory: (name: string) => void;
};

function useBlockly(
  ref: React.RefObject<HTMLDivElement>,
  wsRef: React.MutableRefObject<blockly.WorkspaceSvg | null>,
  initialData: BlocklyState | undefined,
  onBlocklyChange?: BlocklyChangeHandler,
  onRequestGoals?: GoalRequestHandler,
  allowedBlocks?: string[],
  onMarkerSelect?: MarkerSelectHandler,
) {
  const handlerRef = useRef<BlocklyChangeHandler | undefined>(onBlocklyChange);
  const goalHandlerRef = useRef<GoalRequestHandler | undefined>(onRequestGoals);
  const markerSelectRef = useRef<MarkerSelectHandler | undefined>(onMarkerSelect);

  useEffect(() => {
    markerSelectRef.current = onMarkerSelect;
  }, [onMarkerSelect]);

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
      renderer: CUSTOM_RENDERER_NAME,
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

    // Goal-marker pills: clicking one selects a proof position. The pill
    // reports (blockId, target); we resolve that to a source location via the
    // input's child (or the synthesized empty-arm placeholder) and `sourceInfo`.
    setMarkerClickHandler((blockId, target) => {
      const state = blockly.serialization.workspaces.save(ws);
      const { leanCode, sourceInfo } = workspaceToLean(state);
      const location = resolveMarkerLocation(state, sourceInfo, blockId, target);

      // Debug: mark the resolved span in the generated contribution text so the
      // pill→position mapping is visible. End is inserted first so it doesn't
      // shift the start column.
      if (location) {
        const mark = (s: string, [line, col]: [number, number], m: string): string => {
          const lines = s.split('\n');
          if (line < 0 || line >= lines.length) return s;
          lines[line] = lines[line].slice(0, col) + m + lines[line].slice(col);
          return lines.join('\n');
        };
        let marked = mark(leanCode, location.endLineCol, '/-«end»-/');
        marked = mark(marked, location.startLineCol, '/-«start»-/');
        console.log(`[marker] position in text (${blockId}/${target || 'self'}):\n${marked}`);
      }

      // Highlight the clicked marker, clear the rest (any marker field type).
      for (const b of ws.getAllBlocks(false)) {
        for (const input of b.inputList) {
          for (const field of input.fieldRow) {
            if (isGoalPositionMarker(field)) {
              field.setSelected(b.id === blockId && field.getTarget() === target);
            }
          }
        }
      }

      markerSelectRef.current?.(location, blockId, target);
    });

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
      setMarkerClickHandler(null);
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
  onMarkerSelect?: MarkerSelectHandler;
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
    getProofStatusPills: () => {
      const pills: Pill[] = [];
      if (!wsRef.current) return pills;
      for (const block of wsRef.current.getAllBlocks(false)) {
        for (const input of block.inputList) {
          for (const field of input.fieldRow) {
            if (field instanceof FieldProofStatus) {
              pills.push({ blockId: block.id, target: field.getTarget() });
            }
          }
        }
      }
      return pills;
    },
    updateProofStatuses: (statuses: PillStatus[]) => {
      if (!wsRef.current) return;
      for (const { blockId, target, status } of statuses) {
        const block = wsRef.current.getBlockById(blockId);
        if (!block) continue;
        for (const input of block.inputList) {
          for (const field of input.fieldRow) {
            if (field instanceof FieldProofStatus && field.getTarget() === target) {
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
    flashDiagnosticSource: (source: DiagnosticSource) => {
      const block = wsRef.current?.getBlockById(source.blockId);
      if (!block) return;
      if (source.kind === 'pill') {
        for (const input of block.inputList) {
          for (const field of input.fieldRow) {
            if (field instanceof FieldProofStatus && field.getTarget() === source.target) {
              field.flashError();
            }
          }
        }
      } else {
        const svg = (block as BlockSvg).getSvgRoot();
        if (!svg) return;
        svg.classList.add('flashError');
        setTimeout(() => svg.classList.remove('flashError'), 700);
      }
    },
    setTheoremDisplays: (displays: Map<string, TheoremBlockDisplay>) => {
      if (!wsRef.current) return;
      for (const block of wsRef.current.getAllBlocks(false)) {
        if (block.type !== 'lemma') continue;
        const theoremName = block.getFieldValue('THEOREM_NAME');
        if (typeof theoremName !== 'string') continue;
        if (!displays.has(theoremName)) continue;
        const field = block.getField('THEOREM_DECLARATION');
        if (field instanceof FieldTheoremStatement) {
          field.setDisplayOverride(displays.get(theoremName)!);
        }
        (block as BlockSvg).render();
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
          case 'apply': return wrapSingle('tactic_apply', 'ARG');
          case 'specialize': return wrapSingle('tactic_specialize', 'HYP');
          case 'rewrite': return wrapSingle('tactic_rewrite', 'REWRITE_SOURCE');
          case 'choose': {
            const v = affordance.suggestedName;
            const outer = ws.newBlock('tactic_choose') as BlockSvg;
            // The witness name and the proof name are square text fields;
            // loadExtraState adds the second name slot, then we set values.
            (outer as unknown as { loadExtraState: (s: unknown) => void })
              .loadExtraState({ argCount: 1 });
            outer.setFieldValue(v, 'CHOSEN_NAME');
            outer.setFieldValue(`h${v}`, 'CHOSEN_NAME_1');
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
          case 'intro': {
            // Seed the NAME field with the bound variable name from the `∀`
            // so the user starts with `intro <name>`.
            const block = ws.newBlock('tactic_intro') as BlockSvg;
            block.setFieldValue(affordance.suggestedName, 'NAME');
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
    startConvDrag: (enterArgs: string[], e: React.MouseEvent) => {
      startBlockDrag(e, (ws) => {
        // An `enter` tactic carrying the bracketed path, nested inside a
        // `conv` block: dragging out gives `conv => enter [1, c]`.
        const enterBlock = ws.newBlock('tactic_enter') as BlockSvg;
        enterBlock.setFieldValue(`[${enterArgs.join(', ')}]`, 'ENTER_PATH');
        enterBlock.initSvg();
        enterBlock.render();
        const conv = ws.newBlock('tactic_conv') as BlockSvg;
        conv.getInput('BODY')!.connection!.connect(enterBlock.previousConnection!);
        conv.initSvg();
        conv.render();
        return conv;
      });
    },
    isDragging: () => wsRef.current?.isDragging() ?? false,
    openToolboxCategory: (name: string) => {
      const toolbox = wsRef.current?.getToolbox();
      if (!toolbox) return;
      const selected = toolbox.getSelectedItem() as { getName?: () => string } | null;
      if (selected?.getName?.() === name && toolbox.getFlyout()?.isVisible()) {
        return;
      }
      const toolboxWithItems = toolbox as typeof toolbox & {
        getToolboxItems?: () => Array<{
          isSelectable: () => boolean;
          getName?: () => string;
        }>;
      };
      const item = toolboxWithItems.getToolboxItems?.().find(candidate => {
        if (!candidate.isSelectable()) return false;
        return candidate.getName?.() === name;
      });
      if (!item) return;
      toolbox.clearSelection();
      toolbox.setSelectedItem(item as any);
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
    ws.scrollBoundsIntoView = () => { };

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

  useBlockly(
    blocklyRef,
    wsRef,
    props.initialData,
    props.onBlocklyChange,
    props.onRequestGoals,
    props.allowedBlocks,
    props.onMarkerSelect,
  );

  return <div style={props.style} ref={blocklyRef}></div>;
});
