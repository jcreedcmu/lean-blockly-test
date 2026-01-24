import { useEffect, useRef, JSX, forwardRef, useImperativeHandle } from 'react'
import * as React from 'react'
import * as blockly from 'blockly'
import * as blocks from './blocks'
import * as toolboxDef from './toolbox'
import * as generator from './generator'

export type BlocklyState = object;

export type BlocklyHandle = {
  loadWorkspace: (data: BlocklyState) => void;
  saveWorkspace: () => BlocklyState | null;
};

function useBlockly(
  ref: React.RefObject<HTMLDivElement>,
  wsRef: React.MutableRefObject<blockly.WorkspaceSvg | null>,
  initialData: BlocklyState | undefined,
  onBlocklyChange?: BlocklyChangeHandler,
) {
  const handlerRef = useRef<BlocklyChangeHandler | undefined>(onBlocklyChange);

  useEffect(() => {
    handlerRef.current = onBlocklyChange;
  }, [onBlocklyChange]);

  useEffect(() => {
    if (!ref.current) return;

    blocks.defineBlocks();
    const toolbox = toolboxDef.toolbox;
    const leanGenerator = generator.mkLeanGenerator();

    const ws = blockly.inject(ref.current, {
      toolbox: toolbox,
      scrollbars: false,
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

    function changeListener() {
      if (handlerRef.current !== undefined) {
        handlerRef.current(leanGenerator.workspaceToCode(ws));
      }
    }
    ws.addChangeListener(changeListener);

    return () => {
      ws.removeChangeListener(changeListener);
      ws.dispose();
      wsRef.current = null;
    };
  }, []);

}

export type BlocklyChangeHandler = (code: string) => void;

export type BlocklyProps = {
  style: React.CSSProperties;
  initialData?: BlocklyState;
  onBlocklyChange?: BlocklyChangeHandler;
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
    }
  }), []);

  useBlockly(blocklyRef, wsRef, props.initialData, props.onBlocklyChange);

  return <div style={props.style} ref={blocklyRef}></div>;
});
