import { useEffect, useRef, JSX } from 'react'
import * as React from 'react'
import * as blockly from 'blockly'
import * as blocks from './blocks'
import * as toolboxDef from './toolbox'
import * as generator from './generator'

export type BlocklyState = object;

function useBlockly(
  ref: React.RefObject<HTMLDivElement>,
  initialData: BlocklyState | undefined,
  onBlocklyChange?: BlocklyChangeHandler,
) {
  const handlerRef = useRef<BlocklyChangeHandler | undefined>(onBlocklyChange);
  const wsRef = useRef<blockly.WorkspaceSvg | null>(null);

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

export function Blockly(props: BlocklyProps): JSX.Element {
  const blocklyRef = React.useRef(null);
  useBlockly(blocklyRef, props.initialData, props.onBlocklyChange);
  return <div style={props.style} ref={blocklyRef}></div>;
}
