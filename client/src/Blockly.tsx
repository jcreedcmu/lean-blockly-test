import { useCallback, useEffect, useRef, useState, JSX } from 'react'
import * as React from 'react'
import * as blockly from 'blockly'
import * as blocks from './blocks'
import * as toolboxDef from './toolbox'
import * as generator from './generator'

function useBlockly(ref: React.RefObject<HTMLDivElement>, onBlocklyChange?: BlocklyChangeHandler) {
  const handlerRef: React.RefObject<BlocklyChangeHandler | undefined> = useRef(onBlocklyChange);

  useEffect(() => {

    if (!ref.current) {
      return;
    }

    if ((ref.current as any).alreadyInjected) {
      console.log('already injected');
      return;
    }

    (ref.current as any).alreadyInjected = true;

    blocks.defineBlocks();
    const toolbox = toolboxDef.toolbox;
    const leanGenerator = generator.mkLeanGenerator();
    const ws = blockly.inject(ref.current, {
      toolbox: toolbox,
      scrollbars: false,
    });

    function localChangeListener() {
      console.log('testing ');
      if (handlerRef.current !== undefined) {

        console.log('calling ', onBlocklyChange);
        (handlerRef.current)(leanGenerator.workspaceToCode(ws));
      }
    }
    console.log('XXX adding');
    ws.addChangeListener(localChangeListener);
    return () => {
      console.log('XXX destroying');
    }
  });

  useEffect(() => {
    console.log('setting ', onBlocklyChange);
    handlerRef.current = onBlocklyChange;
  }, [onBlocklyChange]);

}

export type BlocklyChangeHandler = (code: string) => void;

export function Blockly(props: { style: React.CSSProperties, onBlocklyChange?: BlocklyChangeHandler }): JSX.Element {
  const blocklyRef = React.useRef(null);
  useBlockly(blocklyRef, props.onBlocklyChange);
  return <div style={props.style} ref={blocklyRef}></div>;
}
