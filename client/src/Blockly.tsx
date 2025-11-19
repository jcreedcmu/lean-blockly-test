import { useCallback, useEffect, useRef, useState, JSX } from 'react'
import * as React from 'react'
import * as blockly from 'blockly'
import * as blocks from './blocks'
import * as toolboxDef from './toolbox'
import * as generator from './generator'

const serialized = { "blocks": { "languageVersion": 0, "blocks": [{ "type": "lemma", "id": "3yAUmdNL2=WYh]Gxi)]X", "x": 96, "y": 40, "fields": { "THEOREM_NAME": "away", "THEOREM_DECLARATION": "(y^2 - 1) / (y - 1) = y + 1" }, "inputs": { "VARIABLES": { "block": { "type": "prop_declaration", "id": "!nj)-l!RB`?Qhr_!_Q7^", "fields": { "VARIABLE_DECL": "y", "VARIABLE_DEF": "ℝ" }, "next": { "block": { "type": "prop_declaration", "id": "lgvV;Skrw^oI04hI%Pc)", "fields": { "VARIABLE_DECL": "hy", "VARIABLE_DEF": "y ≠ 1" } } } } }, "LEMMA_PROOF": { "block": { "type": "tactic_other", "id": "k}|H70s[,ot=/1U@K_,;", "fields": { "PROP_NAME": "grind" } } } } }, { "type": "lemma", "id": "DemnP%+kbpZdIIe~0(3W", "x": 79, "y": 258, "fields": { "THEOREM_NAME": "fun_limit_fact", "THEOREM_DECLARATION": "FunLimAt (fun x => (x^2 - 1) / (x - 1)) 2 1" }, "inputs": { "LEMMA_PROOF": { "block": { "type": "tactic_unfold", "id": "4jk;hHJ|_aSp.)2PU`Gc", "inputs": { "ARG": { "block": { "type": "prop", "id": "Mojm{fSn$rJvFC81z{h(", "fields": { "PROP_NAME": "FunLimAt" } } } }, "next": { "block": { "type": "tactic_intro", "id": "^=/m!cJjN6xgQ.RpEN]y", "inputs": { "ARG": { "block": { "type": "prop", "id": "Y(gRn,NBi~2+wLabs!@A", "fields": { "PROP_NAME": "ε" } } } }, "next": { "block": { "type": "tactic_intro", "id": "MK{[.T(RH!$~`CKvXmL1", "inputs": { "ARG": { "block": { "type": "prop", "id": "mgxS^6SsXB-}9:6^cQ?!", "fields": { "PROP_NAME": "hε" } } } } } } } } } } } }, { "type": "tactic_other", "id": "3#gT|oNu-}[}3uB_a.2U", "x": 550, "y": 330, "fields": { "PROP_NAME": "simp" }, "next": { "block": { "type": "tactic_rw", "id": "f5piLnWwQvlx,Ki5WTp4", "fields": { "DIRECTION_TYPE": "RIGHT" }, "inputs": { "REWRITE_SOURCE": { "block": { "type": "prop", "id": "G.]vQSXK]?]G9T#)g+sJ", "fields": { "PROP_NAME": "away hy" } } } }, "next": { "block": { "type": "tactic_sorry", "id": "@K~Y4S*0PfN%]*ZQ7thS" } } } } }, { "type": "tactic_other", "id": "m.6n,uHODs!Ns?ycFg`M", "x": 639, "y": 154, "fields": { "PROP_NAME": "linarith" }, "next": { "block": { "type": "tactic_intro", "id": "4Nh1ti#nH_#d-A3V$e|_", "inputs": { "ARG": { "block": { "type": "prop", "id": ":un028QY,n#E7%_%,]4[", "fields": { "PROP_NAME": "y" } } } }, "next": { "block": { "type": "tactic_intro", "id": "fxEi-:)M^j3ee76?Z9l+", "inputs": { "ARG": { "block": { "type": "prop", "id": "U:5}c2^h7F]d8+hh(q}8", "fields": { "PROP_NAME": "hy" } } } }, "next": { "block": { "type": "tactic_intro", "id": "]@#*lMzE^dbkiR]{PhGo", "inputs": { "ARG": { "block": { "type": "prop", "id": "*ww_S)5(YZG^Uc84eUlv", "fields": { "PROP_NAME": "hy2" } } } } } } } } } } }] } };

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
    blockly.serialization.workspaces.load(serialized, ws);

    // DEBUGGING LOAD AND SAVE
    (window as any).saveWorkspace = () => {
      const state = blockly.serialization.workspaces.save(ws);
      localStorage.setItem('workspace-state', JSON.stringify(state));
    }
    (window as any).loadWorkspace = () => {
      const state = JSON.parse(localStorage.getItem('workspace-state'));
      blockly.serialization.workspaces.load(state, ws);
    }

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
