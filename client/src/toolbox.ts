import * as blockly from 'blockly';
import * as blocks from './blocks';
/*
Adapted from https://github.com/aneilmac/blockly-plugin-lean under the Apache 2.0 license
*/

const LeanTacticsCategory = {
  kind: 'category',
  name: 'Tactics',
  contents: [
    {
      kind: 'block',
      type: 'lemma',
    },
    {
      kind: 'block',
      type: 'tactic_refl',
    },
    {
      kind: 'block',
      type: 'tactic_rw',
    },
    {
      kind: 'block',
      type: 'tactic_rw_at',
    },
    {
      kind: 'block',
      type: 'tactic_constructor',
    },
    {
      kind: 'block',
      type: 'tactic_show',
    },
    {
      kind: 'block',
      type: 'tactic_sorry',
    },
    ...blocks.singleArgTactics.map(t => ({ kind: 'block', type: `tactic_${t.name}` }))
  ],
};

const LeanVariableCategory = {
  kind: 'category',
  name: 'Variables',
  contents: [
    {
      kind: 'block',
      type: 'prop_declaration',
    },
  ]
};

const LeanValueCategory = {
  kind: 'category',
  name: 'Values',
  contents: [
    {
      kind: 'block',
      type: 'prop',
    },
  ],
};

export const toolbox: blockly.utils.toolbox.ToolboxDefinition = {
  kind: 'categoryToolbox',
  contents: [
    LeanTacticsCategory,
    LeanVariableCategory,
    LeanValueCategory,
  ],
};
