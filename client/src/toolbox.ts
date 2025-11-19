import * as blockly from 'blockly';

/*
Adapted from https://github.com/aneilmac/blockly-plugin-lean under the Apache 2.0 license
*/

const LeanTacticsCategory = {
  kind: 'category',
  name: 'Tactics',
  contents: [
    {
      kind: 'block',
      type: 'prop_declaration',
    },
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
      type: 'tactic_induction',
    },
    {
      kind: 'block',
      type: 'tactic_sorry',
    },
  ],
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
    LeanValueCategory,
  ],
};
