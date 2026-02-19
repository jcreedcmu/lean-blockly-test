import * as blockly from 'blockly';
import * as blocks from './blocks';
/*
Adapted from https://github.com/aneilmac/blockly-plugin-lean under the Apache 2.0 license
*/

type BlockItem = { kind: 'block'; type: string };
type CategoryItem = { kind: 'category'; name: string; contents: BlockItem[] };

const LeanTacticsCategory: CategoryItem = {
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
      type: 'tactic_ring_nf',
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
      type: 'tactic_have',
    },
    {
      kind: 'block',
      type: 'tactic_sorry',
    },
    {
      kind: 'block',
      type: 'tactic_other',
    },
    ...blocks.singleArgTactics.map(t => ({ kind: 'block' as const, type: `tactic_${t.name}` }))
  ],
};

const LeanVariableCategory: CategoryItem = {
  kind: 'category',
  name: 'Variables',
  contents: [
    {
      kind: 'block',
      type: 'prop_declaration',
    },
  ]
};

const LeanValueCategory: CategoryItem = {
  kind: 'category',
  name: 'Values',
  contents: [
    {
      kind: 'block',
      type: 'prop',
    },
  ],
};

const allCategories: CategoryItem[] = [
  LeanTacticsCategory,
  LeanVariableCategory,
  LeanValueCategory,
];

export const toolbox: blockly.utils.toolbox.ToolboxDefinition = {
  kind: 'categoryToolbox',
  contents: allCategories,
};

/**
 * Create a filtered toolbox containing only the specified block types.
 * Categories with no matching blocks are omitted.
 */
export function filterToolbox(allowedBlocks: string[]): blockly.utils.toolbox.ToolboxDefinition {
  const allowedSet = new Set(allowedBlocks);

  const filteredCategories = allCategories
    .map(category => ({
      ...category,
      contents: category.contents.filter(block => allowedSet.has(block.type))
    }))
    .filter(category => category.contents.length > 0);

  return {
    kind: 'categoryToolbox',
    contents: filteredCategories,
  };
}
