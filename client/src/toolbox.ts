import * as blockly from 'blockly';

/*
Adapted from https://github.com/aneilmac/blockly-plugin-lean under the Apache 2.0 license
*/

type ShadowBlock = {
  type: string;
  fields?: Record<string, string>;
};

type BlockItem = {
  kind: 'block';
  type: string;
  id?: string;
  inputs?: Record<string, { shadow: ShadowBlock }>;
};
type CategoryItem = {
  kind: 'category';
  name: string;
  contents: BlockItem[];
  cssconfig?: {
    row?: string;
    label?: string;
  };
};

const LeanTacticsCategory: CategoryItem = {
  kind: 'category',
  name: 'Tactics',
  cssconfig: {
    row: 'blocklyToolboxCategory tutorial-tactics-category-row',
    label: 'blocklyToolboxCategoryLabel tutorial-tactics-category-label',
  },
  contents: [
    {
      kind: 'block',
      type: 'tactic_unfold',
      inputs: { ARG: { shadow: { type: 'prop', fields: { PROP_NAME: 'h' } } } },
    },
    {
      kind: 'block',
      type: 'tactic_calc',
    },
    {
      kind: 'block',
      type: 'tactic_intro',
    },
    {
      kind: 'block',
      type: 'tactic_use',
    },
    {
      kind: 'block',
      type: 'tactic_rewrite',
    },
    {
      kind: 'block',
      type: 'tactic_apply',
      id: 'tutorial-toolbox-apply',
    },
    {
      kind: 'block',
      type: 'tactic_specialize',
    },
    {
      kind: 'block',
      type: 'tactic_choose',
    },
    {
      kind: 'block',
      type: 'tactic_at',
    },
    {
      kind: 'block',
      type: 'tactic_constructor',
    },
    {
      kind: 'block',
      type: 'tactic_have',
    },
    {
      kind: 'block',
      type: 'tactic_show',
    },
    {
      kind: 'block',
      type: 'tactic_sorry',
    },
    {
      kind: 'block',
      type: 'tactic_other',
    },
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

const LeanTheoremsCategory: CategoryItem = {
  kind: 'category',
  name: 'Theorems',
  contents: [
    {
      kind: 'block',
      type: 'term_archprop',
    },
  ],
};

const allCategories: CategoryItem[] = [
  LeanTacticsCategory,
  LeanTheoremsCategory,
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
