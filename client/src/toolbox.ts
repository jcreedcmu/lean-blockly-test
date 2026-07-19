import * as blockly from 'blockly';
import { nasTheoremBlockSpecs } from './nasTheoremBlocks';

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
  fields?: Record<string, string>;
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
      type: 'tactic_let',
    },
    {
      kind: 'block',
      type: 'tactic_apply',
      id: 'tutorial-toolbox-apply',
    },
    {
      kind: 'block',
      type: 'tactic_have',
    },
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
      type: 'tactic_show',
    },
    {
      kind: 'block',
      type: 'tactic_conv',
    },
    {
      kind: 'block',
      type: 'tactic_sorry',
    },
    {
      kind: 'block',
      type: 'tactic_other',
    },
    // Blocks added on the clean branch that the curated order above did
    // not yet account for. They stay registered so levels that use them
    // (e.g. refl/ring_nf in the tutorial world) keep working.
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
      type: 'tactic_simp',
    },
    {
      kind: 'block',
      type: 'tactic_conclude',
    },
    {
      kind: 'block',
      type: 'tactic_rewrite_at',
    },
    {
      kind: 'block',
      type: 'tactic_transform',
    },
    {
      kind: 'block',
      type: 'tactic_exact',
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

const LeanDefinitionsCategory: CategoryItem = {
  kind: 'category',
  name: 'Definitions',
  contents: [
    { kind: 'block', type: 'prop', fields: { PROP_NAME: 'FunLimAt' } },
    { kind: 'block', type: 'prop', fields: { PROP_NAME: 'FunCont' } },
    { kind: 'block', type: 'prop', fields: { PROP_NAME: 'SeqLim' } },
  ],
};

const LeanTheoremsCategory: CategoryItem = {
  kind: 'category',
  name: 'Theorems',
  contents: [
    ...nasTheoremBlockSpecs.map(spec => ({
      kind: 'block' as const,
      type: spec.type,
      inputs: Object.fromEntries(spec.args.map(arg => [
        arg.name,
        {
          shadow: {
            type: 'prop',
            fields: { PROP_NAME: arg.defaultValue },
          },
        },
      ])),
    })),
  ],
};

const allCategories: CategoryItem[] = [
  LeanTacticsCategory,
  LeanTheoremsCategory,
  LeanDefinitionsCategory,
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
