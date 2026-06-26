import * as blockly from 'blockly';
import type { BlockSvg } from 'blockly';

type Row = blockly.blockRendering.Row;

/** Extra vertical space (px) added to the leg directly below the `lemma`
 * block's proof gap, to make room for a better-aligned proof-status
 * indicator. Tune this number to taste. */
const GOAL_STATUS_EXTRA_SPACE = 16;

function needsExtraSpace(block: blockly.Block, prev: blockly.blockRendering.Row): boolean {
  if (block.type === 'lemma' && prev.hasStatement) return true;
  if (block.type === 'tactic_constructor' && prev.hasStatement) return true;
  if (block.type === 'tactic_show' && prev.hasStatement) return true;
}

class CustomRenderInfo extends blockly.zelos.RenderInfo {
  getSpacerRowHeight_(prev: Row, next: Row): number {
    const base = super.getSpacerRowHeight_(prev, next);
    // Only the lemma (theorem) block, and only the spacer that sits
    // immediately below a statement input — i.e. the leg under the
    // proof gap.
    if (needsExtraSpace(this.block_, prev)) {
      return base + GOAL_STATUS_EXTRA_SPACE;
    }
    return base;
  }
}

class CustomRenderer extends blockly.zelos.Renderer {
  protected makeRenderInfo_(block: BlockSvg): CustomRenderInfo {
    return new CustomRenderInfo(this, block);
  }
}

export const CUSTOM_RENDERER_NAME = 'customZelos';

blockly.blockRendering.register(CUSTOM_RENDERER_NAME, CustomRenderer);
