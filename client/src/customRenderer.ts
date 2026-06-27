import * as blockly from 'blockly';
import type { BlockSvg } from 'blockly';
import { FieldProofStatus } from './FieldProofStatus';
import { isGoalPositionMarker } from './goalMarker';

type Row = blockly.blockRendering.Row;
type Measurable = blockly.blockRendering.Measurable;
type StatementInput = blockly.blockRendering.StatementInput;
const Types = blockly.blockRendering.Types;

/** Extra vertical space (px) added to the leg directly below a statement
 * input that carries a proof-status indicator, to give the pill room. */
const PROOF_STATUS_LEG_EXTRA = 0;

/** Distance (px) from the bottom of the proof slot to the top of the pill.
 * The slot bottom is a consistent landmark across blocks (unlike the field
 * row's own top, whose distance below the notch drifts with row spacing), so
 * anchoring here gives a uniform notch→pill gap. */
const PILL_BELOW_SLOT = 16;

/** A Field measurable known to wrap a FieldProofStatus. */
type ProofStatusElem = Measurable & { field: FieldProofStatus };

/** The proof-status Field measurable on a row, if it has one. */
function proofStatusElem(row: Row): ProofStatusElem | null {
  for (const elem of row.elements) {
    if (Types.isField(elem) && (elem as { field: unknown }).field instanceof FieldProofStatus) {
      return elem as unknown as ProofStatusElem;
    }
  }
  return null;
}

/** The StatementInput measurable on a row, if it has one. */
function statementInputElem(row: Row): StatementInput | null {
  for (const elem of row.elements) {
    if (Types.isStatementInput(elem)) return elem;
  }
  return null;
}

/** Width of a (possibly dynamic) connection shape at the given height. */
function shapeWidth(shape: { width: number | ((h: number) => number) }, height: number): number {
  return typeof shape.width === 'number' ? shape.width : shape.width(height);
}

/**
 * Walk upward from row `i`, skipping spacer rows, to the nearest input row;
 * return it only if it carries a statement input (else null — the field isn't
 * directly below a slot).
 */
function statementRowAbove(rows: Row[], i: number): Row | null {
  for (let j = i - 1; j >= 0; j--) {
    if (Types.isSpacerRow(rows[j])) continue;
    return statementInputElem(rows[j]) ? rows[j] : null;
  }
  return null;
}

/**
 * Block-local horizontal extent of a statement input's notch. Mirrors the
 * exact arithmetic in zelos `Drawer.drawStatementInput_`, which draws the
 * notch to the right edge `xPos + notchOffset + shape.width` — note it uses
 * the measurable's own `notchOffset` (= NOTCH_OFFSET_LEFT, 12px in zelos),
 * NOT the constant `STATEMENT_INPUT_NOTCH_OFFSET` (16px). Using `notchOffset`
 * here is what keeps the pill in sync with the notch.
 */
function notchBounds(stmt: StatementInput): { left: number; width: number; center: number } {
  const width = shapeWidth(stmt.shape, stmt.height);
  const left = stmt.xPos + stmt.notchOffset;
  return { left, width, center: left + width / 2 };
}

class CustomRenderInfo extends blockly.zelos.RenderInfo {
  /**
   * Widen the leg directly below a statement input when a proof-status
   * field sits in the row beneath it.
   */
  getSpacerRowHeight_(prev: Row, next: Row): number {
    const base = super.getSpacerRowHeight_(prev, next);
    if (prev.hasStatement && proofStatusElem(next)) {
      return base + PROOF_STATUS_LEG_EXTRA;
    }
    return base;
  }

  /**
   * Size each proof-status field to the notch of the statement input it
   * reports on, center it horizontally on that notch, and place it a fixed
   * distance below the bottom of the proof slot vertically. Done after the
   * base pass has computed widths/positions; the drawer reads these
   * afterwards.
   */
  finalize_(): void {
    super.finalize_();
    for (let i = 0; i < this.rows.length; i++) {
      const elem = proofStatusElem(this.rows[i]);
      if (!elem) continue;
      const stmtRow = statementRowAbove(this.rows, i);
      if (!stmtRow) continue;
      const stmt = statementInputElem(stmtRow)!;
      const { center } = notchBounds(stmt);
      // The pill is a fixed size now — just center it horizontally on the notch.
      elem.xPos = center - elem.width / 2;
      // Vertical: `layoutField_` places the field at `centerline - height/2`,
      // so this puts the pill's top a fixed `PILL_BELOW_SLOT` below the slot
      // bottom — a landmark that's consistent across blocks.
      const slotBottom = stmtRow.yPos + stmtRow.height;
      elem.centerline = slotBottom + PILL_BELOW_SLOT + elem.height / 2;
    }
  }

  /**
   * Faithful copy of zelos `adjustXPosition_`, with our marker pills added to
   * the label/image skip list. zelos pushes a leading non-label field out past
   * the previous-statement notch (to `NOTCH_OFFSET_LEFT + NOTCH_WIDTH`); labels
   * and images are exempt. We exempt goal markers too, so a leading marker pill
   * stays tucked at the left like text instead of indenting the whole block.
   */
  adjustXPosition_(): void {
    const startX = this.constants_.NOTCH_OFFSET_LEFT + this.constants_.NOTCH_WIDTH;
    let b = startX;
    for (let e = 2; e < this.rows.length - 1; e += 2) {
      const prev = this.rows[e - 1] as Row & { followsStatement?: boolean };
      const f = this.rows[e];
      const next = this.rows[e + 1] as Row & { precedesStatement?: boolean };
      const follows = e === 2 ? this.topRow.hasPreviousConnection : !!prev.followsStatement;
      const precedes = e + 2 >= this.rows.length - 1
        ? this.bottomRow.hasNextConnection
        : !!next.precedesStatement;
      if (Types.isInputRow(f) && f.hasStatement) {
        f.measure();
        b = f.width - (f.getLastInput()?.width ?? 0) + startX;
      } else if (follows && (e === 2 || precedes) && Types.isInputRow(f) && !f.hasStatement) {
        let x = (f as Row & { xPos: number }).xPos;
        let spacer: Measurable | null = null;
        for (const h of f.elements) {
          if (Types.isSpacer(h)) spacer = h;
          if (spacer && (Types.isField(h) || Types.isInput(h)) && x < b) {
            const field = (h as { field?: unknown }).field;
            const decoration = Types.isField(h)
              && (field instanceof blockly.FieldLabel
                || field instanceof blockly.FieldImage
                || isGoalPositionMarker(field));
            if (!decoration) spacer.width += b - x;
          }
          x += h.width;
        }
      }
    }
  }

}

class CustomRenderer extends blockly.zelos.Renderer {
  protected makeRenderInfo_(block: BlockSvg): CustomRenderInfo {
    return new CustomRenderInfo(this, block);
  }
}

export const CUSTOM_RENDERER_NAME = 'customZelos';

blockly.blockRendering.register(CUSTOM_RENDERER_NAME, CustomRenderer);
