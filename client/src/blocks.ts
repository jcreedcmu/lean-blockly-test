import * as blockly from 'blockly';
import { FieldLabelSerializable, FieldTextInput, FieldConfig } from 'blockly';
import { attachAbbreviationRewriter } from './abbreviations';
import './FieldProofStatus';

/*
Adapted from https://github.com/aneilmac/blockly-plugin-lean under the Apache 2.0 license
*/

/**
 * Custom field for theorem statements with monospace styling.
 *
 * The *serialized* value is the raw Lean declaration consumed by
 * `workspaceToLean` for codegen. The *displayed* text can be replaced
 * at runtime via `setDisplayOverride` — levels use this to swap in a
 * hand-authored decomposed view (`Objects: … / Assumptions: … / Goal:
 * …`) without touching the serialized value. When the displayed text
 * contains `\n`, it's rendered as multiple lines via `<tspan>` elements
 * (SVG `<text>` itself ignores newlines).
 */
export class FieldTheoremStatement extends FieldLabelSerializable {
  private displayOverride: string | null = null;

  constructor(value?: string) {
    super(value ?? '');
  }

  initView(): void {
    super.initView();
    if (this.textElement_) {
      blockly.utils.dom.addClass(this.textElement_, 'blocklyMonospace');
    }
  }

  /** Replace the rendered label with `text`, or restore the serialized
   * value when `text` is null. Doesn't affect `getValue()` or what the
   * workspace serializer writes. */
  setDisplayOverride(text: string | null): void {
    if (this.displayOverride === text) return;
    this.displayOverride = text;
    this.forceRerender();
  }

  getText(): string {
    return this.displayOverride ?? super.getText();
  }

  /** If the raw text has newlines, split it into `<tspan>` children and
   * resize to the resulting bounding box.
   *
   * Two quirks of Blockly's default rendering we have to work around:
   *   - `getDisplayText_()` runs `text.replace(/\s/g, NBSP)`, which
   *     collapses our `\n`s to non-breaking spaces before they ever
   *     reach the DOM. We go through `getText()` directly.
   *   - `super.render_()` inserts a single `Text` node (the field's
   *     persistent `textContent_`). For multi-line, we replace that
   *     with tspans. To stay consistent across repeated renders (and
   *     across transitions back to single-line), we always fully
   *     rebuild the tspans. */
  protected override render_(): void {
    super.render_();
    if (!this.textElement_) return;
    const text = this.getText();

    // Strip any text / tspan children we (or super) added.
    while (this.textElement_.firstChild) {
      this.textElement_.removeChild(this.textElement_.firstChild);
    }

    const lines = text.split('\n');
    const svgNs = 'http://www.w3.org/2000/svg';
    for (let i = 0; i < lines.length; i++) {
      const tspan = document.createElementNS(svgNs, 'tspan');
      tspan.setAttribute('x', '0');
      if (i > 0) tspan.setAttribute('dy', '1.2em');
      // Non-breaking space for empty lines so each tspan retains height.
      // Also apply the same whitespace→NBSP substitution Blockly would
      // have done (leading spaces on SVG text otherwise collapse).
      tspan.textContent = lines[i].length > 0
        ? lines[i].replace(/ /g, '\u00A0')
        : '\u00A0';
      this.textElement_.appendChild(tspan);
    }

    try {
      const bbox = this.textElement_.getBBox();
      this.size_.width = bbox.width;
      this.size_.height = bbox.height;
    } catch {
      // getBBox can throw for detached DOM; leave size_ as set by super.
    }
  }

  static fromJson(options: FieldConfig & { text?: string }): FieldTheoremStatement {
    return new FieldTheoremStatement(options.text);
  }
}

/**
 * Custom editable text field with monospace styling.
 */
class FieldMonospaceInput extends FieldTextInput {
  constructor(value?: string) {
    super(value ?? '');
  }

  initView(): void {
    super.initView();
    if (this.textElement_) {
      blockly.utils.dom.addClass(this.textElement_, 'blocklyMonospace');
    }
  }

  protected override showEditor_(e?: Event, quietInput?: boolean): void {
    super.showEditor_(e, quietInput);
    if (this.htmlInput_ instanceof HTMLInputElement) {
      attachAbbreviationRewriter(this.htmlInput_);
    }
  }

  static fromJson(options: FieldConfig & { text?: string }): FieldMonospaceInput {
    return new FieldMonospaceInput(options.text);
  }
}

// Register the custom field types
blockly.fieldRegistry.register('field_theorem_statement', FieldTheoremStatement);
blockly.fieldRegistry.register('field_monospace_input', FieldMonospaceInput);

export function defineBlocks() {
  defineLemma();
  defineProposition();
  defineTactics();
  defineMisc();
  defineSpecialize();
}

type TacticProps = { name: string, msg: string };
export const singleArgTactics: TacticProps[] = [
  { name: 'unfold', msg: 'unfold' },
  { name: 'apply', msg: 'apply' },
  { name: 'exact', msg: 'exactly' },
  { name: 'intro', msg: 'intro' },
  { name: 'use', msg: 'use' },
];

function defineMisc() {
  function single_arg_tactic(props: TacticProps) {
    const { name, msg } = props;
    return {
      'type': `tactic_${name}`,
      'message0': `${msg} %1`,
      'args0': [
        {
          'type': 'input_value',
          'name': 'ARG',
          'check': 'proposition',
          'align': 'LEFT',
        },
      ],
      'inputsInline': false,
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'style': 'logic_blocks',
      'tooltip': name,
      'helpUrl': name,
    };
  }
  blockly.defineBlocksWithJsonArray(singleArgTactics.map(single_arg_tactic));
}

function defineLemma() {
  blockly.defineBlocksWithJsonArray([
    {
      'type': 'lemma',
      'message0': '%1 %2 %3   %4 %5 proof: %6 %7 %8',
      'args0': [
        {
          'type': 'field_label_serializable',
          'name': 'THEOREM_BLOCK_LABEL',
          'text': 'theorem',
        },
        {
          'type': 'field_label_serializable',
          'name': 'THEOREM_NAME',
          'text': 'theorem_name',
        },
        {
          'type': 'input_dummy',
        },
        {
          'type': 'field_theorem_statement',
          'name': 'THEOREM_DECLARATION',
          'text': 'theorem_statement',
        },
        {
          'type': 'input_dummy',
        },
        {
          'type': 'input_statement',
          'name': 'LEMMA_PROOF',
          'check': 'tactic',
        },
        {
          'type': 'field_proof_status',
          'name': 'PROOF_STATUS',
        },
        {
          'type': 'input_dummy',
        },
      ],
      'inputsInline': false,
      'style': 'procedure_blocks',
      'tooltip': '',
      'helpUrl': '',
    },
  ]);
}

function defineProposition() {
  blockly.defineBlocksWithJsonArray([
    {
      'type': 'prop_declaration',
      'message0': '%1 : %2',
      'args0': [
        {
          'type': 'field_monospace_input',
          'name': 'VARIABLE_DECL',
          'text': 'default',
        },
        {
          'type': 'field_monospace_input',
          'name': 'VARIABLE_DEF',
          'text': 'default',
        },
      ],
      'previousStatement': 'prop_declaration',
      'nextStatement': 'prop_declaration',
      'style': 'variable_blocks',
      'tooltip': '',
      'helpUrl': '',
    },
    {
      'type': 'prop',
      'message0': '%1',
      'args0': [
        {
          'type': 'field_monospace_input',
          'name': 'PROP_NAME',
          'text': 'h',
        },
      ],
      'output': 'proposition',
      'style': 'variable_blocks',
      'tooltip': '',
      'helpUrl': '',
    },
    {
      'type': 'prop_dynamic',
      'message0': '%1',
      'args0': [
        {
          'type': 'field_monospace_input',
          'name': 'PROP_NAME',
          'text': 'h',
        },
      ],
      'output': 'proposition',
      'style': 'variable_dynamic_blocks',
      'tooltip': '',
      'helpUrl': '',
    },
  ]);
}

function defineTactics() {
  blockly.defineBlocksWithJsonArray([
    {
      'type': 'tactic_refl',
      'message0': 'reflexivity',
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'tooltip': 'refl proves goals of the form X = X.',
      'helpUrl': 'refl',
      'style': 'logic_blocks',
    },
    {
      'type': 'tactic_ring_nf',
      'message0': 'ring',
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'tooltip': 'ring_nf simplifies algebraic expressions.',
      'helpUrl': 'ring_nf',
      'style': 'logic_blocks',
    },
    {
      'type': 'tactic_rewrite',
      'message0': 'rewrite %1 %2',
      'args0': [
        {
          'type': 'field_dropdown',
          'name': 'DIRECTION_TYPE',
          'options': [
            [
              '→',
              'RIGHT',
            ],
            [
              '←',
              'LEFT',
            ],
          ],
        },
        {
          'type': 'input_value',
          'name': 'REWRITE_SOURCE',
          'check': 'proposition',
          'align': 'CENTRE',
        },
      ],
      'inputsInline': false,
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'style': 'logic_blocks',
      'tooltip': 'rewrite',
      'helpUrl': 'rewrite',
    },
    {
      'type': 'tactic_rewrite_at',
      'message0': 'rewrite %1 at %2',
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'args0': [
        {
          'type': 'input_value',
          'name': 'REWRITE_SOURCE',
          'check': 'proposition',
        },
        {
          'type': 'input_value',
          'name': 'REWRITE_TARGET',
          'check': 'proposition',
        },
      ],
      'inputsInline': false,
      'style': 'logic_blocks',
      'tooltip': 'rewrite_at',
      'helpUrl': 'rewrite_at',
    },
    {
      // `choose <var> using <hyp>` destructs an existential hypothesis.
      // CHOSEN is the new variable name to introduce (free text — the
      // student can type multiple names here, e.g. `c hc` to also bind
      // the proof). SOURCE is the hypothesis with the existential.
      'type': 'tactic_choose',
      'message0': 'choose %1 using %2',
      'args0': [
        {
          'type': 'input_value',
          'name': 'CHOSEN',
          'check': 'proposition',
        },
        {
          'type': 'input_value',
          'name': 'SOURCE',
          'check': 'proposition',
        },
      ],
      'inputsInline': true,
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'style': 'logic_blocks',
      'tooltip': 'choose',
      'helpUrl': 'choose',
    },
    {
      'type': 'tactic_sorry',
      'message0': 'sorry',
      'previousStatement': 'tactic',
      'colour': 330,
      'tooltip': 'hole in proof',
      'helpUrl': 'refl',
    },
    {
      'type': 'tactic_other',
      'message0': '%1',
      'args0': [
        {
          'type': 'field_monospace_input',
          'name': 'PROP_NAME',
          'text': 'h',
        },
      ],
      'nextStatement': 'tactic',
      'previousStatement': 'tactic',
      'colour': 110,
      'tooltip': 'other tactic',
      'helpUrl': 'other tactic',
    },
    {
      "type": "tactic_constructor",
      "tooltip": "",
      "helpUrl": "",
      "message0": "pair %1 %2 %3 %4 %5 %6",
      "args0": [
        {
          "type": "input_statement",
          "name": "BODY1"
        },
        {
          "type": "field_proof_status",
          "name": "STATUS_1"
        },
        {
          "type": "input_dummy"
        },
        {
          "type": "input_statement",
          "name": "BODY2"
        },
        {
          "type": "field_proof_status",
          "name": "STATUS_2"
        },
        {
          "type": "input_dummy"
        }
      ],
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      "colour": 165
    },
    {
      "type": "tactic_show",
      "tooltip": "tactic_show",
      "helpUrl": "tactic_show",
      "message0": "show %1 by %2 %3 %4",
      "args0": [
        {
          "type": "input_value",
          "name": "GOAL"
        },
        {
          "type": "input_statement",
          "name": "PROOF"
        },
        {
          "type": "field_proof_status",
          "name": "PROOF_STATUS"
        },
        {
          "type": "input_dummy"
        },
      ],
      "output": "proposition",
      "style": "text_blocks",
    },
    {
      "type": "tactic_have",
      "tooltip": "Introduce a local lemma",
      "helpUrl": "have",
      "message0": "have %1 : %2 %3 by %4 %5 %6",
      "args0": [
        {
          "type": "field_monospace_input",
          "name": "NAME",
          "text": "h"
        },
        {
          "type": "field_monospace_input",
          "name": "TYPE",
          "text": "True"
        },
        {
          "type": "input_dummy"
        },
        {
          "type": "input_statement",
          "name": "PROOF",
          "check": "tactic"
        },
        {
          "type": "field_proof_status",
          "name": "PROOF_STATUS"
        },
        {
          "type": "input_dummy"
        }
      ],
      "previousStatement": "tactic",
      "nextStatement": "tactic",
      "style": "procedure_blocks"
    }
  ]);
}

// ─────────────────────────────────────────────────────────────────────
// Variable-arity `specialize` block.
//
// Matches Lean's `specialize h x y z` syntax: a required hypothesis
// (HYP) followed by zero or more arguments (ARG0..ARGn). Inline `+`
// and `−` field buttons grow/shrink the arg list in place — no
// gear-icon popup.
//
// Serialization (`saveExtraState` / `loadExtraState`) is provided via
// Blockly's mutator API with no decompose/compose, which is the one
// way to legally install those "mutation property" methods without
// also getting a mutator-dialog icon.
// ─────────────────────────────────────────────────────────────────────

// Inline SVG data URIs for the +/- buttons.
const PLUS_ICON_URI = 'data:image/svg+xml;utf8,' + encodeURIComponent(
  '<svg xmlns="http://www.w3.org/2000/svg" width="14" height="14">' +
  '<rect width="14" height="14" rx="2" fill="white" stroke="#666"/>' +
  '<text x="7" y="11" text-anchor="middle" font-family="sans-serif" font-size="12" font-weight="bold" fill="#333">+</text>' +
  '</svg>'
);
const MINUS_ICON_URI = 'data:image/svg+xml;utf8,' + encodeURIComponent(
  '<svg xmlns="http://www.w3.org/2000/svg" width="14" height="14">' +
  '<rect width="14" height="14" rx="2" fill="white" stroke="#666"/>' +
  '<text x="7" y="11" text-anchor="middle" font-family="sans-serif" font-size="12" font-weight="bold" fill="#333">−</text>' +
  '</svg>'
);

// New ARG slots are always appended at the tail. `message0` places
// CONTROLS (the +/- buttons) immediately after HYP, so appending puts
// new args to the right of the buttons.
function appendSpecializeArgInput(
  block: blockly.Block & { argCount_: number },
  i: number,
) {
  block.appendValueInput(`ARG${i}`).setCheck('proposition');
}

// Mixin applied via Blockly's mutator API.
const SPECIALIZE_MIXIN = {
  saveExtraState: function(this: { argCount_: number }) {
    return { argCount: this.argCount_ };
  },
  loadExtraState: function(
    this: blockly.Block & { argCount_: number },
    state: unknown,
  ) {
    const target =
      state && typeof state === 'object' && 'argCount' in state
        ? Number((state as { argCount?: number }).argCount ?? 0)
        : 0;
    while (this.argCount_ < target) {
      appendSpecializeArgInput(this, this.argCount_);
      this.argCount_ += 1;
    }
    while (this.argCount_ > target) {
      this.argCount_ -= 1;
      this.removeInput(`ARG${this.argCount_}`);
    }
  },
};

// Runs on every block init: zero argCount_ and wire +/- buttons.
function specializeInit(this: blockly.Block) {
  const self = this as blockly.Block & { argCount_: number };
  self.argCount_ = 0;

  const plusBtn = new blockly.FieldImage(
    PLUS_ICON_URI, 14, 14, '+',
    () => {
      const i = self.argCount_;
      appendSpecializeArgInput(self, i);
      self.argCount_ = i + 1;
    },
  );
  const minusBtn = new blockly.FieldImage(
    MINUS_ICON_URI, 14, 14, '−',
    () => {
      if (self.argCount_ > 0) {
        self.argCount_ -= 1;
        self.removeInput(`ARG${self.argCount_}`);
      }
    },
  );
  self.getInput('CONTROLS')!
    .appendField(plusBtn, 'PLUS')
    .appendField(minusBtn, 'MINUS');
}

function defineSpecialize() {
  blockly.defineBlocksWithJsonArray([
    {
      'type': 'tactic_specialize',
      'message0': 'specialize %1 %2',
      'args0': [
        { 'type': 'input_value', 'name': 'HYP', 'check': 'proposition', 'align': 'LEFT' },
        { 'type': 'input_dummy', 'name': 'CONTROLS' },
      ],
      'inputsInline': true,
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'style': 'logic_blocks',
      'tooltip': 'specialize',
      'helpUrl': 'specialize',
      'mutator': 'specialize_buttons',
    },
  ]);

  if (!blockly.Extensions.isRegistered('specialize_buttons')) {
    // Register as a mutator (no decompose/compose → no gear icon) so
    // we can legally install saveExtraState / loadExtraState.
    blockly.Extensions.registerMutator(
      'specialize_buttons',
      SPECIALIZE_MIXIN,
      specializeInit,
    );
  }
}
