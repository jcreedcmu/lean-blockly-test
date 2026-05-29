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

// Register extensions (must happen exactly once, before any block definitions)
blockly.Extensions.register('lemma_init', function (this: blockly.Block) {
  (this as blockly.BlockSvg).addClass('lemma-block');
  // THEOREM_NAME is used by codegen but not displayed; the user-visible
  // label is THEOREM_BLOCK_LABEL (e.g. "theorem foo" or "Example").
  this.getField('THEOREM_NAME')?.setVisible(false);
});

export function defineBlocks() {
  defineLemma();
  defineProposition();
  defineTactics();
  defineMisc();
  defineSpecialize();
  defineTermTheorems();
  defineCalc();
}

function defineTermTheorems() {
  blockly.defineBlocksWithJsonArray([
    {
      'type': 'term_archprop',
      'message0': 'ArchProp %1',
      'args0': [
        { 'type': 'input_value', 'name': 'ARG', 'check': 'proposition' },
      ],
      'inputsInline': true,
      'output': 'proposition',
      'colour': 260,
      'tooltip': '∃ N > 0, 1/N < ε  (provide proof that ε > 0)',
      'helpUrl': '',
    },
  ]);
}

type TacticProps = { name: string, msg: string };
export const singleArgTactics: TacticProps[] = [
  { name: 'unfold', msg: 'unfold' },
  { name: 'apply', msg: 'apply' },
  { name: 'exact', msg: 'exactly' },
  { name: 'intro', msg: 'intro' },
  { name: 'use', msg: 'use' },
];

function setDefaultPropShadow(block: blockly.Block, inputName: string) {
  const connection = block.getInput(inputName)?.connection;
  if (!connection || connection.targetBlock()) return;
  connection.setShadowState({
    type: 'prop',
    fields: {
      PROP_NAME: 'h',
    },
  });
}

function appendMultiArgInput(
  block: blockly.Block & { extraArgCount_: number },
  i: number,
) {
  const inputName = `ARG${i}`;
  block.appendValueInput(inputName).setCheck('proposition');
  block.moveInputBefore(inputName, 'CONTROLS');
  setDefaultPropShadow(block, inputName);
}

const MULTI_ARG_TACTIC_MIXIN = {
  saveExtraState: function(this: { extraArgCount_: number }) {
    return { argCount: this.extraArgCount_ };
  },
  loadExtraState: function(
    this: blockly.Block & { extraArgCount_: number },
    state: unknown,
  ) {
    const rawTarget =
      state && typeof state === 'object' && 'argCount' in state
        ? Number((state as { argCount?: number }).argCount ?? 0)
        : 0;
    const target = Number.isFinite(rawTarget)
      ? Math.max(0, Math.floor(rawTarget))
      : 0;

    while (this.extraArgCount_ < target) {
      const nextIndex = this.extraArgCount_ + 1;
      appendMultiArgInput(this, nextIndex);
      this.extraArgCount_ = nextIndex;
    }
    while (this.extraArgCount_ > target) {
      this.removeInput(`ARG${this.extraArgCount_}`);
      this.extraArgCount_ -= 1;
    }
  },
};

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

function multiArgTacticInit(this: blockly.Block) {
  const self = this as blockly.Block & { extraArgCount_: number };
  self.extraArgCount_ = 0;
  setDefaultPropShadow(self, 'ARG');

  const plusBtn = new blockly.FieldImage(
    PLUS_ICON_URI, 14, 14, '+',
    () => {
      const nextIndex = self.extraArgCount_ + 1;
      appendMultiArgInput(self, nextIndex);
      self.extraArgCount_ = nextIndex;
    },
  );
  const minusBtn = new blockly.FieldImage(
    MINUS_ICON_URI, 14, 14, '−',
    () => {
      if (self.extraArgCount_ > 0) {
        self.removeInput(`ARG${self.extraArgCount_}`);
        self.extraArgCount_ -= 1;
      }
    },
  );
  self.getInput('CONTROLS')!
    .appendField(plusBtn, 'PLUS')
    .appendField(minusBtn, 'MINUS');
}

function defineMisc() {
  function single_arg_tactic(props: TacticProps) {
    const { name, msg } = props;
    const definition: Record<string, unknown> = {
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
    if (name === 'apply') {
      definition.classes = 'tutorial-apply-block';
    }
    return definition;
  }
  blockly.defineBlocksWithJsonArray(singleArgTactics.map(single_arg_tactic));
}

function defineLemma() {
  blockly.defineBlocksWithJsonArray([
    {
      'type': 'lemma',
      'extensions': ['lemma_init'],
      'message0': '%1 %2 %3   %4 %5 Proof: %6 %7 %8',
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
      'type': 'tactic_simp',
      'message0': 'simp',
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'tooltip': 'simp simplifies using definitions and rewrite lemmas.',
      'helpUrl': 'simp',
      'style': 'logic_blocks',
    },
    {
      'type': 'tactic_conclude',
      'message0': 'conclude %1',
      'args0': [
        { 'type': 'input_dummy', 'name': 'CONTROLS' },
      ],
      'inputsInline': true,
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'tooltip': 'Auto-finisher. Add hints with +.',
      'helpUrl': 'conclude',
      'style': 'logic_blocks',
      'mutator': 'conclude_arg_buttons',
    },
    {
      'type': 'tactic_rewrite',
      'message0': 'rewrite %1 %2 %3',
      'args0': [
        {
          'type': 'field_dropdown',
          'name': 'DIRECTION_TYPE',
          'options': [['→', 'RIGHT'], ['←', 'LEFT']],
        },
        {
          'type': 'input_value',
          'name': 'REWRITE_SOURCE',
          'check': 'proposition',
          'align': 'CENTRE',
        },
        {
          'type': 'input_dummy',
          'name': 'CONTROLS',
        },
      ],
      'inputsInline': false,
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'style': 'logic_blocks',
      'tooltip': 'rewrite',
      'helpUrl': 'rewrite',
      'mutator': 'rewrite_arg_buttons',
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
      "type": "tactic_at",
      "tooltip": "Apply a tactic at a hypothesis",
      "helpUrl": "tactic_at",
      "message0": "at %1 %2",
      "args0": [
        {
          "type": "field_monospace_input",
          "name": "HYP",
          "text": "h"
        },
        {
          "type": "input_statement",
          "name": "BODY",
          "check": "tactic"
        }
      ],
      "previousStatement": "tactic",
      "nextStatement": "tactic",
      "style": "text_blocks"
    },
    {
      "type": "tactic_transform",
      "tooltip": "Rewrite the goal by proving X = Y",
      "helpUrl": "tactic_transform",
      "message0": "transform %1 to %2 %3 by %4 %5 %6",
      "args0": [
        {
          "type": "field_monospace_input",
          "name": "FROM",
          "text": "X"
        },
        {
          "type": "field_monospace_input",
          "name": "TO",
          "text": "Y"
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
      "style": "logic_blocks"
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

  if (!blockly.Extensions.isRegistered('conclude_arg_buttons')) {
    blockly.Extensions.registerMutator(
      'conclude_arg_buttons',
      {
        saveExtraState: function(this: { extraArgCount_: number }) {
          return { argCount: this.extraArgCount_ };
        },
        loadExtraState: function(
          this: blockly.Block & { extraArgCount_: number },
          state: unknown,
        ) {
          const rawTarget =
            state && typeof state === 'object' && 'argCount' in state
              ? Number((state as { argCount?: number }).argCount ?? 0) : 0;
          const target = Number.isFinite(rawTarget) ? Math.max(0, Math.floor(rawTarget)) : 0;
          while (this.extraArgCount_ < target) {
            const i = this.extraArgCount_;
            this.appendValueInput(`ARG${i}`).setCheck('proposition');
            this.moveInputBefore(`ARG${i}`, 'CONTROLS');
            setDefaultPropShadow(this, `ARG${i}`);
            this.extraArgCount_++;
          }
          while (this.extraArgCount_ > target) {
            this.extraArgCount_--;
            this.removeInput(`ARG${this.extraArgCount_}`);
          }
        },
      },
      function(this: blockly.Block) {
        const self = this as blockly.Block & { extraArgCount_: number };
        self.extraArgCount_ = 0;
        self.getInput('CONTROLS')!
          .appendField(new blockly.FieldImage(PLUS_ICON_URI, 14, 14, '+', () => {
            const i = self.extraArgCount_;
            self.appendValueInput(`ARG${i}`).setCheck('proposition');
            self.moveInputBefore(`ARG${i}`, 'CONTROLS');
            setDefaultPropShadow(self, `ARG${i}`);
            self.extraArgCount_++;
          }), 'PLUS')
          .appendField(new blockly.FieldImage(MINUS_ICON_URI, 14, 14, '−', () => {
            if (self.extraArgCount_ > 0) {
              self.extraArgCount_--;
              self.removeInput(`ARG${self.extraArgCount_}`);
            }
          }), 'MINUS');
      },
    );
  }

  function appendRewriteArgInput(
    block: blockly.Block & { extraArgCount_: number },
    i: number,
  ) {
    block.appendValueInput(`REWRITE_SOURCE_${i}`)
      .appendField(
        new blockly.FieldDropdown([['→', 'RIGHT'], ['←', 'LEFT']]),
        `DIRECTION_TYPE_${i}`,
      )
      .setCheck('proposition');
    block.moveInputBefore(`REWRITE_SOURCE_${i}`, 'CONTROLS');
  }

  if (!blockly.Extensions.isRegistered('rewrite_arg_buttons')) {
    blockly.Extensions.registerMutator(
      'rewrite_arg_buttons',
      {
        saveExtraState: function(this: { extraArgCount_: number }) {
          return { argCount: this.extraArgCount_ };
        },
        loadExtraState: function(
          this: blockly.Block & { extraArgCount_: number },
          state: unknown,
        ) {
          const rawTarget =
            state && typeof state === 'object' && 'argCount' in state
              ? Number((state as { argCount?: number }).argCount ?? 0)
              : 0;
          const target = Number.isFinite(rawTarget)
            ? Math.max(0, Math.floor(rawTarget))
            : 0;
          while (this.extraArgCount_ < target) {
            const nextIndex = this.extraArgCount_ + 1;
            appendRewriteArgInput(this, nextIndex);
            this.extraArgCount_ = nextIndex;
          }
          while (this.extraArgCount_ > target) {
            this.removeInput(`REWRITE_SOURCE_${this.extraArgCount_}`);
            this.extraArgCount_ -= 1;
          }
        },
      },
      function(this: blockly.Block) {
        const self = this as blockly.Block & { extraArgCount_: number };
        self.extraArgCount_ = 0;
        const plusBtn = new blockly.FieldImage(
          PLUS_ICON_URI, 14, 14, '+',
          () => {
            const nextIndex = self.extraArgCount_ + 1;
            appendRewriteArgInput(self, nextIndex);
            self.extraArgCount_ = nextIndex;
          },
        );
        const minusBtn = new blockly.FieldImage(
          MINUS_ICON_URI, 14, 14, '−',
          () => {
            if (self.extraArgCount_ > 0) {
              self.removeInput(`REWRITE_SOURCE_${self.extraArgCount_}`);
              self.extraArgCount_ -= 1;
            }
          },
        );
        self.getInput('CONTROLS')!
          .appendField(plusBtn, 'PLUS')
          .appendField(minusBtn, 'MINUS');
      },
    );
  }
}

function defineSpecialize() {
  blockly.defineBlocksWithJsonArray([
    {
      'type': 'tactic_specialize',
      'message0': 'specialize %1 to (%2) %3 %4',
      'args0': [
        { 'type': 'input_value', 'name': 'HYP', 'check': 'proposition', 'align': 'LEFT' },
        { 'type': 'input_value', 'name': 'ARG', 'check': 'proposition', 'align': 'LEFT' },
        { 'type': 'input_dummy', 'name': 'CLOSE_0' },
        { 'type': 'input_dummy', 'name': 'CONTROLS' },
      ],
      'inputsInline': true,
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'style': 'logic_blocks',
      'tooltip': 'specialize',
      'helpUrl': 'specialize',
      'mutator': 'specialize_arg_buttons',
    },
  ]);

  if (!blockly.Extensions.isRegistered('specialize_arg_buttons')) {
    const MIXIN = {
      saveExtraState: function(this: { extraArgCount_: number }) {
        return { argCount: this.extraArgCount_ };
      },
      loadExtraState: function(
        this: blockly.Block & { extraArgCount_: number },
        state: unknown,
      ) {
        const rawTarget =
          state && typeof state === 'object' && 'argCount' in state
            ? Number((state as { argCount?: number }).argCount ?? 0)
            : 0;
        const target = Number.isFinite(rawTarget)
          ? Math.max(0, Math.floor(rawTarget))
          : 0;
        while (this.extraArgCount_ < target) {
          const nextIndex = this.extraArgCount_ + 1;
          this.appendValueInput(`ARG${nextIndex}`)
            .appendField(new blockly.FieldLabel('('))
            .setCheck('proposition');
          this.moveInputBefore(`ARG${nextIndex}`, 'CONTROLS');
          this.appendDummyInput(`CLOSE_${nextIndex}`)
            .appendField(new blockly.FieldLabel(')'));
          this.moveInputBefore(`CLOSE_${nextIndex}`, 'CONTROLS');
          this.extraArgCount_ = nextIndex;
        }
        while (this.extraArgCount_ > target) {
          this.removeInput(`CLOSE_${this.extraArgCount_}`);
          this.removeInput(`ARG${this.extraArgCount_}`);
          this.extraArgCount_ -= 1;
        }
      },
    };

    blockly.Extensions.registerMutator(
      'specialize_arg_buttons',
      MIXIN,
      function(this: blockly.Block) {
        const self = this as blockly.Block & { extraArgCount_: number };
        self.extraArgCount_ = 0;
        const plusBtn = new blockly.FieldImage(
          PLUS_ICON_URI, 14, 14, '+',
          () => {
            const nextIndex = self.extraArgCount_ + 1;
            self.appendValueInput(`ARG${nextIndex}`)
              .appendField(new blockly.FieldLabel('('))
              .setCheck('proposition');
            self.moveInputBefore(`ARG${nextIndex}`, 'CONTROLS');
            self.appendDummyInput(`CLOSE_${nextIndex}`)
              .appendField(new blockly.FieldLabel(')'));
            self.moveInputBefore(`CLOSE_${nextIndex}`, 'CONTROLS');
            self.extraArgCount_ = nextIndex;
          },
        );
        const minusBtn = new blockly.FieldImage(
          MINUS_ICON_URI, 14, 14, '−',
          () => {
            if (self.extraArgCount_ > 0) {
              self.removeInput(`CLOSE_${self.extraArgCount_}`);
              self.removeInput(`ARG${self.extraArgCount_}`);
              self.extraArgCount_ -= 1;
            }
          },
        );
        self.getInput('CONTROLS')!
          .appendField(plusBtn, 'PLUS')
          .appendField(minusBtn, 'MINUS');
      },
    );
  }
}

function defineCalc() {
  const REL_OPTIONS: [string, string][] = [['=', 'EQ'], ['≤', 'LEQ'], ['<', 'LT']];
  type CalcBlock = blockly.Block & { extraStepCount_: number; stepBubbleCounts_: number[] };

  function appendConcludeBubble(block: CalcBlock, stepIdx: number, bubbleIdx: number) {
    block.appendValueInput(`CONCLUDE_${stepIdx}_${bubbleIdx}`).setCheck('proposition');
    const anchor = stepIdx === 0 ? 'END_ROW_BASE' : `END_ROW_STEP_${stepIdx}`;
    block.moveInputBefore(`CONCLUDE_${stepIdx}_${bubbleIdx}`, anchor);
  }

  function removeConcludeBubble(block: CalcBlock, stepIdx: number, bubbleIdx: number) {
    block.removeInput(`CONCLUDE_${stepIdx}_${bubbleIdx}`);
  }

  function makeBubbleButtons(block: CalcBlock, stepIdx: number) {
    const plusBtn = new blockly.FieldImage(PLUS_ICON_URI, 14, 14, '+', () => {
      const next = block.stepBubbleCounts_[stepIdx] + 1;
      block.stepBubbleCounts_[stepIdx] = next;
      appendConcludeBubble(block, stepIdx, next);
    });
    const minusBtn = new blockly.FieldImage(MINUS_ICON_URI, 14, 14, '−', () => {
      if (block.stepBubbleCounts_[stepIdx] > 0) {
        removeConcludeBubble(block, stepIdx, block.stepBubbleCounts_[stepIdx]);
        block.stepBubbleCounts_[stepIdx] -= 1;
      }
    });
    return { plusBtn, minusBtn };
  }

  function appendCalcStep(block: CalcBlock, stepIdx: number, extraBubbles = 0) {
    block.appendDummyInput(`STEP_${stepIdx}`)
      .appendField(new blockly.FieldLabel('_'))
      .appendField(new blockly.FieldDropdown(REL_OPTIONS), `REL_${stepIdx}`)
      .appendField(new FieldMonospaceInput('b'), `RHS_${stepIdx}`)
      .appendField(new blockly.FieldLabel('using'));
    block.moveInputBefore(`STEP_${stepIdx}`, 'STEP_CONTROLS');
    const { plusBtn, minusBtn } = makeBubbleButtons(block, stepIdx);
    block.appendDummyInput(`BUBBLE_CONTROLS_${stepIdx}`)
      .appendField(plusBtn, `PLUS_BUBBLE_${stepIdx}`)
      .appendField(minusBtn, `MINUS_BUBBLE_${stepIdx}`);
    block.moveInputBefore(`BUBBLE_CONTROLS_${stepIdx}`, 'STEP_CONTROLS');
    block.appendValueInput(`CONCLUDE_${stepIdx}_0`).setCheck('proposition');
    block.moveInputBefore(`CONCLUDE_${stepIdx}_0`, 'STEP_CONTROLS');
    block.appendEndRowInput(`END_ROW_STEP_${stepIdx}`);
    block.moveInputBefore(`END_ROW_STEP_${stepIdx}`, 'STEP_CONTROLS');
    block.stepBubbleCounts_[stepIdx] = 0;
    for (let j = 1; j <= extraBubbles; j++) {
      appendConcludeBubble(block, stepIdx, j);
      block.stepBubbleCounts_[stepIdx] = j;
    }
  }

  function removeCalcStep(block: CalcBlock, stepIdx: number) {
    for (let j = block.stepBubbleCounts_[stepIdx]; j >= 1; j--) {
      removeConcludeBubble(block, stepIdx, j);
    }
    block.removeInput(`END_ROW_STEP_${stepIdx}`);
    block.removeInput(`CONCLUDE_${stepIdx}_0`);
    block.removeInput(`BUBBLE_CONTROLS_${stepIdx}`);
    block.removeInput(`STEP_${stepIdx}`);
    block.stepBubbleCounts_.splice(stepIdx, 1);
  }

  blockly.defineBlocksWithJsonArray([{
    'type': 'tactic_calc',
    'message0': 'calc %1 : %2 %3 %4 using %5 %6',
    'args0': [
      { 'type': 'field_monospace_input', 'name': 'NAME', 'text': 'h' },
      { 'type': 'field_monospace_input', 'name': 'LHS', 'text': 'a' },
      { 'type': 'field_dropdown', 'name': 'REL_0', 'options': REL_OPTIONS },
      { 'type': 'field_monospace_input', 'name': 'RHS_0', 'text': 'b' },
      { 'type': 'input_dummy', 'name': 'BUBBLE_CONTROLS_0' },
      { 'type': 'input_value', 'name': 'CONCLUDE_0_0', 'check': 'proposition' },
    ],
    'inputsInline': true,
    'previousStatement': 'tactic',
    'nextStatement': 'tactic',
    'style': 'procedure_blocks',
    'tooltip': 'have h := calc ...',
    'helpUrl': '',
    'mutator': 'calc_step_buttons',
  }]);

  if (!blockly.Extensions.isRegistered('calc_step_buttons')) {
    blockly.Extensions.registerMutator(
      'calc_step_buttons',
      {
        saveExtraState: function(this: CalcBlock) {
          return { bubbleCounts: [...this.stepBubbleCounts_] };
        },
        loadExtraState: function(this: CalcBlock, state: unknown) {
          const savedCounts: number[] =
            state && typeof state === 'object' && 'bubbleCounts' in state
              ? (state as { bubbleCounts: number[] }).bubbleCounts
              : [0];
          // Reconcile step 0 bubbles
          const target0 = Math.max(0, savedCounts[0] ?? 0);
          while (this.stepBubbleCounts_[0] < target0) {
            appendConcludeBubble(this, 0, this.stepBubbleCounts_[0] + 1);
            this.stepBubbleCounts_[0] += 1;
          }
          while (this.stepBubbleCounts_[0] > target0) {
            removeConcludeBubble(this, 0, this.stepBubbleCounts_[0]);
            this.stepBubbleCounts_[0] -= 1;
          }
          // Reconcile extra steps
          const targetStepCount = savedCounts.length - 1;
          while (this.extraStepCount_ > targetStepCount) {
            removeCalcStep(this, this.extraStepCount_);
            this.extraStepCount_ -= 1;
          }
          while (this.extraStepCount_ < targetStepCount) {
            const nextStep = this.extraStepCount_ + 1;
            appendCalcStep(this, nextStep, savedCounts[nextStep] ?? 0);
            this.extraStepCount_ = nextStep;
          }
        },
      },
      function(this: blockly.Block) {
        const self = this as CalcBlock;
        self.extraStepCount_ = 0;
        self.stepBubbleCounts_ = [0];
        const { plusBtn: plusBubble0, minusBtn: minusBubble0 } = makeBubbleButtons(self, 0);
        self.getInput('BUBBLE_CONTROLS_0')!
          .appendField(plusBubble0, 'PLUS_BUBBLE_0')
          .appendField(minusBubble0, 'MINUS_BUBBLE_0');
        self.appendEndRowInput('END_ROW_BASE');
        self.appendDummyInput('STEP_CONTROLS')
          .appendField(new blockly.FieldImage(PLUS_ICON_URI, 14, 14, '+', () => {
            const nextStep = self.extraStepCount_ + 1;
            appendCalcStep(self, nextStep);
            self.extraStepCount_ = nextStep;
          }), 'PLUS_STEP')
          .appendField(new blockly.FieldImage(MINUS_ICON_URI, 14, 14, '−', () => {
            if (self.extraStepCount_ > 0) {
              removeCalcStep(self, self.extraStepCount_);
              self.extraStepCount_ -= 1;
            }
          }), 'MINUS_STEP');
      },
    );
  }
}
