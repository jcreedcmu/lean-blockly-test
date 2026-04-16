import * as blockly from 'blockly';
import { FieldLabelSerializable, FieldTextInput, FieldConfig } from 'blockly';
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
    // Add custom CSS class to the text element
    if (this.textElement_) {
      blockly.utils.dom.addClass(this.textElement_, 'blocklyMonospace');
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
  defineSpecializeVariants();
}

type TacticProps = { name: string, msg: string };
export const singleArgTactics: TacticProps[] = [
  { name: 'unfold', msg: 'unfold' },
  { name: 'apply', msg: 'apply' },
  { name: 'exact', msg: 'exactly' },
  { name: 'intro', msg: 'intro' },
  { name: 'use', msg: 'use' },
  { name: 'specialize', msg: 'specialize' },
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
      'message0': 'theorem %1 %2   %3 %4 proof: %5 %6 %7',
      'args0': [
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
// Variable-arity specialize: two exploratory variants.
//
//   tactic_specialize1  — mutator variant. A gear icon opens a
//                         popup mini-workspace where you drag
//                         `arg` item blocks in/out to change arity.
//   tactic_specialize2  — plus/minus button variant. Inline `+` and
//                         `−` field buttons append/remove a value
//                         input directly on the block.
//
// Both blocks share the same codegen (`specialize HYP ARG0 ARG1 …`)
// and the same input scheme (HYP + dynamically-added ARG0..ARGn).
// ─────────────────────────────────────────────────────────────────────

// Inline SVG data URIs for the +/- buttons on tactic_specialize2.
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

// Mixin applied to tactic_specialize1 via Blockly's mutator system.
// Provides saveExtraState/loadExtraState/decompose/compose/
// saveConnections — the standard mutator protocol. `updateShape_` is
// the private helper that actually adds/removes ARG inputs.
//
// `any` casts are plentiful here because mutator mixins receive a
// block `this` with a shape that evolves at runtime; spelling that
// out precisely in TypeScript isn't worth the noise.
const SPECIALIZE1_MIXIN = {
  saveExtraState: function(this: { argCount_: number }) {
    return { argCount: this.argCount_ };
  },
  loadExtraState: function(
    this: { argCount_: number; updateShape_: () => void },
    state: { argCount?: number },
  ) {
    this.argCount_ = state?.argCount ?? 0;
    this.updateShape_();
  },
  decompose: function(this: { argCount_: number }, workspace: blockly.Workspace) {
    const container = workspace.newBlock('specialize1_container') as blockly.BlockSvg;
    container.initSvg();
    let connection = container.getInput('STACK')!.connection!;
    for (let i = 0; i < this.argCount_; i++) {
      const item = workspace.newBlock('specialize1_item') as blockly.BlockSvg;
      item.initSvg();
      connection.connect(item.previousConnection!);
      connection = item.nextConnection!;
    }
    return container;
  },
  compose: function(
    this: blockly.Block & { argCount_: number; updateShape_: () => void },
    containerBlock: blockly.Block,
  ) {
    let itemBlock = containerBlock.getInputTargetBlock('STACK');
    const connections: (blockly.Connection | null)[] = [];
    while (itemBlock && !itemBlock.isInsertionMarker()) {
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      connections.push((itemBlock as any).valueConnection_ ?? null);
      itemBlock = itemBlock.getNextBlock();
    }
    // Disconnect any children whose connections weren't preserved.
    for (let i = 0; i < this.argCount_; i++) {
      const conn = this.getInput(`ARG${i}`)?.connection?.targetConnection;
      if (conn && !connections.includes(conn)) conn.disconnect();
    }
    this.argCount_ = connections.length;
    this.updateShape_();
    // Reconnect preserved children.
    for (let i = 0; i < connections.length; i++) {
      const conn = connections[i];
      if (conn) this.getInput(`ARG${i}`)?.connection?.connect(conn);
    }
  },
  saveConnections: function(this: blockly.Block, containerBlock: blockly.Block) {
    let itemBlock = containerBlock.getInputTargetBlock('STACK');
    let i = 0;
    while (itemBlock) {
      const input = this.getInput(`ARG${i}`);
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      (itemBlock as any).valueConnection_ = input?.connection?.targetConnection ?? null;
      itemBlock = itemBlock.getNextBlock();
      i++;
    }
  },
  updateShape_: function(this: blockly.Block & { argCount_: number }) {
    // Remove inputs beyond the current argCount.
    let i = 0;
    while (this.getInput(`ARG${i}`)) {
      if (i >= this.argCount_) this.removeInput(`ARG${i}`);
      i++;
    }
    // Add missing inputs up to argCount.
    for (let j = 0; j < this.argCount_; j++) {
      if (!this.getInput(`ARG${j}`)) {
        this.appendValueInput(`ARG${j}`).setCheck('proposition');
      }
    }
  },
};

// Helpers shared between specialize2's init and the mutator mixin.
// `appendArgInput` keeps the CONTROLS row (the `+` / `−` buttons) at
// the end of the block by always inserting new ARG slots before it.
function appendSpecialize2ArgInput(
  block: blockly.Block & { argCount_: number },
  i: number,
) {
  block.appendValueInput(`ARG${i}`).setCheck('proposition');
  block.moveInputBefore(`ARG${i}`, 'CONTROLS');
}

// Mixin applied to tactic_specialize2 via Blockly's mutator API.
// Blockly prohibits a plain extension from installing saveExtraState
// / loadExtraState ("mutation properties changed"), but allows it
// when registered as a mutator — even one without decompose/compose,
// which means no gear icon / popup mini-workspace is added.
const SPECIALIZE2_MIXIN = {
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
      appendSpecialize2ArgInput(this, this.argCount_);
      this.argCount_ += 1;
    }
    while (this.argCount_ > target) {
      this.argCount_ -= 1;
      this.removeInput(`ARG${this.argCount_}`);
    }
  },
};

// opt_helperFn for the specialize2 mutator: runs on every block init,
// zeroing argCount_ and attaching the +/- buttons in CONTROLS.
function specialize2Init(this: blockly.Block) {
  const self = this as blockly.Block & { argCount_: number };
  self.argCount_ = 0;

  const plusBtn = new blockly.FieldImage(
    PLUS_ICON_URI, 14, 14, '+',
    () => {
      const i = self.argCount_;
      appendSpecialize2ArgInput(self, i);
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

function defineSpecializeVariants() {
  blockly.defineBlocksWithJsonArray([
    // Main block for the mutator variant. The gear icon is added
    // automatically by Blockly when `mutator: '…'` is set.
    {
      'type': 'tactic_specialize1',
      'message0': 'specialize1 %1',
      'args0': [
        { 'type': 'input_value', 'name': 'HYP', 'check': 'proposition', 'align': 'LEFT' },
      ],
      'inputsInline': true,
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'style': 'logic_blocks',
      'tooltip': 'specialize (mutator variant)',
      'helpUrl': 'specialize',
      'mutator': 'specialize1_mutator',
    },
    // Top-level block for specialize1's mini-workspace. Holds a
    // statement stack of `specialize1_item` blocks; adding/removing
    // items on this stack drives `compose`.
    {
      'type': 'specialize1_container',
      'message0': 'arguments %1 %2',
      'args0': [
        { 'type': 'input_dummy' },
        { 'type': 'input_statement', 'name': 'STACK' },
      ],
      'style': 'logic_blocks',
      'tooltip': 'Drag `arg` blocks in or out to set the argument count.',
    },
    // One item in the specialize1 mini-workspace; each represents
    // exactly one ARG value input on the main block.
    {
      'type': 'specialize1_item',
      'message0': 'arg',
      'previousStatement': null,
      'nextStatement': null,
      'style': 'logic_blocks',
      'tooltip': 'One argument slot on the parent specialize block.',
    },
    // Main block for the +/- variant. CONTROLS holds the inline
    // buttons that grow/shrink the arg list.
    {
      'type': 'tactic_specialize2',
      'message0': 'specialize2 %1 %2',
      'args0': [
        { 'type': 'input_value', 'name': 'HYP', 'check': 'proposition', 'align': 'LEFT' },
        { 'type': 'input_dummy', 'name': 'CONTROLS' },
      ],
      'inputsInline': true,
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'style': 'logic_blocks',
      'tooltip': 'specialize (+/− variant)',
      'helpUrl': 'specialize',
      'mutator': 'specialize2_buttons',
    },
  ]);

  // Register mutator for specialize1. `opt_helperFn` runs on every
  // block init and sets the initial arity; `opt_blockList` is the
  // list of block types Blockly allows into the mini-workspace.
  if (!blockly.Extensions.isRegistered('specialize1_mutator')) {
    blockly.Extensions.registerMutator(
      'specialize1_mutator',
      SPECIALIZE1_MIXIN,
      function(this: { argCount_: number }) { this.argCount_ = 0; },
      ['specialize1_item'],
    );
  }
  if (!blockly.Extensions.isRegistered('specialize2_buttons')) {
    // Register as a mutator so we can legally install
    // saveExtraState / loadExtraState (Blockly refuses to let plain
    // extensions install those). No decompose/compose in the mixin
    // means Blockly skips the gear icon entirely — we just get the
    // serialization hooks and the helper-fn button setup.
    blockly.Extensions.registerMutator(
      'specialize2_buttons',
      SPECIALIZE2_MIXIN,
      specialize2Init,
    );
  }
}
