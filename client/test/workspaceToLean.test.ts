/**
 * Unit tests for workspaceToLean.
 *
 * The serialized Blockly state shape is the same one Blockly produces
 * via `blockly.serialization.workspaces.save`. We construct minimal
 * inputs by hand here to keep tests focused on the translator logic.
 */
import { workspaceToLean, emptyArmId } from '../src/workspaceToLean';
import type { BlocklyState } from '../src/Blockly';

// ── Tiny builders for serialized Blockly state ──────────────────────

type Block = {
  type: string;
  id?: string;
  fields?: Record<string, string>;
  inputs?: Record<string, { block?: Block; shadow?: Block }>;
  next?: { block?: Block };
};

function workspace(...topBlocks: Block[]): BlocklyState {
  return { blocks: { languageVersion: 0, blocks: topBlocks } } as BlocklyState;
}

function lemma(name: string, declaration: string, proofBlock?: Block): Block {
  return {
    type: 'lemma',
    id: `lemma-${name}`,
    fields: { THEOREM_NAME: name, THEOREM_DECLARATION: declaration },
    ...(proofBlock ? { inputs: { LEMMA_PROOF: { block: proofBlock } } } : {}),
  };
}

function tactic(type: string, fields: Record<string, string> = {}): Block {
  return { type, id: `${type}-1`, fields };
}

function prop(name: string): Block {
  return {
    type: 'prop',
    id: `prop-${name}`,
    fields: { PROP_NAME: name },
  };
}

function have(name: string, type: string, proofBlock?: Block): Block {
  return {
    type: 'tactic_have',
    id: `have-${name}`,
    fields: { NAME: name, TYPE: type },
    ...(proofBlock ? { inputs: { PROOF: { block: proofBlock } } } : {}),
  };
}

function constructor(body1?: Block, body2?: Block): Block {
  const inputs: Record<string, { block?: Block }> = {};
  if (body1) inputs.BODY1 = { block: body1 };
  if (body2) inputs.BODY2 = { block: body2 };
  return {
    type: 'tactic_constructor',
    id: 'constructor-1',
    ...(Object.keys(inputs).length > 0 ? { inputs } : {}),
  };
}

// ── Tests ────────────────────────────────────────────────────────────

describe('workspaceToLean', () => {
  describe('empty proof bodies emit `skip`', () => {
    test('lemma with no proof body emits `skip`', () => {
      const ws = workspace(lemma('the_problem', '(x : ℝ) (h : x = 5) : x = 5'));
      const { leanCode } = workspaceToLean(ws);
      expect(leanCode).toBe(
        'theorem the_problem (x : ℝ) (h : x = 5) : x = 5 := by\n' +
        '  skip\n'
      );
    });

    test('empty lemma proof body is keyed in sourceInfo (addressable position)', () => {
      const ws = workspace(lemma('the_problem', '(x : ℝ) : x = x'));
      const { sourceInfo } = workspaceToLean(ws);
      const skipInfo = sourceInfo.find(
        si => si.id === emptyArmId('lemma-the_problem', 'LEMMA_PROOF'),
      );
      expect(skipInfo).toBeDefined();
      expect(skipInfo!.startLineCol).toEqual([1, 0]); // the `  skip` line
    });

    test('have with no proof body emits `skip`', () => {
      const ws = workspace(
        lemma('foo', '(x : ℝ) : x = x', have('h', 'x = x')),
      );
      const { leanCode } = workspaceToLean(ws);
      expect(leanCode).toBe(
        'theorem foo (x : ℝ) : x = x := by\n' +
        '  have h : x = x := by\n' +
        '    skip\n' +
        '  skip\n'
      );
    });

    test('constructor with both branches empty emits two `· skip`s', () => {
      const ws = workspace(
        lemma('split', '(p q : Prop) (hp : p) (hq : q) : p ∧ q', constructor()),
      );
      const { leanCode } = workspaceToLean(ws);
      expect(leanCode).toBe(
        'theorem split (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n' +
        '  constructor\n' +
        '  · skip\n' +
        '  · skip\n' +
        '  skip\n'
      );
    });

    test('constructor with only first branch filled emits `· skip` for the second', () => {
      const ws = workspace(
        lemma(
          'split2',
          '(p q : Prop) (hp : p) (hq : q) : p ∧ q',
          constructor(tactic('tactic_refl')),
        ),
      );
      const { leanCode } = workspaceToLean(ws);
      // First branch uses the bulletized refl; second branch is the empty fallback.
      expect(leanCode).toContain('· rfl\n');
      expect(leanCode).toContain('· skip\n');
    });
  });

  describe('non-empty bodies are unaffected (sanity)', () => {
    test('lemma with a single rfl tactic', () => {
      const ws = workspace(
        lemma('refl_example', '(x : ℝ) : x = x', tactic('tactic_refl')),
      );
      const { leanCode } = workspaceToLean(ws);
      expect(leanCode).toBe(
        'theorem refl_example (x : ℝ) : x = x := by\n' +
        '  rfl\n' +
        '  skip\n'
      );
    });

    test('simp tactic emits simp', () => {
      const ws = workspace(
        lemma('simp_example', '(x : ℝ) : x = x', tactic('tactic_simp')),
      );
      const { leanCode } = workspaceToLean(ws);
      expect(leanCode).toBe(
        'theorem simp_example (x : ℝ) : x = x := by\n' +
        '  simp\n' +
        '  skip\n'
      );
    });

    test('source info is produced for the lemma block', () => {
      const ws = workspace(lemma('the_problem', '(x : ℝ) (h : x = 5) : x = 5'));
      const { sourceInfo } = workspaceToLean(ws);
      const lemmaInfo = sourceInfo.find(si => si.id === 'lemma-the_problem');
      expect(lemmaInfo).toBeDefined();
      expect(lemmaInfo!.startLineCol).toEqual([0, 0]);
    });

    test('rewrite tactic emits rewrite instead of rw', () => {
      const ws = workspace(
        lemma(
          'rewrite_example',
          '(x : ℝ) (h : x = 5) : x = 5',
          {
            type: 'tactic_rewrite',
            id: 'rewrite-1',
            fields: { DIRECTION_TYPE: 'RIGHT' },
            inputs: {
              REWRITE_SOURCE: {
                block: {
                  type: 'prop',
                  id: 'prop-h',
                  fields: { PROP_NAME: 'h' },
                },
              },
            },
          },
        ),
      );
      const { leanCode } = workspaceToLean(ws);
      expect(leanCode).toBe(
        'theorem rewrite_example (x : ℝ) (h : x = 5) : x = 5 := by\n' +
        '  rewrite [h]\n' +
        '  skip\n'
      );
      expect(leanCode).not.toContain('rw [h]');
    });

    test('specialize with no args emits bare `specialize hyp`', () => {
      // The smart-affordance flow creates a specialize block with only
      // HYP filled — ARG and any +/- args are unconnected. Codegen must
      // omit the parenthesized arg slots entirely rather than emit `()`.
      const ws = workspace(
        lemma(
          'specialize_no_arg',
          '(hf : ∀ x, x = x) : True',
          {
            type: 'tactic_specialize',
            id: 'specialize-1',
            inputs: {
              HYP: {
                block: { type: 'prop', id: 'prop-hf', fields: { PROP_NAME: 'hf' } },
              },
            },
          },
        ),
      );
      const { leanCode } = workspaceToLean(ws);
      expect(leanCode).toContain('specialize hf\n');
      expect(leanCode).not.toContain('()');
    });

    test('specialize with one arg wraps it in parens', () => {
      const ws = workspace(
        lemma(
          'specialize_one_arg',
          '(hf : ∀ x, x = x) (y : ℕ) : True',
          {
            type: 'tactic_specialize',
            id: 'specialize-1',
            inputs: {
              HYP: {
                block: { type: 'prop', id: 'prop-hf', fields: { PROP_NAME: 'hf' } },
              },
              ARG: {
                block: { type: 'prop', id: 'prop-y', fields: { PROP_NAME: 'y' } },
              },
            },
          },
        ),
      );
      const { leanCode } = workspaceToLean(ws);
      expect(leanCode).toContain('specialize hf (y)\n');
    });

    test('specialize skips empty extra-arg slots', () => {
      // Even if the user adds extra arg slots via +/- but leaves some
      // empty, codegen should skip the empty ones rather than emit `()`.
      const ws = workspace(
        lemma(
          'specialize_sparse',
          '(hf : ∀ x y, x = y) (a b : ℕ) : True',
          {
            type: 'tactic_specialize',
            id: 'specialize-1',
            inputs: {
              HYP: {
                block: { type: 'prop', id: 'prop-hf', fields: { PROP_NAME: 'hf' } },
              },
              ARG: {
                block: { type: 'prop', id: 'prop-a', fields: { PROP_NAME: 'a' } },
              },
              ARG1: { },
            },
          },
        ),
      );
      const { leanCode } = workspaceToLean(ws);
      expect(leanCode).toContain('specialize hf (a)\n');
      expect(leanCode).not.toContain('()');
    });

    test('rewrite at tactic emits bracketed rewrite syntax', () => {
      const ws = workspace(
        lemma(
          'rewrite_at_example',
          '(x y : ℝ) (h : x = y) (h2 : x = x) : x = x',
          {
            type: 'tactic_rewrite_at',
            id: 'rewrite-at-1',
            inputs: {
              REWRITE_SOURCE: {
                block: {
                  type: 'prop',
                  id: 'prop-h',
                  fields: { PROP_NAME: 'h' },
                },
              },
              REWRITE_TARGET: {
                block: {
                  type: 'prop',
                  id: 'prop-h2',
                  fields: { PROP_NAME: 'h2' },
                },
              },
            },
          },
        ),
      );
      const { leanCode } = workspaceToLean(ws);
      expect(leanCode).toBe(
        'theorem rewrite_at_example (x y : ℝ) (h : x = y) (h2 : x = x) : x = x := by\n' +
        '  rewrite [h] at h2\n' +
        '  skip\n'
      );
    });

    test('intro codegen reads the NAME text fields', () => {
      const ws = workspace(
        lemma(
          'intro_many',
          '(p q r : Prop) : p → q → r → p',
          {
            type: 'tactic_intro',
            id: 'intro-many',
            fields: { NAME: 'hp', NAME_1: 'hq', NAME_2: 'hr' },
          },
        ),
      );
      const { leanCode } = workspaceToLean(ws);
      expect(leanCode).toBe(
        'theorem intro_many (p q r : Prop) : p → q → r → p := by\n' +
        '  intro hp hq hr\n' +
        '  skip\n'
      );
    });

    test('use emits multiple argument bubbles separated by commas', () => {
      const ws = workspace(
        lemma(
          'use_many',
          ': ∃ x : ℝ, ∃ y : ℝ, x = y',
          {
            type: 'tactic_use',
            id: 'use-many',
            inputs: {
              ARG: { block: prop('a') },
              ARG1: { shadow: prop('b') },
              ARG2: { shadow: prop('c') },
            },
          },
        ),
      );
      const { leanCode } = workspaceToLean(ws);
      expect(leanCode).toBe(
        'theorem use_many : ∃ x : ℝ, ∃ y : ℝ, x = y := by\n' +
        '  use a, b, c\n' +
        '  skip\n'
      );
    });

    test('conv emits a post-conv `skip` anchor for the trailing goal marker', () => {
      const ws = workspace(
        lemma('c', ': a = a', {
          type: 'tactic_conv',
          id: 'conv-1',
          inputs: {
            BODY: {
              block: { type: 'tactic_enter', id: 'enter-1', fields: { ENTER_PATH: '[1]' } },
            },
          },
        }),
      );
      const { leanCode, sourceInfo } = workspaceToLean(ws);
      // The trailing `skip` is the last conv step (conv mode, body indent).
      expect(leanCode).toContain('  conv =>\n    enter [1]\n    skip\n');
      // …and is addressable for the trailing (AFTER) marker.
      expect(sourceInfo.some(s => s.id === emptyArmId('conv-1', 'AFTER'))).toBe(true);
    });
  });

  // ── Ported from the previous client/test/test-workspaceToLean.ts ────
  // The fixture below was originally written when lemma variables lived
  // in a separate `VARIABLES` input populated with `prop_declaration`
  // blocks. The data model has since been refactored: the full signature
  // (variables + goal) now lives directly in THEOREM_DECLARATION, and
  // workspaceToLean no longer reads a VARIABLES input on lemmas.

  describe('full example workspace', () => {
    const example1Data = { "blocks": { "languageVersion": 0, "blocks": [{ "type": "lemma", "id": "3yAUmdNL2=WYh]Gxi)]X", "x": 13, "y": 22, "fields": { "THEOREM_NAME": "away", "THEOREM_DECLARATION": "(y : ℝ) (hy : y ≠ 1) : (y^2 - 1) / (y - 1) = y + 1" }, "inputs": { "LEMMA_PROOF": { "block": { "type": "tactic_other", "id": "k}|H70s[,ot=/1U@K_,;", "fields": { "PROP_NAME": "grind" } } } } }, { "type": "lemma", "id": "DemnP%+kbpZdIIe~0(3W", "x": 308, "y": 35, "fields": { "THEOREM_NAME": "fun_limit_fact", "THEOREM_DECLARATION": "FunLimAt (fun x => (x^2 - 1) / (x - 1)) 2 1" }, "inputs": { "LEMMA_PROOF": { "block": { "type": "tactic_unfold", "id": "4jk;hHJ|_aSp.)2PU`Gc", "inputs": { "ARG": { "block": { "type": "prop", "id": "Mojm{fSn$rJvFC81z{h(", "fields": { "PROP_NAME": "FunLimAt" } } } }, "next": { "block": { "type": "tactic_intro", "id": "^=/m!cJjN6xgQ.RpEN]y", "fields": { "NAME": "ε" }, "next": { "block": { "type": "tactic_intro", "id": "MK{[.T(RH!$~`CKvXmL1", "fields": { "NAME": "hε" }, "next": { "block": { "type": "tactic_use", "id": "QPSB(Ek%b~pXS8}W4?4/", "inputs": { "ARG": { "block": { "type": "prop", "id": "^XKO;%FbY-Cl)sU%fNl;", "fields": { "PROP_NAME": "ε" } } } }, "next": { "block": { "type": "tactic_constructor", "id": "C=S-)mM.)`C``sWq!YlT", "inputs": { "BODY1": { "block": { "type": "tactic_other", "id": "m.6n,uHODs!Ns?ycFg`M", "fields": { "PROP_NAME": "linarith" } } }, "BODY2": { "block": { "type": "tactic_intro", "id": "4Nh1ti#nH_#d-A3V$e|_", "fields": { "NAME": "y" }, "next": { "block": { "type": "tactic_intro", "id": "fxEi-:)M^j3ee76?Z9l+", "fields": { "NAME": "hy" }, "next": { "block": { "type": "tactic_intro", "id": "]@#*lMzE^dbkiR]{PhGo", "fields": { "NAME": "hy2" }, "next": { "block": { "type": "tactic_other", "id": "3#gT|oNu-}[}3uB_a.2U", "fields": { "PROP_NAME": "simp" }, "next": { "block": { "type": "tactic_rewrite", "id": "f5piLnWwQvlx,Ki5WTp4", "fields": { "DIRECTION_TYPE": "RIGHT" }, "inputs": { "REWRITE_SOURCE": { "block": { "type": "prop", "id": "G.]vQSXK]?]G9T#)g+sJ", "fields": { "PROP_NAME": "away y hy" } } } }, "next": { "block": { "type": "tactic_rewrite", "id": "W|.ZlRq5@bi.2CML=mPB", "fields": { "DIRECTION_TYPE": "RIGHT" }, "inputs": { "REWRITE_SOURCE": { "block": { "type": "tactic_show", "id": "3{s96}qox|({ahT!Azz)", "inputs": { "GOAL": { "block": { "type": "prop", "id": "!bFf)T7:^+.{UW4*Cf*}", "fields": { "PROP_NAME": "y + 1 - 2 = y - 1" } } }, "PROOF": { "block": { "type": "tactic_other", "id": "fqI`{J4OU;d~Kx3hWy%e", "fields": { "PROP_NAME": "grind" } } } } } } }, "next": { "block": { "type": "tactic_exact", "id": "HSp12q.iHmw-1[hrEQB@", "inputs": { "ARG": { "block": { "type": "prop", "id": ",)45@UUo`{kGa5cYgWS8", "fields": { "PROP_NAME": "hy2" } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } }] } } as BlocklyState;

    const expectedOutput = `theorem away (y : ℝ) (hy : y ≠ 1) : (y^2 - 1) / (y - 1) = y + 1 := by
  grind
  skip

theorem fun_limit_fact FunLimAt (fun x => (x^2 - 1) / (x - 1)) 2 1 := by
  unfold FunLimAt
  intro ε
  intro hε
  use ε
  constructor
  · linarith
    skip
  · intro y
    intro hy
    intro hy2
    simp
    rewrite [away y hy]
    rewrite [show y + 1 - 2 = y - 1 by
        grind]
    exact hy2
    skip
  skip
`;

    test('converts the example workspace to expected Lean code', () => {
      const result = workspaceToLean(example1Data);
      expect(result.leanCode).toBe(expectedOutput);
    });

    test('produces sourceInfo for blocks in the example', () => {
      const result = workspaceToLean(example1Data);
      expect(result.sourceInfo.length).toBeGreaterThan(0);
      // The "away" lemma block is tracked.
      const awayLemma = result.sourceInfo.find(s => s.id === '3yAUmdNL2=WYh]Gxi)]X');
      expect(awayLemma).toBeDefined();
      expect(awayLemma!.startLineCol[0]).toBe(0);
    });
  });

  describe('UTF-16 column counting', () => {
    test('characters outside BMP count as 2 UTF-16 code units', () => {
      // 𝕜 (U+1D55C, blackboard-bold k) is outside BMP and takes 2 UTF-16
      // code units. LSP uses UTF-16 columns, so the translator must
      // count them that way.
      const ws = {
        blocks: {
          languageVersion: 0,
          blocks: [{
            type: 'lemma',
            id: 'test-lemma',
            fields: {
              THEOREM_NAME: 'test',
              THEOREM_DECLARATION: ': 𝕜 = 𝕜',
            },
            inputs: {
              LEMMA_PROOF: {
                block: {
                  type: 'tactic_other',
                  id: 'test-tactic',
                  fields: { PROP_NAME: 'rfl' },
                },
              },
            },
          }],
        },
      } as BlocklyState;

      const result = workspaceToLean(ws);

      // The tactic starts on line 1, col 2 (after the "  " indent).
      const tacticInfo = result.sourceInfo.find(s => s.id === 'test-tactic');
      expect(tacticInfo).toBeDefined();
      expect(tacticInfo!.startLineCol).toEqual([1, 2]);
      expect(tacticInfo!.endLineCol).toEqual([2, 0]); // ends after newline
    });
  });

  test('convert emits a NAS theorem application at the presentation depth', () => {
    const theoremTerm: Block = {
      type: 'term_nas_even_total_relation_counts',
      id: 'nas-even-total',
      inputs: {
        SET: { block: prop('Party') },
        SYMMETRY: { block: prop('Handshake_symm') },
        IRREFLEXIVITY: { block: prop('Handshake_irref') },
      },
    };
    const convert: Block = {
      type: 'tactic_convert',
      id: 'convert-nas-helper',
      inputs: { ARG: { block: theoremTerm } },
    };

    const { leanCode } = workspaceToLean(
      workspace(lemma('demo', ': Even total', convert)),
    );

    expect(leanCode).toBe(
      'theorem demo : Even total := by\n' +
      '  convert even_sum_relation_counts (Party) (Handshake_symm) ' +
      '(Handshake_irref) using 3\n' +
      '  skip\n',
    );
  });

  test('let block emits a typed local definition from its three text fields', () => {
    const letBlock: Block = {
      type: 'tactic_let',
      id: 'let-total',
      fields: {
        NAME: 'NumTotHandshakes',
        TYPE: 'ℕ',
        DEFINITION: '∑ x ∈ Party, HandshakeCount x',
      },
    };

    const { leanCode } = workspaceToLean(
      workspace(lemma('demo', ': True', letBlock)),
    );

    expect(leanCode).toBe(
      'theorem demo : True := by\n' +
      '  let NumTotHandshakes : ℕ := ∑ x ∈ Party, HandshakeCount x\n' +
      '  skip\n',
    );
  });

  describe('broad block ranges', () => {
    // Generated text:
    //   theorem foo : T := by      line 0   block L
    //     constructor              line 1   block C
    //     · rfl                    line 2   block r1
    //       skip                   line 3   (C BODY1 anchor)
    //     · rfl                    line 4   block r2
    //       skip                   line 5   (C BODY2 anchor)
    //     skip                     line 6   (L LEMMA_PROOF anchor)
    const ws = workspace({
      type: 'lemma',
      id: 'L',
      fields: { THEOREM_NAME: 'foo', THEOREM_DECLARATION: ': T' },
      inputs: {
        LEMMA_PROOF: {
          block: {
            type: 'tactic_constructor',
            id: 'C',
            inputs: {
              BODY1: { block: { type: 'tactic_refl', id: 'r1' } },
              BODY2: { block: { type: 'tactic_refl', id: 'r2' } },
            },
          },
        },
      },
    });

    test('a block range covers its whole rendered subtree, anchors included', () => {
      const { blockRanges } = workspaceToLean(ws);
      const byId = new Map(blockRanges.map(b => [b.id, b]));
      // Lemma spans the theorem line through its trailing `skip` anchor.
      expect(byId.get('L')).toMatchObject({ startLineCol: [0, 0], endLineCol: [7, 0] });
      // Constructor spans the `constructor` keyword through its second arm's
      // `skip`, but NOT the lemma's trailing skip on line 6.
      expect(byId.get('C')).toMatchObject({ startLineCol: [1, 2], endLineCol: [6, 0] });
    });

    test('ranges nest by containment and a leaf covers only its own line', () => {
      const { blockRanges } = workspaceToLean(ws);
      const byId = new Map(blockRanges.map(b => [b.id, b]));
      const L = byId.get('L')!, C = byId.get('C')!, r1 = byId.get('r1')!;
      // r1 is just the first `rfl` line — not the synthesized arm skip below it.
      expect(r1).toMatchObject({ startLineCol: [2, 4], endLineCol: [3, 0] });
      // Containment: L ⊇ C ⊇ r1.
      const encloses = (a: typeof L, b: typeof L) =>
        a.startLineCol[0] <= b.startLineCol[0] && b.endLineCol[0] <= a.endLineCol[0];
      expect(encloses(L, C)).toBe(true);
      expect(encloses(C, r1)).toBe(true);
    });
  });
});
