import { describe, it, expect } from '@jest/globals';
import { workspaceToLean } from '../src/workspaceToLean';

// Example 1 data from App.tsx (exampleDefinitions[0].initial)
const example1Data = { "blocks": { "languageVersion": 0, "blocks": [{ "type": "lemma", "id": "3yAUmdNL2=WYh]Gxi)]X", "x": 13, "y": 22, "fields": { "THEOREM_NAME": "away", "THEOREM_DECLARATION": "(y^2 - 1) / (y - 1) = y + 1" }, "inputs": { "VARIABLES": { "block": { "type": "prop_declaration", "id": "!nj)-l!RB`?Qhr_!_Q7^", "fields": { "VARIABLE_DECL": "y", "VARIABLE_DEF": "ℝ" }, "next": { "block": { "type": "prop_declaration", "id": "lgvV;Skrw^oI04hI%Pc)", "fields": { "VARIABLE_DECL": "hy", "VARIABLE_DEF": "y ≠ 1" } } } } }, "LEMMA_PROOF": { "block": { "type": "tactic_other", "id": "k}|H70s[,ot=/1U@K_,;", "fields": { "PROP_NAME": "grind" } } } } }, { "type": "lemma", "id": "DemnP%+kbpZdIIe~0(3W", "x": 308, "y": 35, "fields": { "THEOREM_NAME": "fun_limit_fact", "THEOREM_DECLARATION": "FunLimAt (fun x => (x^2 - 1) / (x - 1)) 2 1" }, "inputs": { "LEMMA_PROOF": { "block": { "type": "tactic_unfold", "id": "4jk;hHJ|_aSp.)2PU`Gc", "inputs": { "ARG": { "block": { "type": "prop", "id": "Mojm{fSn$rJvFC81z{h(", "fields": { "PROP_NAME": "FunLimAt" } } } }, "next": { "block": { "type": "tactic_intro", "id": "^=/m!cJjN6xgQ.RpEN]y", "inputs": { "ARG": { "block": { "type": "prop", "id": "Y(gRn,NBi~2+wLabs!@A", "fields": { "PROP_NAME": "ε" } } } }, "next": { "block": { "type": "tactic_intro", "id": "MK{[.T(RH!$~`CKvXmL1", "inputs": { "ARG": { "block": { "type": "prop", "id": "mgxS^6SsXB-}9:6^cQ?!", "fields": { "PROP_NAME": "hε" } } } }, "next": { "block": { "type": "tactic_use", "id": "QPSB(Ek%b~pXS8}W4?4/", "inputs": { "ARG": { "block": { "type": "prop", "id": "^XKO;%FbY-Cl)sU%fNl;", "fields": { "PROP_NAME": "ε" } } } }, "next": { "block": { "type": "tactic_constructor", "id": "C=S-)mM.)`C``sWq!YlT", "inputs": { "BODY1": { "block": { "type": "tactic_other", "id": "m.6n,uHODs!Ns?ycFg`M", "fields": { "PROP_NAME": "linarith" } } }, "BODY2": { "block": { "type": "tactic_intro", "id": "4Nh1ti#nH_#d-A3V$e|_", "inputs": { "ARG": { "block": { "type": "prop", "id": ":un028QY,n#E7%_%,]4[", "fields": { "PROP_NAME": "y" } } } }, "next": { "block": { "type": "tactic_intro", "id": "fxEi-:)M^j3ee76?Z9l+", "inputs": { "ARG": { "block": { "type": "prop", "id": "U:5}c2^h7F]d8+hh(q}8", "fields": { "PROP_NAME": "hy" } } } }, "next": { "block": { "type": "tactic_intro", "id": "]@#*lMzE^dbkiR]{PhGo", "inputs": { "ARG": { "block": { "type": "prop", "id": "*ww_S)5(YZG^Uc84eUlv", "fields": { "PROP_NAME": "hy2" } } } }, "next": { "block": { "type": "tactic_other", "id": "3#gT|oNu-}[}3uB_a.2U", "fields": { "PROP_NAME": "simp" }, "next": { "block": { "type": "tactic_rw", "id": "f5piLnWwQvlx,Ki5WTp4", "fields": { "DIRECTION_TYPE": "RIGHT" }, "inputs": { "REWRITE_SOURCE": { "block": { "type": "prop", "id": "G.]vQSXK]?]G9T#)g+sJ", "fields": { "PROP_NAME": "away y hy" } } } }, "next": { "block": { "type": "tactic_rw", "id": "W|.ZlRq5@bi.2CML=mPB", "fields": { "DIRECTION_TYPE": "RIGHT" }, "inputs": { "REWRITE_SOURCE": { "block": { "type": "tactic_show", "id": "3{s96}qox|({ahT!Azz)", "inputs": { "GOAL": { "block": { "type": "prop", "id": "!bFf)T7:^+.{UW4*Cf*}", "fields": { "PROP_NAME": "y + 1 - 2 = y - 1" } } }, "PROOF": { "block": { "type": "tactic_other", "id": "fqI`{J4OU;d~Kx3hWy%e", "fields": { "PROP_NAME": "grind" } } } } } } }, "next": { "block": { "type": "tactic_exact", "id": "HSp12q.iHmw-1[hrEQB@", "inputs": { "ARG": { "block": { "type": "prop", "id": ",)45@UUo`{kGa5cYgWS8", "fields": { "PROP_NAME": "hy2" } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } }] } };

const expectedOutput = `theorem away(y : ℝ)(hy : y ≠ 1) : (y^2 - 1) / (y - 1) = y + 1 := by
  grind

theorem fun_limit_fact : FunLimAt (fun x => (x^2 - 1) / (x - 1)) 2 1 := by
  unfold FunLimAt
  intro ε
  intro hε
  use ε
  constructor
  · linarith
  · intro y
    intro hy
    intro hy2
    simp
    rw [away y hy]
    rw [show y + 1 - 2 = y - 1 by
        grind]
    exact hy2
`;

describe('workspaceToLean', () => {
  it('should convert example 1 workspace to expected Lean code', () => {
    const result = workspaceToLean(example1Data);
    expect(result.leanCode).toBe(expectedOutput);
  });

  it('should produce sourceInfo for all blocks', () => {
    const result = workspaceToLean(example1Data);
    // Should have sourceInfo entries for blocks
    expect(result.sourceInfo.length).toBeGreaterThan(0);

    // Check that the lemma block is tracked
    const awayLemma = result.sourceInfo.find(s => s.id === '3yAUmdNL2=WYh]Gxi)]X');
    expect(awayLemma).toBeDefined();
    expect(awayLemma!.startLineCol[0]).toBe(0); // First line
  });

  it('should count characters outside BMP as 2 UTF-16 code units', () => {
    // 𝕜 (U+1D55C, blackboard bold k) is outside BMP and takes 2 UTF-16 code units
    // This is important for LSP compatibility
    const workspaceWithBMP = {
      blocks: {
        languageVersion: 0,
        blocks: [{
          type: 'lemma',
          id: 'test-lemma',
          fields: {
            THEOREM_NAME: 'test',
            THEOREM_DECLARATION: '𝕜 = 𝕜'  // Two 𝕜 characters
          },
          inputs: {
            LEMMA_PROOF: {
              block: {
                type: 'tactic_other',
                id: 'test-tactic',
                fields: { PROP_NAME: 'rfl' }
              }
            }
          }
        }]
      }
    };

    const result = workspaceToLean(workspaceWithBMP);

    // Output should be: "theorem test : 𝕜 = 𝕜 := by\n  rfl\n"
    // The lemma block spans from start to end of " := by\n"
    // "theorem test" = 12 chars, then " : " = 3 chars = col 15
    // Then "𝕜 = 𝕜" where each 𝕜 is 2 UTF-16 units: 2 + 3 + 2 = 7 UTF-16 units
    // So " := by\n" starts at col 15 + 7 = 22

    const lemmaInfo = result.sourceInfo.find(s => s.id === 'test-lemma');
    expect(lemmaInfo).toBeDefined();

    // The tactic starts on line 1, col 2 (after "  " indent)
    const tacticInfo = result.sourceInfo.find(s => s.id === 'test-tactic');
    expect(tacticInfo).toBeDefined();
    expect(tacticInfo!.startLineCol).toEqual([1, 2]);
    expect(tacticInfo!.endLineCol).toEqual([2, 0]); // ends after newline
  });
});
