# Project Log

## 2026-05-22

### Working decisions

- The main work folder is `lean-blockly-test`.
- The redesign document currently lives in `Projects/MathlibDemo/REAL_ANALYSIS_REDESIGN.md`, next to `LeanTests.lean`; this is a good location because the pedagogical plan and the tactic-strength test harness should evolve together.
- `RealAnalysisGame/` is now a reference archive for the original game.
  - Use it for theorem statements, legacy level flow, inventory names, and old dependency structure.
  - Do not treat it as the active implementation target for the redesign.
- `verbose-lean4/` is a reference repo for technical suggestions, especially special-purpose tactics and proof ergonomics.
- `real-analysis-gameV2/` is frozen for now.
  - It will be the book version later.
  - Porting to the book should happen only after the redesigned game flow is stable.

### Current interpretation of the repos

- `lean-blockly-test` is the executable redesign target.
- `REAL_ANALYSIS_REDESIGN.md` is the curriculum and world-graph planning surface.
- `LeanTests.lean` is the proving ground for tactic design.
  - It should grow into a representative testbed for the whole game.
  - It should check that custom tactics are not too weak and not too strong.

### Risks noticed so far

- The redesign proposal exists in more than one repo. That invites drift.
- The old game is lecture-centric, while the redesign is topic-first. Mapping between them is useful, but the old structure should not drive new architecture.
- The book repo already has its own structure and registries, so adapting it too early would create duplicated redesign work.

### Practical guidance going forward

- Keep the redesign source of truth in one place.
- Use `RealAnalysisGame` only to extract statements, ordering, and missing content.
- Use `LeanTests.lean` to validate closing tactics and affordance boundaries before scaling out level generation.
- Delay book synchronization until the redesigned world map and level inventory stop moving.

### Open questions

- Which single file is the canonical redesign spec if multiple copies remain in the workspace?
- What is the target schema for a fully redesigned world in `lean-blockly-test`?
- Which tactics belong in the front-loaded proof tutorial versus later, world-specific unlocks?
