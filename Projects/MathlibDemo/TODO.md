# TODO

## Immediate

- Choose one canonical redesign document and treat all other copies as reference-only.
- Build a migration checklist from the old lecture worlds to the new topic-first worlds.
- Expand `LeanTests.lean` so each custom tactic has:
  - positive examples that should succeed
  - negative examples that should fail
  - comments explaining the intended strength boundary

## Redesign work

- Finalize the world list and dependency graph in `REAL_ANALYSIS_REDESIGN.md`.
- Decide world-by-world boss theorems and helper levels.
- Mark levels as one of:
  - already present in old game
  - present but needs refactor
  - missing and must be authored from scratch
- Standardize naming for worlds, levels, and theorem identifiers in `lean-blockly-test`.

## Testing infrastructure

- Decide whether `LeanTests.lean` stays as one growing file or splits into sections/files by world.
- Add a repeatable way to run the tests locally and record expected failures versus regressions.
- Track tactic coverage for:
  - closing tactics like `conclude`
  - structural tactics such as `choose`, `fix`, `assume`, `plug`, `feed`
  - specialized arithmetic or simplification tactics borrowed from `verbose-lean4` when appropriate

## Content extraction from references

- Use `RealAnalysisGame/LECTURE_LEVELS.md` and the original Lean files to harvest:
  - theorem statements
  - introduction/conclusion text worth preserving
  - legacy unlock flow that still makes sense
- Use `verbose-lean4` to collect candidate technical ideas, but only adopt ones that fit the intended student-facing proof language.

## Deferred until game redesign stabilizes

- Keep `real-analysis-gameV2` frozen.
- Do not port redesigned content to the book yet.
- Once the game flow is stable, define the export/import boundary from the game redesign to the book.

## Likely missing at this stage

- A short source-of-truth note in the redesign doc itself saying which repos are active, reference-only, or frozen.
- A lightweight naming convention for redesigned worlds and files before more implementation lands.
- A habit of recording tactic-design decisions in `LeanTests.lean` comments or the project log as they are made.
