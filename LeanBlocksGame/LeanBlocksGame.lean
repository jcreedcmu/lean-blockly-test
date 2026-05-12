import LeanBlocksGame.AbstractCtx
import LeanBlocksGame.Commands
import LeanBlocksGame.EnvExtensions
import LeanBlocksGame.Graph
import LeanBlocksGame.Helpers.PrettyPrinter
import LeanBlocksGame.Helpers
import LeanBlocksGame.Hints
import LeanBlocksGame.Inventory
import LeanBlocksGame.Options
import LeanBlocksGame.SaveData
import LeanBlocksGame.Structures
import LeanBlocksGame.Tactic.LetIntros
import LeanBlocksGame.Utils

/-!
# LeanBlocksGame

A Lean DSL for defining Blockly-based proof games. Forked from the
game-definition subset of lean4game's `GameServer` package
(https://github.com/leanprover-community/lean4game, `server/` directory).

The fork copies the 17 definition-oriented files (commands, data
structures, environment extensions, JSON export) and excludes the 4
server/runtime files (Game.lean, RpcHandlers.lean, Runner.lean,
InteractiveGoal.lean). Modifications from upstream:

- Namespace renamed from `GameServer` to `LeanBlocksGame`.
- `I18n` dependency removed (all `.translate` calls stripped).
- `RpcHandlers` import removed from `Commands.lean`.
- Blockly-specific fields added to `GameLevel` (`allowedBlocks`,
  `allowedAffordances`, `allAffordances`, `theoremBlockLabel`).
- Blockly-specific DSL commands added (`AllowBlock`, `AllowAffordance`,
  `AllowAllAffordances`, `TheoremBlockLabel`).
-/
