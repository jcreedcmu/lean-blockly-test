import LeanBlocksGame.EnvExtensions

namespace LeanBlocksGame

open Lean Meta Elab Command Std

/-! ## Copy images -/

open IO.FS System FilePath in
/-- Copies the folder `images/` to `.lake/gamedata/images/` -/
def copyImages : IO Unit := do
  let target : FilePath := ".lake" / "gamedata"
  if ← FilePath.pathExists "images" then
    for file in ← walkDir "images" do
      let outFile := target.join file
      -- create the directories
      if ← file.isDir then
        createDirAll outFile
      else
        if let some parent := outFile.parent then
          createDirAll parent
        -- copy file
        let content ← readBinFile file
        writeBinFile outFile content

namespace GameData
  def gameDataPath : System.FilePath := ".lake" / "gamedata"
  def gameFileName := s!"game.json"
  def docFileName := fun (inventoryType : InventoryType) (name : Name) => s!"doc__{inventoryType}__{name}.json"
  def levelFileName := fun (worldId : Name) (levelId : Nat) => s!"level__{worldId}__{levelId}.json"
  def inventoryFileName := s!"inventory.json"
end GameData

open GameData in
-- TODO: register all of this as ToJson instance?
def saveGameData (allItemsByType : HashMap InventoryType (HashSet Name))
    (inventory : InventoryOverview): CommandElabM Unit := do
  let game ← getCurGame
  let env ← getEnv
  let path := (← IO.currentDir) / gameDataPath

  if ← path.isDir then
    IO.FS.removeDirAll path
  IO.FS.createDirAll path

  -- copy the images folder
  copyImages

  for (worldId, world) in game.worlds.nodes.toArray do
    for (levelId, level) in world.levels.toArray do
      -- Start with the existing LevelInfo JSON
      let levelJson := toJson (level.toInfo env)
      -- Compute the theoremName: use the explicit name if given, else WorldId_LevelIdx
      let theoremName : String := match level.statementName with
        | .anonymous => s!"{worldId}_{levelId}"
        | name => name.toString
      -- Compute the permissions array in the LevelPermission discriminated-union format
      let mut perms : Array Json := #[]
      for block in level.allowedBlocks do
        perms := perms.push (Json.mkObj [("t", "allowTactic"), ("tacticName", toJson block)])
      for aff in level.allowedAffordances do
        perms := perms.push (Json.mkObj [("t", "allowAffordance"), ("affordance", toJson aff)])
      if level.allAffordances then
        perms := perms.push (Json.mkObj [("t", "allowAllAffordances")])
      -- Merge Blockly-specific fields
      let blocklyFields := Json.mkObj [
        ("name", toJson level.title),
        ("theoremName", toJson theoremName),
        ("theoremStatement", toJson level.theoremStatement),
        ("theoremBlockLabel", toJson level.theoremBlockLabel),
        ("permissions", toJson perms)
      ]
      let mergedJson := levelJson.mergeObj blocklyFields
      IO.FS.writeFile (path / levelFileName worldId levelId) (toString mergedJson)

  IO.FS.writeFile (path / gameFileName) (toString (getGameJson game))

  for inventoryType in [InventoryType.Theorem, .Tactic, .Definition] do
    for name in allItemsByType.getD inventoryType {} do
      let some item ← getInventoryItem? name inventoryType
        | continue -- TODO: cleanup. Hidden items should also not appear in `allItemsByType`
      IO.FS.writeFile (path / docFileName inventoryType name) (toString (toJson item))

  IO.FS.writeFile (path / inventoryFileName) (toString (toJson inventory))



open GameData

def loadData (f : System.FilePath) (α : Type) [FromJson α] : IO α := do
  let str ← IO.FS.readFile f
  let json ← match Json.parse str with
  | .ok v => pure v
  | .error e => throw (IO.userError e)
  let data ← match fromJson? json with
  | .ok v => pure v
  | .error e => throw (IO.userError e)
  return data

def loadGameData (gameDir : System.FilePath) : IO Game :=
  loadData (gameDir / gameDataPath / gameFileName) Game

def loadLevelData (gameDir : System.FilePath) (worldId : Name) (levelId : Nat) : IO LevelInfo :=
  loadData (gameDir / gameDataPath / levelFileName worldId levelId) LevelInfo
