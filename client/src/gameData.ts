import type { BlocklyState } from './Blockly.tsx';

// ── Public types ────────────────────────────────────────────────────

export type LevelPermission =
  | { t: 'allowTactic'; tacticName: string }
  | { t: 'allowAffordance'; affordance: 'rewrite' | 'apply' | 'use' | 'choose' }
  | { t: 'allowAllAffordances' };

export type TutorialAction =
  | { kind: 'openToolboxCategory'; category: string };

export type TutorialStep = {
  target: string;
  spotlightTarget?: string;
  title?: string;
  content: string;
  placement?: 'top' | 'right' | 'bottom' | 'left' | 'auto' | 'center';
  offset?: number;
  targetWaitTimeout?: number;
  skipScroll?: boolean;
  actions?: TutorialAction[];
  conditions?: TutorialCondition[];
  advanceDelayMs?: number;
};

export type TutorialBlockPattern = {
  type: string;
  fields?: Record<string, string>;
  inputs?: Record<string, TutorialBlockPattern>;
};

export type TutorialCondition =
  | {
      kind: 'workspaceHasBlock';
      block: TutorialBlockPattern;
      location?: 'any' | 'topLevel' | 'theoremProof';
    }
  | {
      kind: 'elementExists';
      selector: string;
      visible?: boolean;
    }
  | { kind: 'proofComplete' };

export type LevelDefinition = {
  /** Human-readable level title, e.g. "Archimedean Property". */
  name: string;
  /** Lean identifier for codegen. Used as the declaration name in
   *  `theorem <theoremName> <theoremStatement> := by ...`.
   *  Example: "Lecture3_1" or "ArchProp". */
  theoremName: string;
  /** The Lean declaration signature: binders + `: returnType`.
   *  Does NOT include the theorem keyword, name, or `:= by`.
   *  Example: "{ε : ℝ} (hε : 0 < ε) : ∃ (N : ℕ), 1 / ε < N" */
  theoremStatement: string;
  /** Label shown on the lemma block. If absent, defaults to
   *  "theorem <theoremName>".
   *  Example: "Example", or "theorem ArchProp". */
  theoremBlockLabel?: string;
  /** Non-Prop binders for structured display. Example: "{ε : ℝ}" */
  objects?: string;
  /** Prop binders for structured display. Example: "(hε : 0 < ε)" */
  assumptions?: string;
  /** Target type for structured display.
   *  Example: "∃ (N : ℕ), 1 / ε < N" */
  goal?: string;
  permissions?: LevelPermission[];
  /** Markdown introduction shown before the level. */
  introduction?: string;
  /** Markdown conclusion shown after completing the level. */
  conclusion?: string;
  tutorial?: TutorialStep[];
};

/** Extract the list of allowed block types from permissions, or undefined if unrestricted. */
export function getAllowedBlocks(permissions?: LevelPermission[]): string[] | undefined {
  if (!permissions) return undefined;
  return permissions
    .filter((p): p is Extract<LevelPermission, { t: 'allowTactic' }> => p.t === 'allowTactic')
    .map(p => p.tacticName);
}

/** Extract the set of allowed affordances from permissions, or undefined if unrestricted. */
export function getAllowedAffordances(permissions?: LevelPermission[]): Set<string> | undefined {
  if (!permissions) return undefined;
  const affordances = new Set<string>();
  for (const p of permissions) {
    if (p.t === 'allowAllAffordances') return undefined;
    if (p.t === 'allowAffordance') affordances.add(p.affordance);
  }
  return affordances;
}

export type World = {
  id: string;
  name: string;
  description?: string;
  levels: LevelDefinition[];
  dependsOn: string[];
};

export type GameData = {
  worlds: World[];
};

export type NavigationState =
  | { kind: 'worldOverview' }
  | { kind: 'playing'; worldId: string; levelIndex: number };

// ── Blockly state helper ────────────────────────────────────────────

/** Build a BlocklyState from a level's abstract theorem data. Called at
 * the point of consumption (workspace init / reset), not at data load time. */
export function makeLevelState(level: LevelDefinition): BlocklyState {
  return {
    blocks: {
      languageVersion: 0,
      blocks: [{
        type: 'lemma',
        id: `lemma-${level.theoremName}`,
        x: 61, y: 61,
        fields: {
          THEOREM_BLOCK_LABEL: level.theoremBlockLabel ?? `theorem ${level.theoremName}`,
          THEOREM_NAME: level.theoremName,
          THEOREM_DECLARATION: level.theoremStatement,
        },
      }],
    },
  };
}

/** Render the decomposed-signature sections with the label on its own
 * line and the content indented below it:
 *
 *     Objects:
 *       (x : ℝ)
 *     Assumptions:
 *       (h : x = x)
 *     Goal:
 *       x^2 - 1 = …
 *
 * Returns undefined if the level supplied none of the three sections.
 */
export function formatDisplay(level: LevelDefinition): string | undefined {
  if (!level.objects && !level.assumptions && !level.goal) return undefined;
  const lines: string[] = [];
  if (level.objects)     lines.push('Objects:',     `  ${level.objects}`);
  if (level.assumptions) lines.push('Assumptions:', `  ${level.assumptions}`);
  if (level.goal)        lines.push('Goal:',        `  ${level.goal}`);
  return lines.join('\n');
}

// ── Load levels from JSON emitted by MakeGame ─────────────────────
//
// Vite's `import.meta.glob` with `eager: true` resolves at build time
// into a synchronous map of path → module.

const jsonLevelModules = import.meta.glob<LevelDefinition & { index?: number }>(
  '../../RealAnalysisGame/.lake/gamedata/level__*__*.json',
  { eager: true },
);

// Tutorial files export { worldId, levelIndex, default: TutorialStep[] }.
const tutorialModules = import.meta.glob<{
  default: TutorialStep[];
  worldId: string;
  levelIndex: number;
}>(
  './levels/*/*_tutorial.ts',
  { eager: true },
);

// Build tutorial lookup keyed by "worldId/levelIndex".
const tutorialLookup: Record<string, TutorialStep[]> = {};
for (const [, mod] of Object.entries(tutorialModules)) {
  if (mod.default && mod.worldId != null && mod.levelIndex != null)
    tutorialLookup[`${mod.worldId}/${mod.levelIndex}`] = mod.default;
}

// Group JSON levels by world, sorted by index.
const levelsByWorld: Record<string, LevelDefinition[]> = {};
for (const [path, data] of Object.entries(jsonLevelModules)) {
  const match = path.match(/level__([^_]+)__(\d+)\.json$/);
  if (!match || !data) continue;
  const worldId = match[1];
  const levelIdx = parseInt(match[2], 10);
  if (!levelsByWorld[worldId])
    levelsByWorld[worldId] = [];
  (levelsByWorld[worldId] as (LevelDefinition & { _sortIdx: number })[])
    .push({ ...data, _sortIdx: levelIdx } as LevelDefinition & { _sortIdx: number });
}
for (const worldId of Object.keys(levelsByWorld)) {
  const tagged = levelsByWorld[worldId] as (LevelDefinition & { _sortIdx: number })[];
  tagged.sort((a, b) => a._sortIdx - b._sortIdx);
  levelsByWorld[worldId] = tagged.map(({ _sortIdx: _, ...rest }) => {
    return rest;
  });
  // Attach tutorials by index.
  for (let i = 0; i < levelsByWorld[worldId].length; i++) {
    const tut = tutorialLookup[`${worldId}/${i}`];
    if (tut) levelsByWorld[worldId][i].tutorial = tut;
  }
}

function levelsFor(worldId: string): LevelDefinition[] {
  return levelsByWorld[worldId] ?? [];
}

// ── World list ─────────────────────────────────────────────────────

export const gameData: GameData = {
  worlds: [
    { id: 'RealAnalysisStory', name: 'Tutorial World', levels: levelsFor('RealAnalysisStory'), dependsOn: [] },
    { id: 'L1Pset', name: 'Pset 1', levels: levelsFor('L1Pset'), dependsOn: ['RealAnalysisStory'] },
    { id: 'NewtonsCalculationOfPi', name: "Newton's Computation of π", levels: levelsFor('NewtonsCalculationOfPi'), dependsOn: ['RealAnalysisStory'] },
  ],
};

// ── Navigation helpers (unchanged) ──────────────────────────────────

export function parseHash(hash: string): NavigationState {
  const match = hash.match(/^#([^/]+)\/(\d+)$/);
  if (match) {
    const worldId = match[1];
    const levelIndex = parseInt(match[2], 10);
    const world = gameData.worlds.find(w => w.id === worldId);
    if (world && levelIndex >= 0 && levelIndex < world.levels.length) {
      return { kind: 'playing', worldId, levelIndex };
    }
  }
  return { kind: 'worldOverview' };
}

export function navToHash(nav: NavigationState): string {
  if (nav.kind === 'playing') return `#${nav.worldId}/${nav.levelIndex}`;
  return '#';
}

/** Topological sort of worlds into rows for DAG layout. */
export function getWorldRows(worlds: World[]): World[][] {
  const worldMap = new Map(worlds.map(w => [w.id, w]));
  const depths = new Map<string, number>();

  function getDepth(id: string): number {
    if (depths.has(id)) return depths.get(id)!;
    const world = worldMap.get(id);
    if (!world || world.dependsOn.length === 0) {
      depths.set(id, 0);
      return 0;
    }
    const maxParent = Math.max(...world.dependsOn.map(getDepth));
    const depth = maxParent + 1;
    depths.set(id, depth);
    return depth;
  }

  worlds.forEach(w => getDepth(w.id));

  const maxDepth = Math.max(...Array.from(depths.values()), 0);
  const rows: World[][] = Array.from({ length: maxDepth + 1 }, () => []);
  worlds.forEach(w => rows[depths.get(w.id)!].push(w));
  return rows;
}
