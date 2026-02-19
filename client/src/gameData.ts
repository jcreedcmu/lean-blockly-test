import type { BlocklyState } from './Blockly.tsx';

export type LevelDefinition = {
  name: string;
  initial: BlocklyState;
  allowedBlocks?: string[];
};

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

const emptyLevel: BlocklyState = {
  blocks: {
    languageVersion: 0,
    blocks: [
      {
        type: 'lemma',
        id: 'placeholder-lemma',
        x: 61,
        y: 61,
        fields: {
          THEOREM_NAME: 'placeholder',
          THEOREM_DECLARATION: ': True',
        },
      },
    ],
  },
};

function makeLevels(worldName: string, count: number): LevelDefinition[] {
  return Array.from({ length: count }, (_, i) => ({
    name: `${worldName} Level ${i + 1}`,
    initial: emptyLevel,
  }));
}

export const gameData: GameData = {
  worlds: [
    { id: 'RealAnalysisStory', name: 'The Story of Real Analysis', levels: makeLevels('RealAnalysisStory', 9), dependsOn: [] },
    { id: 'L1Pset', name: 'Pset 1', levels: makeLevels('L1Pset', 5), dependsOn: ['RealAnalysisStory'] },
    { id: 'NewtonsCalculationOfPi', name: "Newton's Computation of π", levels: makeLevels('NewtonsCalculationOfPi', 1), dependsOn: ['RealAnalysisStory'] },
    { id: 'L2Pset', name: 'Pset 2', levels: makeLevels('L2Pset', 2), dependsOn: ['NewtonsCalculationOfPi', 'L1Pset'] },
    { id: 'Lecture3', name: 'More fun with Sequences', levels: makeLevels('Lecture3', 2), dependsOn: ['NewtonsCalculationOfPi'] },
    { id: 'L3Pset', name: 'Pset 3', levels: makeLevels('L3Pset', 4), dependsOn: ['L2Pset'] },
    { id: 'Lecture4', name: 'Even more fun with Sequences', levels: makeLevels('Lecture4', 1), dependsOn: ['L2Pset', 'Lecture3'] },
    { id: 'L4Pset', name: 'Pset 4', levels: makeLevels('L4Pset', 1), dependsOn: ['L3Pset'] },
    { id: 'Lecture5', name: 'Algebraic Limit Theorem, Part I', levels: makeLevels('Lecture5', 1), dependsOn: ['Lecture4', 'L4Pset'] },
    { id: 'Lecture6', name: 'Algebraic Limit Theorem, Part II', levels: makeLevels('Lecture6', 7), dependsOn: ['Lecture5', 'L4Pset'] },
    { id: 'L6Pset', name: 'Pset 6', levels: makeLevels('L6Pset', 5), dependsOn: ['L4Pset'] },
    { id: 'Lecture7', name: 'Algebraic Limit Theorem, Part III', levels: makeLevels('Lecture7', 5), dependsOn: ['Lecture6'] },
    { id: 'L7Pset', name: 'Pset 7', levels: makeLevels('L7Pset', 3), dependsOn: ['L6Pset'] },
    { id: 'Lecture8', name: 'Induction', levels: makeLevels('Lecture8', 1), dependsOn: ['L6Pset', 'L7Pset'] },
    { id: 'L8Pset', name: 'Pset 8', levels: makeLevels('L8Pset', 4), dependsOn: ['L7Pset'] },
    { id: 'Lecture9', name: 'Algebraic Limit Theorem, Part IV', levels: makeLevels('Lecture9', 2), dependsOn: ['L8Pset'] },
    { id: 'L9Pset', name: 'Pset 9', levels: makeLevels('L9Pset', 3), dependsOn: ['L8Pset'] },
    { id: 'Lecture10', name: 'Algebraic Limit Theorem, Part V', levels: makeLevels('Lecture10', 4), dependsOn: ['L9Pset'] },
    { id: 'L10Pset', name: 'Pset 10', levels: makeLevels('L10Pset', 6), dependsOn: ['L9Pset'] },
    { id: 'Lecture11', name: 'The Real Numbers I', levels: makeLevels('Lecture11', 3), dependsOn: ['L9Pset', 'Lecture10', 'L10Pset'] },
    { id: 'L11Pset', name: 'Pset 11', levels: makeLevels('L11Pset', 1), dependsOn: ['Lecture11', 'L10Pset'] },
    { id: 'Lecture12', name: 'Cauchy Sequences II', levels: makeLevels('Lecture12', 4), dependsOn: ['Lecture11', 'L10Pset'] },
    { id: 'L12Pset', name: 'Pset 12', levels: makeLevels('L12Pset', 2), dependsOn: ['Lecture12', 'L11Pset'] },
    { id: 'Lecture13', name: 'Monotone Subsequence', levels: makeLevels('Lecture13', 1), dependsOn: ['L11Pset', 'Lecture12'] },
    { id: 'L13Pset', name: 'Pset 13', levels: makeLevels('L13Pset', 1), dependsOn: ['Lecture13', 'L12Pset'] },
    { id: 'Lecture14', name: 'Bolzano-Weierstrass', levels: makeLevels('Lecture14', 1), dependsOn: ['L12Pset', 'Lecture13'] },
    { id: 'Lecture15', name: 'The Real Numbers', levels: makeLevels('Lecture15', 1), dependsOn: ['Lecture14', 'L13Pset'] },
    { id: 'L15Pset', name: 'Pset 15', levels: makeLevels('L15Pset', 1), dependsOn: ['Lecture15', 'L13Pset'] },
    { id: 'Lecture16', name: 'Series', levels: makeLevels('Lecture16', 1), dependsOn: ['Lecture15'] },
    { id: 'L16Pset', name: 'Pset 16', levels: makeLevels('L16Pset', 3), dependsOn: ['Lecture16', 'L15Pset'] },
    { id: 'Lecture17', name: 'Series II', levels: makeLevels('Lecture17', 4), dependsOn: ['Lecture16', 'L15Pset', 'L16Pset'] },
    { id: 'L17Pset', name: 'Pset 17', levels: makeLevels('L17Pset', 3), dependsOn: ['Lecture17', 'L16Pset'] },
    { id: 'Lecture18', name: 'Infinite Addition', levels: makeLevels('Lecture18', 2), dependsOn: ['Lecture17', 'L16Pset'] },
    { id: 'L18Pset', name: 'Pset 18', levels: makeLevels('L18Pset', 10), dependsOn: ['Lecture18', 'L17Pset', 'L13Pset'] },
    { id: 'Lecture19', name: 'Rearrangements', levels: makeLevels('Lecture19', 4), dependsOn: ['L17Pset', 'L18Pset'] },
    { id: 'Lecture20', name: 'Function Limits', levels: makeLevels('Lecture20', 4), dependsOn: ['L18Pset', 'Lecture19'] },
    { id: 'L20Pset', name: 'Pset 20', levels: makeLevels('L20Pset', 4), dependsOn: ['Lecture20', 'L18Pset'] },
    { id: 'Lecture21', name: 'Function Limits II', levels: makeLevels('Lecture21', 4), dependsOn: ['Lecture20'] },
    { id: 'Lecture22', name: 'Uniformity', levels: makeLevels('Lecture22', 3), dependsOn: ['Lecture21', 'L20Pset'] },
    { id: 'L22Pset', name: 'Pset 22', levels: makeLevels('L22Pset', 4), dependsOn: ['Lecture22', 'L20Pset'] },
    { id: 'Lecture23', name: 'Uniformity II: Continuity', levels: makeLevels('Lecture23', 3), dependsOn: ['Lecture22'] },
    { id: 'Lecture24', name: 'Topology', levels: makeLevels('Lecture24', 5), dependsOn: ['Lecture23', 'L22Pset'] },
    { id: 'L24Pset', name: 'Pset 24', levels: makeLevels('L24Pset', 2), dependsOn: ['Lecture24'] },
    { id: 'Lecture25', name: 'Swapping Limits and Integrals', levels: makeLevels('Lecture25', 2), dependsOn: ['L24Pset', 'Lecture24'] },
  ],
};

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
