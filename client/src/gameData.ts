import type { BlocklyState } from './Blockly.tsx';
import { example as example1 } from './examples/example-1.ts';
import { example as example2 } from './examples/example-2.ts';
import { example as example3 } from './examples/example-3.ts';
import { example as example4 } from './examples/example-4.ts';

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

export const gameData: GameData = {
  worlds: [
    {
      id: 'basics',
      name: 'Basics',
      description: 'Learn to use hypotheses and reflexivity',
      levels: [
        { name: 'Use Hypothesis', initial: example1, allowedBlocks: ['tactic_apply', 'prop'] },
        { name: 'Reflexivity', initial: example2, allowedBlocks: ['tactic_refl'] },
      ],
      dependsOn: [],
    },
    {
      id: 'rewriting',
      name: 'Rewriting',
      description: 'Learn to rewrite using equalities',
      levels: [
        { name: 'Rewrite', initial: example3, allowedBlocks: ['tactic_rw', 'prop'] },
      ],
      dependsOn: ['basics'],
    },
    {
      id: 'advanced',
      name: 'Advanced',
      description: 'Tackle more challenging proofs',
      levels: [
        { name: 'Limit Example', initial: example4 },
      ],
      dependsOn: ['basics', 'rewriting'],
    },
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
