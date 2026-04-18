import { useCallback, useEffect, useState } from 'react';
import type { BlocklyState } from './Blockly';
import type { NavigationState, TutorialStep } from './gameData';
import { gameData } from './gameData';
import { isTutorialDone, type TutorialProps } from './Tutorial';
import { tutorialConditionMet } from './tutorialConditions';

function tutorialStorageKey(worldId: string, levelIndex: number): string {
  return `tutorialDone:${worldId}:${levelIndex}`;
}

export function useLevelTutorial(
  nav: NavigationState,
  proofComplete: boolean | null,
) {
  const [run, setRun] = useState(false);
  const [workspaceState, setWorkspaceState] = useState<BlocklyState | null>(null);

  // Resolve the current level's tutorial steps (if any).
  const currentLevel = nav.kind === 'playing'
    ? gameData.worlds.find(w => w.id === nav.worldId)?.levels[nav.levelIndex]
    : undefined;
  const steps = currentLevel?.tutorial ?? [];
  const storageKey = nav.kind === 'playing'
    ? tutorialStorageKey(nav.worldId, nav.levelIndex)
    : '';

  // Sync workspace state when navigation changes.
  useEffect(() => {
    if (nav.kind !== 'playing') {
      setWorkspaceState(null);
    }
  }, [nav]);

  // Auto-start tutorial on first visit to a level that has one.
  useEffect(() => {
    if (nav.kind !== 'playing') return;
    if (!steps.length) {
      setRun(false);
      return;
    }
    if (isTutorialDone(storageKey)) return;
    setRun(true);
  }, [nav, steps.length, storageKey]);

  const isStepComplete = useCallback((step: TutorialStep) => {
    if (!step.conditions?.length) return false;
    return step.conditions.every(cond =>
      tutorialConditionMet(cond, workspaceState, proofComplete === true),
    );
  }, [proofComplete, workspaceState]);

  const tutorialProps: Omit<TutorialProps, 'onStepActive'> = {
    run,
    steps,
    storageKey,
    isStepComplete,
    onDone: () => setRun(false),
  };

  return {
    run,
    start: () => setRun(true),
    stop: () => setRun(false),
    updateWorkspace: (s: BlocklyState) => setWorkspaceState(s),
    resetWorkspace: (s: BlocklyState) => setWorkspaceState(s),
    tutorialProps,
    hasSteps: steps.length > 0,
    storageKey,
  };
}
