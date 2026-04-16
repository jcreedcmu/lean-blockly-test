/**
 * Onboarding tutorial — a thin wrapper around react-joyride.
 *
 * The component is "controlled": the parent passes `run` and `onDone`.
 * Auto-start on first visit and the "start tutorial" button both go
 * through the same path.
 */
import { Joyride, STATUS } from 'react-joyride';

const STORAGE_KEY = 'tutorialDone';

const STEPS = [
  {
    target: '.tutorial-workspace-anchor',
    spotlightTarget: '.blocklySvg',
    content: <span><b>Welcome to Lean Blocks!</b><br /><br />This is the proof workspace. Snap tactic blocks together inside the theorem block to build your proof step by step.</span>,
    skipBeacon: true,
    placement: 'bottom',
  },
  {
    target: '.blocklyToolbox',
    content: 'This is the tactic palette. Click a category to see available tactics, then drag one into the workspace.',
    skipBeacon: true,
    placement: 'right',
  },
  {
    target: '.goals-panel',
    content: 'Your current proof state appears here: objects, assumptions, and the goal you need to prove.',
    skipBeacon: true,
    placement: 'left',
  },
  {
    target: '.proof-status',
    content: 'This indicator turns green when your proof is complete.',
    skipBeacon: true,
    placement: 'left',
  },
];

/** Returns true if the user has already completed/skipped the tutorial. */
export function isTutorialDone(): boolean {
  return !!localStorage.getItem(STORAGE_KEY);
}

export interface TutorialProps {
  run: boolean;
  onDone: () => void;
}

export function Tutorial({ run, onDone }: TutorialProps) {
  return (
    <Joyride
      steps={STEPS as any}
      run={run}
      continuous
      onEvent={(data: any) => {
        if (data.status === STATUS.FINISHED || data.status === STATUS.SKIPPED) {
          localStorage.setItem(STORAGE_KEY, '1');
          onDone();
        }
      }}
    />
  );
}
