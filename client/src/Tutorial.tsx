/**
 * Onboarding tutorial — a thin wrapper around react-joyride.
 *
 * The component is "controlled": the parent passes `run` and `onDone`.
 * Auto-start on first visit and the "start tutorial" button both go
 * through the same path.
 */
import { useCallback, useEffect, useState } from 'react';
import { ACTIONS, EVENTS, Joyride, STATUS } from 'react-joyride';
import ReactMarkdown from 'react-markdown';
import rehypeKatex from 'rehype-katex';
import remarkGfm from 'remark-gfm';
import remarkMath from 'remark-math';
import 'katex/dist/katex.min.css';
import type { TutorialStepSource } from './gameData';

/** Returns true if the user has already completed/skipped this tutorial. */
export function isTutorialDone(storageKey: string): boolean {
  return !!localStorage.getItem(storageKey);
}

export interface TutorialProps {
  run: boolean;
  steps: TutorialStepSource[];
  storageKey: string;
  isStepComplete?: (step: TutorialStepSource) => boolean;
  onStepActive?: (step: TutorialStepSource) => void;
  onDone: () => void;
}

function TutorialContent({ markdown }: { markdown: string }) {
  return (
    <div className="tutorial-markdown">
      <ReactMarkdown
        remarkPlugins={[remarkGfm, remarkMath]}
        rehypePlugins={[rehypeKatex]}
      >
        {markdown}
      </ReactMarkdown>
    </div>
  );
}

export function Tutorial({
  run,
  steps,
  storageKey,
  isStepComplete,
  onStepActive,
  onDone,
}: TutorialProps) {
  const [stepIndex, setStepIndex] = useState(0);

  const finishTutorial = useCallback(() => {
    localStorage.setItem(storageKey, '1');
    setStepIndex(0);
    onDone();
  }, [onDone, storageKey]);

  useEffect(() => {
    if (run) setStepIndex(0);
  }, [run, storageKey]);

  useEffect(() => {
    if (!run) return;
    const step = steps[stepIndex];
    if (!step) return;
    onStepActive?.(step);

    if (!step.openToolboxCategory) return;
    const interval = window.setInterval(() => onStepActive?.(step), 250);
    return () => window.clearInterval(interval);
  }, [onStepActive, run, stepIndex, steps]);

  useEffect(() => {
    if (!run) return;
    const step = steps[stepIndex];
    if (!step?.advanceOn) return;

    let advanceTimer: number | undefined;
    let interval: number | undefined;

    function advance() {
      if (stepIndex >= steps.length - 1) {
        finishTutorial();
        return;
      }
      setStepIndex(currentIndex =>
        currentIndex === stepIndex ? currentIndex + 1 : currentIndex
      );
    }

    function checkStep() {
      if (!isStepComplete?.(step)) return;
      if (interval !== undefined) window.clearInterval(interval);
      if (advanceTimer !== undefined) return;
      advanceTimer = window.setTimeout(advance, step.advanceDelayMs ?? 650);
    }

    checkStep();
    interval = window.setInterval(checkStep, 150);

    return () => {
      if (interval !== undefined) window.clearInterval(interval);
      if (advanceTimer !== undefined) window.clearTimeout(advanceTimer);
    };
  }, [finishTutorial, isStepComplete, run, stepIndex, steps]);

  if (steps.length === 0) return null;

  return (
    <Joyride
      steps={steps.map(step => {
        const {
          advanceOn: _advanceOn,
          advanceDelayMs: _advanceDelayMs,
          openToolboxCategory: _openToolboxCategory,
          content,
          ...joyrideStep
        } = step;
        return {
          closeButtonAction: 'skip' as const,
          skipBeacon: true,
          overlayClickAction: false as const,
          content: <TutorialContent markdown={content} />,
          ...(step.advanceOn ? { buttons: ['back', 'close'] as const } : {}),
          ...joyrideStep,
        };
      }) as any}
      run={run}
      continuous
      stepIndex={stepIndex}
      locale={{ last: 'Close' }}
      onEvent={(data: any) => {
        if (data.status === STATUS.FINISHED || data.status === STATUS.SKIPPED) {
          finishTutorial();
          return;
        }

        if (data.type !== EVENTS.STEP_AFTER) return;

        if (data.action === ACTIONS.PREV) {
          setStepIndex(Math.max(data.index - 1, 0));
          return;
        }

        if (data.action !== ACTIONS.NEXT) return;

        const step = steps[data.index];
        if (step?.advanceOn && !isStepComplete?.(step)) return;

        const nextIndex = data.index + 1;
        if (nextIndex >= steps.length) {
          finishTutorial();
          return;
        }
        setStepIndex(nextIndex);
      }}
    />
  );
}
