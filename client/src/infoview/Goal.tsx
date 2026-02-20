import * as React from 'react';
import type { InteractiveGoal, InteractiveHypothesisBundle, SubexprInfo } from '@leanprover/infoview-api';
import { Hyp } from './Hyp';
import { InteractiveCode } from './InteractiveCode';

export interface GoalFilterState {
  /** If true, reverse the order of hypotheses. */
  reverse: boolean;
  /** If true, show hypotheses that have isType=true. */
  showType: boolean;
  /** If true, show hypotheses that have isInstance=true. */
  showInstance: boolean;
  /** If true, show hypotheses with inaccessible names (containing dagger). */
  showInaccessible: boolean;
  /** If true, show let-values. */
  showLetValue: boolean;
}

export const defaultGoalFilter: GoalFilterState = {
  reverse: false,
  showType: true,
  showInstance: true,
  showInaccessible: true,
  showLetValue: true,
};

export interface GoalProps {
  goal: InteractiveGoal;
  filter?: GoalFilterState;
  onHypNameClick?: (name: string, hyp: InteractiveHypothesisBundle) => void;
  onHypDragStart?: (name: string, e: React.MouseEvent, mode?: 'prop' | 'apply' | 'rewrite') => void;
  onSubexprClick?: (info: SubexprInfo) => void;
}

function isInaccessibleName(name: string): boolean {
  return name.includes('\u271D');
}

function filterHypotheses(
  hyps: InteractiveHypothesisBundle[],
  filter: GoalFilterState
): InteractiveHypothesisBundle[] {
  return hyps.reduce((acc: InteractiveHypothesisBundle[], h) => {
    if (h.isInstance && !filter.showInstance) return acc;
    if (h.isType && !filter.showType) return acc;

    const names = filter.showInaccessible
      ? h.names
      : h.names.filter((n) => !isInaccessibleName(n));

    if (names.length === 0) return acc;

    const filteredHyp: InteractiveHypothesisBundle = filter.showLetValue
      ? { ...h, names }
      : { ...h, names, val: undefined };

    acc.push(filteredHyp);
    return acc;
  }, []);
}

/**
 * Renders a single goal with its hypotheses and target type.
 */
export function Goal({
  goal,
  filter = defaultGoalFilter,
  onHypNameClick,
  onHypDragStart,
  onSubexprClick,
}: GoalProps): React.ReactElement {
  if (!goal) {
    return <></>;
  }

  const filteredHyps = filterHypotheses(goal.hyps, filter);
  // Split multi-name bundles so each hypothesis gets its own row
  const splitHyps = filteredHyps.flatMap((h) =>
    h.names.map((name) => ({ ...h, names: [name] }))
  );
  const hyps = filter.reverse ? [...splitHyps].reverse() : splitHyps;

  return (
    <div className="goal">
      {goal.userName && (
        <div className="goal-case">
          <span className="goal-case-label">case </span>
          <span className="goal-case-name">{goal.userName}</span>
        </div>
      )}

      {hyps.length > 0 && (
        <div className="goal-hyps">
          {hyps.map((h, i) => (
            <Hyp
              key={i}
              hyp={h}
              onNameClick={onHypNameClick}
              onHypDragStart={onHypDragStart}
              onSubexprClick={onSubexprClick}
            />
          ))}
        </div>
      )}

      <div className="goal-target">
        <span className="goal-vdash">{goal.goalPrefix ?? '\u22A2'} </span>
        <span className="goal-type">
          <InteractiveCode fmt={goal.type} onSubexprClick={onSubexprClick} />
        </span>
      </div>
    </div>
  );
}
