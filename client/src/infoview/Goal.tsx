import * as React from 'react';
import type { InteractiveGoal, InteractiveHypothesisBundle } from '@leanprover/infoview-api';
import { Hyp, type HypInteractionProps } from './Hyp';
import { InteractiveCode } from './InteractiveCode';
import type { Affordance, GoalInfo } from '../LevelEvaluator';

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

export interface GoalProps extends HypInteractionProps {
  goal: InteractiveGoal;
  /** Server-extracted info about this specific goal. Absent when the
   * `getGoalInfo` RPC hasn't populated yet or failed for this mvarId. */
  goalInfo?: GoalInfo;
  filter?: GoalFilterState;
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

/** Check if a hypothesis bundle is an assumption (Prop-typed) using the goalInfo.hyps map. */
function isAssumption(h: InteractiveHypothesisBundle, goalInfo?: GoalInfo): boolean | undefined {
  if (!goalInfo || !h.fvarIds || h.fvarIds.length === 0) return undefined;
  // A bundle may have multiple fvarIds (e.g. "x y z : Nat"), check the first
  return goalInfo.hyps.get(h.fvarIds[0])?.isAssumption;
}

/** Look up the server-reported affordance list for a bundle's first fvarId. */
function hypAffordances(
  h: InteractiveHypothesisBundle,
  goalInfo?: GoalInfo,
): Affordance[] | undefined {
  if (!goalInfo || !h.fvarIds || h.fvarIds.length === 0) return undefined;
  return goalInfo.hyps.get(h.fvarIds[0])?.affordances;
}

function renderHypGroup(
  title: string,
  hyps: InteractiveHypothesisBundle[],
  props: HypInteractionProps,
  goalInfo: GoalInfo | undefined,
): React.ReactElement | null {
  if (hyps.length === 0) return null;
  return (
    <div className="hyp-group">
      <div className="hyp-group-title">{title}</div>
      <div className="goal-hyps">
        {hyps.map((h, i) => (
          <Hyp
            key={i}
            hyp={h}
            affordances={hypAffordances(h, goalInfo)}
            {...props}
          />
        ))}
      </div>
    </div>
  );
}

/**
 * Renders a single goal with its hypotheses and target type.
 */
export function Goal({
  goal,
  goalInfo,
  filter = defaultGoalFilter,
  ...interactionProps
}: GoalProps): React.ReactElement {
  if (!goal) {
    return <></>;
  }

  const filteredHyps = filterHypotheses(goal.hyps, filter);
  // Split multi-name bundles so each hypothesis gets its own row
  const splitHyps = filteredHyps.flatMap((h) =>
    h.names.map((name, nameIdx) => ({
      ...h,
      names: [name],
      // Preserve the correct fvarId for this specific name
      fvarIds: h.fvarIds ? [h.fvarIds[nameIdx]] : undefined,
    }))
  );
  const hyps = filter.reverse ? [...splitHyps].reverse() : splitHyps;

  // Split into objects vs assumptions if we have goalInfo for this goal
  const hasKindData = !!goalInfo && goalInfo.hyps.size > 0;
  const objectHyps = hasKindData ? hyps.filter(h => isAssumption(h, goalInfo) !== true) : hyps;
  const assumptionHyps = hasKindData ? hyps.filter(h => isAssumption(h, goalInfo) === true) : [];

  return (
    <div className="goal">
      {goal.userName && (
        <div className="goal-case">
          <span className="goal-case-label">case </span>
          <span className="goal-case-name">{goal.userName}</span>
        </div>
      )}

      {hasKindData ? (
        <>
          {renderHypGroup('Objects', objectHyps, interactionProps, goalInfo)}
          {renderHypGroup('Assumptions', assumptionHyps, interactionProps, goalInfo)}
        </>
      ) : (
        hyps.length > 0 && (
          <div className="goal-hyps">
            {hyps.map((h, i) => (
              <Hyp
                key={i}
                hyp={h}
                {...interactionProps}
              />
            ))}
          </div>
        )
      )}

      <div className="goal-target">
        <span className="goal-vdash">{goal.goalPrefix ?? '\u22A2'} </span>
        <span className="goal-type">
          <InteractiveCode fmt={goal.type} onSubexprClick={interactionProps.onSubexprClick} />
        </span>
        {interactionProps.onGoalDragStart && goalInfo?.target.affordances.map((a) => {
          if (a.kind !== 'use') return null;
          if (interactionProps.allowedAffordances &&
              !interactionProps.allowedAffordances.has(a.kind)) return null;
          return (
            <span
              key={a.kind}
              className={`goal-action goal-action-${a.kind}`}
              onMouseDown={(e) => interactionProps.onGoalDragStart!(e, a)}
            >
              {a.kind}
            </span>
          );
        })}
      </div>
    </div>
  );
}
