import * as React from 'react';
import type { InteractiveGoal, InteractiveHypothesisBundle, SubexprInfo } from '@leanprover/infoview-api';
import { Hyp, type HypClass } from './Hyp';
import { InteractiveCode } from './InteractiveCode';
import type { HypKindMap } from '../LevelEvaluator';

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
  hypKindMap?: HypKindMap;
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

/** Check if a hypothesis bundle is an assumption (Prop-typed) using the hypKindMap. */
function isAssumption(h: InteractiveHypothesisBundle, hypKindMap?: HypKindMap): boolean | undefined {
  if (!hypKindMap || !h.fvarIds || h.fvarIds.length === 0) return undefined;
  // A bundle may have multiple fvarIds (e.g. "x y z : Nat"), check the first
  return hypKindMap.get(h.fvarIds[0]);
}

function renderHypGroup(
  title: string,
  hyps: InteractiveHypothesisBundle[],
  props: Pick<GoalProps, 'onHypNameClick' | 'onHypDragStart' | 'onSubexprClick'>,
  affordances: HypClass,
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
            affordances={affordances}
            onNameClick={props.onHypNameClick}
            onHypDragStart={props.onHypDragStart}
            onSubexprClick={props.onSubexprClick}
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
  hypKindMap,
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
    h.names.map((name, nameIdx) => ({
      ...h,
      names: [name],
      // Preserve the correct fvarId for this specific name
      fvarIds: h.fvarIds ? [h.fvarIds[nameIdx]] : undefined,
    }))
  );
  const hyps = filter.reverse ? [...splitHyps].reverse() : splitHyps;

  // Split into objects vs assumptions if we have hypKindMap data
  const hasKindData = hypKindMap && hypKindMap.size > 0;
  const objectHyps = hasKindData ? hyps.filter(h => isAssumption(h, hypKindMap) !== true) : hyps;
  const assumptionHyps = hasKindData ? hyps.filter(h => isAssumption(h, hypKindMap) === true) : [];

  const handlerProps = { onHypNameClick, onHypDragStart, onSubexprClick };

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
          {renderHypGroup('Objects', objectHyps, handlerProps, undefined)}
          {renderHypGroup('Assumptions', assumptionHyps, handlerProps, 'equational')}
        </>
      ) : (
        hyps.length > 0 && (
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
        )
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
