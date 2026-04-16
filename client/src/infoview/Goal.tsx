import * as React from 'react';
import type { CodeWithInfos, InteractiveGoal, InteractiveHypothesisBundle } from '@leanprover/infoview-api';
import { Hyp, type HypClass, type HypInteractionProps } from './Hyp';
import { InteractiveCode } from './InteractiveCode';
import type { HypKindMap } from '../LevelEvaluator';

/** Flatten a TaggedText to its plain string form. */
function taggedTextToString(tt: CodeWithInfos): string {
  if ('text' in tt) return tt.text;
  if ('append' in tt) return tt.append.map(taggedTextToString).join('');
  if ('tag' in tt) return taggedTextToString(tt.tag[1]);
  return '';
}

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
  hypKindMap?: HypKindMap;
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

/** Check if a hypothesis bundle is an assumption (Prop-typed) using the hypKindMap. */
function isAssumption(h: InteractiveHypothesisBundle, hypKindMap?: HypKindMap): boolean | undefined {
  if (!hypKindMap || !h.fvarIds || h.fvarIds.length === 0) return undefined;
  // A bundle may have multiple fvarIds (e.g. "x y z : Nat"), check the first
  return hypKindMap.get(h.fvarIds[0]);
}

function renderHypGroup(
  title: string,
  hyps: InteractiveHypothesisBundle[],
  props: HypInteractionProps,
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
  hypKindMap,
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

  // Split into objects vs assumptions if we have hypKindMap data
  const hasKindData = hypKindMap && hypKindMap.size > 0;
  const objectHyps = hasKindData ? hyps.filter(h => isAssumption(h, hypKindMap) !== true) : hyps;
  const assumptionHyps = hasKindData ? hyps.filter(h => isAssumption(h, hypKindMap) === true) : [];

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
          {renderHypGroup('Objects', objectHyps, interactionProps, undefined)}
          {renderHypGroup('Assumptions', assumptionHyps, interactionProps, 'equational')}
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
        {interactionProps.onGoalDragStart &&
          taggedTextToString(goal.type).trimStart().startsWith('\u2203') &&
          (!interactionProps.allowedAffordances || interactionProps.allowedAffordances.has('use')) && (
            <span
              className="goal-action goal-action-use"
              onMouseDown={(e) => interactionProps.onGoalDragStart!(e)}
            >
              use
            </span>
          )}
      </div>
    </div>
  );
}
