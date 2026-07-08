import * as React from 'react';
import type { InteractiveGoals } from '@leanprover/infoview-api';
import { Goal, GoalFilterState, defaultGoalFilter } from './Goal';
import type { HypInteractionProps } from './Hyp';
import type { GoalInfo, GoalInfoMap } from '../LevelEvaluator';

export interface GoalsProps extends HypInteractionProps {
  /** The unsolved-goal leaves shown as the "Main Goal"/"Goal N" tabs. */
  goals: InteractiveGoals | null;
  /** The active tab index, or null when an `overrideGoal` is being shown
   * (a selected pill that doesn't correspond to any unsolved-goal leaf). */
  selectedGoal: number | null;
  /** Select a tab (and, via App, the corresponding pill). */
  onSelectGoal: (index: number) => void;
  /** Goal to display when no tab is active (a pill with no leaf). */
  overrideGoal?: InteractiveGoals | null;
  /** Hyp kinds/affordances for `overrideGoal`, fetched with it. Leaf goals
   * read from `goalInfoMap` instead; the override goal isn't in that map. */
  overrideGoalInfo?: GoalInfo;
  /** When true, the displayed goal is stale (a position query is in flight) —
   * render it dimmed rather than blanking the panel. */
  pending?: boolean;
  /** Conv `enter` targets for the displayed goal. Defined (even if empty) ⇒
   * the goal is conv-mode: render it as the draggable subexpression view. */
  convGoalTargets?: Map<string, string[]>;
  goalInfoMap?: GoalInfoMap;
  filter?: GoalFilterState;
}

/**
 * Controlled goal view. The "Main Goal"/"Goal N" tabs come from `goals` and the
 * active one is `selectedGoal`; when `selectedGoal` is null the `overrideGoal`
 * is shown with no tab active (the inspect-a-non-leaf-position case).
 */
export function Goals({
  goals,
  selectedGoal,
  onSelectGoal,
  overrideGoal,
  overrideGoalInfo,
  pending = false,
  convGoalTargets,
  goalInfoMap,
  filter = defaultGoalFilter,
  ...interactionProps
}: GoalsProps): React.ReactElement {
  const tabGoals = goals?.goals ?? [];
  const showingOverride = selectedGoal === null;
  const displayed = showingOverride
    ? overrideGoal?.goals?.[0] ?? null
    : tabGoals[Math.min(selectedGoal, tabGoals.length - 1)];

  if (!displayed) {
    return (
      <div className="goals goals-empty">
        <span className="goals-message">No goals</span>
      </div>
    );
  }

  return (
    <div className="goals">
      {tabGoals.length > 1 && (
        <div className="goals-tabs">
          {tabGoals.map((_, i) => (
            <button
              key={i}
              className={`goals-tab ${i === selectedGoal ? 'active' : ''}`}
              onClick={() => onSelectGoal(i)}
            >
              {i === 0 ? 'Main Goal' : `Goal ${i + 1}`}
            </button>
          ))}
        </div>
      )}

      <div className={`goals-content${pending ? ' pending' : ''}`}>
        <Goal
          goal={displayed}
          goalInfo={showingOverride
            ? overrideGoalInfo
            : (displayed.mvarId ? goalInfoMap?.get(displayed.mvarId) : undefined)}
          convGoalTargets={convGoalTargets}
          filter={filter}
          {...interactionProps}
        />
      </div>

      {tabGoals.length > 1 && (
        <div className="goals-count">
          {tabGoals.length} goal{tabGoals.length !== 1 ? 's' : ''}
        </div>
      )}
    </div>
  );
}
