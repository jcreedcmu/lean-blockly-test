import * as React from 'react';
import { useState } from 'react';
import type { InteractiveGoal, InteractiveGoals, InteractiveHypothesisBundle, SubexprInfo } from '@leanprover/infoview-api';
import { Goal, GoalFilterState, defaultGoalFilter } from './Goal';

export interface GoalsProps {
  goals: InteractiveGoals;
  filter?: GoalFilterState;
  onHypNameClick?: (name: string, hyp: InteractiveHypothesisBundle) => void;
  onSubexprClick?: (info: SubexprInfo) => void;
}

/**
 * Renders a list of goals with tab selection when there are multiple goals.
 */
export function Goals({
  goals,
  filter = defaultGoalFilter,
  onHypNameClick,
  onSubexprClick,
}: GoalsProps): React.ReactElement {
  const [selectedGoal, setSelectedGoal] = useState(0);

  if (!goals || goals.goals.length === 0) {
    return (
      <div className="goals goals-empty">
        <span className="goals-message">No goals</span>
      </div>
    );
  }

  const goalCount = goals.goals.length;
  const currentGoal = goals.goals[Math.min(selectedGoal, goalCount - 1)];

  return (
    <div className="goals">
      {goalCount > 1 && (
        <div className="goals-tabs">
          {goals.goals.map((_, i) => (
            <button
              key={i}
              className={`goals-tab ${i === selectedGoal ? 'active' : ''}`}
              onClick={() => setSelectedGoal(i)}
            >
              {i === 0 ? 'Main Goal' : `Goal ${i + 1}`}
            </button>
          ))}
        </div>
      )}

      <div className="goals-content">
        <Goal
          goal={currentGoal}
          filter={filter}
          onHypNameClick={onHypNameClick}
          onSubexprClick={onSubexprClick}
        />
      </div>

      {goalCount > 1 && (
        <div className="goals-count">
          {goalCount} goal{goalCount !== 1 ? 's' : ''}
        </div>
      )}
    </div>
  );
}
