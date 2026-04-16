import * as React from 'react';
import type { InteractiveHypothesisBundle, SubexprInfo } from '@leanprover/infoview-api';
import { InteractiveHypothesisBundle_nonAnonymousNames } from '@leanprover/infoview-api';
import { InteractiveCode } from './InteractiveCode';

/** Hypothesis-level drag modes recognized by Blockly's `startHypDrag`.
 * `'prop'` creates a bare `prop` block; the rest wrap the prop in the
 * corresponding tactic block. Also the affordance names reported by
 * the Lean-side `getGoalInfo` RPC. */
export type HypDragMode = 'prop' | 'apply' | 'rewrite' | 'choose';

/** Affordance modes that appear as labeled buttons next to a hyp. Must
 * match the affordance strings the Lean RPC reports. The order here is
 * the left-to-right rendering order in the infoview. */
export const HYP_AFFORDANCES = ['apply', 'rewrite', 'choose'] as const;

/** Props that control hypothesis interaction, shared across Hyp/Goal/Goals. */
export interface HypInteractionProps {
  /** Which drag affordances are allowed on this level (e.g. 'apply', 'rewrite'). undefined = all. */
  allowedAffordances?: Set<string>;
  onHypNameClick?: (name: string, hyp: InteractiveHypothesisBundle) => void;
  onHypDragStart?: (name: string, e: React.MouseEvent, mode?: HypDragMode) => void;
  onGoalDragStart?: (e: React.MouseEvent) => void;
  onSubexprClick?: (info: SubexprInfo) => void;
}

export interface HypProps extends HypInteractionProps {
  hyp: InteractiveHypothesisBundle;
  /** Potentially-available affordances for this hyp, as reported by
   * the server. The client intersects with `allowedAffordances`. */
  affordances?: Set<string>;
}

/** Returns true if the name contains the inaccessible marker. */
function isInaccessibleName(name: string): boolean {
  return name.includes('\u271D'); // dagger symbol
}

/**
 * Renders a single hypothesis bundle.
 * A bundle can have multiple names sharing the same type (e.g., "x y z : Nat").
 */
export function Hyp({ hyp, affordances, allowedAffordances, onHypNameClick, onHypDragStart, onSubexprClick }: HypProps): React.ReactElement {
  const names = InteractiveHypothesisBundle_nonAnonymousNames(hyp);

  const nameElements = names.map((name, i) => {
    const isInaccessible = isInaccessibleName(name);
    const className =
      'hyp-name' +
      (hyp.isInserted ? ' inserted' : '') +
      (hyp.isRemoved ? ' removed' : '') +
      (isInaccessible ? ' inaccessible' : '');

    return (
      <span
        key={i}
        className={className}
        onClick={onHypNameClick ? () => onHypNameClick(name, hyp) : undefined}
        onMouseDown={onHypDragStart ? (e) => onHypDragStart(name, e) : undefined}
        style={{ cursor: onHypDragStart ? 'grab' : onHypNameClick ? 'pointer' : undefined }}
      >
        {name}
        {i < names.length - 1 ? ' ' : ''}
      </span>
    );
  });

  const name = names[0];

  return (
    <div className="hyp">
      <span className="hyp-cell hyp-names">{nameElements}</span>
      <span className="hyp-cell hyp-colon">:</span>
      <span className="hyp-cell hyp-type-cell">
        <span className="hyp-type">
          <InteractiveCode fmt={hyp.type} onSubexprClick={onSubexprClick} />
        </span>
        {hyp.val && (
          <>
            <span className="hyp-assign"> := </span>
            <span className="hyp-val">
              <InteractiveCode fmt={hyp.val} onSubexprClick={onSubexprClick} />
            </span>
          </>
        )}
      </span>
      {onHypDragStart && affordances && HYP_AFFORDANCES.map((a) =>
        affordances.has(a) && (!allowedAffordances || allowedAffordances.has(a)) ? (
          <span
            key={a}
            className={`hyp-cell hyp-action hyp-action-${a}`}
            onMouseDown={(e) => onHypDragStart(name, e, a)}
          >
            {a}
          </span>
        ) : null
      )}
    </div>
  );
}
