import * as React from 'react';
import type { InteractiveHypothesisBundle, SubexprInfo } from '@leanprover/infoview-api';
import { InteractiveHypothesisBundle_nonAnonymousNames } from '@leanprover/infoview-api';
import { InteractiveCode } from './InteractiveCode';
import type { Affordance } from '../LevelEvaluator';

/** Order in which hypothesis-level affordances are rendered (left-to-right).
 * Also gates which kinds are recognized as hyp-side buttons at all. */
export const HYP_AFFORDANCE_KINDS = ['apply', 'rewrite', 'choose'] as const;
type HypAffordanceKind = typeof HYP_AFFORDANCE_KINDS[number];

/** Props that control hypothesis interaction, shared across Hyp/Goal/Goals. */
export interface HypInteractionProps {
  /** Which drag affordances are allowed on this level (by `kind`). undefined = all. */
  allowedAffordances?: Set<string>;
  onHypNameClick?: (name: string, hyp: InteractiveHypothesisBundle) => void;
  /** Start dragging a new block built from this hyp. If `affordance` is
   * omitted, drags a bare `prop` block carrying the hyp name. */
  onHypDragStart?: (name: string, e: React.MouseEvent, affordance?: Affordance) => void;
  /** Start dragging a new block from the goal target's affordance. */
  onGoalDragStart?: (e: React.MouseEvent, affordance: Affordance) => void;
  onSubexprClick?: (info: SubexprInfo) => void;
}

export interface HypProps extends HypInteractionProps {
  hyp: InteractiveHypothesisBundle;
  /** Potentially-available affordances for this hyp, as reported by
   * the server. The client intersects with `allowedAffordances`. */
  affordances?: Affordance[];
}

/** Returns true if the name contains the inaccessible marker. */
function isInaccessibleName(name: string): boolean {
  return name.includes('\u271D'); // dagger symbol
}

function tutorialHypClass(name: string): string {
  return `tutorial-hyp-${name.replace(/[^a-zA-Z0-9_-]/g, '-')}`;
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
      ` ${tutorialHypClass(name)}` +
      (hyp.isInserted ? ' inserted' : '') +
      (hyp.isRemoved ? ' removed' : '') +
      (isInaccessible ? ' inaccessible' : '');

    return (
      <span
        key={i}
        className={className}
        data-hyp-name={name}
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
      {onHypDragStart && affordances && HYP_AFFORDANCE_KINDS.map((kind) => {
        const a = affordances.find((x): x is Affordance & { kind: HypAffordanceKind } =>
          x.kind === kind);
        if (!a) return null;
        if (allowedAffordances && !allowedAffordances.has(kind)) return null;
        return (
          <span
            key={kind}
            className={`hyp-cell hyp-action hyp-action-${kind}`}
            onMouseDown={(e) => onHypDragStart(name, e, a)}
          >
            {kind}
          </span>
        );
      })}
    </div>
  );
}
