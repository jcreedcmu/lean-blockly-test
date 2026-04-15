import * as React from 'react';
import type { InteractiveHypothesisBundle, SubexprInfo } from '@leanprover/infoview-api';
import { InteractiveHypothesisBundle_nonAnonymousNames } from '@leanprover/infoview-api';
import { InteractiveCode } from './InteractiveCode';

/**
 * Classification of a hypothesis for the purpose of choosing which
 * drag affordances to offer next to it. Currently the only non-trivial
 * value is `'equational'`, which earns the `apply` / `rewrite`
 * affordances; the type is a discriminated union to leave room for
 * future classes (e.g. distinguishing genuine equations from
 * implications, or function-typed hypotheses) without rewriting the
 * call sites.
 */
export type HypClass = 'equational' | undefined;

/** Props that control hypothesis interaction, shared across Hyp/Goal/Goals. */
export interface HypInteractionProps {
  /** Which drag affordances are allowed on this level (e.g. 'apply', 'rewrite'). undefined = all. */
  allowedAffordances?: Set<string>;
  onHypNameClick?: (name: string, hyp: InteractiveHypothesisBundle) => void;
  onHypDragStart?: (name: string, e: React.MouseEvent, mode?: 'prop' | 'apply' | 'rewrite') => void;
  onSubexprClick?: (info: SubexprInfo) => void;
}

export interface HypProps extends HypInteractionProps {
  hyp: InteractiveHypothesisBundle;
  /** Classification of this hypothesis. Controls which drag affordances are offered. */
  affordances?: HypClass;
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
      {onHypDragStart && affordances === 'equational' && (
        <>
          {(!allowedAffordances || allowedAffordances.has('apply')) &&
            <span className="hyp-cell hyp-action hyp-action-apply"
              onMouseDown={(e) => onHypDragStart(name, e, 'apply')}>apply</span>}
          {(!allowedAffordances || allowedAffordances.has('rewrite')) &&
            <span className="hyp-cell hyp-action hyp-action-rewrite"
              onMouseDown={(e) => onHypDragStart(name, e, 'rewrite')}>rewrite</span>}
        </>
      )}
    </div>
  );
}
