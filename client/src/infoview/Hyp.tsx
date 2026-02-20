import * as React from 'react';
import type { InteractiveHypothesisBundle, SubexprInfo } from '@leanprover/infoview-api';
import { InteractiveHypothesisBundle_nonAnonymousNames } from '@leanprover/infoview-api';
import { InteractiveCode } from './InteractiveCode';

export interface HypProps {
  hyp: InteractiveHypothesisBundle;
  onNameClick?: (name: string, hyp: InteractiveHypothesisBundle) => void;
  onHypDragStart?: (name: string, e: React.MouseEvent, mode?: 'prop' | 'apply' | 'rewrite') => void;
  onSubexprClick?: (info: SubexprInfo) => void;
}

/** Returns true if the name contains the inaccessible marker. */
function isInaccessibleName(name: string): boolean {
  return name.includes('\u271D'); // dagger symbol
}

/**
 * Renders a single hypothesis bundle.
 * A bundle can have multiple names sharing the same type (e.g., "x y z : Nat").
 */
export function Hyp({ hyp, onNameClick, onHypDragStart, onSubexprClick }: HypProps): React.ReactElement {
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
        onClick={onNameClick ? () => onNameClick(name, hyp) : undefined}
        onMouseDown={onHypDragStart ? (e) => onHypDragStart(name, e) : undefined}
        style={{ cursor: onHypDragStart ? 'grab' : onNameClick ? 'pointer' : undefined }}
      >
        {name}
        {i < names.length - 1 ? ' ' : ''}
      </span>
    );
  });

  return (
    <div className="hyp">
      <span className="hyp-names">{nameElements}</span>
      <span className="hyp-colon"> : </span>
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
      {onHypDragStart && names.map((name, i) => (
        <span key={`actions-${i}`} className="hyp-actions">
          <span className="hyp-action hyp-action-apply"
            onMouseDown={(e) => onHypDragStart(name, e, 'apply')}>apply</span>
          <span className="hyp-action hyp-action-rewrite"
            onMouseDown={(e) => onHypDragStart(name, e, 'rewrite')}>rewrite</span>
        </span>
      ))}
    </div>
  );
}
