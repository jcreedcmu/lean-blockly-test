import * as React from 'react';
import { useState } from 'react';
import type { CodeWithInfos, SubexprInfo, TaggedText } from '@leanprover/infoview-api';

/** Identifies the "current" subexpression box. `path` is a stable structural
 * id (so we can compare/highlight without object identity); `pos` is the Lean
 * `SubExpr.Pos` for that node (what a future conv-RPC would consume). */
export interface CurrentNode {
  path: string;
  pos: string | undefined;
}

export interface SubexprTreeProps {
  fmt: CodeWithInfos;
  /** Controlled "current" node. Omit to let the component manage it itself. */
  current?: CurrentNode | null;
  /** Notified whenever the current node changes (hover or extrinsic). */
  onCurrentChange?: (node: CurrentNode | null) => void;
}

/**
 * Proof-of-concept: render a goal's `CodeWithInfos` as nested bordered boxes
 * mirroring the term's subexpression hierarchy, keeping the same text.
 *
 * The "current" subexpression is explicit React state rather than CSS `:hover`,
 * so exactly one (innermost) box is current at a time, and the selection can be
 * driven either by the mouse here or extrinsically (pass `current` /
 * `onCurrentChange`, e.g. later from keyboard nav or a conv-selection flow).
 */
export function SubexprTree({ fmt, current, onCurrentChange }: SubexprTreeProps): React.ReactElement {
  const [internal, setInternal] = useState<CurrentNode | null>(null);
  // Controlled when `current` is provided (even as null); uncontrolled otherwise.
  const value = current !== undefined ? current : internal;
  const setCurrent = (node: CurrentNode | null) => {
    if (current === undefined) setInternal(node);
    onCurrentChange?.(node);
  };

  return (
    <div className="subexpr-tree">
      <div className="subexpr-tree-path">
        {value?.pos != null && value.pos !== ''
          ? `path from root: ${value.pos}`
          : value
            ? '(current node has no subexprPos)'
            : '(no current node)'}
      </div>
      <div className="subexpr-tree-body">
        {renderNode(fmt, '', null, value, setCurrent, 0)}
      </div>
    </div>
  );
}

function renderNode(
  tt: TaggedText<SubexprInfo>,
  path: string,
  parent: CurrentNode | null,
  current: CurrentNode | null,
  setCurrent: (node: CurrentNode | null) => void,
  key: number,
): React.ReactNode {
  const myPath = `${path}/${key}`;

  if ('text' in tt) {
    return tt.text;
  }

  if ('append' in tt) {
    // Append nodes are not subexpressions themselves: they don't change the
    // enclosing box (`parent`), they only extend the structural path.
    return (
      <React.Fragment key={key}>
        {tt.append.map((child, i) =>
          renderNode(child, myPath, parent, current, setCurrent, i),
        )}
      </React.Fragment>
    );
  }

  if ('tag' in tt) {
    const [info, content] = tt.tag;
    const self: CurrentNode = { path: myPath, pos: info.subexprPos };
    const isCurrent = current?.path === myPath;
    return (
      <div
        key={key}
        className={`subexpr-box${isCurrent ? ' subexpr-box-current' : ''}`}
        // mouseenter/leave (not over/out) so descendant boundaries are ignored:
        // entering this box makes it current; leaving it restores the enclosing
        // box, so the innermost box under the cursor stays current.
        onMouseEnter={() => setCurrent(self)}
        onMouseLeave={() => setCurrent(parent)}
      >
        {renderNode(content, myPath, self, current, setCurrent, 0)}
      </div>
    );
  }

  return null;
}
