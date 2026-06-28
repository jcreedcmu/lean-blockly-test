import * as React from 'react';
import { useState } from 'react';
import type { CodeWithInfos, SubexprInfo, TaggedText } from '@leanprover/infoview-api';

/** Identifies the "current" subexpression box. `path` is a stable structural
 * id (so we can compare/highlight without object identity); `pos` is the Lean
 * `SubExpr.Pos` for that node (what the conv-RPC keys on). */
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
  /** subexprPos → `conv` `enter` args, from the `getConvTargets` RPC. A span
   * is draggable iff its position has an entry here. */
  convTargets?: Map<string, string[]>;
  /** Start dragging an `enter` block populated with the given `enter` args. */
  onSubexprDrag?: (enterArgs: string[], e: React.MouseEvent) => void;
}

interface RenderCtx {
  current: CurrentNode | null;
  setCurrent: (node: CurrentNode | null) => void;
  convTargets?: Map<string, string[]>;
  onSubexprDrag?: (enterArgs: string[], e: React.MouseEvent) => void;
}

/**
 * Render a goal's `CodeWithInfos` as plain inline text — by default it reads
 * exactly like the normal goal view, with the subexpression hierarchy latent in
 * nested spans rather than shown with borders. Hovering highlights the
 * innermost subexpression under the cursor; spans whose position is a valid
 * `conv` target are draggable, spawning a bare `enter` block with that path.
 */
export function SubexprTree({
  fmt, current, onCurrentChange, convTargets, onSubexprDrag,
}: SubexprTreeProps): React.ReactElement {
  const [internal, setInternal] = useState<CurrentNode | null>(null);
  // Controlled when `current` is provided (even as null); uncontrolled otherwise.
  const value = current !== undefined ? current : internal;
  const setCurrent = (node: CurrentNode | null) => {
    if (current === undefined) setInternal(node);
    onCurrentChange?.(node);
  };

  const ctx: RenderCtx = { current: value, setCurrent, convTargets, onSubexprDrag };

  return <span className="subexpr-tree">{renderNode(fmt, '', null, ctx, 0)}</span>;
}

function renderNode(
  tt: TaggedText<SubexprInfo>,
  path: string,
  parent: CurrentNode | null,
  ctx: RenderCtx,
  key: number,
): React.ReactNode {
  const myPath = `${path}/${key}`;

  if ('text' in tt) {
    return tt.text;
  }

  if ('append' in tt) {
    // Append nodes aren't subexpressions: they don't change the enclosing box
    // (`parent`), only the structural path.
    return (
      <React.Fragment key={key}>
        {tt.append.map((child, i) => renderNode(child, myPath, parent, ctx, i))}
      </React.Fragment>
    );
  }

  if ('tag' in tt) {
    const [info, content] = tt.tag;
    const self: CurrentNode = { path: myPath, pos: info.subexprPos };
    const isCurrent = ctx.current?.path === myPath;

    const enter = info.subexprPos != null ? ctx.convTargets?.get(info.subexprPos) : undefined;
    const draggable = !!(enter && ctx.onSubexprDrag);

    const className =
      'subexpr-span'
      // Only highlight the hovered subexpression when it's a valid conv target.
      + (isCurrent && draggable ? ' subexpr-span-current' : '')
      + (draggable ? ' subexpr-span-draggable' : '');

    return (
      <span
        key={key}
        className={className}
        // mouseenter/leave (not over/out): entering makes this span current,
        // leaving restores the enclosing span, so the innermost span wins.
        onMouseEnter={() => ctx.setCurrent(self)}
        onMouseLeave={() => ctx.setCurrent(parent)}
        // stopPropagation so the innermost draggable span owns the drag.
        onMouseDown={draggable
          ? (e) => { e.stopPropagation(); ctx.onSubexprDrag!(enter!, e); }
          : undefined}
      >
        {renderNode(content, myPath, self, ctx, 0)}
      </span>
    );
  }

  return null;
}
