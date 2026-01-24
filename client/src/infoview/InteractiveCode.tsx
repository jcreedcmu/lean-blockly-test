import * as React from 'react';
import type { CodeWithInfos, SubexprInfo, TaggedText } from '@leanprover/infoview-api';

export interface InteractiveCodeProps {
  fmt: CodeWithInfos;
  onSubexprClick?: (info: SubexprInfo) => void;
}

/**
 * Renders CodeWithInfos (TaggedText<SubexprInfo>) as React elements.
 *
 * TaggedText is a recursive structure:
 * - { text: string } - plain text
 * - { append: TaggedText[] } - concatenation of children
 * - { tag: [T, TaggedText] } - tagged subexpression with metadata
 */
export function InteractiveCode({ fmt, onSubexprClick }: InteractiveCodeProps): React.ReactElement {
  return <span className="interactive-code">{renderTaggedText(fmt, onSubexprClick, 0)}</span>;
}

function renderTaggedText(
  tt: TaggedText<SubexprInfo>,
  onSubexprClick: ((info: SubexprInfo) => void) | undefined,
  key: number
): React.ReactNode {
  if ('text' in tt) {
    return tt.text;
  }

  if ('append' in tt) {
    return (
      <React.Fragment key={key}>
        {tt.append.map((child, i) => renderTaggedText(child, onSubexprClick, i))}
      </React.Fragment>
    );
  }

  if ('tag' in tt) {
    const [info, content] = tt.tag;
    const className = getSubexprClassName(info);

    const handleClick = onSubexprClick
      ? (e: React.MouseEvent) => {
          e.stopPropagation();
          onSubexprClick(info);
        }
      : undefined;

    return (
      <span
        key={key}
        className={className}
        onClick={handleClick}
        style={onSubexprClick ? { cursor: 'pointer' } : undefined}
      >
        {renderTaggedText(content, onSubexprClick, 0)}
      </span>
    );
  }

  // Fallback - shouldn't happen with well-formed data
  return null;
}

function getSubexprClassName(info: SubexprInfo): string {
  const classes = ['subexpr'];

  if (info.diffStatus) {
    classes.push(`diff-${info.diffStatus}`);
  }

  return classes.join(' ');
}
