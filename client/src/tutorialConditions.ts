import type { BlocklyState } from './Blockly';
import type { TutorialAdvanceCondition, TutorialBlockPattern } from './gameData';

type SerializedInput = {
  block?: SerializedBlock;
  shadow?: SerializedBlock;
};

type SerializedBlock = {
  type?: string;
  fields?: Record<string, unknown>;
  inputs?: Record<string, SerializedInput>;
  next?: SerializedInput;
};

function topLevelBlocks(workspace: BlocklyState | null): SerializedBlock[] {
  const blocks = (workspace as { blocks?: { blocks?: unknown } } | null)?.blocks?.blocks;
  return Array.isArray(blocks) ? blocks as SerializedBlock[] : [];
}

function inputBlock(input: SerializedInput | undefined): SerializedBlock | undefined {
  return input?.block ?? input?.shadow;
}

function blockChildren(block: SerializedBlock): SerializedBlock[] {
  const children: SerializedBlock[] = [];
  for (const input of Object.values(block.inputs ?? {})) {
    const child = inputBlock(input);
    if (child) children.push(child);
  }
  const next = inputBlock(block.next);
  if (next) children.push(next);
  return children;
}

function blockMatches(block: SerializedBlock | undefined, pattern: TutorialBlockPattern): boolean {
  if (!block || block.type !== pattern.type) return false;

  for (const [name, expectedValue] of Object.entries(pattern.fields ?? {})) {
    if (String(block.fields?.[name] ?? '') !== expectedValue) return false;
  }

  for (const [inputName, inputPattern] of Object.entries(pattern.inputs ?? {})) {
    if (!blockMatches(inputBlock(block.inputs?.[inputName]), inputPattern)) return false;
  }

  return true;
}

function descendantsContain(block: SerializedBlock, pattern: TutorialBlockPattern): boolean {
  if (blockMatches(block, pattern)) return true;
  return blockChildren(block).some(child => descendantsContain(child, pattern));
}

function workspaceContainsBlock(
  workspace: BlocklyState | null,
  pattern: TutorialBlockPattern,
  location: 'any' | 'topLevel' | 'theoremProof' = 'any',
): boolean {
  const blocks = topLevelBlocks(workspace);

  if (location === 'topLevel') {
    return blocks.some(block => blockMatches(block, pattern));
  }

  if (location === 'theoremProof') {
    return blocks
      .filter(block => block.type === 'lemma')
      .some(lemma => {
        const proofRoot = inputBlock(lemma.inputs?.LEMMA_PROOF);
        return proofRoot ? descendantsContain(proofRoot, pattern) : false;
      });
  }

  return blocks.some(block => descendantsContain(block, pattern));
}

function elementIsVisible(element: Element): boolean {
  const rect = element.getBoundingClientRect();
  if (rect.width <= 0 || rect.height <= 0) return false;
  if (element.getClientRects().length === 0) return false;

  let current: Element | null = element;
  while (current) {
    const style = window.getComputedStyle(current);
    if (
      style.display === 'none'
      || style.visibility === 'hidden'
      || style.visibility === 'collapse'
      || style.opacity === '0'
    ) {
      return false;
    }
    current = current.parentElement;
  }

  return true;
}

export function tutorialAdvanceConditionMet(
  condition: TutorialAdvanceCondition,
  workspace: BlocklyState | null,
  proofComplete: boolean,
): boolean {
  if (condition.kind === 'proofComplete') return proofComplete;

  if (condition.kind === 'elementExists') {
    if (typeof document === 'undefined') return false;
    const element = document.querySelector(condition.selector);
    if (!element) return false;
    if (!condition.visible) return true;
    return elementIsVisible(element);
  }

  return workspaceContainsBlock(
    workspace,
    condition.block,
    condition.location ?? 'any',
  );
}
