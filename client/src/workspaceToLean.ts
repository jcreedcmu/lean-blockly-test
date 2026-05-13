/**
 * Convert a serialized Blockly workspace to Lean code.
 */

import type { BlocklyState } from './Blockly';

// Type definitions for the serialized block structure
interface SerializedBlock {
  type: string;
  id?: string;
  x?: number;
  y?: number;
  fields?: Record<string, string>;
  inputs?: Record<string, { block?: SerializedBlock; shadow?: SerializedBlock }>;
  next?: { block?: SerializedBlock };
  data?: string;
}

interface SerializedWorkspace {
  blocks?: {
    languageVersion?: number;
    blocks?: SerializedBlock[];
  };
}

// Intermediate representation: chunks of code with optional block ownership
type CodeChunk = {
  text: string;
  blockId?: string;
};

// Output types
export type SourceInfo = {
  id: string;
  startLineCol: [number, number];
  endLineCol: [number, number];
};

export type WorkspaceToLeanResult = {
  leanCode: string;
  sourceInfo: SourceInfo[];
};

// Helper to create a chunk with block ID
function chunk(text: string, blockId?: string): CodeChunk {
  return { text, blockId };
}

// Helper to create chunks without block ID (plain text)
function text(t: string): CodeChunk {
  return { text: t };
}

function inputBlock(input: { block?: SerializedBlock; shadow?: SerializedBlock } | undefined): SerializedBlock | undefined {
  return input?.block ?? input?.shadow;
}

function collectSequentialInputs(
  inputs: Record<string, { block?: SerializedBlock; shadow?: SerializedBlock }>,
  firstInputName: string,
  nextInputPrefix: string,
  separator: string,
): CodeChunk[] {
  const chunks: CodeChunk[] = [];
  const appendArg = (inputName: string) => {
    const inputChunks = blockToChunks(inputBlock(inputs[inputName]), '');
    if (inputChunks.every(c => c.text.length === 0)) return;
    if (chunks.length > 0) chunks.push(text(separator));
    chunks.push(...inputChunks);
  };

  appendArg(firstInputName);
  for (let i = 1; inputs[`${nextInputPrefix}${i}`]; i++) {
    appendArg(`${nextInputPrefix}${i}`);
  }
  return chunks;
}

/**
 * If a tactic-body slot is empty, fill it with `skip` so the resulting
 * Lean still parses and elaborates as a real proof attempt with an
 * "unsolved goals" diagnostic. The diagnostic carries the goal state at
 * that hole, which is exactly what we want to display to the player.
 *
 * `skip` is preferred over `sorry` because it doesn't make the
 * declaration "succeed" with a warning — the proof legitimately fails
 * with unsolved goals, and `LevelEvaluator` reports the level as
 * incomplete (`complete: false`).
 */
function bodyOrSkip(bodyChunks: CodeChunk[], indent: string): CodeChunk[] {
  if (bodyChunks.length === 0) {
    return [text(`${indent}skip\n`)];
  }
  return bodyChunks;
}

/**
 * Generate code chunks from a single block and its children.
 */
function blockToChunks(
  block: SerializedBlock | undefined,
  indent: string = '',
  noFirstIndent: boolean = false
): CodeChunk[] {
  if (!block) return [];

  const tp = block.type;
  const fields = block.fields ?? {};
  const inputs = block.inputs ?? {};
  const blockId = block.id;

  let chunks: CodeChunk[] = [];

  // Add indent unless noFirstIndent is set
  const indentChunk = noFirstIndent ? [] : [text(indent)];

  switch (tp) {
    case 'lemma': {
      const name = fields['THEOREM_NAME'] ?? 'unnamed';
      const declaration = fields['THEOREM_DECLARATION'] ?? '';
      const proofChunks = blockToChunks(inputBlock(inputs['LEMMA_PROOF']), indent + '  ');
      // THEOREM_DECLARATION should contain the full signature, e.g. "(a b : ℕ) : a + b = b + a"
      chunks = [
        chunk(`theorem ${name} ${declaration} := by\n`, blockId),
        ...bodyOrSkip(proofChunks, indent + '  '),
      ];
      break;
    }

    case 'prop':
    case 'prop_dynamic': {
      const value = block.data ?? fields['PROP_NAME'] ?? '';
      chunks = [chunk(value, blockId)];
      break;
    }

    case 'prop_declaration': {
      const decl = fields['VARIABLE_DECL'] ?? '';
      const def = fields['VARIABLE_DEF'] ?? '';
      chunks = [chunk(`(${decl} : ${def})`, blockId)];
      // Chain to next variable declaration
      if (block.next?.block) {
        chunks.push(...blockToChunks(block.next.block, ''));
      }
      return chunks; // Early return - no indent prefix for prop_declaration
    }

    case 'tactic_sorry': {
      chunks = [...indentChunk, chunk(`sorry\n`, blockId)];
      break;
    }

    case 'tactic_refl': {
      chunks = [...indentChunk, chunk(`rfl\n`, blockId)];
      break;
    }

    case 'tactic_ring_nf': {
      chunks = [...indentChunk, chunk(`ring_nf\n`, blockId)];
      break;
    }

    case 'tactic_simp': {
      chunks = [...indentChunk, chunk(`simp\n`, blockId)];
      break;
    }

    case 'tactic_other': {
      const name = fields['PROP_NAME'] ?? '';
      chunks = [...indentChunk, chunk(`${name}\n`, blockId)];
      break;
    }

    case 'tactic_exact':
    case 'tactic_apply':
    case 'tactic_unfold':
    case 'tactic_cases':
    case 'tactic_induction':
    case 'tactic_obtain': {
      const tacticName = tp.replace('tactic_', '');
      const argChunks = blockToChunks(inputBlock(inputs['ARG']), '');
      chunks = [
        ...indentChunk,
        chunk(`${tacticName} `, blockId),
        ...argChunks,
        chunk(`\n`, blockId),
      ];
      break;
    }

    case 'tactic_intro': {
      const argChunks = collectSequentialInputs(inputs, 'ARG', 'ARG', ' ');

      chunks = [
        ...indentChunk,
        chunk('intro', blockId),
        ...(argChunks.length > 0 ? [chunk(' ', blockId), ...argChunks] : []),
        chunk(`\n`, blockId),
      ];
      break;
    }

    case 'tactic_use': {
      const argChunks = collectSequentialInputs(inputs, 'ARG', 'ARG', ', ');

      chunks = [
        ...indentChunk,
        chunk('use', blockId),
        ...(argChunks.length > 0 ? [chunk(' ', blockId), ...argChunks] : []),
        chunk(`\n`, blockId),
      ];
      break;
    }

    case 'tactic_choose': {
      const chosenChunks = blockToChunks(inputBlock(inputs['CHOSEN']), '');
      const sourceChunks = blockToChunks(inputBlock(inputs['SOURCE']), '');
      chunks = [
        ...indentChunk,
        chunk(`choose `, blockId),
        ...chosenChunks,
        chunk(` using `, blockId),
        ...sourceChunks,
        chunk(`\n`, blockId),
      ];
      break;
    }

    // `specialize <HYP> <ARG> <ARG1> …`
    case 'tactic_specialize': {
      const hypChunks = blockToChunks(inputBlock(inputs['HYP']), '');
      const argChunks: CodeChunk[] = [];
      if (inputs['ARG']) {
        argChunks.push(text(' '));
        argChunks.push(...blockToChunks(inputBlock(inputs['ARG']), ''));
      }
      for (let i = 1; inputs[`ARG${i}`]; i++) {
        argChunks.push(text(' '));
        argChunks.push(...blockToChunks(inputBlock(inputs[`ARG${i}`]), ''));
      }
      chunks = [
        ...indentChunk,
        chunk(`specialize `, blockId),
        ...hypChunks,
        ...argChunks,
        chunk(`\n`, blockId),
      ];
      break;
    }

    case 'tactic_at': {
      const hyp = fields['HYP'] ?? 'h';
      const bodyBlock = inputBlock(inputs['BODY']);
      // Strip next chain so only the first tactic is processed
      const firstBlock = bodyBlock ? { ...bodyBlock, next: undefined } : undefined;
      const tacticChunks = trimTrailingNewline(blockToChunks(firstBlock, indent));
      chunks = tacticChunks.length > 0
        ? [...tacticChunks, chunk(` at ${hyp}\n`, blockId)]
        : [...indentChunk, chunk(`skip at ${hyp}\n`, blockId)];
      break;
    }

    case 'tactic_transform': {
      const from = fields['FROM'] ?? 'X';
      const to = fields['TO'] ?? 'Y';
      const proofChunks = blockToChunks(inputBlock(inputs['PROOF']), indent + '  ');
      const trimmedProofChunks = trimTrailingNewline(
        bodyOrSkip(proofChunks, indent + '  '),
      );
      chunks = [
        ...indentChunk,
        chunk(`rewrite [show ${from} = ${to} by\n`, blockId),
        ...trimmedProofChunks,
        chunk(`]\n`, blockId),
      ];
      break;
    }

    case 'tactic_have': {
      const name = fields['NAME'] ?? 'h';
      const type = fields['TYPE'] ?? 'True';
      const proofChunks = blockToChunks(inputBlock(inputs['PROOF']), indent + '  ');
      chunks = [
        ...indentChunk,
        chunk(`have ${name} : ${type} := by\n`, blockId),
        ...bodyOrSkip(proofChunks, indent + '  '),
      ];
      break;
    }

    case 'tactic_rewrite': {
      const buildEntry = (dirKey: string, srcKey: string): CodeChunk[] => {
        const arrow = fields[dirKey] === 'LEFT' ? '← ' : '';
        const src = blockToChunks(inputBlock(inputs[srcKey]), indent + '  ', true);
        return arrow ? [chunk(arrow, blockId), ...src] : src;
      };
      const entries: CodeChunk[][] = [buildEntry('DIRECTION_TYPE', 'REWRITE_SOURCE')];
      for (let i = 1; inputs[`REWRITE_SOURCE_${i}`]; i++) {
        entries.push(buildEntry(`DIRECTION_TYPE_${i}`, `REWRITE_SOURCE_${i}`));
      }
      const interleaved: CodeChunk[] = [];
      for (let i = 0; i < entries.length; i++) {
        if (i > 0) interleaved.push(chunk(', ', blockId));
        interleaved.push(...entries[i]);
      }
      chunks = [
        ...indentChunk,
        chunk(`rewrite [`, blockId),
        ...interleaved,
        chunk(`]\n`, blockId),
      ];
      break;
    }

    case 'tactic_rewrite_at': {
      const sourceChunks = blockToChunks(inputBlock(inputs['REWRITE_SOURCE']), indent + '  ', true);
      const targetChunks = blockToChunks(inputBlock(inputs['REWRITE_TARGET']), indent + '  ', true);
      chunks = [
        ...indentChunk,
        chunk(`rewrite [`, blockId),
        ...sourceChunks,
        chunk(`] at `, blockId),
        ...targetChunks,
        chunk(`\n`, blockId),
      ];
      break;
    }

    case 'tactic_constructor': {
      const body1Chunks = blockToChunks(inputBlock(inputs['BODY1']), indent + '  ');
      const body2Chunks = blockToChunks(inputBlock(inputs['BODY2']), indent + '  ');

      // Replace first indent with bullet for each body. If a branch is
      // entirely empty, emit `· skip` so it parses and produces an
      // unsolved-goals diagnostic at that branch.
      const bulletize = (bodyChunks: CodeChunk[]): CodeChunk[] => {
        if (bodyChunks.length === 0) {
          return [text(`${indent}· skip\n`)];
        }
        if (bodyChunks.length > 0 && bodyChunks[0].text === indent + '  ') {
          return [text(`${indent}· `), ...bodyChunks.slice(1)];
        }
        return bodyChunks;
      };

      chunks = [
        ...indentChunk,
        chunk(`constructor\n`, blockId),
        ...bulletize(body1Chunks),
        ...bulletize(body2Chunks),
      ];
      break;
    }

    case 'tactic_show': {
      const goalChunks = blockToChunks(inputBlock(inputs['GOAL']), '');
      const proofChunks = blockToChunks(inputBlock(inputs['PROOF']), indent + '  ');

      // Remove trailing newline from proof
      const trimmedProofChunks = trimTrailingNewline(
        bodyOrSkip(proofChunks, indent + '  '),
      );

      chunks = [
        chunk(`show `, blockId),
        ...goalChunks,
        chunk(` by\n`, blockId),
        ...trimmedProofChunks,
      ];
      break;
    }

    default:
      console.warn(`[workspaceToLean] Unknown block type: ${tp}`);
      return [];
  }

  // Handle chained blocks (next connection) for tactics
  // Note: prop_declaration returns early with its own next handling
  if (block.next?.block) {
    chunks.push(...blockToChunks(block.next.block, indent));
  }

  return chunks;
}

/**
 * Remove trailing newline from the last chunk if present.
 */
function trimTrailingNewline(chunks: CodeChunk[]): CodeChunk[] {
  if (chunks.length === 0) return chunks;
  const last = chunks[chunks.length - 1];
  if (last.text.endsWith('\n')) {
    return [
      ...chunks.slice(0, -1),
      { ...last, text: last.text.slice(0, -1) },
    ];
  }
  return chunks;
}

/**
 * Flatten chunks into a string and compute source info.
 */
function flattenChunks(chunks: CodeChunk[]): WorkspaceToLeanResult {
  let leanCode = '';
  let line = 0;
  let col = 0;

  // Track block ranges: blockId -> { start, end }
  const blockRanges = new Map<string, { start: [number, number]; end: [number, number] }>();

  for (const chunk of chunks) {
    const startLine = line;
    const startCol = col;

    // Update position as we add text
    // Use index-based loop to count UTF-16 code units (LSP convention)
    // rather than Unicode codepoints (which for...of would give)
    for (let i = 0; i < chunk.text.length; i++) {
      if (chunk.text[i] === '\n') {
        line++;
        col = 0;
      } else {
        col++;
      }
    }

    leanCode += chunk.text;

    // Track block range
    if (chunk.blockId) {
      const existing = blockRanges.get(chunk.blockId);
      if (existing) {
        // Extend the range
        existing.end = [line, col];
      } else {
        // New range
        blockRanges.set(chunk.blockId, {
          start: [startLine, startCol],
          end: [line, col],
        });
      }
    }
  }

  // Convert to SourceInfo array
  const sourceInfo: SourceInfo[] = [];
  for (const [id, range] of blockRanges) {
    sourceInfo.push({
      id,
      startLineCol: range.start,
      endLineCol: range.end,
    });
  }

  return { leanCode, sourceInfo };
}

/**
 * Convert a serialized Blockly workspace to Lean code with source mapping.
 *
 * @param workspace - The serialized workspace state (from blockly.serialization.workspaces.save)
 * @returns The generated Lean code and source info mapping block IDs to positions
 */
export function workspaceToLean(workspace: BlocklyState): WorkspaceToLeanResult {
  const ws = workspace as SerializedWorkspace;
  const allTopBlocks = ws.blocks?.blocks ?? [];

  // Only process lemma blocks (main theorems), ignore loose tactics or other blocks
  const lemmaBlocks = allTopBlocks.filter(block => block.type === 'lemma');

  const allChunks: CodeChunk[] = [];

  for (let i = 0; i < lemmaBlocks.length; i++) {
    const chunks = blockToChunks(lemmaBlocks[i], '');
    allChunks.push(...chunks);

    // Add blank line between top-level blocks
    if (i < lemmaBlocks.length - 1) {
      allChunks.push(text('\n'));
    }
  }

  return flattenChunks(allChunks);
}
