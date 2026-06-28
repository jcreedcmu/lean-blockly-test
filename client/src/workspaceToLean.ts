/**
 * Convert a serialized Blockly workspace to Lean code.
 */

import type { BlocklyState } from './Blockly';

// Type definitions for the serialized block structure
export interface SerializedBlock {
  type: string;
  id?: string;
  x?: number;
  y?: number;
  fields?: Record<string, string>;
  inputs?: Record<string, { block?: SerializedBlock; shadow?: SerializedBlock }>;
  next?: { block?: SerializedBlock };
  data?: string;
}

export interface SerializedWorkspace {
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

/**
 * Synthetic `sourceInfo` id for an empty statement-input arm. When a tactic
 * synthesizes a placeholder (e.g. `· skip`) for an empty sub-proof, emit it as
 * a chunk keyed by this id so the arm has an addressable source position. The
 * goal-marker resolver reconstructs the same key.
 */
export function emptyArmId(blockId: string, inputName: string): string {
  return `${blockId}::${inputName}`;
}

function inputBlock(input: { block?: SerializedBlock; shadow?: SerializedBlock } | undefined): SerializedBlock | undefined {
  return input?.block ?? input?.shadow;
}

function collectSequentialFields(
  fields: Record<string, string>,
  firstName: string,
  nextPrefix: string,
): string[] {
  const names: string[] = [];
  if (firstName in fields) names.push(fields[firstName]);
  for (let i = 1; `${nextPrefix}${i}` in fields; i++) {
    names.push(fields[`${nextPrefix}${i}`]);
  }
  return names;
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
function bodyOrSkip(
  bodyChunks: CodeChunk[],
  indent: string,
  blockId: string,
  inputName: string,
): CodeChunk[] {
  if (bodyChunks.length === 0) {
    // Key the placeholder so an empty body is still an addressable source
    // position (e.g. for a goal-position marker that targets this input).
    return [chunk(`${indent}skip\n`, emptyArmId(blockId, inputName))];
  }
  return bodyChunks;
}

/**
 * Like `bodyOrSkip`, but **always** ends the body with a `skip` anchor — even
 * when the body is non-empty. This gives the body's *end* an observable,
 * addressable position (keyed by `emptyArmId`) for the status pill that governs
 * it: querying goals at the trailing `skip` yields the proof's end-state ("no
 * goals" when complete, the remaining goal when not), and an `unsolved goals`
 * diagnostic for an incomplete body lands in that same gap.
 *
 * `skip` is a no-op even with no goals, so the trailing anchor is safe after a
 * complete proof. See `plans/pill-position-mapping.md`.
 */
function bodyWithSkipAnchor(
  bodyChunks: CodeChunk[],
  indent: string,
  blockId: string,
  inputName: string,
): CodeChunk[] {
  return [...bodyChunks, chunk(`${indent}skip\n`, emptyArmId(blockId, inputName))];
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
        ...bodyWithSkipAnchor(proofChunks, indent + '  ', blockId, 'LEMMA_PROOF'),
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

    case 'tactic_conclude': {
      const args: CodeChunk[][] = [];
      for (let i = 0; inputs[`ARG${i}`]; i++) {
        args.push(blockToChunks(inputs[`ARG${i}`]?.block, ''));
      }
      const interleaved: CodeChunk[] = [];
      for (let i = 0; i < args.length; i++) {
        if (i > 0) interleaved.push(chunk(', ', blockId));
        interleaved.push(...args[i]);
      }
      chunks = [
        ...indentChunk,
        chunk(`conclude [`, blockId),
        ...interleaved,
        chunk(`]\n`, blockId),
      ];
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
      const names = collectSequentialFields(fields, 'NAME', 'NAME_');
      const nameStr = names.join(' ');
      chunks = [
        ...indentChunk,
        chunk(nameStr ? `intro ${nameStr}\n` : `intro\n`, blockId),
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
      const chosenNames = collectSequentialFields(fields, 'CHOSEN_NAME', 'CHOSEN_NAME_');
      const sourceChunks = blockToChunks(inputBlock(inputs['SOURCE']), '');
      chunks = [
        ...indentChunk,
        chunk(`choose ${chosenNames.join(' ')} using `, blockId),
        ...sourceChunks,
        chunk(`\n`, blockId),
      ];
      break;
    }

    // `specialize <HYP> <ARG> <ARG1> …`
    case 'tactic_specialize': {
      const hypChunks = blockToChunks(inputBlock(inputs['HYP']), '');
      const argChunks: CodeChunk[] = [];
      const emitArg = (key: string) => {
        const argBlock = inputBlock(inputs[key]);
        if (!argBlock) return;
        argChunks.push(text(' ('));
        argChunks.push(...blockToChunks(argBlock, ''));
        argChunks.push(text(')'));
      };
      emitArg('ARG');
      for (let i = 1; inputs[`ARG${i}`]; i++) {
        emitArg(`ARG${i}`);
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

    case 'term_archprop': {
      const argChunks = blockToChunks(inputs['ARG']?.block, '');
      chunks = [
        chunk('ArchProp', blockId),
        ...(argChunks.length > 0 ? [text(' '), ...argChunks] : []),
      ];
      break;
    }

    case 'tactic_at': {
      const hypChunks = blockToChunks(inputBlock(inputs['HYP']), '');
      const hyp = hypChunks.map(c => c.text).join('');
      const bodyBlock = inputs['BODY']?.block;
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
      const proofChunks = blockToChunks(inputs['PROOF']?.block, indent + '  ');
      const trimmedProofChunks = trimTrailingNewline(
        bodyOrSkip(proofChunks, indent + '  ', blockId, 'PROOF'),
      );
      chunks = [
        ...indentChunk,
        chunk(`rewrite [show ${from} = ${to} by\n`, blockId),
        ...trimmedProofChunks,
        chunk(`]\n`, blockId),
      ];
      break;
    }

    case 'tactic_conv': {
      const bodyChunks = blockToChunks(inputBlock(inputs['BODY']), indent + '  ');
      chunks = [
        ...indentChunk,
        chunk(`conv =>\n`, blockId),
        ...bodyOrSkip(bodyChunks, indent + '  ', blockId, 'BODY'),
      ];
      break;
    }

    case 'tactic_enter': {
      // `ENTER_PATH` holds the bracketed `enter` list (e.g. "[1, c]"),
      // precomputed by the server's `getConvTargets` RPC. Only valid inside
      // a `conv` block; used elsewhere it errors in Lean (intentionally).
      const path = fields['ENTER_PATH'] ?? '[]';
      chunks = [...indentChunk, chunk(`enter ${path}\n`, blockId)];
      break;
    }

    case 'tactic_have': {
      const name = fields['NAME'] ?? 'h';
      const type = fields['TYPE'] ?? 'True';
      const proofChunks = blockToChunks(inputBlock(inputs['PROOF']), indent + '  ');
      chunks = [
        ...indentChunk,
        chunk(`have ${name} : ${type} := by\n`, blockId),
        ...bodyOrSkip(proofChunks, indent + '  ', blockId, 'PROOF'),
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

      // Replace first indent with bullet for each body, and always append a
      // trailing `skip` anchor (keyed by a synthetic id) so the arm's end is an
      // observable, addressable position for its status pill — an empty branch
      // becomes `· skip`, a filled one ends with a `skip` continuation line.
      const bulletize = (bodyChunks: CodeChunk[], inputName: string): CodeChunk[] => {
        if (bodyChunks.length === 0) {
          // Empty arm: the bullet carries the `skip` anchor → `· skip`.
          return [text(`${indent}· `), chunk(`skip\n`, emptyArmId(blockId, inputName))];
        }
        // Filled arm: bullet the first tactic, append a `skip` continuation.
        const bulleted = bodyChunks[0].text === indent + '  '
          ? [text(`${indent}· `), ...bodyChunks.slice(1)]
          : bodyChunks;
        return [...bulleted, chunk(`${indent}  skip\n`, emptyArmId(blockId, inputName))];
      };

      chunks = [
        ...indentChunk,
        chunk(`constructor\n`, blockId),
        ...bulletize(body1Chunks, 'BODY1'),
        ...bulletize(body2Chunks, 'BODY2'),
      ];
      break;
    }

    case 'tactic_show': {
      const goalChunks = blockToChunks(inputBlock(inputs['GOAL']), '');
      const proofChunks = blockToChunks(inputBlock(inputs['PROOF']), indent + '  ');

      // Remove trailing newline from proof
      const trimmedProofChunks = trimTrailingNewline(
        bodyOrSkip(proofChunks, indent + '  ', blockId, 'PROOF'),
      );

      chunks = [
        chunk(`show `, blockId),
        ...goalChunks,
        chunk(` by\n`, blockId),
        ...trimmedProofChunks,
      ];
      break;
    }

    case 'tactic_calc': {
      const name = fields['NAME'] ?? 'h';
      const lhs = fields['LHS'] ?? 'a';
      const relSym = (r: string | undefined) =>
        ({ 'LEQ': '≤', 'LT': '<' } as Record<string, string>)[r ?? ''] ?? '=';
      const concludeArgs = (stepIdx: number): string => {
        const parts: string[] = [];
        for (let j = 0; inputs[`CONCLUDE_${stepIdx}_${j}`]; j++) {
          const argChunks = blockToChunks(inputs[`CONCLUDE_${stepIdx}_${j}`]?.block, '');
          const text = argChunks.map(c => c.text).join('').trim();
          if (text) parts.push(text);
        }
        return parts.join(', ');
      };
      chunks = [
        ...indentChunk,
        chunk(`have ${name} := calc\n`, blockId),
        chunk(`${indent}  ${lhs} ${relSym(fields['REL_0'])} ${fields['RHS_0'] ?? 'b'} := by conclude [${concludeArgs(0)}]\n`, blockId),
      ];
      for (let i = 1; `RHS_${i}` in fields; i++) {
        chunks.push(chunk(`${indent}  _ ${relSym(fields[`REL_${i}`])} ${fields[`RHS_${i}`]} := by conclude [${concludeArgs(i)}]\n`, blockId));
      }
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
