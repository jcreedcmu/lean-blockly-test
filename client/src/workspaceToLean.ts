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
  inputs?: Record<string, { block?: SerializedBlock }>;
  next?: { block?: SerializedBlock };
  data?: string;
}

interface SerializedWorkspace {
  blocks?: {
    languageVersion?: number;
    blocks?: SerializedBlock[];
  };
}

/**
 * Generate Lean code from a single block and its children.
 */
function blockToCode(block: SerializedBlock | undefined, indent: string = ''): string {
  if (!block) return '';

  const type = block.type;
  const fields = block.fields ?? {};
  const inputs = block.inputs ?? {};

  let code = '';

  switch (type) {
    case 'lemma': {
      const name = fields['THEOREM_NAME'] ?? 'unnamed';
      const declaration = fields['THEOREM_DECLARATION'] ?? '';
      const variables = blockToCode(inputs['VARIABLES']?.block, '');
      const proof = blockToCode(inputs['LEMMA_PROOF']?.block, indent + '  ');
      code = `${indent}theorem ${name}${variables} : ${declaration} := by\n${proof}`;
      break;
    }

    case 'prop':
    case 'prop_dynamic': {
      // For propositions, return just the name (used as expression value)
      code = block.data ?? fields['PROP_NAME'] ?? '';
      break;
    }

    case 'prop_declaration': {
      const decl = fields['VARIABLE_DECL'] ?? '';
      const def = fields['VARIABLE_DEF'] ?? '';
      code = `(${decl} : ${def})`;
      // Chain to next variable declaration
      if (block.next?.block) {
        code += blockToCode(block.next.block, '');
      }
      break;
    }

    case 'tactic_sorry': {
      code = `${indent}sorry\n`;
      break;
    }

    case 'tactic_refl': {
      code = `${indent}rfl\n`;
      break;
    }

    case 'tactic_other': {
      const name = fields['PROP_NAME'] ?? '';
      code = `${indent}${name}\n`;
      break;
    }

    case 'tactic_intro':
    case 'tactic_exact':
    case 'tactic_apply':
    case 'tactic_use':
    case 'tactic_unfold':
    case 'tactic_have':
    case 'tactic_cases':
    case 'tactic_induction':
    case 'tactic_obtain': {
      const tacticName = type.replace('tactic_', '');
      const arg = blockToCode(inputs['ARG']?.block, '');
      code = `${indent}${tacticName} ${arg}\n`;
      break;
    }

    case 'tactic_rw': {
      const direction = fields['DIRECTION_TYPE'];
      const source = blockToCode(inputs['REWRITE_SOURCE']?.block, '');
      const arrow = direction === 'LEFT' ? '← ' : '';
      code = `${indent}rw [${arrow}${source}]\n`;
      break;
    }

    case 'tactic_rw_at': {
      const source = blockToCode(inputs['REWRITE_SOURCE']?.block, '');
      const target = blockToCode(inputs['REWRITE_TARGET']?.block, '');
      code = `${indent}rw ${source} at ${target}\n`;
      break;
    }

    case 'tactic_constructor': {
      code = `${indent}constructor\n`;
      const body1 = blockToCode(inputs['BODY1']?.block, indent + '  ');
      const body2 = blockToCode(inputs['BODY2']?.block, indent + '  ');
      // Replace leading spaces with bullet point for first line of each body
      if (body1) {
        code += body1.replace(new RegExp(`^${indent}  `), `${indent}· `);
      }
      if (body2) {
        code += body2.replace(new RegExp(`^${indent}  `), `${indent}· `);
      }
      break;
    }

    case 'tactic_show': {
      const goal = blockToCode(inputs['GOAL']?.block, '');
      const proof = blockToCode(inputs['PROOF']?.block, indent + '  ');
      // tactic_show is used as an expression (value input), not a statement
      code = `show ${goal} by\n${proof.replace(/\n$/, '')}`;
      break;
    }

    default:
      console.warn(`[workspaceToLean] Unknown block type: ${type}`);
      break;
  }

  // Handle chained blocks (next connection) for tactics
  if (block.next?.block && type !== 'prop_declaration') {
    code += blockToCode(block.next.block, indent);
  }

  return code;
}

/**
 * Convert a serialized Blockly workspace to Lean code.
 *
 * @param workspace - The serialized workspace state (from blockly.serialization.workspaces.save)
 * @returns The generated Lean code as a string
 */
export function workspaceToLean(workspace: BlocklyState): string {
  const ws = workspace as SerializedWorkspace;
  const topBlocks = ws.blocks?.blocks ?? [];

  const codeBlocks: string[] = [];

  for (const block of topBlocks) {
    const code = blockToCode(block, '');
    if (code) {
      codeBlocks.push(code);
    }
  }

  return codeBlocks.join('\n');
}
