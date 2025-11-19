import * as blockly from 'blockly';
import { Block } from 'blockly';
import * as blocks from './blocks';


/*
Adapted from https://github.com/aneilmac/blockly-plugin-lean under the Apache 2.0 license
*/

enum LeanPrec {
  ORDER_ATOMIC = 0,
  ORDER_NON = 99,
}

function genProp(block: Block): [string, LeanPrec] {
  if (block.data) {
    return [block.data, LeanPrec.ORDER_ATOMIC];
  } else {
    return [block.getFieldValue('PROP_NAME'), LeanPrec.ORDER_ATOMIC];
  }
}

function genLemma(block: Block, gen: blockly.CodeGenerator): string {
  let code = 'theorem ';
  const text_theorem_name = block.getFieldValue('THEOREM_NAME');
  const variables = gen.statementToCode(block, 'VARIABLES');
  const text_theorem_statement = block.getFieldValue('THEOREM_DECLARATION');
  code += text_theorem_name + variables + ' : ' + text_theorem_statement;
  code += ' := by\n';

  // code += 'begin';
  // if (block.data) {
  //   code += ` [${block.data}]`;
  // }
  // code += '\n';

  code += gen.statementToCode(block, 'LEMMA_PROOF');
  return code;
}

export function mkLeanGenerator(): blockly.CodeGenerator {
  const gen = new blockly.CodeGenerator('Lean');

  gen.forBlock['lemma'] = genLemma;
  gen.forBlock['prop'] = genProp;
  gen.forBlock['prop_dynamic'] = genProp;
  gen.forBlock['tactic_other'] = block => block.getFieldValue('PROP_NAME') + '\n';

  gen.forBlock['prop_declaration'] = block => {
    const decl = block.getFieldValue('VARIABLE_DECL');
    const def = block.getFieldValue('VARIABLE_DEF');
    return `(${decl} : ${def})`;
  };
  gen.forBlock['tactic_sorry'] = () => 'sorry\n';
  gen.forBlock['tactic_refl'] = () => 'rfl\n';

  for (const t of blocks.singleArgTactics) {
    gen.forBlock[`tactic_${t.name}`] = block => {
      let code = `${t.name} `;
      code += gen.valueToCode(block, 'ARG', LeanPrec.ORDER_ATOMIC);
      return code + '\n';
    };
  }

  gen.forBlock['tactic_rw'] = block => {
    let code = 'rw [';

    const dropdownDirectionOptions = block.getFieldValue('DIRECTION_TYPE');

    if (dropdownDirectionOptions === 'LEFT') {
      code += '← ';
    }

    code += gen.valueToCode(block, 'REWRITE_SOURCE',
      LeanPrec.ORDER_ATOMIC);

    return code + ']\n';
  };
  gen.forBlock['tactic_rw_at'] = block => {
    let code = 'rw ';

    code += gen.valueToCode(block, 'REWRITE_SOURCE',
      LeanPrec.ORDER_ATOMIC);

    code += ' at ';

    code += gen.valueToCode(block, 'REWRITE_TARGET',
      LeanPrec.ORDER_ATOMIC);

    return code + '\n';
  };
  gen.forBlock['tactic_constructor'] = block => {
    let code = 'constructor\n';
    code += gen.statementToCode(block, 'BODY1').replace(/^ /, '·');
    code += gen.statementToCode(block, 'BODY2').replace(/^ /, '·');
    return code + '\n';
  };
  gen.forBlock['tactic_show'] = block => {
    let code = 'show ' + gen.valueToCode(block, 'GOAL', LeanPrec.ORDER_ATOMIC) + ' by\n';
    code += gen.statementToCode(block, 'PROOF').replace(/\n$/, '');
    return [code, LeanPrec.ORDER_ATOMIC];
  };


  gen.addReservedWords('theorem,lemma,axiom,axioms,variable,protected,' +
    'private,def,meta,mutual,example,noncomputable,' +
    'variables,parameter,parameters,constant,constants,' +
    'using_well_founded,' +
    'end,namespace,section,prelude,' +
    'import,inductive,coinductive,structure,class,universe,' +
    'universes,local,precedence,reserve,infixl,infixr,' +
    'infix,postfix,prefix,notation,' +
    'set_option,open,export,' +
    'attribute,instance,include,omit,' +
    'declare_trace,add_key_equivalence,' +
    'run_cmd,#check,#reduce,#eval,#print,#help,#exit,' +
    '#compile,#unify,' +
    'fun,Pi,let,in,at,' +
    'have,assume,show,suffices,' +
    'do,if,then,else,by,' +
    'hiding,replacing,' +
    'from,Type,Sort,with,without,calc,begin,using,sorry,match,renaming,extends'
  );

  gen.scrub_ = (block, code, optThisOnly) => {
    const nextBlock = block.nextConnection && block.nextConnection.targetBlock();
    const nextCode = optThisOnly ? '' : gen.blockToCode(nextBlock);
    return code + nextCode;
  };

  return gen;
}

// function defineText(Generator: any) {
//   Generator['text'] = (block: Block) => {
//     const code = Generator.quote_(block.getFieldValue('TEXT'));
//     return [code, Generator.LeanPrec.ORDER_ATOMIC];
//   };
// }

//   /**
//    * @param string
//    * @return String that is quoted.
//    */
//   quote_(string: string): string {
//     string = string.replace(/\\/g, '\\\\')
//       .replace(/\n/g, '\\\n');

//     // Follow the CPython behaviour of repr() for a non-byte string.
//     let quote = '"';
//     if (string.indexOf('"') !== -1) {
//       if (string.indexOf('\'') === -1) {
//         quote = '\'';
//       } else {
//         string = string.replace(/"/g, '\\"');
//       }
//     }
//     return quote + string + quote;
//   }
// }
