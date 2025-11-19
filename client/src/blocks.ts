import * as blockly from 'blockly';

/*
Adapted from https://github.com/aneilmac/blockly-plugin-lean under the Apache 2.0 license
*/

export function defineBlocks() {
  defineLemma();
  defineProposition();
  defineTactics();
}

function defineLemma() {
  blockly.defineBlocksWithJsonArray([
    {
      'type': 'lemma',
      'message0': 'theorem %1 %2 variables %3 %4 %5 := %6 begin %7 %8 end',
      'args0': [
        {
          'type': 'field_input',
          'name': 'THEOREM_NAME',
          'text': 'example1',
        },
        {
          'type': 'input_dummy',
        },
        {
          'type': 'input_dummy',
        },
        {
          'type': 'input_statement',
          'name': 'VARIABLES',
          'check': 'prop_declaration',
        },
        {
          'type': 'field_input',
          'name': 'THEOREM_DECLARATION',
          'text': 'default',
        },
        {
          'type': 'input_dummy',
          'align': 'CENTRE',
        },
        {
          'type': 'input_dummy',
        },
        {
          'type': 'input_statement',
          'name': 'LEMMA_PROOF',
          'check': 'tactic',
        },
      ],
      'inputsInline': false,
      'style': 'procedure_blocks',
      'tooltip': '',
      'helpUrl': '',
    },
  ]);
}

function defineProposition() {
  blockly.defineBlocksWithJsonArray([
    {
      'type': 'prop_declaration',
      'message0': '%1 : %2',
      'args0': [
        {
          'type': 'field_input',
          'name': 'VARIABLE_DECL',
          'text': 'default',
        },
        {
          'type': 'field_input',
          'name': 'VARIABLE_DEF',
          'text': 'default',
        },
      ],
      'previousStatement': 'prop_declaration',
      'nextStatement': 'prop_declaration',
      'style': 'variable_blocks',
      'tooltip': '',
      'helpUrl': '',
    },
    {
      'type': 'prop',
      'message0': '%1',
      'args0': [
        {
          'type': 'field_input',
          'name': 'PROP_NAME',
          'text': 'h',
        },
      ],
      'output': 'proposition',
      'style': 'variable_blocks',
      'tooltip': '',
      'helpUrl': '',
    },
    {
      'type': 'prop_dynamic',
      'message0': '%1',
      'args0': [
        {
          'type': 'field_input',
          'name': 'PROP_NAME',
          'text': 'h',
        },
      ],
      'output': 'proposition',
      'style': 'variable_dynamic_blocks',
      'tooltip': '',
      'helpUrl': '',
    },
  ]);
}

function defineTactics() {
  blockly.defineBlocksWithJsonArray([
    {
      'type': 'tactic_refl',
      'message0': 'reflexivity',
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'tooltip': 'refl proves goals of the form X = X.',
      'helpUrl': 'refl',
      'style': 'logic_blocks',
    },
    {
      'type': 'tactic_rw',
      'message0': 'rewrite %1 %2',
      'args0': [
        {
          'type': 'field_dropdown',
          'name': 'DIRECTION_TYPE',
          'options': [
            [
              '→',
              'RIGHT',
            ],
            [
              '←',
              'LEFT',
            ],
          ],
        },
        {
          'type': 'input_value',
          'name': 'REWRITE_SOURCE',
          'check': 'proposition',
          'align': 'CENTRE',
        },
      ],
      'inputsInline': false,
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'style': 'logic_blocks',
      'tooltip': 'rw',
      'helpUrl': 'rw',
    },
    {
      'type': 'tactic_rw_at',
      'message0': 'rewrite %1 at %2',
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'args0': [
        {
          'type': 'input_value',
          'name': 'REWRITE_SOURCE',
          'check': 'proposition',
        },
        {
          'type': 'input_value',
          'name': 'REWRITE_TARGET',
          'check': 'proposition',
        },
      ],
      'inputsInline': false,
      'style': 'logic_blocks',
      'tooltip': 'rw_at',
      'helpUrl': 'rw_at',
    },
    {
      'type': 'tactic_sorry',
      'message0': 'sorry',
      'previousStatement': 'tactic',
      'colour': 330,
      'tooltip': 'but are you really sorry?',
      'helpUrl': 'refl',
    },
    {
      'type': 'tactic_induction',
      'message0': 'induction %1',
      'args0': [
        {
          'type': 'input_value',
          'name': 'EXPR',
        },
      ],
      'inputsInline': false,
      'previousStatement': 'tactic',
      'nextStatement': 'tactic',
      'style': 'logic_blocks',
      'tooltip': '',
      'helpUrl': '',
    },
  ]);
}
