import { useCallback, useEffect, useRef, useState, JSX } from 'react'
import * as React from 'react'
import * as blockly from 'blockly'

const toolbox = {
  'kind': 'flyoutToolbox',
  'contents': [
    {
      'kind': 'block',
      'type': 'tactic_proof'
    },
    {
      'kind': 'block',
      'type': 'intro'
    },
    {
      'kind': 'block',
      'type': 'exact'
    },
    {
      'kind': 'block',
      'type': 'number'
    }
  ]
}

function useBlockly(ref: React.RefObject<HTMLDivElement>) {
  React.useEffect(() => {

    if (!ref.current) {
      return;
    }

    if ((ref.current as any).alreadyInjected) {
      console.log('already injected');
      return;
    }

    (ref.current as any).alreadyInjected = true;


    blockly.common.defineBlocksWithJsonArray([
      {
        "type": "tactic_proof",
        "tooltip": "dfgdfg",
        "helpUrl": "dfgdfgfggf",
        "message0": "Proof by %1",
        "args0": [
          {
            "type": "input_statement",
            "name": "BODY"
          }
        ],
        "output": null,
        "colour": 120
      },
      {
        "type": "intro",
        "tooltip": "dfgdfg",
        "helpUrl": "dfgdfgfggf",
        "message0": "%1 %2 %3",
        "args0": [
          {
            "type": "field_label_serializable",
            "text": "intro",
            "name": "LABEL"
          },
          {
            "type": "field_variable",
            "name": "VAR",
            "variable": "var"
          },
          {
            "type": "input_dummy",
            "name": "BODY"
          }
        ],
        "previousStatement": null,
        "nextStatement": null,
        "colour": 255
      },
      {
        "type": "exact",
        "tooltip": "dfgdfg",
        "helpUrl": "dfgdfgfggf",
        "message0": "%1 %2",
        "args0": [
          {
            "type": "field_label_serializable",
            "text": "exact",
            "name": "LABEL"
          },
          {
            "type": "input_value",
            "name": "BODY",
            "align": "RIGHT"
          }
        ],
        "previousStatement": null,
        "colour": 45
      },
      {
        "type": "number",
        "tooltip": "dfgdfg",
        "helpUrl": "dfgdfgfggf",
        "message0": "%1 %2 %3",
        "args0": [
          {
            "type": "field_label_serializable",
            "text": "number",
            "name": "LABEL"
          },
          {
            "type": "field_number",
            "name": "NAME",
            "value": 0
          },
          {
            "type": "input_dummy",
            "name": "BODY",
            "align": "RIGHT"
          }
        ],
        "output": null,
        "colour": 45
      }
    ]);

    const toolbox: blockly.utils.toolbox.ToolboxDefinition = {
      "kind": "categoryToolbox",
      "contents": [
        {
          "kind": "category",
          "name": "Control",
          "contents": [
            {
              'kind': 'block',
              'type': 'tactic_proof'
            },
            {
              'kind': 'block',
              'type': 'intro'
            },
            {
              'kind': 'block',
              'type': 'exact'
            }
          ]
        },
        {
          "kind": "category",
          "name": "Number",
          "contents": [
            {
              "kind": "block",
              "type": "number"
            }
          ]
        }
      ]
    };

    const leanGenerator = new blockly.CodeGenerator('Lean');

    leanGenerator.forBlock['number'] = (block, generator) => { return 'number'; }
    leanGenerator.forBlock['intro'] = (block, generator) => { return 'intro'; }
    leanGenerator.forBlock['exact'] = (block, generator) => { return 'exact'; }
    leanGenerator.forBlock['tactic_proof'] = (block, generator) => {
      console.log('kids', block.getChildren(true));
      console.log('fields', [...block.getFields()]);
      return `tactic_proof[...]`;
    }

    //    const toolbox: blockly.utils.toolbox.ToolboxDefinition = { kind: 'categoryToolbox', contents: [item] };
    const newWorkspace = blockly.inject(ref.current, {
      toolbox: toolbox,
      scrollbars: false,
    });
    (window as any).debug = () => {
      console.log(leanGenerator.workspaceToCode(newWorkspace));
    }
  });
}

export function Blockly(props: { style: React.CSSProperties }): JSX.Element {
  const blocklyRef = React.useRef(null);
  const foo = useBlockly(blocklyRef);
  return <div style={props.style} ref={blocklyRef}></div>;
}
