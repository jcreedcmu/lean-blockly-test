export type NasTheoremArgument = {
  name: string;
  defaultValue: string;
};

export type NasTheoremBlockSpec = {
  type: string;
  theoremName: string;
  message: string;
  args: NasTheoremArgument[];
  inline: boolean;
  tooltip: string;
};

/**
 * Hard-coded theorem-expression blocks for the standalone NAS presentation
 * experiment. These intentionally bypass the generated theorem inventory.
 */
export const nasTheoremBlockSpecs: NasTheoremBlockSpec[] = [
  {
    type: 'term_nas_even_total_relation_counts',
    theoremName: 'even_sum_relation_fibers',
    message:
      'even_sum_relation_fibers  set %1  symmetry %2  irreflexivity %3',
    args: [
      { name: 'SET', defaultValue: 'Party' },
      { name: 'SYMMETRY', defaultValue: 'Handshake_symm' },
      { name: 'IRREFLEXIVITY', defaultValue: 'Handshake_irref' },
    ],
    inline: true,
    tooltip:
      'For a symmetric, irreflexive relation, the sum of the sizes of its finite-set fibers is even.',
  },
  {
    type: 'term_nas_split_even_odd',
    theoremName: 'sum_eq_sum_even_add_sum_odd',
    message: 'sum_eq_sum_even_add_sum_odd  set %1  values %2',
    args: [
      { name: 'SET', defaultValue: 'Party' },
      { name: 'VALUES', defaultValue: 'HandshakeCount' },
    ],
    inline: true,
    tooltip:
      'Splits a finite natural-number sum into the contribution from even terms and the contribution from odd terms.',
  },
  {
    type: 'term_nas_even_sum_even_terms',
    theoremName: 'even_sum_even_terms',
    message: 'even_sum_even_terms  set %1  values %2',
    args: [
      { name: 'SET', defaultValue: 'Party' },
      { name: 'VALUES', defaultValue: 'HandshakeCount' },
    ],
    inline: true,
    tooltip:
      'The sum of those values in the set which are even is itself even.',
  },
  {
    type: 'term_nas_even_right_of_split',
    theoremName: 'even_right_of_even_split',
    message:
      'even_right_of_even_split  split %1  total even %2  left side even %3',
    args: [
      { name: 'SPLIT', defaultValue: 'NumTot_split' },
      { name: 'TOTAL_EVEN', defaultValue: 'NumTotHandshakes_is_Even' },
      { name: 'LEFT_EVEN', defaultValue: 'NumTotEven_is_Even' },
    ],
    inline: false,
    tooltip:
      'If total = left + right, and total and left are even, then right is even.',
  },
  {
    type: 'term_nas_even_card_odd_terms',
    theoremName: 'even_card_of_even_sum_over_odd_terms',
    message: 'even_card_of_even_sum_over_odd_terms  set %1  values %2  odd-term sum even %3',
    args: [
      { name: 'SET', defaultValue: 'Party' },
      { name: 'VALUES', defaultValue: 'HandshakeCount' },
      { name: 'SUM_EVEN', defaultValue: 'NumTotOdd_is_Even' },
    ],
    inline: false,
    tooltip:
      'If the sum of all odd-valued terms is even, then the set of those terms has even cardinality.',
  },
];

export const nasTheoremBlockSpecByType = new Map(
  nasTheoremBlockSpecs.map(spec => [spec.type, spec]),
);
