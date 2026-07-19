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
    type: 'term_nas_sum_card_fibers',
    theoremName: 'sum_card_fibers_eq_card_relation',
    message: 'fiber sum = relation cardinality  set %1  relation %2',
    args: [
      { name: 'SET', defaultValue: 'Party' },
      { name: 'RELATION', defaultValue: 'Handshake' },
    ],
    inline: true,
    tooltip:
      'The sum of the sizes of all relation fibers equals the number of related ordered pairs.',
  },
  {
    type: 'term_nas_even_symmetric_relation',
    theoremName: 'even_card_symmetric_irreflexive_relation',
    message:
      'symmetric irreflexive relation has even cardinality  set %1  relation %2  symmetry %3  irreflexivity %4',
    args: [
      { name: 'SET', defaultValue: 'Party' },
      { name: 'RELATION', defaultValue: 'Handshake' },
      { name: 'SYMMETRY', defaultValue: 'Handshake_symm' },
      { name: 'IRREFLEXIVITY', defaultValue: 'Handshake_irref' },
    ],
    inline: false,
    tooltip:
      'A symmetric, irreflexive relation on a finite set contains an even number of ordered pairs.',
  },
  {
    type: 'term_nas_split_even_odd',
    theoremName: 'sum_eq_sum_even_add_sum_odd',
    message: 'total = even-term sum + odd-term sum  set %1  values %2',
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
    message: 'sum of even terms is even  set %1  values %2',
    args: [
      { name: 'SET', defaultValue: 'Party' },
      { name: 'VALUES', defaultValue: 'HandshakeCount' },
    ],
    inline: true,
    tooltip:
      'The sum of those values in the set which are even is itself even.',
  },
  {
    type: 'term_nas_even_remainder',
    theoremName: 'even_right_of_even_add',
    message: 'even remainder  whole sum even %1  first part even %2',
    args: [
      { name: 'WHOLE_EVEN', defaultValue: 'NumTotHandshakes_is_Even' },
      { name: 'FIRST_EVEN', defaultValue: 'NumTotEven_is_Even' },
    ],
    inline: false,
    tooltip:
      'If a + b is even and a is even, then the remaining summand b is even.',
  },
  {
    type: 'term_nas_odd_sum_of_odd_card',
    theoremName: 'odd_sum_of_odd_terms_of_odd_card',
    message:
      'odd number of odd terms gives odd sum  set %1  values %2  all terms odd %3  number of terms odd %4',
    args: [
      { name: 'SET', defaultValue: 'OddPeople' },
      { name: 'VALUES', defaultValue: 'HandshakeCount' },
      { name: 'ALL_ODD', defaultValue: 'by simp [OddPeople]' },
      { name: 'CARD_ODD', defaultValue: 'NumOddHandshakes_is_Odd' },
    ],
    inline: false,
    tooltip:
      'If every term is odd and the finite set has odd cardinality, then the sum of its terms is odd.',
  },
];

export const nasTheoremBlockSpecByType = new Map(
  nasTheoremBlockSpecs.map(spec => [spec.type, spec]),
);
