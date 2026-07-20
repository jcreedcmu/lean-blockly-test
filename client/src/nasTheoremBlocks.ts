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
    theoremName: 'even_sum_relation_counts',
    message: 'even_sum_relation_counts %1 %2 %3',
    args: [
      { name: 'SET', defaultValue: 'Finset α' },
      { name: 'SYMMETRY', defaultValue: 'symmetry' },
      { name: 'IRREFLEXIVITY', defaultValue: 'irreflexivity' },
    ],
    inline: false,
    tooltip:
      'On any finite set, if a relation is symmetric and nothing is related ' +
      'to itself, then the total number of related ordered pairs is even.\n\n' +
      'Technical statement:\n{α : Type} (s : Finset α) {R : α → α → Prop}\n' +
      '(symmetry : ∀ x y, R x y → R y x)\n' +
      '(irreflexivity : ∀ x, ¬ R x x) :\n' +
      'Even (∑ x ∈ s, {y ∈ s | R x y}.card)',
  },
  {
    type: 'term_nas_split_even_odd',
    theoremName: 'sum_eq_sum_even_add_sum_odd',
    message: 'sum_eq_sum_even_add_sum_odd %1 %2',
    args: [
      { name: 'SET', defaultValue: 'Finset α' },
      { name: 'VALUES', defaultValue: 'α → ℕ' },
    ],
    inline: false,
    tooltip:
      'Splits a finite natural-number sum into the contribution from even ' +
      'terms and the contribution from odd terms.\n\n' +
      'Technical statement:\n{α : Type} (s : Finset α) (f : α → ℕ) :\n' +
      '(∑ x ∈ s, f x) =\n' +
      '  (∑ x ∈ s.filter fun x => Even (f x), f x) +\n' +
      '  (∑ x ∈ s.filter fun x => Odd (f x), f x)',
  },
  {
    type: 'term_nas_even_sum_even_terms',
    theoremName: 'even_sum_even_terms',
    message: 'even_sum_even_terms %1 %2',
    args: [
      { name: 'SET', defaultValue: 'Finset α' },
      { name: 'VALUES', defaultValue: 'α → ℕ' },
    ],
    inline: false,
    tooltip:
      'The sum of those values in the set which are even is itself even.\n\n' +
      'Technical statement:\n{α : Type} (s : Finset α) (f : α → ℕ) :\n' +
      'Even (∑ x ∈ s.filter fun x => Even (f x), f x)',
  },
  {
    type: 'term_nas_even_right_of_split',
    theoremName: 'even_right_of_even_split',
    message: 'even_right_of_even_split %1 %2 %3',
    args: [
      { name: 'SPLIT', defaultValue: 'total = evenPart + oddPart' },
      { name: 'TOTAL_EVEN', defaultValue: 'Even total' },
      { name: 'LEFT_EVEN', defaultValue: 'Even evenPart' },
    ],
    inline: false,
    tooltip:
      'If total = left + right, and total and left are even, then right is even.\n\n' +
      'Technical statement:\n{total evenPart oddPart : ℕ}\n' +
      '(hsplit : total = evenPart + oddPart)\n' +
      '(htotal : Even total)\n' +
      '(hevenPart : Even evenPart) :\n' +
      'Even oddPart',
  },
  {
    type: 'term_nas_even_card_odd_terms',
    theoremName: 'even_card_of_even_sum_over_odd_terms',
    message: 'even_card_of_even_sum_over_odd_terms %1 %2',
    args: [
      { name: 'SET', defaultValue: 'Finset α' },
      { name: 'SUM_EVEN', defaultValue: 'Even odd-term sum' },
    ],
    inline: false,
    tooltip:
      'If the sum of all odd-valued terms is even, then the set of those ' +
      'terms has even cardinality.\n\n' +
      'Technical statement:\n{α : Type} (s : Finset α) {f : α → ℕ}\n' +
      '(hsum : Even (∑ x ∈ s.filter fun x => Odd (f x), f x)) :\n' +
      'Even (s.filter fun x => Odd (f x)).card',
  },
];

export const nasTheoremBlockSpecByType = new Map(
  nasTheoremBlockSpecs.map(spec => [spec.type, spec]),
);
