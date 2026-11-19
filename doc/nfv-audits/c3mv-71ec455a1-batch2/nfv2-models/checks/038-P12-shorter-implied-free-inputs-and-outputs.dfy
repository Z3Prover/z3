// src: src/ast/seq/seq_replace_all_facet.cpp:225 | if (c >= 2 * p.length() + 2)
function Unsigned32(value: int): int
// synth: specification, checked proof annotation, or structural delimiter
  requires 0 <= value
// synth: specification, checked proof annotation, or structural delimiter
  ensures 0 <= Unsigned32(value) < 4294967296
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/ast/seq/seq_replace_all_facet.cpp:225 | if (c >= 2 * p.length() + 2)
  value % 4294967296
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/ast/seq/seq_replace_all_facet.cpp:215 | bool replace_all_split::apply_case(eq_tree::node& n, unsigned idx, unsigned c, eq_tree::edge& out) {
// src: src/ast/seq/seq_replace_all_facet.cpp:215 | bool replace_all_split::apply_case(eq_tree::node& n, unsigned idx, unsigned c, eq_tree::edge& out) {
lemma NfvShorterImplication(pattern_length: int, case_number: int, admitted: bool)
// synth: original applicability or entire positive property as implication premise
  requires 1 <= pattern_length <= 4294967295
// synth: original applicability or entire positive property as implication premise
  requires 1 <= case_number <= 4294967295
// synth: original applicability or entire positive property as implication premise
  requires admitted == (case_number < 2 * pattern_length + 2)
// synth: proposed strictly shorter consequence with all inputs and outputs free
  ensures case_number >= 2 * pattern_length + 2 || admitted
// synth: proof body
{
// synth: proof body
}
