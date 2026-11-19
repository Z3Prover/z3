// src: src/ast/seq/seq_eq_facet.cpp:989 | bool deq_facet::simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep) {
method CancellationEntry(left: seq<int>, right: seq<int>) returns (L: seq<int>, R: seq<int>, conflict: bool)
// synth: specification, invariant, or structural delimiter
  requires |left| < 4294967295 && |right| < 4294967295
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/seq/seq_eq_facet.cpp:1017 | unsigned li = 0, ri = 0;
  var li, ri := 0, 0;
// src: src/ast/seq/seq_eq_facet.cpp:1018 | while (li < L.size() && ri < R.size() && L.get(li) == R.get(ri)) {
  while li < |left| && ri < |right| && left[li] == right[ri]
// synth: specification, invariant, or structural delimiter
    invariant 0 <= li <= |left| && 0 <= ri <= |right| && li == ri
// synth: specification, invariant, or structural delimiter
    invariant left[..li] == right[..ri]
// synth: specification, invariant, or structural delimiter
    invariant (left == right) == (left[li..] == right[ri..])
// synth: specification, invariant, or structural delimiter
    decreases |left| - li
// synth: specification, invariant, or structural delimiter
  {
// src: src/ast/seq/seq_eq_facet.cpp:1019 | ++li; ++ri;
    li, ri := li + 1, ri + 1;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_eq_facet.cpp:1021 | unsigned le = L.size(), re = R.size();
  var le, re := |left|, |right|;
// src: src/ast/seq/seq_eq_facet.cpp:1022 | while (li < le && ri < re && L.get(le - 1) == R.get(re - 1)) {
  while li < le && ri < re && left[le - 1] == right[re - 1]
// synth: specification, invariant, or structural delimiter
    invariant li <= le <= |left| && ri <= re <= |right|
// synth: specification, invariant, or structural delimiter
    invariant left[le..] == right[re..]
// synth: specification, invariant, or structural delimiter
    invariant (left == right) == (left[li..le] == right[ri..re])
// synth: specification, invariant, or structural delimiter
    decreases le - li
// synth: specification, invariant, or structural delimiter
  {
// src: src/ast/seq/seq_eq_facet.cpp:1023 | --le; --re;
    le, re := le - 1, re - 1;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_eq_facet.cpp:1025 | if (li > 0 || ri > 0 || le < L.size() || re < R.size()) {
  L, R := left, right;
// src: src/ast/seq/seq_eq_facet.cpp:1025 | if (li > 0 || ri > 0 || le < L.size() || re < R.size()) {
  if li > 0 || ri > 0 || le < |left| || re < |right| {
// src: src/ast/seq/seq_eq_facet.cpp:1026 | expr_ref_vector newL(m), newR(m);
// src: src/ast/seq/seq_eq_facet.cpp:1027 | newL.append(le - li, L.data() + li);
    var newL := left[li..le];
// src: src/ast/seq/seq_eq_facet.cpp:1026 | expr_ref_vector newL(m), newR(m);
// src: src/ast/seq/seq_eq_facet.cpp:1028 | newR.append(re - ri, R.data() + ri);
    var newR := right[ri..re];
// src: src/ast/seq/seq_eq_facet.cpp:1029 | m_trail.push(vector_field_trail<disequation, expr_ref_vector>(m_diseqs, i, &disequation::m_lhs));
// src: src/ast/seq/seq_eq_facet.cpp:1031 | L = std::move(newL);
    L := newL;
// src: src/ast/seq/seq_eq_facet.cpp:1030 | m_trail.push(vector_field_trail<disequation, expr_ref_vector>(m_diseqs, i, &disequation::m_rhs));
// src: src/ast/seq/seq_eq_facet.cpp:1032 | R = std::move(newR);
    R := newR;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_eq_facet.cpp:1036 | if (L.empty() && R.empty()) {
// src: src/ast/seq/seq_eq_facet.cpp:1038 | conflict = true;
  conflict := |L| == 0 && |R| == 0;
// synth: specification, invariant, or structural delimiter
}
