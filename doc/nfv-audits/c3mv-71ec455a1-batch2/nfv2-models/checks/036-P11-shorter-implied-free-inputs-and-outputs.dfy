// src: src/ast/seq/seq_ncontains_facet.cpp:154 | break;
function WordContains(h: seq<int>, n: seq<int>): bool
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/ast/seq/seq_ncontains_facet.cpp:154 | break;
  exists i :: 0 <= i <= |h| && i + |n| <= |h| && h[i..i+|n|] == n
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/ast/seq/seq_ncontains_facet.cpp:128 | static lbool compare_alignment(seq_util& u, ast_manager& m, expr_ref_vector const& h, unsigned pos, expr_ref_vector const& n) {
method AlignmentEntry() returns (verdict: int)
// synth: specification, checked proof annotation, or structural delimiter
  ensures verdict == -1
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/ast/seq/seq_ncontains_facet.cpp:131 | expr* ht = h.get(pos + k);
  var h := [0,3,1];
// src: src/ast/seq/seq_ncontains_facet.cpp:132 | expr* nt = n.get(k);
  var n := [0,4,2];
// src: src/ast/seq/seq_ncontains_facet.cpp:135 | if (!u.str.is_unit(ht) || !u.str.is_unit(nt))
  var unit := [false,false,false,true,true];
// src: src/ast/seq/seq_ncontains_facet.cpp:129 | bool undef = false;
  var unknown := false;
// src: src/ast/seq/seq_ncontains_facet.cpp:130 | for (unsigned k = 0; k < n.size(); ++k) {
  var k := 0;
// src: src/ast/seq/seq_ncontains_facet.cpp:130 | for (unsigned k = 0; k < n.size(); ++k) {
  while k < |n|
// synth: specification, checked proof annotation, or structural delimiter
    invariant 0 <= k <= 1
// synth: specification, checked proof annotation, or structural delimiter
    invariant !unknown
// synth: specification, checked proof annotation, or structural delimiter
    decreases |n| - k
// synth: specification, checked proof annotation, or structural delimiter
  {
// src: src/ast/seq/seq_ncontains_facet.cpp:131 | expr* ht = h.get(pos + k);
    var ht := h[k];
// src: src/ast/seq/seq_ncontains_facet.cpp:132 | expr* nt = n.get(k);
    var nt := n[k];
// src: src/ast/seq/seq_ncontains_facet.cpp:133 | if (ht == nt)
    if ht == nt {
// src: src/ast/seq/seq_ncontains_facet.cpp:134 | continue; // identical token (same variable, or same interned constant)
      k := k + 1;
// src: src/ast/seq/seq_ncontains_facet.cpp:134 | continue; // identical token (same variable, or same interned constant)
      continue;
// synth: specification, checked proof annotation, or structural delimiter
    }
// src: src/ast/seq/seq_ncontains_facet.cpp:135 | if (!u.str.is_unit(ht) || !u.str.is_unit(nt))
    if !unit[ht] || !unit[nt] {
// src: src/ast/seq/seq_ncontains_facet.cpp:136 | return l_undef; // unknown length: later tokens are not aligned
      verdict := 0; return;
// synth: specification, checked proof annotation, or structural delimiter
    }
// src: src/ast/seq/seq_ncontains_facet.cpp:137 | if (m.are_distinct(ht, nt))
    if ht != nt {
// src: src/ast/seq/seq_ncontains_facet.cpp:138 | return l_false; // distinct resolved constants: determined mismatch
      verdict := -1; return;
// synth: specification, checked proof annotation, or structural delimiter
    }
// src: src/ast/seq/seq_ncontains_facet.cpp:139 | undef = true;
    unknown := true;
// src: src/ast/seq/seq_ncontains_facet.cpp:130 | for (unsigned k = 0; k < n.size(); ++k) {
    k := k + 1;
// synth: specification, checked proof annotation, or structural delimiter
  }
// src: src/ast/seq/seq_ncontains_facet.cpp:141 | return undef ? l_undef : l_true;
  verdict := if unknown then 0 else 1;
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/ast/seq/seq_ncontains_facet.cpp:201 | stx::simplify_result ncontains_propagation::propagate(eq_tree::node& n) {
// src: src/ast/seq/seq_ncontains_facet.cpp:201 | stx::simplify_result ncontains_propagation::propagate(eq_tree::node& n) {
lemma NfvShorterImplication(X: seq<int>, Y: seq<int>, Z: seq<int>, a: int, b: int, discharged: bool)
// synth: original applicability or entire positive property as implication premise
  requires a != b
// synth: original applicability or entire positive property as implication premise
  requires |X| + 1 + |Y| < 2147483648
// synth: original applicability or entire positive property as implication premise
  requires |X| + 1 + |Z| < 2147483648
// synth: original applicability or entire positive property as implication premise
  requires !discharged || !WordContains(X + [a] + Y, X + [b] + Z)
// synth: proposed strictly shorter consequence with all inputs and outputs free
  ensures !discharged || X + [a] + Y != [a] + X + [b] + Z
// synth: proof body
{
// synth: exhibit the offset-one infix under equality
  assert X + [a] + Y == [a] + X + [b] + Z ==> 0 <= 1 <= |X + [a] + Y| && 1 + |X + [b] + Z| <= |X + [a] + Y| && (X + [a] + Y)[1..1+|X + [b] + Z|] == X + [b] + Z;
// synth: instantiate the existential
  assert X + [a] + Y == [a] + X + [b] + Z ==> WordContains(X + [a] + Y, X + [b] + Z);
// synth: proof body
}
