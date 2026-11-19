// src: src/ast/seq/seq_lex_facet.cpp:175 | int c = cmp_const_chars(u, lh, rh);
function Less(a: seq<int>, b: seq<int>): bool
// synth: specification, invariant, or structural delimiter
  decreases |a| + |b|
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/seq/seq_lex_facet.cpp:175 | int c = cmp_const_chars(u, lh, rh);
  |b| > 0 && (|a| == 0 || a[0] < b[0] || (a[0] == b[0] && Less(a[1..], b[1..])))
// synth: specification, invariant, or structural delimiter
}
// src: src/ast/seq/seq_lex_facet.cpp:104 | bool lex_facet::simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep) {
method LexEntry(L0: seq<int>, R0: seq<int>, strict: bool) returns (discharged: bool, conflict: bool)
// synth: specification, invariant, or structural delimiter
  requires |L0| < 4294967295 && |R0| < 4294967295
// synth: specification, invariant, or structural delimiter
  ensures discharged == (Less(L0, R0) || (!strict && L0 == R0))
// synth: specification, invariant, or structural delimiter
  ensures conflict == !discharged
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/seq/seq_lex_facet.cpp:105 | conflict = false;
// src: src/ast/seq/seq_lex_facet.cpp:107 | bool changed = false;
  conflict, discharged := false, false;
// src: src/ast/seq/seq_lex_facet.cpp:114 | unsigned li = 0, ri = 0;
  var li, ri := 0, 0;
// src: src/ast/seq/seq_lex_facet.cpp:115 | while (li < L0.size() && ri < R0.size()) {
  while li < |L0| && ri < |R0|
// synth: specification, invariant, or structural delimiter
    invariant 0 <= li <= |L0| && 0 <= ri <= |R0| && li == ri
// synth: specification, invariant, or structural delimiter
    invariant Less(L0,R0) == Less(L0[li..],R0[ri..])
// synth: specification, invariant, or structural delimiter
    invariant (L0 == R0) == (L0[li..] == R0[ri..])
// synth: specification, invariant, or structural delimiter
    decreases |L0| - li
// synth: specification, invariant, or structural delimiter
  {
// src: src/ast/seq/seq_lex_facet.cpp:116 | expr* lh = L0.get(li);
    var lh := L0[li];
// src: src/ast/seq/seq_lex_facet.cpp:117 | expr* rh = R0.get(ri);
    var rh := R0[ri];
// src: src/ast/seq/seq_lex_facet.cpp:118 | bool tok_eq = (lh == rh);
// src: src/ast/seq/seq_lex_facet.cpp:119 | if (!tok_eq && is_const_char_unit(u, lh) && is_const_char_unit(u, rh))
// src: src/ast/seq/seq_lex_facet.cpp:120 | tok_eq = (cmp_const_chars(u, lh, rh) == 0);
    var tok_eq := lh == rh;
// src: src/ast/seq/seq_lex_facet.cpp:121 | if (!tok_eq)
    if !tok_eq {
// src: src/ast/seq/seq_lex_facet.cpp:122 | break;
      break;
// synth: specification, invariant, or structural delimiter
    }
// src: src/ast/seq/seq_lex_facet.cpp:123 | ++li; ++ri;
    li, ri := li + 1, ri + 1;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_lex_facet.cpp:125 | if (li > 0 || ri > 0) {
// src: src/ast/seq/seq_lex_facet.cpp:126 | expr_ref_vector newL(m), newR(m);
// src: src/ast/seq/seq_lex_facet.cpp:127 | newL.append(L0.size() - li, L0.data() + li);
// src: src/ast/seq/seq_lex_facet.cpp:129 | set_sides(i, newL, newR);
// src: src/ast/seq/seq_lex_facet.cpp:133 | expr_ref_vector const& L = m_lexs[i].m_lhs;
  var L := L0[li..];
// src: src/ast/seq/seq_lex_facet.cpp:125 | if (li > 0 || ri > 0) {
// src: src/ast/seq/seq_lex_facet.cpp:126 | expr_ref_vector newL(m), newR(m);
// src: src/ast/seq/seq_lex_facet.cpp:128 | newR.append(R0.size() - ri, R0.data() + ri);
// src: src/ast/seq/seq_lex_facet.cpp:129 | set_sides(i, newL, newR);
// src: src/ast/seq/seq_lex_facet.cpp:134 | expr_ref_vector const& R = m_lexs[i].m_rhs;
  var R := R0[ri..];
// src: src/ast/seq/seq_lex_facet.cpp:136 | if (L.empty() && R.empty()) {
  if |L| == 0 && |R| == 0 {
// src: src/ast/seq/seq_lex_facet.cpp:138 | if (lx.m_strict) {
    if strict {
// src: src/ast/seq/seq_lex_facet.cpp:139 | conflict = true;
// src: src/ast/seq/seq_lex_facet.cpp:140 | conflict_dep = lx.m_dep;
// src: src/ast/seq/seq_lex_facet.cpp:141 | return true;
      conflict := true; return;
// synth: specification, invariant, or structural delimiter
    }
// src: src/ast/seq/seq_lex_facet.cpp:143 | remove(i);
// src: src/ast/seq/seq_lex_facet.cpp:144 | changed = true;
// src: src/ast/seq/seq_lex_facet.cpp:145 | continue;
    discharged := true; return;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_lex_facet.cpp:148 | if (L.empty() && !R.empty()) {
// src: src/ast/seq/seq_lex_facet.cpp:149 | if (lx.m_strict && !contains_unit(u, R)) {
  if |L| == 0 && |R| > 0 {
// src: src/ast/seq/seq_lex_facet.cpp:154 | remove(i);
// src: src/ast/seq/seq_lex_facet.cpp:155 | changed = true;
// src: src/ast/seq/seq_lex_facet.cpp:156 | continue;
    discharged := true; return;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_lex_facet.cpp:159 | if (!L.empty() && R.empty()) {
// src: src/ast/seq/seq_lex_facet.cpp:160 | if (!lx.m_strict && !contains_unit(u, L)) {
  if |L| > 0 && |R| == 0 {
// src: src/ast/seq/seq_lex_facet.cpp:165 | conflict = true;
// src: src/ast/seq/seq_lex_facet.cpp:166 | conflict_dep = lx.m_dep;
// src: src/ast/seq/seq_lex_facet.cpp:167 | return true;
    conflict := true; return;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_lex_facet.cpp:171 | expr* lh = L.get(0);
  var lh := L[0];
// src: src/ast/seq/seq_lex_facet.cpp:172 | expr* rh = R.get(0);
  var rh := R[0];
// src: src/ast/seq/seq_lex_facet.cpp:173 | if (is_const_char_unit(u, lh) && is_const_char_unit(u, rh)) {
// src: src/ast/seq/seq_lex_facet.cpp:175 | int c = cmp_const_chars(u, lh, rh);
  var c := if lh < rh then -1 else if lh == rh then 0 else 1;
// synth: specification, invariant, or structural delimiter
  assert c != 0;
// src: src/ast/seq/seq_lex_facet.cpp:177 | if (c < 0) {
  if c < 0 {
// src: src/ast/seq/seq_lex_facet.cpp:179 | remove(i);
// src: src/ast/seq/seq_lex_facet.cpp:180 | changed = true;
// src: src/ast/seq/seq_lex_facet.cpp:181 | continue;
    discharged := true; return;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_lex_facet.cpp:183 | else {
// src: src/ast/seq/seq_lex_facet.cpp:185 | conflict = true;
  conflict := true;
// synth: specification, invariant, or structural delimiter
}
