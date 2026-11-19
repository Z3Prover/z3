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
method DischargeEntry(X: seq<int>, Y: seq<int>, Z: seq<int>, a: int, b: int) returns (discharged: bool)
// synth: specification, checked proof annotation, or structural delimiter
  requires a != b
// synth: specification, checked proof annotation, or structural delimiter
  requires |X| + 1 + |Y| < 2147483648
// synth: specification, checked proof annotation, or structural delimiter
  requires |X| + 1 + |Z| < 2147483648
// synth: concrete witness pin added independently of original applicability
  requires X == [97, 97]
// synth: concrete witness pin added independently of original applicability
  requires Y == [98]
// synth: concrete witness pin added independently of original applicability
  requires Z == []
// synth: concrete witness pin added independently of original applicability
  requires a == 97
// synth: concrete witness pin added independently of original applicability
  requires b == 98
// synth: mechanically selected complete property goal
  ensures !((!discharged || !WordContains(X + [a] + Y, X + [b] + Z)))
// synth: specification, checked proof annotation, or structural delimiter
{
// synth: expose a general concrete-offset infix witness without restricting any input
  assert X + [a] + Y == [a] + X + [b] + Z ==> 0 <= 1 <= |X + [a] + Y| && 1 + |X + [b] + Z| <= |X + [a] + Y| && (X + [a] + Y)[1..1+|X + [b] + Z|] == X + [b] + Z;
// synth: instantiate the existential at offset one under the proved equality condition
  assert X + [a] + Y == [a] + X + [b] + Z ==> WordContains(X + [a] + Y, X + [b] + Z);
// src: src/ast/seq/seq_ncontains_facet.cpp:264 | unsigned h_size = nc.m_haystack.size();
  var h_size := 3;
// src: src/ast/seq/seq_ncontains_facet.cpp:265 | unsigned n_size = nc.m_needle.size();
  var n_size := 3;
// src: src/ast/seq/seq_ncontains_facet.cpp:266 | bool has_window = h_size >= n_size;
  var has_window := h_size >= n_size;
// src: src/ast/seq/seq_ncontains_facet.cpp:267 | unsigned max_pos = has_window ? h_size - n_size : 0;
  var max_pos := if has_window then h_size - n_size else 0;
// src: src/ast/seq/seq_ncontains_facet.cpp:268 | bool found_match = false;
  var found_match := false;
// src: src/ast/seq/seq_ncontains_facet.cpp:269 | unsigned first_undef_pos = max_pos + 1; // sentinel: "no undef position seen"
  var first_undef_pos := max_pos + 1;
// src: src/ast/seq/seq_ncontains_facet.cpp:270 | for (unsigned pos = 0; has_window && pos <= max_pos; ++pos) {
  var pos := 0;
// src: src/ast/seq/seq_ncontains_facet.cpp:270 | for (unsigned pos = 0; has_window && pos <= max_pos; ++pos) {
  while has_window && pos <= max_pos
// synth: specification, checked proof annotation, or structural delimiter
    invariant 0 <= pos <= 1
// synth: specification, checked proof annotation, or structural delimiter
    invariant !found_match && first_undef_pos == 1
// synth: specification, checked proof annotation, or structural delimiter
    decreases 1 - pos
// synth: specification, checked proof annotation, or structural delimiter
  {
// src: src/ast/seq/seq_ncontains_facet.cpp:271 | lbool al = compare_alignment(u, m, nc.m_haystack, pos, nc.m_needle);
    var al := AlignmentEntry();
// src: src/ast/seq/seq_ncontains_facet.cpp:272 | if (al == l_true) {
    if al == 1 {
// src: src/ast/seq/seq_ncontains_facet.cpp:273 | found_match = true;
      found_match := true;
// src: src/ast/seq/seq_ncontains_facet.cpp:274 | break;
      break;
// synth: specification, checked proof annotation, or structural delimiter
    }
// src: src/ast/seq/seq_ncontains_facet.cpp:276 | if (al == l_undef && first_undef_pos > max_pos) {
    if al == 0 && first_undef_pos > max_pos {
// src: src/ast/seq/seq_ncontains_facet.cpp:277 | first_undef_pos = pos;
      first_undef_pos := pos;
// synth: specification, checked proof annotation, or structural delimiter
    }
// src: src/ast/seq/seq_ncontains_facet.cpp:270 | for (unsigned pos = 0; has_window && pos <= max_pos; ++pos) {
    pos := pos + 1;
// synth: specification, checked proof annotation, or structural delimiter
  }
// src: src/ast/seq/seq_ncontains_facet.cpp:281 | if (found_match) {
  if found_match {
// src: src/ast/seq/seq_ncontains_facet.cpp:282 | n.set_conflict(stx::br_plugin_base, nc.m_dep);
// src: src/ast/seq/seq_ncontains_facet.cpp:283 | return stx::simplify_result::conflict;
    discharged := false; return;
// synth: specification, checked proof annotation, or structural delimiter
  }
// src: src/ast/seq/seq_ncontains_facet.cpp:285 | if (has_window && first_undef_pos > max_pos) {
  if has_window && first_undef_pos > max_pos {
// src: src/ast/seq/seq_ncontains_facet.cpp:288 | f.remove(head);
    discharged := true; return;
// synth: specification, checked proof annotation, or structural delimiter
  }
// src: src/ast/seq/seq_ncontains_facet.cpp:293 | if (has_window && first_undef_pos > 0) {
  discharged := false;
// synth: specification, checked proof annotation, or structural delimiter
}

method NfvDomain0()
{
  var out0 := DischargeEntry([97, 97], [98], [], 97, 98);
}
