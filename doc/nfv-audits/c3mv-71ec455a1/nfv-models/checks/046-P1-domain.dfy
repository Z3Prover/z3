// src: src/ast/seq/seq_ncontains_facet.cpp:264 | unsigned h_size = nc.m_haystack.size();
function ContainsWord(h: seq<int>, n: seq<int>): bool
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/seq/seq_ncontains_facet.cpp:264 | unsigned h_size = nc.m_haystack.size();
  exists i :: 0 <= i <= |h| && i + |n| <= |h| && h[i..i+|n|] == n
// synth: specification, invariant, or structural delimiter
}
// src: src/ast/seq/seq_ncontains_facet.cpp:296 | tail.append(h_size - first_undef_pos, nc.m_haystack.data() + first_undef_pos);
function Flatten(words: seq<seq<int>>): seq<int>
// synth: specification, invariant, or structural delimiter
  decreases |words|
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/seq/seq_ncontains_facet.cpp:296 | tail.append(h_size - first_undef_pos, nc.m_haystack.data() + first_undef_pos);
  if |words| == 0 then [] else words[0] + Flatten(words[1..])
// synth: specification, invariant, or structural delimiter
}
// src: src/ast/seq/seq_ncontains_facet.cpp:128 | static lbool compare_alignment(seq_util& u, ast_manager& m, expr_ref_vector const& h, unsigned pos, expr_ref_vector const& n) {
method Alignment(pos: int) returns (r: int)
// synth: specification, invariant, or structural delimiter
  requires 0 <= pos <= 1
// synth: specification, invariant, or structural delimiter
  ensures r == (if pos == 0 then -1 else 0)
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/seq/seq_ncontains_facet.cpp:131 | expr* ht = h.get(pos + k);
  var h: seq<int> := [0, 1, 2];
// src: src/ast/seq/seq_ncontains_facet.cpp:132 | expr* nt = n.get(k);
  var n: seq<int> := [0, 3];
// src: src/ast/seq/seq_ncontains_facet.cpp:135 | if (!u.str.is_unit(ht) || !u.str.is_unit(nt))
  var unit: seq<bool> := [false, true, false, true];
// src: src/ast/seq/seq_ncontains_facet.cpp:129 | bool undef = false;
  var undef := false;
// src: src/ast/seq/seq_ncontains_facet.cpp:130 | for (unsigned k = 0; k < n.size(); ++k) {
  var k := 0;
// src: src/ast/seq/seq_ncontains_facet.cpp:130 | for (unsigned k = 0; k < n.size(); ++k) {
  while k < |n|
// synth: specification, invariant, or structural delimiter
    invariant 0 <= k <= 1
// synth: specification, invariant, or structural delimiter
    invariant !undef
// synth: specification, invariant, or structural delimiter
    invariant pos == 1 ==> k == 0
// synth: specification, invariant, or structural delimiter
    decreases |n| - k
// synth: specification, invariant, or structural delimiter
  {
// src: src/ast/seq/seq_ncontains_facet.cpp:131 | expr* ht = h.get(pos + k);
    var ht := h[pos + k];
// src: src/ast/seq/seq_ncontains_facet.cpp:132 | expr* nt = n.get(k);
    var nt := n[k];
// src: src/ast/seq/seq_ncontains_facet.cpp:133 | if (ht == nt)
    if ht == nt {
// src: src/ast/seq/seq_ncontains_facet.cpp:134 | continue; // identical token (same variable, or same interned constant)
      k := k + 1;
// src: src/ast/seq/seq_ncontains_facet.cpp:134 | continue; // identical token (same variable, or same interned constant)
      continue;
// synth: specification, invariant, or structural delimiter
    }
// src: src/ast/seq/seq_ncontains_facet.cpp:135 | if (!u.str.is_unit(ht) || !u.str.is_unit(nt))
    if !unit[ht] || !unit[nt] {
// src: src/ast/seq/seq_ncontains_facet.cpp:136 | return l_undef; // unknown length: later tokens are not aligned
      r := 0; return;
// synth: specification, invariant, or structural delimiter
    }
// src: src/ast/seq/seq_ncontains_facet.cpp:137 | if (m.are_distinct(ht, nt))
    if ht != nt {
// src: src/ast/seq/seq_ncontains_facet.cpp:138 | return l_false; // distinct resolved constants: determined mismatch
      r := -1; return;
// synth: specification, invariant, or structural delimiter
    }
// src: src/ast/seq/seq_ncontains_facet.cpp:139 | undef = true;
    undef := true;
// src: src/ast/seq/seq_ncontains_facet.cpp:130 | for (unsigned k = 0; k < n.size(); ++k) {
    k := k + 1;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_ncontains_facet.cpp:141 | return undef ? l_undef : l_true;
  r := if undef then 0 else 1;
// synth: specification, invariant, or structural delimiter
}
// src: src/ast/seq/seq_ncontains_facet.cpp:213 | auto const& nc = f.ncontains()[i];
method PruningEntry(x: seq<int>, y: seq<int>, a: int, b: int) returns (before: bool, after: bool, cut: int)
// synth: specification, invariant, or structural delimiter
  requires a != b
// synth: specification, invariant, or structural delimiter
  requires |x| < 2147483647 && |y| < 2147483647
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/seq/seq_ncontains_facet.cpp:264 | unsigned h_size = nc.m_haystack.size();
  var words: seq<seq<int>> := [x, [a], y];
// src: src/ast/seq/seq_ncontains_facet.cpp:265 | unsigned n_size = nc.m_needle.size();
  var needle := x + [b];
// src: src/ast/seq/seq_ncontains_facet.cpp:264 | unsigned h_size = nc.m_haystack.size();
  var h_size := |words|;
// src: src/ast/seq/seq_ncontains_facet.cpp:265 | unsigned n_size = nc.m_needle.size();
  var n_size := 2;
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
// synth: specification, invariant, or structural delimiter
    invariant 0 <= pos <= 2
// synth: specification, invariant, or structural delimiter
    invariant !found_match
// synth: specification, invariant, or structural delimiter
    invariant first_undef_pos == (if pos < 2 then 2 else 1)
// synth: specification, invariant, or structural delimiter
    decreases 2 - pos
// synth: specification, invariant, or structural delimiter
  {
// src: src/ast/seq/seq_ncontains_facet.cpp:271 | lbool al = compare_alignment(u, m, nc.m_haystack, pos, nc.m_needle);
    var al := Alignment(pos);
// src: src/ast/seq/seq_ncontains_facet.cpp:272 | if (al == l_true) {
    if al == 1 {
// src: src/ast/seq/seq_ncontains_facet.cpp:273 | found_match = true;
      found_match := true;
// src: src/ast/seq/seq_ncontains_facet.cpp:274 | break;
      break;
// synth: specification, invariant, or structural delimiter
    }
// src: src/ast/seq/seq_ncontains_facet.cpp:276 | if (al == l_undef && first_undef_pos > max_pos) {
    if al == 0 && first_undef_pos > max_pos {
// src: src/ast/seq/seq_ncontains_facet.cpp:277 | first_undef_pos = pos;
      first_undef_pos := pos;
// synth: specification, invariant, or structural delimiter
    }
// src: src/ast/seq/seq_ncontains_facet.cpp:270 | for (unsigned pos = 0; has_window && pos <= max_pos; ++pos) {
    pos := pos + 1;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_ncontains_facet.cpp:264 | unsigned h_size = nc.m_haystack.size();
  before := ContainsWord(Flatten(words), needle);
// synth: specification, invariant, or structural delimiter
  assert x == [97,97] && y == [98] && a == 97 && b == 98 ==> Flatten(words) == [97,97,97,98] && needle == [97,97,98];
// synth: specification, invariant, or structural delimiter
  assert x == [97,97] && y == [98] && a == 97 && b == 98 ==> Flatten(words)[1..4] == needle;
// src: src/ast/seq/seq_ncontains_facet.cpp:293 | if (has_window && first_undef_pos > 0) {
  cut := 0;
// src: src/ast/seq/seq_ncontains_facet.cpp:281 | if (found_match) {
  if found_match {
// src: src/ast/seq/seq_ncontains_facet.cpp:282 | n.set_conflict(stx::br_plugin_base, nc.m_dep);
// src: src/ast/seq/seq_ncontains_facet.cpp:283 | return stx::simplify_result::conflict;
    after, cut := true, -1; return;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_ncontains_facet.cpp:285 | if (has_window && first_undef_pos > max_pos) {
  if has_window && first_undef_pos > max_pos {
// src: src/ast/seq/seq_ncontains_facet.cpp:288 | f.remove(head);
// src: src/ast/seq/seq_ncontains_facet.cpp:289 | changed = true;
// src: src/ast/seq/seq_ncontains_facet.cpp:290 | ++head;
// src: src/ast/seq/seq_ncontains_facet.cpp:291 | continue;
    after, cut := false, h_size; return;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_ncontains_facet.cpp:293 | if (has_window && first_undef_pos > 0) {
  if has_window && first_undef_pos > 0 {
// src: src/ast/seq/seq_ncontains_facet.cpp:295 | expr_ref_vector tail(m);
// src: src/ast/seq/seq_ncontains_facet.cpp:296 | tail.append(h_size - first_undef_pos, nc.m_haystack.data() + first_undef_pos);
    var tail := words[first_undef_pos..];
// src: src/ast/seq/seq_ncontains_facet.cpp:297 | f.replace_with_tail(head, tail);
    words := tail;
// src: src/ast/seq/seq_ncontains_facet.cpp:298 | changed = true;
// src: src/ast/seq/seq_ncontains_facet.cpp:299 | ++head; // the shortened replacement, appended past `head`,
// src: src/ast/seq/seq_ncontains_facet.cpp:301 | continue;
    cut := first_undef_pos;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_ncontains_facet.cpp:297 | f.replace_with_tail(head, tail);
  after := ContainsWord(Flatten(words), needle);
// synth: specification, invariant, or structural delimiter
}

method NfvDomain0()
{
  var out0, out1, out2 := PruningEntry([97, 97], [98], 97, 98);
}
