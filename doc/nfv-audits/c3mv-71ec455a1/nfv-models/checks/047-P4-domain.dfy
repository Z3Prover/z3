// src: src/ast/seq/seq_replace_all_facet.cpp:120 | static lbool match_at(seq_util& u, expr_ref_vector const& input, unsigned pos, zstring const& p) {
method MatchEntry(input: seq<int>, constant: seq<bool>, pos: int, p: seq<int>) returns (r: int)
// synth: specification, invariant, or structural delimiter
  requires |constant| == |input|
// synth: specification, invariant, or structural delimiter
  requires 0 <= pos <= |input|
// synth: specification, invariant, or structural delimiter
  requires |input| < 2147483647 && 0 < |p| < 2147483647
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/seq/seq_replace_all_facet.cpp:121 | for (unsigned k = 0; k < p.length(); ++k) {
  var k := 0;
// src: src/ast/seq/seq_replace_all_facet.cpp:121 | for (unsigned k = 0; k < p.length(); ++k) {
  while k < |p|
// synth: specification, invariant, or structural delimiter
    invariant 0 <= k <= |p| && pos + k <= |input|
// synth: specification, invariant, or structural delimiter
    invariant input[pos..pos+k] == p[..k]
// synth: specification, invariant, or structural delimiter
    decreases |p| - k
// synth: specification, invariant, or structural delimiter
  {
// src: src/ast/seq/seq_replace_all_facet.cpp:122 | unsigned c;
// src: src/ast/seq/seq_replace_all_facet.cpp:123 | if (pos + k >= input.size())
    if pos + k >= |input| {
// src: src/ast/seq/seq_replace_all_facet.cpp:124 | return l_false;
      r := -1; return;
// synth: specification, invariant, or structural delimiter
    }
// src: src/ast/seq/seq_replace_all_facet.cpp:125 | if (!is_const_unit(u, input.get(pos + k), c))
    if !constant[pos+k] {
// synth: specification, invariant, or structural delimiter
      assert 0 <= k < |p| && pos+k < |input| && !constant[pos+k];
// synth: specification, invariant, or structural delimiter
      assert exists j :: j == k && 0 <= j < |p| && pos+j < |input| && !constant[pos+j];
// src: src/ast/seq/seq_replace_all_facet.cpp:126 | return l_undef;
      r := 0; return;
// synth: specification, invariant, or structural delimiter
    }
// src: src/ast/seq/seq_replace_all_facet.cpp:127 | if (c != p[k])
    if input[pos+k] != p[k] {
// src: src/ast/seq/seq_replace_all_facet.cpp:128 | return l_false;
      r := -1; return;
// synth: specification, invariant, or structural delimiter
    }
// synth: specification, invariant, or structural delimiter
    assert input[pos..pos+k+1] == input[pos..pos+k] + [input[pos+k]];
// synth: specification, invariant, or structural delimiter
    assert p[..k+1] == p[..k] + [p[k]];
// src: src/ast/seq/seq_replace_all_facet.cpp:121 | for (unsigned k = 0; k < p.length(); ++k) {
    k := k + 1;
// synth: specification, invariant, or structural delimiter
  }
// synth: specification, invariant, or structural delimiter
  assert input[pos..pos+|p|] == p;
// src: src/ast/seq/seq_replace_all_facet.cpp:130 | return l_true;
  r := 1;
// synth: specification, invariant, or structural delimiter
}

method NfvDomain0()
{
  var out0 := MatchEntry([97, 98], [true, true], 0, [97, 98]);
}

method NfvDomain1()
{
  var out0 := MatchEntry([97, 99], [false, true], 0, [98, 99]);
}

method NfvDomain2()
{
  var out0 := MatchEntry([], [], 0, [97]);
}
