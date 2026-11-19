// src: src/ast/rewriter/guard_set.cpp:116 | lbool seq::predicate_algebra::mk_fresh(ptr_vector<expr> const& consts, expr_ref& out) const {
method FreshLengthEntry(lengths: seq<int>) returns (length: int, characters: seq<int>)
// synth: specification, invariant, or structural delimiter
  requires |lengths| < 4294967295
// synth: specification, invariant, or structural delimiter
  requires forall i :: 0 <= i < |lengths| ==> 0 <= lengths[i] <= 4294967295
// synth: specification, invariant, or structural delimiter
  requires forall i,j :: 0 <= i < j < |lengths| ==> lengths[i] <= lengths[j]
// synth: specification, invariant, or structural delimiter
  ensures 0 <= length <= |lengths|
// synth: specification, invariant, or structural delimiter
  ensures forall i :: 0 <= i < |lengths| ==> lengths[i] != length
// synth: specification, invariant, or structural delimiter
  ensures |characters| == length && forall i :: 0 <= i < |characters| ==> characters[i] == 0
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/rewriter/guard_set.cpp:127 | unsigned length = 0;
  length := 0;
// src: src/ast/rewriter/guard_set.cpp:128 | for (unsigned n : lengths)
  var i := 0;
// src: src/ast/rewriter/guard_set.cpp:128 | for (unsigned n : lengths)
  while i < |lengths|
// synth: specification, invariant, or structural delimiter
    invariant 0 <= i <= |lengths| && 0 <= length <= i
// synth: specification, invariant, or structural delimiter
    invariant forall j :: 0 <= j < i ==> lengths[j] != length
// synth: specification, invariant, or structural delimiter
    decreases |lengths| - i
// synth: specification, invariant, or structural delimiter
  {
// src: src/ast/rewriter/guard_set.cpp:128 | for (unsigned n : lengths)
    var n := lengths[i];
// src: src/ast/rewriter/guard_set.cpp:129 | if (n == length)
    if n == length {
// src: src/ast/rewriter/guard_set.cpp:130 | ++length;
      length := length + 1;
// synth: specification, invariant, or structural delimiter
    }
// src: src/ast/rewriter/guard_set.cpp:128 | for (unsigned n : lengths)
    i := i+1;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/rewriter/guard_set.cpp:132 | svector<unsigned> characters;
// src: src/ast/rewriter/guard_set.cpp:133 | characters.resize(length, 0);
// src: src/ast/rewriter/guard_set.cpp:134 | out = u.str.mk_string(zstring(characters.size(), characters.data()));
  characters := seq(length, i => 0);
// synth: specification, invariant, or structural delimiter
}
