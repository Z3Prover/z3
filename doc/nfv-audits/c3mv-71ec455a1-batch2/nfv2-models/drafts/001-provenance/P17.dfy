// src: src/ast/rewriter/seq_regex_witness.cpp:154 | bool conjunction = re().is_intersection(r);
method BooleanEntry(conjunction: bool, child_verdicts: seq<int>) returns (verdict: int)
// synth: specification, checked proof annotation, or structural delimiter
  requires forall value :: value in child_verdicts ==> -1 <= value <= 1
// synth: specification, checked proof annotation, or structural delimiter
  requires |child_verdicts| < 4294967296
// synth: specification, checked proof annotation, or structural delimiter
  ensures verdict == (if conjunction then (if -1 in child_verdicts then -1 else if 0 in child_verdicts then 0 else 1) else (if 1 in child_verdicts then 1 else if 0 in child_verdicts then 0 else -1))
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/ast/rewriter/seq_regex_witness.cpp:156 | for (expr* arg : *to_app(r)) {
  verdict := if conjunction then 1 else -1;
// src: src/ast/rewriter/seq_regex_witness.cpp:157 | lbool value = accepts(word, arg, depth + 1, work);
  var i := 0;
// src: src/ast/rewriter/seq_regex_witness.cpp:157 | lbool value = accepts(word, arg, depth + 1, work);
  while i < |child_verdicts|
// synth: specification, checked proof annotation, or structural delimiter
    invariant 0 <= i <= |child_verdicts|
// synth: specification, checked proof annotation, or structural delimiter
    invariant conjunction ==> -1 !in child_verdicts[..i]
// synth: specification, checked proof annotation, or structural delimiter
    invariant !conjunction ==> 1 !in child_verdicts[..i]
// synth: specification, checked proof annotation, or structural delimiter
    invariant verdict == (if 0 in child_verdicts[..i] then 0 else if conjunction then 1 else -1)
// synth: specification, checked proof annotation, or structural delimiter
    decreases |child_verdicts| - i
// synth: specification, checked proof annotation, or structural delimiter
  {
// src: src/ast/rewriter/seq_regex_witness.cpp:158 | if (value == (conjunction ? l_false : l_true))
    var value := child_verdicts[i];
// src: src/ast/rewriter/seq_regex_witness.cpp:159 | return value;
    if value == (if conjunction then -1 else 1) {
// src: src/ast/rewriter/seq_regex_witness.cpp:160 | if (value == l_undef)
      verdict := value; return;
// synth: specification, checked proof annotation, or structural delimiter
    }
// src: src/ast/rewriter/seq_regex_witness.cpp:161 | result = l_undef;
    if value == 0 {
// src: src/ast/rewriter/seq_regex_witness.cpp:162 | }
      verdict := 0;
// synth: specification, checked proof annotation, or structural delimiter
    }
// src: src/ast/rewriter/seq_regex_witness.cpp:157 | lbool value = accepts(word, arg, depth + 1, work);
    i := i + 1;
// synth: specification, checked proof annotation, or structural delimiter
  }
// synth: specification, checked proof annotation, or structural delimiter
}
