// src: src/ast/simplifiers/seq_regular_simplifier.cpp:326 | switch (op) {
function Comparison(value: int, bound: int, op: int): bool
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:327 | case comparison_kind::eq: language = bound.is_minus_one() ? complement(valid) : empty.get(); break;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:328 | case comparison_kind::ne: language = bound.is_minus_one() ? valid : all.get(); break;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:329 | case comparison_kind::le: language = bound.is_minus_one() ? complement(valid) : empty.get(); break;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:330 | case comparison_kind::lt: language = empty; break;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:331 | case comparison_kind::ge: language = all; break;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:332 | case comparison_kind::gt: language = bound.is_minus_one() ? valid : all.get(); break;
  if op == 0 then value == bound else if op == 1 then value != bound else if op == 2 then value <= bound else if op == 3 then value < bound else if op == 4 then value >= bound else value > bound
// synth: specification, invariant, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:316 | expr* decimal_language(comparison_kind op, rational const& bound) {
method DecimalEntry(valid: bool, value: int, bound: int, op: int) returns (member: bool)
// synth: specification, invariant, or structural delimiter
  requires 0 <= op <= 5 && bound < 0
// synth: specification, invariant, or structural delimiter
  requires (valid && value >= 0) || (!valid && value == -1)
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:326 | switch (op) {
  if op == 0 {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:327 | case comparison_kind::eq: language = bound.is_minus_one() ? complement(valid) : empty.get(); break;
    member := if bound == -1 then !valid else false;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:328 | case comparison_kind::ne: language = bound.is_minus_one() ? valid : all.get(); break;
  else if op == 1 {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:328 | case comparison_kind::ne: language = bound.is_minus_one() ? valid : all.get(); break;
    member := if bound == -1 then valid else true;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:329 | case comparison_kind::le: language = bound.is_minus_one() ? complement(valid) : empty.get(); break;
  else if op == 2 {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:329 | case comparison_kind::le: language = bound.is_minus_one() ? complement(valid) : empty.get(); break;
    member := if bound == -1 then !valid else false;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:330 | case comparison_kind::lt: language = empty; break;
  else if op == 3 {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:330 | case comparison_kind::lt: language = empty; break;
    member := false;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:331 | case comparison_kind::ge: language = all; break;
  else if op == 4 {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:331 | case comparison_kind::ge: language = all; break;
    member := true;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:332 | case comparison_kind::gt: language = bound.is_minus_one() ? valid : all.get(); break;
  else {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:332 | case comparison_kind::gt: language = bound.is_minus_one() ? valid : all.get(); break;
    member := if bound == -1 then valid else true;
// synth: specification, invariant, or structural delimiter
  }
// synth: specification, invariant, or structural delimiter
}

method NfvDomain0()
{
  var out0 := DecimalEntry(false, (-1), (-1), 0);
}

method NfvDomain1()
{
  var out0 := DecimalEntry(true, 0, (-2), 5);
}
