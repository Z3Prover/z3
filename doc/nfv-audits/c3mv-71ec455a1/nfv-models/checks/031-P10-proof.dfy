// src: src/ast/rewriter/seq_rewriter.cpp:4519 | // (R+){lo,hi} = R{lo,} when hi > 0.
ghost predicate NestedPlus(count: int, lo: int, hi: int, bounded: bool)
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/rewriter/seq_rewriter.cpp:4519 | // (R+){lo,hi} = R{lo,} when hi > 0.
  exists groups :: 0 <= groups && lo <= groups && (!bounded || groups <= hi) && ((groups == 0 && count == 0) || (groups > 0 && groups <= count))
// synth: specification, invariant, or structural delimiter
}
// src: src/ast/rewriter/seq_rewriter.cpp:4480 | br_status seq_rewriter::mk_re_loop(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
method PlusEntry(count: int, lo: int, hi: int, bounded: bool) returns (accepted: bool)
// synth: specification, invariant, or structural delimiter
  requires 0 <= count && 0 <= lo <= 4294967295 && 0 <= hi <= 4294967295
// synth: specification, invariant, or structural delimiter
  requires bounded ==> lo <= hi
// synth: specification, invariant, or structural delimiter
  ensures accepted == NestedPlus(count,lo,hi,bounded)
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/rewriter/seq_rewriter.cpp:4505 | if (np == 2 && lo2 == 0 && hi2 == 0) {
  if bounded && lo == 0 && hi == 0 {
// src: src/ast/rewriter/seq_rewriter.cpp:4506 | result = mk_to_re(str().mk_empty(re().to_seq(args[0]->get_sort())));
// src: src/ast/rewriter/seq_rewriter.cpp:4507 | return BR_DONE;
    accepted := count == 0; return;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/rewriter/seq_rewriter.cpp:4511 | if (np == 1 && lo2 == 0) {
  if !bounded && lo == 0 {
// src: src/ast/rewriter/seq_rewriter.cpp:4512 | result = mk_star(args[0]);
// src: src/ast/rewriter/seq_rewriter.cpp:4513 | return BR_DONE;
    accepted := true; return;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/rewriter/seq_rewriter.cpp:4515 | if (np == 2 && lo2 == 1 && hi2 == 1) {
  if bounded && lo == 1 && hi == 1 {
// src: src/ast/rewriter/seq_rewriter.cpp:4516 | result = args[0];
// src: src/ast/rewriter/seq_rewriter.cpp:4517 | return BR_DONE;
    accepted := count >= 1; return;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/rewriter/seq_rewriter.cpp:4520 | if ((np == 1 || np == 2) &&
// src: src/ast/rewriter/seq_rewriter.cpp:4521 | (re().is_plus(args[0], a) ||
// src: src/ast/rewriter/seq_rewriter.cpp:4522 | (re().is_concat(args[0], a, b) && re().is_star(b, c) && a == c))) {
// src: src/ast/rewriter/seq_rewriter.cpp:4523 | result = mk_loop(a, lo2);
// src: src/ast/rewriter/seq_rewriter.cpp:4524 | return BR_DONE;
  accepted := count >= lo;
// synth: specification, invariant, or structural delimiter
}
