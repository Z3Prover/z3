module Z3SeqRewriterIndex

(*
   Width audit for src/util/zstring.cpp::indexofu and
   src/ast/rewriter/seq_rewriter.cpp::mk_seq_index.

   The search logic itself is not re-proved here; the only question is whether
   the rewriter's concrete C++ return type (`int`) can represent the true
   mathematical `seq.indexof` result. SMT-LIB uses arbitrary-precision
   integers, so the exact value is always the true match position `k` (or -1 if
   not found). A signed 32-bit C++ `int` can represent that value only when
   k < 2^31.
*)

let int32_min : int = -2147483648
let int32_max : int = 2147483647
let int32_upper_exclusive : nat = 2147483648

type int32 = i:int{ int32_min <= i /\ i <= int32_max }

/// Mathematical seq.indexof result: either -1 or the exact first-match index.
let math_indexofu_result (true_index:option nat) : int =
  match true_index with
  | None -> -1
  | Some k -> k

let indexofu_not_found_spec () : Lemma
  (math_indexofu_result None == -1) =
  ()

let indexofu_found_spec (k:nat) : Lemma
  (math_indexofu_result (Some k) == k) =
  ()

/// A 32-bit implementation value exists exactly when the mathematical index
/// fits the signed range used by C++ `int`.
let indexofu_impl_result (k:nat{k < int32_upper_exclusive}) : int32 = k

/// Conditional correctness for the concrete rewriter path in mk_seq_index:
/// when the true index fits in signed 32-bit range, the `int`-returning
/// implementation can return that exact same value.
let indexofu_correct_when_in_range (k:nat) : Lemma
  (requires k < int32_upper_exclusive)
  (ensures indexofu_impl_result k == math_indexofu_result (Some k)) =
  ()

/// Counterexample to the naive unconditional claim "the C++ int result can
/// always equal the mathematical seq.indexof result": 2^31 itself is a valid
/// SMT-LIB integer result but is not representable by signed 32-bit `int`.
let indexofu_width_mismatch_counterexample () : Lemma
  (~ (exists (r:int32). r == math_indexofu_result (Some int32_upper_exclusive))) =
  ()
