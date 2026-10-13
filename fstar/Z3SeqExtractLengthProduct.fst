(*
   Z3SeqExtractLengthProduct.fst

   Targeted audit of a new `seq_rewriter::mk_seq_extract` simplification
   (src/ast/rewriter/seq_rewriter.cpp, ~line 976), motivated by open
   PR #11165 ("Avoid regex unfolding for provably out-of-range substring
   offsets", fixing issue #11157).

   Context: `(str.substr a offset size)` ("extract", see Z3SeqTheory.fst)
   is empty whenever `offset >= len(a)` -- the start position is at or
   past the end of the string, so no characters are extracted,
   regardless of `size`. When `offset` is a *constant* numeral this was
   already checked elsewhere; PR #11165 adds a *symbolic* case: when
   `offset` is a product (after flattening nested `*` nodes) of the
   form `c * len(a)^k` for a known integer coefficient `c >= 1` and
   `k >= 1` repetitions of the `len(a)` factor (interspersed with other
   `>= 1` numeral factors), the rewriter can conclude `offset >= len(a)`
   symbolically, without knowing `len(a)`'s actual value, and simplify
   the extract straight to the empty sequence.

   The bug being fixed (issue #11157): without this check, a query
   whose only path to `unsat` was recognizing `len(a)^2 >= len(a)`
   (hence the extract is always empty) fell through to a general regex
   membership check over an *unbounded* unrolling of `str.substr`,
   which hit "reached max unfolding" and returned `unknown` instead of
   the correct `unsat`.

   This file isolates and proves the one purely arithmetic fact the new
   rewrite's soundness hinges on: for every natural number `n` (a
   string length, always `>= 0`) and integers `c >= 1`, `k >= 1`,

       c * n^k >= n.

   Combined with `Z3SeqTheory.fst`'s existing `extract`/`extract_nat`
   model (reused directly, not re-derived), this yields the rewrite's
   full correctness: `extract s (c * (len s)^k) size == empty` whenever
   `c >= 1` and `k >= 1`, for *any* `size` -- matching the C++ rewrite,
   which indeed does not inspect the `size` argument at all once the
   offset-dominates-length condition is established.

   The surrounding AST-level machinery (DAG-size-bounded traversal
   flattening nested `*`/visited-set bookkeeping, recognizing
   `str.len a` sub-terms syntactically) is ordinary tree-walking code
   with no independent semantic content beyond "extract the same `c`,
   `k` this file reasons about" and is not re-modeled here, consistent
   with this audit series' treatment of other purely-syntactic
   traversal helpers.
*)
module Z3SeqExtractLengthProduct

open Z3SeqTheory

(* ----------------------------------------------------------------- *)
(* The arithmetic core: c * n^k >= n for n:nat, c >= 1, k >= 1.        *)
(* ----------------------------------------------------------------- *)

let rec pow (n:nat) (k:pos) : nat =
  if k = 1 then n else n * pow n (k - 1)

(* Step 1: n^k >= n for any k >= 1 (monotonicity of powers at base >= 0:
   either n = 0, where n^k = 0 = n for all k >= 1, or n >= 1, where
   multiplying by n (itself >= 1) never decreases the running product). *)
let rec lemma_pow_ge_self (n:nat) (k:pos)
  : Lemma (pow n k >= n)
  = if k = 1 then ()
    else begin
      lemma_pow_ge_self n (k - 1);
      // pow n k == n * pow n (k-1), and pow n (k-1) >= n by IH.
      // If n = 0, pow n k = 0 = n trivially. If n >= 1, n * pow n (k-1)
      // >= n * n >= n * 1 = n (since pow n (k-1) >= n >= 1... but more
      // directly: n * x >= n whenever x >= 1, and pow n (k-1) >= n >= 0;
      // if n = 0 both sides are 0; if n >= 1 then pow n (k-1) >= n >= 1).
      ()
    end

(* Step 2: c * m >= m for any c >= 1, m:nat (scaling up by a factor
   >= 1 never decreases a nonnegative quantity). *)
let lemma_scale_ge_self (c:pos) (m:nat)
  : Lemma (c * m >= m)
  = ()

(* Main arithmetic theorem: c * n^k >= n. *)
let lemma_coeff_times_power_ge_base (n:nat) (c k:pos)
  : Lemma (c * pow n k >= n)
  =
  lemma_pow_ge_self n k;
  lemma_scale_ge_self c (pow n k)

(* ----------------------------------------------------------------- *)
(* Consequence for `extract`: an offset at or past the string's own    *)
(* length always yields an empty extract, for any size.                *)
(* ----------------------------------------------------------------- *)

(* `extract_nat` empties out once `pos` has consumed the whole list; a
   direct induction confirms this for every `pos >= len s`. *)
let rec lemma_extract_nat_oob (#a:eqtype) (s:seq a) (pos:nat) (ln:nat)
  : Lemma (requires pos >= len s)
          (ensures extract_nat s pos ln == empty)
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_extract_nat_oob s' (pos - 1) ln

let lemma_extract_oob (#a:eqtype) (s:seq a) (pos ln:int)
  : Lemma (requires pos >= len s)
          (ensures extract s pos ln == empty)
  =
  if pos < 0 || ln <= 0 then ()
  else lemma_extract_nat_oob s pos ln

(* ----------------------------------------------------------------- *)
(* The rewrite's full correctness: substr at offset c * len(s)^k, any   *)
(* size, is always empty, for c >= 1, k >= 1. This is the F* mirror    *)
(* of `seq_rewriter::mk_seq_extract`'s new branch together with the    *)
(* `out_of_bounds`-implying arithmetic fact it is built on.            *)
(* ----------------------------------------------------------------- *)
let lemma_extract_length_power_offset_empty
      (#a:eqtype) (s:seq a) (c k:pos) (size:int)
  : Lemma (extract s (c * pow (len s) k) size == empty)
  =
  lemma_coeff_times_power_ge_base (len s) c k;
  lemma_extract_oob s (c * pow (len s) k) size
