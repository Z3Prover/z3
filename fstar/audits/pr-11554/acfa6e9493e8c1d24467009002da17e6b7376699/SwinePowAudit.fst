module SwinePowAudit
(* Model of arith_swine::check_model early reject (PR 11554 head acfa6e9,
   src/ast/rewriter/arith_swine.cpp lines 142-156).
   Assumptions: integers unbounded; mpz bitsize bs of v satisfies |v| <= 2^bs
   (holds for log2(a)+1 and mlog2(a)+1). Negative-exponent convention is not
   used by this obligation. *)

let rec pow (x:int) (n:nat) : Tot int (decreases n) = if n = 0 then 1 else x * pow x (n-1)
let iabs (x:int) : nat = if x >= 0 then x else -x

let rec pow_ge (x:int{iabs x >= 2}) (n:nat)
  : Lemma (ensures iabs (pow x n) >= pow2 n) (decreases n) =
  if n = 0 then () else begin
    pow_ge x (n-1);
    assert (iabs (pow x n) == iabs x * iabs (pow x (n-1)));
    assert (iabs x * iabs (pow x (n-1)) >= 2 * pow2 (n-1))
  end

(* O1: y>=0, |x|>=2, y > bs+1, |v| <= 2^bs  ==>  x^y <> v, so l_false is sound *)
let early_reject_sound (x:int) (y:nat) (v:int) (bs:nat)
  : Lemma (requires iabs x >= 2 /\ y > bs + 1 /\ iabs v <= pow2 bs)
          (ensures pow x y <> v) =
  pow_ge x y;
  FStar.Math.Lemmas.pow2_lt_compat y bs
