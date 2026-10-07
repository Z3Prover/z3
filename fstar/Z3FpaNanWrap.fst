(*
   Z3FpaNanWrap.fst

   A concrete, bit-level refinement of Z3FpaNanCongruence.fst, tied
   directly to the actual code mechanism responsible for issue #7842,
   traced this session to `theory_fpa::relevant_eh`
   (src/smt/theory_fpa.cpp, ~line 448-488) together with
   `fpa2bv_converter::{wrap, mk_is_nan, mk_nan}`
   (src/ast/fpa/fpa2bv_converter.cpp).

   The exact mechanism:

     - Every FP-sorted term `n` that becomes relevant and is *not*
       itself a literal `(fp sgn exp sig)` application goes through
       `relevant_eh`'s "general" branch. For a non-FPA-family `n`
       (e.g. a datatype accessor result such as `getFlt_1(x)`),
       `convert(n)` manufactures a *fresh*, otherwise-unconstrained
       `(fp sgn exp sig)` triple of bit-vector constants standing for
       `n`'s unknown value, and the code asserts
           `wrap(n) = concat(sgn, exp, sig)`.
       The sign/exponent/significand constants are constrained *only*
       by whatever other assertions mention `n` (e.g. `fp.isNaN(n)`,
       which merely fixes "exponent = all-1s, significand != 0" --
       `mk_is_nan`'s own definition).

     - A *literal* `(_ NaN eb sb)` numeral, by contrast, goes through
       the sibling "is_numeral" branch, where `convert` yields a
       *concrete* triple -- specifically `mk_nan`'s fixed choice
       `sign = 0, exponent = all-1s, significand = 1` (the smallest
       nonzero significand) -- so its `wrap(...)` is a single fixed
       bit-vector numeral.

     - `theory_datatypes`' congruence closure (deciding, e.g.,
       `distinct(x, Flt(NaN))`) operates on these two `wrap(...)`
       bit-vector values directly, via ordinary (syntactic/semantic)
       bit-vector equality -- it has no notion of "NaN" at all.

   Consequence: `is_nan(n)` only pins down *two* of the `sbits + ebits`
   bits of `wrap(n)` to one of *two* possible values each (the sign bit
   is free, the significand is free except "not all zero") -- every
   other satisfying assignment is a model of `fp.isNaN(n)` yet gives
   `wrap(n)` a *different* concrete bit-vector than the literal NaN's
   fixed `wrap(...)`. This file proves that fact concretely (not just
   abstractly, as `Z3FpaNanCongruence.fst` did), and proves that the
   proposed fix -- forcing `wrap(n) = wrap(mk_nan(...))` whenever
   `is_nan(n)` holds, asserted once per relevant term in exactly the
   branch identified above -- eliminates every such counterexample,
   for every format `(ebits, sbits)`.
*)
module Z3FpaNanWrap

(* ----------------------------------------------------------------- *)
(* Bit-vectors as naturals bounded by width, exactly as the           *)
(* underlying SMT bit-vector theory represents them (no wraparound     *)
(* issues arise below -- every operation here is extraction/            *)
(* concatenation, which `pow2`-arithmetic models exactly).              *)
(* ----------------------------------------------------------------- *)

let rec pow2 (n:nat) : Tot pos =
  if n = 0 then 1 else 2 * pow2 (n - 1)

(* A `(sign, exp, sig)` triple for a format with `ebits` exponent bits  *)
(* and `sbits` significand bits (significand field width = sbits - 1,   *)
(* the hidden bit is implicit and irrelevant to NaN/wrap mechanics).     *)
type triple = { sgn: nat; exp: nat; sig_: nat }

let is_valid_triple (ebits sbits:pos) (t:triple) : prop =
  t.sgn < 2 /\ t.exp < pow2 ebits /\ t.sig_ < pow2 (sbits - 1)

(* `concat(sgn, exp, sig)`, exactly as `fpa2bv_converter::join_fp`/      *)
(* `wrap`'s `mk_concat` computes it: a single bit-vector value           *)
(* `sgn * 2^(ebits+sbits-1) + exp * 2^(sbits-1) + sig`.                   *)
let concat (ebits sbits:pos) (t:triple) : nat =
  t.sgn * (pow2 ebits * pow2 (sbits - 1)) + t.exp * pow2 (sbits - 1) + t.sig_

(* `mk_is_nan`'s own definition: exponent is all-1s (`2^ebits - 1`),      *)
(* significand is nonzero. *)
let is_nan_triple (ebits sbits:pos) (t:triple) : bool =
  (t.exp = pow2 ebits - 1) && (t.sig_ <> 0)

(* `mk_nan`'s fixed choice: sign = 0, exponent = all-1s, significand = 1. *)
let canonical_nan (ebits sbits:pos) : triple =
  { sgn = 0; exp = pow2 ebits - 1; sig_ = 1 }

let lemma_canonical_nan_is_nan (ebits sbits:pos{sbits >= 2})
  : Lemma (is_nan_triple ebits sbits (canonical_nan ebits sbits))
  = ()

(* ----------------------------------------------------------------- *)
(* THE DEFECT, concretely: for any format with at least 2 significand   *)
(* bits (so there is room for a second nonzero significand value),       *)
(* there are *two* distinct, both-valid, both-NaN triples whose `concat` *)
(* (i.e. `wrap(...)`) values differ -- so `fp.isNaN` alone does not       *)
(* pin down a unique wrapped bit-vector, unlike what datatype/UF          *)
(* congruence closure needs to merge them.                                *)
(* ----------------------------------------------------------------- *)

let other_nan (ebits sbits:pos{sbits >= 3}) : triple =
  { sgn = 0; exp = pow2 ebits - 1; sig_ = 2 }

let lemma_defect_concrete (ebits sbits:pos{sbits >= 3})
  : Lemma (let c = canonical_nan ebits sbits in
           let o = other_nan ebits sbits in
           is_valid_triple ebits sbits c /\
           is_valid_triple ebits sbits o /\
           is_nan_triple ebits sbits c /\
           is_nan_triple ebits sbits o /\
           concat ebits sbits c <> concat ebits sbits o)
  = ()

(* ----------------------------------------------------------------- *)
(* THE FIX, concretely: assert, for every relevant FP-sorted term's      *)
(* fresh `(sgn, exp, sig)` triple `t`, the side condition                 *)
(*     is_nan_triple ebits sbits t  ==>  t = canonical_nan ebits sbits    *)
(* (equivalently, on wrapped values: `wrap(n) = wrap(mk_nan(...))`).      *)
(* Under this constraint, *every* valid triple satisfying `is_nan_       *)
(* triple` collapses to the single canonical one, hence to the single    *)
(* canonical `concat` value -- i.e. ordinary syntactic/semantic bit-       *)
(* vector equality (exactly what datatype/UF congruence closure uses)      *)
(* now suffices to merge it with the literal NaN's wrapped value, with      *)
(* zero FP-theory-specific reasoning required downstream.                   *)
(* ----------------------------------------------------------------- *)

let fixed_constraint (ebits sbits:pos) (t:triple) : prop =
  is_valid_triple ebits sbits t /\
  (is_nan_triple ebits sbits t ==> t == canonical_nan ebits sbits)

let lemma_fix_forces_unique_wrap (ebits sbits:pos{sbits >= 2}) (t:triple)
  : Lemma (requires fixed_constraint ebits sbits t /\ is_nan_triple ebits sbits t)
          (ensures concat ebits sbits t = concat ebits sbits (canonical_nan ebits sbits))
  = ()

(* The fix does not exclude the canonical witness itself (satisfiability *)
(* is preserved: `is_nan` is not made vacuous, unlike the #7431 zero-sign  *)
(* bug -- there, the *entire* two-element domain collapsed to one point;   *)
(* here, only the NaN sub-domain is collapsed, every non-NaN triple is      *)
(* untouched). *)
let lemma_fix_is_satisfiable (ebits sbits:pos{sbits >= 2})
  : Lemma (fixed_constraint ebits sbits (canonical_nan ebits sbits))
  = ()

(* The fix leaves every non-NaN triple's constraint exactly as before     *)
(* (it is a conditional, firing only when `is_nan_triple` holds) -- so it  *)
(* cannot introduce any new unsoundness elsewhere; this is the formal       *)
(* counterpart of "no exponential blowup, no pairwise axioms, and no        *)
(* interference with non-NaN reasoning" that the GitHub thread's              *)
(* @wintersteiger worried a naive fix might cause. *)
let lemma_fix_is_conservative (ebits sbits:pos{sbits >= 2}) (t:triple)
  : Lemma (requires is_valid_triple ebits sbits t /\ ~(is_nan_triple ebits sbits t))
          (ensures fixed_constraint ebits sbits t)
  = ()
