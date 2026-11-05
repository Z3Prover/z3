(*
   Z3FpaNanCongruence.fst

   Targeted audit of issue #7842 ("Incorrect model") and the documented
   bug-cluster it belongs to (#7162, #7321, #8185 -- "invalid model
   generated" reports clustering around FP special values crossing a
   theory boundary). Minimal reproducer:

       (declare-datatype Expr ((Flt (getFlt_1 (_ FloatingPoint 8 24)))))
       (declare-fun x () Expr)
       (assert (distinct x (Flt (_ NaN 8 24))))
       (assert (fp.isNaN (getFlt_1 x)))
       (check-sat)

   reported `sat` with `x = (Flt (_ NaN 8 24))`, which directly
   contradicts the `distinct` assertion -- model_validate correctly
   flags this as an invalid model.

   Root cause (reconstructed from the GitHub issue thread's own
   investigation, in particular the comment pinpointing selector
   encoding `0x7f800002` vs. literal-NaN encoding `0x7f800001`):

     The FloatingPoint theory's *own* "=" already treats every NaN
     bit pattern as mutually equal (SMT-LIB's FloatingPoint theory
     specifies this explicitly: unlike raw bit-vectors, "=" on sort
     `(_ FloatingPoint eb sb)` does not distinguish NaN payloads --
     this is confirmed in the thread: "SMT equality (=) on FP terms
     already handles the both-NaN case correctly in `mk_eq`").

     But `theory_datatypes.cpp`'s congruence closure, deciding
     `(distinct x (Flt NaN))`, operates over the *raw* term/bit-vector
     representation produced by `fpa2bv_rewriter` for each operand
     independently -- it has no reason to know that two
     differently-encoded NaN bit-vectors denote the same FP-theory
     value, because the NaN-collapsing equality is a fact *local to*
     `theory_fpa`, never propagated across the datatype constructor/
     selector boundary. The two NaN encodings therefore end up in
     different congruence classes, and `distinct` (correctly, for
     that weaker raw notion of equality) succeeds.

   This is a *substitutivity* failure: the combined theory uses one
   notion of "=" (NaN-collapsing) for direct FP terms and a strictly
   finer one (bit-exact) for FP values nested inside other theories'
   terms, which is not a congruence for the wrapping constructors.

   This file formalizes both notions of equality, proves the FP-level
   one is an equivalence (as the thread asserts), proves the finer
   "raw" one used (in effect) at the datatype boundary is NOT a
   congruence for `Flt` with respect to the FP-level equality (the
   precise formal defect), reproduces the invalid model as a direct
   corollary, and then verifies the fix direction floated in the
   thread itself (@wintersteiger: canonicalize every FP-sorted
   sub-term -- "if is_nan(x) then nan else x" -- before it participates
   in any cross-theory equality): canonicalizing first and then
   comparing with the raw/bit-exact equality is *equivalent* to
   comparing directly with the correct FP-level equality, for every
   pair of values and every wrapping context.
*)
module Z3FpaNanCongruence

(* ----------------------------------------------------------------- *)
(* FP values, with NaN payloads modeled explicitly (`nat`) so that     *)
(* "different bit-pattern, same semantic NaN" is representable at all. *)
(* ----------------------------------------------------------------- *)

type fpval =
  | Num of int       // a finite, non-NaN value (exact integer code, for simplicity)
  | NaN of nat        // a NaN, carrying its raw payload/bit-pattern
  | PInf
  | NInf

(* The FP theory's own "=" (what `theory_fpa::mk_eq` implements):      *)
(* every NaN, regardless of payload, is equal to every other NaN.      *)
let fp_eq (a b:fpval) : bool =
  match a, b with
  | Num x, Num y -> x = y
  | PInf, PInf -> true
  | NInf, NInf -> true
  | NaN _, NaN _ -> true
  | _, _ -> false

let lemma_fp_eq_equivalence ()
  : Lemma ((forall a. fp_eq a a) /\
           (forall a b. fp_eq a b ==> fp_eq b a) /\
           (forall a b c. fp_eq a b /\ fp_eq b c ==> fp_eq a c))
  = ()

(* The RAW/bit-exact equality actually used once an `fpval` is nested   *)
(* inside another theory's term (e.g. as a datatype field): it           *)
(* distinguishes NaN payloads, exactly like ordinary bit-vector          *)
(* equality would. *)
let raw_eq (a b:fpval) : bool =
  match a, b with
  | Num x, Num y -> x = y
  | PInf, PInf -> true
  | NInf, NInf -> true
  | NaN p1, NaN p2 -> p1 = p2
  | _, _ -> false

let lemma_raw_eq_equivalence ()
  : Lemma ((forall a. raw_eq a a) /\
           (forall a b. raw_eq a b ==> raw_eq b a) /\
           (forall a b c. raw_eq a b /\ raw_eq b c ==> raw_eq a c))
  = ()

(* `raw_eq` is strictly finer than `fp_eq`: it implies it, but not       *)
(* conversely (two differently-payloaded NaNs are a counterexample).     *)
let lemma_raw_eq_refines_fp_eq ()
  : Lemma ((forall a b. raw_eq a b ==> fp_eq a b) /\
           (fp_eq (NaN 0) (NaN 2) /\ ~(raw_eq (NaN 0) (NaN 2))))
  = ()

(* ----------------------------------------------------------------- *)
(* The datatype wrapper, and the two candidate notions of equality on   *)
(* wrapped values: the CORRECT one (`dt_eq_correct`, built from           *)
(* `fp_eq`, i.e. what a congruence-respecting combination must use),      *)
(* and the BUGGY one actually computed when the datatype theory's own     *)
(* congruence closure is applied to the raw encoding (`dt_eq_buggy`,       *)
(* built from `raw_eq`).                                                   *)
(* ----------------------------------------------------------------- *)

type dtval = | Flt of fpval

let dt_eq_correct (a b:dtval) : bool =
  let Flt x = a in let Flt y = b in fp_eq x y

let dt_eq_buggy (a b:dtval) : bool =
  let Flt x = a in let Flt y = b in raw_eq x y

(* `dt_eq_correct` is -- trivially, by construction -- a congruence of   *)
(* `fp_eq` for `Flt`: wrapping preserves exactly the FP-level             *)
(* equivalence, no more and no less. *)
let lemma_dt_eq_correct_is_congruence ()
  : Lemma (forall x y. fp_eq x y <==> dt_eq_correct (Flt x) (Flt y))
  = ()

(* THE DEFECT: `dt_eq_buggy` is *not* a congruence of `fp_eq` for         *)
(* `Flt` -- it fails to merge two `Flt`-wrapped values whose underlying   *)
(* FP values the FP theory itself considers equal (both NaN). *)
let lemma_dt_eq_buggy_is_not_a_congruence ()
  : Lemma (fp_eq (NaN 1) (NaN 2) /\ ~(dt_eq_buggy (Flt (NaN 1)) (Flt (NaN 2))))
  = ()

(* ----------------------------------------------------------------- *)
(* Reproduction of #7842's exact invalid model: let `x`'s underlying     *)
(* FP value be the selector-produced NaN payload `2` (standing for the    *)
(* reported `0x7f800002`), and let the literal canonical NaN in the       *)
(* assertion be payload `1` (`0x7f800001`). `fp.isNaN(getFlt_1 x)` holds   *)
(* (the FP-level predicate only inspects the exponent/significand          *)
(* pattern, true for any NaN payload), yet `distinct x (Flt (NaN 1))`      *)
(* is -- incorrectly -- accepted, because `dt_eq_buggy` is what the        *)
(* datatype theory's congruence closure actually consults.                 *)
(* ----------------------------------------------------------------- *)

let is_nan_val (v:fpval) : bool = match v with | NaN _ -> true | _ -> false

let lemma_reproduces_invalid_model ()
  : Lemma (let x : dtval = Flt (NaN 2) in
           let canonical : dtval = Flt (NaN 1) in
           is_nan_val (NaN 2) /\                     // fp.isNaN(getFlt_1 x) holds
           ~(dt_eq_buggy x canonical) /\              // distinct x canonical "succeeds" (buggy)
           dt_eq_correct x canonical)                  // ... yet they ARE FP-equal (ground truth)
  = ()

(* ----------------------------------------------------------------- *)
(* THE FIX (as floated by @wintersteiger in the thread): canonicalize    *)
(* any FP-sorted sub-term to a single representative NaN *before* it      *)
(* participates in any cross-theory equality --                           *)
(*     canonicalize(v) = if is_nan(v) then NaN(0) else v                   *)
(* -- and then compare with the (otherwise-buggy) raw/bit-exact            *)
(* equality. This file proves this is *exactly* equivalent to directly     *)
(* using the correct FP-level equality, for every pair of values and        *)
(* every `Flt`-wrapping context -- i.e. canonicalizing at the boundary       *)
(* is a sufficient and exact repair, matching the thread's own later         *)
(* confirmation ("I tried NaN normalization in unwrap... it fixes the         *)
(* original reproducer").                                                     *)
(* ----------------------------------------------------------------- *)

let canonicalize (v:fpval) : fpval =
  if is_nan_val v then NaN 0 else v

let lemma_canonicalize_then_raw_eq_correct ()
  : Lemma (forall (v w:fpval). raw_eq (canonicalize v) (canonicalize w) <==> fp_eq v w)
  = ()

let lemma_fix_restores_congruence ()
  : Lemma (forall (v w:fpval).
             dt_eq_buggy (Flt (canonicalize v)) (Flt (canonicalize w)) <==> dt_eq_correct (Flt v) (Flt w))
  = ()

(* The fix closes the exact counterexample from `lemma_dt_eq_buggy_      *)
(* is_not_a_congruence`/`lemma_reproduces_invalid_model` above: once      *)
(* both NaN payloads are canonicalized, the (still bit-exact) `dt_eq_     *)
(* buggy` now agrees with the correct, FP-aware notion. *)
let lemma_fix_closes_the_gap ()
  : Lemma (dt_eq_buggy (Flt (canonicalize (NaN 2))) (Flt (canonicalize (NaN 1))))
  = ()

(* ----------------------------------------------------------------- *)
(* Caveat (recorded, not proved away): the thread's own follow-up        *)
(* notes that canonicalizing only at one specific `unwrap` call site      *)
(* leaves OTHER cross-theory contexts unrepaired (e.g. a raw `(fp ...)`    *)
(* term reaching a UF argument position directly, bypassing that one      *)
(* wrap/unwrap bridge). The theorems above establish that canonicalizing  *)
(* is the *right* transformation wherever it is applied; they do not      *)
(* establish -- and the open thread confirms this is still unresolved --  *)
(* that today's code applies it at *every* FP-value crossing point in     *)
(* the solver (datatypes, arrays, and plain UF arguments alike).          *)
(* ----------------------------------------------------------------- *)
