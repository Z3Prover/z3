(*
   Z3BvInterp.fst

   The bit-vector theory's thin, `value`-level companion to
   `Z3BvTheory.fst`, owning two `decl_kind`s: `op_bvand` (the binary
   `bvand` operator) and `op_num_bv` (bit-vector *numeral literals*,
   e.g. `(_ bv3 32)`).
*)
module Z3BvInterp
open Z3AstTheory
open Z3ValueTheory

(* The exact reduction `op_num_bv`'s interpretation applies to a raw
   `int` to land in `Z3BvTheory.bv 32 = k:nat{k < pow2 32}`; exposed
   here (not inlined) so `Z3PatternMatchedProofChecker`'s
   `provably_distinct` can compare *post-reduction* values -- two BV
   literal `func_decl`s with different raw `int_params` but the same
   value mod 2^32 denote the *same* bit-vector, so distinctness must be
   decided on `bv32_value`, never on the raw parameter.

   NB: this just re-exports `Z3BvTheory.bv_of_int` under a 32-specific
   name. Re-deriving `FStar.UInt.to_uint_t`'s range fact *inline*,
   directly inside a monolithic case-split alongside every *other*
   theory's facts, was observed to make Z3's automatic search
   pathologically slow (a multi-hour hang, see
   `PULSE_PROOF_CHECKER_REPORT.md`'s "Performance lesson") --
   almost certainly because that single VC then has to carry
   `FStar.UInt`/`pow2`'s machinery alongside array/seq/bool facts at
   once. Defining the conversion as its own already-checked top-level
   function in `Z3BvTheory.fst` (right next to its other `bv`
   conversions, where the same facts are already established quickly),
   and now additionally isolating *all* bv-touching interpretation
   (this whole file) behind its own `interp_app` entry point so the
   top-level cross-theory dispatcher never has to reason about
   `Z3BvTheory`/`FStar.UInt` facts in the same VC as array/seq
   reasoning, avoids that blowup entirely. *)
let bv32_value (v:int) : Z3BvTheory.bv 32 = Z3BvTheory.bv_of_int v

let interp_bvand (args:list value) : value =
  match args with
  | [VBV a; VBV b] -> VBV (Z3BvTheory.bvand a b)
  | _ -> VInt 0

let interp_num_bv (int_params:list int) : value =
  match int_params with
  | [v] -> VBV (bv32_value v)
  | _ -> VInt 0

let interp_app (k:decl_kind) (int_params:list int) (args:list value) : option value =
  if k = op_bvand then Some (interp_bvand args)
  else if k = op_num_bv then Some (interp_num_bv int_params)
  else None
