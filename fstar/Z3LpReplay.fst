module Z3LpReplay

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ProofIndex
module A = Z3LinearArithmeticAst
module P = Z3LinearArithmeticTheory
module E = Z3LinearArithmeticEmbed
module R = Z3ArithmeticRewrite

let linear_identity (e:expr) : bool =
  match A.comparison e with
  | Some (A.Eq, a, b) -> R.numeric_equivalent a b
  | _ -> false

let lemma_linear_identity_sound (e:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> FStar.Real.real). E.numeric_model i nu) /\
                    Z3ObservationalEquality.boolean_model i /\ eq_sound i /\ linear_identity e)
          (ensures lit_true i rho e) =
  let aux (nu:value -> FStar.Real.real)
    : Lemma (requires E.numeric_model i nu) (ensures lit_true i rho e) =
    match A.comparison e with
    | Some (A.Eq, a, b) ->
      R.lemma_numeric_equivalent a b i nu rho;
      (match e with App _ [_; _] -> () | _ -> ())
    | _ -> ()
  in
  FStar.Classical.exists_elim (lit_true i rho e)
    #(value -> FStar.Real.real) #(fun nu -> E.numeric_model i nu) () (fun nu -> aux nu)

let absolute (n:int) : nat = if n < 0 then -n else n

(* Candidate generation is deliberately outside the soundness argument.
   Every candidate is replayed against the actual native proof formulas. *)
let tightening_coefficients (conclusion:expr) (facts:list expr)
  : option (list A.coefficient) =
  match facts with
  | [context; premise] ->
    if context <> true_expr then None else
    A.prepare_literal (1, 1) true premise >>= (fun p ->
    A.prepare_literal (1, 1) false conclusion >>= (fun q ->
    R.first_nonzero (P.collect p.poly.mono []) >>= (fun (a, e) ->
    let b = R.coefficient e (P.collect q.poly.mono []) in
    if a = 0 || b = 0 || (a > 0) = (b > 0) then None else
    let cs:list A.coefficient =
      [(0, 1); (absolute b * p.poly.denom, 1); (absolute a * q.poly.denom, 1)] in
    Some cs)))
  | _ -> None

let check_tightening (conclusion:expr) (facts:list expr) : bool =
  match tightening_coefficients conclusion facts with
  | None -> false
  | Some cs -> A.check cs conclusion facts

let lemma_tightening_sound (conclusion:expr) (facts:list expr)
                          (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> FStar.Real.real). E.numeric_model i nu) /\
                    Z3ObservationalEquality.boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    check_tightening conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  match tightening_coefficients conclusion facts with
  | None -> ()
  | Some cs -> E.lemma_check_with_numeric_model cs conclusion facts i rho
