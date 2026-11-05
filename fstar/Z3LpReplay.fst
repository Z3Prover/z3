module Z3LpReplay

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ProofIndex
module A = Z3LinearArithmeticAst
module P = Z3LinearArithmeticTheory
module E = Z3LinearArithmeticEmbed
module R = Z3ArithmeticRewrite
module I = Z3IntegerRewrite
module B = Z3BooleanRewrite

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

(* Candidate generation is deliberately outside the soundness argument.
   Every candidate is replayed against the actual native proof formulas. *)
let tightening_coefficients (conclusion:expr) (facts:list expr)
  : option (list A.coefficient) =
  match facts with
  | [context; premise] ->
    if context <> true_expr then None else
    I.implication_coefficients premise conclusion >>= (fun cs -> Some ((0, 1) :: cs))
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

let inferred_bound (conclusion:expr) (facts:list expr) : bool =
  match A.synthesize conclusion facts with
  | Some cs -> A.check cs conclusion facts
  | None -> false

let lemma_inferred_bound (conclusion:expr) (facts:list expr)
                         (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> FStar.Real.real). E.numeric_model i nu) /\
                    Z3ObservationalEquality.boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    inferred_bound conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  match A.synthesize conclusion facts with
  | Some cs -> E.lemma_check_with_numeric_model cs conclusion facts i rho
  | None -> ()

let equality_bounds (conclusion:expr) : option (expr & expr) =
  match A.comparison conclusion with
  | Some (A.Eq, a, b) ->
    let bound name tag =
      App { decl_name = name; domain = [get_sort a; get_sort b]; range = bool_sort;
            interp = Some tag; int_params = [] } [a; b] in
    Some (bound "<=" op_arith_le, bound ">=" op_arith_ge)
  | _ -> None

let bounds_conjunction (lower upper:expr) : expr =
  App (B.connective_decl B.Conjunction [lower; upper]) [lower; upper]

let implied_equality (conclusion:expr) (facts:list expr) : bool =
  match equality_bounds conclusion with
  | Some (lower, upper) ->
    R.split_equation conclusion (bounds_conjunction lower upper) &&
    inferred_bound lower facts && inferred_bound upper facts
  | None -> false

let lemma_implied_equality (conclusion:expr) (facts:list expr)
                           (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> FStar.Real.real). E.numeric_model i nu) /\
                    Z3ObservationalEquality.boolean_model i /\ not_sound i /\ eq_sound i /\
                    or_sound i /\ and_sound i /\ true_sound i /\ false_sound i /\
                    implied_equality conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  match equality_bounds conclusion with
  | Some (lower, upper) ->
    lemma_inferred_bound lower facts i rho;
    lemma_inferred_bound upper facts i rho;
    R.lemma_equivalent_with_numeric_model conclusion (bounds_conjunction lower upper) i rho
  | None -> ()
