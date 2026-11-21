module Z3LpReplaySyntax

open Z3AstTheory
open Z3OperatorTags
open Z3ClauseSyntax
open Z3ProofIndex
module A = Z3LinearArithmeticAst
module R = Z3ArithmeticSyntax
module I = Z3IntegerRewriteSyntax
module B = Z3BooleanRewriteSyntax

let linear_identity (e:expr) : bool =
  match A.comparison e with
  | Some (A.Eq, a, b) -> R.numeric_equivalent a b
  | _ -> false

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

let inferred_bound (conclusion:expr) (facts:list expr) : bool =
  match A.synthesize conclusion facts with
  | Some cs -> A.check cs conclusion facts
  | None -> false

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

