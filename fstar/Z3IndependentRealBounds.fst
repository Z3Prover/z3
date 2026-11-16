module Z3IndependentRealBounds

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open FStar.Real
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module D = Z3ExprScope
module B = Z3BoundedBoolEquiv
module LA = Z3LinearArithmeticAst
module RL = Z3SortedReal
module LIN = Z3SortedRealLinear
module RO = Z3SortedRealOrder
module NR = Z3NnfReplay

let check_large_equations (a b:expr) : bool =
  (None? (expression_budget 256 a) || None? (expression_budget 256 b)) &&
  Some? (expression_budget 4096 a) && Some? (expression_budget 4096 b) &&
  LIN.real_equation_equivalent a b

let lemma_large_equations (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (reals:RL.carrier base) (a b:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped [] a /\
                    D.scoped [] b /\ check_large_equations a b)
          (ensures T.evaluate s bc model other a == T.evaluate s bc model other b) =
  LIN.lemma_real_equation_equivalent s bc model other reals [] (T.empty_environment (S.signature s)) a b

let check (equation bounds:expr) : bool =
  match LIN.real_equation equation, bounds with
  | Some (x, y), App f [a; b] ->
    NR.shallow equation && NR.shallow bounds && T.classify f = T.Nary B.And &&
    (match RO.real_bound x y a, RO.real_bound x y b with
     | Some upper_a, Some upper_b -> upper_a <> upper_b
     | _ -> false)
  | _ -> false

let lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (reals:RL.carrier base) (equation bounds:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped [] equation /\
                    D.scoped [] bounds /\ check equation bounds)
          (ensures T.truth s bc model other equation == T.truth s bc model other bounds) =
  match LIN.real_equation equation, bounds with
  | Some (x, y), App f [a; b] ->
    let rho = T.empty_environment (S.signature s) in
    LIN.lemma_comparison s bc model other reals [] rho equation x y LA.Eq;
    RO.lemma_numeric_at_real s bc model other reals [] rho x;
    RO.lemma_numeric_at_real s bc model other reals [] rho y;
    T.lemma_nary s bc model other f [a; b] B.And;
    T.lemma_truths s bc model other [a; b];
    if T.truth s bc model other equation then (
      RO.lemma_real_implied_by_equation s bc model other reals [] rho x y a;
      RO.lemma_real_implied_by_equation s bc model other reals [] rho x y b)
    else if T.truth s bc model other bounds then (
      RO.lemma_real_bound s bc model other reals [] rho x y a
        (Some?.v (RO.real_bound x y a));
      RO.lemma_real_bound s bc model other reals [] rho x y b
        (Some?.v (RO.real_bound x y b)))
  | _ -> ()
