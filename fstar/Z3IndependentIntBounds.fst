module Z3IndependentIntBounds

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module D = Z3ExprScope
module B = Z3BoundedBoolEquiv
module LA = Z3LinearArithmeticAst
module AR = Z3SortedArithmetic
module R = Z3ClauseSyntax
module NR = Z3NnfReplay

let equation_sides (e:expr) : option (expr & expr) =
  match e with
  | App f [x; y] -> if f = R.eq_decl LA.int_s then Some (x, y) else None
  | _ -> None

let direct_bound (x y c:expr) : option bool =
  match LA.comparison c with
  | Some (rel, l, r) ->
    if get_sort l <> LA.int_s then None
    else if l = x && r = y then
      if rel = LA.Le then Some true else if rel = LA.Ge then Some false else None
    else if l = y && r = x then
      if rel = LA.Le then Some false else if rel = LA.Ge then Some true else None
    else None
  | None -> None

let check (equation bounds:expr) : bool =
  match equation_sides equation, bounds with
  | Some (x, y), App f [a; b] ->
    NR.shallow equation && NR.shallow bounds && T.classify f = T.Nary B.And &&
    (match direct_bound x y a, direct_bound x y b with
     | Some upper_a, Some upper_b -> upper_a <> upper_b
     | _ -> false)
  | _ -> false

let integer_value (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (e:expr) : GTot int =
  AR.integer s bc model other [] (T.empty_environment (S.signature s)) e

let lemma_equation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (e x y:expr)
  : Lemma (requires D.scoped [] e /\ equation_sides e == Some (x, y))
          (ensures D.scoped [] x /\ D.scoped [] y /\ get_sort x == LA.int_s /\
                   get_sort y == LA.int_s /\
                   (T.truth s bc model other e <==>
                    integer_value s bc model other x == integer_value s bc model other y)) =
  match e with
  | App _ [_; _] ->
    V.lemma_sort_eq (get_sort x) LA.int_s;
    V.lemma_sort_eq (get_sort y) LA.int_s;
    T.lemma_equality s bc model other x y;
    AR.lemma_integer_equality s bc model other [] (T.empty_environment (S.signature s)) x y
  | _ -> ()

let lemma_bound (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (x y c:expr) (upper:bool)
  : Lemma (requires D.scoped [] c /\ direct_bound x y c == Some upper)
          (ensures (T.truth s bc model other c <==>
                    (if upper then integer_value s bc model other x <= integer_value s bc model other y
                     else integer_value s bc model other y <= integer_value s bc model other x))) =
  match LA.comparison c with
  | Some (rel, l, r) ->
    AR.lemma_int_comparison s bc model other [] (T.empty_environment (S.signature s)) c rel l r
  | None -> ()

let lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (equation bounds:expr)
  : Lemma (requires D.scoped [] equation /\ D.scoped [] bounds /\ check equation bounds)
          (ensures T.truth s bc model other equation == T.truth s bc model other bounds) =
  match equation_sides equation, bounds with
  | Some (x, y), App f [a; b] ->
    lemma_equation s bc model other equation x y;
    T.lemma_nary s bc model other f [a; b] B.And;
    T.lemma_truths s bc model other [a; b];
    lemma_bound s bc model other x y a (Some?.v (direct_bound x y a));
    lemma_bound s bc model other x y b (Some?.v (direct_bound x y b))
  | _ -> ()
