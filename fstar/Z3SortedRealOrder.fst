module Z3SortedRealOrder

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

(* The Real equality/order atoms of the producer's arith_eq_adapter clauses
   (Z3SortedProof.real_order): the Real mirror of the Int atoms of
   Z3SortedProof (offset, implied_by_equation, bound over a pair (x, y)).
   A separate module on top of Z3SortedRealLinear, so that the checks that
   only decide Real equations (Z3SortedRealLinear.real_equivalent, read by
   Z3NnfReplay) do not carry them. *)

open Z3AstTheory
open Z3ValueTheory
open FStar.Real
module A = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3Definitions
module L = FStar.List.Tot
module RL = Z3SortedReal
module LIN = Z3SortedRealLinear

(* ---------------------------------------------------------------------- *)
(* Real equality/order atoms over a pair (x, y)                             *)
(* ---------------------------------------------------------------------- *)

(* The Real mirror of the Int atoms of the producer's arith_eq_adapter
   clauses (Z3SortedProof.order_clause): x and y are any Real terms (an
   opaque application, a nonlinear product, a quotient, a to_real, a sum),
   read only as their typed scalar values in the one Sorted interpretation
   and matched by expression identity, never linearized. Operators are the
   canonical Real ones, classified by their full declaration (RL.classify:
   interpretation tag, domain, range, numeral parameters), never by name. *)

(* The canonical Real numeral n (that is n/1). *)
let real_numeral (n:int) (e:expr) : bool =
  match e with App k [] -> RL.classify k = RL.Numeral n 1 | _ -> false

let lemma_numeric_at_real (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (reals:RL.carrier base) (scope:list sort)
                          (rho:V.environment base (S.signature s) scope) (e:expr)
  : Lemma (requires get_sort e == A.real_s)
          (ensures RL.numeric_at s bc model other reals scope rho e ==
                   RL.real_at s bc model other reals scope rho e) = ()

let lemma_real_numeral_value (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (reals:RL.carrier base) (scope:list sort)
                             (rho:V.environment base (S.signature s) scope) (n:int) (e:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope e /\ real_numeral n e)
          (ensures get_sort e == A.real_s /\ RL.real_at s bc model other reals scope rho e == of_int n) =
  match e with
  | App k [] -> RL.lemma_real_numeral_at s bc model other reals scope rho k n 1
  | _ -> ()

(* (-1) * y: a canonical binary Real product of the numeral -1 and y. *)
let real_negated_operand (e:expr) : option expr =
  match e with
  | App g [k; y] -> if RL.classify g = RL.Calculate A.Mul && real_numeral (-1) k then Some y else None
  | _ -> None

let lemma_real_negated_operand (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                               (reals:RL.carrier base) (scope:list sort)
                               (rho:V.environment base (S.signature s) scope) (e y:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope e /\ real_negated_operand e == Some y)
          (ensures D.scoped scope y /\ get_sort y == A.real_s /\ get_sort e == A.real_s /\
                   RL.real_at s bc model other reals scope rho e ==
                   0.0R -. RL.real_at s bc model other reals scope rho y) =
  match e with
  | App g [k; _] ->
    RL.lemma_real_binary_at s bc model other reals scope rho g k y A.Mul;
    lemma_real_numeral_value s bc model other reals scope rho (-1) k
  | _ -> ()

(* x - y as a canonical binary Real addition of x and (-1) * y, in either
   operand order (as Z3SortedArithmetic.difference at Int). When both
   operands are negated products, the second is read as (-1) * y. *)
let real_difference (e:expr) : option (expr & expr) =
  match e with
  | App f [a; b] ->
    if RL.classify f <> RL.Calculate A.Add then None
    else (match real_negated_operand b with
          | Some y -> Some (a, y)
          | None -> (match real_negated_operand a with Some y -> Some (b, y) | None -> None))
  | _ -> None

let lemma_real_difference (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (reals:RL.carrier base) (scope:list sort)
                          (rho:V.environment base (S.signature s) scope) (e x y:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope e /\ real_difference e == Some (x, y))
          (ensures D.scoped scope x /\ D.scoped scope y /\ get_sort x == A.real_s /\ get_sort y == A.real_s /\
                   get_sort e == A.real_s /\
                   RL.real_at s bc model other reals scope rho e ==
                   RL.real_at s bc model other reals scope rho x -. RL.real_at s bc model other reals scope rho y) =
  match e with
  | App f [a; b] ->
    RL.lemma_real_binary_at s bc model other reals scope rho f a b A.Add;
    (match real_negated_operand b with
     | Some z -> lemma_real_negated_operand s bc model other reals scope rho b z
     | None -> lemma_real_negated_operand s bc model other reals scope rho a y)
  | _ -> ()

(* The operands l and r of a Real comparison read against the pair (x, y):
   l - r is x - y (Some true) or y - x (Some false), either directly or as a
   difference compared with the numeral 0. *)
let real_offset (x y l r:expr) : option bool =
  if l = x && r = y then Some true
  else if l = y && r = x then Some false
  else if not (real_numeral 0 r) then None
  else match real_difference l with
  | Some (a, b) ->
    if a = x && b = y then Some true
    else if a = y && b = x then Some false
    else None
  | None -> None

let lemma_real_offset (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (reals:RL.carrier base) (scope:list sort)
                      (rho:V.environment base (S.signature s) scope) (x y l r:expr) (sign:bool)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope l /\ D.scoped scope r /\
                    get_sort l == A.real_s /\ real_offset x y l r == Some sign)
          (ensures RL.real_at s bc model other reals scope rho l -. RL.real_at s bc model other reals scope rho r ==
                   (if sign then RL.real_at s bc model other reals scope rho x -. RL.real_at s bc model other reals scope rho y
                    else RL.real_at s bc model other reals scope rho y -. RL.real_at s bc model other reals scope rho x)) =
  if l = x && r = y then ()
  else if l = y && r = x then ()
  else (
    lemma_real_numeral_value s bc model other reals scope rho 0 r;
    match real_difference l with
    | Some (a, b) -> lemma_real_difference s bc model other reals scope rho l a b
    | None -> ())

(* A Real comparison l <= r, l >= r or l = r with l - r = +-(x - y): every
   equal pair x, y satisfies it. *)
let real_implied_by_equation (x y c:expr) : bool =
  match A.comparison c with
  | Some (rel, l, r) ->
    get_sort l = A.real_s && (rel = A.Le || rel = A.Ge || rel = A.Eq) && Some? (real_offset x y l r)
  | None -> false

let lemma_real_implied_by_equation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                   (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                   (reals:RL.carrier base) (scope:list sort)
                                   (rho:V.environment base (S.signature s) scope) (x y c:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope c /\ real_implied_by_equation x y c /\
                    RL.real_at s bc model other reals scope rho x == RL.real_at s bc model other reals scope rho y)
          (ensures T.truth_at s bc model other scope rho c) =
  match A.comparison c with
  | Some (rel, l, r) ->
    LIN.lemma_comparison s bc model other reals scope rho c l r rel;
    lemma_numeric_at_real s bc model other reals scope rho l;
    lemma_numeric_at_real s bc model other reals scope rho r;
    lemma_real_offset s bc model other reals scope rho x y l r (Some?.v (real_offset x y l r))
  | None -> ()

(* A Real comparison read as a bound on x - y: Some true for x - y <= 0,
   Some false for x - y >= 0. Strict comparisons and equations are no bound. *)
let real_bound (x y c:expr) : option bool =
  match A.comparison c with
  | Some (rel, l, r) ->
    if get_sort l <> A.real_s then None
    else (match real_offset x y l r with
          | Some sign -> if rel = A.Le then Some sign else if rel = A.Ge then Some (not sign) else None
          | None -> None)
  | None -> None

let lemma_real_bound (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (reals:RL.carrier base) (scope:list sort)
                     (rho:V.environment base (S.signature s) scope) (x y c:expr) (upper:bool)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope c /\ real_bound x y c == Some upper /\
                    T.truth_at s bc model other scope rho c)
          (ensures (if upper then RL.real_at s bc model other reals scope rho x <=. RL.real_at s bc model other reals scope rho y
                    else RL.real_at s bc model other reals scope rho y <=. RL.real_at s bc model other reals scope rho x)) =
  match A.comparison c with
  | Some (rel, l, r) ->
    LIN.lemma_comparison s bc model other reals scope rho c l r rel;
    lemma_numeric_at_real s bc model other reals scope rho l;
    lemma_numeric_at_real s bc model other reals scope rho r;
    lemma_real_offset s bc model other reals scope rho x y l r (Some?.v (real_offset x y l r))
  | None -> ()
