module Z3SortedRealLinear

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open FStar.Real
module A = Z3LinearArithmeticAst
module P = Z3LinearArithmeticTheory
module E = Z3LinearArithmeticEmbed
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module I = Z3SortedInteger
module AR = Z3SortedArithmetic
module R = Z3ResolutionProofTheory
module D = Z3Definitions
module L = FStar.List.Tot
module RL = Z3SortedReal
module RW = Z3ArithmeticRewrite
module B = Z3BoundedBoolEquiv

(* ---------------------------------------------------------------------- *)
(* Executable classification facts                                          *)
(* ---------------------------------------------------------------------- *)

let rec lemma_real_argument_sorts (args:list expr) (ss:list sort)
  : Lemma (requires sorts_match args ss)
          (ensures L.map get_sort args == ss /\ L.length args == L.length ss /\
                   A.same_sort A.real_s args == RL.real_sorts ss)
          (decreases args) =
  match args, ss with
  | a :: rest, t :: tail -> V.lemma_sort_eq (get_sort a) t; lemma_real_argument_sorts rest tail
  | _, _ -> ()

let rec lemma_real_dummy_sorts (ss:list sort)
  : Lemma (L.map get_sort (S.dummy_fields ss) == ss /\ L.length (S.dummy_fields ss) == L.length ss /\
           A.same_sort A.real_s (S.dummy_fields ss) == RL.real_sorts ss)
          (decreases ss) =
  match ss with [] -> () | _ :: rest -> lemma_real_dummy_sorts rest

let lemma_real_operation (f:func_decl) (args:list expr) (op:A.operation)
  : Lemma (requires f.range == A.real_s /\ sorts_match args f.domain /\ A.operation_of f args == Some op)
          (ensures (op == A.Add \/ op == A.Mul \/ op == A.Sub ==>
                      RL.classify f == RL.Calculate op /\ RL.real_sorts f.domain) /\
                   (op == A.Div ==> RL.classify f == RL.Divide /\ f.domain == [A.real_s; A.real_s]) /\
                   (op == A.ToReal ==> RL.classify f == RL.ToReal /\ f.domain == [A.int_s])) =
  lemma_real_argument_sorts args f.domain;
  lemma_real_dummy_sorts f.domain;
  I.lemma_argument_sorts args f.domain;
  I.lemma_dummy_sorts f.domain;
  match args with
  | [] -> ()
  | [_] -> ()
  | [_; _] -> ()
  | _ -> ()

let lemma_real_numeral (f:func_decl) (n:int) (d:pos)
  : Lemma (requires f.range == A.real_s /\ A.numeral (App f []) == Some (n, d))
          (ensures RL.classify f == RL.Numeral n d) = ()

let lemma_real_compare (f:func_decl) (a b:expr) (r:A.relation)
  : Lemma (requires A.comparison (App f [a; b]) == Some (r, a, b) /\ get_sort a == A.real_s /\ r <> A.Eq)
          (ensures RL.classify f == RL.Compare r) = ()

(* ---------------------------------------------------------------------- *)
(* Argument values                                                          *)
(* ---------------------------------------------------------------------- *)

let rec lemma_integer_arguments (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                (reals:RL.carrier base) (scope:list sort)
                                (rho:V.environment base (S.signature s) scope)
                                (args:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss /\ I.integer_sorts ss)
          (ensures L.map of_int (I.numbers s model.T.integers ss
                     (T.evaluate_arguments_at s bc model other scope rho args ss)) ==
                   L.map (RL.numeric_valuation s bc model other reals scope rho) args)
          (decreases args) =
  match args, ss with
  | a :: rest, t :: tail ->
    V.lemma_sort_eq (get_sort a) t;
    lemma_integer_arguments s bc model other reals scope rho rest tail
  | _, _ -> ()

let rec lemma_real_arguments (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (reals:RL.carrier base) (scope:list sort)
                             (rho:V.environment base (S.signature s) scope)
                             (args:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss /\ RL.real_sorts ss)
          (ensures RL.real_values s reals ss (T.evaluate_arguments_at s bc model other scope rho args ss) ==
                   L.map (RL.numeric_valuation s bc model other reals scope rho) args)
          (decreases args) =
  match args, ss with
  | a :: rest, t :: tail ->
    V.lemma_sort_eq (get_sort a) t;
    lemma_real_arguments s bc model other reals scope rho rest tail
  | _, _ -> ()

let lemma_rational (n:int) (d:pos) : Lemma (of_int d *. (of_int n /. of_int d) == of_int n) = ()

(* ---------------------------------------------------------------------- *)
(* The linear normal form (A.linearize) against the typed numeric valuation *)
(* (Int atoms read through the integer carrier, Real atoms through the Real *)
(* carrier), at every scope and environment                                 *)
(* ---------------------------------------------------------------------- *)

(* An Int application: the existing Int calculation, read into the one
   numeric valuation. *)
let lemma_linearize_integer_application (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                        (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                        (reals:RL.carrier base) (scope:list sort)
                                        (rho:V.environment base (S.signature s) scope)
                                        (f:func_decl) (args:list expr) (op:A.operation) (ps:list A.poly) (p:A.poly)
  : Lemma (requires D.scoped scope (App f args) /\ f.range == A.int_s /\
                    A.operation_of f args == Some op /\ A.combine op ps (App f args) == Some p /\
                    E.denotations ps (L.map (RL.numeric_valuation s bc model other reals scope rho) args)
                      (RL.numeric_valuation s bc model other reals scope rho))
          (ensures E.denotes p (RL.numeric_at s bc model other reals scope rho (App f args))
                     (RL.numeric_valuation s bc model other reals scope rho)) =
  let v = RL.numeric_valuation s bc model other reals scope rho in
  let xs = L.map v args in
  I.lemma_calculate f args op;
  AR.lemma_application s bc model other scope rho f args;
  lemma_integer_arguments s bc model other reals scope rho args f.domain;
  let ns = I.numbers s model.T.integers f.domain
             (T.evaluate_arguments_at s bc model other scope rho args f.domain) in
  AR.lemma_calculation op ns;
  match op with
  | A.Add -> E.lemma_sum ps xs v
  | A.Mul -> (match P.product ps with Some q -> E.lemma_product ps xs q v | None -> ())
  | A.Sub -> E.lemma_subtract ps xs p v
  | _ -> ()

(* A Real sum, product or difference, read through the Real laws. *)
let lemma_linearize_real_calculation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                     (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                     (reals:RL.carrier base) (scope:list sort)
                                     (rho:V.environment base (S.signature s) scope)
                                     (f:func_decl) (args:list expr) (op:A.operation) (ps:list A.poly) (p:A.poly)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope (App f args) /\ f.range == A.real_s /\
                    (op == A.Add \/ op == A.Mul \/ op == A.Sub) /\
                    A.operation_of f args == Some op /\ A.combine op ps (App f args) == Some p /\
                    E.denotations ps (L.map (RL.numeric_valuation s bc model other reals scope rho) args)
                      (RL.numeric_valuation s bc model other reals scope rho))
          (ensures E.denotes p (RL.numeric_at s bc model other reals scope rho (App f args))
                     (RL.numeric_valuation s bc model other reals scope rho)) =
  let v = RL.numeric_valuation s bc model other reals scope rho in
  let xs = L.map v args in
  lemma_real_operation f args op;
  RL.lemma_evaluate_real_at s bc model other scope rho f args;
  let ys = T.evaluate_arguments_at s bc model other scope rho args f.domain in
  assert (RL.real_meaning s bc model.T.integers reals f ys (T.application s bc model other f ys));
  lemma_real_arguments s bc model other reals scope rho args f.domain;
  match op with
  | A.Add -> E.lemma_sum ps xs v
  | A.Mul -> (match P.product ps with Some q -> E.lemma_product ps xs q v | None -> ())
  | _ -> E.lemma_subtract ps xs p v

(* The quotient value of a Real division by a nonzero divisor, in the one
   numeric valuation. *)
let lemma_quotient_value (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (reals:RL.carrier base) (scope:list sort)
                         (rho:V.environment base (S.signature s) scope)
                         (f:func_decl) (a b:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope (App f [a; b]) /\
                    RL.classify f == RL.Divide)
          (ensures ~(RL.numeric_at s bc model other reals scope rho b == 0.0R) ==>
                   RL.numeric_at s bc model other reals scope rho (App f [a; b]) *.
                   RL.numeric_at s bc model other reals scope rho b ==
                   RL.numeric_at s bc model other reals scope rho a) =
  RL.lemma_real_divide_at s bc model other reals scope rho f a b

(* A / by a constant polynomial with a nonzero constant is that scaling;
   otherwise the quotient is an opaque atom. *)
let lemma_quotient_denotes (pa pb p:A.poly) (e:expr) (x y:real) (v:expr -> real)
  : Lemma (requires A.combine A.Div [pa; pb] e == Some p /\ E.denotes pa x v /\ E.denotes pb y v /\
                    (~(y == 0.0R) ==> v e *. y == x))
          (ensures E.denotes p (v e) v) =
  match A.divide pa pb with
  | Some q -> E.lemma_divide pa pb q x y (v e) v
  | None -> ()

(* A Real quotient by a constant polynomial with a nonzero constant; x/0 has
   no law and stays an opaque atom. *)
let lemma_linearize_real_division (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                  (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                  (reals:RL.carrier base) (scope:list sort)
                                  (rho:V.environment base (S.signature s) scope)
                                  (f:func_decl) (args:list expr) (ps:list A.poly) (p:A.poly)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope (App f args) /\ f.range == A.real_s /\
                    A.operation_of f args == Some A.Div /\ A.combine A.Div ps (App f args) == Some p /\
                    E.denotations ps (L.map (RL.numeric_valuation s bc model other reals scope rho) args)
                      (RL.numeric_valuation s bc model other reals scope rho))
          (ensures E.denotes p (RL.numeric_at s bc model other reals scope rho (App f args))
                     (RL.numeric_valuation s bc model other reals scope rho)) =
  let v = RL.numeric_valuation s bc model other reals scope rho in
  lemma_real_operation f args A.Div;
  match args, ps with
  | [a; b], [pa; pb] ->
    lemma_quotient_value s bc model other reals scope rho f a b;
    lemma_quotient_denotes pa pb p (App f args) (v a) (v b) v
  | _, _ -> ()

let lemma_linearize_to_real (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                            (reals:RL.carrier base) (scope:list sort)
                            (rho:V.environment base (S.signature s) scope)
                            (f:func_decl) (args:list expr) (ps:list A.poly) (p:A.poly)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope (App f args) /\ f.range == A.real_s /\
                    A.operation_of f args == Some A.ToReal /\ A.combine A.ToReal ps (App f args) == Some p /\
                    E.denotations ps (L.map (RL.numeric_valuation s bc model other reals scope rho) args)
                      (RL.numeric_valuation s bc model other reals scope rho))
          (ensures E.denotes p (RL.numeric_at s bc model other reals scope rho (App f args))
                     (RL.numeric_valuation s bc model other reals scope rho)) =
  lemma_real_operation f args A.ToReal;
  match args with
  | [a] -> RL.lemma_to_real_at s bc model other reals scope rho f a
  | _ -> ()

(* A Real application: + - * read through the Real laws, / by a nonzero
   constant polynomial, to_real through the integer carrier. *)
let lemma_linearize_real_application (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                     (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                     (reals:RL.carrier base) (scope:list sort)
                                     (rho:V.environment base (S.signature s) scope)
                                     (f:func_decl) (args:list expr) (op:A.operation) (ps:list A.poly) (p:A.poly)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope (App f args) /\ f.range == A.real_s /\
                    A.operation_of f args == Some op /\ A.combine op ps (App f args) == Some p /\
                    E.denotations ps (L.map (RL.numeric_valuation s bc model other reals scope rho) args)
                      (RL.numeric_valuation s bc model other reals scope rho))
          (ensures E.denotes p (RL.numeric_at s bc model other reals scope rho (App f args))
                     (RL.numeric_valuation s bc model other reals scope rho)) =
  match op with
  | A.Div -> lemma_linearize_real_division s bc model other reals scope rho f args ps p
  | A.ToReal -> lemma_linearize_to_real s bc model other reals scope rho f args ps p
  | _ -> lemma_linearize_real_calculation s bc model other reals scope rho f args op ps p

let lemma_linearize_numeral (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                            (reals:RL.carrier base) (scope:list sort)
                            (rho:V.environment base (S.signature s) scope)
                            (f:func_decl) (n:int) (d:pos)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope (App f []) /\
                    A.numeral (App f []) == Some (n, d))
          (ensures E.denotes (P.constant n d) (RL.numeric_at s bc model other reals scope rho (App f []))
                     (RL.numeric_valuation s bc model other reals scope rho)) =
  if f.range = A.int_s then AR.lemma_application s bc model other scope rho f []
  else (
    lemma_real_numeral f n d;
    RL.lemma_real_numeral_at s bc model other reals scope rho f n d;
    lemma_rational n d)

let rec lemma_linearize (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (reals:RL.carrier base) (scope:list sort)
                        (rho:V.environment base (S.signature s) scope)
                        (fuel:nat) (e:expr) (p:A.poly)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope e /\ A.linearize fuel e == Some p)
          (ensures E.denotes p (RL.numeric_at s bc model other reals scope rho e)
                     (RL.numeric_valuation s bc model other reals scope rho))
          (decreases %[fuel; 0]) =
  match A.numeral e with
  | Some (n, d) ->
    (match e with
     | App f [] -> lemma_linearize_numeral s bc model other reals scope rho f n d
     | _ -> ())
  | None ->
    (match e with
     | App f args ->
       (match A.operation_of f args with
        | None -> ()
        | Some op ->
          A.lemma_linearize_application fuel f args op;
          lemma_linearize_arguments s bc model other reals scope rho (fuel - 1) args;
          let ps = Some?.v (A.linearize_args (fuel - 1) args) in
          if f.range = A.int_s
          then lemma_linearize_integer_application s bc model other reals scope rho f args op ps p
          else lemma_linearize_real_application s bc model other reals scope rho f args op ps p)
     | _ -> ())


and lemma_linearize_arguments (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (reals:RL.carrier base) (scope:list sort)
                              (rho:V.environment base (S.signature s) scope)
                              (fuel:nat) (args:list expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped_args scope args /\
                    Some? (A.linearize_args fuel args))
          (ensures E.denotations (Some?.v (A.linearize_args fuel args))
                     (L.map (RL.numeric_valuation s bc model other reals scope rho) args)
                     (RL.numeric_valuation s bc model other reals scope rho))
          (decreases %[fuel; L.length args + 1]) =
  match args with
  | a :: rest ->
    lemma_linearize s bc model other reals scope rho fuel a (Some?.v (A.linearize fuel a));
    lemma_linearize_arguments s bc model other reals scope rho fuel rest
  | [] -> ()

(* ---------------------------------------------------------------------- *)
(* Comparison literals (A.comparison, A.literal) at Int or Real             *)
(* ---------------------------------------------------------------------- *)

let lemma_comparison (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (reals:RL.carrier base) (scope:list sort)
                     (rho:V.environment base (S.signature s) scope)
                     (e a b:expr) (r:A.relation)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope e /\ A.comparison e == Some (r, a, b))
          (ensures D.scoped scope a /\ D.scoped scope b /\ get_sort a == get_sort b /\
                   (T.truth_at s bc model other scope rho e <==>
                    E.numeric_relation r (RL.numeric_at s bc model other reals scope rho a)
                                         (RL.numeric_at s bc model other reals scope rho b))) =
  match e with
  | App f [x; y] ->
    V.lemma_sort_eq (get_sort x) (get_sort a);
    V.lemma_sort_eq (get_sort y) (get_sort a);
    if get_sort a = A.int_s then AR.lemma_comparison s bc model other scope rho e a b r
    else if r = A.Eq then RL.lemma_real_equality_at s bc model other reals scope rho a b
    else (
      lemma_real_compare f a b r;
      RL.lemma_real_comparison_at s bc model other reals scope rho f a b r)
  | _ -> ()

let rec lemma_literal (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (reals:RL.carrier base) (scope:list sort)
                      (rho:V.environment base (S.signature s) scope)
                      (fuel:nat) (positive:bool) (e:expr) (p:bool) (rel:A.relation) (a b:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope e /\
                    A.literal fuel positive e == Some (p, rel, a, b) /\
                    (if positive then T.truth_at s bc model other scope rho e
                     else ~(T.truth_at s bc model other scope rho e)))
          (ensures D.scoped scope a /\ D.scoped scope b /\ get_sort a == get_sort b /\
                   E.parsed_holds p rel (RL.numeric_at s bc model other reals scope rho a)
                                        (RL.numeric_at s bc model other reals scope rho b))
          (decreases fuel) =
  match e with
  | App f [q] ->
    V.lemma_sort_eq (get_sort q) bool_sort;
    T.lemma_evaluate_core_at s bc model other scope rho f [q];
    lemma_literal s bc model other reals scope rho (fuel - 1) (not positive) q p rel a b
  | _ -> lemma_comparison s bc model other reals scope rho e a b rel

(* One weighted Farkas contribution (A.prepare_literal) holds in the typed
   numeric valuation: the Int strict-bound adjustment is applied exactly when
   the literal compares Int terms; Real strict literals stay strict. *)
let lemma_prepare_literal (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (reals:RL.carrier base) (scope:list sort)
                          (rho:V.environment base (S.signature s) scope)
                          (c:A.coefficient) (positive:bool) (e:expr) (out:A.contribution)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope e /\
                    A.prepare_literal c positive e == Some out /\
                    (if positive then T.truth_at s bc model other scope rho e
                     else ~(T.truth_at s bc model other scope rho e)))
          (ensures P.holds out (RL.numeric_valuation s bc model other reals scope rho)) =
  if fst c = 0 then ()
  else
    let p, rel, a, b = Some?.v (A.literal 16 positive e) in
    lemma_literal s bc model other reals scope rho 16 positive e p rel a b;
    let pa = Some?.v (A.linearize 256 a) in
    let pb = Some?.v (A.linearize 256 b) in
    lemma_linearize s bc model other reals scope rho 256 a pa;
    lemma_linearize s bc model other reals scope rho 256 b pb;
    E.lemma_weighted c p rel (get_sort a = A.int_s) pa pb
      (RL.numeric_at s bc model other reals scope rho a) (RL.numeric_at s bc model other reals scope rho b)
      (AR.integer s bc model other scope rho a) (AR.integer s bc model other scope rho b)
      (RL.numeric_valuation s bc model other reals scope rho)

(* ---------------------------------------------------------------------- *)
(* Real rewrite equivalence with the existing Z3ArithmeticRewrite checks    *)
(* (constraint_of, boolean_equivalent, numeric_equivalent, commuted_product)*)
(* ---------------------------------------------------------------------- *)

let lemma_constraint_of_comparison (fuel:nat) (positive:bool) (e a b:expr) (r:A.relation)
                                   (p:A.contribution)
  : Lemma (requires ~(e = R.true_expr || e = R.false_expr) /\
                    A.comparison e == Some (r, a, b) /\ RW.constraint_of fuel positive e == Some p)
          (ensures r <> A.Eq /\ Some? (A.linearize 64 a) /\ Some? (A.linearize 64 b) /\
                   p.P.poly == fst (A.oriented positive r (Some?.v (A.linearize 64 a))
                                                         (Some?.v (A.linearize 64 b))) /\
                   p.P.strict == snd (A.oriented positive r (Some?.v (A.linearize 64 a))
                                                            (Some?.v (A.linearize 64 b)))) =
  ()

let lemma_oriented_constraint (positive:bool) (r:A.relation) (pa pb:A.poly) (p:A.contribution)
                              (x y:real) (v:expr -> real)
  : Lemma (requires p.P.poly == fst (A.oriented positive r pa pb) /\
                    E.denotes pa x v /\ E.denotes pb y v)
          (ensures P.value p.P.poly v == of_int p.P.poly.P.denom *. E.difference positive r x y) =
  E.lemma_oriented positive r pa pb x y v

let rec lemma_constraint (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (reals:RL.carrier base) (scope:list sort)
                         (rho:V.environment base (S.signature s) scope)
                         (fuel:nat) (positive:bool) (e:expr) (p:A.contribution)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope e /\ get_sort e == bool_sort /\
                    RW.constraint_of fuel positive e == Some p)
          (ensures P.holds p (RL.numeric_valuation s bc model other reals scope rho) <==>
                   (if positive then T.truth_at s bc model other scope rho e
                    else ~(T.truth_at s bc model other scope rho e)))
          (decreases fuel) =
  if e = R.true_expr || e = R.false_expr then
    (match e with App f [] -> T.lemma_evaluate_core_at s bc model other scope rho f [] | _ -> ())
  else match e with
  | App f [a] ->
    lemma_constraint s bc model other reals scope rho (fuel - 1) (not positive) a p;
    T.lemma_evaluate_core_at s bc model other scope rho f [a]
  | _ ->
    (match A.comparison e with
     | Some (r, a, b) ->
       lemma_constraint_of_comparison fuel positive e a b r p;
       let pa = Some?.v (A.linearize 64 a) in
       let pb = Some?.v (A.linearize 64 b) in
       lemma_linearize s bc model other reals scope rho 64 a pa;
       lemma_linearize s bc model other reals scope rho 64 b pb;
       let x = RL.numeric_at s bc model other reals scope rho a in
       let y = RL.numeric_at s bc model other reals scope rho b in
       let v = RL.numeric_valuation s bc model other reals scope rho in
       lemma_oriented_constraint positive r pa pb p x y v;
       RW.lemma_scaled_relation positive r p.P.poly.P.denom (P.value p.P.poly v) x y;
       lemma_comparison s bc model other reals scope rho e a b r
     | None -> ())

(* A Real equation: the canonical equality at Real (Z3LinearArithmeticAst.comparison
   checks the exact declaration and equal operand sorts), with its two sides. *)
let real_equation (e:expr) : option (expr & expr) =
  match A.comparison e with
  | Some (A.Eq, x, y) -> if get_sort x = A.real_s then Some (x, y) else None
  | _ -> None

(* Two Real equations whose difference polynomials are the same, opposite or
   proportional by a nonzero factor (Z3ArithmeticRewrite.equation_equivalent,
   read only on Real equations; atoms stay opaque, products of non-constants
   included), and a Real equation of constants decided as true or false
   (Z3ArithmeticRewrite.constant_equation). *)
let real_equation_equivalent (a b:expr) : bool =
  Some? (real_equation a) && Some? (real_equation b) && RW.equation_equivalent a b

let real_constant_equation (e result:expr) : bool =
  Some? (real_equation e) && RW.constant_equation e result

let real_equivalent (a b:expr) : bool =
  Some? (expression_budget 256 a) && Some? (expression_budget 256 b) &&
  ((get_sort a = A.real_s && get_sort b = A.real_s &&
    (RW.numeric_equivalent a b || RW.commuted_product a = Some b)) ||
   RW.boolean_equivalent a b ||
   real_equation_equivalent a b || real_constant_equation a b || real_constant_equation b a)

let lemma_commuted_product (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (reals:RL.carrier base) (scope:list sort)
                           (rho:V.environment base (S.signature s) scope)
                           (a b:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope a /\ D.scoped scope b /\
                    get_sort a == A.real_s /\ RW.commuted_product a == Some b)
          (ensures RL.real_at s bc model other reals scope rho a == RL.real_at s bc model other reals scope rho b) =
  match a with
  | App f [x; y] ->
    lemma_real_operation f [x; y] A.Mul;
    RL.lemma_real_binary_at s bc model other reals scope rho f x y A.Mul;
    RL.lemma_real_binary_at s bc model other reals scope rho f y x A.Mul
  | _ -> ()

(* x = y exactly when x + (0 - y) = 0; the two facts of lemma_real_equation
   combined by linear arithmetic alone. *)
let lemma_equation_zero (t:bool) (x y pv:real)
  : Lemma (requires (t <==> x == y) /\ (pv == 0.0R <==> x +. (0.0R -. y) == 0.0R))
          (ensures t <==> pv == 0.0R) = ()

(* A Real equation e is true exactly when its difference polynomial (the
   linear normal form of lhs - rhs, RW.equation_of) is zero, at every scope
   and environment, read through the one numeric valuation. *)
let lemma_real_equation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (reals:RL.carrier base) (scope:list sort)
                        (rho:V.environment base (S.signature s) scope)
                        (e:expr) (p:A.poly)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope e /\ Some? (real_equation e) /\
                    RW.equation_of e == Some p)
          (ensures T.truth_at s bc model other scope rho e <==>
                   P.value p (RL.numeric_valuation s bc model other reals scope rho) == 0.0R) =
  match A.comparison e with
  | Some (A.Eq, a, b) ->
    lemma_comparison s bc model other reals scope rho e a b A.Eq;
    let pa = Some?.v (A.linearize 64 a) in
    let pb = Some?.v (A.linearize 64 b) in
    let x = RL.numeric_at s bc model other reals scope rho a in
    let y = RL.numeric_at s bc model other reals scope rho b in
    let v = RL.numeric_valuation s bc model other reals scope rho in
    lemma_linearize s bc model other reals scope rho 64 a pa;
    lemma_linearize s bc model other reals scope rho 64 b pb;
    E.lemma_denotes_negative pb y v;
    E.lemma_denotes_add pa (P.scale (-1) 1 pb) x (0.0R -. y) v;
    RW.lemma_denotes_zero p (x +. (0.0R -. y)) v;
    lemma_equation_zero (T.truth_at s bc model other scope rho e) x y (P.value p v)
  | _ -> ()

let lemma_real_equation_equivalent (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                   (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                   (reals:RL.carrier base) (scope:list sort)
                                   (rho:V.environment base (S.signature s) scope)
                                   (a b:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope a /\ D.scoped scope b /\
                    real_equation_equivalent a b)
          (ensures T.evaluate_at s bc model other scope rho a == T.evaluate_at s bc model other scope rho b) =
  let p = Some?.v (RW.equation_of a) in
  let q = Some?.v (RW.equation_of b) in
  let v = RL.numeric_valuation s bc model other reals scope rho in
  lemma_real_equation s bc model other reals scope rho a p;
  lemma_real_equation s bc model other reals scope rho b q;
  RW.lemma_equation_polynomials p q v;
  T.lemma_boolean s bc (T.evaluate_at s bc model other scope rho a);
  T.lemma_boolean s bc (T.evaluate_at s bc model other scope rho b)

(* A Real equation whose monomials all cancel has the constant value of its
   difference polynomial: it is true exactly for the zero constant, which is
   the canonical `true` or `false` the rewrite names. *)
let lemma_real_constant_equation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                 (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                 (reals:RL.carrier base) (scope:list sort)
                                 (rho:V.environment base (S.signature s) scope)
                                 (e result:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope e /\ D.scoped scope result /\
                    real_constant_equation e result)
          (ensures T.evaluate_at s bc model other scope rho e == T.evaluate_at s bc model other scope rho result) =
  let p = Some?.v (RW.equation_of e) in
  let v = RL.numeric_valuation s bc model other reals scope rho in
  lemma_real_equation s bc model other reals scope rho e p;
  P.lemma_collect p.mono [] v;
  P.lemma_all_zero (P.collect p.mono []) v;
  (match result with
   | App f [] -> T.lemma_evaluate_core_at s bc model other scope rho f []
   | _ -> ());
  T.lemma_boolean s bc (T.evaluate_at s bc model other scope rho e);
  T.lemma_boolean s bc (T.evaluate_at s bc model other scope rho result)

(* A Real rewrite leaf accepted by real_equivalent is a semantic identity at
   every scope and environment of the Sorted interpretation. *)
let lemma_real_equivalent (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (reals:RL.carrier base) (scope:list sort)
                          (rho:V.environment base (S.signature s) scope)
                          (a b:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped scope a /\ D.scoped scope b /\
                    real_equivalent a b)
          (ensures T.evaluate_at s bc model other scope rho a == T.evaluate_at s bc model other scope rho b) =
  let v = RL.numeric_valuation s bc model other reals scope rho in
  if get_sort a = A.real_s && get_sort b = A.real_s &&
     (RW.numeric_equivalent a b || RW.commuted_product a = Some b) then (
    (if RW.numeric_equivalent a b then (
      let p = Some?.v (A.linearize 64 a) in
      let q = Some?.v (A.linearize 64 b) in
      lemma_linearize s bc model other reals scope rho 64 a p;
      lemma_linearize s bc model other reals scope rho 64 b q;
      RW.lemma_same_polynomial p q (v a) (v b) v)
     else lemma_commuted_product s bc model other reals scope rho a b);
    RL.lemma_real_injective s reals (T.evaluate_at s bc model other scope rho a)
                                    (T.evaluate_at s bc model other scope rho b))
  else if RW.boolean_equivalent a b then (
    let p = Some?.v (RW.constraint_of 16 true a) in
    let q = Some?.v (RW.constraint_of 16 true b) in
    lemma_constraint s bc model other reals scope rho 16 true a p;
    lemma_constraint s bc model other reals scope rho 16 true b q;
    RW.lemma_same_constraint p q v;
    T.lemma_boolean s bc (T.evaluate_at s bc model other scope rho a);
    T.lemma_boolean s bc (T.evaluate_at s bc model other scope rho b))
  else if real_equation_equivalent a b then
    lemma_real_equation_equivalent s bc model other reals scope rho a b
  else if real_constant_equation a b then
    lemma_real_constant_equation s bc model other reals scope rho a b
  else
    lemma_real_constant_equation s bc model other reals scope rho b a

(* ---------------------------------------------------------------------- *)
(* Typed Farkas replay over Int and Real literals                           *)
(* ---------------------------------------------------------------------- *)

let rec numeric_inputs (xs:list (bool & expr)) (cs:list A.coefficient) : Tot bool (decreases xs) =
  match xs, cs with
  | [], [] -> true
  | (_, e) :: rest, _ :: tail -> D.scoped [] e && get_sort e = bool_sort && numeric_inputs rest tail
  | _, _ -> false

let check_numeric_contradiction (s:S.checked_schema) (xs:list (bool & expr)) (cs:list A.coefficient) : bool =
  RL.real_primitive s && Some? (arguments_budget 4096 (L.map snd xs)) && numeric_inputs xs cs &&
  (match A.prepare xs cs with Some ps -> P.accepts ps | None -> false)

let rec lemma_prepare (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (reals:RL.carrier base) (xs:list (bool & expr)) (cs:list A.coefficient)
                      (ps:list A.contribution)
  : Lemma (requires RL.real_laws s bc model other reals /\ numeric_inputs xs cs /\ A.prepare xs cs == Some ps /\
                    AR.assumptions_hold s bc model other xs)
          (ensures P.all_hold ps (RL.numeric_valuation s bc model other reals [] (T.empty_environment (S.signature s))))
          (decreases xs) =
  match xs, cs with
  | (positive, e) :: rest, c :: tail ->
    lemma_prepare_literal s bc model other reals [] (T.empty_environment (S.signature s)) c positive e
      (Some?.v (A.prepare_literal c positive e));
    lemma_prepare s bc model other reals rest tail (Some?.v (A.prepare rest tail))
  | _, _ -> ()

let lemma_check_numeric_contradiction (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                      (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                      (reals:RL.carrier base) (xs:list (bool & expr)) (cs:list A.coefficient)
  : Lemma (requires RL.real_laws s bc model other reals /\ check_numeric_contradiction s xs cs /\
                    AR.assumptions_hold s bc model other xs)
          (ensures False) =
  let ps = Some?.v (A.prepare xs cs) in
  lemma_prepare s bc model other reals xs cs ps;
  P.lemma_accepts_sound ps (RL.numeric_valuation s bc model other reals [] (T.empty_environment (S.signature s)))

(* ---------------------------------------------------------------------- *)
(* Real strictness                                                          *)
(* ---------------------------------------------------------------------- *)

let rec any_strict (ps:list A.contribution) : Tot bool (decreases ps) =
  match ps with [] -> false | p :: rest -> p.P.strict || any_strict rest

let rec lemma_combined_strict (ps:list A.contribution)
  : Lemma (snd (P.combined ps) == any_strict ps) (decreases ps) =
  match ps with [] -> () | _ :: rest -> lemma_combined_strict rest

(* A certificate whose combined polynomial has a nonpositive constant (in
   particular the zero polynomial) is accepted only through a strict
   contribution. *)
let lemma_zero_polynomial_needs_strict (ps:list A.contribution)
  : Lemma (requires P.accepts ps /\ (fst (P.combined ps)).P.cst <= 0)
          (ensures any_strict ps) =
  lemma_combined_strict ps

(* A zero weight contributes the non-strict zero polynomial, whatever the
   literal; it can never supply strictness. *)
let lemma_zero_weight (d:pos) (positive:bool) (e:expr)
  : Lemma (A.prepare_literal (0, d) positive e == Some ({ P.poly = P.zero; P.strict = false })) = ()

(* A strict contribution comes from a nonzero weight on a strict comparison of
   non-Int terms (a strict Int literal is rounded and becomes non-strict), and
   it is the oriented difference scaled by the positive weight |n|. *)
let lemma_strict_contribution (c:A.coefficient) (positive:bool) (e:expr) (out:A.contribution)
  : Lemma (requires A.prepare_literal c positive e == Some out /\ out.P.strict)
          (ensures fst c <> 0 /\ Some? (A.literal 16 positive e) /\
                   (let (p, rel, a, b) = Some?.v (A.literal 16 positive e) in
                    get_sort a <> A.int_s /\ rel <> A.Eq /\
                    snd (A.oriented p rel (Some?.v (A.linearize 256 a)) (Some?.v (A.linearize 256 b))) /\
                    out.P.poly == P.scale (if fst c > 0 then fst c else - (fst c)) (snd c)
                                    (fst (A.oriented p rel (Some?.v (A.linearize 256 a))
                                                           (Some?.v (A.linearize 256 b)))))) = ()

let strict_literal (c:A.coefficient) (positive:bool) (e:expr) : bool =
  fst c <> 0 &&
  (match A.literal 16 positive e with
   | Some (p, rel, a, _) ->
     get_sort a <> A.int_s && rel <> A.Eq && (if p then rel = A.Lt || rel = A.Gt else rel = A.Le || rel = A.Ge)
   | None -> false)

let rec strict_sources (xs:list (bool & expr)) (cs:list A.coefficient) : Tot bool (decreases xs) =
  match xs, cs with
  | (positive, e) :: rest, c :: tail -> strict_literal c positive e || strict_sources rest tail
  | _, _ -> false

let rec lemma_strict_sources (xs:list (bool & expr)) (cs:list A.coefficient) (ps:list A.contribution)
  : Lemma (requires A.prepare xs cs == Some ps /\ any_strict ps) (ensures strict_sources xs cs) (decreases xs) =
  match xs, cs with
  | (positive, e) :: rest, c :: tail ->
    let out = Some?.v (A.prepare_literal c positive e) in
    if out.P.strict then lemma_strict_contribution c positive e out
    else lemma_strict_sources rest tail (Some?.v (A.prepare rest tail))
  | _, _ -> ()

(* Real strictness, per literal: a certificate whose combined polynomial has a
   non-positive constant (the zero polynomial in particular) is accepted only
   if some literal with a NONZERO weight is a strict comparison of non-Int
   terms. Zero weights and (rounded) Int literals never supply strictness. *)
let lemma_zero_contradiction_needs_weighted_strict (xs:list (bool & expr)) (cs:list A.coefficient)
                                                   (ps:list A.contribution)
  : Lemma (requires A.prepare xs cs == Some ps /\ P.accepts ps /\ (fst (P.combined ps)).P.cst <= 0)
          (ensures strict_sources xs cs) =
  lemma_zero_polynomial_needs_strict ps;
  lemma_strict_sources xs cs ps

let refutes (s:S.checked_schema) (facts:list expr) (conclusion:expr) : bool =
  let inputs = A.assumptions conclusion facts in
  if L.length inputs > 32 then false
  else if None? (arguments_budget 4096 (L.map snd inputs)) then false
  else match A.synthesize conclusion facts with
  | Some cs -> check_numeric_contradiction s inputs cs
  | None -> false

let rec lemma_synthesis_assumptions (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                   (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                   (facts lits:list expr)
  : Lemma (requires T.truths s bc model other facts /\
                    not (B.geval_args (T.truth s bc model other) B.Or (L.map B.Atom lits)))
          (ensures AR.assumptions_hold s bc model other
            (L.append (L.map A.positive_literal facts) (L.map A.negative_literal lits)))
          (decreases %[facts; lits]) =
  match facts with
  | _ :: rest -> lemma_synthesis_assumptions s bc model other rest lits
  | [] -> (match lits with [] -> () | _ :: rest -> lemma_synthesis_assumptions s bc model other [] rest)

let lemma_refutes (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (reals:RL.carrier base) (facts:list expr) (conclusion:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    refutes s facts conclusion /\
                    not (B.geval_args (T.truth s bc model other) B.Or
                           (L.map B.Atom (R.formula_clause conclusion))))
          (ensures False) =
  lemma_synthesis_assumptions s bc model other facts (R.formula_clause conclusion);
  lemma_check_numeric_contradiction s bc model other reals
    (A.assumptions conclusion facts) (Some?.v (A.synthesize conclusion facts))

let equality_bound (lower:bool) (a b:expr) : expr =
  App (if lower then RL.real_le_decl else RL.real_ge_decl) [a; b]

let implied_equality (s:S.checked_schema) (facts:list expr) (a b:expr) : bool =
  if not (RL.real_primitive s) || L.length facts > 30 then false
  else if None? (arguments_budget 4096 (a :: b :: facts)) then false
  else get_sort a = A.real_s && get_sort b = A.real_s && D.scoped [] a && D.scoped [] b &&
       refutes s facts (equality_bound true a b) && refutes s facts (equality_bound false a b)

let lemma_equality_bound (lower:bool) (a b:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\ get_sort a == A.real_s /\ get_sort b == A.real_s)
          (ensures D.scoped [] (equality_bound lower a b) /\
                   A.comparison (equality_bound lower a b) == Some ((if lower then A.Le else A.Ge), a, b) /\
                   R.formula_clause (equality_bound lower a b) == [equality_bound lower a b]) =
  if lower then assert (A.application RL.real_le_decl [a; b] bool_sort "<=" op_arith_le)
  else assert (A.application RL.real_ge_decl [a; b] bool_sort ">=" op_arith_ge)

let lemma_implied_equality (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (reals:RL.carrier base) (facts:list expr) (a b:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    implied_equality s facts a b)
          (ensures T.truth s bc model other (R.mk_eq_expr a b)) =
  let rho = T.empty_environment (S.signature s) in
  let bound (lower:bool) : Lemma (T.truth s bc model other (equality_bound lower a b)) =
    lemma_equality_bound lower a b;
    if not (T.truth s bc model other (equality_bound lower a b)) then
      lemma_refutes s bc model other reals facts (equality_bound lower a b) in
  bound true;
  bound false;
  lemma_comparison s bc model other reals [] rho (equality_bound true a b) a b A.Le;
  lemma_comparison s bc model other reals [] rho (equality_bound false a b) a b A.Ge;
  RL.lemma_real_equality_at s bc model other reals [] rho a b
