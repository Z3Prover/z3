module Z3SortedArithmetic

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open FStar.Real
module A = Z3LinearArithmeticAst
module P = Z3LinearArithmeticTheory
module E = Z3LinearArithmeticEmbed
module R = Z3ArithmeticRewrite
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module I = Z3SortedInteger
module D = Z3Definitions
module L = FStar.List.Tot

let integer (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
            (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
            (scope:list sort) (rho:V.environment base (S.signature s) scope)
            (e:expr) : int =
  if D.scoped scope e && get_sort e = A.int_s
  then I.number s model.integers (T.evaluate_at s bc model other scope rho e)
  else 0

let valuation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
              (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
              (scope:list sort) (rho:V.environment base (S.signature s) scope) : expr -> real =
  fun e -> of_int (integer s bc model other scope rho e)

let lemma_application (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (scope:list sort) (rho:V.environment base (S.signature s) scope)
                      (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped scope (App f args) /\ I.classify f <> I.Other)
          (ensures T.evaluate_at s bc model other scope rho (App f args) ==
            I.application s bc model.integers other f
              (T.evaluate_arguments_at s bc model other scope rho args f.domain)) =
  if L.mem f (S.signature s) then T.lemma_registered_constructor s f;
  assert (T.classify f == T.Other)

let rec lemma_sum (xs:list int)
  : Lemma (of_int (I.sum xs) == E.numeric_sum (L.map of_int xs))
          (decreases xs) =
  match xs with [] -> () | x :: rest ->
    lemma_sum rest;
    P.lemma_of_int_sum x (I.sum rest)

let rec lemma_product (xs:list int)
  : Lemma (of_int (I.product xs) == E.numeric_product (L.map of_int xs))
          (decreases xs) =
  match xs with [] -> () | x :: rest ->
    lemma_product rest;
    P.lemma_of_int_product x (I.product rest)

let lemma_calculation (op:A.operation{op = A.Add || op = A.Mul || op = A.Sub}) (xs:list int)
  : Lemma (of_int (I.calculate op xs) ==
    (match op with
     | A.Add -> E.numeric_sum (L.map of_int xs)
     | A.Mul -> E.numeric_product (L.map of_int xs)
     | A.Sub -> E.numeric_subtract (L.map of_int xs)
     | _ -> 0.0R)) =
  match op with
  | A.Add -> lemma_sum xs
  | A.Mul -> lemma_product xs
  | A.Sub ->
    (match xs with [] -> () | [_] -> () | _ :: rest -> lemma_sum rest)
  | _ -> ()

let rec lemma_linearize (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (scope:list sort) (rho:V.environment base (S.signature s) scope)
                        (fuel:nat) (e:expr) (p:A.poly)
  : Lemma (requires D.scoped scope e /\ get_sort e == A.int_s /\ A.linearize fuel e == Some p)
          (ensures E.denotes p (of_int (integer s bc model other scope rho e))
                     (valuation s bc model other scope rho))
          (decreases %[fuel; 0]) =
  assert (fuel > 0);
  match A.numeral e with
  | Some (n, d) ->
    (match e with App f [] -> lemma_application s bc model other scope rho f [] | _ -> ())
  | None ->
    (match e with
     | App f args ->
       (match A.operation_of f args with
        | None -> ()
        | Some op ->
          I.lemma_calculate f args op;
          A.lemma_linearize_application fuel f args op;
          lemma_application s bc model other scope rho f args;
          lemma_linearize_arguments s bc model other scope rho (fuel - 1) args f.domain;
          let ps = Some?.v (A.linearize_args (fuel - 1) args) in
          let ns = I.numbers s model.integers f.domain
            (T.evaluate_arguments_at s bc model other scope rho args f.domain) in
          let xs = L.map of_int ns in
          let r = valuation s bc model other scope rho in
          lemma_calculation op ns;
          (match op with
           | A.Add -> E.lemma_sum ps xs r
           | A.Mul ->
             (match P.product ps with Some q -> E.lemma_product ps xs q r | None -> ())
           | A.Sub -> E.lemma_subtract ps xs p r
           | _ -> ()))
     | _ -> ())

and lemma_linearize_arguments (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (scope:list sort) (rho:V.environment base (S.signature s) scope)
                              (fuel:nat) (args:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss /\ I.integer_sorts ss /\
                    Some? (A.linearize_args fuel args))
          (ensures E.denotations (Some?.v (A.linearize_args fuel args))
            (L.map of_int (I.numbers s model.integers ss
              (T.evaluate_arguments_at s bc model other scope rho args ss)))
            (valuation s bc model other scope rho))
          (decreases %[fuel; L.length args + 1]) =
  match args, ss with
  | a :: rest, t :: tail ->
    V.lemma_sort_eq (get_sort a) t;
    lemma_linearize s bc model other scope rho fuel a (Some?.v (A.linearize fuel a));
    lemma_linearize_arguments s bc model other scope rho fuel rest tail
  | _, _ -> ()

let rec integer_formula (fuel:nat) (e:expr) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else if e = Z3ResolutionProofTheory.true_expr || e = Z3ResolutionProofTheory.false_expr then true
  else match e with
  | App f [a] ->
    f = R.not_decl && get_sort a = bool_sort && integer_formula (fuel - 1) a
  | _ ->
    (match A.comparison e with
     | Some (_, a, _) -> get_sort a = A.int_s
     | None -> false)

let lemma_integer_equality (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (scope:list sort) (rho:V.environment base (S.signature s) scope)
                           (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\
                    get_sort a == A.int_s /\ get_sort b == A.int_s)
          (ensures integer s bc model other scope rho a == integer s bc model other scope rho b <==>
                   T.evaluate_at s bc model other scope rho a ==
                   T.evaluate_at s bc model other scope rho b) =
  I.lemma_value s model.integers (T.evaluate_at s bc model other scope rho a);
  I.lemma_value s model.integers (T.evaluate_at s bc model other scope rho b)

let lemma_comparison (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (e a b:expr) (r:A.relation)
  : Lemma (requires D.scoped scope e /\ A.comparison e == Some (r, a, b) /\
                    get_sort a == A.int_s)
          (ensures T.truth_at s bc model other scope rho e <==>
            E.numeric_relation r (of_int (integer s bc model other scope rho a))
                                 (of_int (integer s bc model other scope rho b))) =
  match e with
  | App f [x; y] ->
    V.lemma_sort_eq (get_sort x) A.int_s;
    V.lemma_sort_eq (get_sort y) A.int_s;
    if r = A.Eq then (
      T.lemma_equality_at s bc model other scope rho a b;
      lemma_integer_equality s bc model other scope rho a b)
    else (
      assert (I.classify f == I.Compare r);
      lemma_application s bc model other scope rho f [x; y];
      match r with A.Le | A.Lt | A.Ge | A.Gt | A.Eq -> ())
  | _ -> ()

(* `R.constraint_of` at a comparison, unfolded once: an equation has no
   constraint, and otherwise the polynomial is the oriented difference
   (`A.oriented`) of the two linearized sides. A separate lemma, so that the
   comparison case of `lemma_constraint` does not unfold `constraint_of` in
   its own larger context. *)
let lemma_constraint_of_comparison (fuel:nat) (positive:bool) (e a b:expr) (r:A.relation)
                                   (p:A.contribution)
  : Lemma (requires ~(e = Z3ResolutionProofTheory.true_expr || e = Z3ResolutionProofTheory.false_expr) /\
                    A.comparison e == Some (r, a, b) /\ R.constraint_of fuel positive e == Some p)
          (ensures r <> A.Eq /\ Some? (A.linearize 64 a) /\ Some? (A.linearize 64 b) /\
                   p.P.poly == fst (A.oriented positive r (Some?.v (A.linearize 64 a))
                                                         (Some?.v (A.linearize 64 b)))) =
  ()

(* The value of that polynomial, from `E.lemma_oriented`: the precondition of
   `R.lemma_scaled_relation`, proved apart from the larger context of
   `lemma_constraint`. *)
let lemma_oriented_constraint (positive:bool) (r:A.relation) (pa pb:A.poly) (p:A.contribution)
                              (x y:real) (v:expr -> real)
  : Lemma (requires p.P.poly == fst (A.oriented positive r pa pb) /\
                    E.denotes pa x v /\ E.denotes pb y v)
          (ensures P.value p.P.poly v == of_int p.P.poly.denom *. E.difference positive r x y) =
  E.lemma_oriented positive r pa pb x y v

let rec lemma_constraint (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (scope:list sort) (rho:V.environment base (S.signature s) scope)
                         (fuel:nat) (positive:bool) (e:expr) (p:A.contribution)
  : Lemma (requires D.scoped scope e /\ get_sort e == bool_sort /\
                    integer_formula fuel e /\ R.constraint_of fuel positive e == Some p)
          (ensures P.holds p (valuation s bc model other scope rho) <==>
            (if positive then T.truth_at s bc model other scope rho e
             else ~(T.truth_at s bc model other scope rho e)))
          (decreases fuel) =
  if e = Z3ResolutionProofTheory.true_expr || e = Z3ResolutionProofTheory.false_expr then
    (match e with App f [] -> T.lemma_evaluate_core_at s bc model other scope rho f [] | _ -> ())
  else match e with
  | App f [a] ->
    lemma_constraint s bc model other scope rho (fuel - 1) (not positive) a p;
    T.lemma_evaluate_core_at s bc model other scope rho f [a]
  | _ ->
    (match A.comparison e with
     | Some (r, a, b) ->
       lemma_constraint_of_comparison fuel positive e a b r p;
       let pa = Some?.v (A.linearize 64 a) in
       let pb = Some?.v (A.linearize 64 b) in
       lemma_linearize s bc model other scope rho 64 a pa;
       lemma_linearize s bc model other scope rho 64 b pb;
       let x = of_int (integer s bc model other scope rho a) in
       let y = of_int (integer s bc model other scope rho b) in
       let v = valuation s bc model other scope rho in
       lemma_oriented_constraint positive r pa pb p x y v;
       R.lemma_scaled_relation positive r p.poly.denom (P.value p.poly v) x y;
       lemma_comparison s bc model other scope rho e a b r
     | None -> ())

let lemma_equation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (scope:list sort) (rho:V.environment base (S.signature s) scope)
                   (e:expr) (p:A.poly)
  : Lemma (requires D.scoped scope e /\ integer_formula 16 e /\ R.equation_of e == Some p)
          (ensures T.truth_at s bc model other scope rho e <==>
                   P.value p (valuation s bc model other scope rho) == 0.0R) =
  match A.comparison e with
  | Some (A.Eq, a, b) ->
    let pa = Some?.v (A.linearize 64 a) in
    let pb = Some?.v (A.linearize 64 b) in
    let x = of_int (integer s bc model other scope rho a) in
    let y = of_int (integer s bc model other scope rho b) in
    let v = valuation s bc model other scope rho in
    lemma_linearize s bc model other scope rho 64 a pa;
    lemma_linearize s bc model other scope rho 64 b pb;
    E.lemma_denotes_negative pb y v;
    E.lemma_denotes_add pa (P.scale (-1) 1 pb) x (0.0R -. y) v;
    R.lemma_denotes_zero p (x +. (0.0R -. y)) v;
    lemma_comparison s bc model other scope rho e a b A.Eq
  | _ -> ()

let equivalent (a b:expr) : bool =
  let numeric = get_sort a = A.int_s && get_sort b = A.int_s in
  let boolean = get_sort a = bool_sort && get_sort b = bool_sort &&
    integer_formula 16 a && integer_formula 16 b in
  if not (numeric || boolean) then false
  else if not (Some? (expression_budget 256 a) && Some? (expression_budget 256 b)) then false
  else if numeric then R.integer_equivalent a b
  else R.boolean_equivalent a b || R.equation_equivalent a b

let lemma_equivalent (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ equivalent a b)
          (ensures T.evaluate_at s bc model other scope rho a ==
                   T.evaluate_at s bc model other scope rho b) =
  let v = valuation s bc model other scope rho in
  if get_sort a = A.int_s && get_sort b = A.int_s then (
    let p = Some?.v (A.linearize 64 a) in
    let q = Some?.v (A.linearize 64 b) in
    lemma_linearize s bc model other scope rho 64 a p;
    lemma_linearize s bc model other scope rho 64 b q;
    R.lemma_same_polynomial p q (v a) (v b) v;
    lemma_integer_equality s bc model other scope rho a b)
  else (
    if R.boolean_equivalent a b then (
      let p = Some?.v (R.constraint_of 16 true a) in
      let q = Some?.v (R.constraint_of 16 true b) in
      lemma_constraint s bc model other scope rho 16 true a p;
      lemma_constraint s bc model other scope rho 16 true b q;
      R.lemma_same_constraint p q v)
    else (
      let p = Some?.v (R.equation_of a) in
      let q = Some?.v (R.equation_of b) in
      lemma_equation s bc model other scope rho a p;
      lemma_equation s bc model other scope rho b q;
      R.lemma_equation_polynomials p q v);
    T.lemma_boolean s bc (T.evaluate_at s bc model other scope rho a);
    T.lemma_boolean s bc (T.evaluate_at s bc model other scope rho b))
