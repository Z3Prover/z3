module Z3SortedArrayEquality

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module I = Z3SortedInteger
module D = Z3ExprScope
module A = Z3ArraySyntax
module E = Z3ArrayEqualitySyntax
module K = Z3SortedArray
module LA = Z3LinearArithmeticAst
module AR = Z3ArithmeticSyntax
module SA = Z3SortedArithmetic
module R = Z3ClauseSyntax
module L = FStar.List.Tot
module BR = Z3SortedBooleanRewrite

let const_decl : func_decl = {
  decl_name = "const"; domain = [LA.int_s]; range = E.int_array;
  interp = Some Z3OperatorTags.op_const_array; int_params = [];
}

let const_model (#base:sort -> Type0) (s:S.checked_schema)
                (bc:S.boolean_carrier base) (core:T.scalar_model base)
                (other:V.interpretation base (S.signature s))
                (m:K.family base (S.signature s){m.supports LA.int_s LA.int_s}) : prop =
  forall (v:V.value base (S.signature s) LA.int_s).
    T.application s bc core other const_decl [v] ==
    (m.arrays LA.int_s LA.int_s).constant v

let rec lemma_default_scope (#base:sort -> Type0) (#sigma:V.signature)
                            (m:K.family base sigma) (scope:list sort)
                            (fuel:nat) (e d:expr)
  : Lemma (requires D.scoped scope e /\ K.supported m e /\ E.default_term fuel e == Some d)
          (ensures D.scoped scope d /\ K.supported m d /\
                   get_sort e == E.int_array /\ get_sort d == LA.int_s)
          (decreases fuel) =
  E.lemma_default_sort fuel e d;
  match e with
  | App _ [_] -> ()
  | App _ [a; k; v] ->
    K.lemma_store_parts_scope scope e a k v;
    lemma_default_scope m scope (fuel - 1) a d
  | _ -> ()

let rec upper_bound (#base:sort -> Type0) (s:S.checked_schema)
                    (bc:S.boolean_carrier base) (core:T.scalar_model base)
                    (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope)
                    (e:expr) : GTot int (decreases e) =
  match e with
  | App _ [a; k; _] ->
    let b = upper_bound s bc core other scope rho a in
    let n = SA.integer s bc core other scope rho k in
    if n >= b then n + 1 else b
  | _ -> 0

let lemma_const_read (#base:sort -> Type0) (s:S.checked_schema)
                     (bc:S.boolean_carrier base) (core:T.scalar_model base)
                     (other:V.interpretation base (S.signature s))
                     (m:K.family base (S.signature s){m.supports LA.int_s LA.int_s})
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (f:func_decl) (v:expr) (n:int)
  : Lemma (requires const_model s bc core other m /\
                    D.scoped scope v /\ get_sort v == LA.int_s /\ f == const_decl)
          (ensures (m.arrays LA.int_s LA.int_s).read
                     (T.evaluate_at s bc core other scope rho (App f [v]))
                     (I.value s core.integers n) ==
                   T.evaluate_at s bc core other scope rho v) =
  if L.mem f (S.signature s) then T.lemma_registered_constructor s f;
  V.lemma_sort_eq (get_sort v) LA.int_s;
  SA.lemma_evaluate_application s bc core other scope rho f [v];
  let vv = T.evaluate_at s bc core other scope rho v in
  assert (T.evaluate_arguments_at s bc core other scope rho [v] [LA.int_s] == [vv]);
  assert (T.application s bc core other const_decl [vv] ==
          (m.arrays LA.int_s LA.int_s).constant vv)

let rec lemma_default_read (#base:sort -> Type0) (s:S.checked_schema)
                          (bc:S.boolean_carrier base) (core:T.scalar_model base)
                          (other:V.interpretation base (S.signature s))
                          (m:K.family base (S.signature s){m.supports LA.int_s LA.int_s})
                          (scope:list sort) (rho:V.environment base (S.signature s) scope)
                          (fuel:nat)
                          (e:expr{D.scoped scope e /\ get_sort e == E.int_array})
                          (d:expr{D.scoped scope d /\ get_sort d == LA.int_s}) (n:int)
  : Lemma (requires K.model s bc core other m /\ const_model s bc core other m /\
                    K.supported m e /\ E.default_term fuel e == Some d /\
                    n >= upper_bound s bc core other scope rho e)
          (ensures (m.arrays LA.int_s LA.int_s).read
                     (T.evaluate_at s bc core other scope rho e)
                     (I.value s core.integers n) ==
                   T.evaluate_at s bc core other scope rho d)
          (decreases fuel) =
  if fuel = 0 then ()
  else match e with
  | App f [v] -> lemma_const_read s bc core other m scope rho f v n
  | App _ [a; k; v] ->
    K.lemma_store_parts_scope scope e a k v;
    lemma_default_scope m scope (fuel - 1) a d;
    lemma_default_read s bc core other m scope rho (fuel - 1) a d n;
    K.lemma_store s bc core other m scope rho LA.int_s LA.int_s a k v;
    let kv = T.evaluate_at s bc core other scope rho k in
    let key = I.value s core.integers n in
    assert (I.number s core.integers key == n);
    assert (I.number s core.integers kv < n);
    K.lemma_read_other (m.arrays LA.int_s LA.int_s)
      (T.evaluate_at s bc core other scope rho a) kv key
      (T.evaluate_at s bc core other scope rho v)
  | _ -> ()

let lemma_default_arithmetic (x y:expr)
  : Lemma (requires get_sort x == LA.int_s /\ get_sort y == LA.int_s /\
                    AR.equivalent (R.mk_eq_expr x y) R.false_expr)
          (ensures AR.constant_equation (R.mk_eq_expr x y) R.false_expr) = ()

let lemma_unequal_defaults (#base:sort -> Type0) (s:S.checked_schema)
                          (bc:S.boolean_carrier base) (core:T.scalar_model base)
                          (other:V.interpretation base (S.signature s))
                          (m:K.family base (S.signature s){m.supports LA.int_s LA.int_s})
                          (scope:list sort) (rho:V.environment base (S.signature s) scope)
                          (e:expr)
  : Lemma (requires K.model s bc core other m /\ const_model s bc core other m /\
                    D.scoped scope e /\ K.supported m e /\ E.unequal_defaults e)
          (ensures not (T.truth_at s bc core other scope rho e)) =
  match A.equality_parts e with
  | Some (a, b) ->
    K.lemma_equality_parts_scope scope e a b;
    let x = Some?.v (E.default_term 64 a) in
    let y = Some?.v (E.default_term 64 b) in
    lemma_default_scope m scope 64 a x;
    lemma_default_scope m scope 64 b y;
    lemma_default_arithmetic x y;
    V.lemma_sort_eq (get_sort x) (get_sort x);
    V.lemma_sort_eq (get_sort y) (get_sort x);
    assert (D.scoped_args scope [y]);
    assert (D.scoped_args scope [x; y]);
    assert (sorts_match [y] [get_sort x]);
    assert (sorts_match [x; y] [get_sort x; get_sort x]);
    assert (D.scoped scope (R.mk_eq_expr x y));
    SA.lemma_constant_equation s bc core other scope rho (R.mk_eq_expr x y) R.false_expr;
    assert_norm (Z3BooleanRewriteSyntax.boolean_cut [] 1 R.false_expr ==
                 Z3BoundedBoolEquiv.Bool false);
    BR.lemma_cut s bc core other scope rho [] 1 R.false_expr;
    assert (T.truth_at s bc core other scope rho R.false_expr == false);
    assert (T.truth_at s bc core other scope rho (R.mk_eq_expr x y) ==
            T.truth_at s bc core other scope rho R.false_expr);
    T.lemma_equality_at s bc core other scope rho x y;
    assert (~(T.evaluate_at s bc core other scope rho x ==
              T.evaluate_at s bc core other scope rho y));
    let ab = upper_bound s bc core other scope rho a in
    let bb = upper_bound s bc core other scope rho b in
    let n = if ab >= bb then ab else bb in
    lemma_default_read s bc core other m scope rho 64 a x n;
    lemma_default_read s bc core other m scope rho 64 b y n;
    assert (~(T.evaluate_at s bc core other scope rho a ==
              T.evaluate_at s bc core other scope rho b));
    T.lemma_equality_at s bc core other scope rho a b
  | None -> ()
