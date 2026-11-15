module Z3QuantifierVacuitySorted

open Z3AstTheory
open FStar.List.Tot
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module D = Z3ExprScope
module X = Z3QuantifierVacuitySyntax
module P = Z3QuantifierVacuityScope

let inhabitant_of (#base:sort -> Type0) (s:S.checked_schema)
                  (other:V.interpretation base (S.signature s)) (t:sort)
  : GTot (V.value base (S.signature s) t) =
  other.V.application
    { decl_name = "inhabitant"; domain = []; range = t; interp = None; int_params = [] } []

let lemma_exists_truth (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (bound:list sort) (body:expr)
  : Lemma (requires E.exists_model s bc other /\
                    D.scoped (L.rev bound @ scope) body /\ get_sort body == bool_sort)
          (ensures
            T.truth_at s bc eq other scope rho (Quantifier Exists_k bound bool_sort body) <==>
            (exists (vs:V.arguments base (S.signature s) (L.rev bound)).
               T.truth_at s bc eq other (L.rev bound @ scope)
                 (V.extend (S.signature s) scope (L.rev bound) vs rho) body)) =
  let f = V.typed_body (S.signature s) bound bool_sort
    (V.evaluate_body (S.signature s) (T.interpretation s bc eq other) scope rho bound body) in
  assert (E.exists_case s bc other bound f);
  assert (T.truth_value s bc (other.V.quantification Exists_k bound bool_sort f) <==>
          (exists (vs:V.arguments base (S.signature s) (L.rev bound)).
             T.truth_value s bc (f vs)))

let lemma_remove_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope)
                    (n:nat) (q e:expr)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    D.scoped scope q /\ X.remove n q == Some e)
          (ensures D.scoped scope e /\
                   V.evaluate (S.signature s) (T.interpretation s bc eq other) scope rho q ==
                   V.evaluate (S.signature s) (T.interpretation s bc eq other) scope rho e) =
  P.lemma_remove_scope n scope q e;
  match q with
  | Quantifier k bs _ body ->
    let sigma = S.signature s in
    let i = T.interpretation s bc eq other in
    let ss = L.rev bs in
    let ss' = X.erase n ss in
    let body' = Some?.v (X.lower n body) in
    LP.rev_length bs;
    LP.rev_involutive ss';
    let tq (vs:V.arguments base sigma ss) : GTot bool =
      T.truth_at s bc eq other (ss @ scope) (V.extend sigma scope ss vs rho) body in
    let te (ws:V.arguments base sigma ss') : GTot bool =
      T.truth_at s bc eq other (ss' @ scope) (V.extend sigma scope ss' ws rho) body' in
    let down (vs:V.arguments base sigma ss) : Lemma (tq vs == te (P.erase_arguments sigma n ss vs)) =
      P.lemma_lower_bound_evaluate sigma i scope ss vs rho n body body' in
    let up (ws:V.arguments base sigma ss') : Lemma
      (te ws == tq (P.insert_argument sigma ss n (inhabitant_of s other (L.index ss n)) ws)) =
      let vs = P.insert_argument sigma ss n (inhabitant_of s other (L.index ss n)) ws in
      P.lemma_erase_insert_arguments sigma ss n (inhabitant_of s other (L.index ss n)) ws;
      P.lemma_lower_bound_evaluate sigma i scope ss vs rho n body body' in
    FStar.Classical.forall_intro down;
    FStar.Classical.forall_intro up;
    (match k with
     | Forall_k -> Q.lemma_forall_truth s bc eq other scope rho bs body
     | _ -> lemma_exists_truth s bc eq other scope rho bs body);
    if ss' = [] then (
      let w0 : V.arguments base sigma ss' = [] in
      up w0;
      assert (V.extend sigma scope ss' w0 rho == rho)
    ) else (
      match k with
      | Forall_k -> Q.lemma_forall_truth s bc eq other scope rho (L.rev ss') body'
      | _ -> lemma_exists_truth s bc eq other scope rho (L.rev ss') body'
    );
    T.lemma_boolean s bc (T.evaluate_at s bc eq other scope rho q);
    T.lemma_boolean s bc (T.evaluate_at s bc eq other scope rho e)
  | _ -> ()

let rec lemma_first_removal_at (#base:sort -> Type0) (s:S.checked_schema)
                               (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                               (other:V.interpretation base (S.signature s))
                               (scope:list sort) (rho:V.environment base (S.signature s) scope)
                               (remaining n:nat) (q e:expr)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    D.scoped scope q /\ X.first_removal remaining n q == Some e)
          (ensures D.scoped scope e /\
                   V.evaluate (S.signature s) (T.interpretation s bc eq other) scope rho q ==
                   V.evaluate (S.signature s) (T.interpretation s bc eq other) scope rho e)
          (decreases remaining) =
  if remaining > 0 then
    match X.remove n q with
    | Some _ -> lemma_remove_at s bc eq other scope rho n q e
    | None -> lemma_first_removal_at s bc eq other scope rho (remaining - 1) (n + 1) q e

let lemma_step_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (scope:list sort) (rho:V.environment base (S.signature s) scope)
                  (q e:expr)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    D.scoped scope q /\ X.step q == Some e)
          (ensures D.scoped scope e /\
                   V.evaluate (S.signature s) (T.interpretation s bc eq other) scope rho q ==
                   V.evaluate (S.signature s) (T.interpretation s bc eq other) scope rho e) =
  match q with
  | Quantifier _ bound _ _ ->
    lemma_first_removal_at s bc eq other scope rho (L.length bound) 0 q e
  | _ -> ()

let rec lemma_equivalent_sort (fuel:nat) (scope:list sort) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ X.equivalent fuel a b)
          (ensures get_sort a == get_sort b)
          (decreases fuel) =
  if a <> b && fuel > 0 then
    match X.step a, X.step b with
    | Some a', _ ->
      P.lemma_step_scope scope a a';
      lemma_equivalent_sort (fuel - 1) scope a' b
    | None, Some b' ->
      P.lemma_step_scope scope b b';
      lemma_equivalent_sort (fuel - 1) scope a b'
    | None, None -> ()

let rec lemma_equivalent_at (#base:sort -> Type0) (s:S.checked_schema)
                            (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                            (other:V.interpretation base (S.signature s))
                            (fuel:nat) (scope:list sort)
                            (rho:V.environment base (S.signature s) scope) (a b:expr)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    D.scoped scope a /\ D.scoped scope b /\ X.equivalent fuel a b)
          (ensures V.evaluate (S.signature s) (T.interpretation s bc eq other) scope rho a ==
                   V.evaluate (S.signature s) (T.interpretation s bc eq other) scope rho b)
          (decreases %[fuel; 0]) =
  if a <> b && fuel > 0 then
    match X.step a, X.step b with
    | Some a', _ ->
      P.lemma_step_scope scope a a';
      lemma_step_at s bc eq other scope rho a a';
      lemma_equivalent_at s bc eq other (fuel - 1) scope rho a' b
    | None, Some b' ->
      P.lemma_step_scope scope b b';
      lemma_step_at s bc eq other scope rho b b';
      lemma_equivalent_at s bc eq other (fuel - 1) scope rho a b'
    | None, None ->
      match a, b with
      | App f xs, App _ ys ->
        lemma_equivalent_args_at s bc eq other (fuel - 1) scope rho xs ys f.domain
      | Quantifier k bound _ body, Quantifier _ _ _ body' ->
        let sigma = S.signature s in
        let i = T.interpretation s bc eq other in
        lemma_equivalent_sort (fuel - 1) (L.rev bound @ scope) body body';
        let pointwise (vs:V.arguments base sigma (L.rev bound))
          : Lemma (V.evaluate sigma i (L.rev bound @ scope)
                     (V.extend sigma scope (L.rev bound) vs rho) body ==
                   V.evaluate sigma i (L.rev bound @ scope)
                     (V.extend sigma scope (L.rev bound) vs rho) body') =
          lemma_equivalent_at s bc eq other (fuel - 1) (L.rev bound @ scope)
            (V.extend sigma scope (L.rev bound) vs rho) body body' in
        FStar.Classical.forall_intro pointwise;
        V.lemma_quantifier_congruence sigma i scope rho k bound (get_sort body) body body'
      | _, _ -> ()

and lemma_equivalent_args_at (#base:sort -> Type0) (s:S.checked_schema)
                             (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                             (other:V.interpretation base (S.signature s))
                             (fuel:nat) (scope:list sort)
                             (rho:V.environment base (S.signature s) scope)
                             (xs ys:list expr) (ss:list sort)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    D.scoped_args scope xs /\ D.scoped_args scope ys /\
                    sorts_match xs ss /\ sorts_match ys ss /\ X.equivalent_args fuel xs ys)
          (ensures V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho xs ss ==
                   V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho ys ss)
          (decreases %[fuel; L.length xs + 1]) =
  match xs, ys, ss with
  | x :: rest, y :: tail, _ :: stail ->
    lemma_equivalent_at s bc eq other fuel scope rho x y;
    lemma_equivalent_args_at s bc eq other fuel scope rho rest tail stail
  | _, _, _ -> ()
