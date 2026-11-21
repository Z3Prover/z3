module Z3IndependentConditionalDefinition

open Z3AstTheory
module A = Z3ArraySyntax
module B = Z3BoundedBoolEquiv
module D = Z3ExprScope
module R = Z3ClauseSyntax
module S = Z3DatatypeSignature
module SA = Z3SortedArray
module T = Z3SortedSemantics
module V = Z3DatatypeValue
module X = Z3BooleanRewriteSyntax

let lemma_directional (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (premise choice name:expr)
  : Lemma (requires T.truth s bc model other premise /\ directional premise choice name)
          (ensures T.truth s bc model other (R.mk_eq_expr choice name)) =
  match A.ite_parts choice with
  | None -> ()
  | Some (c, t, u) ->
    let neg = R.mk_not_expr c in
    let positive = R.mk_eq_expr name t in
    let negative = R.mk_eq_expr name u in
    let a = disjunction neg positive in
    let b = disjunction c negative in
    let rho = T.empty_environment (S.signature s) in
    SA.lemma_ite_scope [] choice c t u;
    T.lemma_nary s bc model other (R.and_decl [a; b]) [a; b] B.And;
    T.lemma_nary s bc model other (R.or_decl [neg; positive]) [neg; positive] B.Or;
    T.lemma_nary s bc model other (R.or_decl [c; negative]) [c; negative] B.Or;
    T.lemma_negation s bc model other R.not_decl c;
    T.lemma_equality s bc model other name t;
    T.lemma_equality s bc model other name u;
    SA.lemma_ite s bc model other [] rho choice c t u;
    T.lemma_equality s bc model other choice name

let lemma_check (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (premise left right:expr)
  : Lemma (requires T.truth s bc model other premise /\ check premise left right)
          (ensures T.truth s bc model other (R.mk_eq_expr left right)) =
  if directional premise left right then
    lemma_directional s bc model other premise left right
  else (
    lemma_directional s bc model other premise right left;
    T.lemma_equality s bc model other right left;
    T.lemma_equality s bc model other left right)

type ite_branch = {
  condition: expr;
  choice: expr;
  then_value: expr;
  else_value: expr;
  positive: bool;
  guard: expr;
  equation: expr;
  left: expr;
  right: expr;
}

let branch_equation (condition:expr) (positive:bool) (guard equation:expr)
  : option ite_branch =
  match A.equality_parts equation with
  | Some (left, right) ->
    let matches (choice other:expr) : option (expr & expr & expr) =
      match A.ite_parts choice with
      | Some (c, t, u) ->
        if c = condition && other = (if positive then t else u)
        then Some (c, t, u)
        else None
      | _ -> None
    in
    (match matches left right with
     | Some (c, t, u) ->
       Some { condition = c; choice = left; then_value = t; else_value = u;
              positive = positive; guard = guard; equation = equation;
              left = left; right = right }
     | None ->
       (match matches right left with
        | Some (c, t, u) ->
          Some { condition = c; choice = right; then_value = t; else_value = u;
                 positive = positive; guard = guard; equation = equation;
                 left = left; right = right }
        | None -> None))
  | None -> None

let branch_of (formula:expr) : option ite_branch =
  if not (D.scoped [] formula) then None
  else
    match formula with
    | App f [guard; equation] ->
      if f <> R.or_decl [guard; equation] then None
      else
        (match guard with
         | App n [condition] ->
           if n = R.not_decl then
             (match branch_equation condition true guard equation with
              | Some branch -> Some branch
              | None -> branch_equation guard false guard equation)
           else branch_equation guard false guard equation
         | _ -> branch_equation guard false guard equation)
    | _ -> None

let branch_choice_scoped (formula:expr) : bool =
  match branch_of formula with
  | Some branch -> D.scoped [] branch.choice
  | None -> false

let ite_definition_axiom (formula:expr) : bool =
  D.scoped [] formula &&
  (match formula with
   | App f [first; second] ->
     f = R.and_decl [first; second] &&
     branch_choice_scoped first && branch_choice_scoped second
   | _ -> false)

let lemma_branch_axiom (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s)) (formula:expr) (branch:ite_branch)
  : Lemma (requires branch_of formula == Some branch /\ D.scoped [] branch.choice)
          (ensures T.truth s bc model other formula) =
  let rho = T.empty_environment (S.signature s) in
  assert (D.scoped [] formula);
  (match formula with
   | App f [guard; equation] ->
     assert (f = R.or_decl [guard; equation]);
     assert (D.scoped [] guard /\ D.scoped [] equation);
     assert (branch.guard = guard /\ branch.equation = equation)
   | _ -> ());
  assert (D.scoped [] (App (R.or_decl [branch.guard; branch.equation])
                            [branch.guard; branch.equation]));
  assert (A.equality_parts branch.equation == Some (branch.left, branch.right));
  assert (branch.equation = R.mk_eq_expr branch.left branch.right);
  assert (D.scoped [] branch.left /\ D.scoped [] branch.right);
  assert (get_sort branch.left == get_sort branch.right);
  if branch.positive then
    assert (branch.guard = R.mk_not_expr branch.condition)
  else
    assert (branch.guard = branch.condition);
  let selected = if branch.positive then branch.then_value else branch.else_value in
  assert ((branch.left = branch.choice /\ branch.right = selected) ||
          (branch.right = branch.choice /\ branch.left = selected));
  SA.lemma_ite_scope [] branch.choice branch.condition branch.then_value branch.else_value;
  T.lemma_nary s bc model other (R.or_decl [branch.guard; branch.equation])
    [branch.guard; branch.equation] B.Or;
  assert (T.truth s bc model other formula ==
          (T.truth s bc model other branch.guard ||
           T.truth s bc model other branch.equation));
  if branch.positive then T.lemma_negation s bc model other R.not_decl branch.condition;
  T.lemma_equality s bc model other branch.left branch.right;
  SA.lemma_ite s bc model other [] rho branch.choice branch.condition
    branch.then_value branch.else_value;
  let condition_true = T.truth s bc model other branch.condition in
  if branch.positive then
    (if condition_true then
       (assert (T.evaluate s bc model other branch.choice ==
                T.evaluate s bc model other branch.then_value);
        if branch.left = branch.choice then
          (assert (branch.right = branch.then_value);
           assert (T.evaluate s bc model other branch.left ==
                   T.evaluate s bc model other branch.right))
        else
          (assert (branch.right = branch.choice /\ branch.left = branch.then_value);
           assert (T.evaluate s bc model other branch.left ==
                   T.evaluate s bc model other branch.right));
        assert (T.truth s bc model other branch.equation))
     else
       assert (T.truth s bc model other branch.guard))
  else
    (if condition_true then
       assert (T.truth s bc model other branch.guard)
     else
       (assert (T.evaluate s bc model other branch.choice ==
                T.evaluate s bc model other branch.else_value);
        if branch.left = branch.choice then
          (assert (branch.right = branch.else_value);
           assert (T.evaluate s bc model other branch.left ==
                   T.evaluate s bc model other branch.right))
        else
          (assert (branch.right = branch.choice /\ branch.left = branch.else_value);
           assert (T.evaluate s bc model other branch.left ==
                   T.evaluate s bc model other branch.right));
        assert (T.truth s bc model other branch.equation)));
  assert (T.truth s bc model other formula)

let lemma_ite_definition_axiom (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s)) (formula:expr)
  : Lemma (requires ite_definition_axiom formula)
          (ensures T.truth s bc model other formula) =
  match formula with
  | App _ [first; second] ->
    (match branch_of first with
     | Some first_branch ->
       (match branch_of second with
        | Some second_branch ->
          lemma_branch_axiom s bc model other first first_branch;
          lemma_branch_axiom s bc model other second second_branch
        | None -> ())
     | None -> ());
    T.lemma_nary s bc model other (R.and_decl [first; second]) [first; second] B.And
  | _ -> ()
