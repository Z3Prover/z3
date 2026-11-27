module Z3SortedBooleanRewrite

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module X = Z3BooleanRewriteSyntax
module R = Z3ClauseSyntax
module B = Z3BoundedBoolEquiv
module N = Z3BooleanNormalForm
module D = Z3ExprScope
module L = FStar.List.Tot
module CS = Z3ClausalSemantics

let rec lemma_domain (args:list expr)
  : Lemma (T.boolean_sorts (R.boolean_domain args)) (decreases args) =
  match args with [] -> () | _ :: rest -> lemma_domain rest

let lemma_classification (f:func_decl) (args:list expr)
  : Lemma (
      match X.native_bool_op f args with
      | B.BTrue -> T.classify f == T.Constant true
      | B.BFalse -> T.classify f == T.Constant false
      | B.BNot -> T.classify f == T.Negation
      | B.BImplies -> T.classify f == T.Implication
      | B.BNary op -> T.classify f == T.Nary op
      | B.BEq -> T.classify f == T.Equality bool_sort
      | B.BIte -> T.classify f == T.Choice bool_sort
      | B.Opaque -> True) =
  lemma_domain args;
  X.lemma_native_bool_op f args

let lemma_not_at (#base:sort -> Type0) (s:S.checked_schema)
                 (bc:S.boolean_carrier base) (core:T.scalar_model base)
                 (other:V.interpretation base (S.signature s))
                 (scope:list sort) (rho:V.environment base (S.signature s) scope)
                 (a:expr)
  : Lemma (requires D.scoped scope a /\ get_sort a == bool_sort)
          (ensures D.scoped scope (R.mk_not_expr a) /\ get_sort (R.mk_not_expr a) == bool_sort /\
                   T.truth_at s bc core other scope rho (R.mk_not_expr a) ==
                   not (T.truth_at s bc core other scope rho a)) =
  V.lemma_sort_eq (get_sort a) bool_sort;
  T.lemma_evaluate_core_at s bc core other scope rho R.not_decl [a]

let lemma_or_at (#base:sort -> Type0) (s:S.checked_schema)
                (bc:S.boolean_carrier base) (core:T.scalar_model base)
                (other:V.interpretation base (S.signature s))
                (scope:list sort) (rho:V.environment base (S.signature s) scope)
                (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort)
          (ensures T.truth_at s bc core other scope rho (App (R.or_decl [a; b]) [a; b]) ==
                   (T.truth_at s bc core other scope rho a ||
                    T.truth_at s bc core other scope rho b)) =
  V.lemma_sort_eq (get_sort a) bool_sort;
  V.lemma_sort_eq (get_sort b) bool_sort;
  T.lemma_evaluate_core_at s bc core other scope rho (R.or_decl [a; b]) [a; b];
  lemma_domain [a; b];
  T.lemma_boolean_arguments_at s bc core other scope rho [a; b]
    (R.boolean_domain [a; b]) B.Or

let rec lemma_cut (#base:sort -> Type0) (s:S.checked_schema)
                  (bc:S.boolean_carrier base) (model:T.scalar_model base)
                  (other:V.interpretation base (S.signature s))
                  (scope:list sort) (rho:V.environment base (S.signature s) scope)
                  (boundaries:list expr) (depth:nat) (e:expr)
  : Lemma (requires D.scoped scope e /\ get_sort e == bool_sort)
          (ensures B.geval (T.truth_at s bc model other scope rho)
                     (X.boolean_cut boundaries depth e) ==
                   T.truth_at s bc model other scope rho e)
          (decreases e) =
  if X.reflexive_equality e then (
    match e with
    | App _ [a; b] -> T.lemma_equality_at s bc model other scope rho a b
    | _ -> ())
  else if L.mem e boundaries then ()
  else match e with
  | App f args ->
    lemma_classification f args;
    (if X.native_bool_op f args <> B.Opaque then
       T.lemma_evaluate_core_at s bc model other scope rho f args);
    (match X.native_bool_op f args with
     | B.BTrue | B.BFalse | B.Opaque -> ()
     | B.BNot ->
       (match args with
        | [a] ->
          if depth > 0 then lemma_cut s bc model other scope rho boundaries (depth - 1) a
        | _ -> ())
     | B.BImplies ->
       (match args with
        | [a; b] ->
          if depth > 0 then (
            lemma_cut s bc model other scope rho boundaries (depth - 1) a;
            lemma_cut s bc model other scope rho boundaries (depth - 1) b)
        | _ -> ())
     | B.BNary op ->
       if depth > 0 then (
         T.lemma_boolean_arguments_at s bc model other scope rho args f.domain op;
         lemma_cut_args s bc model other scope rho boundaries (depth - 1) args f.domain op)
     | B.BEq ->
       (match args with
        | [a; b] ->
          if depth > 0 then (
            lemma_cut s bc model other scope rho boundaries (depth - 1) a;
            lemma_cut s bc model other scope rho boundaries (depth - 1) b;
            T.lemma_boolean_equality_at s bc model other scope rho a b)
        | _ -> ())
     | B.BIte ->
       (match args with
        | [c; a; b] ->
          if depth > 0 then (
            lemma_cut s bc model other scope rho boundaries (depth - 1) c;
            lemma_cut s bc model other scope rho boundaries (depth - 1) a;
            lemma_cut s bc model other scope rho boundaries (depth - 1) b;
            B.lemma_boolean_ite_geval (T.truth_at s bc model other scope rho)
              (X.boolean_cut boundaries (depth - 1) c)
              (X.boolean_cut boundaries (depth - 1) a)
              (X.boolean_cut boundaries (depth - 1) b))
        | _ -> ()))
  | _ -> ()

and lemma_cut_args (#base:sort -> Type0) (s:S.checked_schema)
                   (bc:S.boolean_carrier base) (model:T.scalar_model base)
                   (other:V.interpretation base (S.signature s))
                   (scope:list sort) (rho:V.environment base (S.signature s) scope)
                   (boundaries:list expr) (depth:nat) (args:list expr)
                   (ss:list sort) (op:B.nary_op)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss /\ T.boolean_sorts ss)
          (ensures B.geval_args (T.truth_at s bc model other scope rho) op
                     (X.boolean_cut_args boundaries depth args) ==
                   B.geval_args (T.truth_at s bc model other scope rho) op (L.map B.Atom args))
          (decreases args) =
  match args, ss with
  | a :: rest, t :: tail ->
    V.lemma_sort_eq (get_sort a) t;
    lemma_cut s bc model other scope rho boundaries depth a;
    lemma_cut_args s bc model other scope rho boundaries depth rest tail op
  | _, _ -> ()

let lemma_equivalent (#base:sort -> Type0) (s:S.checked_schema)
                     (bc:S.boolean_carrier base) (model:T.scalar_model base)
                     (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (depth width:nat) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ X.boolean_equiv depth width a b)
          (ensures T.truth_at s bc model other scope rho a ==
                   T.truth_at s bc model other scope rho b) =
  let v = T.truth_at s bc model other scope rho in
  let boundaries = B.unique (B.intersect (X.boolean_nodes depth a) (X.boolean_nodes depth b)) in
  let ca = X.boolean_cut boundaries depth a in
  let cb = X.boolean_cut boundaries depth b in
  let atoms = B.unique (B.support ca @ B.support cb) in
  if X.structural_boolean_equiv a b then (
    let sa = X.boolean_cut [] (X.boolean_height a) a in
    let sb = X.boolean_cut [] (X.boolean_height b) b in
    B.lemma_freeze_pair v sa sb;
    N.lemma_equivalent_sound (B.freeze v (B.support sa @ B.support sb)) sa sb;
    lemma_cut s bc model other scope rho [] (X.boolean_height a) a;
    lemma_cut s bc model other scope rho [] (X.boolean_height b) b)
  else (
    if N.equivalent ca cb then (
      B.lemma_freeze_pair v ca cb;
      N.lemma_equivalent_sound (B.freeze v (B.support ca @ B.support cb)) ca cb)
    else (
      B.lemma_mem_append (B.support ca) (B.support cb);
      B.lemma_unique_mem (B.support ca @ B.support cb);
      assert (B.agree_outside atoms (fun _ -> false) v ca cb);
      B.lemma_check_rows_sound_ghost atoms (fun _ -> false) v ca cb);
    lemma_cut s bc model other scope rho boundaries depth a;
    lemma_cut s bc model other scope rho boundaries depth b)

let lemma_search (#base:sort -> Type0) (s:S.checked_schema)
                 (bc:S.boolean_carrier base) (model:T.scalar_model base)
                 (other:V.interpretation base (S.signature s))
                 (scope:list sort) (rho:V.environment base (S.signature s) scope)
                 (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ X.boolean_search a b)
          (ensures T.truth_at s bc model other scope rho a ==
                   T.truth_at s bc model other scope rho b) =
  let ca = X.boolean_cut [] (X.boolean_height a) a in
  let cb = X.boolean_cut [] (X.boolean_height b) b in
  let v = T.truth_at s bc model other scope rho in
  let frozen = B.freeze v (B.support ca @ B.support cb) in
  B.lemma_freeze_pair v ca cb;
  N.lemma_shannon_sound frozen 7 (N.normalize_context 2 ca) (N.normalize_context 2 cb);
  N.lemma_normalize_context_sound frozen 2 ca;
  N.lemma_normalize_context_sound frozen 2 cb;
  lemma_cut s bc model other scope rho [] (X.boolean_height a) a;
  lemma_cut s bc model other scope rho [] (X.boolean_height b) b

let connective_holds (op:X.connective) (v:CS.valuation) (args:list expr) : GTot bool =
  if op = X.Conjunction then CS.conj_holds v args else CS.clause_holds v args

let rec lemma_connective_evaluation (op:X.connective) (v:CS.valuation) (args:list expr)
  : Lemma (B.geval_args v (if op = X.Conjunction then B.And else B.Or) (L.map B.Atom args) ==
           connective_holds op v args) (decreases args) =
  match args with [] -> () | _ :: rest -> lemma_connective_evaluation op v rest

let rec lemma_connective_append (op:X.connective) (v:CS.valuation) (xs ys:list expr)
  : Lemma (connective_holds op v (xs @ ys) ==
           (if op = X.Conjunction then connective_holds op v xs && connective_holds op v ys
            else connective_holds op v xs || connective_holds op v ys))
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_connective_append op v rest ys

let rec lemma_boolean_scope_append (scope:list sort) (xs ys:list expr)
  : Lemma (requires D.scoped_args scope xs /\ D.scoped_args scope ys /\
                    X.boolean_args xs /\ X.boolean_args ys)
          (ensures D.scoped_args scope (xs @ ys) /\ X.boolean_args (xs @ ys))
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_boolean_scope_append scope rest ys

let rec lemma_boolean_arguments_match (args:list expr)
  : Lemma (requires X.boolean_args args)
          (ensures sorts_match args (R.boolean_domain args)) (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    V.lemma_sort_eq (get_sort a) bool_sort;
    lemma_boolean_arguments_match rest

let lemma_connective_at (#base:sort -> Type0) (s:S.checked_schema)
                        (bc:S.boolean_carrier base) (core:T.scalar_model base)
                        (other:V.interpretation base (S.signature s))
                        (scope:list sort) (rho:V.environment base (S.signature s) scope)
                        (op:X.connective) (args:list expr)
  : Lemma (requires D.scoped_args scope args /\ X.boolean_args args)
          (ensures T.truth_at s bc core other scope rho (App (X.connective_decl op args) args) ==
                   connective_holds op (T.truth_at s bc core other scope rho) args) =
  lemma_domain args;
  lemma_boolean_arguments_match args;
  X.lemma_connective_decl op args;
  let operator = if op = X.Conjunction then B.And else B.Or in
  assert (T.classify (X.connective_decl op args) == T.Nary operator);
  T.lemma_evaluate_core_at s bc core other scope rho (X.connective_decl op args) args;
  T.lemma_boolean_arguments_at s bc core other scope rho args (R.boolean_domain args) operator;
  lemma_connective_evaluation op (T.truth_at s bc core other scope rho) args

let rec lemma_flatten_expr (#base:sort -> Type0) (s:S.checked_schema)
                          (bc:S.boolean_carrier base) (core:T.scalar_model base)
                          (other:V.interpretation base (S.signature s))
                          (scope:list sort) (rho:V.environment base (S.signature s) scope)
                          (op:X.connective) (e:expr)
  : Lemma (requires D.scoped scope e /\ get_sort e == bool_sort)
          (ensures D.scoped_args scope (X.flatten_expr op e) /\
                   X.boolean_args (X.flatten_expr op e) /\
                   connective_holds op (T.truth_at s bc core other scope rho) (X.flatten_expr op e) ==
                   T.truth_at s bc core other scope rho e)
          (decreases e) =
  match e with
  | App f args ->
    if X.connective_app op f args then (
      lemma_flatten_args s bc core other scope rho op args;
      lemma_connective_at s bc core other scope rho op args)
  | _ -> ()

and lemma_flatten_args (#base:sort -> Type0) (s:S.checked_schema)
                       (bc:S.boolean_carrier base) (core:T.scalar_model base)
                       (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (op:X.connective) (args:list expr)
  : Lemma (requires D.scoped_args scope args /\ X.boolean_args args)
          (ensures D.scoped_args scope (X.flatten_args op args) /\
                   X.boolean_args (X.flatten_args op args) /\
                   connective_holds op (T.truth_at s bc core other scope rho) (X.flatten_args op args) ==
                   connective_holds op (T.truth_at s bc core other scope rho) args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_flatten_expr s bc core other scope rho op a;
    lemma_flatten_args s bc core other scope rho op rest;
    lemma_boolean_scope_append scope (X.flatten_expr op a) (X.flatten_args op rest);
    lemma_connective_append op (T.truth_at s bc core other scope rho)
      (X.flatten_expr op a) (X.flatten_args op rest)

let lemma_flatten_rewrite (#base:sort -> Type0) (s:S.checked_schema)
                         (bc:S.boolean_carrier base) (core:T.scalar_model base)
                         (other:V.interpretation base (S.signature s))
                         (scope:list sort) (rho:V.environment base (S.signature s) scope)
                         (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ X.flatten_rewrite a == Some b)
          (ensures T.evaluate_at s bc core other scope rho a ==
                   T.evaluate_at s bc core other scope rho b) =
  match a with
  | App f args ->
    let op = if f.decl_name = "and" then X.Conjunction else X.Disjunction in
    lemma_flatten_args s bc core other scope rho op args;
    lemma_connective_at s bc core other scope rho op args;
    lemma_connective_at s bc core other scope rho op (X.flatten_args op args);
    T.lemma_boolean s bc (T.evaluate_at s bc core other scope rho a);
    T.lemma_boolean s bc (T.evaluate_at s bc core other scope rho b)
  | _ -> ()
