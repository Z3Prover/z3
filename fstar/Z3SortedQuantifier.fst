module Z3SortedQuantifier

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3Definitions
module R = Z3ResolutionProofTheory
module BR = Z3BooleanRewrite
module SB = Z3BinderSubstitution
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

let rec quantifier_free (e:expr) : Tot bool (decreases e) =
  match e with
  | Var _ _ -> true
  | App _ args -> quantifier_free_args args
  | Quantifier _ _ _ _ -> false

and quantifier_free_args (args:list expr) : Tot bool (decreases args) =
  match args with [] -> true | e :: rest -> quantifier_free e && quantifier_free_args rest

(* Standard universal truth semantics, over sort-indexed assignments.
   Unlike elimination alone, this also supports universal introduction.
   This constrains the operator independently of any proof certificate. *)
let forall_model (#base:sort -> Type0) (s:S.checked_schema)
                 (bc:S.boolean_carrier base)
                 (other:V.interpretation base (S.signature s)) : prop =
  forall (bound:list sort)
         (body:V.arguments base (S.signature s) (L.rev bound) ->
               V.value base (S.signature s) bool_sort).
    T.truth_value s bc (other.quantification Forall_k bound bool_sort body) <==>
    (forall (vs:V.arguments base (S.signature s) (L.rev bound)).
       T.truth_value s bc (body vs))

let lemma_forall_truth (#base:sort -> Type0) (s:S.checked_schema)
                       (bc:S.boolean_carrier base) (eq:T.scalar_equality base)
                       (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (bound:list sort) (body:expr)
  : Lemma (requires forall_model s bc other /\
                    D.scoped (L.rev bound @ scope) body /\ get_sort body == bool_sort)
          (ensures
            T.truth_at s bc eq other scope rho (Quantifier Forall_k bound bool_sort body) <==>
            (forall (vs:V.arguments base (S.signature s) (L.rev bound)).
               T.truth_at s bc eq other (L.rev bound @ scope)
                 (V.extend (S.signature s) scope (L.rev bound) vs rho) body)) =
  let f = V.typed_body (S.signature s) bound bool_sort
    (V.evaluate_body (S.signature s) (T.interpretation s bc eq other) scope rho bound body) in
  assert (T.truth_value s bc (other.quantification Forall_k bound bool_sort f) <==>
          (forall (vs:V.arguments base (S.signature s) (L.rev bound)).
             T.truth_value s bc (f vs)))

let rec append_arguments (#base:sort -> Type0) (sigma:V.signature) (xs ys:list sort)
                         (vs:V.arguments base sigma xs) (ws:V.arguments base sigma ys)
  : Tot (V.arguments base sigma (xs @ ys)) (decreases xs) =
  match xs, vs with
  | [], [] -> ws
  | _ :: rest, v :: tail -> v :: append_arguments sigma rest ys tail ws
  | _, _ -> FStar.Pervasives.false_elim ()

let rec split_arguments (#base:sort -> Type0) (sigma:V.signature) (xs ys:list sort)
                        (vs:V.arguments base sigma (xs @ ys))
  : Tot (p:(V.arguments base sigma xs & V.arguments base sigma ys){
           append_arguments sigma xs ys (fst p) (snd p) == vs})
        (decreases xs) =
  match xs, vs with
  | [], _ -> [], vs
  | _ :: rest, v :: tail ->
    let left, right = split_arguments sigma rest ys tail in
    v :: left, right
  | _, _ -> FStar.Pervasives.false_elim ()

let rec lemma_extend_append (#base:sort -> Type0) (sigma:V.signature)
                            (scope xs ys:list sort)
                            (vs:V.arguments base sigma xs) (ws:V.arguments base sigma ys)
                            (rho:V.environment base sigma scope)
                            (n:nat{n < L.length ((xs @ ys) @ scope)})
  : Lemma (ensures
            (let _ = LP.append_assoc xs ys scope in
             V.extend sigma scope (xs @ ys) (append_arguments sigma xs ys vs ws) rho n ==
             V.extend sigma (ys @ scope) xs vs (V.extend sigma scope ys ws rho) n))
          (decreases xs) =
  LP.append_assoc xs ys scope;
  match xs, vs with
  | [], [] -> ()
  | _ :: rest, _ :: tail ->
    if n > 0 then lemma_extend_append sigma scope rest ys tail ws rho (n - 1)
  | _, _ -> ()

(* Pointwise environments suffice for quantifier-free bodies; no function
   equality or additional extensionality premise is needed. *)
let rec lemma_free_environments (#base:sort -> Type0) (sigma:V.signature)
                               (i:V.interpretation base sigma) (scope:list sort)
                               (rho eta:V.environment base sigma scope) (e:expr)
  : Lemma (requires D.scoped scope e /\ quantifier_free e /\
                    (forall (n:nat{n < L.length scope}). rho n == eta n))
          (ensures V.evaluate sigma i scope rho e == V.evaluate sigma i scope eta e)
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App f args -> lemma_free_args_environments sigma i scope rho eta args f.domain
  | Quantifier _ _ _ _ -> ()

and lemma_free_args_environments (#base:sort -> Type0) (sigma:V.signature)
                                (i:V.interpretation base sigma) (scope:list sort)
                                (rho eta:V.environment base sigma scope)
                                (args:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss /\ quantifier_free_args args /\
                    (forall (n:nat{n < L.length scope}). rho n == eta n))
          (ensures V.evaluate_args sigma i scope rho args ss ==
                   V.evaluate_args sigma i scope eta args ss)
          (decreases args) =
  match args, ss with
  | e :: rest, _ :: tail ->
    lemma_free_environments sigma i scope rho eta e;
    lemma_free_args_environments sigma i scope rho eta rest tail
  | _, _ -> ()

let flatten (a b:expr) : bool =
  match a, b with
  | Quantifier Forall_k outer t (Quantifier Forall_k inner u body),
    Quantifier Forall_k combined v body' ->
    t = bool_sort && u = bool_sort && v = bool_sort &&
    get_sort body = bool_sort && combined = outer @ inner &&
    body = body' && quantifier_free body
  | _, _ -> false

let check_flatten (formula:expr) : bool =
  D.scoped [] formula &&
  (match formula with
   | App f [a; b] -> f = R.eq_decl bool_sort && (flatten a b || flatten b a)
   | _ -> false)

let lemma_flatten (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                  (a b:expr)
  : Lemma (requires forall_model s bc other /\ D.scoped [] a /\ D.scoped [] b /\ flatten a b)
          (ensures T.evaluate s bc eq other a == T.evaluate s bc eq other b) =
  match a, b with
  | Quantifier Forall_k outer _ (Quantifier Forall_k inner _ body),
    Quantifier Forall_k _ _ _ ->
    let sigma = S.signature s in
    let rho = T.empty_environment sigma in
    let xs = L.rev inner in
    let ys = L.rev outer in
    LP.rev_append outer inner;
    LP.append_assoc xs ys [];
    lemma_forall_truth s bc eq other [] rho outer (Quantifier Forall_k inner bool_sort body);
    lemma_forall_truth s bc eq other [] rho (outer @ inner) body;
    let outside (ws:V.arguments base sigma ys)
      : Lemma (T.truth_at s bc eq other (ys @ []) (V.extend sigma [] ys ws rho)
                 (Quantifier Forall_k inner bool_sort body) <==>
               (forall (vs:V.arguments base sigma xs).
                 T.truth_at s bc eq other ((xs @ ys) @ [])
                   (V.extend sigma [] (xs @ ys) (append_arguments sigma xs ys vs ws) rho) body)) =
      lemma_forall_truth s bc eq other (ys @ []) (V.extend sigma [] ys ws rho) inner body;
      let inside (vs:V.arguments base sigma xs)
        : Lemma (T.truth_at s bc eq other ((xs @ ys) @ [])
                   (V.extend sigma [] (xs @ ys) (append_arguments sigma xs ys vs ws) rho) body ==
                 T.truth_at s bc eq other (xs @ (ys @ []))
                   (V.extend sigma (ys @ []) xs vs (V.extend sigma [] ys ws rho)) body) =
        let indices (n:nat{n < L.length ((xs @ ys) @ [])})
          : Lemma (V.extend sigma [] (xs @ ys) (append_arguments sigma xs ys vs ws) rho n ==
                   V.extend sigma (ys @ []) xs vs (V.extend sigma [] ys ws rho) n) =
          lemma_extend_append sigma [] xs ys vs ws rho n in
        FStar.Classical.forall_intro indices;
        lemma_free_environments sigma (T.interpretation s bc eq other) ((xs @ ys) @ [])
          (V.extend sigma [] (xs @ ys) (append_arguments sigma xs ys vs ws) rho)
          (V.extend sigma (ys @ []) xs vs (V.extend sigma [] ys ws rho)) body in
      FStar.Classical.forall_intro inside in
    FStar.Classical.forall_intro outside;
    let forward (_:squash (T.truth s bc eq other a))
      : Lemma (T.truth s bc eq other b) =
      let combined (vs:V.arguments base sigma (xs @ ys))
        : Lemma (T.truth_at s bc eq other ((xs @ ys) @ [])
                   (V.extend sigma [] (xs @ ys) vs rho) body) =
        let left, right = split_arguments sigma xs ys vs in
        outside right in
      FStar.Classical.forall_intro combined in
    FStar.Classical.impl_intro forward;
    let backward (_:squash (T.truth s bc eq other b))
      : Lemma (T.truth s bc eq other a) =
      let outside' (ws:V.arguments base sigma ys)
        : Lemma (T.truth_at s bc eq other (ys @ []) (V.extend sigma [] ys ws rho)
                   (Quantifier Forall_k inner bool_sort body)) =
        let inside' (vs:V.arguments base sigma xs)
          : Lemma (T.truth_at s bc eq other ((xs @ ys) @ [])
                     (V.extend sigma [] (xs @ ys) (append_arguments sigma xs ys vs ws) rho) body) =
          () in
        FStar.Classical.forall_intro inside';
        outside ws in
      FStar.Classical.forall_intro outside' in
    FStar.Classical.impl_intro backward;
    assert (T.truth s bc eq other a <==> T.truth s bc eq other b);
    T.lemma_boolean s bc (T.evaluate s bc eq other a);
    T.lemma_boolean s bc (T.evaluate s bc eq other b)
  | _, _ -> ()

let lemma_check_flatten (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                        (formula:expr)
  : Lemma (requires forall_model s bc other /\ check_flatten formula)
          (ensures T.truth s bc eq other formula) =
  match formula with
  | App _ [a; b] ->
    if flatten a b then lemma_flatten s bc eq other a b
    else lemma_flatten s bc eq other b a;
    T.lemma_equality s bc eq other a b
  | _ -> ()

(* This constrains the logical operator, not the validity of a proof rule. *)
let forall_elimination_model (#base:sort -> Type0) (s:S.checked_schema)
                             (bc:S.boolean_carrier base)
                             (other:V.interpretation base (S.signature s)) : prop =
  forall (bound:list sort)
         (body:V.arguments base (S.signature s) (L.rev bound) ->
               V.value base (S.signature s) bool_sort)
         (vs:V.arguments base (S.signature s) (L.rev bound)).
    T.truth_value s bc (other.quantification Forall_k bound bool_sort body) ==>
    T.truth_value s bc (body vs)

let check (args:list expr) (formula:expr) : bool =
  match formula with
  | App f [App n [Quantifier Forall_k bs t body]; inst] ->
    D.scoped [] formula &&
    f = BR.connective_decl BR.Disjunction [App n [Quantifier Forall_k bs t body]; inst] &&
    n = R.not_decl && t = bool_sort &&
    D.scoped_args [] args && sorts_match (L.rev args) (L.rev bs) &&
    quantifier_free body && SB.substitute (L.rev args) body = Some inst
  | _ -> false

let lemma_forall_elimination (#base:sort -> Type0) (s:S.checked_schema)
                             (bc:S.boolean_carrier base)
                             (other:V.interpretation base (S.signature s))
                             (bound:list sort)
                             (body:V.arguments base (S.signature s) (L.rev bound) ->
                                   V.value base (S.signature s) bool_sort)
                             (vs:V.arguments base (S.signature s) (L.rev bound))
  : Lemma (requires forall_elimination_model s bc other)
          (ensures T.truth_value s bc (other.quantification Forall_k bound bool_sort body) ==>
                   T.truth_value s bc (body vs)) =
  ()

let rec lemma_lookup (#base:sort -> Type0) (sigma:V.signature)
                     (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                     (args:list expr) (ss:list sort)
                     (n:nat{n < L.length ss /\ n < L.length (ss @ [])})
                     (t:sort) (term:expr)
  : Lemma (requires D.scoped_args [] args /\ sorts_match args ss /\ D.scoped [] term /\
                    SB.arguments args n t == Some term)
          (ensures V.extend sigma [] ss (V.evaluate_args sigma i [] rho args ss) rho n ==
                   V.evaluate sigma i [] rho term)
          (decreases args) =
  match args, ss with
  | _ :: rest, _ :: tail ->
    if n > 0 then lemma_lookup sigma i rho rest tail (n - 1) t term
  | _, _ -> ()

let rec lemma_substitute (#base:sort -> Type0) (sigma:V.signature)
                         (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                         (args:list expr) (ss:list sort) (body result:expr)
  : Lemma (requires D.scoped_args [] args /\ sorts_match args ss /\
                    D.scoped (ss @ []) body /\ D.scoped [] result /\ quantifier_free body /\
                    SB.substitute args body == Some result)
          (ensures V.evaluate sigma i (ss @ [])
                     (V.extend sigma [] ss (V.evaluate_args sigma i [] rho args ss) rho) body ==
                   V.evaluate sigma i [] rho result)
          (decreases body) =
  match body, result with
  | Var n t, _ ->
    LP.append_l_nil ss;
    lemma_lookup sigma i rho args ss n t result
  | App f xs, App _ ys ->
    lemma_substitute_args sigma i rho args ss xs ys f.domain
  | _, _ -> ()

and lemma_substitute_args (#base:sort -> Type0) (sigma:V.signature)
                          (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                          (args:list expr) (ss:list sort) (xs ys:list expr) (domain:list sort)
  : Lemma (requires D.scoped_args [] args /\ sorts_match args ss /\
                    D.scoped_args (ss @ []) xs /\ D.scoped_args [] ys /\
                    sorts_match xs domain /\ sorts_match ys domain /\ quantifier_free_args xs /\
                    SB.apply_args (SB.arguments args) xs == Some ys)
          (ensures V.evaluate_args sigma i (ss @ [])
                     (V.extend sigma [] ss (V.evaluate_args sigma i [] rho args ss) rho) xs domain ==
                   V.evaluate_args sigma i [] rho ys domain)
          (decreases xs) =
  match xs, ys, domain with
  | x :: rest, y :: tail, _ :: remaining ->
    lemma_substitute sigma i rho args ss x y;
    lemma_substitute_args sigma i rho args ss rest tail remaining
  | _, _, _ -> ()

(* What `check` establishes about the shape it accepts, in a small context:
   the scoping of each part and the classification of the two connectives. *)
let lemma_check_parts (args:list expr) (f n:func_decl) (bs:list sort) (t:sort) (body inst:expr)
  : Lemma (requires check args (App f [App n [Quantifier Forall_k bs t body]; inst]))
          (ensures D.scoped [] (App f [App n [Quantifier Forall_k bs t body]; inst]) /\
                   D.scoped [] (App n [Quantifier Forall_k bs t body]) /\
                   D.scoped (L.rev bs @ []) body /\ D.scoped [] inst /\ t == bool_sort /\
                   T.classify f == T.Nary Z3BoundedBoolEquiv.Or /\ T.classify n == T.Negation /\
                   D.scoped_args [] args /\ sorts_match (L.rev args) (L.rev bs) /\
                   quantifier_free body /\ SB.substitute (L.rev args) body == Some inst) =
  assert_norm (T.classify R.not_decl == T.Negation);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [App n [Quantifier Forall_k bs t body]; inst]) ==
               T.Nary Z3BoundedBoolEquiv.Or)

(* A two-argument disjunction of atoms, unfolded once. *)
let lemma_or_pair (v:expr -> bool) (a b:expr)
  : Lemma (Z3BoundedBoolEquiv.eval_args v Z3BoundedBoolEquiv.Or (L.map Z3BoundedBoolEquiv.Atom [a; b]) ==
           (v a || v b)) =
  assert_norm (Z3BoundedBoolEquiv.eval_args v Z3BoundedBoolEquiv.Or (L.map Z3BoundedBoolEquiv.Atom [a; b]) ==
               (v a || v b))

let lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                (args:list expr) (formula:expr)
  : Lemma (requires forall_elimination_model s bc other /\ check args formula)
          (ensures T.truth s bc eq other formula) =
  match formula with
  | App f [App n [Quantifier Forall_k bs t body]; inst] ->
    lemma_check_parts args f n bs t body inst;
    let sigma = S.signature s in
    let i = T.interpretation s bc eq other in
    let rho = T.empty_environment sigma in
    let scope = L.rev bs in
    let actuals = L.rev args in
    Z3QuantifierInstantiation.lemma_scoped_reverse_acc [] args [];
    let vs = V.evaluate_args sigma i [] rho actuals scope in
    let function_body = V.typed_body sigma bs bool_sort
      (V.evaluate_body sigma i [] rho bs body) in
    LP.append_l_nil scope;
    lemma_substitute sigma i rho actuals scope body inst;
    T.lemma_negation s bc eq other n (Quantifier Forall_k bs t body);
    T.lemma_nary s bc eq other f [App n [Quantifier Forall_k bs t body]; inst]
      Z3BoundedBoolEquiv.Or;
    lemma_or_pair (T.truth s bc eq other) (App n [Quantifier Forall_k bs t body]) inst;
    assert (T.evaluate s bc eq other (Quantifier Forall_k bs t body) ==
            other.quantification Forall_k bs bool_sort function_body);
    lemma_forall_elimination s bc other bs function_body vs;
    assert (function_body vs == V.evaluate sigma i [] rho inst)
  | _ -> ()
