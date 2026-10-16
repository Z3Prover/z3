module Z3DistinctEmbed

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3BooleanRewrite
module T = Z3BasicExprTheory
module A = Z3DistinctAst

let distinct_sound (i:interpretation value) : prop =
  forall (f:func_decl) (args:list expr) (rho:env value).
    {:pattern (eval i (App f args) rho)}
    A.distinct_app f args ==>
    (lit_true i rho (App f args) <==> T.distinct_values (eval_args i args rho))

let embedding_model (i:interpretation value) : prop =
  boolean_model i /\ not_sound i /\ eq_sound i /\ and_sound i /\ or_sound i /\
  true_sound i /\ distinct_sound i

let rec lemma_disequalities_from (i:interpretation value) (rho:env value)
                                 (a:expr) (args:list expr)
  : Lemma (requires embedding_model i)
          (ensures conj_holds i rho (A.disequalities_from a args) <==>
                   T.distinct_from (eval i a rho) (eval_args i args rho))
          (decreases args) =
  match args with
  | [] -> ()
  | b :: rest ->
    lemma_not_relates i rho not_decl (mk_eq_expr a b);
    lemma_disequalities_from i rho a rest;
    match eval i (mk_eq_expr a b) rho with VBool _ -> () | _ -> ()

let rec lemma_disequalities (i:interpretation value) (rho:env value) (args:list expr)
  : Lemma (requires embedding_model i)
          (ensures conj_holds i rho (A.disequalities args) <==>
                   T.distinct_values (eval_args i args rho))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_disequalities_from i rho a rest;
    lemma_disequalities i rho rest;
    lemma_connective_append Conjunction i rho (A.disequalities_from a rest)
                            (A.disequalities rest)

let lemma_expanded (i:interpretation value) (rho:env value) (args:list expr)
  : Lemma (requires embedding_model i)
          (ensures lit_true i rho (A.expanded args) <==>
                   T.distinct_values (eval_args i args rho)) =
  match args with
  | [] | [_] -> ()
  | [a; b] ->
    lemma_disequalities_from i rho a [b]
  | _ -> lemma_disequalities i rho args

let apply_lemma_distinct (e:expr) : option expr =
  match A.distinct_parts e with
  | Some args -> Some (A.expanded args)
  | None -> None

let lemma_apply_lemma_distinct_sound (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires embedding_model i /\ Some? (apply_lemma_distinct e))
          (ensures eval i e rho == eval i (Some?.v (apply_lemma_distinct e)) rho) =
  match e with
  | App f args ->
    lemma_expanded i rho args;
    A.lemma_expanded_sort args;
    match eval i e rho, eval i (A.expanded args) rho with
    | VBool _, VBool _ -> ()
    | _, _ -> ()
  | _ -> ()

let negation (e:expr) : option expr =
  match e with
  | App f [a] -> if f = not_decl && get_sort a = bool_sort then Some a else None
  | _ -> None

let lemma_negation (i:interpretation value) (rho:env value) (e a:expr)
  : Lemma (requires embedding_model i /\ negation e == Some a)
          (ensures lit_true i rho e <==> ~(lit_true i rho a)) =
  match e with
  | App f [_] ->
    lemma_not_relates i rho f a;
    match eval i a rho with VBool _ -> () | _ -> ()
  | _ -> ()

let distinct_clause (a b:expr) : bool =
  (match negation a with
   | Some d -> apply_lemma_distinct d = Some b
   | None -> false) ||
  (match apply_lemma_distinct a with
   | Some p -> negation b = Some p || negation p = Some b
   | None -> false)

let distinct_axiom (e:expr) : bool =
  match e with
  | App f [a; b] ->
    connective_app Disjunction f [a; b] &&
    (distinct_clause a b || distinct_clause b a)
  | _ -> false

let lemma_distinct_clause (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires embedding_model i /\ distinct_clause a b)
          (ensures lit_true i rho a \/ lit_true i rho b) =
  if (match negation a with Some d -> apply_lemma_distinct d = Some b | None -> false) then (
    let d = Some?.v (negation a) in
    lemma_apply_lemma_distinct_sound i rho d;
    lemma_negation i rho a d)
  else (
    lemma_apply_lemma_distinct_sound i rho a;
    let p = Some?.v (apply_lemma_distinct a) in
    if negation b = Some p then lemma_negation i rho b p
    else lemma_negation i rho p b)

let lemma_distinct_axiom_sound (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires embedding_model i /\ distinct_axiom e)
          (ensures lit_true i rho e) =
  match e with
  | App _ [a; b] ->
    if distinct_clause a b then lemma_distinct_clause i rho a b
    else lemma_distinct_clause i rho b a
  | _ -> ()
