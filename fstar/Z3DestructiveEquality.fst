module Z3DestructiveEquality

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open FStar.List.Tot
module B = Z3BooleanRewrite
module N = Z3QuantifierNnf
module P = Z3QuantifierPull
module S = Z3BinderSubstitution
module R = Z3QuantifierReduce
module L = FStar.List.Tot

let connective (kind:quantifier_kind) : B.connective =
  if kind = Forall_k then B.Disjunction else B.Conjunction

let make_body (kind:quantifier_kind) (args:list expr) : expr =
  App (B.connective_decl (connective kind) args) args

let literals (kind:quantifier_kind) (body:expr) : list expr =
  B.flatten_expr (connective kind) body

let desired_guard (kind:quantifier_kind) (variable:nat) (term:expr) : expr =
  let eq = mk_eq_expr (Var variable (get_sort term)) term in
  if kind = Forall_k then mk_not_expr eq else eq

let reversed_guard (kind:quantifier_kind) (variable:nat) (term:expr) : expr =
  let eq = mk_eq_expr term (Var variable (get_sort term)) in
  if kind = Forall_k then mk_not_expr eq else eq

let guard_ok (kind:quantifier_kind) (bound:nat) (guard:expr) (variable:nat) (term:expr) : bool =
  variable < bound && get_sort guard = bool_sort && not (S.occurs variable 0 term) &&
  (B.boolean_equiv 8 10 guard (desired_guard kind variable term) ||
   B.boolean_equiv 8 10 guard (reversed_guard kind variable term))

let equation_candidate (e:expr) : option (nat & expr) =
  match e with
  | App f [Var n s; term] ->
    if f = eq_decl s && get_sort term = s then Some (n, term) else None
  | App f [term; Var n s] ->
    if f = eq_decl s && get_sort term = s then Some (n, term) else None
  | _ -> None

let candidate (kind:quantifier_kind) (e:expr) : option (nat & expr) =
  if kind = Forall_k then
    match e with
    | App f [Var n s] ->
      if f = not_decl && s = bool_sort then Some (n, true_expr) else None
    | App f [eq] -> if f = not_decl then equation_candidate eq else None
    | Var n s -> if s = bool_sort then Some (n, false_expr) else None
    | App f [a; b] ->
      if f = eq_decl bool_sort then
        (match a, b with
         | Var n s, term | term, Var n s ->
           if s = bool_sort then Some (n, mk_not_expr term) else None
         | App n [Var v s], term | term, App n [Var v s] ->
           if n = not_decl && s = bool_sort then Some (v, term) else None
         | _, _ -> None)
      else None
    | _ -> None
  else
    match e with
    | Var n s -> if s = bool_sort then Some (n, true_expr) else None
    | App f [Var n s] ->
      if f = not_decl && s = bool_sort then Some (n, false_expr) else None
    | _ -> equation_candidate e

let swap_guard (e:expr) : expr =
  match e with
  | App f [a; b] -> App f [b; a]
  | App f [App g [a; b]] -> App f [App g [b; a]]
  | _ -> e

let checked_candidate (kind:quantifier_kind) (bound:nat) (guard:expr) : option (nat & expr) =
  match candidate kind guard with
  | Some (v, t) ->
    if guard_ok kind bound guard v t then Some (v, t)
    else (match candidate kind (swap_guard guard) with
          | Some (v, t) -> if guard_ok kind bound guard v t then Some (v, t) else None
          | None -> None)
  | None ->
    (match candidate kind (swap_guard guard) with
     | Some (v, t) -> if guard_ok kind bound guard v t then Some (v, t) else None
     | None -> None)

let rec find_guard (kind:quantifier_kind) (bound:nat) (args:list expr)
  : Tot (option (list expr & expr & nat & expr & list expr)) (decreases args) =
  match args with
  | [] -> None
  | guard :: rest ->
    let next () =
      match find_guard kind bound rest with
      | Some (prefix, g, v, t, suffix) -> Some (guard :: prefix, g, v, t, suffix)
      | None -> None in
    (match checked_candidate kind bound guard with
     | Some (variable, term) ->
       if guard_ok kind bound guard variable term
       then Some ([], guard, variable, term, rest)
       else next ()
     | None -> next ())

let rec lemma_find_guard (kind:quantifier_kind) (bound:nat) (args:list expr)
  : Lemma (ensures (match find_guard kind bound args with
                    | Some (prefix, guard, variable, term, suffix) ->
                      args == prefix @ (guard :: suffix) /\ guard_ok kind bound guard variable term
                    | None -> True))
          (decreases args)
  = match args with [] -> () | _ :: rest -> lemma_find_guard kind bound rest

let lemma_literals (i:interpretation value) (rho:env value)
                   (kind:quantifier_kind) (body:expr)
  : Lemma (requires B.boolean_rewrite_model i /\ get_sort body = bool_sort)
          (ensures eval i body rho == eval i (make_body kind (literals kind body)) rho)
  = B.lemma_flatten_expr_sound (connective kind) i rho body;
    match eval i body rho, eval i (make_body kind (literals kind body)) rho with
    | VBool _, VBool _ -> ()
    | _, _ -> ()

let lemma_context (i:interpretation value) (rho:env value) (kind:quantifier_kind)
                  (bound:nat) (prefix suffix:list expr) (guard:expr) (variable:nat) (term:expr)
  : Lemma (requires B.boolean_rewrite_model i /\ guard_ok kind bound guard variable term /\
                    (kind = Forall_k \/ kind = Exists_k))
          (ensures P.body_truth i (make_body kind (prefix @ (guard :: suffix)))
                                  (kind = Exists_k) rho <==>
                   (rho variable == eval i term rho ==>
                    P.body_truth i (make_body kind (prefix @ suffix)) (kind = Exists_k) rho))
  = let direct = B.boolean_equiv 8 10 guard (desired_guard kind variable term) in
    (if direct
     then B.lemma_boolean_equiv_sound 8 10 i rho guard (desired_guard kind variable term)
     else B.lemma_boolean_equiv_sound 8 10 i rho guard (reversed_guard kind variable term));
    let eq = if direct then mk_eq_expr (Var variable (get_sort term)) term
             else mk_eq_expr term (Var variable (get_sort term)) in
    assert (lit_true i rho eq <==> rho variable == eval i term rho);
    if kind = Forall_k then N.lemma_not_truth i rho eq;
    B.lemma_connective_append (connective kind) i rho prefix (guard :: suffix);
    B.lemma_connective_append (connective kind) i rho prefix suffix

let lemma_all (i:interpretation value) (rho:env value) (kind:quantifier_kind) (bound:nat)
              (prefix suffix:list expr) (guard:expr) (variable:nat) (term result:expr)
  : Lemma (requires quant_extensional i /\ B.boolean_rewrite_model i /\
                    guard_ok kind bound guard variable term /\
                    (kind = Forall_k \/ kind = Exists_k) /\
                    S.apply (S.replace_one variable term) (make_body kind (prefix @ suffix)) == Some result)
          (ensures P.all_bodies i (make_body kind (prefix @ (guard :: suffix)))
                                 (kind = Exists_k) bound rho <==>
                   P.all_bodies i result (kind = Exists_k) bound rho)
  = let source = make_body kind (prefix @ (guard :: suffix)) in
    let rest = make_body kind (prefix @ suffix) in
    let negative = kind = Exists_k in
    let forward (_:squash (P.all_bodies i source negative bound rho))
      : Lemma (P.all_bodies i result negative bound rho)
      = let bodies (vs:list value{L.length vs = bound})
          : Lemma (P.body_truth i result negative (shift vs rho))
          = let v = eval i term (shift vs rho) in
            let assigned = S.update vs variable v in
            S.lemma_update_length vs variable v;
            let indices (n:nat)
              : Lemma (n <> variable ==> shift assigned rho n == shift vs rho n)
              = S.lemma_update_at vs variable v rho n in
            FStar.Classical.forall_intro indices;
            S.lemma_avoids i term variable 0 (shift assigned rho) (shift vs rho);
            S.lemma_update_at vs variable v rho variable;
            assert (P.body_truth i source negative (shift assigned rho));
            lemma_context i (shift assigned rho) kind bound prefix suffix guard variable term;
            S.lemma_replace_one i rho vs variable term rest result in
        FStar.Classical.forall_intro bodies in
    FStar.Classical.impl_intro forward;
    let backward (_:squash (P.all_bodies i result negative bound rho))
      : Lemma (P.all_bodies i source negative bound rho)
      = let bodies (vs:list value{L.length vs = bound})
          : Lemma (P.body_truth i source negative (shift vs rho))
          = assert (P.body_truth i result negative (shift vs rho));
            lemma_context i (shift vs rho) kind bound prefix suffix guard variable term;
            let equal (_:squash (shift vs rho variable == eval i term (shift vs rho)))
              : Lemma (P.body_truth i rest negative (shift vs rho))
              = S.lemma_replace_equal i (shift vs rho) variable term rest result in
            FStar.Classical.impl_intro equal in
        FStar.Classical.forall_intro bodies in
    FStar.Classical.impl_intro backward

let once (e:expr) : option expr =
  match e with
  | Quantifier k bs s body ->
    if (k = Forall_k || k = Exists_k) && s = bool_sort && get_sort body = bool_sort then
      let args = literals k body in
      if not (P.boolean_args args) then None
      else (match find_guard k (L.length bs) args with
            | Some (prefix, _, variable, term, suffix) ->
              (match S.apply (S.replace_one variable term) (make_body k (prefix @ suffix)) with
               | Some result -> Some (Quantifier k bs bool_sort result)
               | None -> None)
            | None -> None)
    else None
  | _ -> None

let lemma_once (i:interpretation value) (rho:env value) (e result:expr)
  : Lemma (requires quant_extensional i /\ N.quantifier_model i /\ B.boolean_rewrite_model i /\
                    once e == Some result)
          (ensures eval i e rho == eval i result rho)
  = match e with
    | Quantifier k bs s body ->
      let args = literals k body in
      lemma_find_guard k (L.length bs) args;
      (match find_guard k (L.length bs) args with
       | Some (prefix, guard, variable, term, suffix) ->
         let rest = make_body k (prefix @ suffix) in
         (match S.apply (S.replace_one variable term) rest with
          | Some b ->
            let sample = P.sample_values (L.length bs) in
            S.lemma_replace_one i rho sample variable term rest b;
            N.lemma_quantifier_truth i rho k bs body;
            N.lemma_quantifier_truth i rho k bs b;
            let bodies (vs:list value{L.length vs = L.length bs})
              : Lemma (eval i body (shift vs rho) ==
                       eval i (make_body k args) (shift vs rho))
              = lemma_literals i (shift vs rho) k body in
            FStar.Classical.forall_intro bodies;
            lemma_all i rho k (L.length bs) prefix suffix guard variable term b;
            (match eval i e rho, eval i result rho with
            | VBool _, VBool _ -> ()
            | _, _ -> ())
          | None -> ())
       | None -> ())
    | _ -> ()

let rec normalize (fuel:nat) (e:expr) : Tot (option expr) (decreases fuel) =
  if fuel = 0 then None
  else let next:nat = fuel - 1 in
  match once e with
       | Some e' -> normalize next e'
       | None -> Some e

let rec lemma_normalize (fuel:nat) (i:interpretation value) (rho:env value) (e result:expr)
  : Lemma (requires quant_extensional i /\ N.quantifier_model i /\ B.boolean_rewrite_model i /\
                    normalize fuel e == Some result)
          (ensures eval i e rho == eval i result rho)
          (decreases fuel)
  = if fuel = 0 then ()
    else let next:nat = fuel - 1 in
    match once e with
         | Some e' -> lemma_once i rho e e'; lemma_normalize next i rho e' result
         | None -> ()

let check (a b:expr) : bool =
  match normalize 64 a with Some a' -> R.equivalent 64 a' b | None -> false

let lemma_check (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires quant_extensional i /\ N.quantifier_model i /\ B.boolean_rewrite_model i /\
                    check a b)
          (ensures eval i a rho == eval i b rho)
  = match normalize 64 a with
    | Some a' -> lemma_normalize 64 i rho a a'; R.lemma_equivalent 64 i rho a' b
    | None -> ()
