module Z3QuantifierVacuityScope

open Z3AstTheory
open FStar.List.Tot
module D = Z3ExprScope
module V = Z3QuantifierVacuitySyntax
module B = Z3ExprBinding
module Sub = Z3Substitution
module DV = Z3DatatypeValue
module SB = Z3SortedBinding
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

let lower_index (cutoff n:nat) : nat =
  if n <= cutoff then n else n - 1

let lower_substitution (cutoff:nat) : Sub.substitution =
  fun n s -> if n = cutoff then None else Some (Var (lower_index cutoff n) s)

let matches_lower (cutoff:nat) (theta:Sub.substitution) : prop =
  forall (n:nat) (s:sort). theta n s == lower_substitution cutoff n s

let lemma_under_lower (cutoff count:nat) (theta:Sub.substitution)
  : Lemma (requires matches_lower cutoff theta)
          (ensures matches_lower (cutoff + count) (Sub.under count theta)) =
  let indices (n:nat) (s:sort)
    : Lemma (Sub.under count theta n s == lower_substitution (cutoff + count) n s) =
    if n < count then ()
    else if n = cutoff + count then ()
    else () in
  FStar.Classical.forall_intro_2 indices

let rec lemma_lower_apply (cutoff:nat) (theta:Sub.substitution) (e:expr)
  : Lemma (requires matches_lower cutoff theta)
          (ensures Sub.apply theta e == V.lower cutoff e)
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App _ args -> lemma_lower_apply_args cutoff theta args
  | Quantifier _ bound _ body ->
    lemma_under_lower cutoff (L.length bound) theta;
    lemma_lower_apply (cutoff + L.length bound) (Sub.under (L.length bound) theta) body

and lemma_lower_apply_args (cutoff:nat) (theta:Sub.substitution) (args:list expr)
  : Lemma (requires matches_lower cutoff theta)
          (ensures Sub.apply_args theta args == V.lower_args cutoff args)
          (decreases args) =
  match args with
  | [] -> ()
  | e :: rest ->
    lemma_lower_apply cutoff theta e;
    lemma_lower_apply_args cutoff theta rest

let lower_scopes (cutoff:nat) (left right:list sort) : prop =
  forall (n:nat{n < L.length left /\ n <> cutoff}).
    D.scoped right (Var (lower_index cutoff n) (L.index left n))

let lemma_lower_erased_scopes (n:nat) (scope:list sort)
  : Lemma (requires n < L.length scope)
          (ensures lower_scopes n scope (V.erase n scope)) =
  let indices (j:nat{j < L.length scope /\ j <> n})
    : Lemma (D.scoped (V.erase n scope)
               (Var (lower_index n j) (L.index scope j))) =
    V.lemma_erase_index n j scope in
  FStar.Classical.forall_intro indices

let rec lemma_lower_scope_extend (cutoff:nat) (left right bound:list sort)
                                 (n:nat{n < L.length (bound @ left) /\
                                        n <> cutoff + L.length bound})
  : Lemma (requires lower_scopes cutoff left right)
          (ensures D.scoped (bound @ right)
                     (Var (lower_index (cutoff + L.length bound) n)
                          (L.index (bound @ left) n)))
          (decreases bound) =
  LP.append_length bound left;
  LP.append_length bound right;
  match bound with
  | [] -> ()
  | _ :: rest ->
    if n > 0 then lemma_lower_scope_extend cutoff left right rest (n - 1)

let rec lemma_lower_scope (cutoff:nat) (left right:list sort) (e result:expr)
  : Lemma (requires D.scoped left e /\ lower_scopes cutoff left right /\
                    V.lower cutoff e == Some result)
          (ensures D.scoped right result /\ get_sort result == get_sort e)
          (decreases e) =
  match e, result with
  | Var _ _, _ -> ()
  | App f args, App _ results ->
    lemma_lower_args_scope cutoff left right args results f.domain
  | Quantifier _ bound _ body, Quantifier _ _ _ body' ->
    LP.rev_length bound;
    let indices (n:nat{n < L.length (L.rev bound @ left) /\
                       n <> cutoff + L.length bound})
      : Lemma (D.scoped (L.rev bound @ right)
                 (Var (lower_index (cutoff + L.length bound) n)
                      (L.index (L.rev bound @ left) n))) =
      lemma_lower_scope_extend cutoff left right (L.rev bound) n in
    FStar.Classical.forall_intro indices;
    lemma_lower_scope (cutoff + L.length bound)
      (L.rev bound @ left) (L.rev bound @ right) body body'
  | _, _ -> ()

and lemma_lower_args_scope (cutoff:nat) (left right:list sort)
                           (args results:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args left args /\ sorts_match args ss /\
                    lower_scopes cutoff left right /\ V.lower_args cutoff args == Some results)
          (ensures D.scoped_args right results /\ sorts_match results ss)
          (decreases args) =
  match args, results, ss with
  | e :: rest, e' :: rest', _ :: tail ->
    lemma_lower_scope cutoff left right e e';
    lemma_lower_args_scope cutoff left right rest rest' tail
  | _, _, _ -> ()

let lemma_lower_erased_scope (n:nat) (scope:list sort) (e result:expr)
  : Lemma (requires n < L.length scope /\ D.scoped scope e /\ V.lower n e == Some result)
          (ensures D.scoped (V.erase n scope) result /\ get_sort result == get_sort e) =
  lemma_lower_erased_scopes n scope;
  lemma_lower_scope n scope (V.erase n scope) e result

let lemma_lower_evaluate (#base:sort -> Type0) (sigma:DV.signature)
                         (i:DV.interpretation base sigma) (cutoff:nat) (left right:list sort)
                         (rho:DV.environment base sigma left) (eta:DV.environment base sigma right)
                         (e result:expr)
  : Lemma (requires D.scoped left e /\ lower_scopes cutoff left right /\
                    SB.substitution_environments sigma i (lower_substitution cutoff) left right rho eta /\
                    V.lower cutoff e == Some result)
          (ensures D.scoped right result /\ get_sort e == get_sort result /\
                   DV.evaluate sigma i left rho e == DV.evaluate sigma i right eta result) =
  lemma_lower_scope cutoff left right e result;
  lemma_lower_apply cutoff (lower_substitution cutoff) e;
  SB.lemma_apply sigma i (lower_substitution cutoff) left right rho eta e result

let rec lemma_erase_append (#a:Type) (n:nat) (prefix suffix:list a)
  : Lemma (requires n < L.length prefix)
          (ensures V.erase n (prefix @ suffix) == V.erase n prefix @ suffix)
          (decreases prefix) =
  match prefix with
  | [] -> ()
  | _ :: rest -> if n > 0 then lemma_erase_append (n - 1) rest suffix

let lemma_remove_scope (n:nat) (scope:list sort) (e result:expr)
  : Lemma (requires D.scoped scope e /\ V.remove n e == Some result)
          (ensures D.scoped scope result /\ get_sort result == get_sort e) =
  match e with
  | Quantifier _ bound _ body ->
    let b = Some?.v (V.lower n body) in
    let remaining = V.erase n (L.rev bound) in
    LP.rev_length bound;
    LP.append_length (L.rev bound) scope;
    lemma_lower_erased_scope n (L.rev bound @ scope) body b;
    lemma_erase_append n (L.rev bound) scope;
    LP.rev_involutive remaining;
    (match remaining with [] -> () | _ :: _ -> ())
  | _ -> ()

let rec lemma_first_removal_scope (remaining n:nat) (scope:list sort) (e result:expr)
  : Lemma (requires D.scoped scope e /\ V.first_removal remaining n e == Some result)
          (ensures D.scoped scope result /\ get_sort result == get_sort e)
          (decreases remaining) =
  if remaining > 0 then
    match V.remove n e with
    | Some _ -> lemma_remove_scope n scope e result
    | None -> lemma_first_removal_scope (remaining - 1) (n + 1) scope e result

let lemma_step_scope (scope:list sort) (e result:expr)
  : Lemma (requires D.scoped scope e /\ V.step e == Some result)
          (ensures D.scoped scope result /\ get_sort result == get_sort e) =
  match e with
  | Quantifier _ bound _ _ -> lemma_first_removal_scope (L.length bound) 0 scope e result
  | _ -> ()

let rec erase_arguments (#base:sort -> Type0) (sigma:DV.signature) (n:nat)
                        (ss:list sort) (vs:DV.arguments base sigma ss)
  : Tot (DV.arguments base sigma (V.erase n ss)) (decreases ss) =
  match ss, vs with
  | [], [] -> []
  | _ :: rest, v :: tail ->
    if n = 0 then tail else v :: erase_arguments sigma (n - 1) rest tail
  | _, _ -> FStar.Pervasives.false_elim ()

let rec insert_argument (#base:sort -> Type0) (sigma:DV.signature) (ss:list sort)
                        (n:nat{n < L.length ss}) (v:DV.value base sigma (L.index ss n))
                        (vs:DV.arguments base sigma (V.erase n ss))
  : Tot (DV.arguments base sigma ss) (decreases ss) =
  match ss with
  | [] -> FStar.Pervasives.false_elim ()
  | _ :: rest ->
    if n = 0 then v :: vs
    else match vs with
    | x :: tail -> x :: insert_argument sigma rest (n - 1) v tail
    | [] -> FStar.Pervasives.false_elim ()

let rec lemma_erase_insert_arguments (#base:sort -> Type0) (sigma:DV.signature)
                                     (ss:list sort) (n:nat{n < L.length ss})
                                     (v:DV.value base sigma (L.index ss n))
                                     (vs:DV.arguments base sigma (V.erase n ss))
  : Lemma (ensures erase_arguments sigma n ss (insert_argument sigma ss n v vs) == vs)
          (decreases ss) =
  match ss with
  | [] -> ()
  | _ :: rest ->
    if n > 0 then
      match vs with
      | _ :: tail -> lemma_erase_insert_arguments sigma rest (n - 1) v tail
      | [] -> ()

let rec lemma_extended_erasure_at (#base:sort -> Type0) (sigma:DV.signature)
                                  (scope bound:list sort) (vs:DV.arguments base sigma bound)
                                  (rho:DV.environment base sigma scope)
                                  (n:nat{n < L.length bound})
                                  (j:nat{j < L.length (bound @ scope) /\ j <> n})
  : Lemma (ensures (LP.append_length bound scope;
      V.lemma_erase_length n bound; LP.append_length (V.erase n bound) scope;
      (DV.extend sigma scope bound vs rho j <: DV.tree base) ==
      (DV.extend sigma scope (V.erase n bound) (erase_arguments sigma n bound vs) rho
         (lower_index n j) <: DV.tree base)))
          (decreases bound) =
  LP.append_length bound scope;
  lemma_erase_append n bound scope;
  V.lemma_erase_index n j (bound @ scope);
  match bound, vs with
  | _ :: rest, _ :: tail ->
    if n > 0 && j > 0 then
      lemma_extended_erasure_at sigma scope rest tail rho (n - 1) (j - 1)
  | _, _ -> ()

let lemma_lower_bound_evaluate (#base:sort -> Type0) (sigma:DV.signature)
                               (i:DV.interpretation base sigma) (scope bound:list sort)
                               (vs:DV.arguments base sigma bound)
                               (rho:DV.environment base sigma scope)
                               (n:nat{n < L.length bound}) (body result:expr)
  : Lemma (requires D.scoped (bound @ scope) body /\ V.lower n body == Some result)
          (ensures D.scoped (V.erase n bound @ scope) result /\
                   get_sort result == get_sort body /\
                   DV.evaluate sigma i (bound @ scope) (DV.extend sigma scope bound vs rho) body ==
                   DV.evaluate sigma i (V.erase n bound @ scope)
                     (DV.extend sigma scope (V.erase n bound) (erase_arguments sigma n bound vs) rho) result) =
  LP.append_length bound scope;
  lemma_erase_append n bound scope;
  lemma_lower_erased_scopes n (bound @ scope);
  let environments (j:nat{j < L.length (bound @ scope)})
    : Lemma
        (match lower_substitution n j (L.index (bound @ scope) j) with
         | Some e ->
           D.scoped (V.erase n bound @ scope) e /\
           get_sort e == L.index (bound @ scope) j /\
           DV.extend sigma scope bound vs rho j ==
             DV.evaluate sigma i (V.erase n bound @ scope)
               (DV.extend sigma scope (V.erase n bound) (erase_arguments sigma n bound vs) rho) e
         | None -> True) =
    if j <> n then lemma_extended_erasure_at sigma scope bound vs rho n j in
  FStar.Classical.forall_intro environments;
  lemma_lower_evaluate sigma i n (bound @ scope) (V.erase n bound @ scope)
    (DV.extend sigma scope bound vs rho)
    (DV.extend sigma scope (V.erase n bound) (erase_arguments sigma n bound vs) rho)
    body result
