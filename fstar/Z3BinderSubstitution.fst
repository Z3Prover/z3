module Z3BinderSubstitution

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open FStar.List.Tot
module D = Z3Definitions
module P = Z3QuantifierPull
module N = Z3QuantifierNnf
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

type substitution = nat -> sort -> option expr

let under (count:nat) (theta:substitution) : substitution =
  fun n s ->
    if n < count then Some (Var n s)
    else match theta (n - count) s with
         | Some e -> Some (D.lift count 0 e)
         | None -> None

let rec apply (theta:substitution) (e:expr) : Tot (option expr) (decreases e) =
  match e with
  | Var n s ->
    (match theta n s with Some e' -> if get_sort e' = s then Some e' else None | None -> None)
  | App f args ->
    (match apply_args theta args with Some args' -> Some (App f args') | None -> None)
  | Quantifier k bs s body ->
    (match apply (under (L.length bs) theta) body with
     | Some body' -> Some (Quantifier k bs s body') | None -> None)

and apply_args (theta:substitution) (args:list expr)
  : Tot (option (list expr)) (decreases args) =
  match args with
  | [] -> Some []
  | e :: rest ->
    (match apply theta e, apply_args theta rest with
     | Some e', Some rest' -> Some (e' :: rest') | _, _ -> None)

let environments (i:interpretation value) (theta:substitution) (rho sigma:env value) : prop =
  forall (n:nat) (s:sort) (e:expr). theta n s == Some e ==> rho n == eval i e sigma

let lemma_under (i:interpretation value) (theta:substitution)
                (rho sigma:env value) (vs:list value)
  : Lemma (requires quant_extensional i /\ environments i theta rho sigma)
          (ensures environments i (under (L.length vs) theta) (shift vs rho) (shift vs sigma))
  = let indices (n:nat) (s:sort) (e:expr)
      : Lemma (under (L.length vs) theta n s == Some e ==>
               shift vs rho n == eval i e (shift vs sigma))
      = if n < L.length vs then ()
        else match theta (n - L.length vs) s with
        | Some t -> P.lemma_lift_under i t sigma vs
        | None -> () in
    FStar.Classical.forall_intro_3 indices

let rec lemma_apply (i:interpretation value) (theta:substitution)
                    (rho sigma:env value) (e result:expr)
  : Lemma (requires quant_extensional i /\ environments i theta rho sigma /\
                    apply theta e == Some result)
          (ensures eval i e rho == eval i result sigma /\ get_sort e == get_sort result)
          (decreases %[e])
  = match e with
    | Var _ _ -> ()
    | App _ args ->
      lemma_apply_args i theta rho sigma args (Some?.v (apply_args theta args))
    | Quantifier _ bs _ body ->
      (match apply (under (L.length bs) theta) body with
       | Some body' ->
         let bodies (vs:list value{L.length vs = L.length bs})
           : Lemma (eval i body (shift vs rho) == eval i body' (shift vs sigma))
           = lemma_under i theta rho sigma vs;
             lemma_apply i (under (L.length bs) theta) (shift vs rho) (shift vs sigma) body body' in
         FStar.Classical.forall_intro bodies
       | None -> ())

and lemma_apply_args (i:interpretation value) (theta:substitution)
                     (rho sigma:env value) (args results:list expr)
  : Lemma (requires quant_extensional i /\ environments i theta rho sigma /\
                    apply_args theta args == Some results)
          (ensures eval_args i args rho == eval_args i results sigma)
          (decreases %[args])
  = match args, results with
    | [], [] -> ()
    | e :: rest, r :: remaining ->
      lemma_apply i theta rho sigma e r;
      lemma_apply_args i theta rho sigma rest remaining
    | _, _ -> ()

let arguments (args:list expr) : substitution =
  fun n s ->
    if n < L.length args
    then let e = L.index args n in if get_sort e = s then Some e else None
    else Some (Var (n - L.length args) s)

let substitute (args:list expr) (body:expr) : option expr = apply (arguments args) body

let rec lemma_eval_length (i:interpretation value) (args:list expr) (rho:env value)
  : Lemma (L.length (eval_args i args rho) == L.length args) (decreases args)
  = match args with [] -> () | _ :: rest -> lemma_eval_length i rest rho

let rec lemma_eval_index (i:interpretation value) (args:list expr) (rho:env value)
                        (n:nat{n < L.length args})
  : Lemma (requires n < L.length (eval_args i args rho))
          (ensures L.index (eval_args i args rho) n == eval i (L.index args n) rho)
          (decreases args)
  = match args with
    | [] -> ()
    | _ :: rest -> if n = 0 then () else lemma_eval_index i rest rho (n - 1)

let lemma_substitute (i:interpretation value) (rho:env value) (args:list expr) (body result:expr)
  : Lemma (requires quant_extensional i /\ substitute args body == Some result)
          (ensures eval i body (shift (eval_args i args rho) rho) == eval i result rho)
  = lemma_eval_length i args rho;
    let indices (n:nat) (s:sort) (e:expr)
      : Lemma (arguments args n s == Some e ==>
               shift (eval_args i args rho) rho n == eval i e rho)
      = if n < L.length args then lemma_eval_index i args rho n else () in
    FStar.Classical.forall_intro_3 indices;
    lemma_apply i (arguments args) (shift (eval_args i args rho) rho) rho body result

let rec occurs (n depth:nat) (e:expr) : Tot bool (decreases e) =
  match e with
  | Var j _ -> j = n + depth
  | App _ args -> occurs_args n depth args
  | Quantifier _ bs _ body -> occurs n (depth + L.length bs) body

and occurs_args (n depth:nat) (args:list expr) : Tot bool (decreases args) =
  match args with [] -> false | e :: rest -> occurs n depth e || occurs_args n depth rest

let rec used (body:expr) (start count:nat)
  : Tot (list bool) (decreases count) =
  if count = 0 then [] else occurs start 0 body :: used body (start + 1) (count - 1)

let rec count_kept (keep:list bool) : Tot nat (decreases keep) =
  match keep with [] -> 0 | k :: rest -> (if k then 1 else 0) + count_kept rest

let rec thin (keep:list bool) (n:nat) (s:sort) : Tot (option expr) (decreases keep) =
  match keep with
  | [] -> Some (Var n s)
  | k :: rest ->
    if n = 0 then (if k then Some (Var 0 s) else None)
    else match thin rest (n - 1) s with
         | Some (Var j _) -> Some (Var (if k then j + 1 else j) s)
         | _ -> None

let rec filter_values (keep:list bool) (vs:list value)
  : Tot (list value) (decreases keep) =
  match keep, vs with
  | k :: rest, v :: remaining ->
    let tail = filter_values rest remaining in if k then v :: tail else tail
  | _, _ -> []

let rec filter_sorts (keep:list bool) (sorts:list sort)
  : Tot (list sort) (decreases keep) =
  match keep, sorts with
  | k :: rest, s :: remaining ->
    let tail = filter_sorts rest remaining in if k then s :: tail else tail
  | _, _ -> []

let rec inflate (keep:list bool) (vs:list value)
  : Tot (list value) (decreases keep) =
  match keep with
  | [] -> []
  | false :: rest -> VBool false :: inflate rest vs
  | true :: rest ->
    (match vs with [] -> [] | v :: remaining -> v :: inflate rest remaining)

let rec lemma_filter_length (keep:list bool) (vs:list value)
  : Lemma (requires L.length keep = L.length vs)
          (ensures L.length (filter_values keep vs) == count_kept keep)
          (decreases keep)
  = match keep, vs with
    | _ :: rest, _ :: remaining -> lemma_filter_length rest remaining
    | _, _ -> ()

let rec lemma_filter_sorts (keep:list bool) (sorts:list sort)
  : Lemma (requires L.length keep = L.length sorts)
          (ensures L.length (filter_sorts keep sorts) == count_kept keep)
          (decreases keep)
  = match keep, sorts with
    | _ :: rest, _ :: remaining -> lemma_filter_sorts rest remaining
    | _, _ -> ()

let rec lemma_inflate (keep:list bool) (vs:list value)
  : Lemma (requires L.length vs == count_kept keep)
          (ensures L.length (inflate keep vs) == L.length keep /\
                   filter_values keep (inflate keep vs) == vs)
          (decreases keep)
  = match keep with
    | [] -> ()
    | false :: rest -> lemma_inflate rest vs
    | true :: rest ->
      (match vs with [] -> () | _ :: remaining -> lemma_inflate rest remaining)

let rec lemma_thin_at (keep:list bool) (vs:list value) (rho:env value) (n:nat) (s:sort)
  : Lemma (requires L.length vs == L.length keep)
          (ensures (match thin keep n s with
                    | Some (Var j _) -> shift vs rho n == shift (filter_values keep vs) rho j
                    | Some _ -> False
                    | None -> True))
          (decreases keep)
  = match keep, vs with
    | [], [] -> ()
    | k :: rest, _ :: remaining ->
      if n = 0 then ()
      else lemma_thin_at rest remaining rho (n - 1) s
    | _, _ -> ()

let lemma_thin (i:interpretation value) (keep:list bool) (vs:list value)
               (rho:env value) (body result:expr)
  : Lemma (requires quant_extensional i /\ L.length vs == L.length keep /\
                    apply (thin keep) body == Some result)
          (ensures eval i body (shift vs rho) ==
                   eval i result (shift (filter_values keep vs) rho))
  = let indices (n:nat) (s:sort) (e:expr)
      : Lemma (thin keep n s == Some e ==>
               shift vs rho n == eval i e (shift (filter_values keep vs) rho))
      = lemma_thin_at keep vs rho n s in
    FStar.Classical.forall_intro_3 indices;
    lemma_apply i (thin keep) (shift vs rho) (shift (filter_values keep vs) rho) body result

let lemma_all_thin (i:interpretation value) (keep:list bool) (body result:expr)
                   (negative:bool) (rho:env value)
  : Lemma (requires quant_extensional i /\ apply (thin keep) body == Some result)
          (ensures P.all_bodies i body negative (L.length keep) rho <==>
                   P.all_bodies i result negative (count_kept keep) rho)
  = let forward (_:squash (P.all_bodies i body negative (L.length keep) rho))
      : Lemma (P.all_bodies i result negative (count_kept keep) rho)
      = let bodies (vs:list value{L.length vs = count_kept keep})
          : Lemma (P.body_truth i result negative (shift vs rho))
          = lemma_inflate keep vs;
            assert (P.body_truth i body negative (shift (inflate keep vs) rho));
            lemma_thin i keep (inflate keep vs) rho body result in
        FStar.Classical.forall_intro bodies in
    FStar.Classical.impl_intro forward;
    let backward (_:squash (P.all_bodies i result negative (count_kept keep) rho))
      : Lemma (P.all_bodies i body negative (L.length keep) rho)
      = let bodies (vs:list value{L.length vs = L.length keep})
          : Lemma (P.body_truth i body negative (shift vs rho))
          = lemma_filter_length keep vs;
            assert (P.body_truth i result negative (shift (filter_values keep vs) rho));
            lemma_thin i keep vs rho body result in
        FStar.Classical.forall_intro bodies in
    FStar.Classical.impl_intro backward

let quantify (kind:quantifier_kind) (sorts:list sort) (body:expr) : expr =
  if sorts = [] then body else Quantifier kind sorts bool_sort body

let lemma_quantify (i:interpretation value) (rho:env value)
                   (kind:quantifier_kind) (sorts:list sort) (body:expr)
  : Lemma (requires quant_extensional i /\ N.quantifier_model i /\ boolean_model i /\
                    get_sort body = bool_sort /\ (kind = Forall_k \/ kind = Exists_k))
          (ensures eval i (quantify kind sorts body) rho ==
                   eval i (Quantifier kind sorts bool_sort body) rho)
  = if sorts = [] then (
      N.lemma_quantifier_truth i rho kind sorts body;
      let indices (n:nat) : Lemma (shift [] rho n == rho n) = () in
      FStar.Classical.forall_intro indices;
      P.lemma_eval_environments i body (shift [] rho) rho;
      assert (forall (vs:list value{L.length vs = 0}). vs == []);
      match eval i body rho, eval i (Quantifier kind sorts bool_sort body) rho with
      | VBool _, VBool _ -> ()
      | _, _ -> ())

let rec lemma_used_length (body:expr) (start count:nat)
  : Lemma (L.length (used body start count) == count) (decreases count)
  = if count = 0 then () else lemma_used_length body (start + 1) (count - 1)

let elim_unused (e:expr) : option expr =
  match e with
  | Quantifier k bs s body ->
    if (k = Forall_k || k = Exists_k) && s = bool_sort && get_sort body = bool_sort then
      let keep = used body 0 (L.length bs) in
      (match apply (thin keep) body with
       | Some b -> Some (quantify k (L.rev (filter_sorts keep (L.rev bs))) b)
       | None -> None)
    else Some e
  | _ -> Some e

let lemma_eliminate (i:interpretation value) (rho:env value) (e result:expr)
  : Lemma (requires quant_extensional i /\ N.quantifier_model i /\ boolean_model i /\
                    elim_unused e == Some result)
          (ensures eval i e rho == eval i result rho /\ get_sort e == get_sort result)
  = match e with
    | Quantifier k bs s body ->
      if (k = Forall_k || k = Exists_k) && s = bool_sort && get_sort body = bool_sort then (
        let keep = used body 0 (L.length bs) in
        lemma_used_length body 0 (L.length bs);
        LP.rev_length bs;
        lemma_filter_sorts keep (L.rev bs);
        LP.rev_length (filter_sorts keep (L.rev bs));
        match apply (thin keep) body with
        | None -> ()
        | Some b ->
          let sample = P.sample_values (L.length bs) in
          let indices (n:nat) (t:sort) (v:expr)
            : Lemma (thin keep n t == Some v ==>
                     shift sample rho n == eval i v (shift (filter_values keep sample) rho))
            = lemma_thin_at keep sample rho n t in
          FStar.Classical.forall_intro_3 indices;
          lemma_apply i (thin keep) (shift sample rho)
            (shift (filter_values keep sample) rho) body b;
          let sorts = L.rev (filter_sorts keep (L.rev bs)) in
          N.lemma_quantifier_truth i rho k bs body;
          N.lemma_quantifier_truth i rho k sorts b;
          lemma_all_thin i keep body b (k = Exists_k) rho;
          lemma_quantify i rho k sorts b;
          match eval i e rho, eval i result rho with
          | VBool _, VBool _ -> ()
          | _, _ -> ())
    | _ -> ()

let eliminate_check (a b:expr) : bool =
  match elim_unused a, elim_unused b with Some x, Some y -> x = y | _, _ -> false

let lemma_eliminate_check (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires quant_extensional i /\ N.quantifier_model i /\ boolean_model i /\
                    eliminate_check a b)
          (ensures eval i a rho == eval i b rho)
  = match elim_unused a, elim_unused b with
    | Some x, Some y -> lemma_eliminate i rho a x; lemma_eliminate i rho b y
    | _, _ -> ()

let rec lemma_avoids (i:interpretation value) (e:expr) (variable depth:nat)
                    (rho sigma:env value)
  : Lemma (requires quant_extensional i /\ not (occurs variable depth e) /\
                    (forall (n:nat). n <> variable + depth ==> rho n == sigma n))
          (ensures eval i e rho == eval i e sigma)
          (decreases %[e])
  = match e with
    | Var _ _ -> ()
    | App _ args -> lemma_avoids_args i args variable depth rho sigma
    | Quantifier _ bs _ body ->
      let bodies (vs:list value{L.length vs = L.length bs})
        : Lemma (eval i body (shift vs rho) == eval i body (shift vs sigma))
        = let indices (n:nat)
            : Lemma (n <> variable + depth + L.length bs ==>
                     shift vs rho n == shift vs sigma n) = () in
          FStar.Classical.forall_intro indices;
          lemma_avoids i body variable (depth + L.length bs) (shift vs rho) (shift vs sigma) in
      FStar.Classical.forall_intro bodies

and lemma_avoids_args (i:interpretation value) (args:list expr) (variable depth:nat)
                     (rho sigma:env value)
  : Lemma (requires quant_extensional i /\ not (occurs_args variable depth args) /\
                    (forall (n:nat). n <> variable + depth ==> rho n == sigma n))
          (ensures eval_args i args rho == eval_args i args sigma)
          (decreases %[args])
  = match args with
    | [] -> ()
    | e :: rest ->
      lemma_avoids i e variable depth rho sigma;
      lemma_avoids_args i rest variable depth rho sigma

let rec update (vs:list value) (n:nat) (v:value) : Tot (list value) (decreases vs) =
  match vs with
  | [] -> []
  | head :: rest -> if n = 0 then v :: rest else head :: update rest (n - 1) v

let rec lemma_update_length (vs:list value) (n:nat) (v:value)
  : Lemma (L.length (update vs n v) == L.length vs) (decreases vs)
  = match vs with [] -> () | _ :: rest -> if n = 0 then () else lemma_update_length rest (n - 1) v

let rec lemma_update_at (vs:list value) (variable:nat) (v:value) (rho:env value) (n:nat)
  : Lemma (requires variable < L.length vs)
          (ensures shift (update vs variable v) rho n ==
                   (if n = variable then v else shift vs rho n))
          (decreases vs)
  = lemma_update_length vs variable v;
    match vs with
    | [] -> ()
    | _ :: rest ->
      if variable = 0 then ()
      else if n = 0 then ()
      else lemma_update_at rest (variable - 1) v rho (n - 1)

let replace_one (variable:nat) (term:expr) : substitution =
  fun n s -> if n = variable then Some term else Some (Var n s)

let lemma_replace_one (i:interpretation value) (rho:env value)
                      (vs:list value) (variable:nat) (term body result:expr)
  : Lemma (requires quant_extensional i /\ variable < L.length vs /\
                    apply (replace_one variable term) body == Some result)
          (ensures eval i body
                     (shift (update vs variable (eval i term (shift vs rho))) rho) ==
                   eval i result (shift vs rho))
  = let indices (n:nat) (s:sort) (e:expr)
      : Lemma (replace_one variable term n s == Some e ==>
               shift (update vs variable (eval i term (shift vs rho))) rho n ==
               eval i e (shift vs rho))
      = lemma_update_at vs variable (eval i term (shift vs rho)) rho n in
    FStar.Classical.forall_intro_3 indices;
    lemma_apply i (replace_one variable term)
      (shift (update vs variable (eval i term (shift vs rho))) rho) (shift vs rho) body result

let lemma_replace_equal (i:interpretation value) (rho:env value)
                        (variable:nat) (term body result:expr)
  : Lemma (requires quant_extensional i /\ rho variable == eval i term rho /\
                    apply (replace_one variable term) body == Some result)
          (ensures eval i body rho == eval i result rho)
  = let indices (n:nat) (s:sort) (e:expr)
      : Lemma (replace_one variable term n s == Some e ==> rho n == eval i e rho) = () in
    FStar.Classical.forall_intro_3 indices;
    lemma_apply i (replace_one variable term) rho rho body result
