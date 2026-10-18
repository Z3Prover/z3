module Z3QuantifierPull

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open FStar.List.Tot
module D = Z3Definitions
module QN = Z3QuantifierNnf
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

let rec lemma_eval_environments (i:interpretation value) (e:expr) (rho sigma:env value)
  : Lemma (requires quant_extensional i /\ (forall (n:nat). rho n == sigma n))
          (ensures eval i e rho == eval i e sigma)
          (decreases %[e])
  = match e with
    | Var _ _ -> ()
    | App _ args -> lemma_eval_args_environments i args rho sigma
    | Quantifier _ bs _ body ->
      let bodies (vs:list value{L.length vs = L.length bs})
        : Lemma (eval i body (shift vs rho) == eval i body (shift vs sigma))
        = let indices (n:nat)
            : Lemma (shift vs rho n == shift vs sigma n) = () in
          FStar.Classical.forall_intro indices;
          lemma_eval_environments i body (shift vs rho) (shift vs sigma) in
      FStar.Classical.forall_intro bodies

and lemma_eval_args_environments (i:interpretation value) (args:list expr) (rho sigma:env value)
  : Lemma (requires quant_extensional i /\ (forall (n:nat). rho n == sigma n))
          (ensures eval_args i args rho == eval_args i args sigma)
          (decreases %[args])
  = match args with
    | [] -> ()
    | e :: rest ->
      lemma_eval_environments i e rho sigma;
      lemma_eval_args_environments i rest rho sigma

let rec lemma_shift_append (xs ys:list value) (rho:env value) (n:nat)
  : Lemma (shift (xs @ ys) rho n == shift xs (shift ys rho) n)
          (decreases xs)
  = LP.append_length xs ys;
    match xs with
    | [] -> ()
    | _ :: rest -> if n = 0 then () else lemma_shift_append rest ys rho (n - 1)

let lemma_eval_shift_append (i:interpretation value) (e:expr)
                            (xs ys:list value) (rho:env value)
  : Lemma (requires quant_extensional i)
          (ensures eval i e (shift (xs @ ys) rho) ==
                   eval i e (shift xs (shift ys rho)))
  = let indices (n:nat)
      : Lemma (shift (xs @ ys) rho n == shift xs (shift ys rho) n)
      = lemma_shift_append xs ys rho n in
    FStar.Classical.forall_intro indices;
    lemma_eval_environments i e (shift (xs @ ys) rho) (shift xs (shift ys rho))

let rec lemma_split_values (n:nat) (vs:list value)
  : Lemma (requires n <= L.length vs)
          (ensures (let xs, ys = L.splitAt n vs in
                    L.length xs == n /\ L.length ys == L.length vs - n /\ xs @ ys == vs))
          (decreases n)
  = if n = 0 then ()
    else match vs with
    | [] -> ()
    | _ :: rest -> lemma_split_values (n - 1) rest

let body_truth (i:interpretation value) (body:expr) (negative:bool) (rho:env value) : prop =
  if negative then ~(lit_true i rho body) else lit_true i rho body

let all_bodies (i:interpretation value) (body:expr) (negative:bool)
               (n:nat) (rho:env value) : prop =
  forall (vs:list value{L.length vs = n}). body_truth i body negative (shift vs rho)

let nested_bodies (i:interpretation value) (body:expr) (negative:bool)
                  (outer inner:nat) (rho:env value) : prop =
  forall (vs:list value{L.length vs = outer}).
    all_bodies i body negative inner (shift vs rho)

let lemma_combine_bodies (i:interpretation value) (body:expr) (negative:bool)
                         (outer inner:nat) (rho:env value)
  : Lemma (requires quant_extensional i)
          (ensures nested_bodies i body negative outer inner rho <==>
                   all_bodies i body negative (outer + inner) rho)
  = let forward (_:squash (nested_bodies i body negative outer inner rho))
      : Lemma (all_bodies i body negative (outer + inner) rho)
      = let combined (vs:list value{L.length vs = outer + inner})
          : Lemma (body_truth i body negative (shift vs rho))
          = lemma_split_values inner vs;
            let xs, ys = L.splitAt inner vs in
            assert (all_bodies i body negative inner (shift ys rho));
            assert (body_truth i body negative (shift xs (shift ys rho)));
            lemma_eval_shift_append i body xs ys rho in
        FStar.Classical.forall_intro combined in
    FStar.Classical.impl_intro forward;
    let backward (_:squash (all_bodies i body negative (outer + inner) rho))
      : Lemma (nested_bodies i body negative outer inner rho)
      = let outside (ys:list value{L.length ys = outer})
          : Lemma (all_bodies i body negative inner (shift ys rho))
          = let inside (xs:list value{L.length xs = inner})
              : Lemma (body_truth i body negative (shift xs (shift ys rho)))
              = LP.append_length xs ys;
                assert (body_truth i body negative (shift (xs @ ys) rho));
                lemma_eval_shift_append i body xs ys rho in
            FStar.Classical.forall_intro inside in
        FStar.Classical.forall_intro outside in
    FStar.Classical.impl_intro backward

let lemma_flatten (i:interpretation value) (rho:env value)
                  (kind:quantifier_kind) (outer inner:list sort) (body:expr)
  : Lemma (requires quant_extensional i /\ QN.quantifier_model i /\ boolean_model i /\
                    get_sort body == bool_sort /\ (kind = Forall_k \/ kind = Exists_k))
          (ensures eval i (Quantifier kind outer bool_sort
                             (Quantifier kind inner bool_sort body)) rho ==
                   eval i (Quantifier kind (outer @ inner) bool_sort body) rho)
  = LP.append_length outer inner;
    QN.lemma_quantifier_truth i rho kind outer (Quantifier kind inner bool_sort body);
    QN.lemma_quantifier_truth i rho kind (outer @ inner) body;
    let bodies (vs:list value{L.length vs = L.length outer})
      : Lemma ((if kind = Forall_k then
                  lit_true i (shift vs rho) (Quantifier kind inner bool_sort body)
                else ~(lit_true i (shift vs rho) (Quantifier kind inner bool_sort body)))
               <==> all_bodies i body (kind = Exists_k) (L.length inner) (shift vs rho))
      = QN.lemma_quantifier_truth i (shift vs rho) kind inner body in
    FStar.Classical.forall_intro bodies;
    lemma_combine_bodies i body (kind = Exists_k) (L.length outer) (L.length inner) rho;
    match eval i (Quantifier kind outer bool_sort (Quantifier kind inner bool_sort body)) rho,
          eval i (Quantifier kind (outer @ inner) bool_sort body) rho with
    | VBool _, VBool _ -> ()
    | _, _ -> ()

let lift_environments (amount cutoff:nat) (rho sigma:env value) : prop =
  forall (n:nat). sigma (if n < cutoff then n else n + amount) == rho n

let rec lemma_lift (i:interpretation value) (e:expr) (amount cutoff:nat)
                   (rho sigma:env value)
  : Lemma (requires quant_extensional i /\ lift_environments amount cutoff rho sigma)
          (ensures eval i (D.lift amount cutoff e) sigma == eval i e rho)
          (decreases %[e])
  = match e with
    | Var _ _ -> ()
    | App _ args -> lemma_lift_args i args amount cutoff rho sigma
    | Quantifier _ bs _ body ->
      let bodies (vs:list value{L.length vs = L.length bs})
        : Lemma (eval i (D.lift amount (cutoff + L.length bs) body) (shift vs sigma) ==
                 eval i body (shift vs rho))
        = let indices (n:nat)
            : Lemma (shift vs sigma (if n < cutoff + L.length bs then n else n + amount) ==
                     shift vs rho n)
            = if n < L.length vs then ()
              else assert (sigma (if n - L.length vs < cutoff
                                  then n - L.length vs else n - L.length vs + amount) ==
                           rho (n - L.length vs)) in
          FStar.Classical.forall_intro indices;
          lemma_lift i body amount (cutoff + L.length bs) (shift vs rho) (shift vs sigma) in
      FStar.Classical.forall_intro bodies

and lemma_lift_args (i:interpretation value) (args:list expr) (amount cutoff:nat)
                    (rho sigma:env value)
  : Lemma (requires quant_extensional i /\ lift_environments amount cutoff rho sigma)
          (ensures eval_args i (D.lift_args amount cutoff args) sigma == eval_args i args rho)
          (decreases %[args])
  = match args with
    | [] -> ()
    | e :: rest ->
      lemma_lift i e amount cutoff rho sigma;
      lemma_lift_args i rest amount cutoff rho sigma

let lemma_lift_under (i:interpretation value) (e:expr) (rho:env value) (vs:list value)
  : Lemma (requires quant_extensional i)
          (ensures eval i (D.lift (L.length vs) 0 e) (shift vs rho) == eval i e rho)
  = let indices (n:nat)
      : Lemma (shift vs rho (n + L.length vs) == rho n) = () in
    FStar.Classical.forall_intro indices;
    lemma_lift i e (L.length vs) 0 rho (shift vs rho)

let rec lemma_lift_context (i:interpretation value) (args:list expr)
                           (rho:env value) (vs:list value)
  : Lemma (requires quant_extensional i)
          (ensures
            (conj_holds i (shift vs rho) (D.lift_args (L.length vs) 0 args) <==>
             conj_holds i rho args) /\
            (clause_holds i (shift vs rho) (D.lift_args (L.length vs) 0 args) <==>
             clause_holds i rho args))
          (decreases args)
  = match args with
    | [] -> ()
    | e :: rest ->
      lemma_lift_under i e rho vs;
      lemma_lift_context i rest rho vs

let rec boolean_args (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | e :: rest -> get_sort e = bool_sort && boolean_args rest

let context_truth (i:interpretation value) (rho:env value) (f:func_decl)
                  (prefix suffix:list expr) (p:prop) : prop =
  if f.decl_name = "and"
  then conj_holds i rho prefix /\ p /\ conj_holds i rho suffix
  else clause_holds i rho prefix \/ p \/ clause_holds i rho suffix

let rec lemma_context (i:interpretation value) (rho:env value) (f:func_decl)
                      (prefix suffix:list expr) (body:expr)
  : Lemma (requires and_sound i /\ or_sound i /\
                    (f.decl_name = "and" \/ f.decl_name = "or"))
          (ensures lit_true i rho (App f (prefix @ (body :: suffix))) <==>
                   context_truth i rho f prefix suffix (lit_true i rho body))
          (decreases prefix)
  = match prefix with
    | [] -> ()
    | _ :: rest -> lemma_context i rho f rest suffix body

let rec sample_values (n:nat) : GTot (vs:list value{L.length vs = n}) (decreases n) =
  if n = 0 then [] else VBool false :: sample_values (n - 1)

let lemma_pull_context (i:interpretation value) (rho:env value)
                       (f:func_decl) (prefix suffix:list expr)
                       (kind:quantifier_kind) (sorts:list sort) (body:expr)
  : Lemma (requires quant_extensional i /\ QN.quantifier_model i /\ boolean_model i /\
                    and_sound i /\ or_sound i /\ f.range = bool_sort /\
                    (f.decl_name = "and" \/ f.decl_name = "or") /\
                    (kind = Forall_k \/ kind = Exists_k) /\ get_sort body = bool_sort)
          (ensures
            eval i (App f (prefix @ (Quantifier kind sorts bool_sort body :: suffix))) rho ==
            eval i (Quantifier kind sorts bool_sort
                      (App f (D.lift_args (L.length sorts) 0 prefix @
                              (body :: D.lift_args (L.length sorts) 0 suffix)))) rho)
  = let lifted = App f (D.lift_args (L.length sorts) 0 prefix @
                         (body :: D.lift_args (L.length sorts) 0 suffix)) in
    QN.lemma_quantifier_truth i rho kind sorts body;
    QN.lemma_quantifier_truth i rho kind sorts lifted;
    lemma_context i rho f prefix suffix (Quantifier kind sorts bool_sort body);
    let bodies (vs:list value{L.length vs = L.length sorts})
      : Lemma (lit_true i (shift vs rho) lifted <==>
               context_truth i rho f prefix suffix (lit_true i (shift vs rho) body))
      = lemma_lift_context i prefix rho vs;
        lemma_lift_context i suffix rho vs;
        lemma_context i (shift vs rho) f
          (D.lift_args (L.length sorts) 0 prefix)
          (D.lift_args (L.length sorts) 0 suffix) body in
    FStar.Classical.forall_intro bodies;
    let sample = sample_values (L.length sorts) in
    bodies sample;
    match eval i (App f (prefix @ (Quantifier kind sorts bool_sort body :: suffix))) rho,
          eval i (Quantifier kind sorts bool_sort lifted) rho with
    | VBool _, VBool _ -> ()
    | _, _ -> ()

let merge (kind:quantifier_kind) (sorts:list sort) (body:expr) : expr =
  match body with
  | Quantifier k bs s b ->
    if k = kind && s = bool_sort && get_sort b = bool_sort
    then Quantifier kind (sorts @ bs) bool_sort b
    else Quantifier kind sorts bool_sort body
  | _ -> Quantifier kind sorts bool_sort body

let lemma_merge (i:interpretation value) (rho:env value)
                (kind:quantifier_kind) (sorts:list sort) (body:expr)
  : Lemma (requires quant_extensional i /\ QN.quantifier_model i /\ boolean_model i /\
                    (kind = Forall_k \/ kind = Exists_k))
          (ensures eval i (merge kind sorts body) rho ==
                   eval i (Quantifier kind sorts bool_sort body) rho /\
                   get_sort (merge kind sorts body) == bool_sort)
  = match body with
    | Quantifier k bs s b ->
      if k = kind && s = bool_sort && get_sort b = bool_sort
      then lemma_flatten i rho kind sorts bs b
    | _ -> ()

(* Pull the rightmost child first: Z3 orders the resulting binder blocks
   right-to-left, while preserving declaration order inside each block. *)
let rec split_quantifier (args:list expr)
  : Tot (option (list expr & quantifier_kind & list sort & expr & list expr)) (decreases args) =
  match args with
  | [] -> None
  | e :: rest ->
    (match split_quantifier rest with
     | Some (prefix, kind, sorts, body, suffix) ->
       Some (e :: prefix, kind, sorts, body, suffix)
     | None ->
       (match e with
        | Quantifier k bs s body ->
          if (k = Forall_k || k = Exists_k) && s = bool_sort && get_sort body = bool_sort
          then Some ([], k, bs, body, rest) else None
        | _ -> None))

let rec lemma_split_quantifier (args:list expr)
  : Lemma (ensures (match split_quantifier args with
                   | None -> True
                   | Some (prefix, kind, sorts, body, suffix) ->
                     args == prefix @ (Quantifier kind sorts bool_sort body :: suffix) /\
                     (kind = Forall_k \/ kind = Exists_k) /\ get_sort body == bool_sort))
          (decreases args)
  = match args with
    | [] -> ()
    | _ :: rest -> lemma_split_quantifier rest

let rec normalize (fuel:nat) (e:expr) : Tot (option expr) (decreases fuel) =
  if fuel = 0 then None
  else match e with
  | Quantifier k bs s body ->
    if (k = Forall_k || k = Exists_k) && s = bool_sort && get_sort body = bool_sort
    then (match normalize (fuel - 1) body with
          | Some b -> Some (merge k bs b)
          | None -> None)
    else Some e
  | App f args ->
    if (f.decl_name = "and" || f.decl_name = "or") &&
       f.range = bool_sort && boolean_args args then
      (match split_quantifier args with
       | None -> Some e
       | Some (prefix, k, bs, body, suffix) ->
         let inside = App f (D.lift_args (L.length bs) 0 prefix @
                              (body :: D.lift_args (L.length bs) 0 suffix)) in
         (match normalize (fuel - 1) inside with
          | Some b -> Some (merge k bs b)
          | None -> None))
    else if f = not_decl then
      (match args with
       | [Quantifier k bs s body] ->
         if (k = Forall_k || k = Exists_k) && s = bool_sort && get_sort body = bool_sort
         then Some (Quantifier (QN.dual k) bs bool_sort (mk_not_expr body))
         else Some e
       | _ -> Some e)
    else Some e
  | _ -> Some e

let rec lemma_normalize_sound (fuel:nat) (i:interpretation value) (rho:env value) (e result:expr)
  : Lemma (requires quant_extensional i /\ QN.quantifier_model i /\ boolean_model i /\
                    and_sound i /\ or_sound i /\ not_sound i /\ normalize fuel e = Some result)
          (ensures eval i e rho == eval i result rho /\ get_sort e == get_sort result)
          (decreases fuel)
  = if fuel = 0 then ()
    else match e with
    | Quantifier k bs s body ->
      if (k = Forall_k || k = Exists_k) && s = bool_sort && get_sort body = bool_sort
      then (match normalize (fuel - 1) body with
            | Some b ->
              let bodies (vs:list value{L.length vs = L.length bs})
                : Lemma (eval i body (shift vs rho) == eval i b (shift vs rho))
                = lemma_normalize_sound (fuel - 1) i (shift vs rho) body b in
              FStar.Classical.forall_intro bodies;
              lemma_merge i rho k bs b
            | None -> ())
    | App f args ->
      if (f.decl_name = "and" || f.decl_name = "or") &&
         f.range = bool_sort && boolean_args args then
        (match split_quantifier args with
         | None -> ()
         | Some (prefix, k, bs, body, suffix) ->
           lemma_split_quantifier args;
           let inside = App f (D.lift_args (L.length bs) 0 prefix @
                                (body :: D.lift_args (L.length bs) 0 suffix)) in
           lemma_pull_context i rho f prefix suffix k bs body;
           (match normalize (fuel - 1) inside with
            | Some b ->
              let bodies (vs:list value{L.length vs = L.length bs})
                : Lemma (eval i inside (shift vs rho) == eval i b (shift vs rho))
                = lemma_normalize_sound (fuel - 1) i (shift vs rho) inside b in
              FStar.Classical.forall_intro bodies;
              lemma_merge i rho k bs b
            | None -> ()))
      else if f = not_decl then
        (match args with
         | [Quantifier k bs s body] ->
           if (k = Forall_k || k = Exists_k) && s = bool_sort && get_sort body = bool_sort
           then QN.lemma_duality i rho k bs body
         | _ -> ())
    | _ -> ()

let check (a b:expr) : bool =
  match normalize 64 a, normalize 64 b with
  | Some x, Some y -> x = y
  | _, _ -> false

let lemma_check_sound (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires quant_extensional i /\ QN.quantifier_model i /\ boolean_model i /\
                    and_sound i /\ or_sound i /\ not_sound i /\ check a b)
          (ensures eval i a rho == eval i b rho)
  = match normalize 64 a, normalize 64 b with
    | Some x, Some y ->
      lemma_normalize_sound 64 i rho a x;
      lemma_normalize_sound 64 i rho b y
    | _, _ -> ()
