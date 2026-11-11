(* A separate judgment for the checked ground fragment of observational
   equality. These constructors preserve observations in the same model,
   which is sufficient for equisatisfiability. General equivalence modulo
   naming requires model-extension/freshness witnesses and is not asserted
   by this theory. Boolean observations compare truth; non-Boolean
   observations require same-sort value agreement as a sufficient witness.
   In particular, ~ remains a separate judgment, not an object-language
   equality. *)
module Z3ObservationalEquality

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module OS = Z3ObservationalSemantics
module C = Z3CanonicalOps

let typed_oeq_decl (s:sort) : func_decl =
  { decl_name = "~"; domain = [s; s]; range = bool_sort;
    interp = Some op_oeq; int_params = [] }

let oeq_decl : func_decl = typed_oeq_decl bool_sort

let mk_oeq_expr (a b:expr) : expr = App (typed_oeq_decl (get_sort a)) [a; b]

let is_oeq (e:expr) : option (expr & expr) =
  match e with
  | App f [a; b] ->
    if f = typed_oeq_decl (get_sort a) && get_sort a = get_sort b
    then Some (a, b) else None
  | _ -> None

type oproof =
  | ORefl : a:expr -> oproof
  | OSym : p:oproof -> oproof
  | OTrans : p:oproof -> q:oproof -> oproof
  | OCongr : f:func_decl -> args1:list expr -> args2:list expr -> ps:list oproof -> oproof
  | OIff : a:expr -> b:expr -> oproof
  | OPremise : a:expr -> b:expr -> oproof

let rec observation_matches (a b:expr) (facts:list (option (expr & expr)))
  : Tot bool (decreases facts) =
  match facts with
  | [] -> false
  | Some (s, t) :: rest ->
    (s = a && t = b) || observation_matches a b rest
  | None :: rest -> observation_matches a b rest

let rec observations_matched (xs ys:list expr) (facts:list (option (expr & expr)))
  : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | x :: xs', y :: ys' ->
    (x = y || observation_matches x y facts) && observations_matched xs' ys' facts
  | _, _ -> false

let rec ofact (p:oproof) : Tot (option (expr & expr)) (decreases p) =
  let result =
    match p with
    | ORefl a -> Some (a, a)
    | OIff a b ->
      if get_sort a = bool_sort && get_sort b = bool_sort then Some (a, b) else None
    | OPremise a b -> Some (a, b)
    | OSym q ->
      (match ofact q with Some (a, b) -> Some (b, a) | None -> None)
    | OTrans q r ->
      (match ofact q, ofact r with
       | Some (a, b), Some (c, d) -> if b = c then Some (a, d) else None
       | _, _ -> None)
    | OCongr f xs ys ps ->
      if observations_matched xs ys (ofacts ps)
      then Some (App f xs, App f ys)
      else None
  in
  match result with
  | Some (a, b) ->
    if get_sort a = get_sort b then result else None
  | None -> None

and ofacts (ps:list oproof) : Tot (list (option (expr & expr))) (decreases ps) =
  match ps with
  | [] -> []
  | p :: rest -> ofact p :: ofacts rest

let observations_agree (i:interpretation value) (rho:env value) (a b:expr) : prop =
  get_sort a == get_sort b /\
  (if get_sort a = bool_sort then lit_true i rho a <==> lit_true i rho b
   else eval i a rho == eval i b rho)

let boolean_model (i:interpretation value) : prop =
  forall (a:expr) (rho:env value).
    get_sort a == bool_sort ==> VBool? (eval i a rho)

let denotation (#value:Type) (i:interpretation value) (rho:env value)
  : OS.denotation value (fun _ -> true) =
  fun e -> eval i e rho

let lemma_agreement (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (observations_agree i rho a b <==>
           OS.observations_agree (VBool true) (denotation i rho) a b)
  = ()

let lemma_boolean_values (i:interpretation value) (rho:env value)
  : Lemma (requires boolean_model i)
          (ensures OS.boolean_model (VBool true) (VBool false) (denotation i rho))
  = let aux (e:expr)
      : Lemma (get_sort e == bool_sort ==>
               OS.boolean_value (VBool true) (VBool false) (eval i e rho))
      = if get_sort e = bool_sort then
          match eval i e rho with VBool _ -> () | _ -> () in
    FStar.Classical.forall_intro aux

let rec o_obligations (i:interpretation value) (p:oproof)
  : Tot prop (decreases p) =
  match p with
  | ORefl _ -> True
  | OSym q -> o_obligations i q
  | OTrans q r -> o_obligations i q /\ o_obligations i r
  | OCongr _ _ _ ps -> o_obligations_list i ps
  | OIff a b -> forall (rho:env value). lit_true i rho (mk_iff_expr a b)
  | OPremise a b -> forall (rho:env value). observations_agree i rho a b

and o_obligations_list (i:interpretation value) (ps:list oproof)
  : Tot prop (decreases ps) =
  match ps with
  | [] -> True
  | p :: rest -> o_obligations i p /\ o_obligations_list i rest

let rec osize (p:oproof) : Tot nat (decreases p) =
  match p with
  | ORefl _ | OIff _ _ | OPremise _ _ -> 1
  | OSym q -> 1 + osize q
  | OTrans q r -> 1 + osize q + osize r
  | OCongr _ _ _ ps -> 1 + osizes ps

and osizes (ps:list oproof) : Tot nat (decreases ps) =
  match ps with
  | [] -> 0
  | p :: rest -> 1 + osize p + osizes rest

let lemma_observations_values_typed (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires observations_agree i rho a b /\
                    (get_sort a == bool_sort ==>
                     VBool? (eval i a rho) /\ VBool? (eval i b rho)))
          (ensures eval i a rho == eval i b rho)
  = lemma_agreement i rho a b;
    (if get_sort a = bool_sort then
       match eval i a rho, eval i b rho with VBool _, VBool _ -> () | _, _ -> ());
    OS.lemma_values (VBool true) (VBool false) (denotation i rho) a b

let lemma_observations_values (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires boolean_model i /\ observations_agree i rho a b)
          (ensures eval i a rho == eval i b rho)
  = lemma_observations_values_typed i rho a b

(* Per-environment obligations and contracts have no concrete value
   constructors. The legacy universally quantified API is adapted below. *)
let equality_model (#value:Type) (vtrue:value) (i:interpretation value) (rho:env value) : prop =
  forall (f:func_decl) (a b:expr).
    C.canonical_eq f ==>
    (eval i (App f [a; b]) rho == vtrue <==> eval i a rho == eval i b rho)

let rec o_obligations_at (#value:Type) (vtrue:value) (i:interpretation value)
                         (rho:env value) (p:oproof)
  : Tot prop (decreases p) =
  match p with
  | ORefl _ -> True
  | OSym q -> o_obligations_at vtrue i rho q
  | OTrans q r -> o_obligations_at vtrue i rho q /\ o_obligations_at vtrue i rho r
  | OCongr _ _ _ ps -> o_obligations_list_at vtrue i rho ps
  | OIff a b -> eval i (mk_iff_expr a b) rho == vtrue
  | OPremise a b -> OS.observations_agree vtrue (denotation i rho) a b

and o_obligations_list_at (#value:Type) (vtrue:value) (i:interpretation value)
                          (rho:env value) (ps:list oproof)
  : Tot prop (decreases ps) =
  match ps with
  | [] -> True
  | p :: rest -> o_obligations_at vtrue i rho p /\ o_obligations_list_at vtrue i rho rest

let rec lemma_oproof_sound_at (#value:Type) (vtrue vfalse:value)
                              (i:interpretation value) (p:oproof) (rho:env value)
  : Lemma (requires Some? (ofact p) /\ o_obligations_at vtrue i rho p /\
                    OS.boolean_model vtrue vfalse (denotation i rho) /\ equality_model vtrue i rho)
          (ensures OS.observations_agree vtrue (denotation i rho)
                     (fst (Some?.v (ofact p))) (snd (Some?.v (ofact p))))
          (decreases %[osize p; 0])
  = match p with
    | ORefl _ | OIff _ _ | OPremise _ _ -> ()
    | OSym q -> lemma_oproof_sound_at vtrue vfalse i q rho
    | OTrans q r ->
      lemma_oproof_sound_at vtrue vfalse i q rho;
      lemma_oproof_sound_at vtrue vfalse i r rho
    | OCongr f xs ys ps -> lemma_observation_args_sound_at vtrue vfalse i xs ys ps rho

and lemma_matching_observation_sound_at (#value:Type) (vtrue vfalse:value)
                                       (i:interpretation value) (a b:expr)
                                       (ps:list oproof) (rho:env value)
  : Lemma (requires observation_matches a b (ofacts ps) /\
                    o_obligations_list_at vtrue i rho ps /\
                    OS.boolean_model vtrue vfalse (denotation i rho) /\ equality_model vtrue i rho)
          (ensures eval i a rho == eval i b rho)
          (decreases %[osizes ps; 0])
  = match ps with
    | [] -> ()
    | p :: rest ->
      (match ofact p with
       | Some (s, t) ->
         if s = a && t = b then (
           lemma_oproof_sound_at vtrue vfalse i p rho;
           OS.lemma_values vtrue vfalse (denotation i rho) a b)
         else lemma_matching_observation_sound_at vtrue vfalse i a b rest rho
       | None -> lemma_matching_observation_sound_at vtrue vfalse i a b rest rho)

and lemma_observation_args_sound_at (#value:Type) (vtrue vfalse:value)
                                   (i:interpretation value) (xs ys:list expr)
                                   (ps:list oproof) (rho:env value)
  : Lemma (requires observations_matched xs ys (ofacts ps) /\
                    o_obligations_list_at vtrue i rho ps /\
                    OS.boolean_model vtrue vfalse (denotation i rho) /\ equality_model vtrue i rho)
          (ensures eval_args i xs rho == eval_args i ys rho)
          (decreases %[osizes ps; List.Tot.length xs])
  = match xs, ys with
    | [], [] -> ()
    | x :: xs', y :: ys' ->
      (if x = y then () else lemma_matching_observation_sound_at vtrue vfalse i x y ps rho);
      lemma_observation_args_sound_at vtrue vfalse i xs' ys' ps rho

let rec lemma_obligations_at (i:interpretation value) (rho:env value) (p:oproof)
  : Lemma (requires o_obligations i p)
          (ensures o_obligations_at (VBool true) i rho p)
          (decreases p)
  = match p with
    | ORefl _ | OIff _ _ -> ()
    | OPremise a b -> lemma_agreement i rho a b
    | OSym q -> lemma_obligations_at i rho q
    | OTrans q r -> lemma_obligations_at i rho q; lemma_obligations_at i rho r
    | OCongr _ _ _ ps -> lemma_obligations_list_at i rho ps

and lemma_obligations_list_at (i:interpretation value) (rho:env value) (ps:list oproof)
  : Lemma (requires o_obligations_list i ps)
          (ensures o_obligations_list_at (VBool true) i rho ps)
          (decreases ps)
  = match ps with
    | [] -> ()
    | p :: rest -> lemma_obligations_at i rho p; lemma_obligations_list_at i rho rest

let lemma_oproof_sound (i:interpretation value) (p:oproof) (rho:env value)
  : Lemma (requires Some? (ofact p) /\ o_obligations i p /\ boolean_model i /\ eq_sound i)
          (ensures observations_agree i rho (fst (Some?.v (ofact p))) (snd (Some?.v (ofact p))))
  = lemma_obligations_at i rho p;
    lemma_boolean_values i rho;
    lemma_oproof_sound_at (VBool true) (VBool false) i p rho;
    lemma_agreement i rho (fst (Some?.v (ofact p))) (snd (Some?.v (ofact p)))

let lemma_matching_observation_sound (i:interpretation value) (a b:expr)
                                    (ps:list oproof) (rho:env value)
  : Lemma (requires observation_matches a b (ofacts ps) /\
                    o_obligations_list i ps /\ boolean_model i /\ eq_sound i)
          (ensures eval i a rho == eval i b rho)
  = lemma_obligations_list_at i rho ps;
    lemma_boolean_values i rho;
    lemma_matching_observation_sound_at (VBool true) (VBool false) i a b ps rho

let lemma_observation_args_sound (i:interpretation value) (xs ys:list expr)
                                (ps:list oproof) (rho:env value)
  : Lemma (requires observations_matched xs ys (ofacts ps) /\
                    o_obligations_list i ps /\ boolean_model i /\ eq_sound i)
          (ensures eval_args i xs rho == eval_args i ys rho)
  = lemma_obligations_list_at i rho ps;
    lemma_boolean_values i rho;
    lemma_observation_args_sound_at (VBool true) (VBool false) i xs ys ps rho

let lemma_mp_oeq_sound (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires observations_agree i rho a b /\ lit_true i rho a)
          (ensures lit_true i rho b)
  = lemma_agreement i rho a b;
    OS.lemma_mp (VBool true) (denotation i rho) a b

let decide_mp_oeq (a relation:expr) : option expr =
  match is_oeq relation with
  | Some (s, t) -> if a = s then Some t else None
  | None -> None

let lemma_decide_mp_oeq_sound (i:interpretation value) (rho:env value)
                             (a relation:expr)
  : Lemma (requires Some? (decide_mp_oeq a relation) /\ lit_true i rho a /\
                    (match is_oeq relation with
                     | Some (s, t) -> observations_agree i rho s t
                     | None -> False))
          (ensures lit_true i rho (Some?.v (decide_mp_oeq a relation)))
  = match is_oeq relation with
    | Some (s, t) -> lemma_mp_oeq_sound i rho s t
    | None -> ()

let lemma_observations_equisatisfiable (i:interpretation value) (a b:expr)
  : Lemma (requires forall (rho:env value). observations_agree i rho a b)
          (ensures (exists (rho:env value). lit_true i rho a) <==>
                   (exists (rho:env value). lit_true i rho b))
  = let aux (rho:env value)
      : Lemma (OS.observations_agree (VBool true) (denotation i rho) a b)
      = lemma_agreement i rho a b in
    FStar.Classical.forall_intro aux;
    OS.lemma_equisatisfiable (VBool true) (denotation i) a b
