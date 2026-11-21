module Z3ObservationalProof

open Z3AstTheory
open Z3ProofTheory
open Z3ClauseSyntax
module OS = Z3ObservationalSemantics
module C = Z3CanonicalOps

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

let denotation (#value:Type) (i:interpretation value) (rho:env value)
  : OS.denotation value (fun _ -> true) =
  fun e -> eval i e rho

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
