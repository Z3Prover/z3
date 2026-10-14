(* A separate judgment for the checked ground fragment of observational
   equality. These constructors preserve observations in the same model,
   which is sufficient for equisatisfiability. General equivalence modulo
   naming requires model-extension/freshness witnesses and is not asserted
   by this theory. In particular, ~ is not an object-language equality. *)
module Z3ObservationalEquality

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory

let oeq_decl : func_decl =
  { decl_name = "~"; domain = [bool_sort; bool_sort]; range = bool_sort;
    interp = Some op_oeq; int_params = [] }

let mk_oeq_expr (a b:expr) : expr = App oeq_decl [a; b]

let is_oeq (e:expr) : option (expr & expr) =
  match e with
  | App f [a; b] ->
    if f = oeq_decl && get_sort a = bool_sort && get_sort b = bool_sort
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
    | OIff a b | OPremise a b -> Some (a, b)
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
    if get_sort a = bool_sort && get_sort b = bool_sort then result else None
  | None -> None

and ofacts (ps:list oproof) : Tot (list (option (expr & expr))) (decreases ps) =
  match ps with
  | [] -> []
  | p :: rest -> ofact p :: ofacts rest

let observations_agree (i:interpretation value) (rho:env value) (a b:expr) : prop =
  lit_true i rho a <==> lit_true i rho b

let boolean_model (i:interpretation value) : prop =
  forall (a:expr) (rho:env value).
    get_sort a == bool_sort ==> VBool? (eval i a rho)

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

let lemma_observations_values (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires boolean_model i /\ get_sort a == bool_sort /\
                    get_sort b == bool_sort /\ observations_agree i rho a b)
          (ensures eval i a rho == eval i b rho)
  = match eval i a rho, eval i b rho with
    | VBool x, VBool y -> ()
    | _, _ -> ()

let rec lemma_oproof_sound (i:interpretation value) (p:oproof) (rho:env value)
  : Lemma (requires Some? (ofact p) /\ o_obligations i p /\
                    boolean_model i /\ eq_sound i)
          (ensures observations_agree i rho (fst (Some?.v (ofact p)))
                                            (snd (Some?.v (ofact p))))
          (decreases %[osize p; 0])
  = match p with
    | ORefl _ | OIff _ _ | OPremise _ _ -> ()
    | OSym q -> lemma_oproof_sound i q rho
    | OTrans q r ->
      lemma_oproof_sound i q rho;
      lemma_oproof_sound i r rho
    | OCongr f xs ys ps -> lemma_observation_args_sound i xs ys ps rho

and lemma_matching_observation_sound (i:interpretation value) (a b:expr)
                                    (ps:list oproof) (rho:env value)
  : Lemma (requires observation_matches a b (ofacts ps) /\
                    o_obligations_list i ps /\ boolean_model i /\ eq_sound i)
          (ensures eval i a rho == eval i b rho)
          (decreases %[osizes ps; 0])
  = match ps with
    | [] -> ()
    | p :: rest ->
      (match ofact p with
       | Some (s, t) ->
         if s = a && t = b then (
           lemma_oproof_sound i p rho;
           lemma_observations_values i rho a b)
         else lemma_matching_observation_sound i a b rest rho
       | None -> lemma_matching_observation_sound i a b rest rho)

and lemma_observation_args_sound (i:interpretation value) (xs ys:list expr)
                                (ps:list oproof) (rho:env value)
  : Lemma (requires observations_matched xs ys (ofacts ps) /\
                    o_obligations_list i ps /\ boolean_model i /\ eq_sound i)
          (ensures eval_args i xs rho == eval_args i ys rho)
          (decreases %[osizes ps; List.Tot.length xs])
  = match xs, ys with
    | [], [] -> ()
    | x :: xs', y :: ys' ->
      (if x = y then () else lemma_matching_observation_sound i x y ps rho);
      lemma_observation_args_sound i xs' ys' ps rho

let lemma_mp_oeq_sound (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires observations_agree i rho a b /\ lit_true i rho a)
          (ensures lit_true i rho b)
  = ()

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
  = ()
