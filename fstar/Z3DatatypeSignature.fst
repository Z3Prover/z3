module Z3DatatypeSignature

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module DT = Z3DatatypeLemma
module L = FStar.List.Tot

type constructor_case = {
  constructor: func_decl;
  recognizer: func_decl;
  accessors: list func_decl;
}

type schema = {
  sorts: list sort;
  cases: list constructor_case;
}

let signature (s:schema) : V.signature = L.map (fun c -> c.constructor) s.cases

let rec dummy_fields (ss:list sort) : Tot (list expr) (decreases ss) =
  match ss with [] -> [] | s :: rest -> Var 0 s :: dummy_fields rest

let constructor_id (f:func_decl) : option (int & int) = DT.constructor f (dummy_fields f.domain)

let rec accessors_match (owner tag:int) (source:sort) (index:nat)
                        (fields:list sort) (accessors:list func_decl)
  : Tot bool (decreases fields) =
  match fields, accessors with
  | [], [] -> true
  | s :: rest, f :: tail ->
    DT.accessor f (Var 0 source) = Some (owner, tag, index) &&
    f.range = s && accessors_match owner tag source (index + 1) rest tail
  | _, _ -> false

let case_valid (c:constructor_case) : bool =
  match constructor_id c.constructor with
  | None -> false
  | Some (owner, tag) ->
    DT.recognizer c.recognizer (Var 0 c.constructor.range) = Some (owner, tag) &&
    accessors_match owner tag c.constructor.range 0 c.constructor.domain c.accessors

let rec distinct_cases (c:constructor_case) (cs:list constructor_case)
  : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | d :: rest ->
    (match constructor_id c.constructor, constructor_id d.constructor with
     | Some (owner, tag), Some (owner', tag') ->
       (if owner = owner' then c.constructor.range = d.constructor.range && tag <> tag'
        else c.constructor.range <> d.constructor.range) && distinct_cases c rest
     | _, _ -> false)

let rec supported_fields (sigma:V.signature) (ss:list sort) : Tot bool (decreases ss) =
  match ss with
  | [] -> true
  | s :: rest ->
    (V.datatype_sort sigma s || not (V.contains_datatype sigma s)) && supported_fields sigma rest

let rec cases_valid (sigma:V.signature) (sorts:list sort) (cs:list constructor_case)
  : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: rest ->
    L.mem c.constructor.range sorts && case_valid c && distinct_cases c rest &&
    supported_fields sigma c.constructor.domain && cases_valid sigma sorts rest

let shape_witness (sigma:V.signature) (s:sort)
  : option (V.value (fun _ -> bool) sigma s) =
  (* Keep the carrier non-erased when Cherry reference-counts the fallback. *)
  V.inhabit (L.length sigma + 1) sigma (fun _ -> false) s

let rec productive (sigma:V.signature) (sorts:list sort) : Tot bool (decreases sorts) =
  match sorts with
  | [] -> true
  | s :: rest ->
    V.datatype_sort sigma s &&
    Some? (shape_witness sigma s) &&
    not (L.mem s rest) && productive sigma rest

let valid (s:schema) : bool =
  not (V.contains_datatype (signature s) bool_sort) &&
  not (V.datatype_sort (signature s) (BaseSort "Int")) &&
  cases_valid (signature s) s.sorts s.cases && productive (signature s) s.sorts

type checked_schema = s:schema{valid s}

let rec lemma_productive (sigma:V.signature) (sorts:list sort) (s:sort)
  : Lemma (requires productive sigma sorts /\ L.mem s sorts)
          (ensures V.datatype_sort sigma s /\
                   Some? (V.inhabit (L.length sigma + 1) sigma (fun _ -> false) s))
          (decreases sorts) =
  match sorts with
  | [] -> ()
  | t :: rest -> if s <> t then lemma_productive sigma rest s

let inhabitant (#base:sort -> Type0) (s:checked_schema)
               (base_value:(t:sort -> base t)) (t:sort{L.mem t s.sorts})
  : V.value base (signature s) t =
  lemma_productive (signature s) s.sorts t;
  let witness =
    match shape_witness (signature s) t with
    | Some value -> value
    | None -> FStar.Pervasives.false_elim () in
  let convert (sort:sort) (_:bool) : base sort = base_value sort in
  V.lemma_map_base convert (signature s) t witness;
  V.map_base convert witness

let rec lemma_signature_range (sorts:list sort) (cs:list constructor_case)
                              (sigma:V.signature) (t:sort)
  : Lemma (requires cases_valid sigma sorts cs /\
                    V.datatype_sort (L.map (fun c -> c.constructor) cs) t)
          (ensures L.mem t sorts)
          (decreases cs) =
  match cs with
  | [] -> ()
  | c :: rest -> if c.constructor.range <> t then lemma_signature_range sorts rest sigma t

let value_inhabitant (#base:sort -> Type0) (s:checked_schema)
                     (base_value:(t:sort -> base t)) (t:sort)
  : V.value base (signature s) t =
  if V.datatype_sort (signature s) t then (
    lemma_signature_range s.sorts s.cases (signature s) t;
    inhabitant s base_value t)
  else V.Scalar t (base_value t)

let default_interpretation (#base:sort -> Type0) (s:checked_schema)
                           (base_value:(t:sort -> base t))
  : V.interpretation base (signature s) = {
  application = (fun f _ -> value_inhabitant s base_value f.range);
  quantification = (fun k bound body_sort _ ->
    value_inhabitant s base_value (quant_sort k bound body_sort));
}

let rec lemma_case_member (sigma:V.signature) (sorts:list sort)
                         (cs:list constructor_case) (c:constructor_case)
  : Lemma (requires cases_valid sigma sorts cs /\ L.mem c cs)
          (ensures case_valid c /\ L.mem c.constructor.range sorts)
          (decreases cs) =
  match cs with
  | [] -> ()
  | d :: rest -> if c <> d then lemma_case_member sigma sorts rest c

let rec lemma_signature_member (cs:list constructor_case) (c:constructor_case)
  : Lemma (requires L.mem c cs)
          (ensures L.mem c.constructor (L.map (fun d -> d.constructor) cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | d :: rest -> if c <> d then lemma_signature_member rest c

type registered_case (s:checked_schema) = c:constructor_case{L.mem c s.cases}

let constructor_value (#base:sort -> Type0) (s:checked_schema) (c:registered_case s)
                      (xs:V.arguments base (signature s) c.constructor.domain)
  : V.value base (signature s) c.constructor.range =
  lemma_signature_member s.cases c;
  V.construct (signature s) c.constructor xs

let recognizer_value (#base:sort -> Type0) (s:checked_schema) (c:registered_case s)
                     (v:V.value base (signature s) c.constructor.range)
  : bool = V.recognize c.constructor v

let accessor_value (#base:sort -> Type0) (s:checked_schema) (c:registered_case s)
                   (n:nat{n < L.length c.constructor.domain})
                   (fallback:V.value base (signature s) c.constructor.range ->
                     V.value base (signature s) (L.index c.constructor.domain n))
                   (v:V.value base (signature s) c.constructor.range)
  : V.value base (signature s) (L.index c.constructor.domain n) =
  lemma_signature_member s.cases c;
  V.select (signature s) c.constructor n fallback v

let lemma_reconstruction (#base:sort -> Type0) (s:checked_schema) (c:registered_case s)
                         (v:V.value base (signature s) c.constructor.range)
  : Lemma (requires recognizer_value s c v)
          (ensures V.Constructor c.constructor (V.fields v) == v /\
                   V.fields_have_sorts (signature s) c.constructor.domain (V.fields v)) =
  V.lemma_reconstruct (signature s) c.constructor v

let rec case_of (cs:list constructor_case) (f:func_decl) : Tot (option constructor_case) (decreases cs) =
  match cs with
  | [] -> None
  | c :: rest -> if c.constructor = f then Some c else case_of rest f

let rec lemma_case_of (cs:list constructor_case) (f:func_decl)
  : Lemma (requires L.mem f (L.map (fun c -> c.constructor) cs))
          (ensures Some? (case_of cs f) /\ L.mem (Some?.v (case_of cs f)) cs /\
                   (Some?.v (case_of cs f)).constructor == f)
          (decreases cs) =
  match cs with
  | [] -> ()
  | c :: rest -> if c.constructor <> f then lemma_case_of rest f

let lemma_exhaustiveness (#base:sort -> Type0) (s:checked_schema) (t:sort{L.mem t s.sorts})
                         (v:V.value base (signature s) t)
  : Lemma (ensures exists (c:constructor_case).
                   L.mem c s.cases /\ c.constructor.range == t /\ V.recognize c.constructor v) =
  lemma_productive (signature s) s.sorts t;
  match v with
  | V.Constructor f _ -> lemma_case_of s.cases f
  | _ -> ()

let rec find_recognizer (f:func_decl) (cs:list constructor_case)
  : Tot (option (c:constructor_case{L.mem c cs /\
      f.domain = [c.constructor.range] /\ f.range = bool_sort}))
        (decreases cs) =
  match cs with
  | [] -> None
  | c :: rest ->
    let matches =
      match constructor_id c.constructor with
      | Some (owner, tag) ->
        DT.recognizer f (Var 0 c.constructor.range) = Some (owner, tag)
      | None -> false in
    if matches && f.domain = [c.constructor.range] && f.range = bool_sort
    then Some c
    else match find_recognizer f rest with
      | Some d -> Some d
      | None -> None

type accessor_match = {
  matched_case: constructor_case;
  field: nat;
}

let rec find_accessor (f:func_decl) (cs:list constructor_case)
  : Tot (option (r:accessor_match{
      L.mem r.matched_case cs /\ r.field < L.length r.matched_case.constructor.domain /\
      f.domain = [r.matched_case.constructor.range] /\
      f.range = L.index r.matched_case.constructor.domain r.field}))
        (decreases cs) =
  match cs with
  | [] -> None
  | c :: rest ->
    let index =
      match constructor_id c.constructor, DT.accessor f (Var 0 c.constructor.range) with
      | Some (owner, tag), Some (owner', tag', n) ->
        if owner = owner' && tag = tag' then Some n else None
      | _, _ -> None in
    let found = match index with
     | Some n ->
       if n < L.length c.constructor.domain && f.domain = [c.constructor.range] &&
          f.range = L.index c.constructor.domain n
       then Some { matched_case = c; field = n } else None
     | None -> None in
    match found with
    | Some r -> Some r
    | None ->
      (match find_accessor f rest with
       | Some r -> Some r
       | None -> None)

noeq
type boolean_carrier (base:sort -> Type0) = {
  encode_bool: bool -> base bool_sort;
  decode_bool: base bool_sort -> bool;
  boolean_isomorphism: u:unit{
    (forall (b:bool). decode_bool (encode_bool b) == b) /\
    (forall (v:base bool_sort). encode_bool (decode_bool v) == v)};
}

let application (#base:sort -> Type0) (s:checked_schema) (booleans:boolean_carrier base)
                (other:V.interpretation base (signature s))
                (f:func_decl) (xs:V.arguments base (signature s) f.domain)
  : V.value base (signature s) f.range =
  if L.mem f (signature s) then V.construct (signature s) f xs
  else match find_recognizer f s.cases with
  | Some c ->
    (match xs with
     | [v] -> V.Scalar bool_sort
                (booleans.encode_bool (recognizer_value s c v))
     | _ -> FStar.Pervasives.false_elim ())
  | None ->
    (match find_accessor f s.cases with
     | Some r ->
       (match xs with
        | [v] ->
          let fallback (value:V.value base (signature s) r.matched_case.constructor.range)
            : V.value base (signature s) (L.index r.matched_case.constructor.domain r.field) =
            other.application f [value] in
          accessor_value s r.matched_case r.field fallback v
        | _ -> FStar.Pervasives.false_elim ())
     | None -> other.application f xs)

let interpretation (#base:sort -> Type0) (s:checked_schema) (booleans:boolean_carrier base)
                   (other:V.interpretation base (signature s))
  : V.interpretation base (signature s) = {
  application = application s booleans other;
  quantification = other.quantification;
}
