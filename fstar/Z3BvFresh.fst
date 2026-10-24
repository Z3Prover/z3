module Z3BvFresh

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module BV = Z3BvLemma
module W = Z3BvWord
module SM = Z3ScopedModel
module D = Z3Definitions
module SK = Z3Skolemization
module L = FStar.List.Tot
module U = FStar.UInt
module M = FStar.Math.Lemmas

type reconstruction = {
  width: pos;
  original: func_decl;
  constructor: func_decl;
  symbols: list func_decl;
}

let atoms (symbols:list func_decl) : list expr =
  L.map (fun f -> App f []) symbols

let source (r:reconstruction) : expr = App r.original []
let word (r:reconstruction) : expr = App r.constructor (atoms r.symbols)

let rec witnesses (start:nat) (symbols:list func_decl)
  : Tot (list SK.witness) (decreases symbols) =
  match symbols with
  | [] -> []
  | f :: rest -> (start, f) :: witnesses (start + 1) rest

let rec valid_symbols (symbols:list func_decl) : Tot bool (decreases symbols) =
  match symbols with
  | [] -> true
  | f :: rest ->
    f.interp = None && f.int_params = [] && f.domain = [] && f.range = bool_sort &&
    not (L.mem f rest) && valid_symbols rest

let valid (r:reconstruction) : bool =
  r.width <= 4096 && L.length r.symbols = r.width &&
  r.original.interp = None && r.original.int_params = [] &&
  r.original.domain = [] && r.original.range = BV.bv_sort r.width &&
  r.original.range <> bool_sort &&
  valid_symbols r.symbols &&
  BV.word_parts (word r) = Some (r.width, atoms r.symbols)

let rec symbols_of (args:list expr) : Tot (option (list func_decl)) (decreases args) =
  match args with
  | [] -> Some []
  | App f [] :: rest ->
    (match symbols_of rest with Some fs -> Some (f :: fs) | None -> None)
  | _ -> None

let candidate_pair (a b:expr) : option reconstruction =
  match a, b, BV.word_parts b with
  | App f [], App g args, Some (width, _) ->
    (match symbols_of args with
     | Some fs -> Some { width = width; original = f; constructor = g; symbols = fs }
     | None -> None)
  | _, _, _ -> None

let candidate (e:expr) : option reconstruction =
  match Z3ArrayLemma.equality_parts e with
  | Some (a, b) ->
    (match candidate_pair a b with Some r -> Some r | None -> candidate_pair b a)
  | None -> None

let check_condition (inputs:list expr) (e:expr)
  : result:option reconstruction{
      forall r. result == Some r ==>
        valid r /\ SK.fresh_args (witnesses 0 r.symbols) inputs /\
        (e == mk_eq_expr (source r) (word r) \/ e == mk_eq_expr (word r) (source r))} =
  match candidate e with
  | Some r ->
    if valid r && SK.fresh_args (witnesses 0 r.symbols) inputs &&
       (e = mk_eq_expr (source r) (word r) || e = mk_eq_expr (word r) (source r))
    then Some r else None
  | None -> None

let rec lookup (f:func_decl) (symbols:list func_decl) (n:nat)
  : Tot (option bool) (decreases symbols) =
  match symbols with
  | [] -> None
  | g :: rest -> if f = g then Some (n % 2 <> 0) else lookup f rest (n / 2)

let number (r:reconstruction) (i:interpretation value) (project:pos -> value -> int)
  : U.uint_t r.width =
  U.to_uint_t r.width (project r.width (eval i (source r) (fun _ -> VInt 0)))

(* Only nullary fresh Boolean applications are changed. *)
let extend (r:reconstruction) (i:interpretation value) (project:pos -> value -> int)
  : interpretation value =
  let n = number r i project in
  { i with uninterp_app = (fun f vs ->
      match vs with
      | [] ->
        (match lookup f r.symbols n with
         | Some b -> VBool b
         | None -> i.uninterp_app f vs)
      | _ -> i.uninterp_app f vs) }

let rec lemma_lookup_outside (start:nat) (symbols:list func_decl) (f:func_decl) (n:nat)
  : Lemma ((SK.component f (witnesses start symbols) == None) <==>
           lookup f symbols n == None)
          (decreases symbols)
  = match symbols with
    | [] -> ()
    | _ :: rest -> lemma_lookup_outside (start + 1) rest f (n / 2)

let lemma_preserve_inputs (r:reconstruction) (inputs:list expr)
                          (i:interpretation value) (project:pos -> value -> int) (rho:env value)
  : Lemma (requires quant_extensional i /\ SK.fresh_args (witnesses 0 r.symbols) inputs)
          (ensures eval_args i inputs rho == eval_args (extend r i project) inputs rho)
  = let j = extend r i project in
    let outside (f:func_decl{is_uninterp_decl f}) (vs:list value)
      : Lemma (SK.component f (witnesses 0 r.symbols) == None ==>
                 i.uninterp_app f vs == j.uninterp_app f vs)
      = lemma_lookup_outside 0 r.symbols f (number r i project);
        match vs with [] -> () | _ -> () in
    FStar.Classical.forall_intro_2 outside;
    SK.lemma_fresh_args_evaluation (witnesses 0 r.symbols) inputs i j rho

let rec lemma_lookup_member (f:func_decl) (symbols:list func_decl) (n:nat) (b:bool)
  : Lemma (requires lookup f symbols n == Some b)
          (ensures L.mem f symbols)
          (decreases symbols)
  = match symbols with
    | [] -> ()
    | g :: rest -> if f <> g then lemma_lookup_member f rest (n / 2) b

let rec lemma_lookup_other_sort (symbols:list func_decl) (n:nat) (f:func_decl)
  : Lemma (requires valid_symbols symbols /\ f.range <> bool_sort)
          (ensures lookup f symbols n == None)
          (decreases symbols)
  = match symbols with
    | [] -> ()
    | _ :: rest -> lemma_lookup_other_sort rest (n / 2) f

let assignments_hold (j:interpretation value) (symbols:list func_decl) (n:nat) : prop =
  forall (f:func_decl{is_uninterp_decl f}) (b:bool).
    lookup f symbols n == Some b ==> j.uninterp_app f [] == VBool b

let lemma_extend_assignments (r:reconstruction) (i:interpretation value)
                             (project:pos -> value -> int)
  : Lemma (assignments_hold (extend r i project) r.symbols (number r i project))
  = let assigned (f:func_decl{is_uninterp_decl f}) (b:bool)
      : Lemma (lookup f r.symbols (number r i project) == Some b ==>
                 (extend r i project).uninterp_app f [] == VBool b) = () in
    FStar.Classical.forall_intro_2 assigned

let rec lemma_atoms_values (i j:interpretation value) (rho:env value)
                           (symbols:list func_decl) (n:nat)
  : Lemma (requires SM.literal_model i /\ valid_symbols symbols /\ assignments_hold j symbols n)
          (ensures eval_args j (atoms symbols) rho ==
                     eval_args i (W.numeral_bits (L.length symbols) n) rho)
          (decreases symbols)
  = match symbols with
    | [] -> ()
    | f :: rest ->
      let tail (g:func_decl{is_uninterp_decl g}) (b:bool)
        : Lemma (lookup g rest (n / 2) == Some b ==> j.uninterp_app g [] == VBool b)
        = if lookup g rest (n / 2) = Some b then (
            lemma_lookup_member g rest (n / 2) b;
            assert (g <> f)) in
      FStar.Classical.forall_intro_2 tail;
      lemma_atoms_values i j rho rest (n / 2);
      assert (j.uninterp_app f [] == VBool (n % 2 <> 0))

let rec lemma_same_domains (xs ys:list expr)
  : Lemma (requires L.length xs == L.length ys)
          (ensures L.map (fun _ -> bool_sort) xs == L.map (fun _ -> bool_sort) ys)
          (decreases xs)
  = match xs, ys with
    | _ :: rest, _ :: tail -> lemma_same_domains rest tail
    | _, _ -> ()

let rec lemma_atoms_shape (symbols:list func_decl)
  : Lemma (requires valid_symbols symbols)
          (ensures L.length (atoms symbols) == L.length symbols /\
                   D.scoped_args [] (atoms symbols) /\
                   L.for_all (fun a -> get_sort a = bool_sort) (atoms symbols))
          (decreases symbols)
  = match symbols with [] -> () | _ :: rest -> lemma_atoms_shape rest

let lemma_replacement_shape (r:reconstruction) (args:list expr)
  : Lemma (requires valid r /\ L.length args == r.width /\
                    D.scoped_args [] args /\ L.for_all (fun a -> get_sort a = bool_sort) args)
          (ensures D.scoped [] (App r.constructor args) /\
                   BV.word_parts (App r.constructor args) == Some (r.width, args))
  = lemma_atoms_shape r.symbols;
    lemma_same_domains (atoms r.symbols) args;
    W.lemma_boolean_args args

let lemma_number (r:reconstruction) (i:interpretation value)
                 (project:pos -> value -> int) (rho:env value)
  : Lemma (requires valid r /\ BV.bv_model i project)
          (ensures number r i project == project r.width (eval i (source r) rho))
  = BV.lemma_word i rho project r.width (source r);
    assert (eval i (source r) rho == eval i (source r) (fun _ -> VInt 0));
    M.small_mod (project r.width (eval i (source r) rho)) (pow2 r.width)

let lemma_reconstruction_value_in (r:reconstruction) (i j:interpretation value)
                                  (project:pos -> value -> int) (rho:env value)
  : Lemma (requires valid r /\ BV.bv_model i project /\ SM.literal_model i /\
                    j.interp_app == i.interp_app /\
                    eval j (source r) rho == eval i (source r) rho /\
                    assignments_hold j r.symbols (number r i project))
          (ensures eval j (word r) rho == eval i (source r) rho)
  = let n = number r i project in
    lemma_atoms_values i j rho r.symbols n;
    W.lemma_numeral_bits i rho r.width n;
    let bits = W.numeral_bits r.width n in
    let literal_word = App r.constructor bits in
    lemma_replacement_shape r bits;
    W.lemma_parts i rho project literal_word r.width bits;
    lemma_number r i project rho;
    BV.lemma_reflect i rho project r.width (source r) literal_word

let lemma_reconstruction_in (r:reconstruction) (i j:interpretation value)
                            (project:pos -> value -> int) (rho:env value)
  : Lemma (requires valid r /\ BV.bv_model i project /\ SM.literal_model i /\ SM.reflexive_equality i /\
                    j.interp_app == i.interp_app /\
                    eval j (source r) rho == eval i (source r) rho /\
                    assignments_hold j r.symbols (number r i project))
          (ensures eval j (word r) rho == eval i (source r) rho /\
                   eval j (mk_eq_expr (source r) (word r)) rho == VBool true)
  = lemma_reconstruction_value_in r i j project rho;
    let v = eval i (source r) rho in
    assert (i.interp_app (eq_decl (get_sort (source r))) [v; v] == VBool true);
    assert (eval i (mk_eq_expr (source r) (source r)) rho == VBool true)

let lemma_reconstruction (r:reconstruction) (i:interpretation value)
                         (project:pos -> value -> int) (rho:env value)
  : Lemma (requires valid r /\ BV.bv_model i project /\ SM.literal_model i)
          (ensures (let j = extend r i project in
                    eval j (source r) rho == eval i (source r) rho /\
                    eval j (word r) rho == eval i (source r) rho))
  = lemma_lookup_other_sort r.symbols (number r i project) r.original;
    lemma_extend_assignments r i project;
    lemma_reconstruction_value_in r i (extend r i project) project rho

let lemma_model_extension (inputs:list expr) (e:expr) (r:reconstruction)
                          (i:interpretation value) (project:pos -> value -> int) (rho:env value)
  : Lemma (requires check_condition inputs e == Some r /\ quant_extensional i /\
                    BV.bv_model i project /\ SM.literal_model i /\ SM.reflexive_equality i)
          (ensures (let j = extend r i project in
                    quant_extensional j /\ j.interp_app == i.interp_app /\
                    j.interp_quant == i.interp_quant /\
                    eval_args j inputs rho == eval_args i inputs rho /\
                    eval j e rho == VBool true))
  = let j = extend r i project in
    SK.lemma_quantifier_fields i j;
    lemma_preserve_inputs r inputs i project rho;
    lemma_reconstruction r i project rho;
    let v = eval i (source r) rho in
    assert (i.interp_app (eq_decl (get_sort (source r))) [v; v] == VBool true);
    assert (eval i (mk_eq_expr (source r) (source r)) rho == VBool true)

let equations (rs:list reconstruction) : list expr =
  L.map (fun r -> mk_eq_expr (source r) (word r)) rs

let rec valid_context (rs:list reconstruction) : Tot bool (decreases rs) =
  match rs with
  | [] -> true
  | r :: rest ->
    valid r && SK.fresh_args (witnesses 0 r.symbols) (equations rest) && valid_context rest

let rec fresh_inputs (rs:list reconstruction) (inputs:list expr) : Tot bool (decreases rs) =
  match rs with
  | [] -> true
  | r :: rest -> SK.fresh_args (witnesses 0 r.symbols) inputs && fresh_inputs rest inputs

let rec matches (rs:list reconstruction) (es:list expr) : Tot bool (decreases rs) =
  match rs, es with
  | [], [] -> true
  | r :: rest, e :: tail ->
    (e = mk_eq_expr (source r) (word r) || e = mk_eq_expr (word r) (source r)) && matches rest tail
  | _, _ -> false

let rec check_context (inputs es:list expr)
  : Tot (result:option (list reconstruction){
      forall rs. result == Some rs ==> valid_context rs /\ fresh_inputs rs inputs /\ matches rs es})
      (decreases es) =
  match es with
  | [] -> Some []
  | e :: rest ->
    (match check_condition inputs e, check_context inputs rest with
     | Some r, Some rs ->
       if valid_context (r :: rs) then Some (r :: rs) else None
     | _, _ -> None)

let rec extend_context (rs:list reconstruction) (i:interpretation value)
                       (project:pos -> value -> int)
  : Tot (interpretation value) (decreases rs) =
  match rs with
  | [] -> i
  | r :: rest -> extend r (extend_context rest i project) project

let rec lemma_context_fields (rs:list reconstruction) (i:interpretation value)
                             (project:pos -> value -> int)
  : Lemma ((extend_context rs i project).interp_app == i.interp_app /\
           (extend_context rs i project).interp_quant == i.interp_quant)
          (decreases rs)
  = match rs with [] -> () | _ :: rest -> lemma_context_fields rest i project

let rec lemma_context_inputs (rs:list reconstruction) (inputs:list expr)
                             (i:interpretation value) (project:pos -> value -> int) (rho:env value)
  : Lemma (requires quant_extensional i /\ fresh_inputs rs inputs)
          (ensures eval_args (extend_context rs i project) inputs rho == eval_args i inputs rho)
          (decreases rs)
  = match rs with
    | [] -> ()
    | r :: rest ->
      lemma_context_fields rest i project;
      lemma_context_inputs rest inputs i project rho;
      let older = extend_context rest i project in
      SK.lemma_quantifier_fields i older;
      lemma_preserve_inputs r inputs older project rho

let rec lemma_context_other_sort (rs:list reconstruction) (i:interpretation value)
                                 (project:pos -> value -> int)
                                 (f:func_decl{is_uninterp_decl f}) (vs:list value)
  : Lemma (requires valid_context rs /\ f.range <> bool_sort)
          (ensures (extend_context rs i project).uninterp_app f vs == i.uninterp_app f vs)
          (decreases rs)
  = match rs with
    | [] -> ()
    | r :: rest ->
      lemma_context_other_sort rest i project f vs;
      lemma_lookup_other_sort r.symbols (number r (extend_context rest i project) project) f;
      match vs with [] -> () | _ -> ()

let rec lemma_conj_values (i j:interpretation value) (rho:env value) (es:list expr)
  : Lemma (requires eval_args i es rho == eval_args j es rho)
          (ensures conj_holds i rho es <==> conj_holds j rho es)
          (decreases es)
  = match es with [] -> () | _ :: rest -> lemma_conj_values i j rho rest

let rec lemma_member_fresh (symbols:list func_decl) (rs:list reconstruction) (r:reconstruction)
  : Lemma (requires SK.fresh_args (witnesses 0 symbols) (equations rs) /\ L.mem r rs)
          (ensures SK.fresh_args (witnesses 0 symbols) [source r; word r])
          (decreases rs)
  = match rs with
    | [] -> ()
    | s :: rest -> if s <> r then lemma_member_fresh symbols rest r

let rec lemma_context_value (rs:list reconstruction) (r:reconstruction)
                            (i:interpretation value) (project:pos -> value -> int) (rho:env value)
  : Lemma (requires valid_context rs /\ L.mem r rs /\ quant_extensional i /\
                    BV.bv_model i project /\ SM.literal_model i)
          (ensures eval (extend_context rs i project) (word r) rho ==
                     eval (extend_context rs i project) (source r) rho)
          (decreases rs)
  = match rs with
    | [] -> ()
    | s :: rest ->
      lemma_context_fields rest i project;
      let older = extend_context rest i project in
      let j = extend s older project in
      SK.lemma_quantifier_fields i older;
      if s = r then (
        lemma_context_other_sort rest i project s.original [];
        assert (number s older project == number s i project);
        lemma_lookup_other_sort s.symbols (number s older project) s.original;
        lemma_extend_assignments s older project;
        lemma_reconstruction_value_in s i j project rho)
      else (
        lemma_context_value rest r i project rho;
        lemma_member_fresh s.symbols rest r;
        lemma_preserve_inputs s [source r; word r] older project rho)

let rec lemma_context_reconstructions (rs:list reconstruction) (i:interpretation value)
                                      (project:pos -> value -> int) (rho:env value)
  : Lemma (requires valid_context rs /\ quant_extensional i /\
                    BV.bv_model i project /\ SM.literal_model i /\ SM.reflexive_equality i)
          (ensures conj_holds (extend_context rs i project) rho (equations rs))
          (decreases rs)
  = match rs with
    | [] -> ()
    | r :: rest ->
      lemma_context_reconstructions rest i project rho;
      lemma_context_fields rest i project;
      let older = extend_context rest i project in
      let j = extend r older project in
      SK.lemma_quantifier_fields i older;
      lemma_preserve_inputs r (equations rest) older project rho;
      lemma_conj_values older j rho (equations rest);
      lemma_context_other_sort rest i project r.original [];
      assert (number r older project == number r i project);
      lemma_lookup_other_sort r.symbols (number r older project) r.original;
      lemma_extend_assignments r older project;
      lemma_reconstruction_value_in r i j project rho;
      let v = eval i (source r) rho in
      assert (i.interp_app (eq_decl (get_sort (source r))) [v; v] == VBool true)

let lemma_context_model_extension (inputs es:list expr) (rs:list reconstruction)
                                  (i:interpretation value) (project:pos -> value -> int)
                                  (rho:env value)
  : Lemma (requires check_context inputs es == Some rs /\ quant_extensional i /\
                    BV.bv_model i project /\ SM.literal_model i /\ SM.reflexive_equality i)
          (ensures (let j = extend_context rs i project in
                    j.interp_app == i.interp_app /\ j.interp_quant == i.interp_quant /\
                    quant_extensional j /\ eval_args j inputs rho == eval_args i inputs rho /\
                    conj_holds j rho (equations rs)))
  = lemma_context_fields rs i project;
    SK.lemma_quantifier_fields i (extend_context rs i project);
    lemma_context_inputs rs inputs i project rho;
    lemma_context_reconstructions rs i project rho
