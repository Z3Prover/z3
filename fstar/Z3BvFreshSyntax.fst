module Z3BvFreshSyntax

open Z3AstTheory
open Z3ClauseSyntax
module BV = Z3BvSyntax
module W = Z3BvSyntax
module D = Z3DefinitionSyntax
module SK = Z3SkolemSyntax
module L = FStar.List.Tot

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

let rec bit_definitions (width:pos) (original:expr) (start:nat) (symbols:list func_decl)
  : Tot (list D.definition) (decreases symbols) =
  match symbols with
  | [] -> []
  | f :: rest ->
    { D.symbol = f; D.variables = []; D.body = W.projection width original start } ::
      bit_definitions width original (start + 1) rest

let rec projection_definitions (rs:list reconstruction)
  : Tot (list D.definition) (decreases rs) =
  match rs with
  | [] -> []
  | r :: rest ->
    L.append (bit_definitions r.width (source r) 0 r.symbols) (projection_definitions rest)

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
  match Z3ArraySyntax.equality_parts e with
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

