module Z3SkolemSyntax

open Z3AstTheory
open Z3ClauseSyntax
open Z3ProofIndex
module L = FStar.List.Tot
open FStar.List.Tot

type dependency = nat & sort
type witness = nat & func_decl

type definition = {
  bound_sorts: list sort;
  negative: bool;
  body: expr;
  dependencies: list dependency;
  witnesses: list witness;
}

let rec dependency_arguments (depth:nat) (deps:list dependency)
  : Tot (list expr) (decreases deps) =
  match deps with
  | [] -> []
  | (n, s) :: rest -> Var (depth + n) s :: dependency_arguments depth rest

let rec lookup (n:nat) (ws:list witness) : Tot (option func_decl) (decreases ws) =
  match ws with
  | [] -> None
  | (m, f) :: rest -> if n = m then Some f else lookup n rest

let rec component (f:func_decl) (ws:list witness) : Tot (option nat) (decreases ws) =
  match ws with
  | [] -> None
  | (n, g) :: rest -> if f = g then Some n else component f rest

let rec substitute (depth count:nat) (deps:list dependency) (ws:list witness) (e:expr)
  : Tot (option expr) (decreases e) =
  match e with
  | Var n s ->
    if n < depth then Some e
    else if n < depth + count then
      (match lookup (n - depth) ws with
       | Some f -> if f.range = s then Some (App f (dependency_arguments depth deps)) else None
       | None -> None)
    else Some (Var (n - count) s)
  | App f args ->
    substitute_args depth count deps ws args >>= (fun args' -> Some (App f args'))
  | Quantifier k bs s b ->
    substitute (depth + L.length bs) count deps ws b >>=
      (fun b' -> Some (Quantifier k bs s b'))

and substitute_args (depth count:nat) (deps:list dependency) (ws:list witness) (args:list expr)
  : Tot (option (list expr)) (decreases args) =
  match args with
  | [] -> Some []
  | a :: rest ->
    substitute depth count deps ws a >>= (fun a' ->
    substitute_args depth count deps ws rest >>= (fun rest' -> Some (a' :: rest')))

let rec dependency_indices (deps:list dependency) : Tot (list nat) (decreases deps) =
  match deps with [] -> [] | (n, _) :: rest -> n :: dependency_indices rest

let rec covered (depth:nat) (deps:list dependency) (e:expr) : Tot bool (decreases e) =
  match e with
  | Var n _ -> n < depth || L.mem (n - depth) (dependency_indices deps)
  | App _ args -> covered_args depth deps args
  | Quantifier _ bs _ b -> covered (depth + L.length bs) deps b

and covered_args (depth:nat) (deps:list dependency) (args:list expr)
  : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> covered depth deps a && covered_args depth deps rest

let rec fresh (ws:list witness) (e:expr) : Tot bool (decreases e) =
  match e with
  | Var _ _ -> true
  | App f args -> component f ws = None && fresh_args ws args
  | Quantifier _ _ _ b -> fresh ws b

and fresh_args (ws:list witness) (args:list expr) : Tot bool (decreases args) =
  match args with [] -> true | a :: rest -> fresh ws a && fresh_args ws rest

let rec dependency_sorts (deps:list dependency) : Tot (list sort) (decreases deps) =
  match deps with [] -> [] | (_, s) :: rest -> s :: dependency_sorts rest

let rec valid_dependencies (deps:list dependency) : Tot bool (decreases deps) =
  match deps with
  | [] -> true
  | (n, _) :: rest ->
    not (L.mem n (dependency_indices rest)) && valid_dependencies rest

let rec valid_witnesses (sorts:list sort) (deps:list dependency) (ws:list witness)
  : Tot bool (decreases ws) =
  match ws with
  | [] -> true
  | (n, f) :: rest ->
    n < L.length sorts && f.range = L.index sorts n &&
    f.interp = None && f.int_params = [] && f.domain = dependency_sorts deps &&
    lookup n rest = None && component f rest = None && valid_witnesses sorts deps rest

let valid (d:definition) : bool =
  get_sort d.body = bool_sort && d.witnesses <> [] &&
  valid_dependencies d.dependencies &&
  valid_witnesses (L.rev d.bound_sorts) d.dependencies d.witnesses &&
  covered (L.length d.bound_sorts) d.dependencies d.body && fresh d.witnesses d.body

let rec infer_dependencies (depth:nat) (args:list expr)
  : Tot (option (list dependency)) (decreases args) =
  match args with
  | [] -> Some []
  | Var n s :: rest ->
    if n < depth then None
    else infer_dependencies depth rest >>= (fun deps -> Some ((n - depth, s) :: deps))
  | _ -> None

type candidate = nat & func_decl & list dependency

let rec infer (depth count:nat) (a b:expr) : Tot (option (list candidate)) (decreases a) =
  match a, b with
  | Var n s, _ ->
    if n < depth then (if a = b then Some [] else None)
    else if n < depth + count then
      (match b with
       | App f args ->
         if f.range <> s || not (sorts_match args f.domain) then None
         else infer_dependencies depth args >>= (fun deps ->
           let choices:list candidate = [(n - depth, f, deps)] in Some choices)
       | _ -> None)
    else if b = Var (n - count) s then Some [] else None
  | App f args, App g args' ->
    if f = g then infer_args depth count args args' else None
  | Quantifier k bs s body, Quantifier k' bs' s' body' ->
    if k = k' && bs = bs' && s = s'
    then infer (depth + L.length bs) count body body' else None
  | _, _ -> None

and infer_args (depth count:nat) (args args':list expr)
  : Tot (option (list candidate)) (decreases args) =
  match args, args' with
  | [], [] -> Some []
  | a :: rest, b :: tail ->
    infer depth count a b >>= (fun here ->
    infer_args depth count rest tail >>= (fun more -> Some (here @ more)))
  | _, _ -> None

let rec collect_witnesses (deps:list dependency) (choices:list candidate) (ws:list witness)
  : Tot (option (list witness)) (decreases choices) =
  match choices with
  | [] -> Some ws
  | (n, f, ds) :: rest ->
    if ds <> deps then None
    else match lookup n ws with
    | Some old -> if old = f then collect_witnesses deps rest ws else None
    | None -> collect_witnesses deps rest ((n, f) :: ws)

let source (d:definition) : expr =
  let q = Quantifier (if d.negative then Forall_k else Exists_k) d.bound_sorts bool_sort d.body in
  if d.negative then mk_not_expr q else q

let negative_body (e:expr) : option expr =
  match e with
  | App n [a] -> if n = not_decl && get_sort a = bool_sort then Some a else None
  | _ -> None

let negate (e:expr) : expr =
  match negative_body e with Some a -> a | None -> mk_not_expr e

let instantiation (d:definition) : option expr =
  substitute 0 (L.length d.bound_sorts) d.dependencies d.witnesses d.body >>=
    (fun e -> Some (if d.negative then negate e else e))

let make_definition (negative:bool) (sorts:list sort) (body target:expr)
  : result:option definition{
      forall d. result == Some d ==> valid d /\ d.negative == negative /\
        d.bound_sorts == sorts /\ d.body == body /\
        substitute 0 (L.length sorts) d.dependencies d.witnesses body == Some target} =
  infer 0 (L.length sorts) body target >>= (fun choices ->
  match choices with
  | [] -> None
  | (_, _, deps) :: _ ->
    collect_witnesses deps choices [] >>= (fun ws ->
    let d = { bound_sorts = sorts; negative = negative; body = body;
              dependencies = deps; witnesses = ws } in
    if valid d && substitute 0 (L.length sorts) deps ws body = Some target
    then Some d else None))

(* The binding block, polarity, body, and expected instance named by an `sk` conclusion
   `a ~ b`. The choice-based and the vacuous recognizers share this shape check. *)
let block_parts (a b:expr) : option (bool & list sort & expr & expr) =
  match a with
  | Quantifier Exists_k bs s body ->
    if s = bool_sort && get_sort b = bool_sort then Some (false, bs, body, b) else None
  | App n [Quantifier Forall_k bs s body] ->
    if n <> not_decl || s <> bool_sort || get_sort b <> bool_sort then None
    else (match negative_body b with
      | Some target -> Some (true, bs, body, target)
      | None ->
        if Some? (negative_body body) then Some (true, bs, body, mk_not_expr b) else None)
  | _ -> None

let definition_of (a b:expr)
  : result:option definition{
      forall d. result == Some d ==> valid d /\ source d == a /\ instantiation d == Some b} =
  let candidate =
    match block_parts a b with
    | Some (negative, bs, body, target) -> make_definition negative bs body target
    | None -> None in
  candidate >>= (fun d ->
    if valid d && source d = a && instantiation d = Some b then Some d else None)

(* A block none of whose variables occurs in its body has no Skolem symbol to introduce.
   With no witnesses, substitution fails exactly when a variable of the block occurs and
   otherwise only lowers the ambient indices, so nothing is collected from the proof and
   no choice context is consulted. *)
let vacuous_definition (negative:bool) (sorts:list sort) (body:expr) : definition =
  { bound_sorts = sorts; negative = negative; body = body; dependencies = []; witnesses = [] }

let vacuous (a b:expr) : bool =
  match block_parts a b with
  | Some (negative, sorts, body, _) ->
    let d = vacuous_definition negative sorts body in
    get_sort body = bool_sort && source d = a && instantiation d = Some b
  | None -> false

let check (defs:list definition) (a b:expr) : bool =
  vacuous a b || (match definition_of a b with Some d -> L.mem d defs | None -> false)

let rec disjoint (newer older:list witness) : Tot bool (decreases older) =
    match older with
    | [] -> true
    | (_, f) :: rest -> component f newer = None && disjoint newer rest

let rec safe_extension (d:definition) (older:list definition) : Tot bool (decreases older) =
    match older with
    | [] -> true
    | e :: rest ->
      disjoint d.witnesses e.witnesses && fresh d.witnesses e.body && safe_extension d rest

let rec ordered_context (defs:list definition) : Tot bool (decreases defs) =
    match defs with
    | [] -> true
    | d :: rest -> valid d && safe_extension d rest && ordered_context rest

let rec add_definition (defs:list definition) (d:definition)
    : Tot (option (list definition)) (decreases defs) =
    match defs with
    | [] -> Some [d]
    | e :: rest ->
      if not (disjoint d.witnesses e.witnesses) then
        if d = e then Some defs else None
      else add_definition rest d >>= (fun more -> Some (e :: more))

let rec select_latest (prefix remaining:list definition)
    : Tot (option (definition & list definition)) (decreases remaining) =
    match remaining with
    | [] -> None
    | d :: rest ->
      if safe_extension d (prefix @ rest) then Some (d, prefix @ rest)
      else select_latest (d :: prefix) rest

let rec order_context (fuel:nat) (defs:list definition)
    : Tot (option (list definition)) (decreases fuel) =
    if ordered_context defs then Some defs
    else if fuel = 0 then None
    else select_latest [] defs >>= (fun (d, rest) ->
      order_context (fuel - 1) rest >>= (fun tail ->
      let result = d :: tail in if ordered_context result then Some result else None))

let rec fresh_inputs (defs:list definition) (inputs:list expr) : Tot bool (decreases defs) =
    match defs with
    | [] -> true
    | d :: rest -> fresh_args d.witnesses inputs && fresh_inputs rest inputs

let lemma_substitute_sort (depth count:nat) (deps:list dependency)
                            (ws:list witness) (e result:expr)
    : Lemma (requires substitute depth count deps ws e == Some result)
            (ensures get_sort e == get_sort result) =
    match e with Var _ _ | App _ _ | Quantifier _ _ _ _ -> ()

let rec lemma_witness_lookup (sorts:list sort) (deps:list dependency) (ws:list witness)
                             (n:nat) (f:func_decl)
  : Lemma (requires valid_witnesses sorts deps ws /\ lookup n ws == Some f)
          (ensures n < L.length sorts /\ f.interp == None /\ component f ws == Some n)
          (decreases ws) =
  match ws with
  | [] -> ()
  | (m, _) :: rest ->
    if n <> m then lemma_witness_lookup sorts deps rest n f

