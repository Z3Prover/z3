module Z3Skolemization

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ProofIndex
open Z3ObservationalEquality
module D = Z3Definitions
module Q = Z3QuantifierNnf
module P = Z3QuantifierPull
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

(* Choice is a semantic parameter, never executed by the certificate checker. *)
noeq
type hilbert_choice = {
  epsilon: count:nat -> predicate:(list value -> prop) ->
    Tot (vs:list value{L.length vs = count /\
      ((exists (ws:list value{L.length ws = count}). predicate ws) ==> predicate vs)});
}

let rec dependency_values (deps:list dependency) (rho:env value)
  : Tot (list value) (decreases deps) =
  match deps with [] -> [] | (n, _) :: rest -> rho n :: dependency_values rest rho

let rec dependency_environment (deps:list dependency) (values:list value) (n:nat)
  : Tot value (decreases deps) =
  match deps, values with
  | (m, _) :: rest, v :: tail ->
    if n = m then v else dependency_environment rest tail n
  | _, _ -> VInt 0

let assignment_goal (d:definition) (i:interpretation value) (rho:env value)
                    (vs:list value) : prop =
  lit_true i (shift vs rho) d.body <==> not d.negative

let selected (choice:hilbert_choice) (d:definition) (i:interpretation value)
             (values:list value) : list value =
  choice.epsilon (L.length d.bound_sorts)
    (assignment_goal d i (dependency_environment d.dependencies values))

let extend (choice:hilbert_choice) (d:definition) (i:interpretation value)
  : interpretation value =
  { i with uninterp_app = (fun f values ->
      match component f d.witnesses with
      | Some n ->
        let vs = selected choice d i values in
        if n < L.length vs then L.index vs n else i.uninterp_app f values
      | None -> i.uninterp_app f values) }

let rec coordinate_values (ws:list witness) (values:list value)
                          (i:interpretation value) (vs:list value)
  : Tot prop (decreases ws) =
  match ws with
  | [] -> True
  | (n, f) :: rest ->
    n < L.length vs /\ f.interp == None /\
    i.uninterp_app f values == L.index vs n /\ coordinate_values rest values i vs

let witness_values (d:definition) (i:interpretation value) (rho:env value)
                   (vs:list value) : prop =
  coordinate_values d.witnesses (dependency_values d.dependencies rho) i vs

let witness_model (d:definition) (i:interpretation value) : prop =
  forall (rho:env value).
    exists (vs:list value{L.length vs = L.length d.bound_sorts}).
      witness_values d i rho vs /\
      ((exists (ws:list value{L.length ws = L.length d.bound_sorts}).
         assignment_goal d i rho ws) ==> assignment_goal d i rho vs)

let rec context_model (defs:list definition) (i:interpretation value)
  : Tot prop (decreases defs) =
  match defs with [] -> True | d :: rest -> witness_model d i /\ context_model rest i

let rec lemma_dependency_environment (deps:list dependency) (rho:env value) (n:nat)
  : Lemma (requires L.mem n (dependency_indices deps))
          (ensures dependency_environment deps (dependency_values deps rho) n == rho n)
          (decreases deps) =
  match deps with
  | [] -> ()
  | (m, _) :: rest -> if n <> m then lemma_dependency_environment rest rho n

let rec lemma_covered_environment (depth:nat) (deps:list dependency) (e:expr)
                                  (i:interpretation value) (rho sigma:env value)
  : Lemma (requires quant_extensional i /\ covered depth deps e /\
                    (forall (n:nat). (n < depth \/ L.mem (n - depth) (dependency_indices deps)) ==>
                       rho n == sigma n))
          (ensures eval i e rho == eval i e sigma)
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App _ args -> lemma_covered_args_environment depth deps args i rho sigma
  | Quantifier _ bs _ body ->
    let aux (vs:list value{L.length vs = L.length bs})
      : Lemma (eval i body (shift vs rho) == eval i body (shift vs sigma)) =
      lemma_covered_environment (depth + L.length bs) deps body i (shift vs rho) (shift vs sigma)
    in FStar.Classical.forall_intro aux

and lemma_covered_args_environment (depth:nat) (deps:list dependency) (args:list expr)
                                   (i:interpretation value) (rho sigma:env value)
  : Lemma (requires quant_extensional i /\ covered_args depth deps args /\
                    (forall (n:nat). (n < depth \/ L.mem (n - depth) (dependency_indices deps)) ==>
                       rho n == sigma n))
          (ensures eval_args i args rho == eval_args i args sigma)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_covered_environment depth deps a i rho sigma;
    lemma_covered_args_environment depth deps rest i rho sigma

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

let rec build_interpretation (choice:hilbert_choice) (defs:list definition) (i:interpretation value)
    : Tot (interpretation value) (decreases defs) =
    match defs with
    | [] -> i
    | d :: rest -> extend choice d (build_interpretation choice rest i)

let rec lemma_coordinate_lookup (ws:list witness) (values:list value)
                                   (i:interpretation value) (vs:list value) (n:nat) (f:func_decl)
    : Lemma (requires coordinate_values ws values i vs /\ lookup n ws == Some f)
            (ensures n < L.length vs /\ f.interp == None /\ i.uninterp_app f values == L.index vs n)
            (decreases ws) =
    match ws with
    | [] -> ()
    | (m, _) :: rest ->
      if m <> n then lemma_coordinate_lookup rest values i vs n f

let rec lemma_dependency_arguments (depth:nat) (deps:list dependency)
                                     (i:interpretation value) (target rho:env value)
    : Lemma (requires forall (n:nat). target (depth + n) == rho n)
            (ensures eval_args i (dependency_arguments depth deps) target == dependency_values deps rho)
            (decreases deps) =
    match deps with
    | [] -> ()
    | _ :: rest -> lemma_dependency_arguments depth rest i target rho

let substitution_environment (depth count:nat) (vs:list value)
                               (rho source target:env value) : prop =
    L.length vs == count /\
    (forall (n:nat).
      source n == (if n < depth then target n
                   else if n < depth + count then L.index vs (n - depth)
                   else target (n - count))) /\
    (forall (n:nat). target (depth + n) == rho n)

let lemma_substitution_shift (depth count:nat) (vs inner:list value)
                                (rho source target:env value)
    : Lemma (requires substitution_environment depth count vs rho source target)
            (ensures substitution_environment (depth + L.length inner) count vs rho
                       (shift inner source) (shift inner target)) = ()

let rec lemma_substitute_sound (depth:nat) (d:definition) (e result:expr)
                                 (i:interpretation value) (vs:list value)
                                 (rho original target:env value)
    : Lemma (requires quant_extensional i /\ witness_values d i rho vs /\
                      substitution_environment depth (L.length d.bound_sorts) vs rho original target /\
                      substitute depth (L.length d.bound_sorts) d.dependencies d.witnesses e == Some result)
            (ensures eval i e original == eval i result target)
            (decreases e) =
    match e with
    | Var n _ ->
      if n >= depth && n < depth + L.length d.bound_sorts then (
        let f = Some?.v (lookup (n - depth) d.witnesses) in
        lemma_coordinate_lookup d.witnesses (dependency_values d.dependencies rho) i vs (n - depth) f;
        lemma_dependency_arguments depth d.dependencies i target rho)
    | App _ args ->
      lemma_substitute_args_sound depth d args
        (Some?.v (substitute_args depth (L.length d.bound_sorts) d.dependencies d.witnesses args))
        i vs rho original target
    | Quantifier _ bs _ body ->
      let result = Some?.v (substitute (depth + L.length bs) (L.length d.bound_sorts)
                             d.dependencies d.witnesses body) in
      let aux (inner:list value{L.length inner = L.length bs})
        : Lemma (eval i body (shift inner original) == eval i result (shift inner target)) =
        lemma_substitution_shift depth (L.length d.bound_sorts) vs inner rho original target;
        lemma_substitute_sound (depth + L.length bs) d body result i vs rho
          (shift inner original) (shift inner target)
      in FStar.Classical.forall_intro aux

and lemma_substitute_args_sound (depth:nat) (d:definition) (args results:list expr)
                                  (i:interpretation value) (vs:list value)
                                  (rho original target:env value)
    : Lemma (requires quant_extensional i /\ witness_values d i rho vs /\
                      substitution_environment depth (L.length d.bound_sorts) vs rho original target /\
                      substitute_args depth (L.length d.bound_sorts) d.dependencies d.witnesses args == Some results)
            (ensures eval_args i args original == eval_args i results target)
            (decreases args) =
    match args, results with
    | a :: rest, b :: tail ->
      lemma_substitute_sound depth d a b i vs rho original target;
      lemma_substitute_args_sound depth d rest tail i vs rho original target
    | _, _ -> ()

let rec lemma_context_member (defs:list definition) (d:definition) (i:interpretation value)
    : Lemma (requires context_model defs i /\ L.mem d defs)
            (ensures witness_model d i)
            (decreases defs) =
    match defs with
    | [] -> ()
    | e :: rest -> if e <> d then lemma_context_member rest d i

let lemma_substitute_sort (depth count:nat) (deps:list dependency)
                            (ws:list witness) (e result:expr)
    : Lemma (requires substitute depth count deps ws e == Some result)
            (ensures get_sort e == get_sort result) =
    match e with Var _ _ | App _ _ | Quantifier _ _ _ _ -> ()

let lemma_negate_truth (i:interpretation value) (rho:env value) (e:expr)
    : Lemma (requires boolean_model i /\ not_sound i /\ get_sort e == bool_sort)
            (ensures lit_true i rho (negate e) <==> ~(lit_true i rho e)) =
    match negative_body e with
    | Some a -> Q.lemma_not_truth i rho a
    | None -> Q.lemma_not_truth i rho e

let lemma_instance_truth (d:definition) (b:expr) (i:interpretation value) (rho:env value)
    : Lemma (requires valid d /\ instantiation d == Some b /\ witness_model d i /\
                      boolean_model i /\ not_sound i /\ quant_extensional i /\ Q.quantifier_model i)
            (ensures lit_true i rho (source d) <==> lit_true i rho b) =
    let target = Some?.v (substitute 0 (L.length d.bound_sorts) d.dependencies d.witnesses d.body) in
    lemma_substitute_sort 0 (L.length d.bound_sorts) d.dependencies d.witnesses d.body target;
    let q = Quantifier (if d.negative then Forall_k else Exists_k) d.bound_sorts bool_sort d.body in
    Q.lemma_quantifier_truth i rho (if d.negative then Forall_k else Exists_k) d.bound_sorts d.body;
    if d.negative then (Q.lemma_not_truth i rho q; lemma_negate_truth i rho target);
    let aux (vs:list value{L.length vs = L.length d.bound_sorts})
      : Lemma (requires witness_values d i rho vs /\
                        ((exists (ws:list value{L.length ws = L.length d.bound_sorts}).
                          assignment_goal d i rho ws) ==> assignment_goal d i rho vs))
              (ensures lit_true i rho (source d) <==> lit_true i rho b) =
      lemma_substitute_sound 0 d d.body target i vs rho (shift vs rho) rho;
      FStar.Classical.excluded_middle
        (exists (ws:list value{L.length ws = L.length d.bound_sorts}). assignment_goal d i rho ws);
      FStar.Classical.exists_intro
        (fun (ws:list value{L.length ws = L.length d.bound_sorts}) ->
          eval i d.body (shift ws rho) == eval i target rho) vs
    in
    let all (vs:list value{L.length vs = L.length d.bound_sorts})
      : Lemma (witness_values d i rho vs /\
                 ((exists (ws:list value{L.length ws = L.length d.bound_sorts}).
                    assignment_goal d i rho ws) ==> assignment_goal d i rho vs) ==>
               (lit_true i rho (source d) <==> lit_true i rho b)) =
      FStar.Classical.impl_intro
        (fun _ -> aux vs)
    in FStar.Classical.forall_intro all

(* No choice is involved. The only semantic facts are `Z3QuantifierNnf.quantifier_model`, which
   quantifies over every assignment of the block's length, and its inhabitant
   `Z3QuantifierPull.sample_values`, both already used by `Z3BinderSubstitution.lemma_eliminate`
   for unused-variable elimination. The hypotheses are those of `lemma_check_sound`. *)
let lemma_vacuous_sound (a b:expr) (i:interpretation value) (rho:env value)
    : Lemma (requires vacuous a b /\ boolean_model i /\ not_sound i /\ quant_extensional i /\
                      Q.quantifier_model i)
            (ensures observations_agree i rho a b) =
    let (negative, sorts, body, _) = Some?.v (block_parts a b) in
    let d = vacuous_definition negative sorts body in
    let n = L.length sorts in
    let lowered = Some?.v (substitute 0 n [] [] body) in
    lemma_substitute_sort 0 n [] [] body lowered;
    let kind = if negative then Forall_k else Exists_k in
    let q = Quantifier kind sorts bool_sort body in
    Q.lemma_quantifier_truth i rho kind sorts body;
    if negative then (Q.lemma_not_truth i rho q; lemma_negate_truth i rho lowered);
    let same (vs:list value{L.length vs = n})
      : Lemma (lit_true i (shift vs rho) body <==> lit_true i rho lowered) =
      lemma_substitute_sound 0 d body lowered i vs rho (shift vs rho) rho in
    FStar.Classical.forall_intro same;
    same (P.sample_values n)

let lemma_check_sound (defs:list definition) (a b:expr) (i:interpretation value) (rho:env value)
    : Lemma (requires context_model defs i /\ check defs a b /\
                      boolean_model i /\ not_sound i /\ quant_extensional i /\ Q.quantifier_model i)
            (ensures observations_agree i rho a b) =
    if vacuous a b then lemma_vacuous_sound a b i rho
    else (
      let d = Some?.v (definition_of a b) in
      lemma_context_member defs d i;
      lemma_instance_truth d b i rho)

let rec lemma_fresh_evaluation (ws:list witness) (e:expr)
                               (i j:interpretation value) (rho:env value)
  : Lemma (requires quant_extensional i /\ fresh ws e /\
                    i.interp_app == j.interp_app /\ i.interp_quant == j.interp_quant /\
                    (forall (f:func_decl{is_uninterp_decl f}) (vs:list value).
                       component f ws == None ==> i.uninterp_app f vs == j.uninterp_app f vs))
          (ensures eval i e rho == eval j e rho)
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App _ args -> lemma_fresh_args_evaluation ws args i j rho
  | Quantifier _ bs _ body ->
    let aux (vs:list value{L.length vs = L.length bs})
      : Lemma (eval i body (shift vs rho) == eval j body (shift vs rho)) =
      lemma_fresh_evaluation ws body i j (shift vs rho)
    in FStar.Classical.forall_intro aux

and lemma_fresh_args_evaluation (ws:list witness) (args:list expr)
                                (i j:interpretation value) (rho:env value)
  : Lemma (requires quant_extensional i /\ fresh_args ws args /\
                    i.interp_app == j.interp_app /\ i.interp_quant == j.interp_quant /\
                    (forall (f:func_decl{is_uninterp_decl f}) (vs:list value).
                       component f ws == None ==> i.uninterp_app f vs == j.uninterp_app f vs))
          (ensures eval_args i args rho == eval_args j args rho)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_fresh_evaluation ws a i j rho;
    lemma_fresh_args_evaluation ws rest i j rho

let rec lemma_witness_lookup (sorts:list sort) (deps:list dependency) (ws:list witness)
                             (n:nat) (f:func_decl)
  : Lemma (requires valid_witnesses sorts deps ws /\ lookup n ws == Some f)
          (ensures n < L.length sorts /\ f.interp == None /\ component f ws == Some n)
          (decreases ws) =
  match ws with
  | [] -> ()
  | (m, _) :: rest ->
    if n <> m then lemma_witness_lookup sorts deps rest n f

let lemma_assignment_environment (d:definition) (i:interpretation value)
                                 (rho:env value) (vs:list value)
  : Lemma (requires valid d /\ quant_extensional i /\ L.length vs == L.length d.bound_sorts)
          (ensures assignment_goal d i rho vs <==>
                   assignment_goal d i
                     (dependency_environment d.dependencies (dependency_values d.dependencies rho)) vs) =
  let packed = dependency_environment d.dependencies (dependency_values d.dependencies rho) in
  let aux (n:nat)
    : Lemma ((n < L.length d.bound_sorts \/
                L.mem (n - L.length d.bound_sorts) (dependency_indices d.dependencies)) ==>
               shift vs rho n == shift vs packed n) =
    if n >= L.length vs && L.mem (n - L.length vs) (dependency_indices d.dependencies)
    then lemma_dependency_environment d.dependencies rho (n - L.length vs)
  in
  FStar.Classical.forall_intro aux;
  lemma_covered_environment (L.length d.bound_sorts) d.dependencies d.body i
    (shift vs rho) (shift vs packed)

let rec lemma_extend_coordinates (choice:hilbert_choice) (d:definition) (i:interpretation value)
                                 (ws:list witness) (values:list value)
                                 (find:(n:nat -> f:func_decl ->
                                   Lemma (requires lookup n ws == Some f)
                                         (ensures lookup n d.witnesses == Some f)))
  : Lemma (requires valid d /\ valid_witnesses (L.rev d.bound_sorts) d.dependencies ws)
          (ensures coordinate_values ws values (extend choice d i) (selected choice d i values))
          (decreases ws) =
  match ws with
  | [] -> ()
  | (n, f) :: rest ->
    FStar.List.Tot.Properties.rev_length d.bound_sorts;
    find n f;
    lemma_witness_lookup (L.rev d.bound_sorts) d.dependencies d.witnesses n f;
    let find_rest (m:nat) (g:func_decl)
      : Lemma (requires lookup m rest == Some g)
              (ensures lookup m d.witnesses == Some g) =
      assert (m <> n);
      find m g in
    lemma_extend_coordinates choice d i rest values find_rest

let lemma_extend_witness (choice:hilbert_choice) (d:definition) (i:interpretation value)
  : Lemma (requires valid d /\ quant_extensional i)
          (ensures witness_model d (extend choice d i)) =
  let j = extend choice d i in
  let same (rho:env value)
    : Lemma (eval i d.body rho == eval j d.body rho) =
    lemma_fresh_evaluation d.witnesses d.body i j rho in
  FStar.Classical.forall_intro same;
  let aux (rho:env value)
    : Lemma (exists (vs:list value{L.length vs = L.length d.bound_sorts}).
        witness_values d j rho vs /\
        ((exists (ws:list value{L.length ws = L.length d.bound_sorts}).
          assignment_goal d j rho ws) ==> assignment_goal d j rho vs)) =
    let vs = selected choice d i (dependency_values d.dependencies rho) in
    let find (n:nat) (f:func_decl)
      : Lemma (requires lookup n d.witnesses == Some f)
              (ensures lookup n d.witnesses == Some f) = () in
    lemma_extend_coordinates choice d i d.witnesses (dependency_values d.dependencies rho) find;
    let goals (ws:list value{L.length ws = L.length d.bound_sorts})
      : Lemma (assignment_goal d j rho ws <==>
          assignment_goal d i
            (dependency_environment d.dependencies (dependency_values d.dependencies rho)) ws) =
      lemma_assignment_environment d i rho ws in
    FStar.Classical.forall_intro goals;
    FStar.Classical.exists_intro
      (fun (vs:list value{L.length vs = L.length d.bound_sorts}) -> witness_values d j rho vs /\
        ((exists (ws:list value{L.length ws = L.length d.bound_sorts}).
           assignment_goal d j rho ws) ==> assignment_goal d j rho vs)) vs
  in FStar.Classical.forall_intro aux

let rec lemma_coordinate_preservation (choice:hilbert_choice) (d:definition)
                                      (ws:list witness) (values vs:list value)
                                      (i:interpretation value)
  : Lemma (requires disjoint d.witnesses ws /\ coordinate_values ws values i vs)
          (ensures coordinate_values ws values (extend choice d i) vs)
          (decreases ws) =
  match ws with
  | [] -> ()
  | _ :: rest -> lemma_coordinate_preservation choice d rest values vs i

let lemma_witness_preservation (choice:hilbert_choice) (d old:definition)
                               (i:interpretation value)
  : Lemma (requires quant_extensional i /\ disjoint d.witnesses old.witnesses /\
                    fresh d.witnesses old.body /\ witness_model old i)
          (ensures witness_model old (extend choice d i)) =
  let j = extend choice d i in
  let same (rho:env value)
    : Lemma (eval i old.body rho == eval j old.body rho) =
    lemma_fresh_evaluation d.witnesses old.body i j rho in
  FStar.Classical.forall_intro same;
  let aux (rho:env value)
    : Lemma (exists (vs:list value{L.length vs = L.length old.bound_sorts}).
        witness_values old j rho vs /\
        ((exists (ws:list value{L.length ws = L.length old.bound_sorts}).
           assignment_goal old j rho ws) ==> assignment_goal old j rho vs)) =
    let transfer (vs:list value{L.length vs = L.length old.bound_sorts})
      : Lemma (witness_values old i rho vs /\
          ((exists (ws:list value{L.length ws = L.length old.bound_sorts}).
             assignment_goal old i rho ws) ==> assignment_goal old i rho vs) ==>
        witness_values old j rho vs /\
          ((exists (ws:list value{L.length ws = L.length old.bound_sorts}).
             assignment_goal old j rho ws) ==> assignment_goal old j rho vs)) =
      FStar.Classical.impl_intro
        #(witness_values old i rho vs /\
          ((exists (ws:list value{L.length ws = L.length old.bound_sorts}).
             assignment_goal old i rho ws) ==> assignment_goal old i rho vs))
        #(witness_values old j rho vs /\
          ((exists (ws:list value{L.length ws = L.length old.bound_sorts}).
             assignment_goal old j rho ws) ==> assignment_goal old j rho vs))
        (fun _ ->
        lemma_coordinate_preservation choice d old.witnesses
          (dependency_values old.dependencies rho) vs i)
    in FStar.Classical.forall_intro transfer
  in FStar.Classical.forall_intro aux

let rec lemma_context_preservation (choice:hilbert_choice) (d:definition)
                                   (defs:list definition) (i:interpretation value)
  : Lemma (requires quant_extensional i /\ safe_extension d defs /\ context_model defs i)
          (ensures context_model defs (extend choice d i))
          (decreases defs) =
  match defs with
  | [] -> ()
  | e :: rest ->
    lemma_witness_preservation choice d e i;
    lemma_context_preservation choice d rest i

let rec lemma_build_fields (choice:hilbert_choice) (defs:list definition) (i:interpretation value)
  : Lemma (ensures (build_interpretation choice defs i).interp_app == i.interp_app /\
                   (build_interpretation choice defs i).interp_quant == i.interp_quant)
          (decreases defs) =
  match defs with [] -> () | _ :: rest -> lemma_build_fields choice rest i

let lemma_quantifier_fields (i j:interpretation value)
  : Lemma (requires quant_extensional i /\ i.interp_quant == j.interp_quant)
          (ensures quant_extensional j) =
  let aux (k:quantifier_kind) (bs:list sort) (f g:list value -> value)
    : Lemma ((forall (vs:list value{L.length vs = L.length bs}). f vs == g vs) ==>
        j.interp_quant k bs f == j.interp_quant k bs g) = ()
  in FStar.Classical.forall_intro_4 aux;
  assert_norm (quant_extensional j)

let rec lemma_build_context (choice:hilbert_choice) (defs:list definition) (i:interpretation value)
  : Lemma (requires ordered_context defs /\ quant_extensional i)
          (ensures context_model defs (build_interpretation choice defs i))
          (decreases defs) =
  match defs with
  | [] -> ()
  | d :: rest ->
    lemma_build_fields choice rest i;
    lemma_build_context choice rest i;
    let older = build_interpretation choice rest i in
    lemma_quantifier_fields i older;
    lemma_extend_witness choice d older;
    lemma_context_preservation choice d rest older

let rec lemma_build_inputs (choice:hilbert_choice) (defs:list definition)
                           (inputs:list expr) (i:interpretation value) (rho:env value)
  : Lemma (requires quant_extensional i /\ fresh_inputs defs inputs)
          (ensures eval_args i inputs rho ==
                   eval_args (build_interpretation choice defs i) inputs rho)
          (decreases defs) =
  match defs with
  | [] -> ()
  | d :: rest ->
    lemma_build_fields choice rest i;
    lemma_build_inputs choice rest inputs i rho;
    let older = build_interpretation choice rest i in
    lemma_quantifier_fields i older;
    lemma_fresh_args_evaluation d.witnesses inputs older (extend choice d older) rho
