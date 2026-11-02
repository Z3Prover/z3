module Z3NativeProof
open FStar.All
open FStar.List.Tot

open Z3AstTheory
open Z3ValueTheory
open Z3UnifiedProof
open Z3ProofIndex
module N = Z3Native
module P = Z3ProofDocument
module L = FStar.List.Tot
module C = Z3LpCertificate
module BV = Z3BvLemma
module FF = Z3FiniteFieldLemma
module FP = Z3FiniteFieldPac
module DT = Z3DatatypeLemma
module CP = Z3ClauseProof
module R = Z3ResolutionProofTheory
module CG = Z3CheckedGraph
module CD = Z3DagDocument

[@@FStar.Attributes.cherry_boxed]
noeq
type state = {
  sorts: index_tree sort;
  declarations: index_tree (index_tree func_decl);
  expressions: index_tree expr;
  proofs: index_tree nat;
  lp_certificates: index_tree C.certificate;
  (* Z3 can recycle an ID after its last native owner is collected. *)
  retained_asts: list N.ast;
  retained_sorts: list N.native_sort;
  all_declarations: list func_decl;
  all_expressions: list expr;
  entries: list P.entry;
  next_proof: nat;
  clausal: bool;
  (* The opt-in mode `verified-dag-v1` only: the checked graph of binder
     certificates and their preparations (a prepared form, or why there is
     none), by entry. *)
  checked: option CD.ccache;
  companions: index_tree CD.preparation;
}

let empty_state () : state = {
  sorts = Empty; declarations = Empty; expressions = Empty; proofs = Empty;
  lp_certificates = Empty;
  retained_asts = []; retained_sorts = [];
  all_declarations = []; all_expressions = []; entries = []; next_proof = 0;
  clausal = false; checked = None; companions = Empty;
}

let require_some (#a:Type) (message:string) (x:option a) : ML a =
  match x with Some v -> v | None -> N.fail message

let map_prepend (#a:Type) (#b:Type) (f:a -> Tot b) (xs:list a) (tail:list b)
  : Tot (list b) =
  L.fold_left (fun acc x -> f x :: acc) tail (L.rev xs)

let rec marshal_sort (st:state) (s:N.native_sort) : ML (sort & state) =
  let id = N.sort_id s in
  match index_get st.sorts id with
  | Some value -> value, st
  | None ->
    let view = N.view_sort s in
    let value, st =
      match view with
      | N.Base name -> BaseSort name, st
      | N.Array domains range ->
        let domains, st = marshal_sorts st domains in
        let range, st = marshal_sort st range in
        ArraySort domains range, st
    in
    value, { st with sorts = index_put st.sorts id value;
                     retained_sorts = s :: st.retained_sorts }

and marshal_sorts (st:state) (ss:list N.native_sort) : ML (list sort & state) =
  match ss with
  | [] -> [], st
  | s :: rest ->
    let s, st = marshal_sort st s in
    let ss, st = marshal_sorts st rest in
    s :: ss, st

let operator_tag (op:N.operator) (dom:list sort) (range:sort) : option decl_kind =
  let binary_int = dom = [BaseSort "Int"; BaseSort "Int"] && range = BaseSort "Int" in
  match op with
  | N.Not -> Some op_not | N.And -> Some op_and | N.Or -> Some op_or
  | N.Implies -> Some op_implies | N.Eq -> Some op_eq | N.Oeq -> Some op_oeq
  | N.True -> Some op_true | N.False -> Some op_false | N.Ite -> Some op_ite
  | N.Xor -> Some op_xor | N.Distinct -> Some op_distinct
  | N.Select -> if L.length dom >= 2 then Some op_select else None
  | N.Store -> if L.length dom = 3 then Some op_store else None
  | N.ArrayExt -> Some op_array_ext
  | N.ConstArray -> Some op_const_array
  | N.Bvand -> Some BV.op_and | N.Bvor -> Some BV.op_or
  | N.Bvxor -> Some BV.op_xor | N.Bvnot -> Some BV.op_not
  | N.Bvadd -> Some BV.op_add | N.Bvmul -> Some BV.op_mul
  | N.Bvsub -> Some BV.op_sub | N.Bvneg -> Some BV.op_neg
  | N.Bvudiv -> Some BV.op_udiv | N.Bvurem -> Some BV.op_urem
  | N.Bvextract -> Some BV.op_extract | N.Bvconcat -> Some BV.op_concat
  | N.Bvmkbv -> Some BV.op_mkbv
  | N.Bvult -> Some BV.op_ult | N.Bvule -> Some BV.op_ule | N.Bvuge -> Some BV.op_uge
  | N.Bvshl -> Some BV.op_shl | N.Bvlshr -> Some BV.op_lshr
  | N.Bvzeroextend -> Some BV.op_zero_extend
  | N.BvNumeral -> Some BV.op_numeral
  | N.FfNum -> Some FF.op_ff_num | N.FfAdd -> Some FF.op_ff_add
  | N.FfMul -> Some FF.op_ff_mul | N.FfNeg -> Some FF.op_ff_neg
  | N.FfBitsum -> Some FF.op_ff_bitsum
  | N.DatatypeConstructor -> Some DT.op_constructor
  | N.DatatypeRecognizer -> Some DT.op_recognizer
  | N.DatatypeAccessor -> Some DT.op_accessor
  | N.Concat -> if L.length dom = 2 then Some op_concat else None
  | N.Add -> Some (if binary_int then op_plus else op_arith_add)
  | N.Mul -> Some (if binary_int then op_mul else op_arith_mul)
  | N.Sub -> Some op_arith_sub | N.Div -> Some op_arith_div
  | N.IDiv -> Some Z3IntegerDivision.op_idiv | N.Mod -> Some Z3IntegerDivision.op_mod
  | N.Le -> Some op_arith_le | N.Lt -> Some op_arith_lt
  | N.Ge -> Some op_arith_ge | N.Gt -> Some op_arith_gt
  | N.ToReal -> Some op_to_real | N.Rational -> Some op_num_rational
  | N.Opaque -> None

let marshal_declaration (st:state) (d:N.declaration) (args:list expr)
  : ML (func_decl & state) =
  let arity = L.length args in
  let cached = match index_get st.declarations d.id with Some tree -> tree | None -> Empty in
  match index_get cached arity with
  | Some value -> value, st
  | None ->
    let range, st = marshal_sort st d.range in
    let dom = map_prepend get_sort args [] in
    let parameters =
      match d.op, d.numeral with
      | N.Rational, Some (n, den) -> if den > 0 then Some [n; den] else None
      | N.Rational, None -> None
      | N.BvNumeral, Some (n, den) ->
        if den = 1 then Some (d.parameters @ [n]) else None
      | N.BvNumeral, None -> None
      | N.FfNum, Some (n, den) ->
        if den = 1 then Some (d.parameters @ [n]) else None
      | N.FfNum, None -> None
      | _, _ -> Some d.parameters
    in
    let parameters = require_some "Malformed native numeral" parameters in
    let name = if d.op = N.Opaque then d.unique_name else d.name in
    let value = { decl_name = name; domain = dom; range = range;
                  interp = operator_tag d.op dom range; int_params = parameters } in
    value, { st with declarations = index_put st.declarations d.id (index_put cached arity value);
                     all_declarations = value :: st.all_declarations }

let cached_expression (st:state) (e:N.ast) : ML expr =
  let id = N.ast_id e in
  require_some "Native expression dependency was not marshaled" (index_get st.expressions id)

let rec cached_expressions_rev (st:state) (es:list N.ast) (acc:list expr) : ML (list expr) =
  match es with
  | [] -> acc
  | e :: rest ->
    let value = cached_expression st e in
    cached_expressions_rev st rest (value :: acc)

let cached_expressions (st:state) (es:list N.ast) : ML (list expr) =
  L.rev (cached_expressions_rev st es [])

noeq
type expression_job =
  | VisitExpression : N.ast -> expression_job
  | BuildExpression : N.ast -> N.expression_view -> expression_job

let expression_children (view:N.expression_view) : list N.ast =
  match view with
  | N.Variable _ _ -> []
  | N.Application _ args -> args
  | N.Quantified _ _ body -> [body]

let rec marshal_expression_jobs (st:state) (jobs:list expression_job) : ML state =
  match jobs with
  | [] -> st
  | VisitExpression e :: rest ->
    let id = N.ast_id e in
    (match index_get st.expressions id with
     | Some _ -> marshal_expression_jobs st rest
     | None ->
       let view = N.view_expression e in
       let jobs = map_prepend (fun e -> VisitExpression e) (expression_children view)
                    (BuildExpression e view :: rest) in
       marshal_expression_jobs st jobs)
  | BuildExpression e view :: rest ->
    let value, st =
      match view with
      | N.Variable index s ->
        let s, st = marshal_sort st s in
        Var index s, st
      | N.Application d args ->
        let args = cached_expressions st args in
        let d, st = marshal_declaration st d args in
        App d args, st
      | N.Quantified kind sorts body ->
        let sorts, st = marshal_sorts st sorts in
        let body = cached_expression st body in
        Quantifier kind sorts (quant_sort kind sorts (get_sort body)) body, st
    in
    let id = N.ast_id e in
    let st = { st with expressions = index_put st.expressions id value;
                       retained_asts = e :: st.retained_asts;
                       all_expressions = value :: st.all_expressions } in
    marshal_expression_jobs st rest

let marshal_expressions (st:state) (es:list N.ast) : ML state =
  marshal_expression_jobs st (map_prepend (fun e -> VisitExpression e) es [])

(* --- The opt-in checked graph (`verified-dag-v1`) ---------------------------------------------------- *)

(* The checked graph is built only in the opt-in mode, for the conclusions and
   binder sorts of binder certificates, after the default marshaling has read
   them: a native id locates an entry of `Z3DagDocument.ccache`, which the
   checked builders earn (`ccache_ok`). A step that cannot be taken (a graph
   phase exhausted, an id the cache does not hold) stops the graph of the
   certificate being marshaled, which then has no prepared form; the stop
   keeps why, and the graph units left before that step. *)

noeq
type checked (a:Type) =
  | CheckedTo : value:a -> checked a
  | CheckedStopped : reason:CD.unprepared_reason -> prep_left:nat -> store_left:nat -> checked a

let stopped (#a:Type) (c:CD.ccache) (why:CD.unprepared_reason) : checked a =
  CheckedStopped why c.CD.graph.CG.prep c.CD.graph.CG.store

(* The cache built by a step from `c`, or why it stopped. *)
let built_from (c:CD.ccache) (r:CD.step CD.ccache) : checked CD.ccache =
  match r with
  | CD.Built c' -> CheckedTo c'
  | _ -> stopped c (CD.reason_of r)

let rec native_sort_ids (ss:list N.native_sort) (acc:list nat) : ML (list nat) =
  match ss with
  | [] -> L.rev acc
  | s :: rest -> let i = N.sort_id s in native_sort_ids rest (i :: acc)

let rec native_ast_ids (es:list N.ast) (acc:list nat) : ML (list nat) =
  match es with
  | [] -> L.rev acc
  | e :: rest -> let i = N.ast_id e in native_ast_ids rest (i :: acc)

(* Sorts are visited on an explicit worklist (a self tail call), so nesting
   needs no native stack: an array sort's domains and range first, then the
   array sort itself. *)
noeq
type sort_job =
  | SortVisit : N.native_sort -> sort_job
  | SortBuild : nat -> list N.native_sort -> N.native_sort -> sort_job

let rec checked_sort_jobs (c:CD.ccache) (jobs:list sort_job) : ML (checked CD.ccache) =
  match jobs with
  | [] -> CheckedTo c
  | SortVisit s :: rest ->
    let nid = N.sort_id s in
    (match CD.find_sort c nid with
     | CD.Found c' _ -> checked_sort_jobs c' rest
     | CD.LookupExhausted -> stopped c CD.lookup_exhausted
     | CD.Missing c' ->
       (match N.view_sort s with
        | N.Base name ->
          (match built_from c' (CD.build_base_sort c' nid name) with
           | CheckedTo c'' -> checked_sort_jobs c'' rest
           | stop -> stop)
        | N.Array domains range ->
          checked_sort_jobs c'
            (map_prepend (fun s -> SortVisit s) domains (SortVisit range :: SortBuild nid domains range :: rest))))
  | SortBuild nid domains range :: rest ->
    let ds = native_sort_ids domains [] in
    let r = N.sort_id range in
    (match built_from c (CD.build_array_sort c nid ds r) with
     | CheckedTo c' -> checked_sort_jobs c' rest
     | stop -> stop)

let checked_sorts (c:CD.ccache) (ss:list N.native_sort) : ML (checked CD.ccache) =
  checked_sort_jobs c (map_prepend (fun s -> SortVisit s) ss [])

noeq
type checked_job =
  | CheckVisit : N.ast -> checked_job
  | CheckBuild : N.ast -> N.expression_view -> checked_job

let checked_build (st:state) (c:CD.ccache) (e:N.ast) (view:N.expression_view) : ML (checked CD.ccache) =
  let nid = N.ast_id e in
  match view with
  | N.Variable index s ->
    (match checked_sorts c [s] with
     | CheckedTo c1 -> let sid = N.sort_id s in built_from c1 (CD.build_var c1 nid index sid)
     | stop -> stop)
  | N.Application d args ->
    (match checked_sorts c [d.range] with
     | CheckedTo c1 ->
       let arity = L.length args in
       let cached = match index_get st.declarations d.id with Some tree -> index_get tree arity | None -> None in
       (match cached with
        | Some fd ->
          let xs = native_ast_ids args [] in
          let r = N.sort_id d.range in
          built_from c1 (CD.build_app c1 nid d.id fd.decl_name fd.interp fd.int_params xs r)
        | None -> stopped c1 (CD.UnpreparedInvalid CD.MissingDeclaration))
     | stop -> stop)
  | N.Quantified kind sorts body ->
    (match checked_sorts c sorts with
     | CheckedTo c1 ->
       let ss = native_sort_ids sorts [] in
       let b = N.ast_id body in
       built_from c1 (CD.build_quant c1 nid kind ss b)
     | stop -> stop)

let rec checked_expression_jobs (st:state) (c:CD.ccache) (jobs:list checked_job) : ML (checked CD.ccache) =
  match jobs with
  | [] -> CheckedTo c
  | CheckVisit e :: rest ->
    let nid = N.ast_id e in
    (match CD.find_expr c nid with
     | CD.Found c' _ -> checked_expression_jobs st c' rest
     | CD.LookupExhausted -> stopped c CD.lookup_exhausted
     | CD.Missing c' ->
       let view = N.view_expression e in
       let children = expression_children view in
       let n = L.length children in
       (match built_from c' (CD.spend c' (1 + n) (1 + n)) with
        | CheckedTo c'' ->
          checked_expression_jobs st c''
            (map_prepend (fun e -> CheckVisit e) children (CheckBuild e view :: rest))
        | stop -> stop))
  | CheckBuild e view :: rest ->
    (match checked_build st c e view with
     | CheckedTo c' -> checked_expression_jobs st c' rest
     | stop -> stop)

(* The graph of a binder entry: its conclusion and its binder sorts, and the
   entry as `Z3DagDocument.prepare_certificate` reads it. *)
let checked_entry (st:state) (c:CD.ccache) (conclusion:N.ast) (sorts:option (list N.native_sort))
                  (name:string) (premises:list int) : ML (checked (CD.ccache & CD.raw_entry)) =
  match checked_expression_jobs st c [CheckVisit conclusion] with
  | CheckedStopped why p s -> CheckedStopped why p s
  | CheckedTo c1 ->
    let f = N.ast_id conclusion in
    (match sorts with
     | None ->
       CheckedTo (c1, { CD.raw_name = name; CD.raw_formula = f; CD.raw_premises = premises; CD.raw_sorts = None })
     | Some ss ->
       (match checked_sorts c1 ss with
        | CheckedTo c2 ->
          let ids = native_sort_ids ss [] in
          CheckedTo (c2, { CD.raw_name = name; CD.raw_formula = f; CD.raw_premises = premises; CD.raw_sorts = Some ids })
        | CheckedStopped why p s -> CheckedStopped why p s))

(* A binder entry as the default marshaling read it, for the checked graph. *)
noeq
type native_entry = {
  native_conclusion: N.ast;
  native_sorts: option (list N.native_sort);
  native_name: string;
  native_premises: list int;
}

let rec checked_entries (st:state) (c:CD.ccache) (es:list native_entry) (acc:list CD.raw_entry)
  : ML (checked (CD.ccache & list CD.raw_entry)) =
  match es with
  | [] -> CheckedTo (c, L.rev acc)
  | e :: rest ->
    (match checked_entry st c e.native_conclusion e.native_sorts e.native_name e.native_premises with
     | CheckedTo (c', r) -> checked_entries st c' rest (r :: acc)
     | CheckedStopped why p s -> CheckedStopped why p s)


let rec parameter_expressions (ps:list N.parameter_view) : Tot (list N.ast) (decreases ps) =
  match ps with
  | [] -> []
  | N.ParameterExpression e :: rest -> e :: parameter_expressions rest
  | _ :: rest -> parameter_expressions rest

let rec marshal_parameters (st:state) (ps:list N.parameter_view) : ML (list C.raw_parameter) =
  match ps with
  | [] -> []
  | p :: rest ->
    let value =
      match p with
      | N.ParameterRational n d -> C.Rational n d
      | N.ParameterExpression e -> C.Expression (cached_expression st e)
      | N.ParameterUnsupported -> C.Unsupported
    in
    let values = marshal_parameters st rest in
    value :: values

let coefficient ((n, den):(int & int)) : option Z3LinearArithmeticAst.coefficient =
  if den > 0 then Some (n, den) else None

let native_rule (view:N.proof_view) (formula:expr) : ML rule =
  match view.assumed, view.farkas with
  | Some origin, _ -> Unverified ("assumed:" ^ origin)
  | None, Some coefficients ->
    if view.proof_name <> "th-lemma" then N.fail "Farkas parameters on a non-theory node"
    else
      let coefficients = require_some "Malformed native Farkas certificate"
                                      (opt_map_tail coefficient coefficients) in
      ArithmeticFarkas coefficients
  | None, None ->
    match P.rule_of_name view.proof_name with
    | None -> Unverified view.proof_name
    | Some Commutativity ->
      (match classify_fact formula with
       | Some (Equal a b) ->
         if Z3Commutativity.commutativity_step a b then Commutativity else Unverified view.proof_name
       | _ -> Unverified view.proof_name)
    | Some rule -> rule

(* The premises and coefficients of a recorded finite-field certificate are
   ordinary expressions; its node list may be long, so it is walked tail
   recursively. *)
let rec marshal_coefficients (st:state) (ns:list N.ff_pac_node) : ML state =
  match ns with
  | [] -> st
  | N.PacMul _ c _ :: rest -> marshal_coefficients (marshal_expressions st [c]) rest
  | _ :: rest -> marshal_coefficients st rest

let marshal_ff_pac (st:state) (c:option N.ff_pac_view) : ML state =
  match c with
  | None -> st
  | Some c -> marshal_coefficients (marshal_expressions st c.N.pac_premises) c.N.pac_nodes

let rec ff_pac_nodes (st:state) (ns:list N.ff_pac_node) (acc:list FP.pac_node)
  : ML (list FP.pac_node) =
  match ns with
  | [] -> L.rev acc
  | n :: rest ->
    let node =
      match n with
      | N.PacInput i -> FP.PacInput i
      | N.PacAdd a b -> FP.PacAdd a b
      | N.PacMul s c f -> FP.PacMul s (cached_expression st c) f in
    ff_pac_nodes st rest (node :: acc)

let ff_certificate (st:state) (c:N.ff_pac_view) : ML FP.certificate =
  let premises = cached_expressions st c.N.pac_premises in
  let nodes = ff_pac_nodes st c.N.pac_nodes [] in
  { FP.pac_premises = premises; FP.pac_nodes = nodes;
    FP.pac_root = c.N.pac_root; FP.pac_support = c.N.pac_support }

let rec cached_premises (st:state) (ps:list N.ast) : ML (list int) =
  match ps with
  | [] -> []
  | p :: rest ->
    let id = N.ast_id p in
    let index = require_some "Native proof dependency was not marshaled" (index_get st.proofs id) in
    let indices = cached_premises st rest in
    index :: indices

noeq
type binder_job =
  | VisitBinder : N.ast -> binder_job
  | BuildBinder : N.ast -> N.proof_view -> list N.ast ->
                  option (list N.native_sort) -> binder_job

let binder_rule (name:string) : bool =
  name = "quant-intro" || name = "nnf-pos" || name = "nnf-neg"

let binder_dependencies (view:N.proof_view)
  : ML (list N.ast & option (list N.native_sort)) =
  if binder_rule view.proof_name then
    match view.premises with
    | [p] ->
      let bound = N.view_proof p in
      (match bound.binding with
       | Some (sorts, body) -> [body], Some sorts
       | None -> view.premises, None)
    | _ -> view.premises, None
  else view.premises, None

let rec cached_binder_premises (cache:index_tree nat) (children:list N.ast) : ML (list int) =
  match children with
  | [] -> []
  | p :: rest ->
    let id = N.ast_id p in
    let index = require_some "Native binder proof dependency was not marshaled"
                             (index_get cache id) in
    let indices = cached_binder_premises cache rest in
    index :: indices

let rec marshal_binder_jobs (st:state) (cache:index_tree nat)
                           (entries:list binder_entry) (next:nat) (jobs:list binder_job)
                           (raw:list native_entry)
  : ML (state & index_tree nat & list binder_entry & list native_entry) =
  match jobs with
  | [] -> st, cache, L.rev entries, raw
  | VisitBinder p :: rest ->
    (match index_get cache (N.ast_id p) with
     | Some _ -> marshal_binder_jobs st cache entries next rest raw
     | None ->
       let view = N.view_proof p in
       let children, sorts = binder_dependencies view in
       let jobs = map_prepend (fun p -> VisitBinder p) children
                    (BuildBinder p view children sorts :: rest) in
       marshal_binder_jobs st cache entries next jobs raw)
  | BuildBinder p view children native_sorts :: rest ->
    let st = marshal_expressions st [view.conclusion] in
    let sorts, st =
      match native_sorts with
      | None -> None, st
      | Some sorts ->
        let sorts, st = marshal_sorts st sorts in Some sorts, st in
    let premises = cached_binder_premises cache children in
    let name = match view.assumed with
               | Some origin -> "assumed:" ^ origin | None -> view.proof_name in
    let entry = {
      binder_name = name; binder_formula = cached_expression st view.conclusion;
      binder_premises = premises; binder_sorts = sorts;
    } in
    let st = { st with retained_asts = p :: st.retained_asts } in
    let raw =
      if Some? st.checked
      then { native_conclusion = view.conclusion; native_sorts = native_sorts; native_name = name;
             native_premises = premises } :: raw
      else raw in
    marshal_binder_jobs st (index_put cache (N.ast_id p) next)
                       (entry :: entries) (next + 1) rest raw

(* In the opt-in mode the certificate is prepared on the checked graph after
   its entries are marshaled: the graph's allowance is the certificate's,
   `n + 1` shares for `n` entries (`Z3DagDocument.graph_*_per_entry`), then
   `Z3DagDocument.prepare_certificate`; the document holds the prepared
   certificate. A certificate that cannot be prepared is the default one; its
   preparation records why, with the graph units (preparation, storage) that
   the steps before the one that stopped used of the allowance. *)
let marshal_binder (st:state) (p:N.ast) : ML (binder_certificate & state & option CD.preparation) =
  let st, cache, entries, raw = marshal_binder_jobs st Empty [] 0 [VisitBinder p] [] in
  let root = require_some "Native binder proof root was not marshaled"
                         (index_get cache (N.ast_id p)) in
  let certificate = { binder_entries = entries; binder_root = root } in
  match st.checked with
  | None -> certificate, st, None
  | Some c ->
    let shares = L.length entries + 1 in
    let gp = CD.graph_preparation_per_entry * shares in
    let gs = CD.graph_storage_per_entry * shares in
    let c = CD.with_budget c gp gs in
    let unready (why:CD.unprepared_reason) (pl sl:nat) : CD.preparation =
      CD.Unready why (Some ((if pl <= gp then gp - pl else 0), (if sl <= gs then gs - sl else 0))) in
    (match checked_entries st c (L.rev raw) [] with
     | CheckedStopped why pl sl -> certificate, st, Some (unready why pl sl)
     | CheckedTo (c1, rs) ->
       (match CD.prepare_certificate c1 rs root with
        | CD.Built (c', prepared) -> prepared.CD.pcert, { st with checked = Some c' }, Some (CD.Ready prepared)
        | r -> certificate, st,
              Some (unready (CD.reason_of r) c1.CD.graph.CG.prep c1.CD.graph.CG.store)))

let clause_builder (st:state) : CP.builder =
  { CP.entries = st.entries; CP.next = st.next_proof }

let with_clause_builder (st:state) (b:CP.builder) : state =
  { st with entries = b.CP.entries; next_proof = b.CP.next }

let application_declaration (e:expr) : ML func_decl =
  match e with
  | App d _ -> d
  | _ -> N.fail "Expected a logical application"

let clause_literal (st:state) (e:N.ast) : ML CP.literal =
  let atom, negative =
    match N.view_expression e with
    | N.Application d [a] -> if d.op = N.Not then a, true else e, false
    | _ -> e, false in
  let formula = cached_expression st atom in
  let id = if formula = R.true_expr then 0
           else if formula = R.false_expr then 1 else N.ast_id atom + 2 in
  { CP.atom = id; CP.negative = negative; CP.formula = cached_expression st e }

let rec clause_literals (st:state) (es:list N.ast) : ML (list CP.literal) =
  match es with
  | [] -> []
  | e :: rest ->
    let literal = clause_literal st e in
    let literals = clause_literals st rest in
    literal :: literals

let add_clause_entry (st:state) (db:CP.database) (view:N.clause_view)
  : ML (state & CP.database) =
  let st = marshal_expressions st [view.formula] in
  let formula = cached_expression st view.formula in
  let literals = clause_literals st view.literals in
  if view.action = N.DeleteClause then st, CP.delete db literals
  else
    let id, b, db =
      match view.certificate with
      | Some certificate ->
        let proof_view = N.view_proof certificate in
        if cached_expression st proof_view.conclusion <> formula then
          N.fail "Clause certificate conclusion does not match its clause"
        else
          let id = require_some "Clause certificate was not marshaled"
                                (index_get st.proofs (N.ast_id certificate)) in
          id, clause_builder st, db
      | None ->
        (match view.action with
         | N.InputClause ->
           let id, b = CP.emit (clause_builder st) Asserted formula [] in id, b, db
         | N.TheoryClause ->
           let id, b = CP.emit (clause_builder st) (Unverified "th-lemma") formula [] in id, b, db
         | N.LearnedClause ->
           require_some "Clause proof failed reverse unit propagation"
             (CP.prove_cached db (clause_builder st) literals formula)
         | N.DeleteClause -> N.fail "Unexpected clause deletion") in
    with_clause_builder st b,
    CP.add db { CP.literals = literals; CP.formula = formula; CP.proof_id = id }

noeq
type proof_job =
  | VisitProof : N.ast -> proof_job
  | BuildProof : N.ast -> N.proof_view -> proof_job
  | VisitClauseTrail : N.ast -> list N.clause_view -> N.ast -> CP.database -> proof_job
  | BuildClauseEntry : N.ast -> N.clause_view -> list N.clause_view ->
                       N.ast -> CP.database -> proof_job

let rec marshal_proof_jobs (st:state) (jobs:list proof_job) : ML state =
  match jobs with
  | [] -> st
  | VisitProof p :: rest ->
    let id = N.ast_id p in
    (match index_get st.proofs id with
     | Some _ -> marshal_proof_jobs st rest
     | None ->
       (match N.view_clause_trail p with
        | Some (entries, conclusion) ->
          let db, b = CP.empty (clause_builder st) in
          let st = { (with_clause_builder st b) with clausal = true } in
          marshal_proof_jobs st (VisitClauseTrail p entries conclusion db :: rest)
        | None ->
          let view = N.view_proof p in
          let jobs = if binder_rule view.proof_name then BuildProof p view :: rest
                     else map_prepend (fun p -> VisitProof p) view.premises
                            (BuildProof p view :: rest) in
          marshal_proof_jobs st jobs))
  | VisitClauseTrail root [] conclusion db :: rest ->
    let st = marshal_expressions st [conclusion] in
    if cached_expression st conclusion <> R.false_expr then
      N.fail "Clause proof trail is not a refutation"
    else
      let id, b = require_some "Clause proof trail does not derive the empty clause"
                   (CP.prove db (clause_builder st) [] R.false_expr) in
      let st = with_clause_builder st b in
      let st = { st with proofs = index_put st.proofs (N.ast_id root) id;
                         retained_asts = root :: st.retained_asts } in
      marshal_proof_jobs st rest
  | VisitClauseTrail root (entry :: entries) conclusion db :: rest ->
    let build = BuildClauseEntry root entry entries conclusion db in
    let jobs = match entry.certificate with
      | Some certificate -> VisitProof certificate :: build :: rest
      | None -> build :: rest in
    marshal_proof_jobs st jobs
  | BuildClauseEntry root entry entries conclusion db :: rest ->
    let st, db = add_clause_entry st db entry in
    marshal_proof_jobs st (VisitClauseTrail root entries conclusion db :: rest)
  | BuildProof p view :: rest ->
    let parameters = match view.lp_data with Some (_, ps) -> ps | None -> [] in
    let st = marshal_expressions st
      (view.conclusion :: (view.instantiations @ parameter_expressions parameters)) in
    let st = marshal_ff_pac st view.ff_pac in
    let st =
      match view.lp_data with
      | Some ("lp-context", ps) ->
        let certificate = require_some "Malformed native LP certificate"
                            (C.decode (marshal_parameters st ps)) in
        { st with lp_certificates = index_put st.lp_certificates (N.ast_id p) certificate }
      | _ -> st
    in
    let formula = cached_expression st view.conclusion in
    let rule, premises, st =
      if binder_rule view.proof_name then
        let certificate, st, prepared = marshal_binder st p in
        let st = match prepared with
          | Some pc -> { st with companions = index_put st.companions st.next_proof pc }
          | None -> st in
        QuantifierIntroduction certificate, [], st
      else if view.proof_name = "quant-inst" then
        QuantifierInstantiation (cached_expressions st view.instantiations),
        cached_premises st view.premises, st
      else if view.proof_name = "arith/lp-gomory" then
        let candidate =
          match view.lp_data, view.premises with
          | Some ("lp-gomory", [N.ParameterRational index denominator]), context :: _ ->
            if denominator = 1 && index >= 0 then
              index_get st.lp_certificates (N.ast_id context) >>= (fun certificate ->
              Z3LpGomory.candidate certificate index)
            else None
          | _, _ -> None in
        let kind = match candidate with
          | Some c -> ArithmeticGomory c
          | None -> Unverified view.proof_name in
        kind, cached_premises st view.premises, st
      else
        (match view.ff_pac with
         | Some c -> FiniteFieldPac (ff_certificate st c)
         | None -> native_rule view formula), cached_premises st view.premises, st in
    let entry = { P.rule = rule; P.formula = formula; P.premise_ids = premises } in
    let id = N.ast_id p in
    let st = { st with proofs = index_put st.proofs id st.next_proof;
                       retained_asts = p :: st.retained_asts;
                       entries = entry :: st.entries; next_proof = st.next_proof + 1 } in
    marshal_proof_jobs st rest

let marshal_state_using (checked:bool) (assertions:list N.ast) (proof:N.ast) : ML (P.document & state) =
  let st0 = empty_state () in
  let st0 = if checked then { st0 with checked = Some CD.empty_cache } else st0 in
  let st = marshal_expressions st0 assertions in
  let inputs = cached_expressions st assertions in
  let st = marshal_proof_jobs st [VisitProof proof] in
  let id = N.ast_id proof in
  let root = require_some "Native proof root was not marshaled" (index_get st.proofs id) in
  let entries, root =
    if st.clausal then
      require_some "Malformed elaborated clause proof DAG" (CP.prune (clause_builder st) root)
    else L.rev st.entries, root in
  let declarations =
    if st.clausal then
      let truth = application_declaration R.true_expr in
      let falsehood = application_declaration R.false_expr in
      let negation = application_declaration (R.mk_not_expr R.false_expr) in
      L.fold_left (fun ds d -> if L.mem d ds then ds else d :: ds)
        st.all_declarations [truth; falsehood; negation]
    else st.all_declarations in
  let expressions =
    if st.clausal then L.fold_left (fun es e -> e.P.formula :: es) st.all_expressions entries
    else st.all_expressions in
  { P.declarations = declarations; P.expressions = expressions;
    P.assertions = inputs; P.entries = entries; P.root = root }, st

let marshal_state (assertions:list N.ast) (proof:N.ast) : ML (P.document & state) =
  marshal_state_using false assertions proof

let marshal (assertions:list N.ast) (proof:N.ast) : ML P.document =
  let doc, _ = marshal_state assertions proof in doc

let marshal_with_datatypes (assertions:list N.ast) (proof:N.ast)
  : ML (P.document & Z3DatatypeSignature.schema) =
  let doc, st = marshal_state assertions proof in
  let schema = N.view_datatypes st.retained_sorts in
  doc, schema

(* The opt-in mode `verified-dag-v1`: the document, its datatypes and the
   preparations of its quantifier introductions, by entry. A clausal
   document's entries are renumbered when it is pruned, so it has none: every
   quantifier introduction of it is unprepared, as clausal. *)
let marshal_with_datatypes_dag (assertions:list N.ast) (proof:N.ast)
  : ML (P.document & Z3DatatypeSignature.schema & CD.companions) =
  let doc, st = marshal_state_using true assertions proof in
  let schema = N.view_datatypes st.retained_sorts in
  doc, schema, { CD.clausal = st.clausal; CD.preparations = (if st.clausal then Empty else st.companions) }
