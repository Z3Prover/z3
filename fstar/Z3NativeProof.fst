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

noeq
type state = {
  sorts: index_tree sort;
  declarations: index_tree (index_tree func_decl);
  expressions: index_tree expr;
  proofs: index_tree nat;
  (* Z3 can recycle an ID after its last native owner is collected. *)
  retained_asts: list N.ast;
  retained_sorts: list N.native_sort;
  all_declarations: list func_decl;
  all_expressions: list expr;
  entries: list P.entry;
  next_proof: nat;
}

let empty_state () : state = {
  sorts = Empty; declarations = Empty; expressions = Empty; proofs = Empty;
  retained_asts = []; retained_sorts = [];
  all_declarations = []; all_expressions = []; entries = []; next_proof = 0;
}

let require_some (#a:Type) (message:string) (x:option a) : ML a =
  match x with Some v -> v | None -> N.fail message

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
  | N.Select -> if L.length dom = 2 then Some op_select else None
  | N.Store -> if L.length dom = 3 then Some op_store else None
  | N.ArrayExt -> Some op_array_ext
  | N.Bvand -> if L.length dom = 2 then Some op_bvand else None
  | N.Concat -> if L.length dom = 2 then Some op_concat else None
  | N.Add -> Some (if binary_int then op_plus else op_arith_add)
  | N.Mul -> Some (if binary_int then op_mul else op_arith_mul)
  | N.Sub -> Some op_arith_sub | N.Div -> Some op_arith_div
  | N.Le -> Some op_arith_le | N.Lt -> Some op_arith_lt
  | N.Ge -> Some op_arith_ge | N.Gt -> Some op_arith_gt
  | N.ToReal -> Some op_to_real | N.Rational -> Some op_num_rational
  | N.BvNumeral | N.Opaque -> None

let marshal_declaration (st:state) (d:N.declaration) (args:list expr)
  : ML (func_decl & state) =
  let arity = L.length args in
  let cached = match index_get st.declarations d.id with Some tree -> tree | None -> Empty in
  match index_get cached arity with
  | Some value -> value, st
  | None ->
    let range, st = marshal_sort st d.range in
    let dom = L.map get_sort args in
    let parameters =
      match d.op, d.numeral with
      | N.Rational, Some (n, den) -> if den > 0 then Some [n; den] else None
      | N.Rational, None -> None
      | N.BvNumeral, _ -> Some [d.native_kind]
      | _, _ -> Some []
    in
    let parameters = require_some "Malformed native rational numeral" parameters in
    let name = if d.op = N.Opaque then d.unique_name else d.name in
    let value = { decl_name = name; domain = dom; range = range;
                  interp = operator_tag d.op dom range; int_params = parameters } in
    value, { st with declarations = index_put st.declarations d.id (index_put cached arity value);
                     all_declarations = value :: st.all_declarations }

let cached_expression (st:state) (e:N.ast) : ML expr =
  let id = N.ast_id e in
  require_some "Native expression dependency was not marshaled" (index_get st.expressions id)

let rec cached_expressions (st:state) (es:list N.ast) : ML (list expr) =
  match es with
  | [] -> []
  | e :: rest ->
    let value = cached_expression st e in
    let values = cached_expressions st rest in
    value :: values

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
       let children = L.map (fun e -> VisitExpression e) (expression_children view) in
       marshal_expression_jobs st (children @ (BuildExpression e view :: rest)))
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
  marshal_expression_jobs st (L.map (fun e -> VisitExpression e) es)

let coefficient ((n, den):(int & int)) : option Z3LinearArithmeticAst.coefficient =
  if den > 0 then Some (n, den) else None

let native_rule (view:N.proof_view) (formula:expr) : ML rule =
  match view.assumed, view.farkas with
  | Some origin, _ -> Unverified ("assumed:" ^ origin)
  | None, Some coefficients ->
    if view.proof_name <> "th-lemma" then N.fail "Farkas parameters on a non-theory node"
    else
      let coefficients = require_some "Malformed native Farkas certificate"
                                      (opt_map coefficient coefficients) in
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

let rec cached_premises (st:state) (ps:list N.ast) : ML (list int) =
  match ps with
  | [] -> []
  | p :: rest ->
    let id = N.ast_id p in
    let index = require_some "Native proof dependency was not marshaled" (index_get st.proofs id) in
    let indices = cached_premises st rest in
    index :: indices

noeq
type proof_job =
  | VisitProof : N.ast -> proof_job
  | BuildProof : N.ast -> N.proof_view -> proof_job

let rec marshal_proof_jobs (st:state) (jobs:list proof_job) : ML state =
  match jobs with
  | [] -> st
  | VisitProof p :: rest ->
    let id = N.ast_id p in
    (match index_get st.proofs id with
     | Some _ -> marshal_proof_jobs st rest
     | None ->
       let view = N.view_proof p in
       let children = L.map (fun p -> VisitProof p) view.premises in
       marshal_proof_jobs st (children @ (BuildProof p view :: rest)))
  | BuildProof p view :: rest ->
    let st = marshal_expressions st [view.conclusion] in
    let formula = cached_expression st view.conclusion in
    let rule = native_rule view formula in
    let premises = cached_premises st view.premises in
    let entry = { P.rule = rule; P.formula = formula; P.premise_ids = premises } in
    let id = N.ast_id p in
    let st = { st with proofs = index_put st.proofs id st.next_proof;
                       retained_asts = p :: st.retained_asts;
                       entries = entry :: st.entries; next_proof = st.next_proof + 1 } in
    marshal_proof_jobs st rest

let marshal (assertions:list N.ast) (proof:N.ast) : ML P.document =
  let st = marshal_expressions (empty_state ()) assertions in
  let inputs = cached_expressions st assertions in
  let st = marshal_proof_jobs st [VisitProof proof] in
  let id = N.ast_id proof in
  let root = require_some "Native proof root was not marshaled" (index_get st.proofs id) in
  { P.declarations = st.all_declarations; P.expressions = st.all_expressions;
    P.assertions = inputs; P.entries = L.rev st.entries; P.root = root }
