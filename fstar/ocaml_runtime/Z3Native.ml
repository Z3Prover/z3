type ast = Z3native.ast
type native_sort = Z3native.sort

type operator =
  | Not | And | Or | Implies | Eq | Oeq | True | False | Ite | Xor | Distinct
  | Select | Store | ArrayExt | ConstArray | Bvand | Bvor | Bvxor | Bvnot
  | Bvadd | Bvmul | Bvsub | Bvneg | Bvudiv | Bvurem | Bvextract | Bvconcat | Bvmkbv
  | Bvult | Bvule | Bvuge | Bvshl | Bvlshr | Concat
  | DatatypeConstructor | DatatypeRecognizer | DatatypeAccessor
  | Add | Mul | Sub | Div | IDiv | Mod | Le | Lt | Ge | Gt | ToReal
  | Rational | BvNumeral | Bvzeroextend | Opaque

type sort_view =
  | Base of string
  | Array of native_sort list * native_sort

type declaration = {
  id: Z.t;
  name: string;
  unique_name: string;
  op: operator;
  range: native_sort;
  numeral: (Z.t * Z.t) option;
  native_kind: Z.t;
  parameters: Z.t list;
}

type expression_view =
  | Variable of Z.t * native_sort
  | Application of declaration * ast list
  | Quantified of Z3AstTheory.quantifier_kind * native_sort list * ast

type parameter_view =
  | ParameterRational of Z.t * Z.t
  | ParameterExpression of ast
  | ParameterUnsupported

type proof_view = {
  proof_name: string;
  premises: ast list;
  conclusion: ast;
  farkas: (Z.t * Z.t) list option;
  assumed: string option;
  lp_data: (string * parameter_view list) option;
  binding: (native_sort list * ast) option;
  instantiations: ast list;
}

type clause_action = InputClause | LearnedClause | TheoryClause | DeleteClause

type clause_view = {
  action: clause_action;
  formula: ast;
  literals: ast list;
  certificate: ast option;
}

type solve_result =
  | Unsat of ast list * ast
  | Sat
  | Unknown of string

exception Error of string

let fail message = raise (Error message)
let ctx = Z3native.context_of_ast
let ast_id a = Z.of_int (Z3native.get_ast_id (ctx a) a)
let sort_id s = Z.of_int (Z3native.get_sort_id (ctx s) s)
let symbol c s =
  match Z3enums.symbol_kind_of_int (Z3native.get_symbol_kind c s) with
  | Z3enums.INT_SYMBOL -> string_of_int (Z3native.get_symbol_int c s)
  | Z3enums.STRING_SYMBOL -> Z3native.get_symbol_string c s

let unique prefix id name = Printf.sprintf "%s!%s:%s" prefix (Z.to_string id) name

let view_sort s =
  let c = ctx s in
  let kind = Z3enums.sort_kind_of_int (Z3native.get_sort_kind c s) in
  let name = symbol c (Z3native.get_sort_name c s) in
  match kind with
  | Z3enums.BOOL_SORT -> Base "Bool"
  | Z3enums.INT_SORT -> Base "Int"
  | Z3enums.REAL_SORT -> Base "Real"
  | Z3enums.BV_SORT -> Base (Printf.sprintf "BV%d" (Z3native.get_bv_sort_size c s))
  | Z3enums.SEQ_SORT
      when Z3enums.sort_kind_of_int
             (Z3native.get_sort_kind c (Z3native.get_seq_sort_basis c s)) = Z3enums.INT_SORT ->
      Base "SeqInt"
  | Z3enums.ARRAY_SORT ->
      let domains = List.init (Z3native.get_array_arity c s)
          (Z3native.get_array_sort_domain_n c s) in
      Array (domains, Z3native.get_array_sort_range c s)
  | _ -> Base (unique "sort" (sort_id s) name)

let operator = function
  | Z3enums.OP_NOT -> Not | Z3enums.OP_AND -> And | Z3enums.OP_OR -> Or
  | Z3enums.OP_IMPLIES -> Implies | Z3enums.OP_EQ -> Eq | Z3enums.OP_OEQ -> Oeq
  | Z3enums.OP_TRUE -> True | Z3enums.OP_FALSE -> False | Z3enums.OP_ITE -> Ite
  | Z3enums.OP_XOR -> Xor | Z3enums.OP_DISTINCT -> Distinct
  | Z3enums.OP_SELECT -> Select | Z3enums.OP_STORE -> Store
  | Z3enums.OP_ARRAY_EXT -> ArrayExt | Z3enums.OP_BAND -> Bvand
  | Z3enums.OP_BOR -> Bvor | Z3enums.OP_BXOR -> Bvxor | Z3enums.OP_BNOT -> Bvnot
  | Z3enums.OP_BADD -> Bvadd | Z3enums.OP_BMUL -> Bvmul
  | Z3enums.OP_BSUB -> Bvsub | Z3enums.OP_BNEG -> Bvneg
  | Z3enums.OP_BUDIV -> Bvudiv | Z3enums.OP_BUREM -> Bvurem
  | Z3enums.OP_EXTRACT -> Bvextract | Z3enums.OP_CONCAT -> Bvconcat
  | Z3enums.OP_ZERO_EXT -> Bvzeroextend
  | Z3enums.OP_MKBV -> Bvmkbv
  | Z3enums.OP_ULT -> Bvult | Z3enums.OP_ULEQ -> Bvule | Z3enums.OP_UGEQ -> Bvuge
  | Z3enums.OP_BSHL -> Bvshl | Z3enums.OP_BLSHR -> Bvlshr
  | Z3enums.OP_CONST_ARRAY -> ConstArray
  | Z3enums.OP_DT_CONSTRUCTOR -> DatatypeConstructor
  | Z3enums.OP_DT_RECOGNISER | Z3enums.OP_DT_IS -> DatatypeRecognizer
  | Z3enums.OP_DT_ACCESSOR -> DatatypeAccessor
  | Z3enums.OP_SEQ_CONCAT -> Concat | Z3enums.OP_ADD -> Add | Z3enums.OP_MUL -> Mul
  | Z3enums.OP_SUB | Z3enums.OP_UMINUS -> Sub
  | Z3enums.OP_DIV -> Div | Z3enums.OP_IDIV -> IDiv | Z3enums.OP_MOD -> Mod
  | Z3enums.OP_LE -> Le | Z3enums.OP_LT -> Lt
  | Z3enums.OP_GE -> Ge | Z3enums.OP_GT -> Gt | Z3enums.OP_TO_REAL -> ToReal
  | Z3enums.OP_ANUM -> Rational | Z3enums.OP_BNUM -> BvNumeral
  | _ -> Opaque

let rational text =
  try
    let q = Q.of_string text in
    if Z.sign (Q.den q) <= 0 then fail ("Invalid native rational: " ^ text);
    Q.num q, Q.den q
  with Invalid_argument _ | Division_by_zero ->
    fail ("Invalid native rational: " ^ text)

let app_args c a =
  List.init (Z3native.get_app_num_args c a) (Z3native.get_app_arg c a)

let datatype_parameters c d op =
  let id d = Z.of_int (Z3native.get_func_decl_id c d) in
  if op = DatatypeConstructor then
    [sort_id (Z3native.get_range c d); id d; Z.of_int (Z3native.get_domain_size c d)]
  else if op = DatatypeRecognizer then begin
    if Z3native.get_decl_num_parameters c d <> 1 ||
       Z3enums.parameter_kind_of_int (Z3native.get_decl_parameter_kind c d 0) <>
         Z3enums.PARAMETER_FUNC_DECL
    then fail "Malformed native datatype recognizer";
    let constructor = Z3native.get_decl_func_decl_parameter c d 0 in
    [sort_id (Z3native.get_range c constructor); id constructor]
  end else
    let owner = Z3native.get_domain c d 0 in
    let rec constructors index =
      if index = Z3native.get_datatype_sort_num_constructors c owner then
        fail "Native datatype accessor has no owning constructor";
      let constructor = Z3native.get_datatype_sort_constructor c owner index in
      let rec fields field =
        if field = Z3native.get_domain_size c constructor then constructors (index + 1)
        else if Z3native.is_eq_func_decl c d
                  (Z3native.get_datatype_sort_constructor_accessor c owner index field)
        then [sort_id owner; id constructor; Z.of_int field]
        else fields (field + 1)
      in fields 0
    in constructors 0

let view_datatypes roots =
  let module A = Z3AstTheory in
  let module S = Z3DatatypeSignature in
  let converted = Hashtbl.create 16 and seen = Hashtbl.create 16 in
  let rec logical_sort s =
    let id = sort_id s in
    match Hashtbl.find_opt converted id with
    | Some value -> value
    | None ->
        let value = match view_sort s with
          | Base name -> A.BaseSort name
          | Array (domains, range) ->
              A.ArraySort (List.map logical_sort domains, logical_sort range) in
        Hashtbl.add converted id value;
        value
  in
  let declaration c d =
    let op = operator (Z3enums.decl_kind_of_int (Z3native.get_decl_kind c d)) in
    let interp = match op with
      | DatatypeConstructor -> Z3DatatypeLemma.op_constructor
      | DatatypeRecognizer -> Z3DatatypeLemma.op_recognizer
      | DatatypeAccessor -> Z3DatatypeLemma.op_accessor
      | _ -> fail "Non-datatype declaration in native datatype signature" in
    { A.decl_name = symbol c (Z3native.get_decl_name c d);
      domain = List.init (Z3native.get_domain_size c d)
          (fun index -> logical_sort (Z3native.get_domain c d index));
      range = logical_sort (Z3native.get_range c d);
      interp = Some interp; int_params = datatype_parameters c d op }
  in
  let rec nested_datatype s =
    let c = ctx s in
    match Z3enums.sort_kind_of_int (Z3native.get_sort_kind c s) with
    | Z3enums.DATATYPE_SORT -> true
    | Z3enums.SEQ_SORT -> nested_datatype (Z3native.get_seq_sort_basis c s)
    | Z3enums.ARRAY_SORT ->
        List.exists (fun index -> nested_datatype (Z3native.get_array_sort_domain_n c s index))
          (List.init (Z3native.get_array_arity c s) Fun.id) ||
        nested_datatype (Z3native.get_array_sort_range c s)
    | _ -> false
  in
  let rec visit sorts cases = function
    | [] -> { S.sorts = List.rev sorts; cases = List.rev cases }
    | s :: rest when Hashtbl.mem seen (sort_id s) -> visit sorts cases rest
    | s :: rest ->
        Hashtbl.add seen (sort_id s) s;
        let c = ctx s in
        match Z3enums.sort_kind_of_int (Z3native.get_sort_kind c s) with
        | Z3enums.DATATYPE_SORT ->
            let count = Z3native.get_datatype_sort_num_constructors c s in
            if count = 0 then fail "Native datatype signature has no constructors";
            let cases', fields = List.init count (fun index ->
                let constructor = Z3native.get_datatype_sort_constructor c s index in
                let arity = Z3native.get_domain_size c constructor in
                { S.constructor = declaration c constructor;
                  recognizer = declaration c (Z3native.get_datatype_sort_recognizer c s index);
                  accessors = List.init arity (fun field ->
                    declaration c (Z3native.get_datatype_sort_constructor_accessor c s index field)) },
                List.init arity (Z3native.get_domain c constructor))
                |> List.split in
            visit (logical_sort s :: sorts) (List.rev_append cases' cases)
              (List.concat fields @ rest)
        | Z3enums.ARRAY_SORT ->
            let domains = List.init (Z3native.get_array_arity c s)
                (Z3native.get_array_sort_domain_n c s) in
            visit sorts cases (domains @ (Z3native.get_array_sort_range c s :: rest))
        | Z3enums.SEQ_SORT ->
            if nested_datatype s then fail "Nested datatype sequence fields are not supported";
            visit sorts cases rest
        | _ -> visit sorts cases rest
  in
  visit [] [] roots

let view_expression a =
  let c = ctx a in
  match Z3enums.ast_kind_of_int (Z3native.get_ast_kind c a) with
  | Z3enums.VAR_AST ->
      Variable (Z.of_int (Z3native.get_index_value c a), Z3native.get_sort c a)
  | Z3enums.QUANTIFIER_AST ->
      let kind =
        if Z3native.is_quantifier_forall c a then Z3AstTheory.Forall_k
        else if Z3native.is_quantifier_exists c a then Z3AstTheory.Exists_k
        else if Z3native.is_lambda c a then Z3AstTheory.Lambda_k
        else fail "Unknown native quantifier kind"
      in
      let sorts = List.init (Z3native.get_quantifier_num_bound c a)
          (Z3native.get_quantifier_bound_sort c a) in
      Quantified (kind, sorts, Z3native.get_quantifier_body c a)
  | Z3enums.APP_AST | Z3enums.NUMERAL_AST ->
      let app = Z3native.to_app c a in
      let d = Z3native.get_app_decl c app in
      let id = Z.of_int (Z3native.get_func_decl_id c d) in
      let native_kind = Z3native.get_decl_kind c d in
      let op = operator (Z3enums.decl_kind_of_int native_kind) in
      let numeral = if op = Rational || op = BvNumeral
                    then Some (rational (Z3native.get_numeral_string c a))
                    else None in
      let range = Z3native.get_range c d in
      let parameters = match op with
        | Bvand | Bvor | Bvxor | Bvnot | Bvadd | Bvmul | Bvsub | Bvneg |
          Bvudiv | Bvurem | Bvshl | Bvlshr | BvNumeral | Bvmkbv ->
            [Z.of_int (Z3native.get_bv_sort_size c range)]
        | Bvult | Bvule | Bvuge ->
            if Z3native.get_domain_size c d <> 2 then fail "Malformed native unsigned comparison";
            [Z.of_int (Z3native.get_bv_sort_size c (Z3native.get_domain c d 0))]
        | Bvextract ->
            if Z3native.get_decl_num_parameters c d <> 2 ||
               Z3native.get_domain_size c d <> 1 ||
               List.exists (fun i -> Z3enums.parameter_kind_of_int
                 (Z3native.get_decl_parameter_kind c d i) <> Z3enums.PARAMETER_INT) [0; 1]
            then fail "Malformed native bit-vector extraction";
            Z.of_int (Z3native.get_bv_sort_size c (Z3native.get_domain c d 0)) ::
            List.init 2 (fun i -> Z.of_int (Z3native.get_decl_int_parameter c d i))
        | Bvzeroextend ->
            if Z3native.get_decl_num_parameters c d <> 1 ||
               Z3native.get_domain_size c d <> 1 ||
               Z3enums.parameter_kind_of_int (Z3native.get_decl_parameter_kind c d 0) <>
                 Z3enums.PARAMETER_INT
            then fail "Malformed native bit-vector zero extension";
            [Z.of_int (Z3native.get_bv_sort_size c (Z3native.get_domain c d 0));
             Z.of_int (Z3native.get_decl_int_parameter c d 0)]
        | Bvconcat ->
            List.init (Z3native.get_domain_size c d) (fun i ->
              Z.of_int (Z3native.get_bv_sort_size c (Z3native.get_domain c d i)))
        | DatatypeConstructor | DatatypeRecognizer | DatatypeAccessor ->
            datatype_parameters c d op
        | _ -> [] in
      let name = if op = BvNumeral then "bv"
                 else if op = Rational then Z3native.ast_to_string c a
                 else symbol c (Z3native.get_decl_name c d) in
      let declaration = {
        id; name; unique_name = unique "decl" id name; op;
        range; numeral; native_kind = Z.of_int native_kind; parameters;
      } in
      Application (declaration, app_args c app)
  | _ -> fail "Native object is not an expression"

let view_proof a =
  let c = ctx a in
  if not (Z3native.is_app c a) then fail "Native proof node is not an application";
  let app = Z3native.to_app c a in
  let d = Z3native.get_app_decl c app in
  let name = symbol c (Z3native.get_decl_name c d) in
  let args = app_args c app in
  let conclusion, premises =
    match List.rev args with
    | conclusion :: rest ->
        let is_proof e = Z3enums.sort_kind_of_int
            (Z3native.get_sort_kind c (Z3native.get_sort c e)) = Z3enums.UNKNOWN_SORT in
        conclusion, List.filter is_proof (List.rev rest)
    | [] -> fail ("Native proof has no conclusion: " ^ name)
  in
  let count = Z3native.get_decl_num_parameters c d in
  let parameter_kind i =
    Z3enums.parameter_kind_of_int (Z3native.get_decl_parameter_kind c d i) in
  let parameter_symbol i =
    if parameter_kind i = Z3enums.PARAMETER_SYMBOL then
      Some (symbol c (Z3native.get_decl_symbol_parameter c d i))
    else None in
  let arithmetic_hint =
    if name = "th-lemma" && count >= 2 && parameter_symbol 0 = Some "arith"
    then parameter_symbol 1 else None in
  let rational_parameter i =
    match parameter_kind i with
    | Z3enums.PARAMETER_RATIONAL ->
        rational (Z3native.get_decl_rational_parameter c d i)
    | Z3enums.PARAMETER_INT ->
        Z.of_int (Z3native.get_decl_int_parameter c d i), Z.one
    | _ -> fail "Non-rational native arithmetic coefficient" in
  let farkas =
    if arithmetic_hint = Some "farkas" || arithmetic_hint = Some "bound" then
      Some (List.init (count - 2) (fun i -> rational_parameter (i + 2)))
    else if arithmetic_hint = Some "assign-bounds" then
      let coefficients = List.init (count - 2) (fun i -> rational_parameter (i + 2)) in
      (* The propagated bound has implicit unit weight. In clausal proofs it
         precedes the antecedents; otherwise it follows the proof premises. *)
      Some (if premises = [] then (Z.one, Z.one) :: coefficients
            else coefficients @ [Z.one, Z.one])
    else if arithmetic_hint = Some "lp-linear" && count >= 3 then
      (* These are candidate coefficients, not a trusted replay result. The F*
         arithmetic kernel checks them against every actual premise/conclusion. *)
      Some ((Z.zero, Z.one) :: List.init (count - 3) (fun i -> rational_parameter (i + 3)))
    else if (arithmetic_hint = Some "lp-input" || arithmetic_hint = Some "lp-discharge") &&
            count = 3 && (List.length premises = 1 || List.length premises = 2) then
      Some ((Z.zero, Z.one) :: List.init (List.length premises) (fun _ -> Z.one, Z.one))
    else None
  in
  let assumed =
    if name = "th-lemma" && count = 3 &&
       parameter_symbol 0 = Some "arith" && parameter_symbol 1 = Some "assumed"
    then parameter_symbol 2 else None in
  let proof_name =
    if arithmetic_hint = Some "lp-context" then "def-axiom"
    else match arithmetic_hint, farkas with
    | Some tag, None when String.starts_with ~prefix:"lp-" tag -> "arith/" ^ tag
    | _ -> name in
  let lp_data =
    match arithmetic_hint with
    | Some tag when String.starts_with ~prefix:"lp-" tag ->
        let parameters = List.init (count - 2) (fun offset ->
            let i = offset + 2 in
            match parameter_kind i with
            | Z3enums.PARAMETER_RATIONAL ->
                let n, den = rational_parameter i in ParameterRational (n, den)
            | Z3enums.PARAMETER_AST ->
                let value = Z3native.get_decl_ast_parameter c d i in
                (match Z3enums.ast_kind_of_int (Z3native.get_ast_kind c value) with
                 | Z3enums.APP_AST | Z3enums.NUMERAL_AST | Z3enums.VAR_AST
                 | Z3enums.QUANTIFIER_AST -> ParameterExpression value
                 | _ -> ParameterUnsupported)
            | _ -> ParameterUnsupported) in
        Some (tag, parameters)
    | _ -> None in
  let binding =
    if Z3enums.decl_kind_of_int (Z3native.get_decl_kind c d) = Z3enums.OP_PR_BIND then
      match args with
      | [lambda] when Z3native.is_lambda c lambda ->
          let sorts = List.init (Z3native.get_quantifier_num_bound c lambda)
              (Z3native.get_quantifier_bound_sort c lambda) in
          Some (sorts, Z3native.get_quantifier_body c lambda)
      | _ -> fail "Malformed native proof binder"
    else None in
  let instantiations =
    if Z3enums.decl_kind_of_int (Z3native.get_decl_kind c d) = Z3enums.OP_PR_QUANT_INST then
      List.init count (fun i ->
          if parameter_kind i <> Z3enums.PARAMETER_AST then
            fail "Malformed native quantified instance parameter";
          Z3native.get_decl_ast_parameter c d i)
    else [] in
  { proof_name; premises; conclusion; farkas; assumed; lp_data; binding; instantiations }

let view_clause_trail a =
  let c = ctx a in
  let kind a =
    if not (Z3native.is_app c a) then fail "Clause proof entry is not an application";
    Z3enums.decl_kind_of_int
      (Z3native.get_decl_kind c (Z3native.get_app_decl c (Z3native.to_app c a))) in
  if kind a <> Z3enums.OP_PR_CLAUSE_TRAIL then None
  else
    let args = app_args c (Z3native.to_app c a) in
    let conclusion, entries = match List.rev args with
      | conclusion :: entries -> conclusion, List.rev entries
      | [] -> fail "Clause proof trail has no conclusion" in
    let entry a =
      let action = match kind a with
        | Z3enums.OP_PR_ASSUMPTION_ADD -> InputClause
        | Z3enums.OP_PR_LEMMA_ADD -> LearnedClause
        | Z3enums.OP_PR_TH_ASSUMPTION_ADD | Z3enums.OP_PR_TH_LEMMA_ADD -> TheoryClause
        | Z3enums.OP_PR_REDUNDANT_DEL -> DeleteClause
        | _ -> fail "Unknown clause proof entry kind" in
      let certificate, formula = match app_args c (Z3native.to_app c a) with
        | [formula] -> None, formula
        | [certificate; formula] when action <> DeleteClause ->
            Some certificate, formula
        | _ -> fail "Malformed clause proof entry" in
      if Z3enums.sort_kind_of_int
           (Z3native.get_sort_kind c (Z3native.get_sort c formula)) <> Z3enums.BOOL_SORT
      then fail "Clause proof conclusion is not Boolean";
      let formula, literals =
        match kind formula with
        | Z3enums.OP_OR ->
            let literals = app_args c (Z3native.to_app c formula) in
            (match literals with
             | [literal] -> literal, literals
             | _ -> formula, literals)
        | Z3enums.OP_FALSE -> formula, []
        | _ -> formula, [formula] in
      { action; formula; literals; certificate }
    in
    Some (List.map entry entries, conclusion)

let create_context timeout_ms =
  if Z.sign timeout_ms < 0 || Z.gt timeout_ms (Z.of_string "4294967295")
  then fail "Solver timeout must be between 0 and 4294967295 milliseconds";
  let config = Z3native.mk_config () in
  Z3native.set_param_value config "proof" "true";
  Z3native.set_param_value config "timeout" (Z.to_string timeout_ms);
  let c = Z3native.mk_context_rc config in
  Z3native.del_config config;
  Z3native.set_internal_error_handler c;
  Z3native.enable_concurrent_dec_ref c;
  c

let solve_with_clause_proofs input timeout_ms clause_proofs =
  let c = create_context timeout_ms in
  let solver = Z3native.mk_solver c in
  let formulas = Z3native.parse_smtlib2_string c input 0 [] [] 0 [] [] in
  let assertions = List.init (Z3native.ast_vector_size c formulas)
      (Z3native.ast_vector_get c formulas) in
  if clause_proofs then (
    let params = Z3native.mk_params c in
    Z3native.params_set_bool c params (Z3native.mk_string_symbol c "clause_proof") true;
    Z3native.solver_set_params c solver params);
  List.iter (Z3native.solver_assert c solver) assertions;
  match Z3native.solver_check c solver with
  | -1 -> Unsat (assertions, Z3native.solver_get_proof c solver)
  | 1 -> Sat
  | 0 -> Unknown (Z3native.solver_get_reason_unknown c solver)
  | _ -> fail "Invalid native solver status"

let solve input timeout_ms = solve_with_clause_proofs input timeout_ms false

let version () = Z3.Version.to_string
