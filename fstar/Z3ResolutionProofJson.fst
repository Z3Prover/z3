(* Decode the DAG into the unified, judgment-tagged proof kernel.
   JSON owns references and schema validation, not inference semantics. *)
module Z3ResolutionProofJson

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3UnifiedProof
open Z3ProofJson
module D = Z3Definitions

let rule_of_name (name:string) : option rule =
  if name = "asserted" then Some Asserted
  else if name = "def-axiom" then Some DefAxiom
  else if name = "intro-def" then Some DefinitionIntroduction
  else if name = "apply-def" then Some ApplyDefinition
  else if name = "hypothesis" then Some Hypothesis
  else if name = "lemma" then Some LemmaRule
  else if name = "rewrite" then Some RewriteRule
  else if name = "refl" || name = "reflexivity" then Some Reflexivity
  else if name = "symm" then Some Symmetry
  else if name = "trans" then Some Transitivity
  else if name = "trans*" then Some TransitivityPath
  else if name = "monotonicity" then Some Congruence
  else if name = "commutativity" then Some Commutativity
  else if name = "mp" then Some ModusPonens
  else if name = "mp~" then Some ObservationalMP
  else if name = "iff~" then Some IffObservational
  else if name = "unit-resolution" then Some UnitResolution
  else if name = "and-elim" then Some AndElimination
  else if name = "not-or-elim" then Some NotOrElimination
  else if name = "iff-true" then Some IffTrue
  else if name = "iff-false" then Some IffFalse
  else None

let checked_consequence (kind:string) (concl:expr) (facts:list expr) : bool =
  match rule_of_name kind, classify_fact concl, opt_map classify_fact facts with
  | Some r, Some j, Some js -> check_step r j js
  | _, _, _ -> false

let decode_coefficient (j:json) : option Z3LinearArithmeticAst.coefficient =
  match j with
  | JArr [JInt n; JInt d] -> if d > 0 then Some (n, d) else None
  | _ -> None

let theory_rule (tag:string) (fields:list (string & json)) : option rule =
  match json_field fields "arithmetic_certificate" with
  | Some certificate ->
    if tag <> "th-lemma" then Some (Unverified tag)
    else
      json_obj certificate >>= (fun c ->
      json_field c "kind" >>= json_str >>= (fun kind ->
      if kind <> "farkas" then Some (Unverified tag)
      else
        json_field c "coefficients" >>= json_arr >>= opt_map decode_coefficient >>= (fun cs ->
        Some (ArithmeticFarkas cs))))
  | None -> Some (Unverified tag)

let node_rule (fields:list (string & json)) : option rule =
  json_field fields "kind" >>= json_str >>= (fun kind ->
  if kind = "trusted" then
    json_field fields "rule" >>= json_str >>= (fun tag ->
      if tag = "def-axiom" then Some DefAxiom
      else if tag = "intro-def" then Some DefinitionIntroduction
      else if tag = "apply-def" then Some ApplyDefinition
      else theory_rule tag fields)
  else rule_of_name kind)

let rec axiom_branches (exprs:index_tree expr) (js:list json)
  : Tot (option (list expr)) (decreases js) =
  match js with
  | [] -> Some []
  | j :: rest ->
    json_obj j >>= (fun fields ->
    node_rule fields >>= (fun r ->
    axiom_branches exprs rest >>= (fun branches ->
    if r <> DefAxiom then Some branches else
    json_field fields "conclusion" >>= json_int >>= index_find exprs >>= (fun e ->
    Some (if D.axiom_branch e && not (D.tautology 128 e) then e :: branches else branches)))))

let rec collect_definitions (exprs:index_tree expr) (defs:list D.definition)
                            (branches:list expr) (js:list json)
  : Tot (option (list D.definition)) (decreases js) =
  match js with
  | [] -> Some defs
  | j :: rest ->
    json_obj j >>= (fun fields ->
    node_rule fields >>= (fun r ->
    if r <> DefinitionIntroduction && r <> DefAxiom then collect_definitions exprs defs branches rest
    else
      json_field fields "premises" >>= json_arr >>= (fun premises ->
      if Cons? premises then None else
      json_field fields "conclusion" >>= json_int >>= index_find exprs >>= (fun e ->
      if not (D.scoped [] e) then None else
      let candidate = if r = DefinitionIntroduction then D.definition_of e
                      else D.axiom_definition e branches in
      match candidate with
      | None -> if r = DefinitionIntroduction then None else collect_definitions exprs defs branches rest
      | Some d ->
        D.add_definition defs d >>= (fun defs' ->
        collect_definitions exprs defs' branches rest)))))

let decode_node (strict bound:bool) (defs:list D.definition)
                (exprs:index_tree expr) (assertions:list judgment)
                (prev:index_tree checked_fact) (j:json)
  : option (checked_fact & nat) =
  json_obj j >>= (fun fields ->
  node_rule fields >>= (fun r ->
  json_field fields "conclusion" >>= json_int >>= index_find exprs >>= (fun original ->
  if bound && not (D.scoped [] original) then None else
  D.expand (FStar.List.Tot.length defs) defs original >>= (fun e ->
  if bound && not (D.scoped [] e) then None else
  classify_fact e >>= (fun concl ->
  json_field fields "premises" >>= json_arr >>= opt_map json_int >>= (fun indices ->
  opt_map (fun (i:int) -> if i < 0 then None else index_get prev i) indices >>= (fun nodes ->
  check_node_with_inputs strict assertions { kind = r; conclusion = concl; premises = nodes })))))))

let rec decode_nodes (strict bound:bool) (defs:list D.definition)
                     (exprs:index_tree expr) (assertions:list judgment)
                     (acc:index_tree checked_fact) (next:nat) (trusted:nat) (js:list json)
  : Tot (option (index_tree checked_fact & nat)) (decreases js) =
  match js with
  | [] -> Some (acc, trusted)
  | j :: rest ->
    (* Premises are cached checked facts, never recursively checked nodes. *)
    decode_node strict bound defs exprs assertions acc j >>= (fun nt ->
    decode_nodes strict bound defs exprs assertions (index_put acc next (fst nt))
                 (next + 1) (trusted + snd nt) rest)

let rec ground_exprs (exprs:list expr) : Tot bool (decreases exprs) =
  match exprs with
  | [] -> true
  | App f args :: rest ->
    sorts_match args f.domain && ordinary_facts args && ground_exprs rest
  | _ -> false

let rec well_formed_exprs (exprs:list expr) : Tot bool (decreases exprs) =
  match exprs with
  | [] -> true
  | App f args :: rest ->
    sorts_match args f.domain && ordinary_facts args && well_formed_exprs rest
  | Quantifier k bs s b :: rest ->
    s = quant_sort k bs (get_sort b) && (k = Lambda_k || get_sort b = bool_sort) &&
    ordinary_facts [b] && well_formed_exprs rest
  | Var _ _ :: rest -> well_formed_exprs rest

let rec scoped_assertions (assertions:list expr) : Tot bool (decreases assertions) =
  match assertions with
  | [] -> true
  | a :: rest -> D.scoped [] a && scoped_assertions rest

let rec boolean_domains (dom:list sort) : Tot bool (decreases dom) =
  match dom with
  | [] -> true
  | s :: rest -> s = bool_sort && boolean_domains rest

let logical_decl (f:func_decl) : bool =
  if f.decl_name = "not" then
    f.interp = Some op_not && f.domain = [bool_sort] && f.range = bool_sort
  else if f.decl_name = "and" || f.decl_name = "or" then
    f.interp = Some (if f.decl_name = "and" then op_and else op_or) &&
    boolean_domains f.domain && f.range = bool_sort
  else if f.decl_name = "implies" || f.decl_name = "=>" then
    f.interp = Some op_implies && f.domain = [bool_sort; bool_sort] && f.range = bool_sort
  else if f.decl_name = "=" then
    (match f.domain with
     | [s; t] -> s = t && f.interp = Some op_eq && f.range = bool_sort
     | _ -> false)
  else if f.decl_name = "xor" then f = Z3BooleanRewrite.boolean_xor_decl
  else if f.decl_name = "distinct" then Z3DistinctAst.distinct_declaration f
  else if f.decl_name = "~" then f = oeq_decl
  else if f.interp = Some op_oeq then false
  else if f.decl_name = "true" || f.decl_name = "false" then
    f.interp = Some (if f.decl_name = "true" then op_true else op_false) &&
    f.domain = [] && f.range = bool_sort
  else true

let rec logical_decls (decls:list func_decl) : Tot bool (decreases decls) =
  match decls with
  | [] -> true
  | d :: rest -> logical_decl d && logical_decls rest

let decode_resolution_doc (force_strict:bool) (fields:list (string & json)) : option nat =
  (match json_field fields "check_original_assertions" with
   | None -> Some force_strict
   | Some (JBool b) -> Some (force_strict || b)
   | Some _ -> None) >>= (fun strict ->
  json_field fields "sorts" >>= json_arr >>= decode_sorts [] >>= (fun sorts ->
  json_field fields "decls" >>= json_arr >>= decode_decls sorts [] >>= (fun decls ->
  if not (logical_decls decls) then None else
  json_field fields "exprs" >>= json_arr >>= decode_indexed_exprs sorts decls Empty 0 [] >>= (fun decoded ->
  let exprs = fst decoded in
  let bound = not (ground_exprs (snd decoded)) in
  if bound && not (well_formed_exprs (snd decoded)) then None else
  json_field fields "assertions" >>= json_arr >>= opt_map json_int >>= opt_map (index_find exprs) >>= (fun assertions ->
  if not (ordinary_facts assertions) || (bound && not (scoped_assertions assertions)) then None else
  json_field fields "proofs" >>= json_arr >>= (fun proofs ->
  axiom_branches exprs proofs >>= (fun branches ->
  collect_definitions exprs [] branches proofs >>= (fun defs ->
  if not (D.acyclic (FStar.List.Tot.length defs) defs defs) then None else
  D.expand_args (FStar.List.Tot.length defs) defs assertions >>= (fun expanded ->
  opt_map classify_fact expanded >>= (fun inputs ->
  decode_nodes strict bound defs exprs inputs Empty 0 0 proofs >>= (fun result ->
  json_field fields "root" >>= json_int >>= (fun root ->
  if root < 0 then None else
  index_get (fst result) root >>= (fun node ->
  if false_judgment node.conclusion && node.hypotheses = [] then
    (* This deliberately examines the original inputs, after the entire DAG. *)
    if D.check_fresh_inputs defs assertions then Some (snd result) else None
  else None)))))))))))))

(* -2 selects the legacy equational decoder; -1 rejects. A nonnegative
   result counts explicit, still-unverified leaf obligations. *)
let check_resolution_json_with_inputs (force_strict:bool) (s:string) : int =
  match parse_json s with
  | Some (JObj fields) ->
    (match json_field fields "format" with
     | None -> if force_strict then -1 else -2
     | Some (JStr "resolution-v1") ->
       (match decode_resolution_doc force_strict fields with Some n -> n | None -> -1)
     | Some _ -> -1)
  | _ -> -1

let check_resolution_json (s:string) : int =
  check_resolution_json_with_inputs false s
