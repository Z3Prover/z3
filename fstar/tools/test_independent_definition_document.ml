module A = Z3AstTheory
module U = Z3UnifiedProofSyntax
module R = Z3ClauseSyntax
module O = Z3ObservationalSyntax
module P = Z3DocumentSyntax
module S = Z3DatatypeSignature
module D = Z3IndependentDefinitionDocument
module DN = Z3IndependentDefinitionNnfDocument
module Root = Z3SortedRootDocument
module Checker = Z3IndependentChecker
module Combined = Z3IndependentDefinitionSkolemReplay
module CombinedDoc = Z3IndependentDefinitionSkolemDocument
module SkolemReplay = Z3IndependentSkolemReplay
module DependentReplay = Z3IndependentDependentReplay
module SkolemRoot = Z3IndependentSkolemRoot
module Sorted = Z3SortedProof

let require value message = if not value then failwith message
let schema = { S.sorts = []; cases = [] }
let domain = A.BaseSort "U"
let symbol = { A.decl_name = "fresh"; domain = [domain]; range = A.bool_sort;
               interp = None; int_params = [] }
let name = A.App (symbol, [A.Var (Z.zero, domain)])
let clause args = A.App (R.or_decl args, args)
let positive = A.Quantifier (A.Forall_k, [domain], A.bool_sort,
                             clause [R.mk_not_expr name; R.true_expr])
let negative = A.Quantifier (A.Forall_k, [domain], A.bool_sort,
                             clause [name; R.mk_not_expr R.true_expr])
let formula = let args = [positive; negative] in A.App (R.and_decl args, args)
let definition = { P.rule = U.DefinitionIntroduction; formula; premise_ids = [] }
let false_entry = { P.rule = U.Asserted; formula = R.false_expr; premise_ids = [] }
let doc = { P.declarations = []; expressions = []; assertions = [R.false_expr];
            entries = [definition; false_entry]; root = Z.one }

let forall body = A.Quantifier (A.Forall_k, [domain], A.bool_sort, body)
let lhs = forall name
let rhs = forall R.true_expr
let nnf_entry target =
  let formula = A.App (O.typed_oeq_decl A.bool_sort, [lhs; target]) in
  let step = { U.binder_name = "nnf-pos"; binder_formula = formula;
               binder_premises = []; binder_sorts = None } in
  { P.rule = U.QuantifierIntroduction { U.binder_entries = [step]; binder_root = Z.zero };
    formula; premise_ids = [] }
let nnf_doc target =
  { doc with P.entries = [definition; nnf_entry target; false_entry]; root = Z.of_int 2 }

let dependent_skolem witness =
  let relation = { A.decl_name = "relation"; domain = [A.bool_sort; domain];
                   range = A.bool_sort; interp = None; int_params = [] } in
  let source = A.Quantifier (A.Exists_k, [A.bool_sort], A.bool_sort,
                             A.App (relation, [A.Var (Z.zero, A.bool_sort);
                                               A.Var (Z.one, domain)])) in
  let target = A.App (relation, [A.App (witness, [A.Var (Z.zero, domain)]);
                                  A.Var (Z.zero, domain)]) in
  let equation a b = A.App (O.typed_oeq_decl A.bool_sort, [a; b]) in
  let bound_source = forall source and bound_target = forall target in
  let steps = [
    { U.binder_name = "sk"; binder_formula = equation source target;
      binder_premises = []; binder_sorts = None };
    { U.binder_name = "nnf-pos"; binder_formula = equation bound_source bound_target;
      binder_premises = [Z.zero]; binder_sorts = Some [domain] }
  ] in
  { P.rule = U.QuantifierIntroduction { U.binder_entries = steps; binder_root = Z.one };
    formula = equation bound_source bound_target; premise_ids = [] }

let large_skolem () =
  let int_sort = A.SortApp (A.IntSymbol, []) in
  let witness = { A.decl_name = "closed-witness"; domain = []; range = int_sort;
                  interp = None; int_params = [] } in
  let predicate = { A.decl_name = "large-predicate";
                    domain = List.init 2050 (fun _ -> int_sort); range = A.bool_sort;
                    interp = None; int_params = [] } in
  let source = A.Quantifier (A.Exists_k, [int_sort], A.bool_sort,
                             A.App (predicate, List.init 2050 (fun _ -> A.Var (Z.zero, int_sort)))) in
  let target = A.App (predicate, List.init 2050 (fun _ -> A.App (witness, []))) in
  { P.rule = U.Skolemization;
    formula = A.App (O.typed_oeq_decl A.bool_sort, [source; target]); premise_ids = [] }

let large_dependent witness =
  let relation = { A.decl_name = "large-dependent-relation";
                   domain = A.bool_sort :: List.init 2050 (fun _ -> domain);
                   range = A.bool_sort; interp = None; int_params = [] } in
  let source = A.Quantifier (A.Exists_k, [A.bool_sort], A.bool_sort,
      A.App (relation, A.Var (Z.zero, A.bool_sort) ::
                       List.init 2050 (fun _ -> A.Var (Z.one, domain)))) in
  let target = A.App (relation, A.App (witness, [A.Var (Z.zero, domain)]) ::
                              List.init 2050 (fun _ -> A.Var (Z.zero, domain))) in
  let equation a b = A.App (O.typed_oeq_decl A.bool_sort, [a; b]) in
  let outer = equation (forall source) (forall target) in
  let steps = [
    { U.binder_name = "sk"; binder_formula = equation source target;
      binder_premises = []; binder_sorts = None };
    { U.binder_name = "nnf-pos"; binder_formula = outer;
      binder_premises = [Z.zero]; binder_sorts = Some [domain] } ] in
  { P.rule = U.QuantifierIntroduction { U.binder_entries = steps; binder_root = Z.one };
    formula = outer; premise_ids = [] }, forall target

let large_binder () =
  let int_sort = A.SortApp (A.IntSymbol, []) in
  let pred = { A.decl_name = "binder-predicate";
               domain = List.init 10000 (fun _ -> int_sort); range = A.bool_sort;
               interp = None; int_params = [] } in
  let body = A.App (pred, List.init 10000 (fun _ -> A.Var (Z.zero, int_sort))) in
  let quantified = A.Quantifier (A.Forall_k, [int_sort], A.bool_sort, body) in
  let eq a b = A.App (R.eq_decl A.bool_sort, [a; b]) in
  let inner = { U.binder_name = "refl"; binder_formula = eq body body;
                binder_premises = []; binder_sorts = None } in
  let outer = { U.binder_name = "quant-intro"; binder_formula = eq quantified quantified;
                binder_premises = [Z.zero]; binder_sorts = Some [int_sort] } in
  let cert = { U.binder_entries = [inner; outer]; binder_root = Z.one } in
  { P.rule = U.QuantifierIntroduction cert; formula = eq quantified quantified; premise_ids = [] }

let () =
  require (D.has_definition doc.P.entries) "definition gate missed a definition";
  require (D.eligible schema doc) "valid definition was not selected";
  require (List.length (D.context schema doc) = 1) "definition count differs";
  require (Root.check_root_document schema doc = Root.RootPending Z.one)
    "original definition was not pending";
  require (Root.check_root_document schema (D.augment schema doc) = Root.RootCertified)
    "augmented document was not certified";
  require (Checker.check_definition schema doc = Root.RootCertified)
    "definition checker did not certify the refutation";
  require (Checker.diagnose_definition schema doc = P.DocumentChecked (Z.zero, []))
    "definition diagnostics disagree with the certified verdict";
  let duplicate = { doc with P.entries = [definition; definition; false_entry]; root = Z.of_int 2 } in
  require (not (D.eligible schema duplicate)) "duplicate predicate was accepted";
  require (not (D.eligible schema { doc with P.assertions = [formula] }))
    "predicate occurring in an input was accepted";
  require (not (D.eligible schema { doc with P.entries =
    [{ definition with P.premise_ids = [Z.zero] }; false_entry] }))
    "definition with premises was accepted";
  require (Checker.check_definition schema duplicate = Checker.check schema duplicate)
    "ineligible definition changed the original verdict";
  let with_nnf = nnf_doc rhs in
  require (D.eligible schema with_nnf) "NNF definition was not eligible";
  let items, prepared = D.prepare schema with_nnf in
  let prepared_base = D.augment_prepared schema with_nnf items prepared in
  require (items = D.context schema with_nnf &&
           D.eligible_context schema with_nnf items = D.eligible schema with_nnf)
    "prepared definition context differs";
  require (prepared_base = D.augment schema with_nnf)
    "prepared definition document differs";
  require (DN.augment_prepared schema with_nnf items prepared_base = DN.augment schema with_nnf)
    "prepared NNF document differs";
  require (Root.check_root_document schema (D.augment schema with_nnf) <> Root.RootCertified)
    "definition-only route unexpectedly certified NNF control";
  require (Root.check_root_document schema (DN.augment schema with_nnf) = Root.RootCertified)
    "definition-backed NNF augmentation was not certified";
  require (Checker.check_definition schema with_nnf = Root.RootCertified)
    "definition-backed NNF fallback did not certify";
  require (Checker.diagnose_definition schema with_nnf = P.DocumentChecked (Z.zero, []))
    "NNF fallback diagnostics disagree with verdict";
  let wrong = nnf_doc (forall R.false_expr) in
  require (Checker.check_definition schema wrong = Checker.check schema wrong)
    "incorrect NNF substitution changed the verdict";
  let premature = { with_nnf with P.entries =
    [definition; { (nnf_entry rhs) with P.premise_ids = [Z.zero] }; false_entry] } in
  require (Checker.check_definition schema premature = Checker.check schema premature)
    "NNF with premises changed the verdict";
  let separate_witness = { symbol with A.decl_name = "witness" } in
  let mixed witness = { doc with P.entries = [definition; dependent_skolem witness; false_entry];
                                 root = Z.of_int 2 } in
  let safe = mixed separate_witness in
  let colliding = mixed symbol in
  let dependent doc =
    Sorted.dependent_context schema doc (SkolemReplay.context schema doc) in
  require (List.length (dependent safe) = 1 && List.length (dependent colliding) = 1)
    "dependent Skolem controls did not collect their witnesses";
  require (Combined.compatible schema safe (D.context schema safe))
    "fresh definition and Skolem witness were rejected";
  require (not (Combined.compatible schema colliding (D.context schema colliding)))
    "colliding definition and Skolem witness were accepted";
  let skolem = large_skolem () in
  let combined = { doc with
    P.entries = [definition; nnf_entry rhs; skolem; false_entry]; root = Z.of_int 3 } in
  require (CombinedDoc.eligible schema combined) "combined document was not eligible";
  require (Root.check_root_document schema (DN.augment schema combined) <> Root.RootCertified)
    "definition-only replay unexpectedly certified the mixed proof";
  require (Root.check_root_document schema (CombinedDoc.augment schema combined) = Root.RootCertified)
    "combined replay did not certify definition, NNF and Skolem obligations";
  require (Checker.check_definition schema combined = Root.RootCertified)
    "definition route did not use the combined fallback";
  require (Checker.diagnose_definition schema combined = P.DocumentChecked (Z.zero, []))
    "combined fallback diagnostics disagree with verdict";
  let wrong_combined = { combined with P.entries =
    [definition; nnf_entry (forall R.false_expr); skolem; false_entry] } in
  require (Checker.check_definition schema wrong_combined = Checker.check schema wrong_combined)
    "incorrect combined NNF substitution changed the verdict";
  let nonfresh_combined = { combined with P.assertions = [R.false_expr; skolem.P.formula] } in
  require (Checker.check_definition schema nonfresh_combined = Checker.check schema nonfresh_combined)
    "nonfresh combined Skolem witness changed the verdict";
  let colliding_combined = { colliding with P.entries =
    [definition; dependent_skolem symbol; skolem; false_entry]; root = Z.of_int 3 } in
  require (not (CombinedDoc.eligible schema colliding_combined))
    "combined document accepted a definition/witness collision";
  let large, witness_in_input = large_dependent separate_witness in
  let definition_free = { doc with P.entries = [large; false_entry]; root = Z.one } in
  require (DependentReplay.may_change schema definition_free)
    "definition-free dependent candidate was not detected";
  require (match Checker.check schema definition_free with Root.RootPending _ -> true | _ -> false)
    "definition-free dependent control was not pending";
  require (SkolemRoot.check_dependent schema definition_free = Root.RootCertified)
    "definition-free dependent root was not certified";
  require (Checker.check_definition schema definition_free = Root.RootCertified)
    "definition route did not use definition-free dependent replay";
  require (Checker.diagnose_definition schema definition_free = P.DocumentChecked (Z.zero, []))
    "definition-free dependent diagnostics disagree with verdict";
  let nonfresh_free = { definition_free with P.assertions = [R.false_expr; witness_in_input] } in
  require (Checker.check_definition schema nonfresh_free = Checker.check schema nonfresh_free)
    "nonfresh definition-free dependent witness changed the verdict";
  let malformed = match large.P.rule with
    | U.QuantifierIntroduction cert ->
      (match cert.U.binder_entries with
       | [inner; outer] ->
         { large with P.rule = U.QuantifierIntroduction
           { cert with U.binder_entries = [{ inner with U.binder_premises = [Z.zero] }; outer] } }
       | _ -> assert false)
    | _ -> assert false in
  let malformed_free = { definition_free with P.entries = [malformed; false_entry] } in
  require (Checker.check_definition schema malformed_free = Checker.check schema malformed_free)
    "malformed definition-free dependent witness changed the verdict";
  let unknown_definition = { false_entry with P.rule = U.DefinitionIntroduction } in
  let not_free = { definition_free with P.entries = [large; false_entry; unknown_definition] } in
  require (Checker.check_definition schema not_free = Checker.check schema not_free)
    "definition-free dependent fallback accepted a mixed document";
  let dependent_mixed = { doc with
    P.entries = [definition; nnf_entry rhs; large; false_entry]; root = Z.of_int 3 } in
  let closed = SkolemReplay.context schema dependent_mixed in
  require (Sorted.dependent_context schema dependent_mixed closed = [] &&
           List.length (DependentReplay.context schema dependent_mixed closed) = 1)
    "large dependent witness did not distinguish replay contexts";
  require (CombinedDoc.eligible_dependent schema dependent_mixed)
    "combined dependent document was not eligible";
  require (Root.check_root_document schema (CombinedDoc.augment schema dependent_mixed) <> Root.RootCertified)
    "smaller combined replay unexpectedly certified dependent proof";
  require (Root.check_root_document schema (CombinedDoc.augment_dependent schema dependent_mixed) = Root.RootCertified)
    "larger combined replay did not certify dependent proof";
  require (Checker.check_definition schema dependent_mixed = Root.RootCertified)
    "definition route did not use combined dependent replay";
  require (Checker.diagnose_definition schema dependent_mixed = P.DocumentChecked (Z.zero, []))
    "combined dependent diagnostics disagree with verdict";
  let nonfresh_dependent = { dependent_mixed with P.assertions = [R.false_expr; witness_in_input] } in
  require (Checker.check_definition schema nonfresh_dependent = Checker.check schema nonfresh_dependent)
    "nonfresh dependent witness changed the verdict";
  let collision, _ = large_dependent symbol in
  let collision_doc = { dependent_mixed with P.entries =
    [definition; nnf_entry rhs; collision; false_entry] } in
  require (not (CombinedDoc.eligible_dependent schema collision_doc))
    "large dependent witness collided with a defined predicate";
  require (Checker.check_definition schema collision_doc = Checker.check schema collision_doc)
    "colliding dependent witness changed the verdict";
  let wrong_dependent = { dependent_mixed with P.entries =
    [definition; nnf_entry (forall R.false_expr); large; false_entry] } in
  require (Checker.check_definition schema wrong_dependent = Checker.check schema wrong_dependent)
    "incorrect dependent NNF substitution changed the verdict";
  let binder = large_binder () in
  let uncovered_binder = { doc with P.entries = [binder; false_entry]; root = Z.one } in
  require (Root.check_root_document_epsilon schema uncovered_binder = Root.RootUncovered)
    "definition-free binder control was already covered";
  require (Checker.check schema uncovered_binder = Root.RootCertified &&
           Checker.check_definition schema uncovered_binder = Root.RootCertified)
    "definition route lost recovery of an unused out-of-budget certificate";
  let free_binder = { doc with P.entries = [large; binder; false_entry]; root = Z.of_int 2 } in
  require (DependentReplay.may_change schema free_binder)
    "definition-free binder control did not need the larger dependent context";
  require (match Checker.check schema free_binder with Root.RootPending _ -> true | _ -> false)
    "definition-free binder control was not pending";
  require (SkolemRoot.check schema free_binder <> Root.RootCertified &&
           SkolemRoot.check_dependent schema free_binder <> Root.RootCertified)
    "prior Skolem replay unexpectedly certified the definition-free binder control";
  require (Checker.check_definition schema free_binder = Root.RootCertified)
    "definition-free selected binder was not certified";
  require (Checker.diagnose_definition schema free_binder = P.DocumentChecked (Z.zero, []))
    "definition-free binder diagnostics disagree with verdict";
  let free_closed_binder = { doc with P.entries = [skolem; binder; false_entry]; root = Z.of_int 2 } in
  require (not (D.has_definition free_closed_binder.P.entries) &&
           not (D.eligible schema free_closed_binder) &&
           Checker.definition_augmented schema free_closed_binder = None)
    "definition-free Skolem elaboration produced a definition";
  require (not (DependentReplay.may_change schema free_closed_binder))
    "closed binder control unexpectedly changed the dependent context";
  require (match Checker.check schema free_closed_binder with Root.RootPending _ -> true | _ -> false)
    "closed binder control was not pending";
  require (SkolemRoot.check schema free_closed_binder <> Root.RootCertified)
    "closed Skolem replay unexpectedly certified the binder control";
  require (Checker.check_definition schema free_closed_binder = Root.RootCertified)
    "definition route did not certify the closed Skolem and binder control";
  require (Checker.diagnose_definition schema free_closed_binder = P.DocumentChecked (Z.zero, []))
    "closed binder diagnostics disagree with verdict";
  let free_closed_nonfresh = { free_closed_binder with P.assertions = [R.false_expr; skolem.P.formula] } in
  require (Checker.check_definition schema free_closed_nonfresh = Checker.check schema free_closed_nonfresh)
    "closed binder accepted a nonfresh witness";
  let free_premise = { free_binder with P.entries =
    [large; { binder with P.premise_ids = [Z.zero] }; false_entry] } in
  require (Checker.check_definition schema free_premise = Checker.check schema free_premise)
    "definition-free binder with premises changed the verdict";
  let free_nonfresh = { free_binder with P.assertions = [R.false_expr; witness_in_input];
    entries = [large; binder; false_entry]; root = Z.of_int 2 } in
  require (Checker.check_definition schema free_nonfresh = Checker.check schema free_nonfresh)
    "definition-free binder accepted a nonfresh witness";
  let binder_only = { doc with P.entries =
    [definition; nnf_entry rhs; binder; false_entry]; root = Z.of_int 3 } in
  require (not (DependentReplay.may_change schema binder_only) &&
           Checker.check_definition schema binder_only = Root.RootCertified)
    "combined binder replay required a larger dependent context";
  let binder_mixed = { dependent_mixed with P.entries =
    [definition; nnf_entry rhs; large; binder; false_entry]; root = Z.of_int 4 } in
  require (Root.check_root_document schema (CombinedDoc.augment_dependent schema binder_mixed) <> Root.RootCertified)
    "combined dependent replay unexpectedly certified large binder";
  require (Root.check_root_document schema (CombinedDoc.augment_binder schema binder_mixed) = Root.RootCertified)
    "combined binder elaboration did not certify mixed proof";
  require (Checker.check_definition schema binder_mixed = Root.RootCertified)
    "definition route did not use combined binder replay";
  require (Checker.diagnose_definition schema binder_mixed = P.DocumentChecked (Z.zero, []))
    "combined binder diagnostics disagree with verdict";
  let binder_with_premise = { binder_mixed with P.entries =
    [definition; nnf_entry rhs; large; { binder with P.premise_ids = [Z.zero] }; false_entry] } in
  require (Checker.check_definition schema binder_with_premise = Checker.check schema binder_with_premise)
    "binder with premises changed the verdict";
  let cyclic = match binder.P.rule with
    | U.QuantifierIntroduction cert ->
      (match cert.U.binder_entries with
       | [inner; outer] ->
         { binder with P.rule = U.QuantifierIntroduction
           { cert with U.binder_entries = [inner; { outer with U.binder_premises = [Z.one] }] } }
       | _ -> assert false)
    | _ -> assert false in
  let cyclic_binder = { binder_mixed with P.entries =
    [definition; nnf_entry rhs; large; cyclic; false_entry] } in
  require (Checker.check_definition schema cyclic_binder = Checker.check schema cyclic_binder)
    "cyclic binder changed the verdict";
  let free_cyclic = { free_binder with P.entries = [large; cyclic; false_entry] } in
  require (Checker.check_definition schema free_cyclic = Checker.check schema free_cyclic)
    "cyclic definition-free binder changed the verdict";
  let free_closed_cyclic = { free_closed_binder with P.entries = [skolem; cyclic; false_entry] } in
  require (Checker.check_definition schema free_closed_cyclic = Checker.check schema free_closed_cyclic)
    "cyclic closed binder changed the verdict";
  let nonfresh_binder = { binder_mixed with P.assertions = [R.false_expr; witness_in_input] } in
  require (Checker.check_definition schema nonfresh_binder = Checker.check schema nonfresh_binder)
    "nonfresh witness changed combined binder verdict";
  let collision_binder = { binder_mixed with P.entries =
    [definition; nnf_entry rhs; collision; binder; false_entry] } in
  require (Checker.check_definition schema collision_binder = Checker.check schema collision_binder)
    "colliding witness changed combined binder verdict";
  let wrong_binder = { binder_mixed with P.entries =
    [definition; nnf_entry (forall R.false_expr); large; binder; false_entry] } in
  require (Checker.check_definition schema wrong_binder = Checker.check schema wrong_binder)
    "incorrect NNF changed combined binder verdict";
  print_endline "definition document replay tests passed"
