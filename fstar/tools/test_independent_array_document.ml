module A = Z3AstTheory
module U = Z3UnifiedProofSyntax
module R = Z3ClauseSyntax
module P = Z3DocumentSyntax
module S = Z3DatatypeSignature
module Tags = Z3OperatorTags
module D = Z3IndependentArrayDocument
module Checker = Z3IndependentChecker
module Definition = Z3IndependentDefinitionDocument
module ArrayDefinition = Z3IndependentArrayDefinitionDocument
module ArrayGround = Z3IndependentArrayGroundDocument
module Ground = Z3IndependentGroundDocument
module Root = Z3SortedRootDocument

let require value message = if not value then failwith message
let schema = { S.sorts = []; cases = [] }
let int_sort = A.SortApp (A.IntSymbol, [])
let array_sort = A.ArraySort ([int_sort], int_sort)
let decl name domain range interp int_params =
  { A.decl_name = name; domain; range; interp; int_params }
let constant name sort = A.App (decl name [] sort None [], [])
let array = constant "a" array_sort
let index = constant "i" int_sort
let value = constant "v" int_sort
let select_decl = decl "select" [array_sort; int_sort] int_sort (Some Tags.op_select) []
let store_decl =
  decl "store" [array_sort; int_sort; int_sort] array_sort (Some Tags.op_store) []
let ext_decl = decl "array-ext" [array_sort; array_sort] int_sort (Some Tags.op_array_ext) []
let stored = A.App (store_decl, [array; index; value])
let read = A.App (select_decl, [stored; index])
let formula = R.mk_eq_expr read value
let negated = R.mk_not_expr formula
let leaf rule formula = { P.rule; formula; premise_ids = [] }
let asserted = leaf U.Asserted negated
let resolution = { P.rule = U.UnitResolution; formula = R.false_expr;
                   premise_ids = [Z.zero; Z.one] }
let doc entry = { P.declarations = []; expressions = []; assertions = [negated];
                  entries = [entry; asserted; resolution]; root = Z.of_int 2 }

let require_combined input =
  let verdict, diagnostic = Checker.check_array_diagnosed schema input in
  let expected = Checker.check_array schema input in
  require (verdict = expected) "combined array verdict changed";
  require (diagnostic =
    (if expected = Root.RootCertified then P.DocumentChecked (Z.zero, [])
     else Checker.diagnose schema input))
    "combined array diagnostic changed"

let () =
  let th = leaf (U.Unverified "th-lemma") formula in
  let rewrite = leaf U.RewriteRule formula in
  List.iter (fun entry ->
    let input = doc entry in
    require (D.within_budget input) "small document exceeded budget";
    require (D.has_candidates schema input) "array leaf was not selected";
    require (Root.check_root_document_epsilon schema input = Root.RootPending Z.one)
      "original array leaf was not pending";
    require (Root.check_root_document_epsilon schema (D.augment schema input) = Root.RootCertified)
      "augmented document was not certified";
    require (D.check schema input = Root.RootCertified) "array document was not certified";
    require (Checker.check_array schema input = Root.RootCertified) "array checker did not certify";
    require (Checker.check_definition schema input = Root.RootPending Z.one)
      "array control was not pending in definition mode";
    require (Checker.check_definition_array schema input = Root.RootCertified)
      "definition-array checker did not certify";
    require (Checker.check_definition_array_diagnosed schema input =
             (Root.RootCertified, P.DocumentChecked (Z.zero, [])))
      "definition-array diagnostic did not reflect certification";
    require (Checker.diagnose_array schema input = P.DocumentChecked (Z.zero, []))
      "array checker diagnostic did not reflect replay"
  ) [th; rewrite];
  let pair = decl "pair" [int_sort; int_sort] int_sort None [] in
  let rec expanded n term =
    if n = 0 then term
    else expanded (n - 1) (A.App (pair, [term; term])) in
  let large_value = expanded 11 value in
  let large_store = A.App (store_decl, [array; index; large_value]) in
  let large_formula = R.mk_eq_expr (A.App (select_decl, [large_store; index])) large_value in
  require (A.expression_budget (Z.of_int 4096) large_formula = None)
    "large control did not exceed the old bound";
  require (D.eligible_entry schema (leaf (U.Unverified "th-lemma") large_formula))
    "valid array lemma within the new bound was not selected";
  let larger_value = expanded 13 value in
  let larger_store = A.App (store_decl, [array; index; larger_value]) in
  let larger_formula =
    R.mk_eq_expr (A.App (select_decl, [larger_store; index])) larger_value in
  require (A.expression_budget (Z.of_int 32768) larger_formula = None)
    "larger control did not exceed the previous bound";
  require (D.eligible_entry schema (leaf (U.Unverified "th-lemma") larger_formula))
    "valid array lemma above the previous bound was not selected";
  let oversized_value = expanded 14 value in
  let oversized_store = A.App (store_decl, [array; index; oversized_value]) in
  let oversized_formula =
    R.mk_eq_expr (A.App (select_decl, [oversized_store; index])) oversized_value in
  require (not (D.eligible_entry schema (leaf (U.Unverified "th-lemma") oversized_formula)))
    "array lemma above the new bound was selected";
  let oversized_rewrite_value = expanded 15 value in
  require (not (Z3IndependentArrayReplay.rewrite [] oversized_rewrite_value oversized_rewrite_value))
    "array rewrite above the new bound was selected";
  let other_index = constant "j" int_sort in
  let nested_store = A.App (store_decl, [stored; index; value]) in
  let nested_read = A.App (select_decl, [nested_store; other_index]) in
  let simplified_read = A.App (select_decl, [stored; other_index]) in
  let rewrite_formula = R.mk_eq_expr nested_read simplified_read in
  let rewrite_negated = R.mk_not_expr rewrite_formula in
  let rewrite_th = leaf (U.Unverified "th-lemma") rewrite_formula in
  let rewrite_doc = { (doc rewrite_th) with
    P.assertions = [rewrite_negated];
    entries = [rewrite_th; leaf U.Asserted rewrite_negated; resolution] } in
  require (not (Z3IndependentArrayReplay.clause [] rewrite_formula))
    "nested rewrite unexpectedly matched an array clause";
  require (D.has_candidates schema rewrite_doc) "array rewrite theory lemma was not selected";
  require (Root.check_root_document_epsilon schema rewrite_doc = Root.RootPending Z.one)
    "nested array rewrite was not originally pending";
  require (Checker.check_array schema rewrite_doc = Root.RootCertified)
    "nested array rewrite theory lemma was not certified";
  let domain = A.BaseSort "U" in
  let predicate = decl "fresh" [domain] A.bool_sort None [] in
  let name = A.App (predicate, [A.Var (Z.zero, domain)]) in
  let clause args = A.App (R.or_decl args, args) in
  let positive = A.Quantifier (A.Forall_k, [domain], A.bool_sort,
      clause [R.mk_not_expr name; R.true_expr]) in
  let negative = A.Quantifier (A.Forall_k, [domain], A.bool_sort,
      clause [name; R.mk_not_expr R.true_expr]) in
  let parts = [positive; negative] in
  let definition = leaf U.DefinitionIntroduction (A.App (R.and_decl parts, parts)) in
  let mixed = { (doc th) with
    P.entries = [definition; th; asserted; { resolution with P.premise_ids = [Z.one; Z.of_int 2] }];
    root = Z.of_int 3 } in
  require (D.check schema mixed <> Root.RootCertified)
    "array-only route unexpectedly certified mixed proof";
  require (Definition.eligible schema mixed) "mixed proof definition was not eligible";
  require (Root.check_root_document schema (Definition.augment schema mixed) <> Root.RootCertified)
    "definition-only route unexpectedly certified mixed proof";
  require (Checker.check_array schema mixed = Root.RootCertified)
    "combined array and definition replay did not certify";
  require (Checker.diagnose_array schema mixed = P.DocumentChecked (Z.zero, []))
    "combined replay diagnostic did not reflect certification";
  let nonfresh = { mixed with P.assertions =
    negated :: [A.App (predicate, [constant "u" domain])] } in
  require (ArrayDefinition.selected schema nonfresh = None)
    "definition occurring in an input was accepted";
  require (Checker.check_array schema nonfresh = D.check schema nonfresh)
    "nonfresh definition changed the array verdict";
  let condition = A.App (predicate, [constant "u" domain]) in
  let ite_decl = decl "if" [A.bool_sort; int_sort; int_sort] int_sort (Some Tags.op_ite) [] in
  let conditional_value = A.App (ite_decl, [condition; value; index]) in
  let conditional_store = A.App (store_decl, [array; index; conditional_value]) in
  let conditional_read = A.App (select_decl, [conditional_store; index]) in
  let extra = leaf (U.Unverified "th-lemma") (R.mk_eq_expr conditional_read conditional_value) in
  let extra_nonfresh = { mixed with P.entries =
    [definition; th; extra; asserted; { resolution with P.premise_ids = [Z.one; Z.of_int 3] }];
    root = Z.of_int 4 } in
  require (Definition.eligible schema extra_nonfresh) "original inputs should be fresh";
  require (D.eligible_entry schema extra) "conditional array lemma was not recognized";
  require (not (Definition.eligible schema (D.augment schema extra_nonfresh)))
    "definition occurring in an added array fact was accepted";
  require (ArrayDefinition.selected schema extra_nonfresh = None)
    "nonfresh added array fact was accepted";
  let fresh_array = constant "fresh-array" array_sort in
  let ground_formula = R.mk_eq_expr fresh_array stored in
  let ground_entry = leaf U.DefinitionIntroduction ground_formula in
  let fresh_store = A.App (store_decl, [fresh_array; index; value]) in
  let fresh_read = A.App (select_decl, [fresh_store; index]) in
  let fresh_lemma = leaf (U.Unverified "th-lemma") (R.mk_eq_expr fresh_read value) in
  let false_entry = leaf U.Asserted R.false_expr in
  let ground_mixed = { P.declarations = []; expressions = []; assertions = [R.false_expr];
                       entries = [ground_entry; fresh_lemma; false_entry]; root = Z.of_int 2 } in
  require (Root.check_root_document_epsilon schema ground_mixed = Root.RootPending (Z.of_int 2))
    "mixed ground proof was not originally pending";
  require (D.check schema ground_mixed <> Root.RootCertified)
    "array-only route unexpectedly certified mixed ground proof";
  require (Ground.selected schema ground_mixed = None)
    "ground-only route unexpectedly certified mixed ground proof";
  require (ArrayGround.selected schema ground_mixed <> None)
    "combined ground-array proof was not selected";
  require (Checker.check_array schema ground_mixed = Root.RootCertified)
    "combined ground-array proof was not certified";
  require (Checker.diagnose_array schema ground_mixed = P.DocumentChecked (Z.zero, []))
    "combined ground-array diagnostic did not reflect replay";
  require_combined ground_mixed;
  let ground_nonfresh = { ground_mixed with P.assertions =
    [R.false_expr; R.mk_eq_expr fresh_array array] } in
  require (ArrayGround.selected schema ground_nonfresh = None)
    "nonfresh ground definition was accepted";
  require (Checker.check_array schema ground_nonfresh = D.check schema ground_nonfresh)
    "nonfresh ground definition changed the array verdict";
  let ground_cyclic = { ground_mixed with P.entries =
    [{ ground_entry with P.formula = R.mk_eq_expr fresh_array fresh_array };
     fresh_lemma; false_entry] } in
  require (ArrayGround.selected schema ground_cyclic = None) "cyclic ground definition was accepted";
  let ground_premise = { ground_mixed with P.entries =
    [{ ground_entry with P.premise_ids = [Z.zero] }; fresh_lemma; false_entry] } in
  require (ArrayGround.selected schema ground_premise = None)
    "premise-bearing ground definition was accepted";
  let unsafe_ext = A.App (ext_decl, [array; array]) in
  let ground_with_ext = { ground_mixed with P.assertions =
    [R.false_expr; R.mk_eq_expr unsafe_ext index] } in
  require (ArrayGround.selected schema ground_with_ext = None)
    "original assertion with array-ext was accepted";
  let with_entry entry = { (doc entry) with P.entries = [entry] } in
  require (not (D.has_candidates schema (with_entry { th with P.premise_ids = [Z.zero] })))
    "premise-bearing lemma was selected";
  let bad_read = A.App ({ select_decl with A.int_params = [Z.one] }, [stored; index]) in
  require (not (D.has_candidates schema (with_entry { th with P.formula = R.mk_eq_expr bad_read value })))
    "malformed select was selected";
  let false_formula = R.mk_eq_expr read index in
  require (not (D.has_candidates schema (with_entry { th with P.formula = false_formula })))
    "invalid array lemma was selected";
  let ext = A.App (ext_decl, [array; array]) in
  let with_ext = { (doc th) with P.assertions = [negated; R.mk_eq_expr ext index] } in
  require (D.selected schema with_ext = None) "selected array-ext in an input was accepted";
  require (D.check schema with_ext = Root.check_root_document_epsilon schema with_ext)
    "unsafe input changed its verdict";
  let certified = { (doc th) with P.assertions = [R.false_expr];
                                   entries = [leaf U.Asserted R.false_expr]; root = Z.zero } in
  require (D.check schema certified = Root.check_root_document_epsilon schema certified)
    "already-certified verdict changed";
  let rejected = { certified with P.root = Z.of_int 7 } in
  require (D.check schema rejected = Root.check_root_document_epsilon schema rejected)
    "nonpending verdict changed";
  let pending = { certified with P.entries =
    [leaf (U.Unverified "unknown") condition; leaf U.Asserted R.false_expr]; root = Z.one } in
  require (Checker.check_array schema pending = Root.RootPending Z.one)
    "pending control was not pending";
  List.iter require_combined [doc th; mixed; nonfresh; certified; rejected; pending];
  print_endline "array document replay tests passed"
