module A = Z3AstTheory
module U = Z3UnifiedProofSyntax
module R = Z3ClauseSyntax
module P = Z3DocumentSyntax
module S = Z3DatatypeSignature
module F = Z3IndependentFiniteFieldDocument
module Checker = Z3IndependentChecker
module Root = Z3SortedRootDocument
module FC = Z3FiniteFieldCertificate
module Replay = Z3IndependentFiniteFieldReplay
module Witness = Z3IndependentFiniteFieldWitness
module SortedField = Z3SortedFiniteField

let require value message = if not value then failwith message
let p = Z.of_int 5
let field = A.SortApp (A.FiniteFieldSymbol p, [])
let decl name domain range interp int_params =
  { A.decl_name = name; domain; range; interp; int_params }
let x = A.App (decl "x" [] field None [], [])
let number n =
  A.App (decl "ff" [] field (Some (Z.of_int 300)) [p; Z.of_int n], [])
let add a b =
  A.App (decl "ff.add" [field; field] field (Some (Z.of_int 301)) [p], [a; b])
let formula = R.mk_eq_expr (add x (number 0)) x
let entry = { P.rule = U.RewriteRule; formula; premise_ids = [] }
let negated = R.mk_not_expr formula
let asserted = { entry with P.rule = U.Asserted; formula = negated }
let resolution = { P.rule = U.UnitResolution; formula = R.false_expr;
                   premise_ids = [Z.zero; Z.one] }
let doc = { P.declarations = []; expressions = []; assertions = [negated];
            entries = [entry; asserted; resolution]; root = Z.of_int 2 }
let schema = { S.sorts = []; cases = [] }

let () =
  require (F.has_candidates p doc) "valid rewrite was not selected";
  let seven = Z.of_int 7 in
  let other_field = A.SortApp (A.FiniteFieldSymbol seven, []) in
  let other_number =
    A.App (decl "ff" [] other_field (Some (Z.of_int 300)) [seven; Z.zero], []) in
  let ignored = { entry with P.rule = U.Asserted;
                             formula = R.mk_eq_expr other_number other_number } in
  require (F.modulus { doc with P.entries = [ignored; entry] } = Some p)
    "modulus selection used an ineligible entry";
  require (Root.check_root_document_epsilon schema doc = Root.RootPending Z.one)
    "original rewrite was not pending";
  let augmented = F.augment p doc in
  require (Root.check_root_document_epsilon schema augmented = Root.RootCertified)
    "valid rewrite did not yield a certified refutation";
  require (Checker.check_field schema doc = Root.RootCertified)
    "field checker did not certify the refutation";
  require (Checker.diagnose_field schema doc = P.DocumentChecked (Z.zero, []))
    "field diagnostics disagree with the certified verdict";
  require (not (F.has_candidates (Z.of_int 7) doc)) "wrong modulus was selected";
  let with_entry e = { doc with P.entries = [e] } in
  require (not (F.has_candidates p (with_entry { entry with P.premise_ids = [Z.zero] })))
    "rewrite with premises was selected";
  require (not (F.has_candidates p (with_entry
    { entry with P.formula = R.mk_eq_expr (add x (number 1)) x })))
    "false rewrite was selected";
  let open_x = A.Var (Z.zero, field) in
  require (not (F.has_candidates p (with_entry
    { entry with P.formula = R.mk_eq_expr (add open_x (number 0)) open_x })))
    "unscoped rewrite was selected";
  let valid_clause = R.mk_not_expr (R.mk_eq_expr x (add x (number 1))) in
  let clause_entry = { P.rule = U.Unverified "th-lemma"; formula = valid_clause; premise_ids = [] } in
  require (F.has_candidates p (with_entry clause_entry)) "valid field clause was not selected";
  require (not (F.has_candidates p (with_entry
    { clause_entry with P.formula = R.mk_not_expr (R.mk_eq_expr x (add x (number 0))) })))
    "false field clause was selected";
  require (not (F.has_candidates (Z.of_int 7) (with_entry clause_entry)))
    "wrong-modulus field clause was selected";
  let no_candidates = with_entry { entry with P.premise_ids = [Z.zero] } in
  require (Checker.check_field schema no_candidates = Checker.check schema no_candidates)
    "field checker changed an unsupported verdict";
  let modulus = Z.of_int 2147483647 in
  let fs = A.SortApp (A.FiniteFieldSymbol modulus, []) in
  let num n = A.App (decl "ff" [] fs (Some (Z.of_int 300)) [modulus; Z.of_int n], []) in
  let symbol name = A.App (decl name [] fs None [], []) in
  let op name tag args =
    A.App (decl name (List.map (fun _ -> fs) args) fs (Some (Z.of_int tag)) [modulus], args) in
  let plus args = op "ff.add" 301 args and mul args = op "ff.mul" 302 args in
  let a = symbol "a" and b = symbol "b" in
  let eq0 = R.mk_eq_expr (mul [a; b]) (num 1) in
  let eq1 = R.mk_eq_expr (mul [a; plus [num 1; b]]) (plus [num 2; a]) in
  let clause = A.App (R.or_decl [R.mk_not_expr eq0; R.mk_not_expr eq1],
                      [R.mk_not_expr eq0; R.mk_not_expr eq1]) in
  let minus_one = A.App (decl "ff" [] fs (Some (Z.of_int 300))
                        [modulus; Z.pred modulus], []) in
  let i n = Z.of_int n in
  let certificate = {
    FC.pac_premises = [eq0; eq1];
    pac_nodes = [FC.PacInput (i 4); FC.PacInput (i 5); FC.PacInput (i 3);
      FC.PacMul (i 2, minus_one, []); FC.PacAdd (i 1, i 3); FC.PacAdd (i 0, i 4);
      FC.PacInput (i 2); FC.PacMul (i 6, minus_one, [i 1]); FC.PacAdd (i 5, i 7);
      FC.PacInput (i 1); FC.PacInput (i 0); FC.PacMul (i 10, minus_one, []);
      FC.PacAdd (i 9, i 11); FC.PacMul (i 12, minus_one, []);
      FC.PacAdd (i 8, i 13); FC.PacMul (i 14, minus_one, [])];
    pac_root = i 15; pac_support = [i 0; i 1] } in
  let pac_entry = { P.rule = U.FiniteFieldPac certificate; formula = clause; premise_ids = [] } in
  require (not (Replay.clause modulus clause) && Replay.pac modulus certificate clause)
    "valid PAC was not recognized independently of exhaustive replay";
  let pac_doc = { doc with assertions = [R.mk_not_expr clause];
    entries = [pac_entry; { asserted with P.formula = R.mk_not_expr clause }; resolution] } in
  require (Root.check_root_document_epsilon schema pac_doc = Root.RootPending Z.one)
    "original PAC proof was not pending";
  require (Checker.check_field schema pac_doc = Root.RootCertified)
    "valid PAC proof was not certified";
  require (not (Replay.pac (i 7) certificate clause)) "wrong PAC modulus was accepted";
  require (not (Replay.pac modulus certificate R.false_expr))
    "PAC was accepted for a different conclusion";
  let open_premise = R.mk_eq_expr (A.Var (Z.zero, fs)) (num 0) in
  let open_certificate = { certificate with FC.pac_premises = [open_premise; eq1] } in
  require (not (Replay.pac modulus open_certificate clause))
    "PAC with an open premise was accepted";
  let invalid = { certificate with FC.pac_root = i 14 } in
  require (not (F.has_candidates modulus (with_entry
    { pac_entry with P.rule = U.FiniteFieldPac invalid })))
    "invalid PAC root was selected";
  require (not (F.has_candidates modulus (with_entry
    { pac_entry with P.premise_ids = [Z.zero] })))
    "PAC with proof premises was selected";
  let witness_fixture modulus =
    let field = A.SortApp (A.FiniteFieldSymbol modulus, []) in
    let num n =
      A.App (decl "ff" [] field (Some (i 300)) [modulus; i n], []) in
    let var = A.App (decl "x" [] field None [], []) in
    let sum = A.App (decl "ff.add" [field; field] field (Some (i 301)) [modulus],
                     [var; num 0]) in
    let equality = R.mk_eq_expr sum var in
    let premise = R.mk_not_expr equality in
    let neg_one = A.App (decl "ff" [] field (Some (i 300)) [modulus; Z.pred modulus], []) in
    let cert = { FC.pac_premises = [premise];
      pac_nodes = [FC.PacInput (i 1); FC.PacInput (i 0);
        FC.PacMul (i 1, neg_one, [i 2]); FC.PacAdd (i 0, i 2);
        FC.PacMul (i 3, neg_one, [])];
      pac_root = i 4; pac_support = [i 0] } in
    equality, cert in
  let equality, witness = witness_fixture p in
  require (not (SortedField.check witness equality))
    "legacy PAC unexpectedly accepted a witness";
  require (Witness.check witness equality && Replay.pac p witness equality)
    "prime witness certificate was not accepted";
  require (not (Replay.pac p { witness with FC.pac_root = i 3 } equality))
    "invalid witness root was accepted";
  require (not (Replay.pac p { witness with FC.pac_support = [] } equality))
    "unsupported witness premise was accepted";
  require (not (Replay.pac p witness R.false_expr))
    "witness certificate accepted an unrelated conclusion";
  require (not (Replay.pac (i 7) witness equality))
    "witness certificate accepted the wrong modulus";
  List.iter (fun modulus ->
    let equality, cert = witness_fixture modulus in
    require (not (Replay.pac modulus cert equality))
      "composite or unsupported prime witness was accepted") [i 4; i 65537];
  let larger_equality, larger_witness = witness_fixture (i 263) in
  require (not (SortedField.check larger_witness larger_equality) &&
           Replay.pac (i 263) larger_witness larger_equality)
    "witness certificate for prime 263 was not accepted";
  let equality_65537, witness_65537 = witness_fixture (i 65537) in
  let evidence_65537 = Some (i 3, List.init 16 (fun _ -> i 2)) in
  require (Witness.check_with_evidence witness_65537 equality_65537 evidence_65537)
    "valid large-prime evidence did not enable witness replay";
  require (Replay.pac_with_evidence (i 65537) witness_65537 equality_65537 evidence_65537)
    "valid large-prime evidence did not enable PAC replay";
  require (not (Replay.pac_with_evidence (i 65539) witness_65537 equality_65537 evidence_65537))
    "PAC replay accepted a mismatched modulus with prime evidence";
  require (not (Witness.check_with_evidence witness_65537 equality_65537 None))
    "missing large-prime evidence was accepted";
  require (not (Witness.check_with_evidence witness_65537 equality_65537
                  (Some (i 3, List.init 15 (fun _ -> i 2)))))
    "incomplete large-prime evidence was accepted";
  require (not (Witness.check_with_evidence witness_65537 equality_65537
                  (Some (i 5, [i 2; i 3]))))
    "evidence for a different modulus was accepted";
  require (not (Witness.check_with_evidence
                  { witness_65537 with FC.pac_root = i 3 } equality_65537 evidence_65537))
    "large-prime evidence accepted an invalid witness root";
  let evidence_clause =
    A.App (R.or_decl [equality_65537; R.false_expr], [equality_65537; R.false_expr]) in
  let evidence_entry = { P.rule = U.FiniteFieldPac witness_65537;
                         formula = evidence_clause; premise_ids = [] } in
  let evidence_negated = R.mk_not_expr evidence_clause in
  let evidence_doc = { doc with P.assertions = [evidence_negated];
    entries = [evidence_entry; { asserted with P.formula = evidence_negated }; resolution] } in
  require (not (F.has_candidates (i 65537) evidence_doc))
    "large-prime witness unexpectedly selected without evidence";
  require (F.has_candidates_with_evidence (i 65537) evidence_doc evidence_65537)
    "valid evidence did not select the large-prime witness";
  require (Root.check_root_document_epsilon schema
             (F.augment_with_evidence (i 65537) evidence_doc evidence_65537) = Root.RootCertified)
    "valid evidence did not certify the witness document";
  require (Checker.check_field_with_evidence schema evidence_doc evidence_65537 = Root.RootCertified)
    "evidence-aware checker did not certify the witness document";
  require (Checker.diagnose_field_with_evidence schema evidence_doc evidence_65537 =
           P.DocumentChecked (Z.zero, []))
    "evidence-aware diagnostics disagree with the certified verdict";
  require (Checker.check_field_with_evidence schema evidence_doc None =
           Checker.check_field schema evidence_doc)
    "missing evidence changed the witness document verdict";
  require (not (F.has_candidates_with_evidence (i 65537) evidence_doc
                  (Some (i 3, List.init 15 (fun _ -> i 2)))))
    "invalid evidence selected the witness document";
  let composite_equality, composite_witness = witness_fixture (i 4) in
  require (not (Witness.check_with_evidence composite_witness composite_equality
                  (Some (i 1, [i 3]))))
    "composite modulus was accepted with invalid evidence";
  let artifact_prime = Z.of_string
    "52435875175126190479447740508185965837690552500527637822603658699938581184513" in
  let artifact_equality, artifact_witness = witness_fixture artifact_prime in
  let artifact_factors = List.init 32 (fun _ -> i 2) @
    List.map i [3; 11; 19; 10177; 906349; 906349; 2508409; 125527;
                859267; 2529403; 52437899; 254760293; 254760293] in
  require (Witness.check_with_evidence artifact_witness artifact_equality
             (Some (i 7, artifact_factors)))
    "255-bit primality evidence did not enable witness replay";
  require (Replay.pac_with_evidence artifact_prime artifact_witness artifact_equality
             (Some (i 7, artifact_factors)))
    "255-bit primality evidence did not enable PAC replay";
  let artifact_clause =
    A.App (R.or_decl [artifact_equality; R.false_expr], [artifact_equality; R.false_expr]) in
  let artifact_negated = R.mk_not_expr artifact_clause in
  let artifact_entry = { P.rule = U.FiniteFieldPac artifact_witness;
                         formula = artifact_clause; premise_ids = [] } in
  let artifact_doc = { doc with P.assertions = [artifact_negated];
    entries = [artifact_entry; { asserted with P.formula = artifact_negated }; resolution] } in
  require (Root.check_root_document_epsilon schema
             (F.augment_with_evidence artifact_prime artifact_doc (Some (i 7, artifact_factors)))
           = Root.RootCertified)
    "255-bit evidence did not certify the witness document";
  require (Checker.check_field_with_evidence schema artifact_doc (Some (i 7, artifact_factors))
           = Root.RootCertified)
    "evidence-aware checker did not certify the 255-bit witness document";
  let composite = i 4 in
  let composite_field = A.SortApp (A.FiniteFieldSymbol composite, []) in
  let cnum n = A.App (decl "ff" [] composite_field (Some (i 300)) [composite; i n], []) in
  let composite_eq = R.mk_eq_expr (cnum 0) (cnum 1) in
  let composite_cert = { FC.pac_premises = [composite_eq];
    pac_nodes = [FC.PacInput (i 0); FC.PacMul (i 0, cnum 3, [])];
    pac_root = i 1; pac_support = [i 0] } in
  let composite_clause = R.mk_not_expr composite_eq in
  require (SortedField.check composite_cert composite_clause &&
           not (Witness.check composite_cert composite_clause) &&
           Replay.pac composite composite_cert composite_clause &&
           Replay.pac_with_evidence composite composite_cert composite_clause (Some (i 1, [])))
    "existing composite-modulus PAC behavior changed";
  let prime = i 251 in
  let field = A.SortApp (A.FiniteFieldSymbol prime, []) in
  let var name = A.App (decl name [] field None [], []) in
  let number n = A.App (decl "ff" [] field (Some (i 300)) [prime; i n], []) in
  let plus x y = A.App (decl "ff.add" [field; field] field (Some (i 301)) [prime], [x; y]) in
  let a = var "a" and b = var "b" in
  let equality = R.mk_eq_expr (plus a b) (plus (plus a (number 0)) b) in
  let premise = R.mk_not_expr equality in
  let minus_one = number 250 in
  let witness = { FC.pac_premises = [premise];
    pac_nodes = [FC.PacInput (i 3); FC.PacInput (i 0);
      FC.PacMul (i 1, minus_one, [i 5]); FC.PacAdd (i 0, i 2);
      FC.PacInput (i 2); FC.PacMul (i 4, number 1, [i 5]); FC.PacAdd (i 3, i 5);
      FC.PacInput (i 1); FC.PacMul (i 7, number 1, [i 5]); FC.PacAdd (i 6, i 8);
      FC.PacMul (i 9, minus_one, [])];
    pac_root = i 10; pac_support = [i 0] } in
  let clause = A.App (R.or_decl [equality; R.false_expr], [equality; R.false_expr]) in
  require (not (Replay.clause prime clause) && not (SortedField.check witness clause) &&
           Replay.pac prime witness clause)
    "witness PAC was not recognized independently of the earlier checkers";
  let witness_entry = { P.rule = U.FiniteFieldPac witness; formula = clause; premise_ids = [] } in
  let neg_clause = R.mk_not_expr clause in
  let witness_doc = { doc with assertions = [neg_clause];
    entries = [witness_entry; { asserted with P.formula = neg_clause }; resolution] } in
  require (Root.check_root_document_epsilon schema witness_doc <> Root.RootCertified)
    "witness PAC proof was already certified before field replay";
  require (Checker.check_field schema witness_doc = Root.RootCertified)
    "witness PAC proof was not certified by field replay";
  print_endline "finite-field document replay tests passed"
