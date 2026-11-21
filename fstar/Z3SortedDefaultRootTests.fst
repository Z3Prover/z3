module Z3SortedDefaultRootTests

open Z3AstTheory
module U = Z3UnifiedProof
module P = Z3ProofDocument
module I = Z3ProofIndex
module IT = Z3IdTable
module D = Z3DefinitionRecognition
module R = Z3ClauseSyntax
module SC = Z3SortedRelational
module Replay = Z3SortedScopedReplay
module Root = Z3SortedDefaultRoot
module Cases = Z3SortedRelationalTests
module SyntaxCases = Z3ModusPonensSyntaxTests
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module L = FStar.List.Tot

let implication = App SyntaxCases.implies_decl [Cases.p; R.false_expr]
let asserted_p : P.entry = { P.rule = U.Asserted; P.formula = Cases.p; P.premise_ids = [] }
let asserted_implication : P.entry = { P.rule = U.Asserted; P.formula = implication; P.premise_ids = [] }
let mp : P.entry = { P.rule = U.ModusPonens; P.formula = R.false_expr; P.premise_ids = [0; 1] }
let inputs = [U.Holds Cases.p; U.Holds implication]
let fp : U.checked_fact = { U.conclusion = U.Holds Cases.p; U.hypotheses = [] }
let fi : U.checked_fact = { U.conclusion = U.Holds implication; U.hypotheses = [] }
let ff : U.checked_fact = { U.conclusion = U.Holds R.false_expr; U.hypotheses = [] }
let t1 = IT.put IT.empty 0 fp
let t2 = IT.put t1 1 fi
let t3 = IT.put t2 2 ff
let doc : P.document = {
  P.declarations = []; P.expressions = []; P.assertions = [Cases.p; implication];
  P.entries = [asserted_p; asserted_implication; mp]; P.root = 2;
}

let supported ()
  : Lemma (Replay.entries_supported Cases.scope false [] doc.P.entries) =
  let at (cache:IT.t U.checked_fact) (e:P.entry) (node:U.proof_node)
    : Lemma (L.mem e doc.P.entries /\ P.prepare_entry_table false [] cache e == Some node ==>
             Replay.node_supported Cases.scope node) =
    I.lemma_opt_map_tail (IT.find cache) [0; 1];
    match I.opt_map (IT.find cache) [0; 1] with
    | Some _ -> ()
    | None -> () in
  FStar.Classical.forall_intro_3 at

let refutation (#base:sort -> Type0) (s:S.checked_schema)
               (bc:S.boolean_carrier base) (eq:T.scalar_model base)
               (other:V.interpretation base (S.signature s))
               (rho:V.environment base (S.signature s) Cases.scope)
  : Lemma (requires T.truth_at s bc eq other Cases.scope rho Cases.p /\
                    T.truth_at s bc eq other Cases.scope rho implication)
          (ensures False) =
  IT.lemma_find_put t1 1 fi 0;
  IT.lemma_find_put t1 1 fi 1;
  IT.lemma_find_put IT.empty 0 fp 0;
  IT.lemma_find_put t2 2 ff 2;
  I.lemma_opt_map_tail (IT.find t2) [0; 1];
  assert (I.opt_map_tail (IT.find t2) [0; 1] == Some [fp; fi]);
  supported ();
  let input_sound (j:U.judgment)
    : Lemma (P.linear_lookup inputs j ==> SC.judgment_holds s bc eq other Cases.scope rho j) = () in
  FStar.Classical.forall_intro input_sound;
  assert_norm (P.check_entry_table [] true false [] inputs (P.linear_lookup inputs) IT.empty asserted_p ==
               Some (fp, 0));
  assert_norm (P.check_entry_table [] true false [] inputs (P.linear_lookup inputs) t1 asserted_implication ==
               Some (fi, 0));
  assert (P.prepare_entry_table false [] t2 mp ==
          Some { U.kind = U.ModusPonens; conclusion = U.Holds R.false_expr; premises = [fp; fi] });
  assert_norm (U.check_node_with_membership [] true inputs (P.linear_lookup inputs)
                 { U.kind = U.ModusPonens; conclusion = U.Holds R.false_expr; premises = [fp; fi] } ==
               Some (ff, 0));
  assert (P.check_entry_table [] true false [] inputs (P.linear_lookup inputs) t2 mp == Some (ff, 0));
  assert (P.diagnose_entries_using (P.checker_using D.linear_expander) [] false [] inputs
            (P.linear_lookup inputs) IT.empty 0 0 [] doc.P.entries ==
          P.EntriesChecked t3 0 []);
  assert (P.diagnose_prepared_document_using D.linear_expander P.linear_lookup doc false [] inputs [] ==
          P.DocumentChecked 0 []);
  assert_norm (P.prepare_skolem_context [] doc.P.assertions doc.P.assertions doc.P.entries == Some []);
  Root.lemma_diagnose_inputs P.linear_lookup doc false [] inputs doc.P.assertions [];
  Root.lemma_inputs_refutation s bc eq other Cases.scope rho P.linear_lookup doc false [] inputs doc.P.assertions [] []
