module Z3QuantifierInstantiationTests

open Z3AstTheory
module C = Z3CanonicalOps
module R = Z3ClauseSyntax
module D = Z3ExprScope
module I = Z3QuantifierInstantiation
module U = Z3UnifiedProof
module P = Z3ProofDocument
module Q = Z3SortedQuantifier
module G = Z3GroundScope
module GS = Z3DocumentScope
module L = FStar.List.Tot
module Def = Z3Definitions
module DS = Z3DefinitionScope

let lemma_ground_document_term (doc:P.document) (e:expr)
  : Lemma (requires P.ground_exprs doc.P.expressions /\ G.listed doc.P.expressions e)
          (ensures D.scoped [] e) =
  GS.lemma_ground_term doc.P.expressions e

let lemma_prepared_entry_formula_scoped
    (doc:P.document) (defs:list Def.definition) (premises:option (list U.checked_fact))
    (entry:P.entry) (transform:Def.expander)
  : Lemma (
      requires Some? (P.prepare_entry_from transform
                       (not (P.ground_exprs doc.P.expressions)) defs premises entry) /\
               (not (P.ground_exprs doc.P.expressions) \/
                G.listed doc.P.expressions entry.P.formula))
      (ensures D.scoped [] entry.P.formula) =
  if P.ground_exprs doc.P.expressions then
    lemma_ground_document_term doc entry.P.formula

let lemma_prepared_entry_expansion_scoped
    (doc:P.document) (defs:list Def.definition) (premises:option (list U.checked_fact))
    (entry:P.entry) (transform:Def.expander) (result:expr)
  : Lemma (
      requires DS.definition_scopes defs /\
               Some? (P.prepare_entry_from transform
                       (not (P.ground_exprs doc.P.expressions)) defs premises entry) /\
               (not (P.ground_exprs doc.P.expressions) \/
                G.listed doc.P.expressions entry.P.formula) /\
               transform (L.length defs) defs entry.P.formula == Some result)
      (ensures D.scoped [] result /\ get_sort result == get_sort entry.P.formula) =
  lemma_prepared_entry_formula_scoped doc defs premises entry transform;
  DS.lemma_expand_scope (L.length defs) defs [] entry.P.formula result

let lemma_document_entry_expansion_scoped
    (doc:P.document) (defs:list Def.definition) (premises:option (list U.checked_fact))
    (entry:P.entry) (transform:Def.expander) (result:expr)
  : Lemma (
      requires P.document_definitions doc == Some defs /\
               Some? (P.prepare_entry_from transform
                       (not (P.ground_exprs doc.P.expressions)) defs premises entry) /\
               (not (P.ground_exprs doc.P.expressions) \/
                G.listed doc.P.expressions entry.P.formula) /\
               transform (L.length defs) defs entry.P.formula == Some result)
      (ensures D.scoped [] result /\ get_sort result == get_sort entry.P.formula) =
  DS.lemma_document_definitions doc defs;
  lemma_prepared_entry_expansion_scoped doc defs premises entry transform result

let forall_true = Quantifier Forall_k [] bool_sort R.true_expr
let malformed_or = App (C.or_decl 0) [App C.not_decl [forall_true]; R.true_expr]

let accepted_unscoped_instantiation ()
  : Lemma (I.check [] malformed_or /\ not (D.scoped [] malformed_or)) =
  assert_norm (I.check [] malformed_or /\ not (D.scoped [] malformed_or))

let malformed_node : U.proof_node = {
  U.kind = U.QuantifierInstantiation [];
  U.conclusion = U.Holds malformed_or;
  U.premises = [];
}

let malformed_document : P.document = {
  P.declarations = [];
  P.expressions = [];
  P.assertions = [R.mk_not_expr malformed_or];
  P.entries = [
    { P.rule = U.Asserted; P.formula = R.mk_not_expr malformed_or; P.premise_ids = [] };
    { P.rule = U.QuantifierInstantiation []; P.formula = malformed_or; P.premise_ids = [] };
    { P.rule = U.UnitResolution; P.formula = R.false_expr; P.premise_ids = [0; 1] }
  ];
  P.root = 2;
}

let accepted_unscoped_node_and_document ()
  : Lemma (U.check_node [] malformed_node ==
             Some ({ U.conclusion = U.Holds malformed_or; U.hypotheses = [] }, 0) /\
           not (Q.check [] malformed_or) /\
           P.check_document malformed_document == Some 0 /\
           P.check_document { malformed_document with P.expressions = [malformed_or] } == None /\
           P.check_document { malformed_document with P.expressions = [forall_true] } == None) =
  assert_norm (U.check_node [] malformed_node ==
                 Some ({ U.conclusion = U.Holds malformed_or; U.hypotheses = [] }, 0));
  assert_norm (not (Q.check [] malformed_or));
  assert_norm (P.check_document malformed_document == Some 0);
  assert_norm (P.check_document { malformed_document with P.expressions = [malformed_or] } == None);
  assert_norm (P.check_document { malformed_document with P.expressions = [forall_true] } == None)

let accepted_unscoped_indexed_document (hash:U.judgment -> nat)
  : Lemma (P.check_document_indexed hash malformed_document == Some 0 /\
           P.diagnostic_result (P.diagnose_document_indexed hash malformed_document) == Some 0) =
  accepted_unscoped_node_and_document ();
  P.lemma_check_document_indexed hash malformed_document;
  P.lemma_diagnose_document_indexed hash malformed_document

let complete_ground_table_scopes_terms ()
  : Lemma (
      let e = R.mk_not_expr R.true_expr in
      let doc = { malformed_document with P.expressions = [e; R.true_expr] } in
      P.ground_exprs doc.P.expressions /\ G.listed doc.P.expressions e /\ D.scoped [] e /\
      not (G.listed [malformed_or] malformed_or)) =
  let e = R.mk_not_expr R.true_expr in
  let doc = { malformed_document with P.expressions = [e; R.true_expr] } in
  assert_norm (P.ground_exprs doc.P.expressions /\ G.listed doc.P.expressions e);
  lemma_ground_document_term doc e;
  assert_norm (not (G.listed [malformed_or] malformed_or))
