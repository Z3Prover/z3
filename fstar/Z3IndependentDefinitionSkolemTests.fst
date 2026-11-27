module Z3IndependentDefinitionSkolemTests

open Z3AstTheory
module X = Z3IndependentDefinitionModelTests
module C = Z3IndependentDefinitionContextTests
module Context = Z3IndependentDefinitionContext
module Combined = Z3IndependentDefinitionSkolem
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module Root = Z3SortedRootDocument
module SP = Z3SortedProof
module E = Z3SortedSkolem
module DS = Z3SortedDependentSkolem
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module O = Z3ObservationalSyntax
module L = FStar.List.Tot

let integer = TR.int_s
let symbol (name:string) (ds:list sort) (r:sort) : func_decl =
  { decl_name = name; domain = ds; range = r; interp = None; int_params = [] }
let constant = symbol "sk!closed" [] integer
let predicate = symbol "predicate" [integer] bool_sort
let relation = symbol "relation" [integer; integer; integer] bool_sort
let witness = symbol "sk!dependent" [integer] integer
let closed_source = Quantifier Exists_k [integer] bool_sort (App predicate [Var 0 integer])
let closed_target = App predicate [App constant []]
let dependent_source = Quantifier Exists_k [integer] bool_sort
  (App relation [Var 0 integer; Var 1 integer; App constant []])
let dependent_target = App relation [App witness [Var 0 integer]; Var 0 integer; App constant []]
let bound_source = Quantifier Forall_k [integer] bool_sort dependent_source
let bound_target = Quantifier Forall_k [integer] bool_sort dependent_target
let certificate : U.binder_certificate = {
  U.binder_entries = [
    { U.binder_name = "sk"; binder_formula = O.mk_oeq_expr dependent_source dependent_target;
      binder_premises = []; binder_sorts = None };
    { U.binder_name = "nnf-pos"; binder_formula = O.mk_oeq_expr bound_source bound_target;
      binder_premises = [0]; binder_sorts = Some [integer] }
  ];
  binder_root = 1;
}
let doc : P.document = {
  P.declarations = []; expressions = []; assertions = X.inputs;
  entries = [
    { P.rule = U.Skolemization; formula = O.mk_oeq_expr closed_source closed_target; premise_ids = [] };
    { P.rule = U.QuantifierIntroduction certificate;
      formula = O.mk_oeq_expr bound_source bound_target; premise_ids = [] }
  ];
  root = 0;
}

let contexts_and_gate ()
  : Lemma (
    L.length (SP.epsilon_context X.schema doc) == 1 /\
    L.length (SP.dependent_context X.schema doc (SP.epsilon_context X.schema doc)) == 1 /\
    Combined.compatible X.schema doc [C.old_item]) =
  assert_norm (L.length (SP.epsilon_context X.schema doc) == 1);
  assert_norm (L.length (SP.dependent_context X.schema doc (SP.epsilon_context X.schema doc)) == 1);
  assert_norm (Combined.compatible X.schema doc [C.old_item])

let collision_relation = symbol "collision" [bool_sort; X.domain] bool_sort
let collision_source = Quantifier Exists_k [bool_sort] bool_sort
  (App collision_relation [Var 0 bool_sort; Var 1 X.domain])
let collision_target = App collision_relation [App X.symbol [Var 0 X.domain]; Var 0 X.domain]
let collision_bound_source = Quantifier Forall_k [X.domain] bool_sort collision_source
let collision_bound_target = Quantifier Forall_k [X.domain] bool_sort collision_target
let collision_certificate : U.binder_certificate = {
  U.binder_entries = [
    { U.binder_name = "sk"; binder_formula = O.mk_oeq_expr collision_source collision_target;
      binder_premises = []; binder_sorts = None };
    { U.binder_name = "nnf-pos";
      binder_formula = O.mk_oeq_expr collision_bound_source collision_bound_target;
      binder_premises = [0]; binder_sorts = Some [X.domain] }
  ];
  binder_root = 1;
}
let collision_doc : P.document = {
  doc with P.entries = [
    { P.rule = U.QuantifierIntroduction collision_certificate;
      formula = O.mk_oeq_expr collision_bound_source collision_bound_target; premise_ids = [] }
  ]
}

let collision_rejected ()
  : Lemma (
    L.length (SP.dependent_context X.schema collision_doc
      (SP.epsilon_context X.schema collision_doc)) == 1 /\
    not (Combined.compatible X.schema collision_doc [C.old_item])) =
  assert_norm (L.length (SP.dependent_context X.schema collision_doc
    (SP.epsilon_context X.schema collision_doc)) == 1);
  assert_norm (not (Combined.compatible X.schema collision_doc [C.old_item]))

let inhabited_combined_model ()
  : Lemma (
    let original = TR.standard X.uninterpreted X.schema X.symbols in
    let result = Combined.build X.schema (TR.booleans X.uninterpreted)
      (SR.root_scalars X.uninterpreted) (Root.root_choice X.uninterpreted X.schema)
      doc [C.old_item] original in
    TR.root_model X.uninterpreted X.schema result /\
    T.truths X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      result (Context.formulas X.schema doc.P.assertions [C.old_item]) /\
    T.truths X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      result (SP.epsilon_equations X.schema (SP.epsilon_context X.schema doc) doc.P.entries) /\
    T.truths X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      result (DS.closures X.schema (SP.dependent_context X.schema doc (SP.epsilon_context X.schema doc)))) =
  let original = TR.standard X.uninterpreted X.schema X.symbols in
  TR.lemma_standard_root X.uninterpreted X.schema X.symbols;
  Root.lemma_forall_model X.uninterpreted X.schema original;
  Root.lemma_exists_model X.uninterpreted X.schema original;
  assert_norm (Context.ordered X.schema doc.P.assertions [C.old_item]);
  contexts_and_gate ();
  Combined.lemma_build X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    (Root.root_choice X.uninterpreted X.schema) doc [C.old_item] original;
  Combined.lemma_build_root X.uninterpreted X.schema (TR.booleans X.uninterpreted)
    (SR.root_scalars X.uninterpreted) (Root.root_choice X.uninterpreted X.schema)
    doc [C.old_item] original
