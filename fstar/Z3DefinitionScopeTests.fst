module Z3DefinitionScopeTests

open Z3AstTheory
module D = Z3ExprScope
module Def = Z3DefinitionRecognition
module R = Z3ClauseSyntax
module S = Z3DefinitionScope
module L = FStar.List.Tot
module P = Z3DocumentPreparation
module U = Z3UnifiedProofSyntax
module A = Z3ArraySyntax
module BF = Z3BvFreshSyntax
module BW = Z3BvSyntax
module BV = Z3BvSyntax

let int_sort = SortApp IntSymbol []
let symbol : func_decl = {
  decl_name = "defined";
  domain = [int_sort; bool_sort];
  range = bool_sort;
  interp = None;
  int_params = [];
}
let templates = [Var 1 int_sort; Var 0 bool_sort]
let body = Quantifier Forall_k [bool_sort] bool_sort
  (R.mk_eq_expr (Var 2 int_sort) (Var 2 int_sort))
let definition : Def.definition = {
  Def.symbol = symbol;
  Def.variables = [1; 0];
  Def.body = body;
}
let source = App symbol [Var 0 int_sort; R.true_expr]
let expected = Quantifier Forall_k [bool_sort] bool_sort
  (R.mk_eq_expr (Var 1 int_sort) (Var 1 int_sort))

let defining_formula = Quantifier Forall_k [int_sort; bool_sort] bool_sort
  (R.mk_eq_expr (App symbol templates) body)
let defining_document : P.document = {
  P.declarations = [symbol];
  P.expressions = [];
  P.assertions = [];
  P.entries = [{ P.rule = U.DefinitionIntroduction;
                 P.formula = defining_formula; P.premise_ids = [] }];
  P.root = 0;
}

let collected_definition_is_scoped ()
  : Lemma (P.document_definitions defining_document == Some [definition] /\
           S.definition_scopes [definition]) =
  assert_norm (P.reconstruction_equations defining_document.P.entries [] == []);
  assert_norm (P.document_definitions defining_document == Some [definition]);
  S.lemma_document_definitions defining_document [definition]

let bool_symbol (name:string) : func_decl = {
  decl_name = name; domain = []; range = bool_sort; interp = None; int_params = [];
}
let guard = App (bool_symbol "guard") []
let name = App (bool_symbol "choice") []
let first_clause =
  let args = [R.mk_not_expr guard; R.mk_eq_expr name R.true_expr] in
  App (R.or_decl args) args
let second_clause =
  let args = [guard; R.mk_eq_expr name R.false_expr] in
  App (R.or_decl args) args
let paired_definition : Def.definition = {
  Def.symbol = bool_symbol "choice"; Def.variables = [];
  Def.body = App (A.term_ite_decl bool_sort) [guard; R.true_expr; R.false_expr];
}
let paired_document : P.document = {
  P.declarations = [bool_symbol "guard"; bool_symbol "choice"];
  P.expressions = []; P.assertions = [];
  P.entries = [
    { P.rule = U.DefAxiom; P.formula = first_clause; P.premise_ids = [] };
    { P.rule = U.DefAxiom; P.formula = second_clause; P.premise_ids = [] }
  ];
  P.root = 1;
}

let paired_axioms_collect_a_scoped_definition ()
  : Lemma (Def.paired_definition first_clause [second_clause] == Some paired_definition /\
           P.document_definitions paired_document == Some [paired_definition] /\
           S.definition_scopes [paired_definition]) =
  assert_norm (Def.paired_definition first_clause [second_clause] == Some paired_definition);
  assert_norm (P.reconstruction_equations paired_document.P.entries [] == []);
  assert_norm (P.document_definitions paired_document == Some [paired_definition]);
  S.lemma_document_definitions paired_document [paired_definition]

let original : func_decl = {
  decl_name = "word"; domain = []; range = BV.bv_sort 1; interp = None; int_params = [];
}
let bit = bool_symbol "bit"
let reconstructed_word = BW.word [App bit []]
let reconstruction : expr = R.mk_eq_expr (App original []) reconstructed_word
let projection : Def.definition = {
  Def.symbol = bit; Def.variables = [];
  Def.body = BW.projection 1 (App original []) 0;
}
let reconstruction_document : P.document = {
  P.declarations = [original; bit];
  P.expressions = []; P.assertions = [];
  P.entries = [{ P.rule = U.RewriteRule; P.formula = reconstruction; P.premise_ids = [] }];
  P.root = 0;
}

let reconstructed_projection_is_scoped ()
  : Lemma (P.reconstruction_equations reconstruction_document.P.entries [] <> [] /\
           P.document_definitions reconstruction_document == Some [projection] /\
           S.definition_scopes [projection]) =
  assert_norm (P.reconstruction_equations reconstruction_document.P.entries [] <> []);
  assert_norm (P.document_definitions reconstruction_document == Some [projection]);
  S.lemma_document_definitions reconstruction_document [projection]

let original3 : func_decl = { original with range = BV.bv_sort 3 }
let bits3 = [bool_symbol "bit0"; bool_symbol "bit1"; bool_symbol "bit2"]
let equation3 = R.mk_eq_expr (App original3 []) (BW.word (BF.atoms bits3))
let document3 : P.document = {
  reconstruction_document with
  P.entries = [{ P.rule = U.RewriteRule; P.formula = equation3; P.premise_ids = [] }]
}
let projections3 = L.rev (BF.bit_definitions 3 (App original3 []) 0 bits3)

let multi_bit_projections_are_scoped ()
  : Lemma (P.reconstruction_equations document3.P.entries [] <> [] /\
           P.document_definitions document3 == Some projections3 /\
           S.definition_scopes projections3) =
  assert_norm (P.reconstruction_equations document3.P.entries [] <> []);
  assert_norm (P.document_definitions document3 == Some projections3);
  S.lemma_document_definitions document3 projections3

let constructed_definition_expands_under_binder ()
  : Lemma (Def.make_definition [bool_sort; int_sort] (App symbol templates) body == Some definition /\
           D.scoped [int_sort] source /\ Def.expand 1 [definition] source == Some expected /\
           D.scoped [int_sort] expected /\ get_sort expected == get_sort source) =
  assert_norm (Def.make_definition [bool_sort; int_sort] (App symbol templates) body == Some definition);
  assert_norm (D.scoped [int_sort] source /\ Def.expand 1 [definition] source == Some expected);
  let at (d:Def.definition)
    : Lemma (L.mem d [definition] ==> S.constructed d) =
    if L.mem d [definition] then
      S.lemma_make_constructed [bool_sort; int_sort] (App symbol templates) body d in
  FStar.Classical.forall_intro at;
  S.lemma_constructed_scopes [definition];
  S.lemma_expand_scope 1 [definition] [int_sort] source expected

let malformed_argument_needs_scope_precondition ()
  : Lemma (
      let bad = App symbol [Var 0 bool_sort; R.true_expr] in
      let result = Quantifier Forall_k [bool_sort] bool_sort
        (App (R.eq_decl int_sort) [Var 1 bool_sort; Var 1 bool_sort]) in
      not (D.scoped [bool_sort] bad) /\ Def.expand 1 [definition] bad == Some result /\
      not (D.scoped [bool_sort] result)) =
  assert_norm (
    let bad = App symbol [Var 0 bool_sort; R.true_expr] in
    let result = Quantifier Forall_k [bool_sort] bool_sort
      (App (R.eq_decl int_sort) [Var 1 bool_sort; Var 1 bool_sort]) in
    not (D.scoped [bool_sort] bad) /\ Def.expand 1 [definition] bad == Some result /\
    not (D.scoped [bool_sort] result))
