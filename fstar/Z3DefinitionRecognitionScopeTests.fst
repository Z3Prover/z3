module Z3DefinitionRecognitionScopeTests

open Z3AstTheory
module Def = Z3DefinitionRecognition
module Scope = Z3DefinitionRecognitionScope
module R = Z3ClauseSyntax
module A = Z3ArraySyntax

let symbol (name:string) : func_decl = {
  decl_name = name; domain = []; range = bool_sort; interp = None; int_params = [];
}
let guard = App (symbol "guard") []
let name = App (symbol "choice") []
let first_clause =
  let args = [R.mk_not_expr guard; R.mk_eq_expr name R.true_expr] in
  App (R.or_decl args) args
let second_clause =
  let args = [guard; R.mk_eq_expr name R.false_expr] in
  App (R.or_decl args) args
let definition : Def.definition = {
  Def.symbol = symbol "choice"; Def.variables = [];
  Def.body = App (A.term_ite_decl bool_sort) [guard; R.true_expr; R.false_expr];
}

let paired_axiom_provenance ()
  : Lemma (Def.axiom_definition first_clause [second_clause] == Some definition /\
           Scope.constructed definition) =
  assert_norm (Def.axiom_definition first_clause [second_clause] == Some definition);
  Scope.lemma_axiom_constructed first_clause [second_clause] definition

let direct_definition_provenance ()
  : Lemma (Def.definition_of (R.mk_eq_expr name R.true_expr) ==
             Some { Def.symbol = symbol "choice"; Def.variables = []; Def.body = R.true_expr } /\
           Scope.constructed { Def.symbol = symbol "choice"; Def.variables = []; Def.body = R.true_expr }) =
  assert_norm (Def.definition_of (R.mk_eq_expr name R.true_expr) ==
               Some { Def.symbol = symbol "choice"; Def.variables = []; Def.body = R.true_expr });
  Scope.lemma_definition_constructed (R.mk_eq_expr name R.true_expr)
    { Def.symbol = symbol "choice"; Def.variables = []; Def.body = R.true_expr }
