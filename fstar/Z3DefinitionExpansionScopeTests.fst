module Z3DefinitionExpansionScopeTests

open Z3AstTheory
module D = Z3ExprScope
module Def = Z3DefinitionSyntax
module Scope = Z3DefinitionExpansionScope
module R = Z3ClauseSyntax
module L = FStar.List.Tot

let int_sort = SortApp IntSymbol []
let symbol : func_decl = {
  decl_name = "defined"; domain = [int_sort; bool_sort]; range = bool_sort;
  interp = None; int_params = [];
}
let templates = [Var 1 int_sort; Var 0 bool_sort]
let body = Quantifier Forall_k [bool_sort] bool_sort
  (R.mk_eq_expr (Var 2 int_sort) (Var 2 int_sort))
let definition : Def.definition = {
  Def.symbol = symbol; Def.variables = [1; 0]; Def.body = body;
}
let source = App symbol [Var 0 int_sort; R.true_expr]
let expected = Quantifier Forall_k [bool_sort] bool_sort
  (R.mk_eq_expr (Var 1 int_sort) (Var 1 int_sort))

let scoped_expansion_with_any_cache_hash (hash:(nat & expr) -> nat)
  : Lemma (Def.expand 1 [definition] source == Some expected /\
           Def.memoized_expand hash 1 [definition] source == Some expected /\
           D.scoped [int_sort] expected /\ get_sort expected == get_sort source) =
  assert_norm (Def.make_definition [bool_sort; int_sort] (App symbol templates) body == Some definition);
  assert_norm (D.scoped [int_sort] source /\ Def.expand 1 [definition] source == Some expected);
  let at (d:Def.definition) : Lemma (L.mem d [definition] ==> Scope.constructed d) =
    if L.mem d [definition] then
      Scope.lemma_make_constructed [bool_sort; int_sort] (App symbol templates) body d in
  FStar.Classical.forall_intro at;
  Scope.lemma_constructed_scopes [definition];
  Scope.lemma_expand_scope 1 [definition] [int_sort] source expected
