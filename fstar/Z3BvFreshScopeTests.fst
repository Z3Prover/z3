module Z3BvFreshScopeTests

open Z3AstTheory
module B = Z3BvSyntax
module F = Z3BvFreshSyntax
module S = Z3BvFreshScope
module R = Z3ClauseSyntax

let symbol (name:string) (range:sort) : func_decl = {
  decl_name = name; domain = []; range = range; interp = None; int_params = [];
}
let bits = [symbol "b0" bool_sort; symbol "b1" bool_sort; symbol "b2" bool_sort]
let constructor = match B.word (F.atoms bits) with App f _ -> f | _ -> symbol "bad" bool_sort
let reconstruction : F.reconstruction = {
  F.width = 3; F.original = symbol "word" (B.bv_sort 3);
  F.constructor = constructor; F.symbols = bits;
}
let equation = R.mk_eq_expr (F.source reconstruction) (F.word reconstruction)
let invalid = { reconstruction with F.symbols = [symbol "b0" bool_sort; symbol "b0" bool_sort; symbol "b2" bool_sort] }

let valid_projections_are_constructed ()
  : Lemma (F.check_context [] [equation] == Some [reconstruction] /\
           S.constructed_definitions (F.projection_definitions [reconstruction]) /\
           not (F.valid invalid)) =
  assert_norm (F.check_context [] [equation] == Some [reconstruction] /\ not (F.valid invalid));
  S.lemma_projections_constructed [reconstruction]
