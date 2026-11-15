module Z3ModusPonensSyntaxTests

open Z3AstTheory
module U = Z3UnifiedProofSyntax
module R = Z3ClauseSyntax
module M = Z3ModusPonensSyntax

let p = Var 0 bool_sort
let q = Var 1 bool_sort
let implies_decl : func_decl = {
  decl_name = "=>"; domain = [bool_sort; bool_sort]; range = bool_sort;
  interp = Some Z3OperatorTags.op_implies; int_params = [];
}
let implication = App implies_decl [p; q]

let recognizer ()
  : Lemma (M.step U.ModusPonens (U.Holds q) [U.Holds p; U.Holds implication] /\
           M.step U.ModusPonens (U.Holds q) [U.Holds p; U.Equal p q] /\
           M.step U.ObservationalMP (U.Holds q) [U.Holds p; U.Observational p q] /\
           not (M.step U.ModusPonens (U.Holds p) [U.Holds p; U.Holds implication]) /\
           not (M.step U.ObservationalMP (U.Holds p) [U.Holds p; U.Observational p q]) /\
           not (M.step U.ModusPonens (U.Holds q) [U.Holds p])) =
  assert_norm (M.step U.ModusPonens (U.Holds q) [U.Holds p; U.Holds implication] /\
               M.step U.ModusPonens (U.Holds q) [U.Holds p; U.Equal p q] /\
               M.step U.ObservationalMP (U.Holds q) [U.Holds p; U.Observational p q] /\
               not (M.step U.ModusPonens (U.Holds p) [U.Holds p; U.Holds implication]) /\
               not (M.step U.ObservationalMP (U.Holds p) [U.Holds p; U.Observational p q]) /\
               not (M.step U.ModusPonens (U.Holds q) [U.Holds p]))
