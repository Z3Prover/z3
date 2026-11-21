module Z3LpIntegerCutSyntax

open Z3AstTheory
module A = Z3LinearArithmeticAst

type step = {
  bound: expr;
  weights: list A.coefficient;
}

type certificate = {
  steps: list step;
  refutation: list A.coefficient;
}

val synthesize : conclusion:expr -> facts:list expr -> Tot (option certificate)
