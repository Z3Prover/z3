module Z3QuantifierNnfSyntax

open Z3AstTheory

let dual (kind:quantifier_kind) : quantifier_kind =
  match kind with Forall_k -> Exists_k | Exists_k -> Forall_k | Lambda_k -> Lambda_k
