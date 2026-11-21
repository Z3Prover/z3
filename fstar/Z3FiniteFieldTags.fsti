module Z3FiniteFieldTags

open Z3AstTheory

val op_ff_num : x:decl_kind{x == 300}
val op_ff_add : x:decl_kind{x == 301}
val op_ff_mul : x:decl_kind{x == 302}
val op_ff_neg : x:decl_kind{x == 303}
val op_ff_bitsum : x:decl_kind{x == 304}
