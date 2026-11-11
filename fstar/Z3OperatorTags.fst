module Z3OperatorTags

open Z3AstTheory

(* Checker transport tags, not the native Z3 decl_kind enumeration.
   Keep this vocabulary independent of concrete semantic carriers. *)
let op_not : decl_kind = 1
let op_plus : decl_kind = 2
let op_select : decl_kind = 3
let op_store : decl_kind = 4
let op_bvand : decl_kind = 5
let op_concat : decl_kind = 6
let op_eq : decl_kind = 7
let op_true : decl_kind = 8
let op_false : decl_kind = 9
let op_num_int : decl_kind = 10
let op_num_bv : decl_kind = 11
let op_seq_unit : decl_kind = 12
let op_and : decl_kind = 13
let op_or : decl_kind = 14
let op_implies : decl_kind = 15
let op_oeq : decl_kind = 16
let op_mul : decl_kind = 17
let op_array_ext : decl_kind = 18
let op_ite : decl_kind = 19
let op_xor : decl_kind = 20
let op_distinct : decl_kind = 21
let op_num_rational : decl_kind = 22
let op_arith_add : decl_kind = 23
let op_arith_mul : decl_kind = 24
let op_arith_sub : decl_kind = 25
let op_arith_div : decl_kind = 26
let op_arith_le : decl_kind = 27
let op_arith_lt : decl_kind = 28
let op_arith_ge : decl_kind = 29
let op_arith_gt : decl_kind = 30
let op_to_real : decl_kind = 31
let op_const_array : decl_kind = 32
