(**
   The Z3 ML/Ocaml Interface.

   Copyright (C) 2012 Microsoft Corporation
   @author CM Wintersteiger (cwinter) 2012-12-17
*)

type context

type int_symbol
type string_symbol
type symbol = S_Int of int_symbol | S_Str of string_symbol

type ast 
type ast_vector 
type ast_map 

type sort = Sort of ast

type uninterpreted_sort = UninterpretedSort of sort
type bool_sort = BoolSort of sort
type array_sort = ArraySort of sort
type set_sort = SetSort of sort
type datatype_sort = DatatypeSort of sort
type relation_sort = RelationSort of sort
type finite_domain_sort = FiniteDomainSort of sort
type enum_sort = EnumSort of sort
type list_sort = ListSort of sort
type tuple_sort = TupleSort of sort
type arith_sort = ArithSort of sort
type bitvec_sort = BitVecSort of sort
type int_sort = IntSort of arith_sort
type real_sort = RealSort of arith_sort

type func_decl = FuncDecl of ast

type parameter =
    P_Int of int
  | P_Dbl of float
  | P_Sym of symbol
  | P_Srt of sort
  | P_Ast of ast
  | P_Fdl of func_decl
  | P_Rat of string

type params 
type param_descrs 

type expr = Expr of ast
type bool_expr = BoolExpr of expr
type arith_expr = ArithExpr of expr
type int_expr = IntExpr of arith_expr
type real_expr = RealExpr of arith_expr
type bitvec_expr = BitVecExpr of expr
type array_expr = ArrayExpr of expr
type datatype_expr = DatatypeExpr of expr
type int_num = IntNum of int_expr
type rat_num = RatNum of real_expr
type algebraic_num = AlgebraicNum of arith_expr
type bitvec_num = BitVecNum of bitvec_expr
type quantifier = Quantifier of expr
type pattern = Pattern of ast

type constructor 

type goal 

type model 
type func_interp 
type func_entry 

type probe 

type tactic 
type apply_result 

type solver 
type status = UNSATISFIABLE | UNKNOWN | SATISFIABLE

type statistics 
type statistics_entry

type fixedpoint 

val ast_of_sort : sort -> ast
val sort_of_uninterpreted_sort : uninterpreted_sort -> sort
val sort_of_bool_sort : bool_sort -> sort
val sort_of_array_sort : array_sort -> sort
val sort_of_set_sort : set_sort -> sort
val sort_of_datatype_sort : datatype_sort -> sort
val sort_of_relation_sort : relation_sort -> sort
val sort_of_finite_domain_sort : finite_domain_sort -> sort
val sort_of_enum_sort : enum_sort -> sort
val sort_of_list_sort : list_sort -> sort
val sort_of_tuple_sort : tuple_sort -> sort
val sort_of_arith_sort : arith_sort -> sort
val sort_of_bitvec_sort : bitvec_sort -> sort
val arith_sort_of_int_sort : int_sort -> arith_sort
val arith_sort_of_real_sort : real_sort -> arith_sort
val uninterpreted_sort_of_sort : sort -> uninterpreted_sort
val bool_sort_of_sort : sort -> bool_sort
val array_sort_of_sort : sort -> array_sort
val datatype_sort_of_sort : sort -> datatype_sort
val relation_sort_of_sort : sort -> relation_sort
val finite_domain_sort_of_sort : sort -> finite_domain_sort
val arith_sort_of_sort : sort -> arith_sort
val bitvec_sort_of_sort : sort -> bitvec_sort
val int_sort_of_arith_sort : arith_sort -> int_sort
val real_sort_of_arith_sort : arith_sort -> real_sort
val ast_of_func_decl : func_decl -> ast
val ast_of_expr : expr -> ast
val expr_of_bool_expr : bool_expr -> expr
val expr_of_arith_expr : arith_expr -> expr
val expr_of_bitvec_expr : bitvec_expr -> expr
val expr_of_array_expr : array_expr -> expr
val expr_of_datatype_expr : datatype_expr -> expr
val arith_expr_of_int_expr : int_expr -> arith_expr
val arith_expr_of_real_expr : real_expr -> arith_expr
val int_expr_of_int_num : int_num -> int_expr
val real_expr_of_rat_num : rat_num -> real_expr
val arith_expr_of_algebraic_num : algebraic_num -> arith_expr
val bitvec_expr_of_bitvec_num : bitvec_num -> bitvec_expr
val expr_of_quantifier : quantifier -> expr
val ast_of_pattern : pattern -> ast
val expr_of_ast : ast -> expr
val bool_expr_of_expr : expr -> bool_expr
val arith_expr_of_expr : expr -> arith_expr
val bitvec_expr_of_expr : expr -> bitvec_expr
val array_expr_of_expr : expr -> array_expr
val datatype_expr_of_expr : expr -> datatype_expr
val int_expr_of_arith_expr : arith_expr -> int_expr
val real_expr_of_arith_expr : arith_expr -> real_expr
val int_num_of_int_expr : int_expr -> int_num
val rat_num_of_real_expr : real_expr -> rat_num
val algebraic_num_of_arith_expr : arith_expr -> algebraic_num
val bitvec_num_of_bitvec_expr : bitvec_expr -> bitvec_num
val quantifier_of_expr : expr -> quantifier
val pattern_of_ast : ast -> pattern

module Log :
sig
  val open_ : string -> bool
  val close : unit
  val append : string -> unit
end

module Version :
sig
  val major : int
  val minor : int
  val build : int
  val revision : int
  val to_string : string
end

val mk_context : (string * string) list -> context

module Symbol :
sig
  val kind : symbol -> Z3enums.symbol_kind
  val is_int_symbol : symbol -> bool
  val is_string_symbol : symbol -> bool
  val get_int : int_symbol -> int
  val get_string : string_symbol -> string
  val to_string : symbol -> string
  val mk_int : context -> int -> symbol
  val mk_string : context -> string -> symbol
  val mk_ints : context -> int array -> symbol array
  val mk_strings : context -> string array -> symbol array
end

module AST :
sig

  module ASTVector :
  sig
    val get_size : ast_vector -> int
    val get : ast_vector -> int -> ast_vector
    val set : ast_vector -> int -> ast -> unit
    val resize : ast_vector -> int -> unit
    val push : ast_vector -> ast -> unit
    val translate : ast_vector -> context -> ast_vector
    val to_string : ast_vector -> string
  end

  module ASTMap :
  sig
    val contains : ast_map -> ast -> bool
    val find : ast_map -> ast -> ast_map
    val insert : ast_map -> ast -> ast -> unit
    val erase : ast_map -> ast -> unit
    val reset : ast_map -> unit
    val get_size : ast_map -> int
    val get_keys : ast_map -> ast_vector
    val to_string : ast_map -> string
  end

  val get_hash_code : ast -> int
  val get_id : ast -> int
  val get_ast_kind : ast -> Z3enums.ast_kind
  val is_expr : ast -> bool
  val is_var : ast -> bool
  val is_quantifier : ast -> bool
  val is_sort : ast -> bool
  val is_func_decl : ast -> bool
  val to_string : ast -> string
  val to_sexpr : ast -> string
  val ( = ) : ast -> ast -> bool
  val compare : ast -> ast -> int
  val ( < ) : ast -> ast -> int
  val translate : ast -> context -> ast
  val wrap : context -> Z3native.z3_ast -> ast
  val unwrap_ast : ast -> Z3native.ptr
end

module Sort :
sig
  val ( = ) : sort -> sort -> bool
  val get_id : sort -> int
  val get_sort_kind : sort -> Z3enums.sort_kind
  val get_name : sort -> symbol
  val to_string : sort -> string
  val mk_uninterpreted : context -> symbol -> uninterpreted_sort
  val mk_uninterpreted_s : context -> string -> uninterpreted_sort
end

module FuncDecl :
sig

  module Parameter :
  sig
    val get_kind : parameter -> Z3enums.parameter_kind
    val get_int : parameter -> int
    val get_float : parameter -> float
    val get_symbol : parameter -> symbol
    val get_sort : parameter -> sort
    val get_ast : parameter -> ast
    val get_func_decl : parameter -> string
  end

  val mk_func_decl : context -> symbol -> sort array -> sort -> func_decl
  val mk_func_decl_s : context -> string -> sort array -> sort -> func_decl
  val mk_fresh_func_decl : context -> string -> sort array -> sort -> func_decl
  val mk_const_decl : context -> symbol -> sort -> func_decl
  val mk_const_decl_s : context -> string -> sort -> func_decl
  val mk_fresh_const_decl : context -> string -> sort -> func_decl
  val ( = ) : func_decl -> func_decl -> bool
  val to_string : func_decl -> string
  val get_id : func_decl -> int
  val get_arity : func_decl -> int
  val get_domain_size : func_decl -> int
  val get_domain : func_decl -> sort array
  val get_range : func_decl -> sort
  val get_decl_kind : func_decl -> Z3enums.decl_kind
  val get_name : func_decl -> symbol
  val get_num_parameters : func_decl -> int
  val get_parameters : func_decl -> parameter list
  val apply : func_decl -> expr array -> expr
end

module Params :
sig

  module ParamDescrs :
  sig
    val validate : param_descrs -> params -> unit
    val get_kind : param_descrs -> symbol -> Z3enums.param_kind
    val get_names : param_descrs -> symbol array
    val get_size : param_descrs -> int
    val to_string : param_descrs -> string
  end

  val add_bool : params -> symbol -> bool -> unit
  val add_int : params -> symbol -> int -> unit
  val add_double : params -> symbol -> float -> unit
  val add_symbol : params -> symbol -> symbol -> unit
  val add_s_bool : params -> string -> bool -> unit
  val add_s_int : params -> string -> int -> unit
  val add_s_double : params -> string -> float -> unit
  val add_s_symbol : params -> string -> symbol -> unit
  val mk_params : context -> params
  val to_string : params -> string
end

module Expr :
sig
  val simplify : expr -> params option -> expr
  val get_simplify_help : context -> string
  val get_simplify_parameter_descrs : context -> param_descrs
  val get_func_decl : expr -> func_decl
  val get_bool_value : expr -> Z3enums.lbool
  val get_num_args : expr -> int
  val get_args : expr -> expr array
  val update : expr -> expr array -> expr
  val substitute : expr -> expr array -> expr array -> expr
  val substitute_one : expr -> expr -> expr -> expr
  val substitute_vars : expr -> expr array -> expr
  val translate : expr -> context -> expr
  val to_string : expr -> string
  val is_numeral : expr -> bool
  val is_well_sorted : expr -> bool
  val get_sort : expr -> sort
  val is_bool : expr -> bool
  val is_const : expr -> bool
  val is_true : expr -> bool
  val is_false : expr -> bool
  val is_eq : expr -> bool
  val is_distinct : expr -> bool
  val is_ite : expr -> bool
  val is_and : expr -> bool
  val is_or : expr -> bool
  val is_iff : expr -> bool
  val is_xor : expr -> bool
  val is_not : expr -> bool
  val is_implies : expr -> bool
  val is_label : expr -> bool
  val is_oeq : expr -> bool
  val mk_const : context -> symbol -> sort -> expr
  val mk_const_s : context -> string -> sort -> expr
  val mk_const_f : context -> func_decl -> expr
  val mk_fresh_const : context -> string -> sort -> expr
  val mk_app : context -> func_decl -> expr array -> expr
  val mk_numeral_string : context -> string -> sort -> expr
  val mk_numeral_int : context -> int -> sort -> expr
end

module Boolean :
sig
  val mk_sort : context -> bool_sort
  val mk_const : context -> symbol -> bool_expr
  val mk_const_s : context -> string -> bool_expr
  val mk_true : context -> bool_expr
  val mk_false : context -> bool_expr
  val mk_val : context -> bool -> bool_expr
  val mk_eq : context -> expr -> expr -> bool_expr
  val mk_distinct : context -> expr array -> bool_expr
  val mk_not : context -> bool_expr -> bool_expr
  val mk_ite : context -> bool_expr -> bool_expr -> bool_expr -> bool_expr
  val mk_iff : context -> bool_expr -> bool_expr -> bool_expr
  val mk_implies : context -> bool_expr -> bool_expr -> bool_expr
  val mk_xor : context -> bool_expr -> bool_expr -> bool_expr
  val mk_and : context -> bool_expr array -> bool_expr
  val mk_or : context -> bool_expr array -> bool_expr
end

module Quantifier :
sig

  module Pattern :
  sig
    val get_num_terms : pattern -> int
    val get_terms : pattern -> expr array
    val to_string : pattern -> string
  end

  val get_index : expr -> int
  val is_universal : quantifier -> bool
  val is_existential : quantifier -> bool
  val get_weight : quantifier -> int
  val get_num_patterns : quantifier -> int
  val get_patterns : quantifier -> pattern array
  val get_num_no_patterns : quantifier -> int
  val get_no_patterns : quantifier -> pattern array
  val get_num_bound : quantifier -> int
  val get_bound_variable_names : quantifier -> symbol array
  val get_bound_variable_sorts : quantifier -> sort array
  val get_body : quantifier -> bool_expr
  val mk_bound : context -> int -> sort -> expr
  val mk_pattern : context -> expr array -> pattern
  val mk_forall :
    context ->
    sort array ->
    symbol array ->
    expr ->
    int option ->
    pattern array ->
    expr array -> symbol option -> symbol option -> quantifier
  val mk_forall_const :
    context ->
    expr array ->
    expr ->
    int option ->
    pattern array ->
    expr array -> symbol option -> symbol option -> quantifier
  val mk_exists :
    context ->
    sort array ->
    symbol array ->
    expr ->
    int option ->
    pattern array ->
    expr array -> symbol option -> symbol option -> quantifier
  val mk_exists_const :
    context ->
    expr array ->
    expr ->
    int option ->
    pattern array ->
    expr array -> symbol option -> symbol option -> quantifier
  val mk_quantifier :
    context ->
    bool ->
    expr array ->
    expr ->
    int option ->
    pattern array ->
    expr array -> symbol option -> symbol option -> quantifier
end

module Array_ :
sig
  val mk_sort : context -> sort -> sort -> array_sort
  val is_store : expr -> bool
  val is_select : expr -> bool
  val is_constant_array : expr -> bool
  val is_default_array : expr -> bool
  val is_array_map : expr -> bool
  val is_as_array : expr -> bool
  val is_array : expr -> bool
  val get_domain : array_sort -> sort
  val get_range : array_sort -> sort
  val mk_const : context -> symbol -> sort -> sort -> array_expr
  val mk_const_s : context -> string -> sort -> sort -> array_expr
  val mk_select : context -> array_expr -> expr -> expr -> expr
  val mk_const_array : context -> sort -> expr -> expr
  val mk_map : context -> func_decl -> array_expr array -> expr
  val mk_term_array : context -> array_expr -> expr
end

module Set :
sig
  val is_union : expr -> bool
  val is_intersect : expr -> bool
  val is_difference : expr -> bool
  val is_complement : expr -> bool
  val is_subset : expr -> bool
  val mk_sort : context -> sort -> set_sort
  val mk_empty : context -> sort -> expr
  val mk_full : context -> sort -> expr
  val mk_set_add : context -> expr -> expr -> expr
  val mk_del : context -> expr -> expr -> expr
  val mk_union : context -> expr array -> expr
  val mk_intersection : context -> expr array -> expr
  val mk_difference : context -> expr -> expr -> expr
  val mk_complement : context -> expr -> expr
  val mk_membership : context -> expr -> expr -> expr
  val mk_subset : context -> expr -> expr -> expr
end

module FiniteDomain :
sig
  val mk_sort : context -> symbol -> int -> finite_domain_sort
  val mk_sort_s : context -> string -> int -> finite_domain_sort
  val is_finite_domain : expr -> bool
  val is_lt : expr -> bool
  val get_size : finite_domain_sort -> int
end

module Relation :
sig
  val is_relation : expr -> bool
  val is_store : expr -> bool
  val is_empty : expr -> bool
  val is_is_empty : expr -> bool
  val is_join : expr -> bool
  val is_union : expr -> bool
  val is_widen : expr -> bool
  val is_project : expr -> bool
  val is_filter : expr -> bool
  val is_negation_filter : expr -> bool
  val is_rename : expr -> bool
  val is_complement : expr -> bool
  val is_select : expr -> bool
  val is_clone : expr -> bool
  val get_arity : relation_sort -> int
  val get_column_sorts : relation_sort -> relation_sort array
end

module Datatype :
sig

  module Constructor :
  sig
    val get_n : constructor -> int
    val tester_decl : constructor -> func_decl
    val constructor_decl : constructor -> func_decl
    val accessor_decls : constructor -> func_decl array
    val get_num_fields : constructor -> int
    val get_constructor_decl : constructor -> func_decl
    val get_tester_decl : constructor -> func_decl
    val get_accessor_decls : constructor -> func_decl array
  end

  val mk_constructor : context -> symbol -> symbol -> symbol array -> sort array -> int array -> constructor
  val mk_constructor_s : context -> string -> symbol -> symbol array -> sort array -> int array -> constructor
  val mk_sort : context -> symbol -> constructor array -> datatype_sort
  val mk_sort_s : context -> string -> constructor array -> datatype_sort
  val mk_sorts : context -> symbol array -> constructor array array -> datatype_sort array
  val mk_sorts_s : context -> string array -> constructor array array -> datatype_sort array
  val get_num_constructors : datatype_sort -> int
  val get_constructors : datatype_sort -> func_decl array
  val get_recognizers : datatype_sort -> func_decl array
  val get_accessors : datatype_sort -> func_decl array array
end

module Enumeration :
sig
  val mk_sort : context -> symbol -> symbol array -> enum_sort
  val mk_sort_s : context -> string -> string array -> enum_sort
  val get_const_decls : enum_sort -> func_decl array
  val get_tester_decls : enum_sort -> func_decl array
end

module List_ :
sig
  val mk_sort : context -> symbol -> sort -> list_sort
  val mk_list_s : context -> string -> sort -> list_sort
  val get_nil_decl : list_sort -> func_decl
  val get_is_nil_decl : list_sort -> func_decl
  val get_cons_decl : list_sort -> func_decl
  val get_is_cons_decl : list_sort -> func_decl
  val get_head_decl : list_sort -> func_decl
  val get_tail_decl : list_sort -> func_decl
  val nil : list_sort -> expr
end

module Tuple :
sig
  val mk_sort :
    context -> symbol -> symbol array -> sort array -> tuple_sort
  val get_mk_decl : tuple_sort -> func_decl
  val get_num_fields : tuple_sort -> int
  val get_field_decls : tuple_sort -> func_decl array
end

module Arithmetic :
sig

  module Integer :
  sig
    val mk_sort : context -> int_sort
    val get_int : int_num -> int
    val to_string : int_num -> string
    val mk_int_const : context -> symbol -> int_expr
    val mk_int_const_s : context -> string -> int_expr
    val mk_mod : context -> int_expr -> int_expr -> expr
    val mk_rem : context -> int_expr -> int_expr -> expr
    val mk_int_numeral_s : context -> string -> int_num
    val mk_int_numeral_i : context -> int -> int_num
    val mk_int2real : context -> int_expr -> real_expr
    val mk_int2bv : context -> int -> int_expr -> bitvec_expr
  end

  module Real :
  sig
    val mk_sort : context -> real_sort
    val get_numerator : rat_num -> int_num
    val get_denominator : rat_num -> int_num
    val to_decimal_string : rat_num -> int -> string
    val to_string : rat_num -> string
    val mk_real_const : context -> symbol -> real_expr
    val mk_real_const_s : context -> string -> real_expr
    val mk_numeral_nd : context -> int -> int -> rat_num
    val mk_numeral_s : context -> string -> rat_num
    val mk_numeral_i : context -> int -> rat_num
    val mk_is_integer : context -> real_expr -> bool_expr
    val mk_real2int : context -> real_expr -> int_expr
  end

  module AlgebraicNumber :
  sig
    val to_upper : algebraic_num -> int -> rat_num
    val to_lower : algebraic_num -> int -> rat_num
    val to_decimal_string : algebraic_num -> int -> string
    val to_string : algebraic_num -> string
  end

  val is_int : expr -> bool
  val is_arithmetic_numeral : expr -> bool
  val is_le : expr -> bool
  val is_ge : expr -> bool
  val is_lt : expr -> bool
  val is_gt : expr -> bool
  val is_add : expr -> bool
  val is_sub : expr -> bool
  val is_uminus : expr -> bool
  val is_mul : expr -> bool
  val is_div : expr -> bool
  val is_idiv : expr -> bool
  val is_remainder : expr -> bool
  val is_modulus : expr -> bool
  val is_inttoreal : expr -> bool
  val is_real_to_int : expr -> bool
  val is_real_is_int : expr -> bool
  val is_real : expr -> bool
  val is_int_numeral : expr -> bool
  val is_rat_num : expr -> bool
  val is_algebraic_number : expr -> bool
  val mk_add : context -> arith_expr array -> arith_expr
  val mk_mul : context -> arith_expr array -> arith_expr
  val mk_sub : context -> arith_expr array -> arith_expr
  val mk_unary_minus : context -> arith_expr -> arith_expr
  val mk_div : context -> arith_expr -> arith_expr -> arith_expr
  val mk_power : context -> arith_expr -> arith_expr -> arith_expr
  val mk_lt : context -> arith_expr -> arith_expr -> bool_expr
  val mk_le : context -> arith_expr -> arith_expr -> bool_expr
  val mk_gt : context -> arith_expr -> arith_expr -> bool_expr
  val mk_ge : context -> arith_expr -> arith_expr -> bool_expr
end

module BitVector :
sig
  val mk_sort : context -> int -> bitvec_sort
  val is_bv : expr -> bool
  val is_bv_numeral : expr -> bool
  val is_bv_bit1 : expr -> bool
  val is_bv_bit0 : expr -> bool
  val is_bv_uminus : expr -> bool
  val is_bv_add : expr -> bool
  val is_bv_sub : expr -> bool
  val is_bv_mul : expr -> bool
  val is_bv_sdiv : expr -> bool
  val is_bv_udiv : expr -> bool
  val is_bv_SRem : expr -> bool
  val is_bv_urem : expr -> bool
  val is_bv_smod : expr -> bool
  val is_bv_sdiv0 : expr -> bool
  val is_bv_udiv0 : expr -> bool
  val is_bv_srem0 : expr -> bool
  val is_bv_urem0 : expr -> bool
  val is_bv_smod0 : expr -> bool
  val is_bv_ule : expr -> bool
  val is_bv_sle : expr -> bool
  val is_bv_uge : expr -> bool
  val is_bv_sge : expr -> bool
  val is_bv_ult : expr -> bool
  val is_bv_slt : expr -> bool
  val is_bv_ugt : expr -> bool
  val is_bv_sgt : expr -> bool
  val is_bv_and : expr -> bool
  val is_bv_or : expr -> bool
  val is_bv_not : expr -> bool
  val is_bv_xor : expr -> bool
  val is_bv_nand : expr -> bool
  val is_bv_nor : expr -> bool
  val is_bv_xnor : expr -> bool
  val is_bv_concat : expr -> bool
  val is_bv_signextension : expr -> bool
  val is_bv_zeroextension : expr -> bool
  val is_bv_extract : expr -> bool
  val is_bv_repeat : expr -> bool
  val is_bv_reduceor : expr -> bool
  val is_bv_reduceand : expr -> bool
  val is_bv_comp : expr -> bool
  val is_bv_shiftleft : expr -> bool
  val is_bv_shiftrightlogical : expr -> bool
  val is_bv_shiftrightarithmetic : expr -> bool
  val is_bv_rotateleft : expr -> bool
  val is_bv_rotateright : expr -> bool
  val is_bv_rotateleftextended : expr -> bool
  val is_bv_rotaterightextended : expr -> bool
  val is_int_to_bv : expr -> bool
  val is_bv_to_int : expr -> bool
  val is_bv_carry : expr -> bool
  val is_bv_xor3 : expr -> bool
  val get_size : bitvec_sort -> int
  val get_int : bitvec_num -> int
  val to_string : bitvec_num -> string
  val mk_const : context -> symbol -> int -> bitvec_expr
  val mk_const_s : context -> string -> int -> bitvec_expr
  val mk_not : context -> bitvec_expr -> expr
  val mk_redand : context -> bitvec_expr -> expr
  val mk_redor : context -> bitvec_expr -> expr
  val mk_and : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_or : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_xor : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_nand : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_nor : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_xnor : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_neg : context -> bitvec_expr -> expr
  val mk_add : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_sub : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_mul : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_udiv : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_sdiv : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_urem : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_srem : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_smod : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_ult : context -> bitvec_expr -> bitvec_expr -> bool_expr
  val mk_slt : context -> bitvec_expr -> bitvec_expr -> bool_expr
  val mk_ule : context -> bitvec_expr -> bitvec_expr -> bool_expr
  val mk_sle : context -> bitvec_expr -> bitvec_expr -> bool_expr
  val mk_uge : context -> bitvec_expr -> bitvec_expr -> bool_expr
  val mk_sge : context -> bitvec_expr -> bitvec_expr -> bool_expr
  val mk_ugt : context -> bitvec_expr -> bitvec_expr -> bool_expr
  val mk_sgt : context -> bitvec_expr -> bitvec_expr -> bool_expr
  val mk_concat : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_extract : context -> int -> int -> bitvec_expr -> expr
  val mk_sign_ext : context -> int -> bitvec_expr -> expr
  val mk_zero_ext : context -> int -> bitvec_expr -> expr
  val mk_repeat : context -> int -> bitvec_expr -> expr
  val mk_shl : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_lshr : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_ashr : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_rotate_left : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_rotate_right : context -> bitvec_expr -> bitvec_expr -> expr
  val mk_bv2int : context -> bitvec_expr -> bool -> int_expr
  val mk_add_no_overflow : context -> bitvec_expr -> bitvec_expr -> bool -> bool_expr
  val mk_add_no_underflow : context -> bitvec_expr -> bitvec_expr -> bool_expr
  val mk_sub_no_overflow : context -> bitvec_expr -> bitvec_expr -> bool_expr
  val mk_sub_no_underflow : context -> bitvec_expr -> bitvec_expr -> bool -> bool_expr
  val mk_sdiv_no_overflow : context -> bitvec_expr -> bitvec_expr -> bool_expr
  val mk_neg_no_overflow : context -> bitvec_expr -> bool_expr
  val mk_mul_no_overflow : context -> bitvec_expr -> bitvec_expr -> bool -> bool_expr
  val mk_mul_no_underflow : context -> bitvec_expr -> bitvec_expr -> bool_expr
  val mk_numeral : context -> string -> int -> bitvec_num
end

module Proof :
sig
  val is_true : expr -> bool
  val is_asserted : expr -> bool
  val is_goal : expr -> bool
  val is_modus_ponens : expr -> bool
  val is_reflexivity : expr -> bool
  val is_symmetry : expr -> bool
  val is_transitivity : expr -> bool
  val is_Transitivity_star : expr -> bool
  val is_monotonicity : expr -> bool
  val is_quant_intro : expr -> bool
  val is_distributivity : expr -> bool
  val is_and_elimination : expr -> bool
  val is_or_elimination : expr -> bool
  val is_rewrite : expr -> bool
  val is_rewrite_star : expr -> bool
  val is_pull_quant : expr -> bool
  val is_pull_quant_star : expr -> bool
  val is_push_quant : expr -> bool
  val is_elim_unused_vars : expr -> bool
  val is_der : expr -> bool
  val is_quant_inst : expr -> bool
  val is_hypothesis : expr -> bool
  val is_lemma : expr -> bool
  val is_unit_resolution : expr -> bool
  val is_iff_true : expr -> bool
  val is_iff_false : expr -> bool
  val is_commutativity : expr -> bool
  val is_def_axiom : expr -> bool
  val is_def_intro : expr -> bool
  val is_apply_def : expr -> bool
  val is_iff_oeq : expr -> bool
  val is_nnf_pos : expr -> bool
  val is_nnf_neg : expr -> bool
  val is_nnf_star : expr -> bool
  val is_cnf_star : expr -> bool
  val is_skolemize : expr -> bool
  val is_modus_ponens_oeq : expr -> bool
  val is_theory_lemma : expr -> bool
end

module Goal :
sig
  val get_precision : goal -> Z3enums.goal_prec
  val is_precise : goal -> bool
  val is_underapproximation : goal -> bool
  val is_overapproximation : goal -> bool
  val is_garbage : goal -> bool
  val assert_ : goal -> bool_expr array -> unit
  val is_inconsistent : goal -> bool
  val get_depth : goal -> int
  val reset : goal -> unit
  val get_size : goal -> int
  val get_formulas : goal -> bool_expr array
  val get_num_exprs : goal -> int
  val is_decided_sat : goal -> bool
  val is_decided_unsat : goal -> bool
  val translate : goal -> context -> goal
  val simplify : goal -> params option -> goal
  val mk_goal : context -> bool -> bool -> bool -> goal
  val to_string : goal -> string
end

module Model :
sig

  module FuncInterp :
  sig

    module FuncEntry :
    sig
      val get_value : func_entry -> expr
      val get_num_args : func_entry -> int
      val get_args : func_entry -> expr array
      val to_string : func_entry -> string
    end

    val get_num_entries : func_interp -> int
    val get_entries : func_interp -> func_entry array
    val get_else : func_interp -> expr
    val get_arity : func_interp -> int
    val to_string : func_interp -> string
  end

  val get_const_interp : model -> func_decl -> expr option
  val get_const_interp_e : model -> expr -> expr option
  val get_func_interp : model -> func_decl -> func_interp option
  val get_num_consts : model -> int
  val get_const_decls : model -> func_decl array
  val get_num_funcs : model -> int
  val get_func_decls : model -> func_decl array
  val get_decls : model -> func_decl array
  exception ModelEvaluationFailedException of string
  val eval : model -> expr -> bool -> expr
  val evaluate : model -> expr -> bool -> expr
  val get_num_sorts : model -> int
  val get_sorts : model -> sort array
  val sort_universe : model -> sort -> ast_vector array
  val to_string : model -> string
end

module Probe :
sig
  val apply : probe -> goal -> float
  val get_num_probes : context -> int
  val get_probe_names : context -> string array
  val get_probe_description : context -> string -> string
  val mk_probe : context -> string -> probe
  val const : context -> float -> probe
  val lt : context -> probe -> probe -> probe
  val gt : context -> probe -> probe -> probe
  val le : context -> probe -> probe -> probe
  val ge : context -> probe -> probe -> probe
  val eq : context -> probe -> probe -> probe
  val and_ : context -> probe -> probe -> probe
  val or_ : context -> probe -> probe -> probe
  val not_ : context -> probe -> probe
end

module Tactic :
sig

  module ApplyResult :
  sig
    val get_num_subgoals : apply_result -> int
    val get_subgoals : apply_result -> goal array
    val get_subgoal : apply_result -> int -> goal
    val convert_model : apply_result -> int -> model -> model
    val to_string : apply_result -> string
  end

  val get_help : tactic -> string
  val get_param_descrs : tactic -> param_descrs
  val apply : tactic -> goal -> params option -> apply_result
  val get_num_tactics : context -> int
  val get_tactic_names : context -> string array
  val get_tactic_description : context -> string -> string
  val mk_tactic : context -> string -> tactic
  val and_then : context -> tactic -> tactic -> tactic array -> tactic
  val or_else : context -> tactic -> tactic -> tactic
  val try_for : context -> tactic -> int -> tactic
  val when_ : context -> probe -> tactic -> tactic
  val cond : context -> probe -> tactic -> tactic -> tactic
  val repeat : context -> tactic -> int -> tactic
  val skip : context -> tactic
  val fail : context -> tactic
  val fail_if : context -> probe -> tactic
  val fail_if_not_decided : context -> tactic
  val using_params : context -> tactic -> params -> tactic
  val with_ : context -> tactic -> params -> tactic
  val par_or : context -> tactic array -> tactic
  val par_and_then : context -> tactic -> tactic -> tactic
  val interrupt : context -> unit
end

module Solver :
sig
  val string_of_status : status -> string

  module Statistics :
  sig

    module Entry :
    sig
      val get_key : statistics_entry -> string
      val get_int : statistics_entry -> int
      val get_float : statistics_entry -> float
      val is_int : statistics_entry -> bool
      val is_float : statistics_entry -> bool
      val to_string_value : statistics_entry -> string
      val to_string : statistics_entry -> string
    end

    val to_string : statistics -> string
    val get_size : statistics -> int
    val get_entries : statistics -> statistics_entry array
    val get_keys : statistics -> string array
    val get : statistics -> string -> statistics_entry option
  end

  val get_help : solver -> string
  val set_parameters : solver -> params -> unit
  val get_param_descrs : solver -> param_descrs
  val get_num_scopes : solver -> int
  val push : solver -> unit
  val pop : solver -> int -> unit
  val reset : solver -> unit
  val assert_ : solver -> bool_expr array -> unit
  val assert_and_track : solver -> bool_expr -> bool_expr -> unit
  val get_num_assertions : solver -> int
  val get_assertions : solver -> bool_expr array
  val check : solver -> bool_expr array -> status
  val get_model : solver -> model option
  val get_proof : solver -> expr option
  val get_unsat_core : solver -> ast_vector array
  val get_reason_unknown : solver -> string
  val get_statistics : solver -> statistics
  val mk_solver : context -> symbol option -> solver
  val mk_solver_s : context -> string -> solver
  val mk_simple_solver : context -> solver
  val mk_solver_t : context -> tactic -> solver
  val to_string : solver -> string
end

module Fixedpoint :
sig
  val get_help : fixedpoint -> string
  val set_params : fixedpoint -> params -> unit
  val get_param_descrs : fixedpoint -> param_descrs
  val assert_ : fixedpoint -> bool_expr array -> unit
  val register_relation : fixedpoint -> func_decl -> unit
  val add_rule : fixedpoint -> bool_expr -> symbol option -> unit
  val add_fact : fixedpoint -> func_decl -> int array -> unit
  val query : fixedpoint -> bool_expr -> status
  val query_r : fixedpoint -> func_decl array -> status
  val push : fixedpoint -> unit
  val pop : fixedpoint -> unit
  val update_rule : fixedpoint -> bool_expr -> symbol -> unit
  val get_answer : fixedpoint -> expr option
  val get_reason_unknown : fixedpoint -> string
  val get_num_levels : fixedpoint -> func_decl -> int
  val get_cover_delta : fixedpoint -> int -> func_decl -> expr option
  val add_cover : fixedpoint -> int -> func_decl -> expr -> unit
  val to_string : fixedpoint -> string
  val set_predicate_representation : fixedpoint -> func_decl -> symbol array -> unit
  val to_string_q : fixedpoint -> bool_expr array -> string
  val get_rules : fixedpoint -> bool_expr array
  val get_assertions : fixedpoint -> bool_expr array
  val mk_fixedpoint : context -> fixedpoint
end

module Options :
sig
  val update_param_value : context -> string -> string -> unit
  val get_param_value : context -> string -> string option
  val set_print_mode : context -> Z3enums.ast_print_mode -> unit
  val toggle_warning_messages : bool -> unit
end

module SMT :
sig
  val benchmark_to_smtstring : context -> string -> string -> string -> string -> bool_expr array -> bool_expr -> string
  val parse_smtlib_string : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> unit
  val parse_smtlib_file : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> unit
  val get_num_smtlib_formulas : context -> int
  val get_smtlib_formulas : context -> bool_expr array
  val get_num_smtlib_assumptions : context -> int
  val get_smtlib_assumptions : context -> bool_expr array
  val get_num_smtlib_decls : context -> int
  val get_smtlib_decls : context -> func_decl array
  val get_num_smtlib_sorts : context -> int
  val get_smtlib_sorts : context -> sort array
  val parse_smtlib2_string : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> bool_expr
  val parse_smtlib2_file : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> bool_expr
end

val set_global_param : string -> string -> unit
val get_global_param : string -> string option
val global_param_reset_all : unit
