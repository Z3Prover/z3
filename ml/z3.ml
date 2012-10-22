(* File generated from z3.idl *)

type context
and symbol
and ast
and sort = private ast
and func_decl = private ast
and app = private ast
and pattern = private ast
and params
and param_descrs
and model
and func_interp
and func_entry
and fixedpoint
and ast_vector
and ast_map
and goal
and tactic
and probe
and apply_result
and solver
and stats



and constructor
and constructor_list

and lbool =
  | L_FALSE
  | L_UNDEF
  | L_TRUE

and symbol_kind =
  | INT_SYMBOL
  | STRING_SYMBOL

and parameter_kind =
  | PARAMETER_INT
  | PARAMETER_DOUBLE
  | PARAMETER_RATIONAL
  | PARAMETER_SYMBOL
  | PARAMETER_SORT
  | PARAMETER_AST
  | PARAMETER_FUNC_DECL

and sort_kind =
  | UNINTERPRETED_SORT
  | BOOL_SORT
  | INT_SORT
  | REAL_SORT
  | BV_SORT
  | ARRAY_SORT
  | DATATYPE_SORT
  | RELATION_SORT
  | FINITE_DOMAIN_SORT
  | UNKNOWN_SORT

and ast_kind =
  | NUMERAL_AST
  | APP_AST
  | VAR_AST
  | QUANTIFIER_AST
  | SORT_AST
  | FUNC_DECL_AST
  | UNKNOWN_AST

and decl_kind =
  | OP_TRUE
  | OP_FALSE
  | OP_EQ
  | OP_DISTINCT
  | OP_ITE
  | OP_AND
  | OP_OR
  | OP_IFF
  | OP_XOR
  | OP_NOT
  | OP_IMPLIES
  | OP_OEQ
  | OP_ANUM
  | OP_AGNUM
  | OP_LE
  | OP_GE
  | OP_LT
  | OP_GT
  | OP_ADD
  | OP_SUB
  | OP_UMINUS
  | OP_MUL
  | OP_DIV
  | OP_IDIV
  | OP_REM
  | OP_MOD
  | OP_TO_REAL
  | OP_TO_INT
  | OP_IS_INT
  | OP_POWER
  | OP_STORE
  | OP_SELECT
  | OP_CONST_ARRAY
  | OP_ARRAY_MAP
  | OP_ARRAY_DEFAULT
  | OP_SET_UNION
  | OP_SET_INTERSECT
  | OP_SET_DIFFERENCE
  | OP_SET_COMPLEMENT
  | OP_SET_SUBSET
  | OP_AS_ARRAY
  | OP_BNUM
  | OP_BIT1
  | OP_BIT0
  | OP_BNEG
  | OP_BADD
  | OP_BSUB
  | OP_BMUL
  | OP_BSDIV
  | OP_BUDIV
  | OP_BSREM
  | OP_BUREM
  | OP_BSMOD
  | OP_BSDIV0
  | OP_BUDIV0
  | OP_BSREM0
  | OP_BUREM0
  | OP_BSMOD0
  | OP_ULEQ
  | OP_SLEQ
  | OP_UGEQ
  | OP_SGEQ
  | OP_ULT
  | OP_SLT
  | OP_UGT
  | OP_SGT
  | OP_BAND
  | OP_BOR
  | OP_BNOT
  | OP_BXOR
  | OP_BNAND
  | OP_BNOR
  | OP_BXNOR
  | OP_CONCAT
  | OP_SIGN_EXT
  | OP_ZERO_EXT
  | OP_EXTRACT
  | OP_REPEAT
  | OP_BREDOR
  | OP_BREDAND
  | OP_BCOMP
  | OP_BSHL
  | OP_BLSHR
  | OP_BASHR
  | OP_ROTATE_LEFT
  | OP_ROTATE_RIGHT
  | OP_EXT_ROTATE_LEFT
  | OP_EXT_ROTATE_RIGHT
  | OP_INT2BV
  | OP_BV2INT
  | OP_CARRY
  | OP_XOR3
  | OP_PR_UNDEF
  | OP_PR_TRUE
  | OP_PR_ASSERTED
  | OP_PR_GOAL
  | OP_PR_MODUS_PONENS
  | OP_PR_REFLEXIVITY
  | OP_PR_SYMMETRY
  | OP_PR_TRANSITIVITY
  | OP_PR_TRANSITIVITY_STAR
  | OP_PR_MONOTONICITY
  | OP_PR_QUANT_INTRO
  | OP_PR_DISTRIBUTIVITY
  | OP_PR_AND_ELIM
  | OP_PR_NOT_OR_ELIM
  | OP_PR_REWRITE
  | OP_PR_REWRITE_STAR
  | OP_PR_PULL_QUANT
  | OP_PR_PULL_QUANT_STAR
  | OP_PR_PUSH_QUANT
  | OP_PR_ELIM_UNUSED_VARS
  | OP_PR_DER
  | OP_PR_QUANT_INST
  | OP_PR_HYPOTHESIS
  | OP_PR_LEMMA
  | OP_PR_UNIT_RESOLUTION
  | OP_PR_IFF_TRUE
  | OP_PR_IFF_FALSE
  | OP_PR_COMMUTATIVITY
  | OP_PR_DEF_AXIOM
  | OP_PR_DEF_INTRO
  | OP_PR_APPLY_DEF
  | OP_PR_IFF_OEQ
  | OP_PR_NNF_POS
  | OP_PR_NNF_NEG
  | OP_PR_NNF_STAR
  | OP_PR_CNF_STAR
  | OP_PR_SKOLEMIZE
  | OP_PR_MODUS_PONENS_OEQ
  | OP_PR_TH_LEMMA
  | OP_PR_HYPER_RESOLVE
  | OP_RA_STORE
  | OP_RA_EMPTY
  | OP_RA_IS_EMPTY
  | OP_RA_JOIN
  | OP_RA_UNION
  | OP_RA_WIDEN
  | OP_RA_PROJECT
  | OP_RA_FILTER
  | OP_RA_NEGATION_FILTER
  | OP_RA_RENAME
  | OP_RA_COMPLEMENT
  | OP_RA_SELECT
  | OP_RA_CLONE
  | OP_FD_LT
  | OP_LABEL
  | OP_LABEL_LIT
  | OP_DT_CONSTRUCTOR
  | OP_DT_RECOGNISER
  | OP_DT_ACCESSOR
  | OP_UNINTERPRETED

and param_kind =
  | PK_UINT
  | PK_BOOL
  | PK_DOUBLE
  | PK_SYMBOL
  | PK_STRING
  | PK_OTHER
  | PK_INVALID

and search_failure =
  | NO_FAILURE
  | UNKNOWN
  | TIMEOUT
  | MEMOUT_WATERMARK
  | CANCELED
  | NUM_CONFLICTS
  | THEORY
  | QUANTIFIERS

and ast_print_mode =
  | PRINT_SMTLIB_FULL
  | PRINT_LOW_LEVEL
  | PRINT_SMTLIB_COMPLIANT
  | PRINT_SMTLIB2_COMPLIANT

and error_code =
  | OK
  | SORT_ERROR
  | IOB
  | INVALID_ARG
  | PARSER_ERROR
  | NO_PARSER
  | INVALID_PATTERN
  | MEMOUT_FAIL
  | FILE_ACCESS_ERROR
  | INTERNAL_FATAL
  | INVALID_USAGE
  | DEC_REF_ERROR
  | EXCEPTION

and goal_prec =
  | GOAL_PRECISE
  | GOAL_UNDER
  | GOAL_OVER
  | GOAL_UNDER_OVER


external finalize_Z3_context : context -> unit = "finalize_Z3_context";; let _ = Callback.register "finalize_Z3_context" finalize_Z3_context
external finalize_Z3_ast : ast -> unit = "finalize_Z3_ast";; let _ = Callback.register "finalize_Z3_ast" finalize_Z3_ast
external finalize_Z3_params : params -> unit = "finalize_Z3_params";; let _ = Callback.register "finalize_Z3_params" finalize_Z3_params
external finalize_Z3_param_descrs : param_descrs -> unit = "finalize_Z3_param_descrs";; let _ = Callback.register "finalize_Z3_param_descrs" finalize_Z3_param_descrs
external finalize_Z3_model : model -> unit = "finalize_Z3_model";; let _ = Callback.register "finalize_Z3_model" finalize_Z3_model
external finalize_Z3_func_interp : func_interp -> unit = "finalize_Z3_func_interp";; let _ = Callback.register "finalize_Z3_func_interp" finalize_Z3_func_interp
external finalize_Z3_func_entry : func_entry -> unit = "finalize_Z3_func_entry";; let _ = Callback.register "finalize_Z3_func_entry" finalize_Z3_func_entry
external finalize_Z3_fixedpoint : fixedpoint -> unit = "finalize_Z3_fixedpoint";; let _ = Callback.register "finalize_Z3_fixedpoint" finalize_Z3_fixedpoint
external finalize_Z3_ast_vector : ast_vector -> unit = "finalize_Z3_ast_vector";; let _ = Callback.register "finalize_Z3_ast_vector" finalize_Z3_ast_vector
external finalize_Z3_ast_map : ast_map -> unit = "finalize_Z3_ast_map";; let _ = Callback.register "finalize_Z3_ast_map" finalize_Z3_ast_map
external finalize_Z3_goal : goal -> unit = "finalize_Z3_goal";; let _ = Callback.register "finalize_Z3_goal" finalize_Z3_goal
external finalize_Z3_tactic : tactic -> unit = "finalize_Z3_tactic";; let _ = Callback.register "finalize_Z3_tactic" finalize_Z3_tactic
external finalize_Z3_probe : probe -> unit = "finalize_Z3_probe";; let _ = Callback.register "finalize_Z3_probe" finalize_Z3_probe
external finalize_Z3_apply_result : apply_result -> unit = "finalize_Z3_apply_result";; let _ = Callback.register "finalize_Z3_apply_result" finalize_Z3_apply_result
external finalize_Z3_solver : solver -> unit = "finalize_Z3_solver";; let _ = Callback.register "finalize_Z3_solver" finalize_Z3_solver
external finalize_Z3_stats : stats -> unit = "finalize_Z3_stats";; let _ = Callback.register "finalize_Z3_stats" finalize_Z3_stats

let del_constructor _ _ = ()
let del_constructor_list _ _ = ()
let del_model _ _ = ()
let del_context _ = ()
let reset_memory () = ()


(** Exceptions raised by Z3. It is safe to continue interacting with Z3 after
    catching [Error] exceptions.

    - {b See also}: {!get_error_msg}
*)
exception Error of context * error_code



let _ = Callback.register_exception "Z3.Error" (Error (Obj.magic None, OK))

external mk_context: (string * string) list -> context = "caml_z3_mk_context"

external update_param_value : context -> string -> string -> unit
	= "camlidl_z3_Z3_update_param_value"

external get_param_value : context -> string -> string option
	= "camlidl_z3_Z3_get_param_value"

external interrupt : context -> unit
	= "camlidl_z3_Z3_interrupt"

external mk_params : context -> params
	= "camlidl_z3_Z3_mk_params"

external params_set_bool : context -> params -> symbol -> bool -> unit
	= "camlidl_z3_Z3_params_set_bool"

external params_set_uint : context -> params -> symbol -> int -> unit
	= "camlidl_z3_Z3_params_set_uint"

external params_set_double : context -> params -> symbol -> float -> unit
	= "camlidl_z3_Z3_params_set_double"

external params_set_symbol : context -> params -> symbol -> symbol -> unit
	= "camlidl_z3_Z3_params_set_symbol"

external params_to_string : context -> params -> string
	= "camlidl_z3_Z3_params_to_string"

external params_validate : context -> params -> param_descrs -> unit
	= "camlidl_z3_Z3_params_validate"

external param_descrs_get_kind : context -> param_descrs -> symbol -> param_kind
	= "camlidl_z3_Z3_param_descrs_get_kind"

external param_descrs_size : context -> param_descrs -> int
	= "camlidl_z3_Z3_param_descrs_size"

external param_descrs_get_name : context -> param_descrs -> int -> symbol
	= "camlidl_z3_Z3_param_descrs_get_name"

external param_descrs_to_string : context -> param_descrs -> string
	= "camlidl_z3_Z3_param_descrs_to_string"


(**
   Refined view of a {!symbol}.

   - {b See also}: {!mk_symbol}
   - {b See also}: {!symbol_refine}
*)
type symbol_refined =
  | Symbol_int of int
  | Symbol_string of string

external mk_int_symbol : context -> int -> symbol
	= "camlidl_z3_Z3_mk_int_symbol"

external mk_string_symbol : context -> string -> symbol
	= "camlidl_z3_Z3_mk_string_symbol"


(**
   A datatype constructor descriptor.
*)
type datatype_constructor_desc = {
  constructor_desc : symbol;            	(** name of the constructor function *)
  recognizer_desc : symbol;             	(** name of the recognizer function *)
  accessor_descs : (symbol * sort) array;	(** names and sorts of the fields *)
}

(**
   A datatype is described by a name and constructor descriptors.
*)
type datatype_desc = symbol * datatype_constructor_desc array

(**
   A datatype constructor representation.
*)
type datatype_constructor = {
  constructor : func_decl;              	(** constructor function *)
  recognizer : func_decl;               	(** recognizer function *)
  accessors : func_decl array;          	(** field accessor functions *)
}

(**
   A datatype is represented by a sort and constructors.
*)
type datatype = sort * datatype_constructor array

(**
   Refined view of a {!sort}.

   - {b See also}: {!mk_sort}
   - {b See also}: {!sort_refine}
*)
type sort_refined =
  | Sort_uninterpreted of symbol
  | Sort_bool
  | Sort_int
  | Sort_bv of int
  | Sort_finite_domain of symbol * int64
  | Sort_real
  | Sort_array of sort * sort
  | Sort_datatype of datatype_constructor array
  | Sort_relation of sort array
  | Sort_unknown

external mk_uninterpreted_sort : context -> symbol -> sort
	= "camlidl_z3_Z3_mk_uninterpreted_sort"

external mk_bool_sort : context -> sort
	= "camlidl_z3_Z3_mk_bool_sort"

external mk_int_sort : context -> sort
	= "camlidl_z3_Z3_mk_int_sort"

external mk_real_sort : context -> sort
	= "camlidl_z3_Z3_mk_real_sort"

external mk_bv_sort : context -> int -> sort
	= "camlidl_z3_Z3_mk_bv_sort"

external mk_finite_domain_sort : context -> symbol -> int64 -> sort
	= "camlidl_z3_Z3_mk_finite_domain_sort"

external mk_array_sort : context -> sort -> sort -> sort
	= "camlidl_z3_Z3_mk_array_sort"

external mk_tuple_sort : context -> symbol -> symbol array -> sort array -> sort * func_decl * func_decl array
	= "camlidl_z3_Z3_mk_tuple_sort"

external mk_enumeration_sort : context -> symbol -> symbol array -> sort * func_decl array * func_decl array
	= "camlidl_z3_Z3_mk_enumeration_sort"

external mk_list_sort : context -> symbol -> sort -> sort * func_decl * func_decl * func_decl * func_decl * func_decl * func_decl
	= "camlidl_z3_Z3_mk_list_sort"

external mk_constructor : context -> symbol -> symbol -> symbol array -> sort option array -> int array -> constructor
	= "camlidl_z3_Z3_mk_constructor_bytecode" "camlidl_z3_Z3_mk_constructor"

external del_constructor : context -> constructor -> unit
	= "camlidl_z3_Z3_del_constructor"

external mk_datatype : context -> symbol -> constructor array -> sort * constructor array
	= "camlidl_z3_Z3_mk_datatype"

external mk_constructor_list : context -> constructor array -> constructor_list
	= "camlidl_z3_Z3_mk_constructor_list"

external del_constructor_list : context -> constructor_list -> unit
	= "camlidl_z3_Z3_del_constructor_list"

external mk_datatypes : context -> symbol array -> constructor_list array -> sort array * constructor_list array
	= "camlidl_z3_Z3_mk_datatypes"

external query_constructor : context -> constructor -> int -> func_decl * func_decl * func_decl array
	= "camlidl_z3_Z3_query_constructor"

external mk_func_decl : context -> symbol -> sort array -> sort -> func_decl
	= "camlidl_z3_Z3_mk_func_decl"

external mk_app : context -> func_decl -> ast array -> ast
	= "camlidl_z3_Z3_mk_app"

external mk_const : context -> symbol -> sort -> ast
	= "camlidl_z3_Z3_mk_const"

external mk_fresh_func_decl : context -> string -> sort array -> sort -> func_decl
	= "camlidl_z3_Z3_mk_fresh_func_decl"

external mk_fresh_const : context -> string -> sort -> ast
	= "camlidl_z3_Z3_mk_fresh_const"

external mk_true : context -> ast
	= "camlidl_z3_Z3_mk_true"

external mk_false : context -> ast
	= "camlidl_z3_Z3_mk_false"

external mk_eq : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_eq"

external mk_distinct : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_distinct"

external mk_not : context -> ast -> ast
	= "camlidl_z3_Z3_mk_not"

external mk_ite : context -> ast -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_ite"

external mk_iff : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_iff"

external mk_implies : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_implies"

external mk_xor : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_xor"

external mk_and : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_and"

external mk_or : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_or"

external mk_add : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_add"

external mk_mul : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_mul"

external mk_sub : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_sub"

external mk_unary_minus : context -> ast -> ast
	= "camlidl_z3_Z3_mk_unary_minus"

external mk_div : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_div"

external mk_mod : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_mod"

external mk_rem : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_rem"

external mk_power : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_power"

external mk_lt : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_lt"

external mk_le : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_le"

external mk_gt : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_gt"

external mk_ge : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_ge"

external mk_int2real : context -> ast -> ast
	= "camlidl_z3_Z3_mk_int2real"

external mk_real2int : context -> ast -> ast
	= "camlidl_z3_Z3_mk_real2int"

external mk_is_int : context -> ast -> ast
	= "camlidl_z3_Z3_mk_is_int"

external mk_bvnot : context -> ast -> ast
	= "camlidl_z3_Z3_mk_bvnot"

external mk_bvredand : context -> ast -> ast
	= "camlidl_z3_Z3_mk_bvredand"

external mk_bvredor : context -> ast -> ast
	= "camlidl_z3_Z3_mk_bvredor"

external mk_bvand : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvand"

external mk_bvor : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvor"

external mk_bvxor : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvxor"

external mk_bvnand : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvnand"

external mk_bvnor : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvnor"

external mk_bvxnor : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvxnor"

external mk_bvneg : context -> ast -> ast
	= "camlidl_z3_Z3_mk_bvneg"

external mk_bvadd : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvadd"

external mk_bvsub : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsub"

external mk_bvmul : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvmul"

external mk_bvudiv : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvudiv"

external mk_bvsdiv : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsdiv"

external mk_bvurem : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvurem"

external mk_bvsrem : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsrem"

external mk_bvsmod : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsmod"

external mk_bvult : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvult"

external mk_bvslt : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvslt"

external mk_bvule : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvule"

external mk_bvsle : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsle"

external mk_bvuge : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvuge"

external mk_bvsge : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsge"

external mk_bvugt : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvugt"

external mk_bvsgt : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsgt"

external mk_concat : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_concat"

external mk_extract : context -> int -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_extract"

external mk_sign_ext : context -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_sign_ext"

external mk_zero_ext : context -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_zero_ext"

external mk_repeat : context -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_repeat"

external mk_bvshl : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvshl"

external mk_bvlshr : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvlshr"

external mk_bvashr : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvashr"

external mk_rotate_left : context -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_rotate_left"

external mk_rotate_right : context -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_rotate_right"

external mk_ext_rotate_left : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_ext_rotate_left"

external mk_ext_rotate_right : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_ext_rotate_right"

external mk_int2bv : context -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_int2bv"

external mk_bv2int : context -> ast -> bool -> ast
	= "camlidl_z3_Z3_mk_bv2int"

external mk_bvadd_no_overflow : context -> ast -> ast -> bool -> ast
	= "camlidl_z3_Z3_mk_bvadd_no_overflow"

external mk_bvadd_no_underflow : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvadd_no_underflow"

external mk_bvsub_no_overflow : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsub_no_overflow"

external mk_bvsub_no_underflow : context -> ast -> ast -> bool -> ast
	= "camlidl_z3_Z3_mk_bvsub_no_underflow"

external mk_bvsdiv_no_overflow : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsdiv_no_overflow"

external mk_bvneg_no_overflow : context -> ast -> ast
	= "camlidl_z3_Z3_mk_bvneg_no_overflow"

external mk_bvmul_no_overflow : context -> ast -> ast -> bool -> ast
	= "camlidl_z3_Z3_mk_bvmul_no_overflow"

external mk_bvmul_no_underflow : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvmul_no_underflow"

external mk_select : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_select"

external mk_store : context -> ast -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_store"

external mk_const_array : context -> sort -> ast -> ast
	= "camlidl_z3_Z3_mk_const_array"

external mk_map : context -> func_decl -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_map"

external mk_array_default : context -> ast -> ast
	= "camlidl_z3_Z3_mk_array_default"

external mk_set_sort : context -> sort -> sort
	= "camlidl_z3_Z3_mk_set_sort"

external mk_empty_set : context -> sort -> ast
	= "camlidl_z3_Z3_mk_empty_set"

external mk_full_set : context -> sort -> ast
	= "camlidl_z3_Z3_mk_full_set"

external mk_set_add : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_set_add"

external mk_set_del : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_set_del"

external mk_set_union : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_set_union"

external mk_set_intersect : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_set_intersect"

external mk_set_difference : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_set_difference"

external mk_set_complement : context -> ast -> ast
	= "camlidl_z3_Z3_mk_set_complement"

external mk_set_member : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_set_member"

external mk_set_subset : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_set_subset"


(**
  Summary: \[ [ numeral_refined ] \] is the refined view of a numeral .
*)
type numeral_refined =
  | Numeral_int      of int * sort
  | Numeral_int64    of int64 * sort
  | Numeral_large    of string * sort
  | Numeral_rational of numeral_refined * numeral_refined

external mk_numeral : context -> string -> sort -> ast
	= "camlidl_z3_Z3_mk_numeral"

external mk_real : context -> int -> int -> ast
	= "camlidl_z3_Z3_mk_real"

external mk_int : context -> int -> sort -> ast
	= "camlidl_z3_Z3_mk_int"

external mk_int64 : context -> int64 -> sort -> ast
	= "camlidl_z3_Z3_mk_int64"

external mk_pattern : context -> ast array -> pattern
	= "camlidl_z3_Z3_mk_pattern"

external mk_bound : context -> int -> sort -> ast
	= "camlidl_z3_Z3_mk_bound"

external mk_forall : context -> int -> pattern array -> sort array -> symbol array -> ast -> ast
	= "camlidl_z3_Z3_mk_forall_bytecode" "camlidl_z3_Z3_mk_forall"

external mk_exists : context -> int -> pattern array -> sort array -> symbol array -> ast -> ast
	= "camlidl_z3_Z3_mk_exists_bytecode" "camlidl_z3_Z3_mk_exists"

external mk_quantifier : context -> bool -> int -> pattern array -> sort array -> symbol array -> ast -> ast
	= "camlidl_z3_Z3_mk_quantifier_bytecode" "camlidl_z3_Z3_mk_quantifier"

external mk_quantifier_ex : context -> bool -> int -> symbol -> symbol -> pattern array -> ast array -> sort array -> symbol array -> ast -> ast
	= "camlidl_z3_Z3_mk_quantifier_ex_bytecode" "camlidl_z3_Z3_mk_quantifier_ex"

external mk_forall_const : context -> int -> app array -> pattern array -> ast -> ast
	= "camlidl_z3_Z3_mk_forall_const"

external mk_exists_const : context -> int -> app array -> pattern array -> ast -> ast
	= "camlidl_z3_Z3_mk_exists_const"

external mk_quantifier_const : context -> bool -> int -> app array -> pattern array -> ast -> ast
	= "camlidl_z3_Z3_mk_quantifier_const_bytecode" "camlidl_z3_Z3_mk_quantifier_const"

external mk_quantifier_const_ex : context -> bool -> int -> symbol -> symbol -> app array -> pattern array -> ast array -> ast -> ast
	= "camlidl_z3_Z3_mk_quantifier_const_ex_bytecode" "camlidl_z3_Z3_mk_quantifier_const_ex"

external get_symbol_kind : context -> symbol -> symbol_kind
	= "camlidl_z3_Z3_get_symbol_kind"

external get_symbol_int : context -> symbol -> int
	= "camlidl_z3_Z3_get_symbol_int"

external get_symbol_string : context -> symbol -> string
	= "camlidl_z3_Z3_get_symbol_string"

external get_sort_name : context -> sort -> symbol
	= "camlidl_z3_Z3_get_sort_name"

external get_sort_id : context -> sort -> int
	= "camlidl_z3_Z3_get_sort_id"

external sort_to_ast : context -> sort -> ast
	= "camlidl_z3_Z3_sort_to_ast"

external is_eq_sort : context -> sort -> sort -> bool
	= "camlidl_z3_Z3_is_eq_sort"

external get_sort_kind : context -> sort -> sort_kind
	= "camlidl_z3_Z3_get_sort_kind"

external get_bv_sort_size : context -> sort -> int
	= "camlidl_z3_Z3_get_bv_sort_size"

external get_finite_domain_sort_size : context -> sort -> int64 option
	= "camlidl_z3_Z3_get_finite_domain_sort_size"

external get_array_sort_domain : context -> sort -> sort
	= "camlidl_z3_Z3_get_array_sort_domain"

external get_array_sort_range : context -> sort -> sort
	= "camlidl_z3_Z3_get_array_sort_range"

external get_tuple_sort_mk_decl : context -> sort -> func_decl
	= "camlidl_z3_Z3_get_tuple_sort_mk_decl"

external get_tuple_sort_num_fields : context -> sort -> int
	= "camlidl_z3_Z3_get_tuple_sort_num_fields"

external get_tuple_sort_field_decl : context -> sort -> int -> func_decl
	= "camlidl_z3_Z3_get_tuple_sort_field_decl"

external get_datatype_sort_num_constructors : context -> sort -> int
	= "camlidl_z3_Z3_get_datatype_sort_num_constructors"

external get_datatype_sort_constructor : context -> sort -> int -> func_decl
	= "camlidl_z3_Z3_get_datatype_sort_constructor"

external get_datatype_sort_recognizer : context -> sort -> int -> func_decl
	= "camlidl_z3_Z3_get_datatype_sort_recognizer"

external get_datatype_sort_constructor_accessor : context -> sort -> int -> int -> func_decl
	= "camlidl_z3_Z3_get_datatype_sort_constructor_accessor"

external get_relation_arity : context -> sort -> int
	= "camlidl_z3_Z3_get_relation_arity"

external get_relation_column : context -> sort -> int -> sort
	= "camlidl_z3_Z3_get_relation_column"

external func_decl_to_ast : context -> func_decl -> ast
	= "camlidl_z3_Z3_func_decl_to_ast"

external is_eq_func_decl : context -> func_decl -> func_decl -> bool
	= "camlidl_z3_Z3_is_eq_func_decl"

external get_func_decl_id : context -> func_decl -> int
	= "camlidl_z3_Z3_get_func_decl_id"

external get_decl_name : context -> func_decl -> symbol
	= "camlidl_z3_Z3_get_decl_name"

external get_decl_kind : context -> func_decl -> decl_kind
	= "camlidl_z3_Z3_get_decl_kind"

external get_domain_size : context -> func_decl -> int
	= "camlidl_z3_Z3_get_domain_size"

external get_arity : context -> func_decl -> int
	= "camlidl_z3_Z3_get_arity"

external get_domain : context -> func_decl -> int -> sort
	= "camlidl_z3_Z3_get_domain"

external get_range : context -> func_decl -> sort
	= "camlidl_z3_Z3_get_range"

external get_decl_num_parameters : context -> func_decl -> int
	= "camlidl_z3_Z3_get_decl_num_parameters"

external get_decl_parameter_kind : context -> func_decl -> int -> parameter_kind
	= "camlidl_z3_Z3_get_decl_parameter_kind"

external get_decl_int_parameter : context -> func_decl -> int -> int
	= "camlidl_z3_Z3_get_decl_int_parameter"

external get_decl_double_parameter : context -> func_decl -> int -> float
	= "camlidl_z3_Z3_get_decl_double_parameter"

external get_decl_symbol_parameter : context -> func_decl -> int -> symbol
	= "camlidl_z3_Z3_get_decl_symbol_parameter"

external get_decl_sort_parameter : context -> func_decl -> int -> sort
	= "camlidl_z3_Z3_get_decl_sort_parameter"

external get_decl_ast_parameter : context -> func_decl -> int -> ast
	= "camlidl_z3_Z3_get_decl_ast_parameter"

external get_decl_func_decl_parameter : context -> func_decl -> int -> func_decl
	= "camlidl_z3_Z3_get_decl_func_decl_parameter"

external get_decl_rational_parameter : context -> func_decl -> int -> string
	= "camlidl_z3_Z3_get_decl_rational_parameter"

external app_to_ast : context -> app -> ast
	= "camlidl_z3_Z3_app_to_ast"

external get_app_decl : context -> app -> func_decl
	= "camlidl_z3_Z3_get_app_decl"

external get_app_num_args : context -> app -> int
	= "camlidl_z3_Z3_get_app_num_args"

external get_app_arg : context -> app -> int -> ast
	= "camlidl_z3_Z3_get_app_arg"


(**
  Summary: \[ [ binder_type ] \] is a universal or existential quantifier.

  - {b See also}: {!term_refined}
*)
type binder_type = Forall | Exists

(**
  Summary: \[ [ term_refined ] \] is the refinement of a {!ast} .

  - {b See also}: {!term_refine}
*)
type term_refined =
  | Term_numeral    of numeral_refined
  | Term_app        of decl_kind * func_decl * ast array
  | Term_quantifier of binder_type * int * ast array array * (symbol * sort) array * ast
  | Term_var        of int * sort

external is_eq_ast : context -> ast -> ast -> bool
	= "camlidl_z3_Z3_is_eq_ast"

external get_ast_id : context -> ast -> int
	= "camlidl_z3_Z3_get_ast_id"

external get_ast_hash : context -> ast -> int
	= "camlidl_z3_Z3_get_ast_hash"

external get_sort : context -> ast -> sort
	= "camlidl_z3_Z3_get_sort"

external is_well_sorted : context -> ast -> bool
	= "camlidl_z3_Z3_is_well_sorted"

external get_bool_value : context -> ast -> lbool
	= "camlidl_z3_Z3_get_bool_value"

external get_ast_kind : context -> ast -> ast_kind
	= "camlidl_z3_Z3_get_ast_kind"

external is_app : context -> ast -> bool
	= "camlidl_z3_Z3_is_app"

external is_numeral_ast : context -> ast -> bool
	= "camlidl_z3_Z3_is_numeral_ast"

external is_algebraic_number : context -> ast -> bool
	= "camlidl_z3_Z3_is_algebraic_number"

external to_app : context -> ast -> app
	= "camlidl_z3_Z3_to_app"

external to_func_decl : context -> ast -> func_decl
	= "camlidl_z3_Z3_to_func_decl"

external get_numeral_string : context -> ast -> string
	= "camlidl_z3_Z3_get_numeral_string"

external get_numeral_decimal_string : context -> ast -> int -> string
	= "camlidl_z3_Z3_get_numeral_decimal_string"

external get_numerator : context -> ast -> ast
	= "camlidl_z3_Z3_get_numerator"

external get_denominator : context -> ast -> ast
	= "camlidl_z3_Z3_get_denominator"

external get_numeral_small : context -> ast -> bool * int64 * int64
	= "camlidl_z3_Z3_get_numeral_small"

external get_numeral_int : context -> ast -> bool * int
	= "camlidl_z3_Z3_get_numeral_int"

external get_numeral_int64 : context -> ast -> bool * int64
	= "camlidl_z3_Z3_get_numeral_int64"

external get_numeral_rational_int64 : context -> ast -> bool * int64 * int64
	= "camlidl_z3_Z3_get_numeral_rational_int64"

external get_algebraic_number_lower : context -> ast -> int -> ast
	= "camlidl_z3_Z3_get_algebraic_number_lower"

external get_algebraic_number_upper : context -> ast -> int -> ast
	= "camlidl_z3_Z3_get_algebraic_number_upper"

external pattern_to_ast : context -> pattern -> ast
	= "camlidl_z3_Z3_pattern_to_ast"

external get_pattern_num_terms : context -> pattern -> int
	= "camlidl_z3_Z3_get_pattern_num_terms"

external get_pattern : context -> pattern -> int -> ast
	= "camlidl_z3_Z3_get_pattern"

external get_index_value : context -> ast -> int
	= "camlidl_z3_Z3_get_index_value"

external is_quantifier_forall : context -> ast -> bool
	= "camlidl_z3_Z3_is_quantifier_forall"

external get_quantifier_weight : context -> ast -> int
	= "camlidl_z3_Z3_get_quantifier_weight"

external get_quantifier_num_patterns : context -> ast -> int
	= "camlidl_z3_Z3_get_quantifier_num_patterns"

external get_quantifier_pattern_ast : context -> ast -> int -> pattern
	= "camlidl_z3_Z3_get_quantifier_pattern_ast"

external get_quantifier_num_no_patterns : context -> ast -> int
	= "camlidl_z3_Z3_get_quantifier_num_no_patterns"

external get_quantifier_no_pattern_ast : context -> ast -> int -> ast
	= "camlidl_z3_Z3_get_quantifier_no_pattern_ast"

external get_quantifier_num_bound : context -> ast -> int
	= "camlidl_z3_Z3_get_quantifier_num_bound"

external get_quantifier_bound_name : context -> ast -> int -> symbol
	= "camlidl_z3_Z3_get_quantifier_bound_name"

external get_quantifier_bound_sort : context -> ast -> int -> sort
	= "camlidl_z3_Z3_get_quantifier_bound_sort"

external get_quantifier_body : context -> ast -> ast
	= "camlidl_z3_Z3_get_quantifier_body"

external simplify : context -> ast -> ast
	= "camlidl_z3_Z3_simplify"

external simplify_ex : context -> ast -> params -> ast
	= "camlidl_z3_Z3_simplify_ex"

external simplify_get_help : context -> string
	= "camlidl_z3_Z3_simplify_get_help"

external simplify_get_param_descrs : context -> param_descrs
	= "camlidl_z3_Z3_simplify_get_param_descrs"

external update_term : context -> ast -> ast array -> ast
	= "camlidl_z3_Z3_update_term"

external substitute : context -> ast -> ast array -> ast array -> ast
	= "camlidl_z3_Z3_substitute"

external substitute_vars : context -> ast -> ast array -> ast
	= "camlidl_z3_Z3_substitute_vars"

external translate : context -> ast -> context -> ast
	= "camlidl_z3_Z3_translate"


(**
   A model assigns uninterpreted sorts to finite universes of distinct values, constants to values,
   and arrays and functions to finite maps from argument values to result values plus a default
   value for all other arguments.
*)
type model_refined = {
  sorts : (sort, ast_vector) Hashtbl.t;
  consts : (func_decl, ast) Hashtbl.t;
  arrays : (func_decl, (ast, ast) Hashtbl.t * ast) Hashtbl.t;
  funcs : (func_decl, (ast array, ast) Hashtbl.t * ast) Hashtbl.t;
}

external model_eval : context -> model -> ast -> bool -> ast option
	= "camlidl_z3_Z3_model_eval"

external model_get_const_interp : context -> model -> func_decl -> ast option
	= "camlidl_z3_Z3_model_get_const_interp"

external model_get_func_interp : context -> model -> func_decl -> func_interp option
	= "camlidl_z3_Z3_model_get_func_interp"

external model_get_num_consts : context -> model -> int
	= "camlidl_z3_Z3_model_get_num_consts"

external model_get_const_decl : context -> model -> int -> func_decl
	= "camlidl_z3_Z3_model_get_const_decl"

external model_get_num_funcs : context -> model -> int
	= "camlidl_z3_Z3_model_get_num_funcs"

external model_get_func_decl : context -> model -> int -> func_decl
	= "camlidl_z3_Z3_model_get_func_decl"

external model_get_num_sorts : context -> model -> int
	= "camlidl_z3_Z3_model_get_num_sorts"

external model_get_sort : context -> model -> int -> sort
	= "camlidl_z3_Z3_model_get_sort"

external model_get_sort_universe : context -> model -> sort -> ast_vector
	= "camlidl_z3_Z3_model_get_sort_universe"

external is_as_array : context -> ast -> bool
	= "camlidl_z3_Z3_is_as_array"

external get_as_array_func_decl : context -> ast -> func_decl
	= "camlidl_z3_Z3_get_as_array_func_decl"

external func_interp_get_num_entries : context -> func_interp -> int
	= "camlidl_z3_Z3_func_interp_get_num_entries"

external func_interp_get_entry : context -> func_interp -> int -> func_entry
	= "camlidl_z3_Z3_func_interp_get_entry"

external func_interp_get_else : context -> func_interp -> ast
	= "camlidl_z3_Z3_func_interp_get_else"

external func_interp_get_arity : context -> func_interp -> int
	= "camlidl_z3_Z3_func_interp_get_arity"

external func_entry_get_value : context -> func_entry -> ast
	= "camlidl_z3_Z3_func_entry_get_value"

external func_entry_get_num_args : context -> func_entry -> int
	= "camlidl_z3_Z3_func_entry_get_num_args"

external func_entry_get_arg : context -> func_entry -> int -> ast
	= "camlidl_z3_Z3_func_entry_get_arg"

external open_log : string -> bool
	= "camlidl_z3_Z3_open_log"

external append_log : string -> unit
	= "camlidl_z3_Z3_append_log"

external close_log : unit -> unit
	= "camlidl_z3_Z3_close_log"

external toggle_warning_messages : bool -> unit
	= "camlidl_z3_Z3_toggle_warning_messages"

external set_ast_print_mode : context -> ast_print_mode -> unit
	= "camlidl_z3_Z3_set_ast_print_mode"

external ast_to_string : context -> ast -> string
	= "camlidl_z3_Z3_ast_to_string"

external pattern_to_string : context -> pattern -> string
	= "camlidl_z3_Z3_pattern_to_string"

external sort_to_string : context -> sort -> string
	= "camlidl_z3_Z3_sort_to_string"

external func_decl_to_string : context -> func_decl -> string
	= "camlidl_z3_Z3_func_decl_to_string"

external model_to_string : context -> model -> string
	= "camlidl_z3_Z3_model_to_string"

external benchmark_to_smtlib_string : context -> string -> string -> string -> string -> ast array -> ast -> string
	= "camlidl_z3_Z3_benchmark_to_smtlib_string_bytecode" "camlidl_z3_Z3_benchmark_to_smtlib_string"

external parse_smtlib2_string : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> ast
	= "camlidl_z3_Z3_parse_smtlib2_string_bytecode" "camlidl_z3_Z3_parse_smtlib2_string"

external parse_smtlib2_file : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> ast
	= "camlidl_z3_Z3_parse_smtlib2_file_bytecode" "camlidl_z3_Z3_parse_smtlib2_file"

external parse_smtlib_string : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> unit
	= "camlidl_z3_Z3_parse_smtlib_string_bytecode" "camlidl_z3_Z3_parse_smtlib_string"

external parse_smtlib_file : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> unit
	= "camlidl_z3_Z3_parse_smtlib_file_bytecode" "camlidl_z3_Z3_parse_smtlib_file"

external get_smtlib_num_formulas : context -> int
	= "camlidl_z3_Z3_get_smtlib_num_formulas"

external get_smtlib_formula : context -> int -> ast
	= "camlidl_z3_Z3_get_smtlib_formula"

external get_smtlib_num_assumptions : context -> int
	= "camlidl_z3_Z3_get_smtlib_num_assumptions"

external get_smtlib_assumption : context -> int -> ast
	= "camlidl_z3_Z3_get_smtlib_assumption"

external get_smtlib_num_decls : context -> int
	= "camlidl_z3_Z3_get_smtlib_num_decls"

external get_smtlib_decl : context -> int -> func_decl
	= "camlidl_z3_Z3_get_smtlib_decl"

external get_smtlib_num_sorts : context -> int
	= "camlidl_z3_Z3_get_smtlib_num_sorts"

external get_smtlib_sort : context -> int -> sort
	= "camlidl_z3_Z3_get_smtlib_sort"

external get_smtlib_error : context -> string
	= "camlidl_z3_Z3_get_smtlib_error"

external parse_z3_string : context -> string -> ast
	= "camlidl_z3_Z3_parse_z3_string"

external parse_z3_file : context -> string -> ast
	= "camlidl_z3_Z3_parse_z3_file"

external set_error : context -> error_code -> unit
	= "camlidl_z3_Z3_set_error"

external get_error_msg_ex : context -> error_code -> string
	= "camlidl_z3_Z3_get_error_msg_ex"

external get_version : unit -> int * int * int * int
	= "camlidl_z3_Z3_get_version"

external mk_fixedpoint : context -> fixedpoint
	= "camlidl_z3_Z3_mk_fixedpoint"

external fixedpoint_add_rule : context -> fixedpoint -> ast -> symbol -> unit
	= "camlidl_z3_Z3_fixedpoint_add_rule"

external fixedpoint_add_fact : context -> fixedpoint -> func_decl -> int array -> unit
	= "camlidl_z3_Z3_fixedpoint_add_fact"

external fixedpoint_assert : context -> fixedpoint -> ast -> unit
	= "camlidl_z3_Z3_fixedpoint_assert"

external fixedpoint_query : context -> fixedpoint -> ast -> lbool
	= "camlidl_z3_Z3_fixedpoint_query"

external fixedpoint_query_relations : context -> fixedpoint -> func_decl array -> lbool
	= "camlidl_z3_Z3_fixedpoint_query_relations"

external fixedpoint_get_answer : context -> fixedpoint -> ast
	= "camlidl_z3_Z3_fixedpoint_get_answer"

external fixedpoint_get_reason_unknown : context -> fixedpoint -> string
	= "camlidl_z3_Z3_fixedpoint_get_reason_unknown"

external fixedpoint_update_rule : context -> fixedpoint -> ast -> symbol -> unit
	= "camlidl_z3_Z3_fixedpoint_update_rule"

external fixedpoint_get_num_levels : context -> fixedpoint -> func_decl -> int
	= "camlidl_z3_Z3_fixedpoint_get_num_levels"

external fixedpoint_get_cover_delta : context -> fixedpoint -> int -> func_decl -> ast
	= "camlidl_z3_Z3_fixedpoint_get_cover_delta"

external fixedpoint_add_cover : context -> fixedpoint -> int -> func_decl -> ast -> unit
	= "camlidl_z3_Z3_fixedpoint_add_cover"

external fixedpoint_get_statistics : context -> fixedpoint -> stats
	= "camlidl_z3_Z3_fixedpoint_get_statistics"

external fixedpoint_register_relation : context -> fixedpoint -> func_decl -> unit
	= "camlidl_z3_Z3_fixedpoint_register_relation"

external fixedpoint_set_predicate_representation : context -> fixedpoint -> func_decl -> symbol array -> unit
	= "camlidl_z3_Z3_fixedpoint_set_predicate_representation"

external fixedpoint_simplify_rules : context -> fixedpoint -> ast array -> func_decl array -> ast_vector
	= "camlidl_z3_Z3_fixedpoint_simplify_rules"

external fixedpoint_set_params : context -> fixedpoint -> params -> unit
	= "camlidl_z3_Z3_fixedpoint_set_params"

external fixedpoint_get_help : context -> fixedpoint -> string
	= "camlidl_z3_Z3_fixedpoint_get_help"

external fixedpoint_get_param_descrs : context -> fixedpoint -> param_descrs
	= "camlidl_z3_Z3_fixedpoint_get_param_descrs"

external fixedpoint_to_string : context -> fixedpoint -> ast array -> string
	= "camlidl_z3_Z3_fixedpoint_to_string"

external fixedpoint_push : context -> fixedpoint -> unit
	= "camlidl_z3_Z3_fixedpoint_push"

external fixedpoint_pop : context -> fixedpoint -> unit
	= "camlidl_z3_Z3_fixedpoint_pop"

external mk_ast_vector : context -> ast_vector
	= "camlidl_z3_Z3_mk_ast_vector"

external ast_vector_size : context -> ast_vector -> int
	= "camlidl_z3_Z3_ast_vector_size"

external ast_vector_get : context -> ast_vector -> int -> ast
	= "camlidl_z3_Z3_ast_vector_get"

external ast_vector_set : context -> ast_vector -> int -> ast -> unit
	= "camlidl_z3_Z3_ast_vector_set"

external ast_vector_resize : context -> ast_vector -> int -> unit
	= "camlidl_z3_Z3_ast_vector_resize"

external ast_vector_push : context -> ast_vector -> ast -> unit
	= "camlidl_z3_Z3_ast_vector_push"

external ast_vector_translate : context -> ast_vector -> context -> ast_vector
	= "camlidl_z3_Z3_ast_vector_translate"

external ast_vector_to_string : context -> ast_vector -> string
	= "camlidl_z3_Z3_ast_vector_to_string"

external mk_ast_map : context -> ast_map
	= "camlidl_z3_Z3_mk_ast_map"

external ast_map_contains : context -> ast_map -> ast -> bool
	= "camlidl_z3_Z3_ast_map_contains"

external ast_map_find : context -> ast_map -> ast -> ast
	= "camlidl_z3_Z3_ast_map_find"

external ast_map_insert : context -> ast_map -> ast -> ast -> unit
	= "camlidl_z3_Z3_ast_map_insert"

external ast_map_erase : context -> ast_map -> ast -> unit
	= "camlidl_z3_Z3_ast_map_erase"

external ast_map_reset : context -> ast_map -> unit
	= "camlidl_z3_Z3_ast_map_reset"

external ast_map_size : context -> ast_map -> int
	= "camlidl_z3_Z3_ast_map_size"

external ast_map_keys : context -> ast_map -> ast_vector
	= "camlidl_z3_Z3_ast_map_keys"

external ast_map_to_string : context -> ast_map -> string
	= "camlidl_z3_Z3_ast_map_to_string"

external mk_goal : context -> bool -> bool -> bool -> goal
	= "camlidl_z3_Z3_mk_goal"

external goal_precision : context -> goal -> goal_prec
	= "camlidl_z3_Z3_goal_precision"

external goal_assert : context -> goal -> ast -> unit
	= "camlidl_z3_Z3_goal_assert"

external goal_inconsistent : context -> goal -> bool
	= "camlidl_z3_Z3_goal_inconsistent"

external goal_depth : context -> goal -> int
	= "camlidl_z3_Z3_goal_depth"

external goal_reset : context -> goal -> unit
	= "camlidl_z3_Z3_goal_reset"

external goal_size : context -> goal -> int
	= "camlidl_z3_Z3_goal_size"

external goal_formula : context -> goal -> int -> ast
	= "camlidl_z3_Z3_goal_formula"

external goal_num_exprs : context -> goal -> int
	= "camlidl_z3_Z3_goal_num_exprs"

external goal_is_decided_sat : context -> goal -> bool
	= "camlidl_z3_Z3_goal_is_decided_sat"

external goal_is_decided_unsat : context -> goal -> bool
	= "camlidl_z3_Z3_goal_is_decided_unsat"

external goal_translate : context -> goal -> context -> goal
	= "camlidl_z3_Z3_goal_translate"

external goal_to_string : context -> goal -> string
	= "camlidl_z3_Z3_goal_to_string"

external mk_tactic : context -> string -> tactic
	= "camlidl_z3_Z3_mk_tactic"

external mk_probe : context -> string -> probe
	= "camlidl_z3_Z3_mk_probe"

external tactic_and_then : context -> tactic -> tactic -> tactic
	= "camlidl_z3_Z3_tactic_and_then"

external tactic_or_else : context -> tactic -> tactic -> tactic
	= "camlidl_z3_Z3_tactic_or_else"

external tactic_par_or : context -> tactic array -> tactic
	= "camlidl_z3_Z3_tactic_par_or"

external tactic_par_and_then : context -> tactic -> tactic -> tactic
	= "camlidl_z3_Z3_tactic_par_and_then"

external tactic_try_for : context -> tactic -> int -> tactic
	= "camlidl_z3_Z3_tactic_try_for"

external tactic_when : context -> probe -> tactic -> tactic
	= "camlidl_z3_Z3_tactic_when"

external tactic_cond : context -> probe -> tactic -> tactic -> tactic
	= "camlidl_z3_Z3_tactic_cond"

external tactic_repeat : context -> tactic -> int -> tactic
	= "camlidl_z3_Z3_tactic_repeat"

external tactic_skip : context -> tactic
	= "camlidl_z3_Z3_tactic_skip"

external tactic_fail : context -> tactic
	= "camlidl_z3_Z3_tactic_fail"

external tactic_fail_if : context -> probe -> tactic
	= "camlidl_z3_Z3_tactic_fail_if"

external tactic_fail_if_not_decided : context -> tactic
	= "camlidl_z3_Z3_tactic_fail_if_not_decided"

external tactic_using_params : context -> tactic -> params -> tactic
	= "camlidl_z3_Z3_tactic_using_params"

external probe_const : context -> float -> probe
	= "camlidl_z3_Z3_probe_const"

external probe_lt : context -> probe -> probe -> probe
	= "camlidl_z3_Z3_probe_lt"

external probe_gt : context -> probe -> probe -> probe
	= "camlidl_z3_Z3_probe_gt"

external probe_le : context -> probe -> probe -> probe
	= "camlidl_z3_Z3_probe_le"

external probe_ge : context -> probe -> probe -> probe
	= "camlidl_z3_Z3_probe_ge"

external probe_eq : context -> probe -> probe -> probe
	= "camlidl_z3_Z3_probe_eq"

external probe_and : context -> probe -> probe -> probe
	= "camlidl_z3_Z3_probe_and"

external probe_or : context -> probe -> probe -> probe
	= "camlidl_z3_Z3_probe_or"

external probe_not : context -> probe -> probe
	= "camlidl_z3_Z3_probe_not"

external get_num_tactics : context -> int
	= "camlidl_z3_Z3_get_num_tactics"

external get_tactic_name : context -> int -> string
	= "camlidl_z3_Z3_get_tactic_name"

external get_num_probes : context -> int
	= "camlidl_z3_Z3_get_num_probes"

external get_probe_name : context -> int -> string
	= "camlidl_z3_Z3_get_probe_name"

external tactic_get_help : context -> tactic -> string
	= "camlidl_z3_Z3_tactic_get_help"

external tactic_get_param_descrs : context -> tactic -> param_descrs
	= "camlidl_z3_Z3_tactic_get_param_descrs"

external tactic_get_descr : context -> string -> string
	= "camlidl_z3_Z3_tactic_get_descr"

external probe_get_descr : context -> string -> string
	= "camlidl_z3_Z3_probe_get_descr"

external probe_apply : context -> probe -> goal -> float
	= "camlidl_z3_Z3_probe_apply"

external tactic_apply : context -> tactic -> goal -> apply_result
	= "camlidl_z3_Z3_tactic_apply"

external tactic_apply_ex : context -> tactic -> goal -> params -> apply_result
	= "camlidl_z3_Z3_tactic_apply_ex"

external apply_result_to_string : context -> apply_result -> string
	= "camlidl_z3_Z3_apply_result_to_string"

external apply_result_get_num_subgoals : context -> apply_result -> int
	= "camlidl_z3_Z3_apply_result_get_num_subgoals"

external apply_result_get_subgoal : context -> apply_result -> int -> goal
	= "camlidl_z3_Z3_apply_result_get_subgoal"

external apply_result_convert_model : context -> apply_result -> int -> model -> model
	= "camlidl_z3_Z3_apply_result_convert_model"

external mk_solver : context -> solver
	= "camlidl_z3_Z3_mk_solver"

external mk_simple_solver : context -> solver
	= "camlidl_z3_Z3_mk_simple_solver"

external mk_solver_for_logic : context -> symbol -> solver
	= "camlidl_z3_Z3_mk_solver_for_logic"

external mk_solver_from_tactic : context -> tactic -> solver
	= "camlidl_z3_Z3_mk_solver_from_tactic"

external solver_get_help : context -> solver -> string
	= "camlidl_z3_Z3_solver_get_help"

external solver_get_param_descrs : context -> solver -> param_descrs
	= "camlidl_z3_Z3_solver_get_param_descrs"

external solver_set_params : context -> solver -> params -> unit
	= "camlidl_z3_Z3_solver_set_params"

external solver_push : context -> solver -> unit
	= "camlidl_z3_Z3_solver_push"

external solver_pop : context -> solver -> int -> unit
	= "camlidl_z3_Z3_solver_pop"

external solver_reset : context -> solver -> unit
	= "camlidl_z3_Z3_solver_reset"

external solver_get_num_scopes : context -> solver -> int
	= "camlidl_z3_Z3_solver_get_num_scopes"

external solver_assert : context -> solver -> ast -> unit
	= "camlidl_z3_Z3_solver_assert"

external solver_get_assertions : context -> solver -> ast_vector
	= "camlidl_z3_Z3_solver_get_assertions"

external solver_check : context -> solver -> lbool
	= "camlidl_z3_Z3_solver_check"

external solver_check_assumptions : context -> solver -> ast array -> lbool
	= "camlidl_z3_Z3_solver_check_assumptions"

external solver_get_model : context -> solver -> model
	= "camlidl_z3_Z3_solver_get_model"

external solver_get_proof : context -> solver -> ast
	= "camlidl_z3_Z3_solver_get_proof"

external solver_get_unsat_core : context -> solver -> ast_vector
	= "camlidl_z3_Z3_solver_get_unsat_core"

external solver_get_reason_unknown : context -> solver -> string
	= "camlidl_z3_Z3_solver_get_reason_unknown"

external solver_get_statistics : context -> solver -> stats
	= "camlidl_z3_Z3_solver_get_statistics"

external solver_to_string : context -> solver -> string
	= "camlidl_z3_Z3_solver_to_string"


type stat_datum = Stat_int of int | Stat_float of float
type stats_refined = (string, stat_datum) Hashtbl.t

external stats_to_string : context -> stats -> string
	= "camlidl_z3_Z3_stats_to_string"

external stats_size : context -> stats -> int
	= "camlidl_z3_Z3_stats_size"

external stats_get_key : context -> stats -> int -> string
	= "camlidl_z3_Z3_stats_get_key"

external stats_is_uint : context -> stats -> int -> bool
	= "camlidl_z3_Z3_stats_is_uint"

external stats_is_double : context -> stats -> int -> bool
	= "camlidl_z3_Z3_stats_is_double"

external stats_get_uint_value : context -> stats -> int -> int
	= "camlidl_z3_Z3_stats_get_uint_value"

external stats_get_double_value : context -> stats -> int -> float
	= "camlidl_z3_Z3_stats_get_double_value"



(* Internal auxiliary functions: *)
(*
(* Transform a pair of arrays into an array of pairs *)
let array_combine a b =
  if Array.length a <> Array.length b then raise (Invalid_argument "array_combine");
  Array.init (Array.length a) (fun i -> (a.(i), b.(i)))

(* [a |> b] is the pipeline operator for [b(a)] *)
let ( |> ) x f = f x
*)

(* Find the index of an element in an array, raises Not_found is missing *)
let find equal x a =
  let len = Array.length a in
  let rec find_ i =
    if i >= len then
      raise Not_found
    else
      if equal x a.(i) then
        i
      else
        find_ (i+1)
  in
  find_ 0


(* Symbols *)

let symbol_refine c s =
  match get_symbol_kind c s with
  | INT_SYMBOL -> Symbol_int (get_symbol_int c s)
  | STRING_SYMBOL -> Symbol_string (get_symbol_string c s)

let mk_symbol c = function
  | Symbol_int(i) -> mk_int_symbol c i
  | Symbol_string(s) -> mk_string_symbol c s


(* Sorts *)

let get_datatype_sort c s = 
  Array.init (get_datatype_sort_num_constructors c s) (fun i -> 
    let constructor = get_datatype_sort_constructor c s i in
    let recognizer = get_datatype_sort_recognizer c s i in
    let accessors =
      Array.init (get_domain_size c constructor) (fun j ->
        get_datatype_sort_constructor_accessor c s i j
      ) in
    {constructor; recognizer; accessors}
  )

let sort_refine c s =
  match get_sort_kind c s with
  | UNINTERPRETED_SORT -> Sort_uninterpreted (get_sort_name c s)
  | BOOL_SORT -> Sort_bool
  | INT_SORT -> Sort_int
  | BV_SORT -> Sort_bv (get_bv_sort_size c s)
  | FINITE_DOMAIN_SORT ->
      (match get_finite_domain_sort_size c s with
      | Some(sz) -> Sort_finite_domain (get_sort_name c s, sz)
      | None -> failwith "Z3.sort_refine: failed to get size of finite-domain sort"
      )
  | REAL_SORT -> Sort_real
  | ARRAY_SORT -> Sort_array (get_array_sort_domain c s, get_array_sort_range c s)
  | DATATYPE_SORT -> Sort_datatype (get_datatype_sort c s)
  | RELATION_SORT -> Sort_relation (Array.init (get_relation_arity c s) (fun i -> get_relation_column c s i))
  | UNKNOWN_SORT -> Sort_unknown

let mk_sort c = function
  | Sort_uninterpreted(s) -> mk_uninterpreted_sort c s
  | Sort_bool -> mk_bool_sort c
  | Sort_int -> mk_int_sort c
  | Sort_bv(size) -> mk_bv_sort c size
  | Sort_finite_domain(name,size) -> mk_finite_domain_sort c name size
  | Sort_real -> mk_real_sort c
  | Sort_array(domain,range) -> mk_array_sort c domain range
  | Sort_datatype(constructors) -> get_range c constructors.(0).constructor
  | Sort_relation(_) -> invalid_arg "Z3.mk_sort: cannot construct relation sorts"
  | Sort_unknown(_) -> invalid_arg "Z3.mk_sort: cannot construct unknown sorts"


(* Replacement datatypes creation API *)

let mk_datatypes ctx generator =
  let usort0 = mk_uninterpreted_sort ctx (mk_int_symbol ctx 0)
  in
  let rec find_num_sorts i =
    if i = max_int then invalid_arg "mk_datatypes: too many sorts"
    else
    match generator (Array.make i usort0) with
    | None -> find_num_sorts (i+1)
    | Some(a) when Array.length a = i -> i
    | Some _ -> invalid_arg "mk_datatypes: number of sorts and datatype descriptors must be equal"
  in
  let num_sorts = find_num_sorts 0
  in
  let sorts0 = Array.init num_sorts (fun i -> mk_uninterpreted_sort ctx (mk_int_symbol ctx i))
  in
  let ctorss_descriptors =
    match generator sorts0 with
    | Some(ctorss_descriptors) -> ctorss_descriptors
    | None -> invalid_arg "mk_datatypes: generator failed"
  in
  let names = Array.map fst ctorss_descriptors
  in
  let ctorss =
    Array.map (fun (_, ctors_descriptor) ->
      Array.map (fun {constructor_desc; recognizer_desc; accessor_descs} ->
        let field_names = Array.map fst accessor_descs
        in
        let sort_refs = Array.make (Array.length accessor_descs) 0
        in
        let field_sorts =
          Array.mapi (fun i (_, sort) ->
            try
              let j = find (fun s t -> is_eq_sort ctx s t) sort sorts0 in
              sort_refs.(i) <- j ;
              None
            with Not_found ->
              Some(sort)
          ) accessor_descs
        in
        mk_constructor ctx constructor_desc recognizer_desc field_names field_sorts sort_refs
      ) ctors_descriptor
    ) ctorss_descriptors
  in
  let constructor_lists = Array.map (mk_constructor_list ctx) ctorss
  in
  let sorts,_ = mk_datatypes ctx names constructor_lists
  in
  let datatypes =
    Array.mapi (fun i sort ->
      (sort,
       Array.mapi (fun j ctor ->
         let num_fields = Array.length (snd ctorss_descriptors.(i)).(j).accessor_descs in
         let constructor, recognizer, accessors = query_constructor ctx ctor num_fields in
         {constructor; recognizer; accessors}
       ) ctorss.(i))
    ) sorts
  in
  Array.iter (fun ctor_list ->
    del_constructor_list ctx ctor_list
  ) constructor_lists
  ;
  Array.iter (fun ctors ->
    Array.iter (fun ctor ->
      del_constructor ctx ctor
    ) ctors
  ) ctorss
  ;
  datatypes


(* Numerals *)

let rec numeral_refine c t =
  assert( get_ast_kind c t = NUMERAL_AST );
  let sort = get_sort c t in
  let is_int, i = get_numeral_int c t in
  if is_int then 
    Numeral_int (i, sort)
  else
  let is_int64, i = get_numeral_int64 c t in
  if is_int64 then 
    Numeral_int64 (i, sort)
  else
  if get_sort_kind c sort <> REAL_SORT then
    Numeral_large (get_numeral_string c t, sort)
  else
    let n = numeral_refine c (get_numerator c t) in
    let d = numeral_refine c (get_denominator c t) in
    Numeral_rational (n, d)


let to_real c x =
  if get_sort_kind c (get_sort c x) = REAL_SORT then
    x
  else
    mk_int2real c x

let rec embed_numeral c = function
  | Numeral_int (i, s) -> mk_int c i s
  | Numeral_int64 (i, s) -> mk_int64 c i s
  | Numeral_large (l, s) -> mk_numeral c l s
  | Numeral_rational (Numeral_int(n,_), Numeral_int(d,_)) -> mk_real c n d
  | Numeral_rational (n, d) ->
      mk_div c (to_real c (embed_numeral c n)) (to_real c (embed_numeral c d))
      (* Or should the following be used instead?
      let n_str = get_numeral_string c (embed_numeral c n) in
      let d_str = get_numeral_string c (embed_numeral c d) in
      mk_numeral c (n_str ^ " / " ^ d_str) (mk_real_sort c)
      *)

(* Terms *)

let get_app_args c a =
  Array.init (get_app_num_args c a) (get_app_arg c a);;

let get_domains c d =
  Array.init (get_domain_size c d) (get_domain c d);;


let get_pattern_terms c p = 
  Array.init (get_pattern_num_terms c p) (get_pattern c p)


let term_refine c t = 
  match get_ast_kind c t with
  | NUMERAL_AST ->
      Term_numeral (numeral_refine c t)
  | APP_AST ->
      let t' = to_app c t in
      let f = get_app_decl c t' in
      let num_args = get_app_num_args c t' in
      let args = Array.init num_args (get_app_arg c t') in
      let k = get_decl_kind c f in
      Term_app (k, f, args)
  | QUANTIFIER_AST -> 
      let bt = if is_quantifier_forall c t then Forall else Exists in
      let w = get_quantifier_weight c t                            in
      let np = get_quantifier_num_patterns c t                     in
      let pats = Array.init np (get_quantifier_pattern_ast c t)    in
      let pats = Array.map (get_pattern_terms c) pats              in
      let nb = get_quantifier_num_bound c t                        in
      let bound =
        Array.init nb (fun i ->
          (get_quantifier_bound_name c t i, get_quantifier_bound_sort c t i)
        ) in
      let body = get_quantifier_body c t in
      Term_quantifier (bt, w, pats, bound, body)
  | VAR_AST -> 
      Term_var (get_index_value c t, get_sort c t)
  | _ ->
      assert false


(* let mk_term c = function *)
(*   | Term_numeral (numeral, sort) -> mk_numeral c numeral sort *)
(*   | Term_app (kind, decl, args) -> *)
(*   | Term_quantifier (strength, weight, pats, bound, body) -> *)
(*   | Term_var (index, sort) -> *)



(* Refined model API *)

let model_refine c m =
  let num_sorts = model_get_num_sorts c m in
  let sorts = Hashtbl.create num_sorts in
  for i = 0 to num_sorts - 1 do
    let sort = model_get_sort c m i in
    let universe = model_get_sort_universe c m sort in
    Hashtbl.add sorts sort universe
  done;
  let num_consts = model_get_num_consts c m in
  let consts = Hashtbl.create num_consts in
  let arrays = Hashtbl.create 0 in
  for i = 0 to num_consts - 1 do
    let const_decl = model_get_const_decl c m i in
    match model_get_const_interp c m const_decl with
    | Some(const_interp) ->
        if is_as_array c const_interp then
          let array_decl = get_as_array_func_decl c const_interp in
          match model_get_func_interp c m array_decl with
          | Some(array_interp) ->
              let num_entries = func_interp_get_num_entries c array_interp in
              let tbl = Hashtbl.create num_entries in
              for i = 0 to num_entries - 1 do
                let entry = func_interp_get_entry c array_interp i in
                assert( func_entry_get_num_args c entry = 1 );
                let arg = func_entry_get_arg c entry 0 in
                let value = func_entry_get_value c entry in
                Hashtbl.add tbl arg value
              done;
              let default = func_interp_get_else c array_interp in
              Hashtbl.add arrays const_decl (tbl, default)
          | None ->
              ()
        else
          Hashtbl.add consts const_decl const_interp
    | None ->
        ()
  done;
  let num_funcs = model_get_num_funcs c m in
  let funcs = Hashtbl.create num_funcs in
  for i = 0 to num_funcs - 1 do
    let func_decl = model_get_func_decl c m i in
    if not (Hashtbl.mem arrays func_decl) then
      match model_get_func_interp c m func_decl with
      | Some(func_interp) ->
          let num_entries = func_interp_get_num_entries c func_interp in
          let tbl = Hashtbl.create num_entries in
          for i = 0 to num_entries - 1 do
            let entry = func_interp_get_entry c func_interp i in
            let num_args = func_entry_get_num_args c entry in
            let args = Array.init num_args (fun i -> func_entry_get_arg c entry i) in
            let value = func_entry_get_value c entry in
            Hashtbl.add tbl args value
          done;
          let default = func_interp_get_else c func_interp in
          Hashtbl.add funcs func_decl (tbl, default)
      | None ->
          ()
  done;
  {sorts; consts; arrays; funcs}


(* Extended parser API *)

let get_smtlib_formulas c = 
  Array.init (get_smtlib_num_formulas c) (get_smtlib_formula c)

let get_smtlib_assumptions c = 
  Array.init (get_smtlib_num_assumptions c) (get_smtlib_assumption c)

let get_smtlib_decls c =
  Array.init (get_smtlib_num_decls c) (get_smtlib_decl c)

let get_smtlib_parse_results c =
  (get_smtlib_formulas c, get_smtlib_assumptions c, get_smtlib_decls c)

let parse_smtlib_string_x c a1 a2 a3 a4 a5 = 
  parse_smtlib_string c a1 a2 a3 a4 a5 ;
  get_smtlib_parse_results c

let parse_smtlib_file_x c a1 a2 a3 a4 a5 = 
  parse_smtlib_file c a1 a2 a3 a4 a5 ;
  get_smtlib_parse_results c

let parse_smtlib_string_formula c a1 a2 a3 a4 a5 = 
  parse_smtlib_string c a1 a2 a3 a4 a5 ;
  match get_smtlib_formulas c with [|f|] -> f | _ -> failwith "Z3: parse_smtlib_string_formula"

let parse_smtlib_file_formula c a1 a2 a3 a4 a5 = 
  parse_smtlib_file c a1 a2 a3 a4 a5 ;
  match get_smtlib_formulas c with [|f|] -> f | _ -> failwith "Z3: parse_smtlib_file_formula"


(* Error handling *)

let get_error_msg c e =
  match e with
  | PARSER_ERROR -> (get_error_msg_ex c e) ^ ": " ^ (get_smtlib_error c)
  | _ -> get_error_msg_ex c e


(* Refined stats API *)

let stats_refine c s =
  let num_stats = stats_size c s in
  let tbl = Hashtbl.create num_stats in
  for i = 0 to num_stats - 1 do
    let key = stats_get_key c s i in
    let datum =
      if stats_is_uint c s i then
        Stat_int(stats_get_uint_value c s i)
      else
        Stat_float(stats_get_double_value c s i) in
    Hashtbl.add tbl key datum
  done;
  tbl


let _ =
  Printexc.register_printer (function
    | Error(c,e) -> Some ("Z3 "^(get_error_msg c e))
    | _ -> None
  )


module V3 = struct

(* File generated from z3.idl *)

type symbol
and literals
and theory
and config
and context
and sort
and func_decl
and ast
and app
and pattern
and model
and constructor
and constructor_list

and lbool =
  | L_FALSE
  | L_UNDEF
  | L_TRUE

and symbol_kind =
  | INT_SYMBOL
  | STRING_SYMBOL

and parameter_kind =
  | PARAMETER_INT
  | PARAMETER_DOUBLE
  | PARAMETER_RATIONAL
  | PARAMETER_SYMBOL
  | PARAMETER_SORT
  | PARAMETER_AST
  | PARAMETER_FUNC_DECL

and sort_kind =
  | UNINTERPRETED_SORT
  | BOOL_SORT
  | INT_SORT
  | REAL_SORT
  | BV_SORT
  | ARRAY_SORT
  | DATATYPE_SORT
  | RELATION_SORT
  | FINITE_DOMAIN_SORT
  | UNKNOWN_SORT

and ast_kind =
  | NUMERAL_AST
  | APP_AST
  | VAR_AST
  | QUANTIFIER_AST
  | SORT_AST
  | FUNC_DECL_AST
  | UNKNOWN_AST

and decl_kind =
  | OP_TRUE
  | OP_FALSE
  | OP_EQ
  | OP_DISTINCT
  | OP_ITE
  | OP_AND
  | OP_OR
  | OP_IFF
  | OP_XOR
  | OP_NOT
  | OP_IMPLIES
  | OP_OEQ
  | OP_ANUM
  | OP_AGNUM
  | OP_LE
  | OP_GE
  | OP_LT
  | OP_GT
  | OP_ADD
  | OP_SUB
  | OP_UMINUS
  | OP_MUL
  | OP_DIV
  | OP_IDIV
  | OP_REM
  | OP_MOD
  | OP_TO_REAL
  | OP_TO_INT
  | OP_IS_INT
  | OP_POWER
  | OP_STORE
  | OP_SELECT
  | OP_CONST_ARRAY
  | OP_ARRAY_MAP
  | OP_ARRAY_DEFAULT
  | OP_SET_UNION
  | OP_SET_INTERSECT
  | OP_SET_DIFFERENCE
  | OP_SET_COMPLEMENT
  | OP_SET_SUBSET
  | OP_AS_ARRAY
  | OP_BNUM
  | OP_BIT1
  | OP_BIT0
  | OP_BNEG
  | OP_BADD
  | OP_BSUB
  | OP_BMUL
  | OP_BSDIV
  | OP_BUDIV
  | OP_BSREM
  | OP_BUREM
  | OP_BSMOD
  | OP_BSDIV0
  | OP_BUDIV0
  | OP_BSREM0
  | OP_BUREM0
  | OP_BSMOD0
  | OP_ULEQ
  | OP_SLEQ
  | OP_UGEQ
  | OP_SGEQ
  | OP_ULT
  | OP_SLT
  | OP_UGT
  | OP_SGT
  | OP_BAND
  | OP_BOR
  | OP_BNOT
  | OP_BXOR
  | OP_BNAND
  | OP_BNOR
  | OP_BXNOR
  | OP_CONCAT
  | OP_SIGN_EXT
  | OP_ZERO_EXT
  | OP_EXTRACT
  | OP_REPEAT
  | OP_BREDOR
  | OP_BREDAND
  | OP_BCOMP
  | OP_BSHL
  | OP_BLSHR
  | OP_BASHR
  | OP_ROTATE_LEFT
  | OP_ROTATE_RIGHT
  | OP_EXT_ROTATE_LEFT
  | OP_EXT_ROTATE_RIGHT
  | OP_INT2BV
  | OP_BV2INT
  | OP_CARRY
  | OP_XOR3
  | OP_PR_UNDEF
  | OP_PR_TRUE
  | OP_PR_ASSERTED
  | OP_PR_GOAL
  | OP_PR_MODUS_PONENS
  | OP_PR_REFLEXIVITY
  | OP_PR_SYMMETRY
  | OP_PR_TRANSITIVITY
  | OP_PR_TRANSITIVITY_STAR
  | OP_PR_MONOTONICITY
  | OP_PR_QUANT_INTRO
  | OP_PR_DISTRIBUTIVITY
  | OP_PR_AND_ELIM
  | OP_PR_NOT_OR_ELIM
  | OP_PR_REWRITE
  | OP_PR_REWRITE_STAR
  | OP_PR_PULL_QUANT
  | OP_PR_PULL_QUANT_STAR
  | OP_PR_PUSH_QUANT
  | OP_PR_ELIM_UNUSED_VARS
  | OP_PR_DER
  | OP_PR_QUANT_INST
  | OP_PR_HYPOTHESIS
  | OP_PR_LEMMA
  | OP_PR_UNIT_RESOLUTION
  | OP_PR_IFF_TRUE
  | OP_PR_IFF_FALSE
  | OP_PR_COMMUTATIVITY
  | OP_PR_DEF_AXIOM
  | OP_PR_DEF_INTRO
  | OP_PR_APPLY_DEF
  | OP_PR_IFF_OEQ
  | OP_PR_NNF_POS
  | OP_PR_NNF_NEG
  | OP_PR_NNF_STAR
  | OP_PR_CNF_STAR
  | OP_PR_SKOLEMIZE
  | OP_PR_MODUS_PONENS_OEQ
  | OP_PR_TH_LEMMA
  | OP_PR_HYPER_RESOLVE
  | OP_RA_STORE
  | OP_RA_EMPTY
  | OP_RA_IS_EMPTY
  | OP_RA_JOIN
  | OP_RA_UNION
  | OP_RA_WIDEN
  | OP_RA_PROJECT
  | OP_RA_FILTER
  | OP_RA_NEGATION_FILTER
  | OP_RA_RENAME
  | OP_RA_COMPLEMENT
  | OP_RA_SELECT
  | OP_RA_CLONE
  | OP_FD_LT
  | OP_LABEL
  | OP_LABEL_LIT
  | OP_DT_CONSTRUCTOR
  | OP_DT_RECOGNISER
  | OP_DT_ACCESSOR
  | OP_UNINTERPRETED

and param_kind =
  | PK_UINT
  | PK_BOOL
  | PK_DOUBLE
  | PK_SYMBOL
  | PK_STRING
  | PK_OTHER
  | PK_INVALID

and search_failure =
  | NO_FAILURE
  | UNKNOWN
  | TIMEOUT
  | MEMOUT_WATERMARK
  | CANCELED
  | NUM_CONFLICTS
  | THEORY
  | QUANTIFIERS

and ast_print_mode =
  | PRINT_SMTLIB_FULL
  | PRINT_LOW_LEVEL
  | PRINT_SMTLIB_COMPLIANT
  | PRINT_SMTLIB2_COMPLIANT


external mk_config : unit -> config
	= "camlidl_z3V3_Z3_mk_config"

external del_config : config -> unit
	= "camlidl_z3V3_Z3_del_config"

external set_param_value : config -> string -> string -> unit
	= "camlidl_z3V3_Z3_set_param_value"

external mk_context : config -> context
	= "camlidl_z3V3_Z3_mk_context"

external del_context : context -> unit
	= "camlidl_z3V3_Z3_del_context"

external update_param_value : context -> string -> string -> unit
	= "camlidl_z3V3_Z3_update_param_value"

external get_param_value : context -> string -> string option
	= "camlidl_z3V3_Z3_get_param_value"

external mk_int_symbol : context -> int -> symbol
	= "camlidl_z3V3_Z3_mk_int_symbol"

external mk_string_symbol : context -> string -> symbol
	= "camlidl_z3V3_Z3_mk_string_symbol"

external mk_uninterpreted_sort : context -> symbol -> sort
	= "camlidl_z3V3_Z3_mk_uninterpreted_sort"

external mk_bool_sort : context -> sort
	= "camlidl_z3V3_Z3_mk_bool_sort"

external mk_int_sort : context -> sort
	= "camlidl_z3V3_Z3_mk_int_sort"

external mk_real_sort : context -> sort
	= "camlidl_z3V3_Z3_mk_real_sort"

external mk_bv_sort : context -> int -> sort
	= "camlidl_z3V3_Z3_mk_bv_sort"

external mk_finite_domain_sort : context -> symbol -> int64 -> sort
	= "camlidl_z3V3_Z3_mk_finite_domain_sort"

external mk_array_sort : context -> sort -> sort -> sort
	= "camlidl_z3V3_Z3_mk_array_sort"

external mk_tuple_sort : context -> symbol -> symbol array -> sort array -> sort * func_decl * func_decl array
	= "camlidl_z3V3_Z3_mk_tuple_sort"

external mk_enumeration_sort : context -> symbol -> symbol array -> sort * func_decl array * func_decl array
	= "camlidl_z3V3_Z3_mk_enumeration_sort"

external mk_list_sort : context -> symbol -> sort -> sort * func_decl * func_decl * func_decl * func_decl * func_decl * func_decl
	= "camlidl_z3V3_Z3_mk_list_sort"

external mk_constructor : context -> symbol -> symbol -> symbol array -> sort array -> int array -> constructor
	= "camlidl_z3_Z3_mk_constructor_bytecode" "camlidl_z3V3_Z3_mk_constructor"

external del_constructor : context -> constructor -> unit
	= "camlidl_z3V3_Z3_del_constructor"

external mk_datatype : context -> symbol -> constructor array -> sort * constructor array
	= "camlidl_z3V3_Z3_mk_datatype"

external mk_constructor_list : context -> constructor array -> constructor_list
	= "camlidl_z3V3_Z3_mk_constructor_list"

external del_constructor_list : context -> constructor_list -> unit
	= "camlidl_z3V3_Z3_del_constructor_list"

external mk_datatypes : context -> symbol array -> constructor_list array -> sort array * constructor_list array
	= "camlidl_z3V3_Z3_mk_datatypes"

external query_constructor : context -> constructor -> int -> func_decl * func_decl * func_decl array
	= "camlidl_z3V3_Z3_query_constructor"

external mk_func_decl : context -> symbol -> sort array -> sort -> func_decl
	= "camlidl_z3V3_Z3_mk_func_decl"

external mk_app : context -> func_decl -> ast array -> ast
	= "camlidl_z3V3_Z3_mk_app"

external mk_const : context -> symbol -> sort -> ast
	= "camlidl_z3V3_Z3_mk_const"

external mk_fresh_func_decl : context -> string -> sort array -> sort -> func_decl
	= "camlidl_z3V3_Z3_mk_fresh_func_decl"

external mk_fresh_const : context -> string -> sort -> ast
	= "camlidl_z3V3_Z3_mk_fresh_const"

external mk_true : context -> ast
	= "camlidl_z3V3_Z3_mk_true"

external mk_false : context -> ast
	= "camlidl_z3V3_Z3_mk_false"

external mk_eq : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_eq"

external mk_distinct : context -> ast array -> ast
	= "camlidl_z3V3_Z3_mk_distinct"

external mk_not : context -> ast -> ast
	= "camlidl_z3V3_Z3_mk_not"

external mk_ite : context -> ast -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_ite"

external mk_iff : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_iff"

external mk_implies : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_implies"

external mk_xor : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_xor"

external mk_and : context -> ast array -> ast
	= "camlidl_z3V3_Z3_mk_and"

external mk_or : context -> ast array -> ast
	= "camlidl_z3V3_Z3_mk_or"

external mk_add : context -> ast array -> ast
	= "camlidl_z3V3_Z3_mk_add"

external mk_mul : context -> ast array -> ast
	= "camlidl_z3V3_Z3_mk_mul"

external mk_sub : context -> ast array -> ast
	= "camlidl_z3V3_Z3_mk_sub"

external mk_unary_minus : context -> ast -> ast
	= "camlidl_z3V3_Z3_mk_unary_minus"

external mk_div : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_div"

external mk_mod : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_mod"

external mk_rem : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_rem"

external mk_power : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_power"

external mk_lt : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_lt"

external mk_le : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_le"

external mk_gt : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_gt"

external mk_ge : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_ge"

external mk_int2real : context -> ast -> ast
	= "camlidl_z3V3_Z3_mk_int2real"

external mk_real2int : context -> ast -> ast
	= "camlidl_z3V3_Z3_mk_real2int"

external mk_is_int : context -> ast -> ast
	= "camlidl_z3V3_Z3_mk_is_int"

external mk_bvnot : context -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvnot"

external mk_bvredand : context -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvredand"

external mk_bvredor : context -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvredor"

external mk_bvand : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvand"

external mk_bvor : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvor"

external mk_bvxor : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvxor"

external mk_bvnand : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvnand"

external mk_bvnor : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvnor"

external mk_bvxnor : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvxnor"

external mk_bvneg : context -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvneg"

external mk_bvadd : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvadd"

external mk_bvsub : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvsub"

external mk_bvmul : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvmul"

external mk_bvudiv : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvudiv"

external mk_bvsdiv : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvsdiv"

external mk_bvurem : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvurem"

external mk_bvsrem : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvsrem"

external mk_bvsmod : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvsmod"

external mk_bvult : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvult"

external mk_bvslt : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvslt"

external mk_bvule : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvule"

external mk_bvsle : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvsle"

external mk_bvuge : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvuge"

external mk_bvsge : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvsge"

external mk_bvugt : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvugt"

external mk_bvsgt : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvsgt"

external mk_concat : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_concat"

external mk_extract : context -> int -> int -> ast -> ast
	= "camlidl_z3V3_Z3_mk_extract"

external mk_sign_ext : context -> int -> ast -> ast
	= "camlidl_z3V3_Z3_mk_sign_ext"

external mk_zero_ext : context -> int -> ast -> ast
	= "camlidl_z3V3_Z3_mk_zero_ext"

external mk_repeat : context -> int -> ast -> ast
	= "camlidl_z3V3_Z3_mk_repeat"

external mk_bvshl : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvshl"

external mk_bvlshr : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvlshr"

external mk_bvashr : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvashr"

external mk_rotate_left : context -> int -> ast -> ast
	= "camlidl_z3V3_Z3_mk_rotate_left"

external mk_rotate_right : context -> int -> ast -> ast
	= "camlidl_z3V3_Z3_mk_rotate_right"

external mk_ext_rotate_left : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_ext_rotate_left"

external mk_ext_rotate_right : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_ext_rotate_right"

external mk_int2bv : context -> int -> ast -> ast
	= "camlidl_z3V3_Z3_mk_int2bv"

external mk_bv2int : context -> ast -> bool -> ast
	= "camlidl_z3V3_Z3_mk_bv2int"

external mk_bvadd_no_overflow : context -> ast -> ast -> bool -> ast
	= "camlidl_z3V3_Z3_mk_bvadd_no_overflow"

external mk_bvadd_no_underflow : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvadd_no_underflow"

external mk_bvsub_no_overflow : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvsub_no_overflow"

external mk_bvsub_no_underflow : context -> ast -> ast -> bool -> ast
	= "camlidl_z3V3_Z3_mk_bvsub_no_underflow"

external mk_bvsdiv_no_overflow : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvsdiv_no_overflow"

external mk_bvneg_no_overflow : context -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvneg_no_overflow"

external mk_bvmul_no_overflow : context -> ast -> ast -> bool -> ast
	= "camlidl_z3V3_Z3_mk_bvmul_no_overflow"

external mk_bvmul_no_underflow : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_bvmul_no_underflow"

external mk_select : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_select"

external mk_store : context -> ast -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_store"

external mk_const_array : context -> sort -> ast -> ast
	= "camlidl_z3V3_Z3_mk_const_array"

external mk_map : context -> func_decl -> int -> ast -> ast
	= "camlidl_z3V3_Z3_mk_map"

external mk_array_default : context -> ast -> ast
	= "camlidl_z3V3_Z3_mk_array_default"

external mk_set_sort : context -> sort -> sort
	= "camlidl_z3V3_Z3_mk_set_sort"

external mk_empty_set : context -> sort -> ast
	= "camlidl_z3V3_Z3_mk_empty_set"

external mk_full_set : context -> sort -> ast
	= "camlidl_z3V3_Z3_mk_full_set"

external mk_set_add : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_set_add"

external mk_set_del : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_set_del"

external mk_set_union : context -> ast array -> ast
	= "camlidl_z3V3_Z3_mk_set_union"

external mk_set_intersect : context -> ast array -> ast
	= "camlidl_z3V3_Z3_mk_set_intersect"

external mk_set_difference : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_set_difference"

external mk_set_complement : context -> ast -> ast
	= "camlidl_z3V3_Z3_mk_set_complement"

external mk_set_member : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_set_member"

external mk_set_subset : context -> ast -> ast -> ast
	= "camlidl_z3V3_Z3_mk_set_subset"

external mk_numeral : context -> string -> sort -> ast
	= "camlidl_z3V3_Z3_mk_numeral"

external mk_real : context -> int -> int -> ast
	= "camlidl_z3V3_Z3_mk_real"

external mk_int : context -> int -> sort -> ast
	= "camlidl_z3V3_Z3_mk_int"

external mk_int64 : context -> int64 -> sort -> ast
	= "camlidl_z3V3_Z3_mk_int64"

external mk_pattern : context -> ast array -> pattern
	= "camlidl_z3V3_Z3_mk_pattern"

external mk_bound : context -> int -> sort -> ast
	= "camlidl_z3V3_Z3_mk_bound"

external mk_forall : context -> int -> pattern array -> sort array -> symbol array -> ast -> ast
	= "camlidl_z3_Z3_mk_forall_bytecode" "camlidl_z3V3_Z3_mk_forall"

external mk_exists : context -> int -> pattern array -> sort array -> symbol array -> ast -> ast
	= "camlidl_z3_Z3_mk_exists_bytecode" "camlidl_z3V3_Z3_mk_exists"

external mk_quantifier : context -> bool -> int -> pattern array -> sort array -> symbol array -> ast -> ast
	= "camlidl_z3_Z3_mk_quantifier_bytecode" "camlidl_z3V3_Z3_mk_quantifier"

external mk_quantifier_ex : context -> bool -> int -> symbol -> symbol -> pattern array -> ast array -> sort array -> symbol array -> ast -> ast
	= "camlidl_z3_Z3_mk_quantifier_ex_bytecode" "camlidl_z3V3_Z3_mk_quantifier_ex"

external mk_forall_const : context -> int -> app array -> pattern array -> ast -> ast
	= "camlidl_z3V3_Z3_mk_forall_const"

external mk_exists_const : context -> int -> app array -> pattern array -> ast -> ast
	= "camlidl_z3V3_Z3_mk_exists_const"

external mk_quantifier_const : context -> bool -> int -> app array -> pattern array -> ast -> ast
	= "camlidl_z3_Z3_mk_quantifier_const_bytecode" "camlidl_z3V3_Z3_mk_quantifier_const"

external mk_quantifier_const_ex : context -> bool -> int -> symbol -> symbol -> app array -> pattern array -> ast array -> ast -> ast
	= "camlidl_z3_Z3_mk_quantifier_const_ex_bytecode" "camlidl_z3V3_Z3_mk_quantifier_const_ex"

external get_symbol_kind : context -> symbol -> symbol_kind
	= "camlidl_z3V3_Z3_get_symbol_kind"

external get_symbol_int : context -> symbol -> int
	= "camlidl_z3V3_Z3_get_symbol_int"

external get_symbol_string : context -> symbol -> string
	= "camlidl_z3V3_Z3_get_symbol_string"

external get_sort_name : context -> sort -> symbol
	= "camlidl_z3V3_Z3_get_sort_name"

external get_sort_id : context -> sort -> int
	= "camlidl_z3V3_Z3_get_sort_id"

external sort_to_ast : context -> sort -> ast
	= "camlidl_z3V3_Z3_sort_to_ast"

external is_eq_sort : context -> sort -> sort -> bool
	= "camlidl_z3V3_Z3_is_eq_sort"

external get_sort_kind : context -> sort -> sort_kind
	= "camlidl_z3V3_Z3_get_sort_kind"

external get_bv_sort_size : context -> sort -> int
	= "camlidl_z3V3_Z3_get_bv_sort_size"

external get_finite_domain_sort_size : context -> sort -> int64 option
	= "camlidl_z3V3_Z3_get_finite_domain_sort_size"

external get_array_sort_domain : context -> sort -> sort
	= "camlidl_z3V3_Z3_get_array_sort_domain"

external get_array_sort_range : context -> sort -> sort
	= "camlidl_z3V3_Z3_get_array_sort_range"

external get_tuple_sort_mk_decl : context -> sort -> func_decl
	= "camlidl_z3V3_Z3_get_tuple_sort_mk_decl"

external get_tuple_sort_num_fields : context -> sort -> int
	= "camlidl_z3V3_Z3_get_tuple_sort_num_fields"

external get_tuple_sort_field_decl : context -> sort -> int -> func_decl
	= "camlidl_z3V3_Z3_get_tuple_sort_field_decl"

external get_datatype_sort_num_constructors : context -> sort -> int
	= "camlidl_z3V3_Z3_get_datatype_sort_num_constructors"

external get_datatype_sort_constructor : context -> sort -> int -> func_decl
	= "camlidl_z3V3_Z3_get_datatype_sort_constructor"

external get_datatype_sort_recognizer : context -> sort -> int -> func_decl
	= "camlidl_z3V3_Z3_get_datatype_sort_recognizer"

external get_datatype_sort_constructor_accessor : context -> sort -> int -> int -> func_decl
	= "camlidl_z3V3_Z3_get_datatype_sort_constructor_accessor"

external get_relation_arity : context -> sort -> int
	= "camlidl_z3V3_Z3_get_relation_arity"

external get_relation_column : context -> sort -> int -> sort
	= "camlidl_z3V3_Z3_get_relation_column"

external func_decl_to_ast : context -> func_decl -> ast
	= "camlidl_z3V3_Z3_func_decl_to_ast"

external is_eq_func_decl : context -> func_decl -> func_decl -> bool
	= "camlidl_z3V3_Z3_is_eq_func_decl"

external get_func_decl_id : context -> func_decl -> int
	= "camlidl_z3V3_Z3_get_func_decl_id"

external get_decl_name : context -> func_decl -> symbol
	= "camlidl_z3V3_Z3_get_decl_name"

external get_decl_kind : context -> func_decl -> decl_kind
	= "camlidl_z3V3_Z3_get_decl_kind"

external get_domain_size : context -> func_decl -> int
	= "camlidl_z3V3_Z3_get_domain_size"

external get_arity : context -> func_decl -> int
	= "camlidl_z3V3_Z3_get_arity"

external get_domain : context -> func_decl -> int -> sort
	= "camlidl_z3V3_Z3_get_domain"

external get_range : context -> func_decl -> sort
	= "camlidl_z3V3_Z3_get_range"

external get_decl_num_parameters : context -> func_decl -> int
	= "camlidl_z3V3_Z3_get_decl_num_parameters"

external get_decl_parameter_kind : context -> func_decl -> int -> parameter_kind
	= "camlidl_z3V3_Z3_get_decl_parameter_kind"

external get_decl_int_parameter : context -> func_decl -> int -> int
	= "camlidl_z3V3_Z3_get_decl_int_parameter"

external get_decl_double_parameter : context -> func_decl -> int -> float
	= "camlidl_z3V3_Z3_get_decl_double_parameter"

external get_decl_symbol_parameter : context -> func_decl -> int -> symbol
	= "camlidl_z3V3_Z3_get_decl_symbol_parameter"

external get_decl_sort_parameter : context -> func_decl -> int -> sort
	= "camlidl_z3V3_Z3_get_decl_sort_parameter"

external get_decl_ast_parameter : context -> func_decl -> int -> ast
	= "camlidl_z3V3_Z3_get_decl_ast_parameter"

external get_decl_func_decl_parameter : context -> func_decl -> int -> func_decl
	= "camlidl_z3V3_Z3_get_decl_func_decl_parameter"

external get_decl_rational_parameter : context -> func_decl -> int -> string
	= "camlidl_z3V3_Z3_get_decl_rational_parameter"

external app_to_ast : context -> app -> ast
	= "camlidl_z3V3_Z3_app_to_ast"

external get_app_decl : context -> app -> func_decl
	= "camlidl_z3V3_Z3_get_app_decl"

external get_app_num_args : context -> app -> int
	= "camlidl_z3V3_Z3_get_app_num_args"

external get_app_arg : context -> app -> int -> ast
	= "camlidl_z3V3_Z3_get_app_arg"

external is_eq_ast : context -> ast -> ast -> bool
	= "camlidl_z3V3_Z3_is_eq_ast"

external get_ast_id : context -> ast -> int
	= "camlidl_z3V3_Z3_get_ast_id"

external get_ast_hash : context -> ast -> int
	= "camlidl_z3V3_Z3_get_ast_hash"

external get_sort : context -> ast -> sort
	= "camlidl_z3V3_Z3_get_sort"

external is_well_sorted : context -> ast -> bool
	= "camlidl_z3V3_Z3_is_well_sorted"

external get_bool_value : context -> ast -> lbool
	= "camlidl_z3V3_Z3_get_bool_value"

external get_ast_kind : context -> ast -> ast_kind
	= "camlidl_z3V3_Z3_get_ast_kind"

external is_app : context -> ast -> bool
	= "camlidl_z3V3_Z3_is_app"

external is_numeral_ast : context -> ast -> bool
	= "camlidl_z3V3_Z3_is_numeral_ast"

external is_algebraic_number : context -> ast -> bool
	= "camlidl_z3V3_Z3_is_algebraic_number"

external to_app : context -> ast -> app
	= "camlidl_z3V3_Z3_to_app"

external to_func_decl : context -> ast -> func_decl
	= "camlidl_z3V3_Z3_to_func_decl"

external get_numeral_string : context -> ast -> string
	= "camlidl_z3V3_Z3_get_numeral_string"

external get_numeral_decimal_string : context -> ast -> int -> string
	= "camlidl_z3V3_Z3_get_numeral_decimal_string"

external get_numerator : context -> ast -> ast
	= "camlidl_z3V3_Z3_get_numerator"

external get_denominator : context -> ast -> ast
	= "camlidl_z3V3_Z3_get_denominator"

external get_numeral_small : context -> ast -> bool * int64 * int64
	= "camlidl_z3V3_Z3_get_numeral_small"

external get_numeral_int : context -> ast -> bool * int
	= "camlidl_z3V3_Z3_get_numeral_int"

external get_numeral_int64 : context -> ast -> bool * int64
	= "camlidl_z3V3_Z3_get_numeral_int64"

external get_numeral_rational_int64 : context -> ast -> bool * int64 * int64
	= "camlidl_z3V3_Z3_get_numeral_rational_int64"

external get_algebraic_number_lower : context -> ast -> int -> ast
	= "camlidl_z3V3_Z3_get_algebraic_number_lower"

external get_algebraic_number_upper : context -> ast -> int -> ast
	= "camlidl_z3V3_Z3_get_algebraic_number_upper"

external pattern_to_ast : context -> pattern -> ast
	= "camlidl_z3V3_Z3_pattern_to_ast"

external get_pattern_num_terms : context -> pattern -> int
	= "camlidl_z3V3_Z3_get_pattern_num_terms"

external get_pattern : context -> pattern -> int -> ast
	= "camlidl_z3V3_Z3_get_pattern"

external get_index_value : context -> ast -> int
	= "camlidl_z3V3_Z3_get_index_value"

external is_quantifier_forall : context -> ast -> bool
	= "camlidl_z3V3_Z3_is_quantifier_forall"

external get_quantifier_weight : context -> ast -> int
	= "camlidl_z3V3_Z3_get_quantifier_weight"

external get_quantifier_num_patterns : context -> ast -> int
	= "camlidl_z3V3_Z3_get_quantifier_num_patterns"

external get_quantifier_pattern_ast : context -> ast -> int -> pattern
	= "camlidl_z3V3_Z3_get_quantifier_pattern_ast"

external get_quantifier_num_no_patterns : context -> ast -> int
	= "camlidl_z3V3_Z3_get_quantifier_num_no_patterns"

external get_quantifier_no_pattern_ast : context -> ast -> int -> ast
	= "camlidl_z3V3_Z3_get_quantifier_no_pattern_ast"

external get_quantifier_num_bound : context -> ast -> int
	= "camlidl_z3V3_Z3_get_quantifier_num_bound"

external get_quantifier_bound_name : context -> ast -> int -> symbol
	= "camlidl_z3V3_Z3_get_quantifier_bound_name"

external get_quantifier_bound_sort : context -> ast -> int -> sort
	= "camlidl_z3V3_Z3_get_quantifier_bound_sort"

external get_quantifier_body : context -> ast -> ast
	= "camlidl_z3V3_Z3_get_quantifier_body"

external simplify : context -> ast -> ast
	= "camlidl_z3V3_Z3_simplify"

external update_term : context -> ast -> ast array -> ast
	= "camlidl_z3V3_Z3_update_term"

external substitute : context -> ast -> ast array -> ast array -> ast
	= "camlidl_z3V3_Z3_substitute"

external substitute_vars : context -> ast -> ast array -> ast
	= "camlidl_z3V3_Z3_substitute_vars"

external open_log : string -> bool
	= "camlidl_z3V3_Z3_open_log"

external append_log : string -> unit
	= "camlidl_z3V3_Z3_append_log"

external close_log : unit -> unit
	= "camlidl_z3V3_Z3_close_log"

external toggle_warning_messages : bool -> unit
	= "camlidl_z3V3_Z3_toggle_warning_messages"

external set_ast_print_mode : context -> ast_print_mode -> unit
	= "camlidl_z3V3_Z3_set_ast_print_mode"

external ast_to_string : context -> ast -> string
	= "camlidl_z3V3_Z3_ast_to_string"

external pattern_to_string : context -> pattern -> string
	= "camlidl_z3V3_Z3_pattern_to_string"

external sort_to_string : context -> sort -> string
	= "camlidl_z3V3_Z3_sort_to_string"

external func_decl_to_string : context -> func_decl -> string
	= "camlidl_z3V3_Z3_func_decl_to_string"

external model_to_string : context -> model -> string
	= "camlidl_z3V3_Z3_model_to_string"

external benchmark_to_smtlib_string : context -> string -> string -> string -> string -> ast array -> ast -> string
	= "camlidl_z3_Z3_benchmark_to_smtlib_string_bytecode" "camlidl_z3V3_Z3_benchmark_to_smtlib_string"

external parse_smtlib2_string : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> ast
	= "camlidl_z3_Z3_parse_smtlib2_string_bytecode" "camlidl_z3V3_Z3_parse_smtlib2_string"

external parse_smtlib2_file : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> ast
	= "camlidl_z3_Z3_parse_smtlib2_file_bytecode" "camlidl_z3V3_Z3_parse_smtlib2_file"

external parse_smtlib_string : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> unit
	= "camlidl_z3_Z3_parse_smtlib_string_bytecode" "camlidl_z3V3_Z3_parse_smtlib_string"

external parse_smtlib_file : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> unit
	= "camlidl_z3_Z3_parse_smtlib_file_bytecode" "camlidl_z3V3_Z3_parse_smtlib_file"

external get_smtlib_num_formulas : context -> int
	= "camlidl_z3V3_Z3_get_smtlib_num_formulas"

external get_smtlib_formula : context -> int -> ast
	= "camlidl_z3V3_Z3_get_smtlib_formula"

external get_smtlib_num_assumptions : context -> int
	= "camlidl_z3V3_Z3_get_smtlib_num_assumptions"

external get_smtlib_assumption : context -> int -> ast
	= "camlidl_z3V3_Z3_get_smtlib_assumption"

external get_smtlib_num_decls : context -> int
	= "camlidl_z3V3_Z3_get_smtlib_num_decls"

external get_smtlib_decl : context -> int -> func_decl
	= "camlidl_z3V3_Z3_get_smtlib_decl"

external get_smtlib_num_sorts : context -> int
	= "camlidl_z3V3_Z3_get_smtlib_num_sorts"

external get_smtlib_sort : context -> int -> sort
	= "camlidl_z3V3_Z3_get_smtlib_sort"

external get_smtlib_error : context -> string
	= "camlidl_z3V3_Z3_get_smtlib_error"

external parse_z3_string : context -> string -> ast
	= "camlidl_z3_Z3_parse_z3V3_string"

external parse_z3_file : context -> string -> ast
	= "camlidl_z3_Z3_parse_z3V3_file"

external get_version : unit -> int * int * int * int
	= "camlidl_z3V3_Z3_get_version"

external reset_memory : unit -> unit
	= "camlidl_z3V3_Z3_reset_memory"

external theory_mk_sort : context -> theory -> symbol -> sort
	= "camlidl_z3V3_Z3_theory_mk_sort"

external theory_mk_value : context -> theory -> symbol -> sort -> ast
	= "camlidl_z3V3_Z3_theory_mk_value"

external theory_mk_constant : context -> theory -> symbol -> sort -> ast
	= "camlidl_z3V3_Z3_theory_mk_constant"

external theory_mk_func_decl : context -> theory -> symbol -> sort array -> sort -> func_decl
	= "camlidl_z3V3_Z3_theory_mk_func_decl"

external theory_get_context : theory -> context
	= "camlidl_z3V3_Z3_theory_get_context"

external theory_assert_axiom : theory -> ast -> unit
	= "camlidl_z3V3_Z3_theory_assert_axiom"

external theory_assume_eq : theory -> ast -> ast -> unit
	= "camlidl_z3V3_Z3_theory_assume_eq"

external theory_enable_axiom_simplification : theory -> bool -> unit
	= "camlidl_z3V3_Z3_theory_enable_axiom_simplification"

external theory_get_eqc_root : theory -> ast -> ast
	= "camlidl_z3V3_Z3_theory_get_eqc_root"

external theory_get_eqc_next : theory -> ast -> ast
	= "camlidl_z3V3_Z3_theory_get_eqc_next"

external theory_get_num_parents : theory -> ast -> int
	= "camlidl_z3V3_Z3_theory_get_num_parents"

external theory_get_parent : theory -> ast -> int -> ast
	= "camlidl_z3V3_Z3_theory_get_parent"

external theory_is_value : theory -> ast -> bool
	= "camlidl_z3V3_Z3_theory_is_value"

external theory_is_decl : theory -> func_decl -> bool
	= "camlidl_z3V3_Z3_theory_is_decl"

external theory_get_num_elems : theory -> int
	= "camlidl_z3V3_Z3_theory_get_num_elems"

external theory_get_elem : theory -> int -> ast
	= "camlidl_z3V3_Z3_theory_get_elem"

external theory_get_num_apps : theory -> int
	= "camlidl_z3V3_Z3_theory_get_num_apps"

external theory_get_app : theory -> int -> ast
	= "camlidl_z3V3_Z3_theory_get_app"

external mk_injective_function : context -> symbol -> sort array -> sort -> func_decl
	= "camlidl_z3V3_Z3_mk_injective_function"

external set_logic : context -> string -> bool
	= "camlidl_z3V3_Z3_set_logic"

external push : context -> unit
	= "camlidl_z3V3_Z3_push"

external pop : context -> int -> unit
	= "camlidl_z3V3_Z3_pop"

external get_num_scopes : context -> int
	= "camlidl_z3V3_Z3_get_num_scopes"

external persist_ast : context -> ast -> int -> unit
	= "camlidl_z3V3_Z3_persist_ast"

external assert_cnstr : context -> ast -> unit
	= "camlidl_z3V3_Z3_assert_cnstr"

external check_and_get_model : context -> lbool * model
	= "camlidl_z3V3_Z3_check_and_get_model"

external check : context -> lbool
	= "camlidl_z3V3_Z3_check"

external check_assumptions : context -> ast array -> int -> ast array -> lbool * model * ast * int * ast array
	= "camlidl_z3V3_Z3_check_assumptions"

external get_implied_equalities : context -> ast array -> lbool * int array
	= "camlidl_z3V3_Z3_get_implied_equalities"

external del_model : context -> model -> unit
	= "camlidl_z3V3_Z3_del_model"

external soft_check_cancel : context -> unit
	= "camlidl_z3V3_Z3_soft_check_cancel"

external get_search_failure : context -> search_failure
	= "camlidl_z3V3_Z3_get_search_failure"

external mk_label : context -> symbol -> bool -> ast -> ast
	= "camlidl_z3V3_Z3_mk_label"

external get_relevant_labels : context -> literals
	= "camlidl_z3V3_Z3_get_relevant_labels"

external get_relevant_literals : context -> literals
	= "camlidl_z3V3_Z3_get_relevant_literals"

external get_guessed_literals : context -> literals
	= "camlidl_z3V3_Z3_get_guessed_literals"

external del_literals : context -> literals -> unit
	= "camlidl_z3V3_Z3_del_literals"

external get_num_literals : context -> literals -> int
	= "camlidl_z3V3_Z3_get_num_literals"

external get_label_symbol : context -> literals -> int -> symbol
	= "camlidl_z3V3_Z3_get_label_symbol"

external get_literal : context -> literals -> int -> ast
	= "camlidl_z3V3_Z3_get_literal"

external disable_literal : context -> literals -> int -> unit
	= "camlidl_z3V3_Z3_disable_literal"

external block_literals : context -> literals -> unit
	= "camlidl_z3V3_Z3_block_literals"

external get_model_num_constants : context -> model -> int
	= "camlidl_z3V3_Z3_get_model_num_constants"

external get_model_constant : context -> model -> int -> func_decl
	= "camlidl_z3V3_Z3_get_model_constant"

external get_model_num_funcs : context -> model -> int
	= "camlidl_z3V3_Z3_get_model_num_funcs"

external get_model_func_decl : context -> model -> int -> func_decl
	= "camlidl_z3V3_Z3_get_model_func_decl"

external eval_func_decl : context -> model -> func_decl -> bool * ast
	= "camlidl_z3V3_Z3_eval_func_decl"

external is_array_value : context -> model -> ast -> bool * int
	= "camlidl_z3V3_Z3_is_array_value"

external get_array_value : context -> model -> ast -> ast array -> ast array -> ast array * ast array * ast
	= "camlidl_z3V3_Z3_get_array_value"

external get_model_func_else : context -> model -> int -> ast
	= "camlidl_z3V3_Z3_get_model_func_else"

external get_model_func_num_entries : context -> model -> int -> int
	= "camlidl_z3V3_Z3_get_model_func_num_entries"

external get_model_func_entry_num_args : context -> model -> int -> int -> int
	= "camlidl_z3V3_Z3_get_model_func_entry_num_args"

external get_model_func_entry_arg : context -> model -> int -> int -> int -> ast
	= "camlidl_z3V3_Z3_get_model_func_entry_arg"

external get_model_func_entry_value : context -> model -> int -> int -> ast
	= "camlidl_z3V3_Z3_get_model_func_entry_value"

external eval : context -> model -> ast -> bool * ast
	= "camlidl_z3V3_Z3_eval"

external eval_decl : context -> model -> func_decl -> ast array -> bool * ast
	= "camlidl_z3V3_Z3_eval_decl"

external context_to_string : context -> string
	= "camlidl_z3V3_Z3_context_to_string"

external statistics_to_string : context -> string
	= "camlidl_z3V3_Z3_statistics_to_string"

external get_context_assignment : context -> ast
	= "camlidl_z3V3_Z3_get_context_assignment"




(* Internal auxillary functions: *)

(* Transform a pair of arrays into an array of pairs *)
let array_combine a b =
  if Array.length a <> Array.length b then raise (Invalid_argument "array_combine");
  Array.init (Array.length a) (fun i->(a.(i),b.(i)));;

(* [a |> b] is the pipeline operator for [b(a)] *)
let ( |> ) x f = f x;;


(* Extensions, except for refinement: *)
let mk_context_x configs = 
  let config = mk_config() in
  let f(param_id,param_value) = set_param_value config param_id param_value in
  Array.iter f configs;
  let context = mk_context config in
  del_config config;
  context;;

let get_app_args c a =
  Array.init (get_app_num_args c a) (get_app_arg c a);;

let get_domains c d =
  Array.init (get_domain_size c d) (get_domain c d);;

let get_array_sort c t = (get_array_sort_domain c t, get_array_sort_range c t);;

let get_tuple_sort c ty = 
  (get_tuple_sort_mk_decl c ty,
   Array.init (get_tuple_sort_num_fields c ty) (get_tuple_sort_field_decl c ty));;

type datatype_constructor_refined = { 
   constructor : func_decl; 
   recognizer : func_decl; 
   accessors : func_decl array 
}

let get_datatype_sort c ty = 
  Array.init (get_datatype_sort_num_constructors c ty)
  (fun idx_c -> 
   let constr = get_datatype_sort_constructor c ty idx_c in
   let recog = get_datatype_sort_recognizer  c ty idx_c in
   let num_acc = get_domain_size c constr in
   { constructor = constr;
     recognizer = recog;
     accessors = Array.init num_acc (get_datatype_sort_constructor_accessor c ty idx_c);
   })

let get_model_constants c m =
  Array.init (get_model_num_constants c m) (get_model_constant c m);;


let get_model_func_entry c m i j =
  (Array.init
     (get_model_func_entry_num_args c m i j)
     (get_model_func_entry_arg c m i j),
   get_model_func_entry_value c m i j);;

let get_model_func_entries c m i =
  Array.init (get_model_func_num_entries c m i) (get_model_func_entry c m i);;

let get_model_funcs c m =
  Array.init (get_model_num_funcs c m)
    (fun i->(get_model_func_decl c m i |> get_decl_name c,
             get_model_func_entries c m i,
             get_model_func_else c m i));;
 
let get_smtlib_formulas c = 
  Array.init (get_smtlib_num_formulas c) (get_smtlib_formula c);;

let get_smtlib_assumptions c = 
  Array.init (get_smtlib_num_assumptions c) (get_smtlib_assumption c);;

let get_smtlib_decls c =
  Array.init (get_smtlib_num_decls c) (get_smtlib_decl c);;

let get_smtlib_parse_results c =
  (get_smtlib_formulas c, get_smtlib_assumptions c, get_smtlib_decls c);;

let parse_smtlib_string_formula c a1 a2 a3 a4 a5 = 
  (parse_smtlib_string c a1 a2 a3 a4 a5;
   match get_smtlib_formulas c with [|f|] -> f | _ -> failwith "Z3: parse_smtlib_string_formula");;

let parse_smtlib_file_formula c a1 a2 a3 a4 a5 = 
  (parse_smtlib_file c a1 a2 a3 a4 a5;
   match get_smtlib_formulas c with [|f|] -> f | _ -> failwith "Z3: parse_smtlib_file_formula");;

let parse_smtlib_string_x c a1 a2 a3 a4 a5 = 
  (parse_smtlib_string c a1 a2 a3 a4 a5; get_smtlib_parse_results c);;

let parse_smtlib_file_x c a1 a2 a3 a4 a5 = 
  (parse_smtlib_file c a1 a2 a3 a4 a5; get_smtlib_parse_results c);;

(* Refinement: *)

type symbol_refined =
  | Symbol_int of int
  | Symbol_string of string
  | Symbol_unknown;;

let symbol_refine c s =
  match get_symbol_kind c s with
  | INT_SYMBOL -> Symbol_int (get_symbol_int c s)
  | STRING_SYMBOL -> Symbol_string (get_symbol_string c s);;

type sort_refined =
  | Sort_uninterpreted of symbol
  | Sort_bool
  | Sort_int
  | Sort_real
  | Sort_bv of int
  | Sort_array of (sort * sort)
  | Sort_datatype of datatype_constructor_refined array
  | Sort_relation
  | Sort_finite_domain
  | Sort_unknown of symbol;;

let sort_refine c ty =
  match get_sort_kind c ty with
  | UNINTERPRETED_SORT -> Sort_uninterpreted (get_sort_name c ty)
  | BOOL_SORT -> Sort_bool
  | INT_SORT -> Sort_int
  | REAL_SORT -> Sort_real
  | BV_SORT -> Sort_bv (get_bv_sort_size c ty)
  | ARRAY_SORT -> Sort_array (get_array_sort_domain c ty, get_array_sort_range c ty)
  | DATATYPE_SORT -> Sort_datatype (get_datatype_sort c ty)
  | RELATION_SORT -> Sort_relation 
  | FINITE_DOMAIN_SORT -> Sort_finite_domain
  | UNKNOWN_SORT -> Sort_unknown (get_sort_name c ty);;

let get_pattern_terms c p = 
  Array.init (get_pattern_num_terms c p) (get_pattern c p)

type binder_type = | Forall | Exists 

type numeral_refined = 
  | Numeral_small  of int64 * int64
  | Numeral_large  of string

type term_refined = 
  | Term_app        of decl_kind * func_decl * ast array
  | Term_quantifier of binder_type * int * ast array array * (symbol *sort) array * ast
  | Term_numeral    of numeral_refined * sort
  | Term_var        of int * sort

let term_refine c t = 
  match get_ast_kind c t with
  | NUMERAL_AST -> 
      let (is_small, n, d) = get_numeral_small c t in
      if is_small then 
	Term_numeral(Numeral_small(n,d), get_sort c t)
      else
	Term_numeral(Numeral_large(get_numeral_string c t), get_sort c t)
  | APP_AST   -> 
      let t' = to_app c t in
      let f =  get_app_decl c t' in
      let num_args = get_app_num_args c t' in
      let args = Array.init num_args (get_app_arg c t') in
      let k = get_decl_kind c f in
      Term_app (k, f, args)
  | QUANTIFIER_AST -> 
      let bt = if is_quantifier_forall c t then Forall else Exists in
      let w = get_quantifier_weight c t                            in
      let np = get_quantifier_num_patterns c t                     in
      let pats = Array.init np (get_quantifier_pattern_ast c t)    in
      let pats = Array.map (get_pattern_terms c) pats              in
      let nb = get_quantifier_num_bound c t                        in
      let bound = Array.init nb 
	  (fun i -> (get_quantifier_bound_name c t i, get_quantifier_bound_sort c t i)) in
      let body = get_quantifier_body c t in
      Term_quantifier(bt, w, pats, bound, body)
  | VAR_AST -> 
      Term_var(get_index_value c t, get_sort c t)
  | _ -> assert false
  
type theory_callbacks = 
  {
     mutable delete_theory : unit -> unit;
     mutable reduce_eq : ast -> ast -> ast option;
     mutable reduce_app : func_decl -> ast array -> ast option;
     mutable reduce_distinct : ast array -> ast option;
     mutable final_check : unit -> bool;
     mutable new_app : ast -> unit;
     mutable new_elem : ast -> unit;
     mutable init_search: unit -> unit;
     mutable push: unit -> unit;
     mutable pop: unit -> unit;
     mutable restart : unit -> unit;
     mutable reset: unit -> unit;
     mutable new_eq : ast -> ast -> unit;
     mutable new_diseq : ast -> ast -> unit;
     mutable new_assignment: ast -> bool -> unit;
     mutable new_relevant : ast -> unit;
  }

let mk_theory_callbacks() = 
    {
     delete_theory = (fun () -> ());
     reduce_eq = (fun _ _ -> None);
     reduce_app = (fun _ _ -> None);
     reduce_distinct = (fun _ -> None);
     final_check = (fun _ -> true);
     new_app = (fun _ -> ());
     new_elem = (fun _ -> ());
     init_search= (fun () -> ());
     push= (fun () -> ());
     pop= (fun () -> ());
     restart = (fun () -> ());
     reset= (fun () -> ());
     new_eq = (fun _ _ -> ());
     new_diseq = (fun _ _ -> ());
     new_assignment = (fun _ _ -> ());
     new_relevant = (fun _ -> ());
    }


external get_theory_callbacks : theory -> theory_callbacks = "get_theory_callbacks"
external mk_theory_register : context -> string -> theory_callbacks -> theory = "mk_theory_register"
external set_delete_callback_register : theory -> unit = "set_delete_callback_register"
external set_reduce_app_callback_register : theory -> unit = "set_reduce_app_callback_register"
external set_reduce_eq_callback_register : theory -> unit = "set_reduce_eq_callback_register"
external set_reduce_distinct_callback_register : theory -> unit = "set_reduce_distinct_callback_register"
external set_new_app_callback_register : theory -> unit = "set_new_app_callback_register"
external set_new_elem_callback_register : theory -> unit = "set_new_elem_callback_register"
external set_init_search_callback_register : theory -> unit = "set_init_search_callback_register"
external set_push_callback_register : theory -> unit = "set_push_callback_register"
external set_pop_callback_register : theory -> unit = "set_pop_callback_register"
external set_restart_callback_register : theory -> unit = "set_restart_callback_register"
external set_reset_callback_register : theory -> unit = "set_reset_callback_register"
external set_final_check_callback_register : theory -> unit = "set_final_check_callback_register"
external set_new_eq_callback_register : theory -> unit = "set_new_eq_callback_register"
external set_new_diseq_callback_register : theory -> unit = "set_new_diseq_callback_register"
external set_new_assignment_callback_register : theory -> unit = "set_new_assignment_callback_register"
external set_new_relevant_callback_register : theory -> unit = "set_new_relevant_callback_register"

let is_some opt = 
    match opt with
    | Some v -> true
    | None   -> false

let get_some opt = 
    match opt with
    | Some v -> v
    | None   -> failwith "None unexpected"

  


let apply_delete (th:theory_callbacks) = th.delete_theory ()
let set_delete_callback th cb = 
    let cbs = get_theory_callbacks th in
    cbs.delete_theory <- cb;
    set_delete_callback_register th

let mk_theory context name = 
    Callback.register "is_some" is_some;
    Callback.register "get_some" get_some;
    Callback.register "apply_delete" apply_delete;
    let cbs = mk_theory_callbacks() in
    mk_theory_register context name cbs


let apply_reduce_app (th:theory_callbacks) f args = th.reduce_app f args
let set_reduce_app_callback th cb = 
    Callback.register "apply_reduce_app" apply_reduce_app;
    let cbs = get_theory_callbacks th in
    cbs.reduce_app <- cb;
    set_reduce_app_callback_register th

let apply_reduce_eq (th:theory_callbacks) a b = th.reduce_eq a b
let set_reduce_eq_callback th cb = 
    Callback.register "apply_reduce_eq" apply_reduce_eq;
    let cbs = get_theory_callbacks th in
    cbs.reduce_eq <- cb;
    set_reduce_eq_callback_register th

let apply_reduce_distinct (th:theory_callbacks) args = th.reduce_distinct args
let set_reduce_distinct_callback th cb = 
    Callback.register "apply_reduce_distinct" apply_reduce_distinct;
    let cbs = get_theory_callbacks th in
    cbs.reduce_distinct <- cb;
    set_reduce_distinct_callback_register th
 

let apply_new_app (th:theory_callbacks) a = th.new_app a
let set_new_app_callback th cb = 
    Callback.register "apply_new_app" apply_new_app;
    let cbs = get_theory_callbacks th in
    cbs.new_app <- cb;
    set_new_app_callback_register th

let apply_new_elem (th:theory_callbacks) a = th.new_elem a
let set_new_elem_callback th cb = 
    Callback.register "apply_new_elem" apply_new_elem;
    let cbs = get_theory_callbacks th in
    cbs.new_elem <- cb;
    set_new_elem_callback_register th


let apply_init_search (th:theory_callbacks) = th.init_search()
let set_init_search_callback th cb = 
    Callback.register "apply_init_search" apply_init_search;
    let cbs = get_theory_callbacks th in
    cbs.init_search <- cb;
    set_init_search_callback_register th


let apply_push (th:theory_callbacks) = th.push()
let set_push_callback th cb = 
    Callback.register "apply_push" apply_push;
    let cbs = get_theory_callbacks th in
    cbs.push <- cb;
    set_push_callback_register th

let apply_pop (th:theory_callbacks) = th.pop()
let set_pop_callback th cb = 
    Callback.register "apply_pop" apply_pop;
    let cbs = get_theory_callbacks th in
    cbs.pop <- cb;
    set_pop_callback_register th
 

let apply_restart (th:theory_callbacks) = th.restart()
let set_restart_callback th cb = 
    Callback.register "apply_restart" apply_restart;
    let cbs = get_theory_callbacks th in
    cbs.restart <- cb;
    set_restart_callback_register th
 

let apply_reset (th:theory_callbacks) = th.reset()
let set_reset_callback th cb = 
    Callback.register "apply_reset" apply_reset;
    let cbs = get_theory_callbacks th in
    cbs.reset <- cb;
    set_reset_callback_register th

let apply_final_check (th:theory_callbacks) = th.final_check()
let set_final_check_callback th cb = 
    Callback.register "apply_final_check" apply_final_check;
    let cbs = get_theory_callbacks th in
    cbs.final_check <- cb;
    set_final_check_callback_register th

let apply_new_eq (th:theory_callbacks) a b = th.new_eq a b
let set_new_eq_callback th cb = 
    Callback.register "apply_new_eq" apply_new_eq;
    let cbs = get_theory_callbacks th in
    cbs.new_eq <- cb;
    set_new_eq_callback_register th


let apply_new_diseq (th:theory_callbacks) a b = th.new_diseq a b
let set_new_diseq_callback th cb = 
    Callback.register "apply_new_diseq" apply_new_diseq;
    let cbs = get_theory_callbacks th in
    cbs.new_diseq <- cb;
    set_new_diseq_callback_register th

let apply_new_assignment (th:theory_callbacks) a b = th.new_assignment a b
let set_new_assignment_callback th cb = 
    Callback.register "apply_new_assignment" apply_new_assignment;
    let cbs = get_theory_callbacks th in
    cbs.new_assignment <- cb;
    set_new_assignment_callback_register th

let apply_new_relevant (th:theory_callbacks) a = th.new_relevant a
let set_new_relevant_callback th cb = 
    Callback.register "apply_new_relevant" apply_new_relevant;
    let cbs = get_theory_callbacks th in
    cbs.new_relevant <- cb;
    set_new_relevant_callback_register th



end

