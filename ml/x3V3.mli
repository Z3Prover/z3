
quote (mli,"

(** {2 {L ML Extensions}} *)

(**
  \[ [ mk_context_x configs] \] is a shorthand for the context with configurations in [configs].
*)
val mk_context_x: (string * string) array -> context;;

(**
  \[ [ get_app_args c a ] \] is the array of arguments of an application. If [t] is a constant, then the array is empty.

  - {b See also}: {!Z3.get_app_num_args}
  - {b See also}: {!Z3.get_app_arg}
*)
val get_app_args:  context -> app -> ast array

(**
  \[ [ get_app_args c d ] \] is the array of parameters of [d].

  - {b See also}: {!Z3.get_domain_size}
  - {b See also}: {!Z3.get_domain}
*)
val get_domains: context -> func_decl -> sort array

(**
  \[ [ get_array_sort c t ] \] is the domain and the range of [t].

  - {b See also}: {!Z3.get_array_sort_domain}
  - {b See also}: {!Z3.get_array_sort_range}
*)
val get_array_sort: context -> sort -> sort * sort

(**
  \[ [ get_tuple_sort c ty ] \] is the pair [(mk_decl, fields)] where [mk_decl] is the constructor declaration of [ty], and [fields] is the array of fields in [ty].

  - {b See also}: {!Z3.get_tuple_sort_mk_decl}
  - {b See also}: {!Z3.get_tuple_sort_num_fields}
  - {b See also}: {!Z3.get_tuple_sort_field_decl}
*)
val get_tuple_sort: context -> sort -> (func_decl * func_decl array)

(**
  \[ [ datatype_constructor_refined ] \] is the refinement of a datatype constructor.
  
  It contains the constructor declaration, recognizer, and list of accessor functions.
*)
type datatype_constructor_refined = { 
   constructor : func_decl; 
   recognizer : func_decl; 
   accessors : func_decl array 
}

(**
  \[ [ get_datatype_sort c ty ] \] is the array of triples [(constructor, recognizer, fields)] where [constructor] is the constructor declaration of [ty], [recognizer] is the recognizer for the [constructor], and [fields] is the array of fields in [ty].

  - {b See also}: {!Z3.get_datatype_sort_num_constructors}
  - {b See also}: {!Z3.get_datatype_sort_constructor}
  - {b See also}: {!Z3.get_datatype_sort_recognizer}
  - {b See also}: {!Z3.get_datatype_sort_constructor_accessor}
*)


val get_datatype_sort: context -> sort -> datatype_constructor_refined array

(**
  \[ [ get_model_constants c m ] \] is the array of constants in the model [m].

  - {b See also}: {!Z3.get_model_num_constants}
  - {b See also}: {!Z3.get_model_constant}
*)
val get_model_constants: context -> model -> func_decl array


(**
  \[ [ get_model_func_entry c m i j ] \] is the [j]'th entry in the [i]'th function in the model [m].

  - {b See also}: {!Z3.get_model_func_entry_num_args}
  - {b See also}: {!Z3.get_model_func_entry_arg}
  - {b See also}: {!Z3.get_model_func_entry_value}
*)
val get_model_func_entry: context -> model -> int -> int -> (ast array * ast);;

(**
  \[ [ get_model_func_entries c m i ] \] is the array of entries in the [i]'th function in the model [m].

  - {b See also}: {!Z3.get_model_func_num_entries}
  - {b See also}: {!Z3.get_model_func_entry}
*)
val get_model_func_entries: context -> model -> int -> (ast array * ast) array;;

(**
  \[ [ get_model_funcs c m ] \] is the array of functions in the model [m]. Each function is represented by the triple [(decl, entries, else)], where [decl] is the declaration name for the function, [entries] is the array of entries in the function, and [else] is the default (else) value for the function.

  - {b See also}: {!Z3.get_model_num_funcs}
  - {b See also}: {!Z3.get_model_func_decl}
  - {b See also}: {!Z3.get_model_func_entries}
  - {b See also}: {!Z3.get_model_func_else}
*)
val get_model_funcs: context -> model -> 
  (symbol *
   (ast array * ast) array * 
   ast) array

(**
  \[ [ get_smtlib_formulas c ] \] is the array of formulas created by a preceding call to {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.

  Recommend use {!Z3.parse_smtlib_string_x} or {!Z3.parse_smtlib_file_x} for functional style interface to the SMT-LIB parser.

  - {b See also}: {!Z3.parse_smtlib_string_x}
  - {b See also}: {!Z3.parse_smtlib_file_x}
  - {b See also}: {!Z3.parse_smtlib_string}
  - {b See also}: {!Z3.parse_smtlib_file}
  - {b See also}: {!Z3.get_smtlib_num_formulas}
  - {b See also}: {!Z3.get_smtlib_formula}
*)
val get_smtlib_formulas: context -> ast array

(**
  \[ [get_smtlib_assumptions c] \] is the array of assumptions created by a preceding call to {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.

  Recommend use {!Z3.parse_smtlib_string_x} or {!Z3.parse_smtlib_file_x} for functional style interface to the SMT-LIB parser.


  - {b See also}: {!Z3.parse_smtlib_string_x}
  - {b See also}: {!Z3.parse_smtlib_file_x}
  - {b See also}: {!Z3.parse_smtlib_string}
  - {b See also}: {!Z3.parse_smtlib_file}
  - {b See also}: {!Z3.get_smtlib_num_assumptions}
  - {b See also}: {!Z3.get_smtlib_assumption}
*)
val get_smtlib_assumptions: context -> ast array

(**
  \[ [ get_smtlib_decls c ] \] is the array of declarations created by a preceding call to {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.

  Recommend use {!Z3.parse_smtlib_string_x} or {!Z3.parse_smtlib_file_x} for functional style interface to the SMT-LIB parser.


  - {b See also}: {!Z3.parse_smtlib_string_x}
  - {b See also}: {!Z3.parse_smtlib_file_x}
  - {b See also}: {!Z3.parse_smtlib_string}
  - {b See also}: {!Z3.parse_smtlib_file}
  - {b See also}: {!Z3.get_smtlib_num_decls}
  - {b See also}: {!Z3.get_smtlib_decl}
*)
val get_smtlib_decls: context -> func_decl array

(**
  \[ [ get_smtlib_parse_results c ] \] is the triple [(get_smtlib_formulas c, get_smtlib_assumptions c, get_smtlib_decls c)].

  Recommend use {!Z3.parse_smtlib_string_x} or {!Z3.parse_smtlib_file_x} for functional style interface to the SMT-LIB parser.


  - {b See also}: {!Z3.parse_smtlib_string_x}
  - {b See also}: {!Z3.parse_smtlib_file_x}
  - {b See also}: {!Z3.parse_smtlib_string}
  - {b See also}: {!Z3.parse_smtlib_file}
  - {b See also}: {!Z3.get_smtlib_formulas}
  - {b See also}: {!Z3.get_smtlib_assumptions}
  - {b See also}: {!Z3.get_smtlib_decls}
*)
val get_smtlib_parse_results: context -> (ast array * ast array * func_decl array)

(**
  \[ [ parse_smtlib_string_formula c ... ] \] calls [(parse_smtlib_string c ...)] and returns the single formula produced. 

  Recommended for functional style interface to the SMT-LIB parser.

  - {b See also}: {!Z3.parse_smtlib_file_formula}
  - {b See also}: {!Z3.parse_smtlib_string_x}
*)
val parse_smtlib_string_formula: context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> ast

(**
  \[ [ parse_smtlib_file_formula c ... ] \] calls [(parse_smtlib_file c ...)] and returns the single formula produced. 

  Recommended for functional style interface to the SMT-LIB parser.

  - {b See also}: {!Z3.parse_smtlib_file_formula}
  - {b See also}: {!Z3.parse_smtlib_file_x}
*)
val parse_smtlib_file_formula: context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> ast

(**
  \[ [ parse_smtlib_string_x c ... ] \] is [(parse_smtlib_string c ...; get_smtlib_parse_results c)]

  Recommended for functional style interface to the SMT-LIB parser.

  - {b See also}: {!Z3.parse_smtlib_file_x}
  - {b See also}: {!Z3.parse_smtlib_string}
  - {b See also}: {!Z3.get_smtlib_parse_results}
*)
val parse_smtlib_string_x: context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> (ast array * ast array * func_decl array)

(**
  \[ [ parse_smtlib_file_x c ... ] \] is [(parse_smtlib_file c ...; get_smtlib_parse_results c)]

  Recommended for functional style interface to the SMT-LIB parser.

  - {b See also}: {!Z3.parse_smtlib_string_x}
  - {b See also}: {!Z3.parse_smtlib_file}
  - {b See also}: {!Z3.get_smtlib_parse_results}
*)
val parse_smtlib_file_x: context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> (ast array * ast array * func_decl array)

(**
  \[ [ symbol_refined ] \] is the refinement of a {!Z3.symbol} .

  - {b See also}: {!Z3.symbol_refine}
  - {b See also}: {!Z3.get_symbol_kind}
*)
type symbol_refined =
  | Symbol_int of int
  | Symbol_string of string
  | Symbol_unknown;;

(**
  \[ [ symbol_refine c s ] \] is the refined symbol of [s].

  - {b See also}:  {!Z3.symbol_refined}
  - {b See also}: {!Z3.get_symbol_kind}
*)
val symbol_refine: context -> symbol -> symbol_refined;;

(**
  \[ [ sort_refined ] \] is the refinement of a {!Z3.sort} .

  - {b See also}: {!Z3.sort_refine}
  - {b See also}: {!Z3.get_sort_kind}
*)


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
  | Sort_unknown of symbol

(**
  \[ [ sort_refine c t ] \] is the refined sort of [t].

  - {b See also}:  {!Z3.sort_refined}
  - {b See also}: {!Z3.get_sort_kind}
*)
val sort_refine: context -> sort -> sort_refined;;

(**
  \[ [ binder_type ] \] is a universal or existential quantifier.

  - {b See also}: {!Z3.term_refined}
*)
type binder_type = | Forall | Exists 

(**
  \[ [ numeral_refined ] \] is the refinement of a numeral .

  Numerals whose fractional representation can be fit with
  64 bit integers are treated as small.

*)
type numeral_refined = 
  | Numeral_small  of int64 * int64
  | Numeral_large  of string

(**
  \[ [ term_refined ] \] is the refinement of a {!Z3.ast} .

  - {b See also}: {!Z3.term_refine}
*)
type term_refined = 
  | Term_app        of decl_kind * func_decl * ast array
  | Term_quantifier of binder_type * int * ast array array * (symbol * sort) array * ast
  | Term_numeral    of numeral_refined * sort
  | Term_var        of int * sort

(**
  \[ [ term_refine c a ] \] is the refined term of [a].

  - {b See also}:  {!Z3.term_refined}
*)
val term_refine : context -> ast -> term_refined

(** 
  \[ [mk_theory c name ] \] create a custom theory.

*)
val mk_theory : context -> string -> theory

(**
  \[ [set_delete_callback th cb] \] set callback when theory gets deleted.
*)
val set_delete_callback : theory -> (unit -> unit) -> unit

(**
  \[ [set_reduce_app_callback th cb] \] set callback for simplifying theory terms.
*)
val set_reduce_app_callback : theory -> (func_decl -> ast array -> ast option) -> unit

(**
  \[ [set_reduce_eq_callback th cb] \] set callback for simplifying equalities over theory terms.
*)
val set_reduce_eq_callback : theory -> (ast -> ast -> ast option) -> unit

(**
  \[ [set_reduce_distinct_callback th cb] \] set callback for simplifying disequalities over theory terms.
*)
val set_reduce_distinct_callback : theory -> (ast array -> ast option) -> unit

(**
  \[ [set_new_app_callback th cb] \] set callback for registering new application.
*)
val set_new_app_callback : theory -> (ast -> unit) -> unit

(**
  \[ [set_new_elem_callback th cb] \] set callback for registering new element.

  - {b See also}: the help for the corresponding C API function.  
*)
val set_new_elem_callback : theory -> (ast -> unit) -> unit

(**
  \[ [set_init_search_callback th cb] \] set callback when Z3 starts searching for a satisfying assignment.
*)
val set_init_search_callback : theory -> (unit -> unit) -> unit

(**
  \[ [set_push_callback th cb] \] set callback for a logical context push.
*)
val set_push_callback : theory -> (unit -> unit) -> unit

(**
  \[ [set_pop_callback th cb] \] set callback for a logical context pop.
*)
val set_pop_callback : theory -> (unit -> unit) -> unit

(**
  \[ [set_restart_callback th cb] \] set callback for search restart.
*)
val set_restart_callback : theory -> (unit -> unit) -> unit

val set_reset_callback : theory -> (unit -> unit) -> unit

val set_final_check_callback : theory -> (unit -> bool) -> unit

val set_new_eq_callback : theory -> (ast -> ast -> unit) -> unit

val set_new_diseq_callback : theory -> (ast -> ast -> unit) -> unit

val set_new_assignment_callback : theory -> (ast -> bool -> unit) -> unit

val set_new_relevant_callback : theory -> (ast -> unit) -> unit

");
