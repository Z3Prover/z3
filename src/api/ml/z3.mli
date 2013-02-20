(**
   The Z3 ML/Ocaml Interface.

   Copyright (C) 2012 Microsoft Corporation
   @author CM Wintersteiger (cwinter) 2012-12-17
*)



(** Context objects.

    Most interactions with Z3 are interpreted in some context; many users will only 
    require one such object, but power users may require more than one. To start using 
    Z3, do 

    <code>
    let ctx = (mk_context []) in 
    (...)
    </code>

    where a list of pairs of strings may be passed to set options on
    the context, e.g., like so:

    <code>
    let cfg = [("model", "true"); ("...", "...")] in
    let ctx = (mk_context cfg) in 
    (...)
    </code>
*)
type context

(** Create a context object *)
val mk_context : (string * string) list -> context


(** Interaction logging for Z3
    Note that this is a global, static log and if multiple Context 
    objects are created, it logs the interaction with all of them. *)
module Log :
sig
  (** Open an interaction log file. 
      @param filename the name of the file to open.
      @return True if opening the log file succeeds, false otherwise.
  *)
  (* CMW: "open" seems to be a reserved keyword? *)
  val open_ : string -> bool

  (** Closes the interaction log. *)
  val close : unit

  (** Appends a user-provided string to the interaction log.
      @param s the string to append*)
  val append : string -> unit
end

(** Version information *)
module Version :
sig
  (** The major version. *)
  val major : int

  (** The minor version. *)
  val minor : int

  (** The build version. *)
  val build : int

  (** The revision. *)
  val revision : int

  (** A string representation of the version information. *)
  val to_string : string
end

(** Symbols are used to name several term and type constructors *)
module Symbol :
sig
  (** Numbered Symbols  *)
  type int_symbol
    
  (** Named Symbols  *)
  type string_symbol
    
  (** Symbols *)
  type symbol = S_Int of int_symbol | S_Str of string_symbol

  (** The kind of the symbol (int or string) *)
  val kind : symbol -> Z3enums.symbol_kind

  (** Indicates whether the symbol is of Int kind *)
  val is_int_symbol : symbol -> bool

  (** Indicates whether the symbol is of string kind. *)
  val is_string_symbol : symbol -> bool

  (** The int value of the symbol. *)
  val get_int : int_symbol -> int

  (** The string value of the symbol. *)
  val get_string : string_symbol -> string

  (** A string representation of the symbol. *)
  val to_string : symbol -> string

  (**
     Creates a new symbol using an integer.
     
     Not all integers can be passed to this function.
     The legal range of unsigned integers is 0 to 2^30-1.
  *)
  val mk_int : context -> int -> symbol

  (** Creates a new symbol using a string. *)
  val mk_string : context -> string -> symbol

  (** Create an array of symbols. *)
  val mk_ints : context -> int array -> symbol array

  (** Create an array of symbols. *)
  val mk_strings : context -> string array -> symbol array
end

(** The abstract syntax tree (AST) module *)
module AST :
sig
  type ast 

  (** Vectors of ASTs *)
  module ASTVector :
  sig
    type ast_vector 
      
    (** The size of the vector *)
    val get_size : ast_vector -> int

    (** 
	Retrieves the i-th object in the vector.
	@param i Index
	@return An AST
    *)
    val get : ast_vector -> int -> ast

    (** Sets the i-th object in the vector. *)
    val set : ast_vector -> int -> ast -> unit

    (** Resize the vector to <paramref name="newSize"/>. 
	@param newSize The new size of the vector. *)
    val resize : ast_vector -> int -> unit

    (**
       Add the AST <paramref name="a"/> to the back of the vector. The size
       is increased by 1.
       @param a An AST
    *)
    val push : ast_vector -> ast -> unit

    (**
       Translates all ASTs in the vector to <paramref name="to_ctx"/>.
       @param to_ctx A context
       @return A new ASTVector
    *)
    val translate : ast_vector -> context -> ast_vector

    (** Retrieves a string representation of the vector. *)
    val to_string : ast_vector -> string
  end

  (** Map from AST to AST *)
  module ASTMap :
  sig
    type ast_map       
      
    (** Checks whether the map contains the key <paramref name="k"/>.
	@param k An AST
	@return True if <paramref name="k"/> is a key in the map, false otherwise. *)
    val contains : ast_map -> ast -> bool

    (** Finds the value associated with the key <paramref name="k"/>.
	<remarks>
	This function signs an error when <paramref name="k"/> is not a key in the map.
	@param k An AST 
    *)
    val find : ast_map -> ast -> ast

    (**
       Stores or replaces a new key/value pair in the map.
       @param k The key AST
       @param v The value AST
    *)
    val insert : ast_map -> ast -> ast -> unit

    (**
       Erases the key <paramref name="k"/> from the map.
       @param k An AST
    *)
    val erase : ast_map -> ast -> unit

    (**  Removes all keys from the map. *)
    val reset : ast_map -> unit

    (** The size of the map *)
    val get_size : ast_map -> int

    (** The keys stored in the map. *)
    val get_keys : ast_map -> ASTVector.ast_vector

    (** Retrieves a string representation of the map.*)
    val to_string : ast_map -> string
  end

  (**
     The AST's hash code.
     @return A hash code
  *)
  val get_hash_code : ast -> int

  (** A unique identifier for the AST (unique among all ASTs). *)
  val get_id : ast -> int

  (** The kind of the AST.  *)    
  val get_ast_kind : ast -> Z3enums.ast_kind

  (** Indicates whether the AST is an Expr *)
  val is_expr : ast -> bool

  (** Indicates whether the AST is a bound variable*)
  val is_var : ast -> bool

  (** Indicates whether the AST is a Quantifier  *)
  val is_quantifier : ast -> bool

  (** Indicates whether the AST is a Sort *)
  val is_sort : ast -> bool

  (** Indicates whether the AST is a func_decl  *)
  val is_func_decl : ast -> bool

  (** A string representation of the AST. *)
  val to_string : ast -> string

  (** A string representation of the AST in s-expression notation. *)
  val to_sexpr : ast -> string

  (**
     Comparison operator.
     @param a An AST
     @param b An AST
     @return True if <paramref name="a"/> and <paramref name="b"/> are from the same context 
     and represent the same sort; false otherwise.
  *)
  val ( = ) : ast -> ast -> bool

  (**
     Object Comparison.
     @param other Another ast
     @return Negative if the object should be sorted before <paramref name="other"/>, positive if after else zero.
  *)
  val compare : ast -> ast -> int

  (** Operator < *)
  val ( < ) : ast -> ast -> int

  (**
     Translates (copies) the AST to the Context <paramref name="ctx"/>.
     @param ctx A context
     @return A copy of the AST which is associated with <paramref name="ctx"/>
  *)
  val translate : ast -> context -> ast

  (**
     Wraps an AST.

     <remarks>This function is used for transitions between native and 
     managed objects. Note that <paramref name="nativeObject"/> must be a 
     native object obtained from Z3 (e.g., through <seealso cref="UnwrapAST"/>)
     and that it must have a correct reference count (see e.g., 
     <seealso cref="Z3native.inc_ref"/>.
     <seealso cref="UnwrapAST"/>
     @param nativeObject The native pointer to wrap.
  *)
  val wrap : context -> Z3native.z3_ast -> ast

  (**
     Unwraps an AST.
     <remarks>This function is used for transitions between native and 
     managed objects. It returns the native pointer to the AST. Note that 
     AST objects are reference counted and unwrapping an AST disables automatic
     reference counting, i.e., all references to the IntPtr that is returned 
     must be handled externally and through native calls (see e.g., 
     <seealso cref="Z3native.inc_ref"/>).
     <seealso cref="WrapAST"/>
     @param a The AST to unwrap.
  *)
  val unwrap_ast : ast -> Z3native.ptr
end

(** The Sort module implements type information for ASTs *)
module Sort :
sig
  (** Sorts *)
  type sort = Sort of AST.ast

  (** Uninterpreted Sorts *)
  type uninterpreted_sort = UninterpretedSort of sort

  val ast_of_sort : sort -> AST.ast
  val sort_of_uninterpreted_sort : uninterpreted_sort -> sort
  val uninterpreted_sort_of_sort : sort -> uninterpreted_sort

  (**
     Comparison operator.
     @param a A sort
     @param b A sort
     @return True if <paramref name="a"/> and <paramref name="b"/> are from the same context 
     and represent the same sort; false otherwise.
  *)
  val ( = ) : sort -> sort -> bool

  (** Returns a unique identifier for the sort. *)
  val get_id : sort -> int

  (** The kind of the sort. *)
  val get_sort_kind : sort -> Z3enums.sort_kind

  (** The name of the sort *)
  val get_name : sort -> Symbol.symbol

  (** A string representation of the sort. *)
  val to_string : sort -> string

  (** Create a new uninterpreted sort. *)
  val mk_uninterpreted : context -> Symbol.symbol -> uninterpreted_sort

  (** Create a new uninterpreted sort. *)
  val mk_uninterpreted_s : context -> string -> uninterpreted_sort
end

(** Function declarations *)
module rec FuncDecl :
sig
  type func_decl = FuncDecl of AST.ast

  val ast_of_func_decl : FuncDecl.func_decl -> AST.ast

  (** Parameters of Func_Decls *)
  module Parameter :
  sig
    (** Parameters of func_decls *)
    type parameter =
	P_Int of int
      | P_Dbl of float
      | P_Sym of Symbol.symbol
      | P_Srt of Sort.sort
      | P_Ast of AST.ast
      | P_Fdl of func_decl
      | P_Rat of string
	  
    (** The kind of the parameter. *)
    val get_kind : parameter -> Z3enums.parameter_kind

    (** The int value of the parameter.*)
    val get_int : parameter -> int

    (** The double value of the parameter.*)
    val get_float : parameter -> float

    (** The Symbol.Symbol value of the parameter.*)
    val get_symbol : parameter -> Symbol.symbol

    (** The Sort value of the parameter.*)
    val get_sort : parameter -> Sort.sort

    (** The AST value of the parameter.*)
    val get_ast : parameter -> AST.ast

    (** The FunctionDeclaration value of the parameter.*)
    val get_func_decl : parameter -> func_decl

    (** The rational string value of the parameter.*)
    val get_rational : parameter -> string
  end

  (** Creates a new function declaration. *)
  val mk_func_decl : context -> Symbol.symbol -> Sort.sort array -> Sort.sort -> func_decl

  (** Creates a new function declaration. *)
  val mk_func_decl_s : context -> string -> Sort.sort array -> Sort.sort -> func_decl
  (** Creates a fresh function declaration with a name prefixed with <paramref name="prefix"/>.
      <seealso cref="MkFunc_Decl(string,Sort,Sort)"/>
      <seealso cref="MkFunc_Decl(string,Sort[],Sort)"/> *)

  val mk_fresh_func_decl : context -> string -> Sort.sort array -> Sort.sort -> func_decl

  (** Creates a new constant function declaration. *)
  val mk_const_decl : context -> Symbol.symbol -> Sort.sort -> func_decl

  (** Creates a new constant function declaration. *)
  val mk_const_decl_s : context -> string -> Sort.sort -> func_decl

  (** Creates a fresh constant function declaration with a name prefixed with <paramref name="prefix"/>.
      <seealso cref="MkFunc_Decl(string,Sort,Sort)"/>
      <seealso cref="MkFunc_Decl(string,Sort[],Sort)"/> *)
  val mk_fresh_const_decl : context -> string -> Sort.sort -> func_decl

  (** Comparison operator.
      @param a A func_decl
      @param b A func_decl
      @return True if <paramref name="a"/> and <paramref name="b"/> are from the same context 
      and represent the same func_decl; false otherwise. *)
  val ( = ) : func_decl -> func_decl -> bool

  (** A string representations of the function declaration. *)
  val to_string : func_decl -> string

  (** Returns a unique identifier for the function declaration. *)
  val get_id : func_decl -> int

  (** The arity of the function declaration *)
  val get_arity : func_decl -> int

  (** The size of the domain of the function declaration
      <seealso cref="Arity"/> *)
  val get_domain_size : func_decl -> int
    
  (** The domain of the function declaration *)
  val get_domain : func_decl -> Sort.sort array
    
  (** The range of the function declaration *)
  val get_range : func_decl -> Sort.sort

  (** The kind of the function declaration. *)
  val get_decl_kind : func_decl -> Z3enums.decl_kind

  (** The name of the function declaration*)
  val get_name : func_decl -> Symbol.symbol

  (** The number of parameters of the function declaration *)
  val get_num_parameters : func_decl -> int

  (** The parameters of the function declaration *)
  val get_parameters : func_decl -> Parameter.parameter list

  (** Create expression that applies function to arguments.
      @param args The arguments *)	   
  val apply : func_decl -> Expr.expr array -> Expr.expr
end

(** Parameter sets (of Solvers, Tactics, ...)

    A Params objects represents a configuration in the form of Symbol.symbol/value pairs. *)
and Params :
sig
  type params

  (** ParamDescrs describe sets of parameters (of Solvers, Tactics, ...) *)
  module ParamDescrs :
  sig
    type param_descrs 

    (** Validate a set of parameters. *)
    val validate : param_descrs -> params -> unit

    (** Retrieve kind of parameter. *)
    val get_kind : param_descrs -> Symbol.symbol -> Z3enums.param_kind

    (** Retrieve all names of parameters. *)
    val get_names : param_descrs -> Symbol.symbol array

    (** The size of the ParamDescrs. *)
    val get_size : param_descrs -> int

    (** Retrieves a string representation of the ParamDescrs. *)
    val to_string : param_descrs -> string
  end

  (** Adds a parameter setting. *)
  val add_bool : params -> Symbol.symbol -> bool -> unit

  (** Adds a parameter setting. *)
  val add_int : params -> Symbol.symbol -> int -> unit

  (** Adds a parameter setting. *)
  val add_double : params -> Symbol.symbol -> float -> unit

  (** Adds a parameter setting. *)
  val add_symbol : params -> Symbol.symbol -> Symbol.symbol -> unit

  (** Adds a parameter setting. *)
  val add_s_bool : params -> string -> bool -> unit

  (** Adds a parameter setting. *)
  val add_s_int : params -> string -> int -> unit

  (** Adds a parameter setting. *)
  val add_s_double : params -> string -> float -> unit

  (** Adds a parameter setting. *)
  val add_s_symbol : params -> string -> Symbol.symbol -> unit

  (** Creates a new parameter set *)
  val mk_params : context -> params

  (** A string representation of the parameter set. *)
  val to_string : params -> string
end

and Expr :
sig
  (** General Expressions (Terms) *)
  type expr = Expr of AST.ast

  val ast_of_expr : Expr.expr -> AST.ast
  val expr_of_ast : AST.ast -> Expr.expr

  val simplify : Expr.expr -> Params.params option -> expr
  val get_simplify_help : context -> string
  val get_simplify_parameter_descrs : context -> Params.ParamDescrs.param_descrs
  val get_func_decl : Expr.expr -> FuncDecl.func_decl
  val get_bool_value : Expr.expr -> Z3enums.lbool
  val get_num_args : Expr.expr -> int
  val get_args : Expr.expr -> Expr.expr array
  val update : Expr.expr -> Expr.expr array -> expr
  val substitute : Expr.expr -> Expr.expr array -> Expr.expr array -> expr
  val substitute_one : Expr.expr -> Expr.expr -> Expr.expr -> expr
  val substitute_vars : Expr.expr -> Expr.expr array -> expr
  val translate : Expr.expr -> context -> expr
  val to_string : Expr.expr -> string
  val is_numeral : Expr.expr -> bool
  val is_well_sorted : Expr.expr -> bool
  val get_sort : Expr.expr -> Sort.sort
  val is_bool : Expr.expr -> bool
  val is_const : Expr.expr -> bool
  val is_true : Expr.expr -> bool
  val is_false : Expr.expr -> bool
  val is_eq : Expr.expr -> bool
  val is_distinct : Expr.expr -> bool
  val is_ite : Expr.expr -> bool
  val is_and : Expr.expr -> bool
  val is_or : Expr.expr -> bool
  val is_iff : Expr.expr -> bool
  val is_xor : Expr.expr -> bool
  val is_not : Expr.expr -> bool
  val is_implies : Expr.expr -> bool
  val is_label : Expr.expr -> bool
  val is_oeq : Expr.expr -> bool
  val mk_const : context -> Symbol.symbol -> Sort.sort -> expr
  val mk_const_s : context -> string -> Sort.sort -> expr
  val mk_const_f : context -> FuncDecl.func_decl -> expr
  val mk_fresh_const : context -> string -> Sort.sort -> expr
  val mk_app : context -> FuncDecl.func_decl -> Expr.expr array -> expr
  val mk_numeral_string : context -> string -> Sort.sort -> expr
  val mk_numeral_int : context -> int -> Sort.sort -> expr
end

module Boolean :
sig
  type bool_sort = BoolSort of Sort.sort
  type bool_expr = BoolExpr of Expr.expr

  val expr_of_bool_expr : bool_expr -> Expr.expr
  val sort_of_bool_sort : bool_sort -> Sort.sort
  val bool_sort_of_sort : Sort.sort -> bool_sort
  val bool_expr_of_expr : Expr.expr -> bool_expr

  val mk_sort : context -> bool_sort
  val mk_const : context -> Symbol.symbol -> bool_expr
  val mk_const_s : context -> string -> bool_expr
  val mk_true : context -> bool_expr
  val mk_false : context -> bool_expr
  val mk_val : context -> bool -> bool_expr
  val mk_eq : context -> Expr.expr -> Expr.expr -> bool_expr
  val mk_distinct : context -> Expr.expr array -> bool_expr
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
  type quantifier = Quantifier of Expr.expr

  val expr_of_quantifier : quantifier -> Expr.expr
  val quantifier_of_expr : Expr.expr -> quantifier


  module Pattern :
  sig
    type pattern = Pattern of AST.ast

    val ast_of_pattern : pattern -> AST.ast
    val pattern_of_ast : AST.ast -> pattern

    val get_num_terms : pattern -> int
    val get_terms : pattern -> Expr.expr array
    val to_string : pattern -> string
  end

  val get_index : Expr.expr -> int
  val is_universal : quantifier -> bool
  val is_existential : quantifier -> bool
  val get_weight : quantifier -> int
  val get_num_patterns : quantifier -> int
  val get_patterns : quantifier -> Pattern.pattern array
  val get_num_no_patterns : quantifier -> int
  val get_no_patterns : quantifier -> Pattern.pattern array
  val get_num_bound : quantifier -> int
  val get_bound_variable_names : quantifier -> Symbol.symbol array
  val get_bound_variable_sorts : quantifier -> Sort.sort array
  val get_body : quantifier -> Boolean.bool_expr
  val mk_bound : context -> int -> Sort.sort -> Expr.expr
  val mk_pattern : context -> Expr.expr array -> Pattern.pattern
  val mk_forall :
    context ->
    Sort.sort array ->
    Symbol.symbol array ->
    Expr.expr ->
    int option ->
    Pattern.pattern array ->
    Expr.expr array -> Symbol.symbol option -> Symbol.symbol option -> quantifier
  val mk_forall_const :
    context ->
    Expr.expr array ->
    Expr.expr ->
    int option ->
    Pattern.pattern array ->
    Expr.expr array -> Symbol.symbol option -> Symbol.symbol option -> quantifier
  val mk_exists :
    context ->
    Sort.sort array ->
    Symbol.symbol array ->
    Expr.expr ->
    int option ->
    Pattern.pattern array ->
    Expr.expr array -> Symbol.symbol option -> Symbol.symbol option -> quantifier
  val mk_exists_const :
    context ->
    Expr.expr array ->
    Expr.expr ->
    int option ->
    Pattern.pattern array ->
    Expr.expr array -> Symbol.symbol option -> Symbol.symbol option -> quantifier
  val mk_quantifier :
    context ->
    bool ->
    Expr.expr array ->
    Expr.expr ->
    int option ->
    Pattern.pattern array ->
    Expr.expr array -> Symbol.symbol option -> Symbol.symbol option -> quantifier
end

module Array_ :
sig
  type array_sort = ArraySort of Sort.sort
  type array_expr = ArrayExpr of Expr.expr

  val sort_of_array_sort : array_sort -> Sort.sort
  val array_sort_of_sort : Sort.sort -> array_sort
  val expr_of_array_expr : array_expr -> Expr.expr

  val array_expr_of_expr : Expr.expr -> array_expr

  val mk_sort : context -> Sort.sort -> Sort.sort -> array_sort
  val is_store : Expr.expr -> bool
  val is_select : Expr.expr -> bool
  val is_constant_array : Expr.expr -> bool
  val is_default_array : Expr.expr -> bool
  val is_array_map : Expr.expr -> bool
  val is_as_array : Expr.expr -> bool
  val is_array : Expr.expr -> bool
  val get_domain : array_sort -> Sort.sort
  val get_range : array_sort -> Sort.sort
  val mk_const : context -> Symbol.symbol -> Sort.sort -> Sort.sort -> array_expr
  val mk_const_s : context -> string -> Sort.sort -> Sort.sort -> array_expr
  val mk_select : context -> array_expr -> Expr.expr -> Expr.expr -> array_expr
  val mk_const_array : context -> Sort.sort -> Expr.expr -> array_expr
  val mk_map : context -> FuncDecl.func_decl -> array_expr array -> array_expr
  val mk_term_array : context -> array_expr -> array_expr
end

module Set :
sig
  type set_sort = SetSort of Sort.sort

  val sort_of_set_sort : set_sort -> Sort.sort

  val is_union : Expr.expr -> bool
  val is_intersect : Expr.expr -> bool
  val is_difference : Expr.expr -> bool
  val is_complement : Expr.expr -> bool
  val is_subset : Expr.expr -> bool
  val mk_sort : context -> Sort.sort -> set_sort
  val mk_empty : context -> Sort.sort -> Expr.expr
  val mk_full : context -> Sort.sort -> Expr.expr
  val mk_set_add : context -> Expr.expr -> Expr.expr -> Expr.expr
  val mk_del : context -> Expr.expr -> Expr.expr -> Expr.expr
  val mk_union : context -> Expr.expr array -> Expr.expr
  val mk_intersection : context -> Expr.expr array -> Expr.expr
  val mk_difference : context -> Expr.expr -> Expr.expr -> Expr.expr
  val mk_complement : context -> Expr.expr -> Expr.expr
  val mk_membership : context -> Expr.expr -> Expr.expr -> Expr.expr
  val mk_subset : context -> Expr.expr -> Expr.expr -> Expr.expr
end

module FiniteDomain :
sig
  type finite_domain_sort = FiniteDomainSort of Sort.sort

  val sort_of_finite_domain_sort : finite_domain_sort -> Sort.sort
  val finite_domain_sort_of_sort : Sort.sort -> finite_domain_sort

  val mk_sort : context -> Symbol.symbol -> int -> finite_domain_sort
  val mk_sort_s : context -> string -> int -> finite_domain_sort
  val is_finite_domain : Expr.expr -> bool
  val is_lt : Expr.expr -> bool
  val get_size : finite_domain_sort -> int
end

module Relation :
sig
  type relation_sort = RelationSort of Sort.sort

  val sort_of_relation_sort : relation_sort -> Sort.sort
  val relation_sort_of_sort : Sort.sort -> relation_sort

  val is_relation : Expr.expr -> bool
  val is_store : Expr.expr -> bool
  val is_empty : Expr.expr -> bool
  val is_is_empty : Expr.expr -> bool
  val is_join : Expr.expr -> bool
  val is_union : Expr.expr -> bool
  val is_widen : Expr.expr -> bool
  val is_project : Expr.expr -> bool
  val is_filter : Expr.expr -> bool
  val is_negation_filter : Expr.expr -> bool
  val is_rename : Expr.expr -> bool
  val is_complement : Expr.expr -> bool
  val is_select : Expr.expr -> bool
  val is_clone : Expr.expr -> bool
  val get_arity : relation_sort -> int
  val get_column_sorts : relation_sort -> relation_sort array
end

module Datatype :
sig
  type datatype_sort = DatatypeSort of Sort.sort
  type datatype_expr = DatatypeExpr of Expr.expr

  val sort_of_datatype_sort : datatype_sort -> Sort.sort
  val datatype_sort_of_sort : Sort.sort -> datatype_sort
  val expr_of_datatype_expr : datatype_expr -> Expr.expr
  val datatype_expr_of_expr : Expr.expr -> datatype_expr

  module Constructor :
  sig
    (** Constructors *)
    type constructor

    val get_n : constructor -> int
    val constructor_decl : constructor -> FuncDecl.func_decl
    val tester_decl : constructor -> FuncDecl.func_decl
    val accessor_decls : constructor -> FuncDecl.func_decl array
    val get_num_fields : constructor -> int
    val get_constructor_decl : constructor -> FuncDecl.func_decl
    val get_tester_decl : constructor -> FuncDecl.func_decl
    val get_accessor_decls : constructor -> FuncDecl.func_decl array
  end

  val mk_constructor : context -> Symbol.symbol -> Symbol.symbol -> Symbol.symbol array -> Sort.sort array -> int array -> Constructor.constructor
  val mk_constructor_s : context -> string -> Symbol.symbol -> Symbol.symbol array -> Sort.sort array -> int array -> Constructor.constructor
  val mk_sort : context -> Symbol.symbol -> Constructor.constructor array -> datatype_sort
  val mk_sort_s : context -> string -> Constructor.constructor array -> datatype_sort
  val mk_sorts : context -> Symbol.symbol array -> Constructor.constructor array array -> datatype_sort array
  val mk_sorts_s : context -> string array -> Constructor.constructor array array -> datatype_sort array
  val get_num_constructors : datatype_sort -> int
  val get_constructors : datatype_sort -> FuncDecl.func_decl array
  val get_recognizers : datatype_sort -> FuncDecl.func_decl array
  val get_accessors : datatype_sort -> FuncDecl.func_decl array array
end

module Enumeration :
sig
  type enum_sort = EnumSort of Sort.sort

  val sort_of_enum_sort : enum_sort -> Sort.sort

  val mk_sort : context -> Symbol.symbol -> Symbol.symbol array -> enum_sort
  val mk_sort_s : context -> string -> string array -> enum_sort
  val get_const_decls : enum_sort -> FuncDecl.func_decl array
  val get_tester_decls : enum_sort -> FuncDecl.func_decl array
end

module List_ :
sig
  type list_sort = ListSort of Sort.sort

  val sort_of_list_sort : list_sort -> Sort.sort

  val mk_sort : context -> Symbol.symbol -> Sort.sort -> list_sort
  val mk_list_s : context -> string -> Sort.sort -> list_sort
  val get_nil_decl : list_sort -> FuncDecl.func_decl
  val get_is_nil_decl : list_sort -> FuncDecl.func_decl
  val get_cons_decl : list_sort -> FuncDecl.func_decl
  val get_is_cons_decl : list_sort -> FuncDecl.func_decl
  val get_head_decl : list_sort -> FuncDecl.func_decl
  val get_tail_decl : list_sort -> FuncDecl.func_decl
  val nil : list_sort -> Expr.expr
end

module Tuple :
sig
  type tuple_sort = TupleSort of Sort.sort

  val sort_of_tuple_sort : tuple_sort -> Sort.sort

  val mk_sort : context -> Symbol.symbol -> Symbol.symbol array -> Sort.sort array -> tuple_sort
  val get_mk_decl : tuple_sort -> FuncDecl.func_decl
  val get_num_fields : tuple_sort -> int
  val get_field_decls : tuple_sort -> FuncDecl.func_decl array
end

module rec Arithmetic :
sig
  type arith_sort = ArithSort of Sort.sort
  type arith_expr = ArithExpr of Expr.expr

  val sort_of_arith_sort : Arithmetic.arith_sort -> Sort.sort
  val arith_sort_of_sort : Sort.sort -> Arithmetic.arith_sort
  val expr_of_arith_expr : Arithmetic.arith_expr -> Expr.expr
  val arith_expr_of_expr : Expr.expr -> Arithmetic.arith_expr

  module rec Integer :
  sig
    type int_sort = IntSort of arith_sort
    type int_expr = IntExpr of arith_expr
    type int_num = IntNum of int_expr

    val arith_sort_of_int_sort : Arithmetic.Integer.int_sort -> Arithmetic.arith_sort
    val int_sort_of_arith_sort : Arithmetic.arith_sort -> Arithmetic.Integer.int_sort
    val arith_expr_of_int_expr : Arithmetic.Integer.int_expr -> Arithmetic.arith_expr
    val int_expr_of_int_num : Arithmetic.Integer.int_num -> Arithmetic.Integer.int_expr
    val int_expr_of_arith_expr : Arithmetic.arith_expr -> Arithmetic.Integer.int_expr
    val int_num_of_int_expr : Arithmetic.Integer.int_expr -> Arithmetic.Integer.int_num
      
    val mk_sort : context -> int_sort
    val get_int : int_num -> int
    val to_string : int_num -> string
    val mk_int_const : context -> Symbol.symbol -> int_expr
    val mk_int_const_s : context -> string -> int_expr
    val mk_mod : context -> int_expr -> int_expr -> int_expr
    val mk_rem : context -> int_expr -> int_expr -> int_expr
    val mk_int_numeral_s : context -> string -> int_num
    val mk_int_numeral_i : context -> int -> int_num
    val mk_int2real : context -> int_expr -> Real.real_expr
    val mk_int2bv : context -> int -> int_expr -> BitVector.bitvec_expr
  end

  and Real :
  sig
    type real_sort = RealSort of arith_sort
    type real_expr = RealExpr of arith_expr
    type rat_num = RatNum of real_expr

    val arith_sort_of_real_sort : Arithmetic.Real.real_sort -> Arithmetic.arith_sort
    val real_sort_of_arith_sort : Arithmetic.arith_sort -> Arithmetic.Real.real_sort
    val arith_expr_of_real_expr : Arithmetic.Real.real_expr -> Arithmetic.arith_expr
    val real_expr_of_rat_num : Arithmetic.Real.rat_num -> Arithmetic.Real.real_expr
    val real_expr_of_arith_expr : Arithmetic.arith_expr -> Arithmetic.Real.real_expr
    val rat_num_of_real_expr : Arithmetic.Real.real_expr -> Arithmetic.Real.rat_num      

    val mk_sort : context -> real_sort
    val get_numerator : rat_num -> Integer.int_num
    val get_denominator : rat_num -> Integer.int_num
    val to_decimal_string : rat_num -> int -> string
    val to_string : rat_num -> string
    val mk_real_const : context -> Symbol.symbol -> real_expr
    val mk_real_const_s : context -> string -> real_expr
    val mk_numeral_nd : context -> int -> int -> rat_num
    val mk_numeral_s : context -> string -> rat_num
    val mk_numeral_i : context -> int -> rat_num
    val mk_is_integer : context -> real_expr -> Boolean.bool_expr
    val mk_real2int : context -> real_expr -> Integer.int_expr
  end

  and AlgebraicNumber :
  sig
    type algebraic_num = AlgebraicNum of arith_expr

    val arith_expr_of_algebraic_num : Arithmetic.AlgebraicNumber.algebraic_num -> Arithmetic.arith_expr
    val algebraic_num_of_arith_expr : Arithmetic.arith_expr -> Arithmetic.AlgebraicNumber.algebraic_num
    
    val to_upper : algebraic_num -> int -> Real.rat_num
    val to_lower : algebraic_num -> int -> Real.rat_num
    val to_decimal_string : algebraic_num -> int -> string
    val to_string : algebraic_num -> string
  end

  val is_int : Expr.expr -> bool
  val is_arithmetic_numeral : Expr.expr -> bool
  val is_le : Expr.expr -> bool
  val is_ge : Expr.expr -> bool
  val is_lt : Expr.expr -> bool
  val is_gt : Expr.expr -> bool
  val is_add : Expr.expr -> bool
  val is_sub : Expr.expr -> bool
  val is_uminus : Expr.expr -> bool
  val is_mul : Expr.expr -> bool
  val is_div : Expr.expr -> bool
  val is_idiv : Expr.expr -> bool
  val is_remainder : Expr.expr -> bool
  val is_modulus : Expr.expr -> bool
  val is_inttoreal : Expr.expr -> bool
  val is_real_to_int : Expr.expr -> bool
  val is_real_is_int : Expr.expr -> bool
  val is_real : Expr.expr -> bool
  val is_int_numeral : Expr.expr -> bool
  val is_rat_num : Expr.expr -> bool
  val is_algebraic_number : Expr.expr -> bool
  val mk_add : context -> arith_expr array -> arith_expr
  val mk_mul : context -> arith_expr array -> arith_expr
  val mk_sub : context -> arith_expr array -> arith_expr
  val mk_unary_minus : context -> arith_expr -> arith_expr
  val mk_div : context -> arith_expr -> arith_expr -> arith_expr
  val mk_power : context -> arith_expr -> arith_expr -> arith_expr
  val mk_lt : context -> arith_expr -> arith_expr -> Boolean.bool_expr
  val mk_le : context -> arith_expr -> arith_expr -> Boolean.bool_expr
  val mk_gt : context -> arith_expr -> arith_expr -> Boolean.bool_expr
  val mk_ge : context -> arith_expr -> arith_expr -> Boolean.bool_expr
end

and BitVector :
sig
  type bitvec_sort = BitVecSort of Sort.sort
  type bitvec_expr = BitVecExpr of Expr.expr
  type bitvec_num = BitVecNum of bitvec_expr

  val sort_of_bitvec_sort : BitVector.bitvec_sort -> Sort.sort
  val bitvec_sort_of_sort : Sort.sort -> BitVector.bitvec_sort
  val expr_of_bitvec_expr : BitVector.bitvec_expr -> Expr.expr
  val bitvec_expr_of_bitvec_num : BitVector.bitvec_num -> BitVector.bitvec_expr
  val bitvec_expr_of_expr : Expr.expr -> BitVector.bitvec_expr
  val bitvec_num_of_bitvec_expr : BitVector.bitvec_expr -> BitVector.bitvec_num

  val mk_sort : context -> int -> bitvec_sort
  val is_bv : Expr.expr -> bool
  val is_bv_numeral : Expr.expr -> bool
  val is_bv_bit1 : Expr.expr -> bool
  val is_bv_bit0 : Expr.expr -> bool
  val is_bv_uminus : Expr.expr -> bool
  val is_bv_add : Expr.expr -> bool
  val is_bv_sub : Expr.expr -> bool
  val is_bv_mul : Expr.expr -> bool
  val is_bv_sdiv : Expr.expr -> bool
  val is_bv_udiv : Expr.expr -> bool
  val is_bv_SRem : Expr.expr -> bool
  val is_bv_urem : Expr.expr -> bool
  val is_bv_smod : Expr.expr -> bool
  val is_bv_sdiv0 : Expr.expr -> bool
  val is_bv_udiv0 : Expr.expr -> bool
  val is_bv_srem0 : Expr.expr -> bool
  val is_bv_urem0 : Expr.expr -> bool
  val is_bv_smod0 : Expr.expr -> bool
  val is_bv_ule : Expr.expr -> bool
  val is_bv_sle : Expr.expr -> bool
  val is_bv_uge : Expr.expr -> bool
  val is_bv_sge : Expr.expr -> bool
  val is_bv_ult : Expr.expr -> bool
  val is_bv_slt : Expr.expr -> bool
  val is_bv_ugt : Expr.expr -> bool
  val is_bv_sgt : Expr.expr -> bool
  val is_bv_and : Expr.expr -> bool
  val is_bv_or : Expr.expr -> bool
  val is_bv_not : Expr.expr -> bool
  val is_bv_xor : Expr.expr -> bool
  val is_bv_nand : Expr.expr -> bool
  val is_bv_nor : Expr.expr -> bool
  val is_bv_xnor : Expr.expr -> bool
  val is_bv_concat : Expr.expr -> bool
  val is_bv_signextension : Expr.expr -> bool
  val is_bv_zeroextension : Expr.expr -> bool
  val is_bv_extract : Expr.expr -> bool
  val is_bv_repeat : Expr.expr -> bool
  val is_bv_reduceor : Expr.expr -> bool
  val is_bv_reduceand : Expr.expr -> bool
  val is_bv_comp : Expr.expr -> bool
  val is_bv_shiftleft : Expr.expr -> bool
  val is_bv_shiftrightlogical : Expr.expr -> bool
  val is_bv_shiftrightarithmetic : Expr.expr -> bool
  val is_bv_rotateleft : Expr.expr -> bool
  val is_bv_rotateright : Expr.expr -> bool
  val is_bv_rotateleftextended : Expr.expr -> bool
  val is_bv_rotaterightextended : Expr.expr -> bool
  val is_int_to_bv : Expr.expr -> bool
  val is_bv_to_int : Expr.expr -> bool
  val is_bv_carry : Expr.expr -> bool
  val is_bv_xor3 : Expr.expr -> bool
  val get_size : bitvec_sort -> int
  val get_int : bitvec_num -> int
  val to_string : bitvec_num -> string
  val mk_const : context -> Symbol.symbol -> int -> bitvec_expr
  val mk_const_s : context -> string -> int -> bitvec_expr
  val mk_not : context -> bitvec_expr -> Expr.expr
  val mk_redand : context -> bitvec_expr -> Expr.expr
  val mk_redor : context -> bitvec_expr -> Expr.expr
  val mk_and : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_or : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_xor : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_nand : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_nor : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_xnor : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_neg : context -> bitvec_expr -> bitvec_expr
  val mk_add : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_sub : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_mul : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_udiv : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_sdiv : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_urem : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_srem : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_smod : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_ult : context -> bitvec_expr -> bitvec_expr -> Boolean.bool_expr
  val mk_slt : context -> bitvec_expr -> bitvec_expr -> Boolean.bool_expr
  val mk_ule : context -> bitvec_expr -> bitvec_expr -> Boolean.bool_expr
  val mk_sle : context -> bitvec_expr -> bitvec_expr -> Boolean.bool_expr
  val mk_uge : context -> bitvec_expr -> bitvec_expr -> Boolean.bool_expr
  val mk_sge : context -> bitvec_expr -> bitvec_expr -> Boolean.bool_expr
  val mk_ugt : context -> bitvec_expr -> bitvec_expr -> Boolean.bool_expr
  val mk_sgt : context -> bitvec_expr -> bitvec_expr -> Boolean.bool_expr
  val mk_concat : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_extract : context -> int -> int -> bitvec_expr -> bitvec_expr
  val mk_sign_ext : context -> int -> bitvec_expr -> bitvec_expr
  val mk_zero_ext : context -> int -> bitvec_expr -> bitvec_expr
  val mk_repeat : context -> int -> bitvec_expr -> bitvec_expr
  val mk_shl : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_lshr : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_ashr : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_rotate_left : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_rotate_right : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_bv2int : context -> bitvec_expr -> bool -> Arithmetic.Integer.int_expr
  val mk_add_no_overflow : context -> bitvec_expr -> bitvec_expr -> bool -> Boolean.bool_expr
  val mk_add_no_underflow : context -> bitvec_expr -> bitvec_expr -> Boolean.bool_expr
  val mk_sub_no_overflow : context -> bitvec_expr -> bitvec_expr -> Boolean.bool_expr
  val mk_sub_no_underflow : context -> bitvec_expr -> bitvec_expr -> bool -> Boolean.bool_expr
  val mk_sdiv_no_overflow : context -> bitvec_expr -> bitvec_expr -> Boolean.bool_expr
  val mk_neg_no_overflow : context -> bitvec_expr -> Boolean.bool_expr
  val mk_mul_no_overflow : context -> bitvec_expr -> bitvec_expr -> bool -> Boolean.bool_expr
  val mk_mul_no_underflow : context -> bitvec_expr -> bitvec_expr -> Boolean.bool_expr
  val mk_numeral : context -> string -> int -> bitvec_num
end

module Proof :
sig
  val is_true : Expr.expr -> bool
  val is_asserted : Expr.expr -> bool
  val is_goal : Expr.expr -> bool
  val is_modus_ponens : Expr.expr -> bool
  val is_reflexivity : Expr.expr -> bool
  val is_symmetry : Expr.expr -> bool
  val is_transitivity : Expr.expr -> bool
  val is_Transitivity_star : Expr.expr -> bool
  val is_monotonicity : Expr.expr -> bool
  val is_quant_intro : Expr.expr -> bool
  val is_distributivity : Expr.expr -> bool
  val is_and_elimination : Expr.expr -> bool
  val is_or_elimination : Expr.expr -> bool
  val is_rewrite : Expr.expr -> bool
  val is_rewrite_star : Expr.expr -> bool
  val is_pull_quant : Expr.expr -> bool
  val is_pull_quant_star : Expr.expr -> bool
  val is_push_quant : Expr.expr -> bool
  val is_elim_unused_vars : Expr.expr -> bool
  val is_der : Expr.expr -> bool
  val is_quant_inst : Expr.expr -> bool
  val is_hypothesis : Expr.expr -> bool
  val is_lemma : Expr.expr -> bool
  val is_unit_resolution : Expr.expr -> bool
  val is_iff_true : Expr.expr -> bool
  val is_iff_false : Expr.expr -> bool
  val is_commutativity : Expr.expr -> bool
  val is_def_axiom : Expr.expr -> bool
  val is_def_intro : Expr.expr -> bool
  val is_apply_def : Expr.expr -> bool
  val is_iff_oeq : Expr.expr -> bool
  val is_nnf_pos : Expr.expr -> bool
  val is_nnf_neg : Expr.expr -> bool
  val is_nnf_star : Expr.expr -> bool
  val is_cnf_star : Expr.expr -> bool
  val is_skolemize : Expr.expr -> bool
  val is_modus_ponens_oeq : Expr.expr -> bool
  val is_theory_lemma : Expr.expr -> bool
end


module Goal :
sig
  type goal 

  val get_precision : goal -> Z3enums.goal_prec
  val is_precise : goal -> bool
  val is_underapproximation : goal -> bool
  val is_overapproximation : goal -> bool
  val is_garbage : goal -> bool
  val assert_ : goal -> Boolean.bool_expr array -> unit
  val is_inconsistent : goal -> bool
  val get_depth : goal -> int
  val reset : goal -> unit
  val get_size : goal -> int
  val get_formulas : goal -> Boolean.bool_expr array
  val get_num_exprs : goal -> int
  val is_decided_sat : goal -> bool
  val is_decided_unsat : goal -> bool
  val translate : goal -> context -> goal
  val simplify : goal -> Params.params option -> goal
  val mk_goal : context -> bool -> bool -> bool -> goal
  val to_string : goal -> string
end

module Model :
sig
  type model 

  module FuncInterp :
  sig
    type func_interp 
      
    module FuncEntry :
    sig
      type func_entry 
	
      val get_value : func_entry -> Expr.expr
      val get_num_args : func_entry -> int
      val get_args : func_entry -> Expr.expr array
      val to_string : func_entry -> string
    end

    val get_num_entries : func_interp -> int
    val get_entries : func_interp -> FuncEntry.func_entry array
    val get_else : func_interp -> Expr.expr
    val get_arity : func_interp -> int
    val to_string : func_interp -> string
  end

  val get_const_interp : model -> FuncDecl.func_decl -> Expr.expr option
  val get_const_interp_e : model -> Expr.expr -> Expr.expr option
  val get_func_interp : model -> FuncDecl.func_decl -> FuncInterp.func_interp option
  val get_num_consts : model -> int
  val get_const_decls : model -> FuncDecl.func_decl array
  val get_num_funcs : model -> int
  val get_func_decls : model -> FuncDecl.func_decl array
  val get_decls : model -> FuncDecl.func_decl array
  exception ModelEvaluationFailedException of string
  val eval : model -> Expr.expr -> bool -> Expr.expr
  val evaluate : model -> Expr.expr -> bool -> Expr.expr
  val get_num_sorts : model -> int
  val get_sorts : model -> Sort.sort array
  val sort_universe : model -> Sort.sort -> AST.ASTVector.ast_vector array
  val to_string : model -> string
end

module Probe :
sig
  type probe 

  val apply : probe -> Goal.goal -> float
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
  type tactic 

  module ApplyResult :
  sig
    type apply_result 

    val get_num_subgoals : apply_result -> int
    val get_subgoals : apply_result -> Goal.goal array
    val get_subgoal : apply_result -> int -> Goal.goal
    val convert_model : apply_result -> int -> Model.model -> Model.model
    val to_string : apply_result -> string
  end

  val get_help : tactic -> string
  val get_param_descrs : tactic -> Params.ParamDescrs.param_descrs
  val apply : tactic -> Goal.goal -> Params.params option -> ApplyResult.apply_result
  val get_num_tactics : context -> int
  val get_tactic_names : context -> string array
  val get_tactic_description : context -> string -> string
  val mk_tactic : context -> string -> tactic
  val and_then : context -> tactic -> tactic -> tactic array -> tactic
  val or_else : context -> tactic -> tactic -> tactic
  val try_for : context -> tactic -> int -> tactic
  val when_ : context -> Probe.probe -> tactic -> tactic
  val cond : context -> Probe.probe -> tactic -> tactic -> tactic
  val repeat : context -> tactic -> int -> tactic
  val skip : context -> tactic
  val fail : context -> tactic
  val fail_if : context -> Probe.probe -> tactic
  val fail_if_not_decided : context -> tactic
  val using_params : context -> tactic -> Params.params -> tactic
  val with_ : context -> tactic -> Params.params -> tactic
  val par_or : context -> tactic array -> tactic
  val par_and_then : context -> tactic -> tactic -> tactic
  val interrupt : context -> unit
end

module Solver :
sig
  type solver 
  type status = UNSATISFIABLE | UNKNOWN | SATISFIABLE
      
  val string_of_status : status -> string

  module Statistics :
  sig
    type statistics 

    module Entry :
    sig
      type statistics_entry

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
    val get_entries : statistics -> Entry.statistics_entry array
    val get_keys : statistics -> string array
    val get : statistics -> string -> Entry.statistics_entry option
  end

  val get_help : solver -> string
  val set_parameters : solver -> Params.params -> unit
  val get_param_descrs : solver -> Params.ParamDescrs.param_descrs
  val get_num_scopes : solver -> int
  val push : solver -> unit
  val pop : solver -> int -> unit
  val reset : solver -> unit
  val assert_ : solver -> Boolean.bool_expr array -> unit
  val assert_and_track : solver -> Boolean.bool_expr -> Boolean.bool_expr -> unit
  val get_num_assertions : solver -> int
  val get_assertions : solver -> Boolean.bool_expr array
  val check : solver -> Boolean.bool_expr array -> status
  val get_model : solver -> Model.model option
  val get_proof : solver -> Expr.expr option
  val get_unsat_core : solver -> AST.ASTVector.ast_vector array
  val get_reason_unknown : solver -> string
  val get_statistics : solver -> Statistics.statistics
  val mk_solver : context -> Symbol.symbol option -> solver
  val mk_solver_s : context -> string -> solver
  val mk_simple_solver : context -> solver
  val mk_solver_t : context -> Tactic.tactic -> solver
  val to_string : solver -> string
end

module Fixedpoint :
sig
  type fixedpoint 
    
  val get_help : fixedpoint -> string
  val set_params : fixedpoint -> Params.params -> unit
  val get_param_descrs : fixedpoint -> Params.ParamDescrs.param_descrs
  val assert_ : fixedpoint -> Boolean.bool_expr array -> unit
  val register_relation : fixedpoint -> FuncDecl.func_decl -> unit
  val add_rule : fixedpoint -> Boolean.bool_expr -> Symbol.symbol option -> unit
  val add_fact : fixedpoint -> FuncDecl.func_decl -> int array -> unit
  val query : fixedpoint -> Boolean.bool_expr -> Solver.status
  val query_r : fixedpoint -> FuncDecl.func_decl array -> Solver.status
  val push : fixedpoint -> unit
  val pop : fixedpoint -> unit
  val update_rule : fixedpoint -> Boolean.bool_expr -> Symbol.symbol -> unit
  val get_answer : fixedpoint -> Expr.expr option
  val get_reason_unknown : fixedpoint -> string
  val get_num_levels : fixedpoint -> FuncDecl.func_decl -> int
  val get_cover_delta : fixedpoint -> int -> FuncDecl.func_decl -> Expr.expr option
  val add_cover : fixedpoint -> int -> FuncDecl.func_decl -> Expr.expr -> unit
  val to_string : fixedpoint -> string
  val set_predicate_representation : fixedpoint -> FuncDecl.func_decl -> Symbol.symbol array -> unit
  val to_string_q : fixedpoint -> Boolean.bool_expr array -> string
  val get_rules : fixedpoint -> Boolean.bool_expr array
  val get_assertions : fixedpoint -> Boolean.bool_expr array
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
  val benchmark_to_smtstring : context -> string -> string -> string -> string -> Boolean.bool_expr array -> Boolean.bool_expr -> string
  val parse_smtlib_string : context -> string -> Symbol.symbol array -> Sort.sort array -> Symbol.symbol array -> FuncDecl.func_decl array -> unit
  val parse_smtlib_file : context -> string -> Symbol.symbol array -> Sort.sort array -> Symbol.symbol array -> FuncDecl.func_decl array -> unit
  val get_num_smtlib_formulas : context -> int
  val get_smtlib_formulas : context -> Boolean.bool_expr array
  val get_num_smtlib_assumptions : context -> int
  val get_smtlib_assumptions : context -> Boolean.bool_expr array
  val get_num_smtlib_decls : context -> int
  val get_smtlib_decls : context -> FuncDecl.func_decl array
  val get_num_smtlib_sorts : context -> int
  val get_smtlib_sorts : context -> Sort.sort array
  val parse_smtlib2_string : context -> string -> Symbol.symbol array -> Sort.sort array -> Symbol.symbol array -> FuncDecl.func_decl array -> Boolean.bool_expr
  val parse_smtlib2_file : context -> string -> Symbol.symbol array -> Sort.sort array -> Symbol.symbol array -> FuncDecl.func_decl array -> Boolean.bool_expr
end

val set_global_param : string -> string -> unit
val get_global_param : string -> string option
val global_param_reset_all : unit
