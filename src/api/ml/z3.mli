(**
   The Z3 ML/OCaml Interface.

   Copyright (C) 2012 Microsoft Corporation
   @author CM Wintersteiger (cwinter) 2012-12-17
*)

(** General Z3 exceptions

    Many functions in this API may throw an exception; if they do, it is this one.*)
exception Error of string

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

(** Create a context object
    The following parameters can be set:

    - proof  (Boolean)           Enable proof generation
    - debug_ref_count (Boolean)  Enable debug support for Z3_ast reference counting
    - trace  (Boolean)           Tracing support for VCC
    - trace_file_name (String)   Trace out file for VCC traces
    - timeout (unsigned)         default timeout (in milliseconds) used for solvers
    - well_sorted_check          type checker
    - auto_config                use heuristics to automatically select solver and configure it
    - model                      model generation for solvers, this parameter can be overwritten when creating a solver
    - model_validate             validate models produced by solvers
    - unsat_core                 unsat-core generation for solvers, this parameter can be overwritten when creating a solver
*)
val mk_context : (string * string) list -> context

(** Interaction logging for Z3
    Note that this is a global, static log and if multiple Context
    objects are created, it logs the interaction with all of them. *)
module Log :
sig
  (** Open an interaction log file.
      @return True if opening the log file succeeds, false otherwise. *)
  (* CMW: "open" is a reserved keyword. *)
  val open_ : string -> bool

  (** Closes the interaction log. *)
  val close : unit -> unit

  (** Appends a user-provided string to the interaction log. *)
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

  (** A full version string. *)
  val full_version : string

  (** A string representation of the version information. *)
  val to_string : string
end

(** Symbols are used to name several term and type constructors *)
module Symbol :
sig
  type symbol

  (** The kind of the symbol (int or string) *)
  val kind : symbol -> Z3enums.symbol_kind

  (** Indicates whether the symbol is of Int kind *)
  val is_int_symbol : symbol -> bool

  (** Indicates whether the symbol is of string kind. *)
  val is_string_symbol : symbol -> bool

  (** The int value of the symbol. *)
  val get_int : symbol -> int

  (** The string value of the symbol. *)
  val get_string : symbol -> string

  (** A string representation of the symbol. *)
  val to_string : symbol -> string

  (** Creates a new symbol using an integer.
      Not all integers can be passed to this function.
      The legal range of unsigned integers is 0 to 2^30-1. *)
  val mk_int : context -> int -> symbol

  (** Creates a new symbol using a string. *)
  val mk_string : context -> string -> symbol

  (** Create a list of symbols. *)
  val mk_ints : context -> int list -> symbol list

  (** Create a list of symbols. *)
  val mk_strings : context -> string list -> symbol list
end

(** The abstract syntax tree (AST) module *)
module rec AST :
sig
  type ast

  (** Vectors of ASTs *)
  module ASTVector :
  sig
    type ast_vector

    (** Create an empty AST vector *)
    val mk_ast_vector : context -> ast_vector

    (** The size of the vector *)
    val get_size : ast_vector -> int

    (** Retrieves the i-th object in the vector.
                @return An AST *)
    val get : ast_vector -> int -> ast

    (** Sets the i-th object in the vector. *)
    val set : ast_vector -> int -> ast -> unit

    (** Resize the vector to a new size. *)
    val resize : ast_vector -> int -> unit

    (** Add an ast to the back of the vector. The size
                is increased by 1. *)
    val push : ast_vector -> ast -> unit

    (** Translates all ASTs in the vector to another context.
                @return A new ASTVector *)
    val translate : ast_vector -> context -> ast_vector

    (** Translates the ASTVector into an (Ast.ast list) *)
    val to_list : ast_vector -> ast list

    (** Translates the ASTVector into an (Expr.expr list) *)
    val to_expr_list : ast_vector -> Expr.expr list

    (** Retrieves a string representation of the vector. *)
    val to_string : ast_vector -> string
  end

  (** Map from AST to AST *)
  module ASTMap :
  sig
    type ast_map

    (** Create an empty mapping from AST to AST *)
    val mk_ast_map : context -> ast_map

    (** Checks whether the map contains a key.
                @return True if the key in the map, false otherwise. *)
    val contains : ast_map -> ast -> bool

    (** Finds the value associated with the key.
                This function signs an error when the key is not a key in the map. *)
    val find : ast_map -> ast -> ast

    (**   Stores or replaces a new key/value pair in the map. *)
    val insert : ast_map -> ast -> ast -> unit

    (**   Erases the key from the map.*)
    val erase : ast_map -> ast -> unit

    (**  Removes all keys from the map. *)
    val reset : ast_map -> unit

    (** The size of the map *)
    val get_size : ast_map -> int

    (** The keys stored in the map. *)
    val get_keys : ast_map -> ast list

    (** Retrieves a string representation of the map.*)
    val to_string : ast_map -> string
  end

  (** The AST's hash code.
      @return A hash code *)
  val hash : ast -> int

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

  (** Comparison operator.
      @return True if the two ast's are from the same context
      and represent the same sort; false otherwise. *)
  val equal : ast -> ast -> bool

  (** Object Comparison.
      @return Negative if the first ast should be sorted before the second, positive if after else zero. *)
  val compare : ast -> ast -> int

  (** Translates (copies) the AST to another context.
      @return A copy of the AST which is associated with the other context.  *)
  val translate : ast -> context -> ast
end

(** The Sort module implements type information for ASTs *)
and Sort :
sig
  type sort

  (** Comparison operator.
      @return True if the two sorts are from the same context
      and represent the same sort; false otherwise. *)
  val equal : sort -> sort -> bool

  (** Returns a unique identifier for the sort. *)
  val get_id : sort -> int

  (** The kind of the sort. *)
  val get_sort_kind : sort -> Z3enums.sort_kind

  (** The name of the sort *)
  val get_name : sort -> Symbol.symbol

  (** A string representation of the sort. *)
  val to_string : sort -> string

  (** Create a new uninterpreted sort. *)
  val mk_uninterpreted : context -> Symbol.symbol -> sort

  (** Create a new uninterpreted sort. *)
  val mk_uninterpreted_s : context -> string -> sort
end

(** Function declarations *)
and FuncDecl :
sig
  type func_decl

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

    (** The float value of the parameter.*)
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
  val mk_func_decl : context -> Symbol.symbol -> Sort.sort list -> Sort.sort -> func_decl

  (** Creates a new function declaration. *)
  val mk_func_decl_s : context -> string -> Sort.sort list -> Sort.sort -> func_decl
  (** Creates a fresh function declaration with a name prefixed with a prefix string. *)

  val mk_fresh_func_decl : context -> string -> Sort.sort list -> Sort.sort -> func_decl

  (** Creates a new constant function declaration. *)
  val mk_const_decl : context -> Symbol.symbol -> Sort.sort -> func_decl

  (** Creates a new constant function declaration. *)
  val mk_const_decl_s : context -> string -> Sort.sort -> func_decl

  (** Creates a fresh constant function declaration with a name prefixed with a prefix string.
      {!mk_func_decl}
      {!mk_func_decl} *)
  val mk_fresh_const_decl : context -> string -> Sort.sort -> func_decl

  (** Comparison operator.
      @return True if a and b are from the same context and represent the same func_decl; false otherwise. *)
  val equal : func_decl -> func_decl -> bool

  (** A string representations of the function declaration. *)
  val to_string : func_decl -> string

  (** Returns a unique identifier for the function declaration. *)
  val get_id : func_decl -> int

  (** The arity of the function declaration *)
  val get_arity : func_decl -> int

  (** The size of the domain of the function declaration
      {!get_arity} *)
  val get_domain_size : func_decl -> int

  (** The domain of the function declaration *)
  val get_domain : func_decl -> Sort.sort list

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

  (** Create expression that applies function to arguments. *)
  val apply : func_decl -> Expr.expr list -> Expr.expr
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
    val get_names : param_descrs -> Symbol.symbol list

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
  val add_float : params -> Symbol.symbol -> float -> unit

  (** Adds a parameter setting. *)
  val add_symbol : params -> Symbol.symbol -> Symbol.symbol -> unit

  (** Creates a new parameter set *)
  val mk_params : context -> params

  (** A string representation of the parameter set. *)
  val to_string : params -> string

  (** Update a mutable configuration parameter.

      The list of all configuration parameters can be obtained using the Z3 executable:
      [z3.exe -p]
      Only a few configuration parameters are mutable once the context is created.
      An exception is thrown when trying to modify an immutable parameter. *)
  val update_param_value : context -> string -> string -> unit

  (** Selects the format used for pretty-printing expressions.

      The default mode for pretty printing expressions is to produce
      SMT-LIB style output where common subexpressions are printed
      at each occurrence. The mode is called PRINT_SMTLIB_FULL.
      To print shared common subexpressions only once,
      use the PRINT_LOW_LEVEL mode.
      To print in way that conforms to SMT-LIB standards and uses let
      expressions to share common sub-expressions use PRINT_SMTLIB_COMPLIANT.
      {!AST.to_string}
      {!Quantifier.Pattern.to_string}
      {!FuncDecl.to_string}
      {!Sort.to_string} *)
  val set_print_mode : context -> Z3enums.ast_print_mode -> unit
end

(** General Expressions (terms) *)
and Expr :
sig
  type expr

  val ast_of_expr : Expr.expr -> AST.ast
  val expr_of_ast : AST.ast -> Expr.expr

  (** Returns a simplified version of the expression.
      {!get_simplify_help} *)
  val simplify : Expr.expr -> Params.params option -> expr

  (** A string describing all available parameters to [Expr.Simplify]. *)
  val get_simplify_help : context -> string

  (** Retrieves parameter descriptions for simplifier. *)
  val get_simplify_parameter_descrs : context -> Params.ParamDescrs.param_descrs

  (** The function declaration of the function that is applied in this expression. *)
  val get_func_decl : Expr.expr -> FuncDecl.func_decl

  (** The number of arguments of the expression. *)
  val get_num_args : Expr.expr -> int

  (** The arguments of the expression. *)
  val get_args : Expr.expr -> Expr.expr list

  (** Update the arguments of the expression using an array of expressions.
      The number of new arguments should coincide with the current number of arguments. *)
  val update : Expr.expr -> Expr.expr list -> expr

  (** Substitute every occurrence of [from[i]] in the expression with [to[i]], for [i] smaller than [num_exprs].

      The result is the new expression. The arrays [from] and [to] must have size [num_exprs].
      For every [i] smaller than [num_exprs], we must have that
      sort of [from[i]] must be equal to sort of [to[i]]. *)
  val substitute : Expr.expr -> Expr.expr list -> Expr.expr list -> expr

  (** Substitute every occurrence of [from] in the expression with [to].
      {!substitute} *)
  val substitute_one : Expr.expr -> Expr.expr -> Expr.expr -> expr

  (** Substitute the free variables in the expression with the expressions in the expr array

      For every [i] smaller than [num_exprs], the variable with de-Bruijn index [i] is replaced with term [to[i]]. *)
  val substitute_vars : Expr.expr -> Expr.expr list -> expr

  (** Translates (copies) the term to another context.
      @return A copy of the term which is associated with the other context *)
  val translate : Expr.expr -> context -> expr

  (** Returns a string representation of the expression. *)
  val to_string : Expr.expr -> string

  (** Indicates whether the term is a numeral *)
  val is_numeral : Expr.expr -> bool

  (** Indicates whether the term is well-sorted.
      @return True if the term is well-sorted, false otherwise. *)
  val is_well_sorted : Expr.expr -> bool

  (** The Sort of the term. *)
  val get_sort : Expr.expr -> Sort.sort

  (** Indicates whether the term represents a constant. *)
  val is_const : Expr.expr -> bool

  (** Creates a new constant. *)
  val mk_const : context -> Symbol.symbol -> Sort.sort -> expr

  (** Creates a new constant. *)
  val mk_const_s : context -> string -> Sort.sort -> expr

  (** Creates a  constant from the func_decl. *)
  val mk_const_f : context -> FuncDecl.func_decl -> expr

  (** Creates a fresh constant with a name prefixed with a string. *)
  val mk_fresh_const : context -> string -> Sort.sort -> expr

  (** Create a new function application. *)
  val mk_app : context -> FuncDecl.func_decl -> Expr.expr list -> expr

  (** Create a numeral of a given sort.
      @return A Term with the given value and sort *)
  val mk_numeral_string : context -> string -> Sort.sort -> expr

  (** Create a numeral of a given sort. This function can be used to create numerals that fit in a machine integer.
      It is slightly faster than [MakeNumeral] since it is not necessary to parse a string.
      @return A Term with the given value and sort *)
  val mk_numeral_int : context -> int -> Sort.sort -> expr

  (** Comparison operator.
      @return True if the two expr's are equal; false otherwise. *)
  val equal : expr -> expr -> bool

  (** Object Comparison.
      @return Negative if the first expr should be sorted before the second, positive if after, else zero. *)
  val compare : expr -> expr -> int
end

(** Boolean expressions; Propositional logic and equality *)
module Boolean :
sig
  (** Create a Boolean sort *)
  val mk_sort : context -> Sort.sort

  (** Create a Boolean constant. *)
  val mk_const : context -> Symbol.symbol -> Expr.expr

  (** Create a Boolean constant. *)
  val mk_const_s : context -> string -> Expr.expr

  (** The true Term. *)
  val mk_true : context -> Expr.expr

  (** The false Term. *)
  val mk_false : context -> Expr.expr

  (** Creates a Boolean value. *)
  val mk_val : context -> bool -> Expr.expr

  (** Mk an expression representing [not(a)]. *)
  val mk_not : context -> Expr.expr -> Expr.expr

  (** Create an expression representing an if-then-else: [ite(t1, t2, t3)]. *)
  val mk_ite : context -> Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create an expression representing [t1 iff t2]. *)
  val mk_iff : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create an expression representing [t1 -> t2]. *)
  val mk_implies : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create an expression representing [t1 xor t2]. *)
  val mk_xor : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create an expression representing the AND of args *)
  val mk_and : context -> Expr.expr list -> Expr.expr

  (** Create an expression representing the OR of args *)
  val mk_or : context -> Expr.expr list -> Expr.expr

  (** Creates the equality between two expr's. *)
  val mk_eq : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Creates a [distinct] term. *)
  val mk_distinct : context -> Expr.expr list -> Expr.expr

  (** Indicates whether the expression is the true or false expression
      or something else (L_UNDEF). *)
  val get_bool_value : Expr.expr -> Z3enums.lbool

  (** Indicates whether the term has Boolean sort. *)
  val is_bool : Expr.expr -> bool

  (** Indicates whether the term is the constant true. *)
  val is_true : Expr.expr -> bool

  (** Indicates whether the term is the constant false. *)
  val is_false : Expr.expr -> bool

  (** Indicates whether the term is an equality predicate. *)
  val is_eq : Expr.expr -> bool

  (** Indicates whether the term is an n-ary distinct predicate (every argument is mutually distinct). *)
  val is_distinct : Expr.expr -> bool

  (** Indicates whether the term is a ternary if-then-else term *)
  val is_ite : Expr.expr -> bool

  (** Indicates whether the term is an n-ary conjunction *)
  val is_and : Expr.expr -> bool

  (** Indicates whether the term is an n-ary disjunction *)
  val is_or : Expr.expr -> bool

  (** Indicates whether the term is an if-and-only-if (Boolean equivalence, binary) *)
  val is_iff : Expr.expr -> bool

  (** Indicates whether the term is an exclusive or *)
  val is_xor : Expr.expr -> bool

  (** Indicates whether the term is a negation *)
  val is_not : Expr.expr -> bool

  (** Indicates whether the term is an implication *)
  val is_implies : Expr.expr -> bool
end

(** Quantifier expressions *)
module Quantifier :
sig
  type quantifier

  val expr_of_quantifier : quantifier -> Expr.expr
  val quantifier_of_expr : Expr.expr -> quantifier

  (** Quantifier patterns

      Patterns comprise a list of terms. The list should be
      non-empty.  If the list comprises of more than one term, it is
      also called a multi-pattern. *)
  module Pattern :
  sig
    type pattern

    (** The number of terms in the pattern. *)
    val get_num_terms : pattern -> int

    (** The terms in the pattern. *)
    val get_terms : pattern -> Expr.expr list

    (** A string representation of the pattern. *)
    val to_string : pattern -> string
  end


  (** The de-Bruijn index of a bound variable.

      Bound variables are indexed by de-Bruijn indices. It is perhaps easiest to explain
      the meaning of de-Bruijn indices by indicating the compilation process from
      non-de-Bruijn formulas to de-Bruijn format.
      <code>
      abs(forall (x1) phi) = forall (x1) abs1(phi, x1, 0)
      abs(forall (x1, x2) phi) = abs(forall (x1) abs(forall (x2) phi))
      abs1(x, x, n) = b_n
      abs1(y, x, n) = y
      abs1(f(t1,...,tn), x, n) = f(abs1(t1,x,n), ..., abs1(tn,x,n))
      abs1(forall (x1) phi, x, n) = forall (x1) (abs1(phi, x, n+1))
      </code>
      The last line is significant: the index of a bound variable is different depending
      on the scope in which it appears. The deeper ( x : expr ) appears, the higher is its
      index. *)
  val get_index : Expr.expr -> int

  (** Indicates whether the quantifier is universal. *)
  val is_universal : quantifier -> bool

  (** Indicates whether the quantifier is existential. *)
  val is_existential : quantifier -> bool

  (** The weight of the quantifier. *)
  val get_weight : quantifier -> int

  (** The number of patterns. *)
  val get_num_patterns : quantifier -> int

  (** The patterns. *)
  val get_patterns : quantifier -> Pattern.pattern list

  (** The number of no-patterns. *)
  val get_num_no_patterns : quantifier -> int

  (** The no-patterns. *)
  val get_no_patterns : quantifier -> Pattern.pattern list

  (** The number of bound variables. *)
  val get_num_bound : quantifier -> int

  (** The symbols for the bound variables. *)
  val get_bound_variable_names : quantifier -> Symbol.symbol list

  (** The sorts of the bound variables. *)
  val get_bound_variable_sorts : quantifier -> Sort.sort list

  (** The body of the quantifier. *)
  val get_body : quantifier -> Expr.expr

  (** Creates a new bound variable. *)
  val mk_bound : context -> int -> Sort.sort -> Expr.expr

  (** Create a quantifier pattern. *)
  val mk_pattern : context -> Expr.expr list -> Pattern.pattern

  (** Create a universal Quantifier. *)
  val mk_forall : context -> Sort.sort list -> Symbol.symbol list -> Expr.expr -> int option -> Pattern.pattern list -> Expr.expr list -> Symbol.symbol option -> Symbol.symbol option -> quantifier

  (** Create a universal Quantifier. *)
  val mk_forall_const : context -> Expr.expr list -> Expr.expr -> int option -> Pattern.pattern list -> Expr.expr list -> Symbol.symbol option -> Symbol.symbol option -> quantifier

  (** Create an existential Quantifier. *)
  val mk_exists : context -> Sort.sort list -> Symbol.symbol list -> Expr.expr -> int option -> Pattern.pattern list -> Expr.expr list -> Symbol.symbol option -> Symbol.symbol option -> quantifier

  (** Create an existential Quantifier. *)
  val mk_exists_const : context -> Expr.expr list -> Expr.expr -> int option -> Pattern.pattern list -> Expr.expr list -> Symbol.symbol option -> Symbol.symbol option -> quantifier

  (** Create a lambda binding. *)
  val mk_lambda_const : context -> Expr.expr list -> Expr.expr -> quantifier

  (** Create a lambda binding where bound variables are given by symbols and sorts *)
  val mk_lambda : context -> (Symbol.symbol * Sort.sort) list -> Expr.expr -> quantifier

  (** Create a Quantifier. *)
  val mk_quantifier : context -> bool -> Sort.sort list -> Symbol.symbol list -> Expr.expr -> int option -> Pattern.pattern list -> Expr.expr list -> Symbol.symbol option -> Symbol.symbol option -> quantifier

  (** Create a Quantifier. *)
  val mk_quantifier_const : context -> bool -> Expr.expr list -> Expr.expr -> int option -> Pattern.pattern list -> Expr.expr list -> Symbol.symbol option -> Symbol.symbol option -> quantifier

  (** A string representation of the quantifier. *)
  val to_string : quantifier -> string
end

(** Functions to manipulate Array expressions *)
module Z3Array :
sig
  (** Create a new array sort. *)
  val mk_sort : context -> Sort.sort -> Sort.sort -> Sort.sort

  (** Indicates whether the term is an array store.
      It satisfies select(store(a,i,v),j) = if i = j then v else select(a,j).
      Array store takes at least 3 arguments.  *)
  val is_store : Expr.expr -> bool

  (** Indicates whether the term is an array select. *)
  val is_select : Expr.expr -> bool

  (** Indicates whether the term is a constant array.
      For example, select(const(v),i) = v holds for every v and i. The function is unary. *)
  val is_constant_array : Expr.expr -> bool

  (** Indicates whether the term is a default array.
      For example default(const(v)) = v. The function is unary. *)
  val is_default_array : Expr.expr -> bool

  (** Indicates whether the term is an array map.
      It satisfies map[f](a1,..,a_n)[i] = f(a1[i],...,a_n[i]) for every i. *)
  val is_array_map : Expr.expr -> bool

  (** Indicates whether the term is an as-array term.
      An as-array term is n array value that behaves as the function graph of the
      function passed as parameter. *)
  val is_as_array : Expr.expr -> bool

  (** Indicates whether the term is of an array sort. *)
  val is_array : Expr.expr -> bool

  (** The domain of the array sort. *)
  val get_domain : Sort.sort -> Sort.sort

  (** The range of the array sort. *)
  val get_range : Sort.sort -> Sort.sort

  (** Create an array constant. *)
  val mk_const : context -> Symbol.symbol -> Sort.sort -> Sort.sort -> Expr.expr

  (** Create an array constant. *)
  val mk_const_s : context -> string -> Sort.sort -> Sort.sort -> Expr.expr

  (** Array read.

      The argument [a] is the array and [i] is the index
      of the array that gets read.

      The node [a] must have an array sort [[domain -> range]],
      and [i] must have the sort [domain].
      The sort of the result is [range].
      {!Z3Array.mk_sort}
      {!mk_store} *)
  val mk_select : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Array update.

      The node [a] must have an array sort [[domain -> range]],
      [i] must have sort [domain],
      [v] must have sort range. The sort of the result is [[domain -> range]].
      The semantics of this function is given by the theory of arrays described in the SMT-LIB
      standard. See http://smtlib.org for more details.
      The result of this function is an array that is equal to [a]
      (with respect to [select])
      on all indices except for [i], where it maps to [v]
      (and the [select] of [a] with
      respect to [i] may be a different value).
      {!Z3Array.mk_sort}
      {!mk_select} *)
  val mk_store : context -> Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create a constant array.

      The resulting term is an array, such that a [select]on an arbitrary index
      produces the value [v].
      {!Z3Array.mk_sort}
      {!mk_select} *)
  val mk_const_array : context -> Sort.sort -> Expr.expr -> Expr.expr

  (** Maps f on the argument arrays.

      Each element of [args] must be of an array sort [[domain_i -> range_i]].
      The function declaration [f] must have type [ range_1 .. range_n -> range].
      [v] must have sort range. The sort of the result is [[domain_i -> range]].
      {!Z3Array.mk_sort}
      {!mk_select}
      {!mk_store} *)
  val mk_map : context -> FuncDecl.func_decl -> Expr.expr list -> Expr.expr

  (** Access the array default value.

      Produces the default range value, for arrays that can be represented as
      finite maps with a default range value. *)
  val mk_term_array : context -> Expr.expr -> Expr.expr

  (** Create array extensionality index given two arrays with the same sort.

      The meaning is given by the axiom:
          (=> (= (select A (array-ext A B)) (select B (array-ext A B))) (= A B)) *)
  val mk_array_ext : context -> Expr.expr -> Expr.expr -> Expr.expr

end

(** Functions to manipulate Set expressions *)
module Set :
sig
  (** Create a set type. *)
  val mk_sort : context -> Sort.sort -> Sort.sort

  (** Indicates whether the term is set union *)
  val is_union : Expr.expr -> bool

  (** Indicates whether the term is set intersection *)
  val is_intersect : Expr.expr -> bool

  (** Indicates whether the term is set difference *)
  val is_difference : Expr.expr -> bool

  (** Indicates whether the term is set complement *)
  val is_complement : Expr.expr -> bool

  (** Indicates whether the term is set subset *)
  val is_subset : Expr.expr -> bool

  (** Create an empty set. *)
  val mk_empty : context -> Sort.sort -> Expr.expr

  (** Create the full set. *)
  val mk_full : context -> Sort.sort -> Expr.expr

  (** Add an element to the set. *)
  val mk_set_add : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Remove an element from a set. *)
  val mk_del : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Take the union of a list of sets. *)
  val mk_union : context -> Expr.expr list -> Expr.expr

  (** Take the intersection of a list of sets. *)
  val mk_intersection : context -> Expr.expr list -> Expr.expr

  (** Take the difference between two sets. *)
  val mk_difference : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Take the complement of a set. *)
  val mk_complement : context -> Expr.expr -> Expr.expr

  (** Check for set membership. *)
  val mk_membership : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Check for subsetness of sets. *)
  val mk_subset : context -> Expr.expr -> Expr.expr -> Expr.expr
end

(** Functions to manipulate Finite Domain expressions *)
module FiniteDomain :
sig
  (** Create a new finite domain sort. *)
  val mk_sort : context -> Symbol.symbol -> int -> Sort.sort

  (** Create a new finite domain sort. *)
  val mk_sort_s : context -> string -> int -> Sort.sort

  (** Indicates whether the term is of an array sort. *)
  val is_finite_domain : Expr.expr -> bool

  (** Indicates whether the term is a less than predicate over a finite domain. *)
  val is_lt : Expr.expr -> bool

  (** The size of the finite domain sort. *)
  val get_size : Sort.sort -> int
end


(** Functions to manipulate Relation expressions *)
module Relation :
sig
  (** Indicates whether the term is of a relation sort. *)
  val is_relation : Expr.expr -> bool

  (** Indicates whether the term is an relation store

      Insert a record into a relation.
      The function takes [n+1] arguments, where the first argument is the relation and the remaining [n] elements
      correspond to the [n] columns of the relation. *)
  val is_store : Expr.expr -> bool

  (** Indicates whether the term is an empty relation *)
  val is_empty : Expr.expr -> bool

  (** Indicates whether the term is a test for the emptiness of a relation *)
  val is_is_empty : Expr.expr -> bool

  (** Indicates whether the term is a relational join *)
  val is_join : Expr.expr -> bool

  (** Indicates whether the term is the union or convex hull of two relations.
      The function takes two arguments. *)
  val is_union : Expr.expr -> bool

  (** Indicates whether the term is the widening of two relations
      The function takes two arguments. *)
  val is_widen : Expr.expr -> bool

  (** Indicates whether the term is a projection of columns (provided as numbers in the parameters).
      The function takes one argument. *)
  val is_project : Expr.expr -> bool

  (** Indicates whether the term is a relation filter

      Filter (restrict) a relation with respect to a predicate.
      The first argument is a relation.
      The second argument is a predicate with free de-Bruijn indices
      corresponding to the columns of the relation.
      So the first column in the relation has index 0. *)
  val is_filter : Expr.expr -> bool

  (** Indicates whether the term is an intersection of a relation with the negation of another.

      Intersect the first relation with respect to negation
      of the second relation (the function takes two arguments).
      Logically, the specification can be described by a function

      target = filter_by_negation(pos, neg, columns)

      where columns are pairs c1, d1, .., cN, dN of columns from pos and neg, such that
      target are elements in ( x : expr ) in pos, such that there is no y in neg that agrees with
      ( x : expr ) on the columns c1, d1, .., cN, dN. *)
  val is_negation_filter : Expr.expr -> bool

  (** Indicates whether the term is the renaming of a column in a relation

      The function takes one argument.
      The parameters contain the renaming as a cycle. *)
  val is_rename : Expr.expr -> bool

  (** Indicates whether the term is the complement of a relation *)
  val is_complement : Expr.expr -> bool

  (** Indicates whether the term is a relational select

      Check if a record is an element of the relation.
      The function takes [n+1] arguments, where the first argument is a relation,
      and the remaining [n] arguments correspond to a record. *)
  val is_select : Expr.expr -> bool

  (** Indicates whether the term is a relational clone (copy)

      Create a fresh copy (clone) of a relation.
      The function is logically the identity, but
      in the context of a register machine allows
      for terms of kind {!is_union}
      to perform destructive updates to the first argument. *)
  val is_clone : Expr.expr -> bool

  (** The arity of the relation sort. *)
  val get_arity : Sort.sort -> int

  (** The sorts of the columns of the relation sort. *)
  val get_column_sorts : Sort.sort -> Sort.sort list
end

(** Functions to manipulate Datatype expressions *)
module Datatype :
sig
  (** Datatype Constructors *)
  module Constructor :
  sig
    type constructor

    (** The number of fields of the constructor. *)
    val get_num_fields : constructor -> int

    (** The function declaration of the constructor. *)
    val get_constructor_decl : constructor -> FuncDecl.func_decl

    (** The function declaration of the tester. *)
    val get_tester_decl : constructor -> FuncDecl.func_decl

    (** The function declarations of the accessors *)
    val get_accessor_decls : constructor -> FuncDecl.func_decl list
  end

  (** Create a datatype constructor.
      if the corresponding sort reference is 0, then the value in sort_refs should be an index
      referring to one of the recursive datatypes that is declared. *)
  val mk_constructor : context -> Symbol.symbol -> Symbol.symbol -> Symbol.symbol list -> Sort.sort option list -> int list -> Constructor.constructor

  (** Create a datatype constructor.
      if the corresponding sort reference is 0, then the value in sort_refs should be an index
      referring to one of the recursive datatypes that is declared. *)
  val mk_constructor_s : context -> string -> Symbol.symbol -> Symbol.symbol list -> Sort.sort option list -> int list -> Constructor.constructor

  (** Create a new datatype sort. *)
  val mk_sort : context -> Symbol.symbol -> Constructor.constructor list -> Sort.sort

  (** Create a new datatype sort. *)
  val mk_sort_s : context -> string -> Constructor.constructor list -> Sort.sort

  (** Create mutually recursive datatypes. *)
  val mk_sorts : context -> Symbol.symbol list -> Constructor.constructor list list -> Sort.sort list

  (** Create mutually recursive data-types. *)
  val mk_sorts_s : context -> string list -> Constructor.constructor list list -> Sort.sort list

  (** The number of constructors of the datatype sort. *)
  val get_num_constructors : Sort.sort -> int

  (** The constructors. *)
  val get_constructors : Sort.sort -> FuncDecl.func_decl list

  (** The recognizers. *)
  val get_recognizers : Sort.sort -> FuncDecl.func_decl list

  (** The constructor accessors. *)
  val get_accessors : Sort.sort -> FuncDecl.func_decl list list
end

(** Functions to manipulate Enumeration expressions *)
module Enumeration :
sig
  (** Create a new enumeration sort. *)
  val mk_sort : context -> Symbol.symbol -> Symbol.symbol list -> Sort.sort

  (** Create a new enumeration sort. *)
  val mk_sort_s : context -> string -> string list -> Sort.sort

  (** The function declarations of the constants in the enumeration. *)
  val get_const_decls : Sort.sort -> FuncDecl.func_decl list

  (** Retrieves the inx'th constant declaration in the enumeration. *)
  val get_const_decl : Sort.sort -> int -> FuncDecl.func_decl

  (** The constants in the enumeration. *)
  val get_consts : Sort.sort -> Expr.expr list

  (** Retrieves the inx'th constant in the enumeration. *)
  val get_const : Sort.sort -> int -> Expr.expr

  (** The test predicates for the constants in the enumeration. *)
  val get_tester_decls : Sort.sort -> FuncDecl.func_decl list

  (** Retrieves the inx'th tester/recognizer declaration in the enumeration. *)
  val get_tester_decl : Sort.sort -> int -> FuncDecl.func_decl
end

(** Functions to manipulate List expressions *)
module Z3List :
sig
  (** Create a new list sort. *)
  val mk_sort : context -> Symbol.symbol -> Sort.sort -> Sort.sort

  (** Create a new list sort. *)
  val mk_list_s : context -> string -> Sort.sort -> Sort.sort

  (** The declaration of the nil function of this list sort. *)
  val get_nil_decl : Sort.sort -> FuncDecl.func_decl

  (** The declaration of the isNil function of this list sort. *)
  val get_is_nil_decl : Sort.sort -> FuncDecl.func_decl

  (** The declaration of the cons function of this list sort. *)
  val get_cons_decl : Sort.sort -> FuncDecl.func_decl

  (** The declaration of the isCons function of this list sort. *)
  val get_is_cons_decl : Sort.sort -> FuncDecl.func_decl

  (** The declaration of the head function of this list sort. *)
  val get_head_decl : Sort.sort -> FuncDecl.func_decl

  (** The declaration of the tail function of this list sort. *)
  val get_tail_decl : Sort.sort -> FuncDecl.func_decl

  (** The empty list. *)
  val nil : Sort.sort -> Expr.expr
end

(** Functions to manipulate Tuple expressions *)
module Tuple :
sig
  (** Create a new tuple sort. *)
  val mk_sort : context -> Symbol.symbol -> Symbol.symbol list -> Sort.sort list -> Sort.sort

  (**  The constructor function of the tuple. *)
  val get_mk_decl : Sort.sort -> FuncDecl.func_decl

  (** The number of fields in the tuple. *)
  val get_num_fields : Sort.sort -> int

  (** The field declarations. *)
  val get_field_decls : Sort.sort -> FuncDecl.func_decl list
end

(** Functions to manipulate arithmetic expressions *)
module Arithmetic :
sig
  (** Integer Arithmetic *)
  module Integer :
  sig
    (** Create a new integer sort. *)
    val mk_sort : context -> Sort.sort

    (** Get a big_int from an integer numeral *)
    val get_big_int : Expr.expr -> Z.t

    (** Returns a string representation of a numeral. *)
    val numeral_to_string : Expr.expr -> string

    (** Creates an integer constant. *)
    val mk_const : context -> Symbol.symbol -> Expr.expr

    (** Creates an integer constant. *)
    val mk_const_s : context -> string -> Expr.expr

    (** Create an expression representing [t1 mod t2].
        The arguments must have int type. *)
    val mk_mod : context -> Expr.expr -> Expr.expr -> Expr.expr

    (** Create an expression representing [t1 rem t2].
        The arguments must have int type. *)
    val mk_rem : context -> Expr.expr -> Expr.expr -> Expr.expr

    (** Create an integer numeral. *)
    val mk_numeral_s : context -> string -> Expr.expr

    (** Create an integer numeral.
        @return A Term with the given value and sort Integer *)
    val mk_numeral_i : context -> int -> Expr.expr

    (** Coerce an integer to a real.

        There is also a converse operation exposed. It follows the semantics prescribed by the SMT-LIB standard.

        You can take the floor of a real by creating an auxiliary integer Term [k] and
        and asserting [MakeInt2Real(k) <= t1 < MkInt2Real(k)+1].
        The argument must be of integer sort. *)
    val mk_int2real : context -> Expr.expr -> Expr.expr

    (**   Create an n-bit bit-vector from an integer argument.

          NB. This function is essentially treated as uninterpreted.
          So you cannot expect Z3 to precisely reflect the semantics of this function
          when solving constraints with this function.

          The argument must be of integer sort. *)
    val mk_int2bv : context -> int -> Expr.expr -> Expr.expr
  end

  (** Real Arithmetic *)
  module Real :
  sig
    (** Create a real sort. *)
    val mk_sort : context -> Sort.sort

    (** The numerator of a rational numeral. *)
    val get_numerator : Expr.expr -> Expr.expr

    (** The denominator of a rational numeral. *)
    val get_denominator : Expr.expr -> Expr.expr

    (** Get a ratio from a real numeral *)
    val get_ratio : Expr.expr -> Q.t

    (** Returns a string representation in decimal notation.
        The result has at most as many decimal places as indicated by the int argument.*)
    val to_decimal_string : Expr.expr-> int -> string

    (** Returns a string representation of a numeral. *)
    val numeral_to_string : Expr.expr-> string

    (** Creates a real constant. *)
    val mk_const : context -> Symbol.symbol -> Expr.expr

    (** Creates a real constant. *)
    val mk_const_s : context -> string -> Expr.expr

    (** Create a real numeral from a fraction.
        @return A Term with rational value and sort Real
        {!mk_numeral_s} *)
    val mk_numeral_nd : context -> int -> int -> Expr.expr

    (** Create a real numeral.
        @return A Term with the given value and sort Real *)
    val mk_numeral_s : context -> string -> Expr.expr

    (** Create a real numeral.
        @return A Term with the given value and sort Real *)
    val mk_numeral_i : context -> int -> Expr.expr

    (** Creates an expression that checks whether a real number is an integer. *)
    val mk_is_integer : context -> Expr.expr -> Expr.expr

    (** Coerce a real to an integer.

        The semantics of this function follows the SMT-LIB standard for the function to_int.
        The argument must be of real sort. *)
    val mk_real2int : context -> Expr.expr -> Expr.expr

    (** Algebraic Numbers *)
    module AlgebraicNumber :
    sig
      (** Return a upper bound for a given real algebraic number.
          The interval isolating the number is smaller than 1/10^precision.
          {!is_algebraic_number}
          @return A numeral Expr of sort Real *)
      val to_upper : Expr.expr -> int -> Expr.expr

      (** Return a lower bound for the given real algebraic number.
          The interval isolating the number is smaller than 1/10^precision.
          {!is_algebraic_number}
          @return A numeral Expr of sort Real *)
      val to_lower : Expr.expr -> int -> Expr.expr

      (** Returns a string representation in decimal notation.
          The result has at most as many decimal places as the int argument provided.*)
      val to_decimal_string : Expr.expr -> int -> string

      (** Returns a string representation of a numeral. *)
      val numeral_to_string : Expr.expr -> string
    end
  end

  (** Indicates whether the term is of integer sort. *)
  val is_int : Expr.expr -> bool

  (** Indicates whether the term is an arithmetic numeral. *)
  val is_arithmetic_numeral : Expr.expr -> bool

  (** Indicates whether the term is a less-than-or-equal *)
  val is_le : Expr.expr -> bool

  (** Indicates whether the term is a greater-than-or-equal *)
  val is_ge : Expr.expr -> bool

  (** Indicates whether the term is a less-than *)
  val is_lt : Expr.expr -> bool

  (** Indicates whether the term is a greater-than *)
  val is_gt : Expr.expr -> bool

  (** Indicates whether the term is addition (binary) *)
  val is_add : Expr.expr -> bool

  (** Indicates whether the term is subtraction (binary) *)
  val is_sub : Expr.expr -> bool

  (** Indicates whether the term is a unary minus *)
  val is_uminus : Expr.expr -> bool

  (** Indicates whether the term is multiplication (binary) *)
  val is_mul : Expr.expr -> bool

  (** Indicates whether the term is division (binary) *)
  val is_div : Expr.expr -> bool

  (** Indicates whether the term is integer division (binary) *)
  val is_idiv : Expr.expr -> bool

  (** Indicates whether the term is remainder (binary) *)
  val is_remainder : Expr.expr -> bool

  (** Indicates whether the term is modulus (binary) *)
  val is_modulus : Expr.expr -> bool

  (** Indicates whether the term is a coercion of integer to real (unary) *)
  val is_int2real : Expr.expr -> bool

  (** Indicates whether the term is a coercion of real to integer (unary) *)
  val is_real2int : Expr.expr -> bool

  (** Indicates whether the term is a check that tests whether a real is integral (unary) *)
  val is_real_is_int : Expr.expr -> bool

  (** Indicates whether the term is of sort real. *)
  val is_real : Expr.expr -> bool

  (** Indicates whether the term is an integer numeral. *)
  val is_int_numeral : Expr.expr -> bool

  (** Indicates whether the term is a real numeral. *)
  val is_rat_numeral : Expr.expr -> bool

  (** Indicates whether the term is an algebraic number *)
  val is_algebraic_number : Expr.expr -> bool

  (** Create an expression representing [t[0] + t[1] + ...]. *)
  val mk_add : context -> Expr.expr list -> Expr.expr

  (** Create an expression representing [t[0] * t[1] * ...]. *)
  val mk_mul : context -> Expr.expr list -> Expr.expr

  (** Create an expression representing [t[0] - t[1] - ...]. *)
  val mk_sub : context -> Expr.expr list -> Expr.expr

  (** Create an expression representing [-t]. *)
  val mk_unary_minus : context -> Expr.expr -> Expr.expr

  (** Create an expression representing [t1 / t2]. *)
  val mk_div : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create an expression representing [t1 ^ t2]. *)
  val mk_power : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create an expression representing [t1 < t2] *)
  val mk_lt : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create an expression representing [t1 <= t2] *)
  val mk_le : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create an expression representing [t1 > t2] *)
  val mk_gt : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create an expression representing [t1 >= t2] *)
  val mk_ge : context -> Expr.expr -> Expr.expr -> Expr.expr
end

(** Functions to manipulate bit-vector expressions *)
module BitVector :
sig
  (** Create a new bit-vector sort. *)
  val mk_sort : context -> int -> Sort.sort

  (** Indicates whether the terms is of bit-vector sort. *)
  val is_bv : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector numeral *)
  val is_bv_numeral : Expr.expr -> bool

  (** Indicates whether the term is a one-bit bit-vector with value one *)
  val is_bv_bit1 : Expr.expr -> bool

  (** Indicates whether the term is a one-bit bit-vector with value zero *)
  val is_bv_bit0 : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector unary minus *)
  val is_bv_uminus : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector addition (binary) *)
  val is_bv_add : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector subtraction (binary) *)
  val is_bv_sub : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector multiplication (binary) *)
  val is_bv_mul : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector signed division (binary) *)
  val is_bv_sdiv : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector unsigned division (binary) *)
  val is_bv_udiv : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector signed remainder (binary) *)
  val is_bv_SRem : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector unsigned remainder (binary) *)
  val is_bv_urem : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector signed modulus *)
  val is_bv_smod : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector signed division by zero *)
  val is_bv_sdiv0 : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector unsigned division by zero *)
  val is_bv_udiv0 : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector signed remainder by zero *)
  val is_bv_srem0 : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector unsigned remainder by zero *)
  val is_bv_urem0 : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector signed modulus by zero *)
  val is_bv_smod0 : Expr.expr -> bool

  (** Indicates whether the term is an unsigned bit-vector less-than-or-equal *)
  val is_bv_ule : Expr.expr -> bool

  (** Indicates whether the term is a signed bit-vector less-than-or-equal *)
  val is_bv_sle : Expr.expr -> bool

  (** Indicates whether the term is an unsigned bit-vector greater-than-or-equal *)
  val is_bv_uge : Expr.expr -> bool

  (** Indicates whether the term is a signed bit-vector greater-than-or-equal *)
  val is_bv_sge : Expr.expr -> bool

  (** Indicates whether the term is an unsigned bit-vector less-than *)
  val is_bv_ult : Expr.expr -> bool

  (** Indicates whether the term is a signed bit-vector less-than *)
  val is_bv_slt : Expr.expr -> bool

  (** Indicates whether the term is an unsigned bit-vector greater-than *)
  val is_bv_ugt : Expr.expr -> bool

  (** Indicates whether the term is a signed bit-vector greater-than *)
  val is_bv_sgt : Expr.expr -> bool

  (** Indicates whether the term is a bit-wise AND *)
  val is_bv_and : Expr.expr -> bool

  (** Indicates whether the term is a bit-wise OR *)
  val is_bv_or : Expr.expr -> bool

  (** Indicates whether the term is a bit-wise NOT *)
  val is_bv_not : Expr.expr -> bool

  (** Indicates whether the term is a bit-wise XOR *)
  val is_bv_xor : Expr.expr -> bool

  (** Indicates whether the term is a bit-wise NAND *)
  val is_bv_nand : Expr.expr -> bool

  (** Indicates whether the term is a bit-wise NOR *)
  val is_bv_nor : Expr.expr -> bool

  (** Indicates whether the term is a bit-wise XNOR *)
  val is_bv_xnor : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector concatenation (binary) *)
  val is_bv_concat : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector sign extension *)
  val is_bv_signextension : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector zero extension *)
  val is_bv_zeroextension : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector extraction *)
  val is_bv_extract : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector repetition *)
  val is_bv_repeat : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector reduce OR *)
  val is_bv_reduceor : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector reduce AND *)
  val is_bv_reduceand : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector comparison *)
  val is_bv_comp : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector shift left *)
  val is_bv_shiftleft : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector logical shift right *)
  val is_bv_shiftrightlogical : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector arithmetic shift left *)
  val is_bv_shiftrightarithmetic : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector rotate left *)
  val is_bv_rotateleft : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector rotate right *)
  val is_bv_rotateright : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector rotate left (extended)
      Similar to Z3_OP_ROTATE_LEFT, but it is a binary operator instead of a parametric one. *)
  val is_bv_rotateleftextended : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector rotate right (extended)
      Similar to Z3_OP_ROTATE_RIGHT, but it is a binary operator instead of a parametric one. *)
  val is_bv_rotaterightextended : Expr.expr -> bool

  (** Indicates whether the term is a coercion from bit-vector to integer
      This function is not supported by the decision procedures. Only the most
      rudimentary simplification rules are applied to this function. *)
  val is_int2bv : Expr.expr -> bool

  (** Indicates whether the term is a coercion from integer to bit-vector
      This function is not supported by the decision procedures. Only the most
      rudimentary simplification rules are applied to this function. *)
  val is_bv2int : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector carry
      Compute the carry bit in a full-adder.  The meaning is given by the
      equivalence (carry l1 l2 l3) <=> (or (and l1 l2) (and l1 l3) (and l2 l3))) *)
  val is_bv_carry : Expr.expr -> bool

  (** Indicates whether the term is a bit-vector ternary XOR
      The meaning is given by the equivalence (xor3 l1 l2 l3) <=> (xor (xor l1 l2) l3) *)
  val is_bv_xor3 : Expr.expr -> bool

  (** The size of a bit-vector sort. *)
  val get_size : Sort.sort -> int

  (** Returns a string representation of a numeral. *)
  val numeral_to_string : Expr.expr -> string

  (** Creates a bit-vector constant. *)
  val mk_const : context -> Symbol.symbol -> int -> Expr.expr

  (** Creates a bit-vector constant. *)
  val mk_const_s : context -> string -> int -> Expr.expr

  (** Bitwise negation.
      The argument must have a bit-vector sort. *)
  val mk_not : context -> Expr.expr -> Expr.expr

  (** Take conjunction of bits in a vector,vector of length 1.
      The argument must have a bit-vector sort. *)
  val mk_redand : context -> Expr.expr -> Expr.expr

  (** Take disjunction of bits in a vector,vector of length 1.
      The argument must have a bit-vector sort. *)
  val mk_redor : context -> Expr.expr -> Expr.expr

  (** Bitwise conjunction.
      The arguments must have a bit-vector sort. *)
  val mk_and : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Bitwise disjunction.
      The arguments must have a bit-vector sort. *)
  val mk_or : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Bitwise XOR.
      The arguments must have a bit-vector sort. *)
  val mk_xor : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Bitwise NAND.
      The arguments must have a bit-vector sort. *)
  val mk_nand : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Bitwise NOR.
      The arguments must have a bit-vector sort. *)
  val mk_nor : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Bitwise XNOR.
      The arguments must have a bit-vector sort. *)
  val mk_xnor : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Standard two's complement unary minus.
      The arguments must have a bit-vector sort. *)
  val mk_neg : context -> Expr.expr -> Expr.expr

  (** Two's complement addition.
      The arguments must have the same bit-vector sort. *)
  val mk_add : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Two's complement subtraction.
      The arguments must have the same bit-vector sort. *)
  val mk_sub : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Two's complement multiplication.
      The arguments must have the same bit-vector sort. *)
  val mk_mul : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Unsigned division.

      It is defined as the floor of [t1/t2] if \c t2 is
      different from zero. If [t2] is zero, then the result
      is undefined.
      The arguments must have the same bit-vector sort. *)
  val mk_udiv : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Signed division.

      It is defined in the following way:

      - The \c floor of [t1/t2] if \c t2 is different from zero, and [t1*t2 >= 0].

      - The \c ceiling of [t1/t2] if \c t2 is different from zero, and [t1*t2 < 0].

      If [t2] is zero, then the result is undefined.
      The arguments must have the same bit-vector sort. *)
  val mk_sdiv : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Unsigned remainder.

      It is defined as [t1 - (t1 /u t2) * t2], where [/u] represents unsigned division.
      If [t2] is zero, then the result is undefined.
      The arguments must have the same bit-vector sort. *)
  val mk_urem : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Signed remainder.

      It is defined as [t1 - (t1 /s t2) * t2], where [/s] represents signed division.
      The most significant bit (sign) of the result is equal to the most significant bit of \c t1.

      If [t2] is zero, then the result is undefined.
      The arguments must have the same bit-vector sort. *)
  val mk_srem : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Two's complement signed remainder (sign follows divisor).

      If [t2] is zero, then the result is undefined.
      The arguments must have the same bit-vector sort. *)
  val mk_smod : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Unsigned less-than

      The arguments must have the same bit-vector sort. *)
  val mk_ult : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Two's complement signed less-than

      The arguments must have the same bit-vector sort. *)
  val mk_slt : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Unsigned less-than or equal to.

      The arguments must have the same bit-vector sort. *)
  val mk_ule : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Two's complement signed less-than or equal to.

      The arguments must have the same bit-vector sort. *)
  val mk_sle : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Unsigned greater than or equal to.

      The arguments must have the same bit-vector sort. *)
  val mk_uge : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Two's complement signed greater than or equal to.

      The arguments must have the same bit-vector sort. *)
  val mk_sge : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Unsigned greater-than.

      The arguments must have the same bit-vector sort. *)
  val mk_ugt : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Two's complement signed greater-than.

      The arguments must have the same bit-vector sort. *)
  val mk_sgt : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Bit-vector concatenation.

      The arguments must have a bit-vector sort.
      @return
      The result is a bit-vector of size [n1+n2], where [n1] ([n2])
      is the size of [t1] ([t2]). *)
  val mk_concat : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Bit-vector extraction.

      Extract the bits between two limits from a bitvector of
      size [m] to yield a new bitvector of size [n], where
      [n = high - low + 1]. *)
  val mk_extract : context -> int -> int -> Expr.expr -> Expr.expr

  (** Bit-vector sign extension.

      Sign-extends the given bit-vector to the (signed) equivalent bitvector of
      size [m+i], where \c m is the size of the given bit-vector. *)
  val mk_sign_ext : context -> int -> Expr.expr -> Expr.expr

  (** Bit-vector zero extension.

      Extend the given bit-vector with zeros to the (unsigned) equivalent
      bitvector of size [m+i], where \c m is the size of the
      given bit-vector. *)
  val mk_zero_ext : context -> int -> Expr.expr -> Expr.expr

  (** Bit-vector repetition. *)
  val mk_repeat : context -> int -> Expr.expr -> Expr.expr

  (** Shift left.

      It is equivalent to multiplication by [2^x] where \c x is the value of third argument.

      NB. The semantics of shift operations varies between environments. This
      definition does not necessarily capture directly the semantics of the
      programming language or assembly architecture you are modeling.*)
  val mk_shl : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Logical shift right

      It is equivalent to unsigned division by [2^x] where \c x is the value of the third argument.

      NB. The semantics of shift operations varies between environments. This
      definition does not necessarily capture directly the semantics of the
      programming language or assembly architecture you are modeling.

      The arguments must have a bit-vector sort. *)
  val mk_lshr : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Arithmetic shift right

      It is like logical shift right except that the most significant
      bits of the result always copy the most significant bit of the
      second argument.

      NB. The semantics of shift operations varies between environments. This
      definition does not necessarily capture directly the semantics of the
      programming language or assembly architecture you are modeling.

      The arguments must have a bit-vector sort. *)
  val mk_ashr : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Rotate Left.
      Rotate bits of \c t to the left \c i times. *)
  val mk_rotate_left : context -> int -> Expr.expr -> Expr.expr

  (** Rotate Right.
      Rotate bits of \c t to the right \c i times.*)
  val mk_rotate_right : context -> int -> Expr.expr -> Expr.expr

  (** Rotate Left.
      Rotate bits of the second argument to the left.*)
  val mk_ext_rotate_left : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Rotate Right.
      Rotate bits of the second argument to the right. *)
  val mk_ext_rotate_right : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create an integer from the bit-vector argument

      If \c is_signed is false, then the bit-vector \c t1 is treated as unsigned.
      So the result is non-negative and in the range [[0..2^N-1]], where
      N are the number of bits in the argument.
      If \c is_signed is true, \c t1 is treated as a signed bit-vector.

      NB. This function is essentially treated as uninterpreted.
      So you cannot expect Z3 to precisely reflect the semantics of this function
      when solving constraints with this function.*)
  val mk_bv2int : context -> Expr.expr -> bool -> Expr.expr

  (** Create a predicate that checks that the bit-wise addition does not overflow.

      The arguments must be of bit-vector sort. *)
  val mk_add_no_overflow : context -> Expr.expr -> Expr.expr -> bool -> Expr.expr

  (** Create a predicate that checks that the bit-wise addition does not underflow.

      The arguments must be of bit-vector sort. *)
  val mk_add_no_underflow : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create a predicate that checks that the bit-wise subtraction does not overflow.

      The arguments must be of bit-vector sort. *)
  val mk_sub_no_overflow : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create a predicate that checks that the bit-wise subtraction does not underflow.

      The arguments must be of bit-vector sort. *)
  val mk_sub_no_underflow : context -> Expr.expr -> Expr.expr -> bool -> Expr.expr

  (** Create a predicate that checks that the bit-wise signed division does not overflow.

      The arguments must be of bit-vector sort. *)
  val mk_sdiv_no_overflow : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create a predicate that checks that the bit-wise negation does not overflow.

      The arguments must be of bit-vector sort. *)
  val mk_neg_no_overflow : context -> Expr.expr -> Expr.expr

  (** Create a predicate that checks that the bit-wise multiplication does not overflow.

      The arguments must be of bit-vector sort. *)
  val mk_mul_no_overflow : context -> Expr.expr -> Expr.expr -> bool -> Expr.expr

  (** Create a predicate that checks that the bit-wise multiplication does not underflow.

      The arguments must be of bit-vector sort. *)
  val mk_mul_no_underflow : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create a bit-vector numeral. *)
  val mk_numeral : context -> string -> int -> Expr.expr
end

(** Sequences, Strings and Regular Expressions **)
module Seq : 
sig
  (* create a sequence sort *)
  val mk_seq_sort : context -> Sort.sort -> Sort.sort

  (* test if sort is a sequence sort *)
  val is_seq_sort : context -> Sort.sort -> bool

  (* create regular expression sorts over sequences of the argument sort *)   
  val mk_re_sort : context -> Sort.sort -> Sort.sort

  (* test if sort is a regular expression sort *)
  val is_re_sort : context -> Sort.sort -> bool

  (* create string sort *)
  val mk_string_sort : context -> Sort.sort

  (* test if sort is a string sort (a sequence of 8-bit bit-vectors) *)
  val is_string_sort : context -> Sort.sort -> bool 

  (* create a string literal *)
  val mk_string : context -> string -> Expr.expr

  (* test if expression is a string *)
  val is_string : context -> Expr.expr -> bool 

  (* retrieve string from string Expr.expr *)
  val get_string : context -> Expr.expr -> string 

  (* the empty sequence over base sort *)
  val mk_seq_empty : context -> Sort.sort -> Expr.expr 

  (* a unit sequence *)
  val mk_seq_unit : context -> Expr.expr -> Expr.expr 

  (* sequence concatenation *)
  val mk_seq_concat : context -> Expr.expr list -> Expr.expr 

  (* predicate if the first argument is a prefix of the second *)
  val mk_seq_prefix : context -> Expr.expr -> Expr.expr -> Expr.expr  

  (* predicate if the first argument is a suffix of the second *)
  val mk_seq_suffix : context -> Expr.expr -> Expr.expr -> Expr.expr  

  (* predicate if the first argument contains the second *)
  val mk_seq_contains : context -> Expr.expr -> Expr.expr -> Expr.expr  

  (* extract sub-sequence starting at index given by second argument and of length provided by third argument *)
  val mk_seq_extract : context -> Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr  

  (* replace first occurrence of second argument by third *)
  val mk_seq_replace : context -> Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr  

  (* a unit sequence at index provided by second argument *)
  val mk_seq_at : context -> Expr.expr -> Expr.expr -> Expr.expr 

  (* length of a sequence *)
  val mk_seq_length : context -> Expr.expr -> Expr.expr  

  (* index of the first occurrence of the second argument in the first *)
  val mk_seq_index : context -> Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr 

  (* retrieve integer expression encoded in string *)
  val mk_str_to_int : context -> Expr.expr -> Expr.expr

  (* convert an integer expression to a string *)
  val mk_int_to_str : context -> Expr.expr -> Expr.expr 

  (* create regular expression that accepts the argument sequence *)
  val mk_seq_to_re : context -> Expr.expr -> Expr.expr 

  (* regular expression membership predicate *)
  val mk_seq_in_re : context -> Expr.expr -> Expr.expr -> Expr.expr 

  (* regular expression plus *)
  val mk_re_plus : context -> Expr.expr -> Expr.expr 

  (* regular expression star *)
  val mk_re_star : context -> Expr.expr -> Expr.expr 

  (* optional regular expression *)
  val mk_re_option : context -> Expr.expr -> Expr.expr 

  (* union of regular expressions *)
  val mk_re_union : context -> Expr.expr list -> Expr.expr 

  (* concatenation of regular expressions *)
  val mk_re_concat : context -> Expr.expr list -> Expr.expr 
  
  (* regular expression for the range between two characters *)
  val mk_re_range : context -> Expr.expr -> Expr.expr -> Expr.expr 

  (* bounded loop regular expression *)
  val mk_re_loop : context -> Expr.expr -> int -> int -> Expr.expr 
  
  (* intersection of regular expressions *)
  val mk_re_intersect : context -> int -> Expr.expr list -> Expr.expr

  (* the regular expression complement *)
  val mk_re_complement : context -> Expr.expr -> Expr.expr 

  (* the regular expression that accepts no sequences *)
  val mk_re_empty : context -> Sort.sort -> Expr.expr 

  (* the regular expression that accepts all sequences *)
  val mk_re_full : context -> Sort.sort -> Expr.expr 

end

(** Floating-Point Arithmetic *)
module FloatingPoint :
sig

  (** Rounding Modes *)
  module RoundingMode :
  sig
    (** Create the RoundingMode sort. *)
    val mk_sort : context -> Sort.sort

    (** Indicates whether the terms is of floating-point rounding mode sort. *)
    val is_fprm : Expr.expr -> bool

    (** Create a numeral of RoundingMode sort which represents the NearestTiesToEven rounding mode. *)
    val mk_round_nearest_ties_to_even : context -> Expr.expr

    (** Create a numeral of RoundingMode sort which represents the NearestTiesToEven rounding mode. *)
    val mk_rne : context -> Expr.expr

    (** Create a numeral of RoundingMode sort which represents the NearestTiesToAway rounding mode. *)
    val mk_round_nearest_ties_to_away : context -> Expr.expr

    (** Create a numeral of RoundingMode sort which represents the NearestTiesToAway rounding mode. *)
    val mk_rna : context -> Expr.expr

    (** Create a numeral of RoundingMode sort which represents the TowardPositive rounding mode. *)
    val mk_round_toward_positive : context -> Expr.expr

    (** Create a numeral of RoundingMode sort which represents the TowardPositive rounding mode. *)
    val mk_rtp : context -> Expr.expr

    (** Create a numeral of RoundingMode sort which represents the TowardNegative rounding mode. *)
    val mk_round_toward_negative : context -> Expr.expr

    (** Create a numeral of RoundingMode sort which represents the TowardNegative rounding mode. *)
    val mk_rtn : context -> Expr.expr

    (** Create a numeral of RoundingMode sort which represents the TowardZero rounding mode. *)
    val mk_round_toward_zero : context -> Expr.expr

    (** Create a numeral of RoundingMode sort which represents the TowardZero rounding mode. *)
    val mk_rtz : context -> Expr.expr
  end

  (** Create a FloatingPoint sort. *)
  val mk_sort : context -> int -> int -> Sort.sort

  (** Create the half-precision (16-bit) FloatingPoint sort.*)
  val mk_sort_half : context -> Sort.sort

  (** Create the half-precision (16-bit) FloatingPoint sort. *)
  val mk_sort_16 : context -> Sort.sort

  (** Create the single-precision (32-bit) FloatingPoint sort.*)
  val mk_sort_single : context -> Sort.sort

  (** Create the single-precision (32-bit) FloatingPoint sort. *)
  val mk_sort_32 : context -> Sort.sort

  (** Create the double-precision (64-bit) FloatingPoint sort. *)
  val mk_sort_double : context -> Sort.sort

  (** Create the double-precision (64-bit) FloatingPoint sort. *)
  val mk_sort_64 : context -> Sort.sort

  (** Create the quadruple-precision (128-bit) FloatingPoint sort. *)
  val mk_sort_quadruple : context -> Sort.sort

  (** Create the quadruple-precision (128-bit) FloatingPoint sort. *)
  val mk_sort_128 : context -> Sort.sort

  (** Create a floating-point NaN of a given FloatingPoint sort. *)
  val mk_nan : context -> Sort.sort -> Expr.expr

  (** Create a floating-point infinity of a given FloatingPoint sort. *)
  val mk_inf : context -> Sort.sort -> bool -> Expr.expr

  (** Create a floating-point zero of a given FloatingPoint sort. *)
  val mk_zero : context -> Sort.sort -> bool -> Expr.expr

  (** Create an expression of FloatingPoint sort from three bit-vector expressions.

      This is the operator named `fp' in the SMT FP theory definition.
      Note that \c sign is required to be a bit-vector of size 1. Significand and exponent
      are required to be greater than 1 and 2 respectively. The FloatingPoint sort
      of the resulting expression is automatically determined from the bit-vector sizes
      of the arguments. *)
  val mk_fp : context -> Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr

  (** Create a numeral of FloatingPoint sort from a float.

      This function is used to create numerals that fit in a float value.
      It is slightly faster than #Z3_mk_numeral since it is not necessary to parse a string. *)
  val mk_numeral_f : context -> float -> Sort.sort -> Expr.expr

  (** Create a numeral of FloatingPoint sort from a signed integer. *)
  val mk_numeral_i : context -> int -> Sort.sort -> Expr.expr

  (** Create a numeral of FloatingPoint sort from a sign bit and two integers. *)
  val mk_numeral_i_u : context -> bool -> int -> int -> Sort.sort -> Expr.expr

  (** Create a numeral of FloatingPoint sort from a string *)
  val mk_numeral_s : context -> string -> Sort.sort -> Expr.expr

  (** Indicates whether the terms is of floating-point sort. *)
  val is_fp : Expr.expr -> bool


  (** Indicates whether an expression is a floating-point abs expression *)
  val is_abs : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point neg expression *)
  val is_neg : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point add expression *)
  val is_add : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point sub expression *)
  val is_sub : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point mul expression *)
  val is_mul : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point div expression *)
  val is_div : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point fma expression *)
  val is_fma : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point sqrt expression *)
  val is_sqrt : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point rem expression *)
  val is_rem : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point round_to_integral expression *)
  val is_round_to_integral : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point min expression *)
  val is_min : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point max expression *)
  val is_max : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point leq expression *)
  val is_leq : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point lt expression *)
  val is_lt : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point geq expression *)
  val is_geq : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point gt expression *)
  val is_gt : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point eq expression *)
  val is_eq : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point is_normal expression *)
  val is_is_normal : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point is_subnormal expression *)
  val is_is_subnormal : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point is_zero expression *)
  val is_is_zero : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point is_infinite expression *)
  val is_is_infinite : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point is_nan expression *)
  val is_is_nan : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point is_negative expression *)
  val is_is_negative : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point is_positive expression *)
  val is_is_positive : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point to_fp expression *)
  val is_to_fp : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point to_fp_unsigned expression *)
  val is_to_fp_unsigned : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point to_ubv expression *)
  val is_to_ubv : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point to_sbv expression *)
  val is_to_sbv : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point to_real expression *)
  val is_to_real : Expr.expr -> bool

  (** Indicates whether an expression is a floating-point to_ieee_bv expression *)
  val is_to_ieee_bv : Expr.expr -> bool


  (** Returns a string representation of a numeral. *)
  val numeral_to_string : Expr.expr -> string

  (** Creates a floating-point constant. *)
  val mk_const : context -> Symbol.symbol -> Sort.sort -> Expr.expr

  (** Creates a floating-point constant. *)
  val mk_const_s : context -> string -> Sort.sort -> Expr.expr

  (** Floating-point absolute value *)
  val mk_abs : context -> Expr.expr -> Expr.expr

  (** Floating-point negation *)
  val mk_neg : context -> Expr.expr -> Expr.expr

  (** Floating-point addition *)
  val mk_add : context -> Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr

  (** Floating-point subtraction *)
  val mk_sub : context -> Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr

  (** Floating-point multiplication *)
  val mk_mul : context -> Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr

  (** Floating-point division *)
  val mk_div : context -> Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr

  (** Floating-point fused multiply-add. *)
  val mk_fma : context -> Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr

  (** Floating-point square root *)
  val mk_sqrt : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Floating-point remainder *)
  val mk_rem : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Floating-point roundToIntegral.

      Rounds a floating-point number to the closest integer,
      again represented as a floating-point number. *)
  val mk_round_to_integral : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Minimum of floating-point numbers. *)
  val mk_min : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Maximum of floating-point numbers. *)
  val mk_max : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Floating-point less than or equal. *)
  val mk_leq : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Floating-point less than. *)
  val mk_lt : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Floating-point greater than or equal. *)
  val mk_geq : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Floating-point greater than. *)
  val mk_gt : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Floating-point equality. *)
  val mk_eq : context -> Expr.expr -> Expr.expr -> Expr.expr

  (** Predicate indicating whether t is a normal floating-point number. *)
  val mk_is_normal : context -> Expr.expr -> Expr.expr

  (** Predicate indicating whether t is a subnormal floating-point number. *)
  val mk_is_subnormal : context -> Expr.expr -> Expr.expr

  (** Predicate indicating whether t is a floating-point number with zero value, i.e., +zero or -zero. *)
  val mk_is_zero : context -> Expr.expr -> Expr.expr

  (** Predicate indicating whether t is a floating-point number representing +oo or -oo. *)
  val mk_is_infinite : context -> Expr.expr -> Expr.expr

  (** Predicate indicating whether t is a NaN. *)
  val mk_is_nan : context -> Expr.expr -> Expr.expr

  (** Predicate indicating whether t is a negative floating-point number. *)
  val mk_is_negative : context -> Expr.expr -> Expr.expr

  (** Predicate indicating whether t is a positive floating-point number. *)
  val mk_is_positive : context -> Expr.expr -> Expr.expr

  (** Conversion of a single IEEE 754-2008 bit-vector into a floating-point number. *)
  val mk_to_fp_bv : context -> Expr.expr -> Sort.sort -> Expr.expr

  (** Conversion of a FloatingPoint term into another term of different FloatingPoint sort. *)
  val mk_to_fp_float : context -> Expr.expr -> Expr.expr -> Sort.sort -> Expr.expr

  (** Conversion of a term of real sort into a term of FloatingPoint sort. *)
  val mk_to_fp_real : context -> Expr.expr -> Expr.expr -> Sort.sort -> Expr.expr

  (** Conversion of a 2's complement signed bit-vector term into a term of FloatingPoint sort. *)
  val mk_to_fp_signed : context -> Expr.expr -> Expr.expr -> Sort.sort -> Expr.expr

  (** Conversion of a 2's complement unsigned bit-vector term into a term of FloatingPoint sort. *)
  val mk_to_fp_unsigned : context -> Expr.expr -> Expr.expr -> Sort.sort -> Expr.expr

  (** Conversion of a floating-point term into an unsigned bit-vector. *)
  val mk_to_ubv : context -> Expr.expr -> Expr.expr -> int -> Expr.expr

  (** Conversion of a floating-point term into a signed bit-vector. *)
  val mk_to_sbv : context -> Expr.expr -> Expr.expr -> int -> Expr.expr

  (** Conversion of a floating-point term into a real-numbered term. *)
  val mk_to_real : context -> Expr.expr -> Expr.expr

  (** Retrieves the number of bits reserved for the exponent in a FloatingPoint sort. *)
  val get_ebits : context -> Sort.sort -> int

  (** Retrieves the number of bits reserved for the significand in a FloatingPoint sort. *)
  val get_sbits : context -> Sort.sort -> int

  (** Retrieves the sign of a floating-point literal. *)
  val get_numeral_sign : context -> Expr.expr -> bool * int

  (** Return the sign of a floating-point numeral as a bit-vector expression. 
      Remark: NaN's do not have a bit-vector sign, so they are invalid arguments. *)
  val get_numeral_sign_bv : context -> Expr.expr -> Expr.expr

  (** Return the exponent value of a floating-point numeral as a string *)
  val get_numeral_exponent_string : context -> Expr.expr -> bool -> string

  (** Return the exponent value of a floating-point numeral as a signed integer *)
  val get_numeral_exponent_int : context -> Expr.expr -> bool -> bool * int

  (** Return the exponent of a floating-point numeral as a bit-vector expression. 
      Remark: NaN's do not have a bit-vector exponent, so they are invalid arguments. *)
  val get_numeral_exponent_bv : context -> Expr.expr -> bool -> Expr.expr

  (** Return the significand value of a floating-point numeral as a bit-vector expression. 
      Remark: NaN's do not have a bit-vector significand, so they are invalid arguments. *)
  val get_numeral_significand_bv : context -> Expr.expr -> Expr.expr

  (** Return the significand value of a floating-point numeral as a string. *)
  val get_numeral_significand_string : context -> Expr.expr -> string

  (** Return the significand value of a floating-point numeral as a uint64.
      Remark: This function extracts the significand bits, without the
      hidden bit or normalization. Throws an exception if the
      significand does not fit into an int. *)
  val get_numeral_significand_uint : context -> Expr.expr -> bool * int

  (** Indicates whether a floating-point numeral is a NaN. *)
  val is_numeral_nan : context -> Expr.expr -> bool

  (** Indicates whether a floating-point numeral is +oo or -oo. *)
  val is_numeral_inf : context -> Expr.expr -> bool

  (** Indicates whether a floating-point numeral is +zero or -zero. *)
  val is_numeral_zero : context -> Expr.expr -> bool

  (** Indicates whether a floating-point numeral is normal. *)
  val is_numeral_normal : context -> Expr.expr -> bool

  (** Indicates whether a floating-point numeral is subnormal. *)
  val is_numeral_subnormal : context -> Expr.expr -> bool

  (** Indicates whether a floating-point numeral is positive. *)
  val is_numeral_positive : context -> Expr.expr -> bool

  (** Indicates whether a floating-point numeral is negative. *)
  val is_numeral_negative : context -> Expr.expr -> bool
   
  (** Conversion of a floating-point term into a bit-vector term in IEEE 754-2008 format. *)
  val mk_to_ieee_bv : context -> Expr.expr -> Expr.expr

  (** Conversion of a real-sorted significand and an integer-sorted exponent into a term of FloatingPoint sort. *)
  val mk_to_fp_int_real : context -> Expr.expr -> Expr.expr -> Expr.expr -> Sort.sort -> Expr.expr

  (** The string representation of a numeral *)
  val numeral_to_string : Expr.expr -> string
end


(** Functions to manipulate proof expressions *)
module Proof :
sig
  (** Indicates whether the term is a Proof for the expression 'true'. *)
  val is_true : Expr.expr -> bool

  (** Indicates whether the term is a proof for a fact asserted by the user. *)
  val is_asserted : Expr.expr -> bool

  (** Indicates whether the term is a proof for a fact (tagged as goal) asserted by the user. *)
  val is_goal : Expr.expr -> bool

  (** Indicates whether the term is a binary equivalence modulo namings.
      This binary predicate is used in proof terms.
      It captures equisatisfiability and equivalence modulo renamings. *)
  val is_oeq : Expr.expr -> bool

  (** Indicates whether the term is proof via modus ponens

      Given a proof for p and a proof for (implies p q), produces a proof for q.
      T1: p
      T2: (implies p q)
      [mp T1 T2]: q
      The second antecedents may also be a proof for (iff p q). *)
  val is_modus_ponens : Expr.expr -> bool

  (** Indicates whether the term is a proof for (R t t), where R is a reflexive relation.
      This proof object has no antecedents.
      The only reflexive relations that are used are
      equivalence modulo namings, equality and equivalence.
      That is, R is either '~', '=' or 'iff'. *)
  val is_reflexivity : Expr.expr -> bool

  (** Indicates whether the term is proof by symmetricity of a relation

      Given an symmetric relation R and a proof for (R t s), produces a proof for (R s t).
      T1: (R t s)
      [symmetry T1]: (R s t)
      T1 is the antecedent of this proof object. *)
  val is_symmetry : Expr.expr -> bool

  (** Indicates whether the term is a proof by transitivity of a relation

      Given a transitive relation R, and proofs for (R t s) and (R s u), produces a proof
      for (R t u).
      T1: (R t s)
      T2: (R s u)
      [trans T1 T2]: (R t u) *)
  val is_transitivity : Expr.expr -> bool

  (** Indicates whether the term is a proof by condensed transitivity of a relation

      Condensed transitivity proof.
      It combines several symmetry and transitivity proofs.
      Example:
      T1: (R a b)
      T2: (R c b)
      T3: (R c d)
      [trans* T1 T2 T3]: (R a d)
      R must be a symmetric and transitive relation.

      Assuming that this proof object is a proof for (R s t), then
      a proof checker must check if it is possible to prove (R s t)
      using the antecedents, symmetry and transitivity.  That is,
      if there is a path from s to t, if we view every
      antecedent (R a b) as an edge between a and b. *)
  val is_Transitivity_star : Expr.expr -> bool

  (** Indicates whether the term is a monotonicity proof object.

      T1: (R t_1 s_1)
      ...
      Tn: (R t_n s_n)
      [monotonicity T1 ... Tn]: (R (f t_1 ... t_n) (f s_1 ... s_n))
      Remark: if t_i == s_i, then the antecedent Ti is suppressed.
      That is, reflexivity proofs are suppressed to save space. *)
  val is_monotonicity : Expr.expr -> bool

  (** Indicates whether the term is a quant-intro proof

      Given a proof for (~ p q), produces a proof for (~ (forall (x) p) (forall (x) q)).
      T1: (~ p q)
      [quant-intro T1]: (~ (forall (x) p) (forall (x) q)) *)
  val is_quant_intro : Expr.expr -> bool

  (** Indicates whether the term is a distributivity proof object.

      Given that f (= or) distributes over g (= and), produces a proof for
      (= (f a (g c d))
      (g (f a c) (f a d)))
      If f and g are associative, this proof also justifies the following equality:
      (= (f (g a b) (g c d))
      (g (f a c) (f a d) (f b c) (f b d)))
      where each f and g can have arbitrary number of arguments.

      This proof object has no antecedents.
      Remark. This rule is used by the CNF conversion pass and
      instantiated by f = or, and g = and. *)
  val is_distributivity : Expr.expr -> bool

  (** Indicates whether the term is a proof by elimination of AND

      Given a proof for (and l_1 ... l_n), produces a proof for l_i
      T1: (and l_1 ... l_n)
      [and-elim T1]: l_i *)
  val is_and_elimination : Expr.expr -> bool

  (** Indicates whether the term is a proof by elimination of not-or

      Given a proof for (not (or l_1 ... l_n)), produces a proof for (not l_i).
      T1: (not (or l_1 ... l_n))
      [not-or-elim T1]: (not l_i)        *)
  val is_or_elimination : Expr.expr -> bool

  (** Indicates whether the term is a proof by rewriting

      A proof for a local rewriting step (= t s).
      The head function symbol of t is interpreted.

      This proof object has no antecedents.
      The conclusion of a rewrite rule is either an equality (= t s),
      an equivalence (iff t s), or equi-satisfiability (~ t s).
      Remark: if f is bool, then = is iff.

      Examples:
      (= (+ ( x : expr ) 0) x)
      (= (+ ( x : expr ) 1 2) (+ 3 x))
      (iff (or ( x : expr ) false) x)           *)
  val is_rewrite : Expr.expr -> bool

  (** Indicates whether the term is a proof by rewriting

      A proof for rewriting an expression t into an expression s.
      This proof object can have n antecedents.
      The antecedents are proofs for equalities used as substitution rules.
      The object is also used in a few cases. The cases are:
      - When applying contextual simplification (CONTEXT_SIMPLIFIER=true)
      - When converting bit-vectors to Booleans (BIT2BOOL=true) *)
  val is_rewrite_star : Expr.expr -> bool

  (** Indicates whether the term is a proof for pulling quantifiers out.

      A proof for (iff (f (forall (x) q(x)) r) (forall (x) (f (q x) r))). This proof object has no antecedents. *)
  val is_pull_quant : Expr.expr -> bool

  (** Indicates whether the term is a proof for pushing quantifiers in.

      A proof for:
      (iff (forall (x_1 ... x_m) (and p_1[x_1 ... x_m] ... p_n[x_1 ... x_m]))
      (and (forall (x_1 ... x_m) p_1[x_1 ... x_m])
      ...
      (forall (x_1 ... x_m) p_n[x_1 ... x_m])))
      This proof object has no antecedents *)
  val is_push_quant : Expr.expr -> bool

  (** Indicates whether the term is a proof for elimination of unused variables.

      A proof for (iff (forall (x_1 ... x_n y_1 ... y_m) p[x_1 ... x_n])
      (forall (x_1 ... x_n) p[x_1 ... x_n]))

      It is used to justify the elimination of unused variables.
      This proof object has no antecedents. *)
  val is_elim_unused_vars : Expr.expr -> bool

  (** Indicates whether the term is a proof for destructive equality resolution

      A proof for destructive equality resolution:
      (iff (forall (x) (or (not (= ( x : expr ) t)) P[x])) P[t])
      if ( x : expr ) does not occur in t.

      This proof object has no antecedents.

      Several variables can be eliminated simultaneously. *)
  val is_der : Expr.expr -> bool

  (** Indicates whether the term is a proof for quantifier instantiation

      A proof of (or (not (forall (x) (P x))) (P a)) *)
  val is_quant_inst : Expr.expr -> bool

  (** Indicates whether the term is a hypothesis marker.
      Mark a hypothesis in a natural deduction style proof. *)
  val is_hypothesis : Expr.expr -> bool

  (** Indicates whether the term is a proof by lemma

      T1: false
      [lemma T1]: (or (not l_1) ... (not l_n))

      This proof object has one antecedent: a hypothetical proof for false.
      It converts the proof in a proof for (or (not l_1) ... (not l_n)),
      when T1 contains the hypotheses: l_1, ..., l_n. *)
  val is_lemma : Expr.expr -> bool

  (** Indicates whether the term is a proof by unit resolution

      T1:      (or l_1 ... l_n l_1' ... l_m')
      T2:      (not l_1)
      ...
      T(n+1):  (not l_n)
      [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m') *)
  val is_unit_resolution : Expr.expr -> bool

  (** Indicates whether the term is a proof by iff-true

      T1: p
      [iff-true T1]: (iff p true) *)
  val is_iff_true : Expr.expr -> bool

  (** Indicates whether the term is a proof by iff-false

      T1: (not p)
      [iff-false T1]: (iff p false) *)
  val is_iff_false : Expr.expr -> bool

  (** Indicates whether the term is a proof by commutativity

      [comm]: (= (f a b) (f b a))

      f is a commutative operator.

      This proof object has no antecedents.
      Remark: if f is bool, then = is iff. *)
  val is_commutativity : Expr.expr -> bool

  (** Indicates whether the term is a proof for Tseitin-like axioms

      Proof object used to justify Tseitin's like axioms:

      (or (not (and p q)) p)
      (or (not (and p q)) q)
      (or (not (and p q r)) p)
      (or (not (and p q r)) q)
      (or (not (and p q r)) r)
      ...
      (or (and p q) (not p) (not q))
      (or (not (or p q)) p q)
      (or (or p q) (not p))
      (or (or p q) (not q))
      (or (not (iff p q)) (not p) q)
      (or (not (iff p q)) p (not q))
      (or (iff p q) (not p) (not q))
      (or (iff p q) p q)
      (or (not (ite a b c)) (not a) b)
      (or (not (ite a b c)) a c)
      (or (ite a b c) (not a) (not b))
      (or (ite a b c) a (not c))
      (or (not (not a)) (not a))
      (or (not a) a)

      This proof object has no antecedents.
      Note: all axioms are propositional tautologies.
      Note also that 'and' and 'or' can take multiple arguments.
      You can recover the propositional tautologies by
      unfolding the Boolean connectives in the axioms a small
      bounded number of steps (=3). *)
  val is_def_axiom : Expr.expr -> bool

  (** Indicates whether the term is a proof for introduction of a name

      Introduces a name for a formula/term.
      Suppose e is an expression with free variables x, and def-intro
      introduces the name n(x). The possible cases are:

      When e is of Boolean type:
      [def-intro]: (and (or n (not e)) (or (not n) e))

      or:
      [def-intro]: (or (not n) e)
      when e only occurs positively.

      When e is of the form (ite cond th el):
      [def-intro]: (and (or (not cond) (= n th)) (or cond (= n el)))

      Otherwise:
      [def-intro]: (= n e)        *)
  val is_def_intro : Expr.expr -> bool

  (** Indicates whether the term is a proof for application of a definition

      [apply-def T1]: F ~ n
      F is 'equivalent' to n, given that T1 is a proof that
      n is a name for F. *)
  val is_apply_def : Expr.expr -> bool

  (** Indicates whether the term is a proof iff-oeq

      T1: (iff p q)
      [iff~ T1]: (~ p q) *)
  val is_iff_oeq : Expr.expr -> bool

  (** Indicates whether the term is a proof for a positive NNF step

      Proof for a (positive) NNF step. Example:

      T1: (not s_1) ~ r_1
      T2: (not s_2) ~ r_2
      T3: s_1 ~ r_1'
      T4: s_2 ~ r_2'
      [nnf-pos T1 T2 T3 T4]: (~ (iff s_1 s_2)
      (and (or r_1 r_2') (or r_1' r_2)))

      The negation normal form steps NNF_POS and NNF_NEG are used in the following cases:
      (a) When creating the NNF of a positive force quantifier.
      The quantifier is retained (unless the bound variables are eliminated).
      Example
      T1: q ~ q_new
      [nnf-pos T1]: (~ (forall (x T) q) (forall (x T) q_new))

      (b) When recursively creating NNF over Boolean formulas, where the top-level
      connective is changed during NNF conversion. The relevant Boolean connectives
      for NNF_POS are 'implies', 'iff', 'xor', 'ite'.
      NNF_NEG furthermore handles the case where negation is pushed
      over Boolean connectives 'and' and 'or'. *)
  val is_nnf_pos : Expr.expr -> bool

  (** Indicates whether the term is a proof for a negative NNF step

      Proof for a (negative) NNF step. Examples:

      T1: (not s_1) ~ r_1
      ...
      Tn: (not s_n) ~ r_n
      [nnf-neg T1 ... Tn]: (not (and s_1 ... s_n)) ~ (or r_1 ... r_n)
      and
      T1: (not s_1) ~ r_1
      ...
      Tn: (not s_n) ~ r_n
      [nnf-neg T1 ... Tn]: (not (or s_1 ... s_n)) ~ (and r_1 ... r_n)
      and
      T1: (not s_1) ~ r_1
      T2: (not s_2) ~ r_2
      T3: s_1 ~ r_1'
      T4: s_2 ~ r_2'
      [nnf-neg T1 T2 T3 T4]: (~ (not (iff s_1 s_2))
      (and (or r_1 r_2) (or r_1' r_2'))) *)
  val is_nnf_neg : Expr.expr -> bool

  (** Indicates whether the term is a proof for a Skolemization step

      Proof for:

      [sk]: (~ (not (forall ( x : expr ) (p ( x : expr ) y))) (not (p (sk y) y)))
      [sk]: (~ (exists ( x : expr ) (p ( x : expr ) y)) (p (sk y) y))

      This proof object has no antecedents. *)
  val is_skolemize : Expr.expr -> bool

  (** Indicates whether the term is a proof by modus ponens for equi-satisfiability.

      Modus ponens style rule for equi-satisfiability.
      T1: p
      T2: (~ p q)
      [mp~ T1 T2]: q   *)
  val is_modus_ponens_oeq : Expr.expr -> bool

  (** Indicates whether the term is a proof for theory lemma

      Generic proof for theory lemmas.

      The theory lemma function comes with one or more parameters.
      The first parameter indicates the name of the theory.
      For the theory of arithmetic, additional parameters provide hints for
      checking the theory lemma.
      The hints for arithmetic are:
      - farkas - followed by rational coefficients. Multiply the coefficients to the
      inequalities in the lemma, add the (negated) inequalities and obtain a contradiction.
      - triangle-eq - Indicates a lemma related to the equivalence:
      (iff (= t1 t2) (and (<= t1 t2) (<= t2 t1)))
      - gcd-test - Indicates an integer linear arithmetic lemma that uses a gcd test. *)
  val is_theory_lemma : Expr.expr -> bool
end

(** Goals

    A goal (aka problem). A goal is essentially a
    of formulas, that can be solved and/or transformed using
    tactics and solvers. *)
module Goal :
sig
  type goal

  (** The precision of the goal.

      Goals can be transformed using over and under approximations.
      An under approximation is applied when the objective is to find a model for a given goal.
      An over approximation is applied when the objective is to find a proof for a given goal. *)
  val get_precision : goal -> Z3enums.goal_prec

  (** Indicates whether the goal is precise. *)
  val is_precise : goal -> bool

  (** Indicates whether the goal is an under-approximation. *)
  val is_underapproximation : goal -> bool

  (** Indicates whether the goal is an over-approximation. *)
  val is_overapproximation : goal -> bool

  (** Indicates whether the goal is garbage (i.e., the product of over- and under-approximations). *)
  val is_garbage : goal -> bool

  (** Adds the constraints to the given goal. *)
  val add : goal -> Expr.expr list -> unit

  (** Indicates whether the goal contains `false'. *)
  val is_inconsistent : goal -> bool

  (** The depth of the goal.
      This tracks how many transformations were applied to it. *)
  val get_depth : goal -> int

  (** Erases all formulas from the given goal. *)
  val reset : goal -> unit

  (** The number of formulas in the goal. *)
  val get_size : goal -> int

  (** The formulas in the goal. *)
  val get_formulas : goal -> Expr.expr list

  (** The number of formulas, subformulas and terms in the goal. *)
  val get_num_exprs : goal -> int

  (** Indicates whether the goal is empty, and it is precise or the product of an under approximation. *)
  val is_decided_sat : goal -> bool

  (** Indicates whether the goal contains `false', and it is precise or the product of an over approximation. *)
  val is_decided_unsat : goal -> bool

  (**  Translates (copies) the Goal to another context.. *)
  val translate : goal -> context -> goal

  (** Simplifies the goal. Essentially invokes the `simplify' tactic on the goal. *)
  val simplify : goal -> Params.params option -> goal

  (** Creates a new Goal.

      Note that the Context must have been created with proof generation support if
      the fourth argument is set to true here. *)
  val mk_goal : context -> bool -> bool -> bool -> goal

  (**  A string representation of the Goal. *)
  val to_string : goal -> string

  (** Goal to BoolExpr conversion. *)
  val as_expr : goal -> Expr.expr
end

(** Models

    A Model contains interpretations (assignments) of constants and functions. *)
module Model :
sig
  type model

  (** Function interpretations

      A function interpretation is represented as a finite map and an 'else'.
      Each entry in the finite map represents the value of a function given a set of arguments.   *)
  module FuncInterp :
  sig
    type func_interp

    (** Function interpretations entries

        An Entry object represents an element in the finite map used to a function interpretation. *)
    module FuncEntry :
    sig
      type func_entry

      (** Return the (symbolic) value of this entry.
      *)
      val get_value : func_entry -> Expr.expr

      (** The number of arguments of the entry.
      *)
      val get_num_args : func_entry -> int

      (** The arguments of the function entry.
      *)
      val get_args : func_entry -> Expr.expr list

      (** A string representation of the function entry.
      *)
      val to_string : func_entry -> string
    end

    (**   The number of entries in the function interpretation. *)
    val get_num_entries : func_interp -> int

    (**   The entries in the function interpretation *)
    val get_entries : func_interp -> FuncEntry.func_entry list

    (**   The (symbolic) `else' value of the function interpretation. *)
    val get_else : func_interp -> Expr.expr

    (**   The arity of the function interpretation *)
    val get_arity : func_interp -> int

    (**   A string representation of the function interpretation. *)
    val to_string : func_interp -> string
  end

  (** Retrieves the interpretation (the assignment) of a func_decl in the model.
      @return An expression if the function has an interpretation in the model, null otherwise. *)
  val get_const_interp : model -> FuncDecl.func_decl -> Expr.expr option

  (** Retrieves the interpretation (the assignment) of an expression in the model.
      @return An expression if the constant has an interpretation in the model, null otherwise. *)
  val get_const_interp_e : model -> Expr.expr -> Expr.expr option

  (** Retrieves the interpretation (the assignment) of a non-constant func_decl in the model.
      @return A FunctionInterpretation if the function has an interpretation in the model, null otherwise. *)
  val get_func_interp : model -> FuncDecl.func_decl -> FuncInterp.func_interp option

  (** The number of constant interpretations in the model. *)
  val get_num_consts : model -> int

  (** The function declarations of the constants in the model. *)
  val get_const_decls : model -> FuncDecl.func_decl list

  (** The number of function interpretations in the model. *)
  val get_num_funcs : model -> int

  (** The function declarations of the function interpretations in the model. *)
  val get_func_decls : model -> FuncDecl.func_decl list

  (** All symbols that have an interpretation in the model. *)
  val get_decls : model -> FuncDecl.func_decl list

  (** Evaluates an expression in the current model.

      This function may fail if the argument contains quantifiers,
      is partial (MODEL_PARTIAL enabled), or if it is not well-sorted.
      In this case a [ModelEvaluationFailedException] is thrown.
  *)
  val eval : model -> Expr.expr -> bool -> Expr.expr option

  (** Alias for [eval]. *)
  val evaluate : model -> Expr.expr -> bool -> Expr.expr option

  (** The number of uninterpreted sorts that the model has an interpretation for. *)
  val get_num_sorts : model -> int

  (** The uninterpreted sorts that the model has an interpretation for.

      Z3 also provides an interpretation for uninterpreted sorts used in a formula.
      The interpretation for a sort is a finite set of distinct values. We say this finite set is
      the "universe" of the sort.
      {!get_num_sorts}
      {!sort_universe} *)
  val get_sorts : model -> Sort.sort list

  (** The finite set of distinct values that represent the interpretation of a sort.
      {!get_sorts}
      @return A list of expressions, where each is an element of the universe of the sort *)
  val sort_universe : model -> Sort.sort -> Expr.expr list

  (** Conversion of models to strings.
      @return A string representation of the model. *)
  val to_string : model -> string
end

(** Probes

    Probes are used to inspect a goal (aka problem) and collect information that may be used to decide
    which solver and/or preprocessing step will be used.
    The complete list of probes may be obtained using the procedures [Context.NumProbes]
    and [Context.ProbeNames].
    It may also be obtained using the command [(help-tactic)] in the SMT 2.0 front-end.
*)
module Probe :
sig
  type probe

  (** Execute the probe over the goal.
      @return A probe always produce a float value.
      "Boolean" probes return 0.0 for false, and a value different from 0.0 for true. *)
  val apply : probe -> Goal.goal -> float

  (** The number of supported Probes. *)
  val get_num_probes : context -> int

  (** The names of all supported Probes. *)
  val get_probe_names : context -> string list

  (** Returns a string containing a description of the probe with the given name. *)
  val get_probe_description : context -> string -> string

  (** Creates a new Probe. *)
  val mk_probe : context -> string -> probe

  (** Create a probe that always evaluates to a float value. *)
  val const : context -> float -> probe

  (** Create a probe that evaluates to "true" when the value returned by the first argument
      is less than the value returned by second argument *)
  val lt : context -> probe -> probe -> probe

  (** Create a probe that evaluates to "true" when the value returned by the first argument
      is greater than the value returned by second argument *)
  val gt : context -> probe -> probe -> probe

  (** Create a probe that evaluates to "true" when the value returned by the first argument
      is less than or equal the value returned by second argument *)
  val le : context -> probe -> probe -> probe

  (** Create a probe that evaluates to "true" when the value returned by the first argument
      is greater than or equal the value returned by second argument *)
  val ge : context -> probe -> probe -> probe


  (** Create a probe that evaluates to "true" when the value returned by the first argument
      is equal the value returned by second argument *)
  val eq : context -> probe -> probe -> probe

  (** Create a probe that evaluates to "true" when both of two probes evaluate to "true". *)
  val and_ : context -> probe -> probe -> probe

  (** Create a probe that evaluates to "true" when either of two probes evaluates to "true". *)
  val or_ : context -> probe -> probe -> probe

  (** Create a probe that evaluates to "true" when another probe does not evaluate to "true". *)
  val not_ : context -> probe -> probe
end

(** Tactics

    Tactics are the basic building block for creating custom solvers for specific problem domains.
    The complete list of tactics may be obtained using [Context.get_num_tactics]
    and [Context.get_tactic_names].
    It may also be obtained using the command [(help-tactic)] in the SMT 2.0 front-end.
*)
module Tactic :
sig
  type tactic

  (** Tactic application results

      ApplyResult objects represent the result of an application of a
      tactic to a goal. It contains the subgoals that were produced. *)
  module ApplyResult :
  sig
    type apply_result

    (** The number of Subgoals. *)
    val get_num_subgoals : apply_result -> int

    (** Retrieves the subgoals from the apply_result. *)
    val get_subgoals : apply_result -> Goal.goal list

    (** Retrieves a subgoal from the apply_result. *)
    val get_subgoal : apply_result -> int -> Goal.goal

    (** A string representation of the ApplyResult. *)
    val to_string : apply_result -> string
  end

  (** A string containing a description of parameters accepted by the tactic. *)
  val get_help : tactic -> string

  (** Retrieves parameter descriptions for Tactics. *)
  val get_param_descrs : tactic -> Params.ParamDescrs.param_descrs

  (** Apply the tactic to the goal. *)
  val apply : tactic -> Goal.goal -> Params.params option -> ApplyResult.apply_result

  (** The number of supported tactics. *)
  val get_num_tactics : context -> int

  (** The names of all supported tactics. *)
  val get_tactic_names : context -> string list

  (** Returns a string containing a description of the tactic with the given name. *)
  val get_tactic_description : context -> string -> string

  (** Creates a new Tactic. *)
  val mk_tactic : context -> string -> tactic

  (** Create a tactic that applies one tactic to a Goal and
      then another one to every subgoal produced by the first one. *)
  val and_then : context -> tactic -> tactic -> tactic list -> tactic

  (** Create a tactic that first applies one tactic to a Goal and
      if it fails then returns the result of another tactic applied to the Goal. *)
  val or_else : context -> tactic -> tactic -> tactic

  (** Create a tactic that applies one tactic to a goal for some time (in milliseconds).

      If the tactic does not terminate within the timeout, then it fails. *)
  val try_for : context -> tactic -> int -> tactic

  (** Create a tactic that applies one tactic to a given goal if the probe
      evaluates to true.

      If the probe evaluates to false, then the new tactic behaves like the [skip] tactic.  *)
  val when_ : context -> Probe.probe -> tactic -> tactic

  (** Create a tactic that applies a tactic to a given goal if the probe
      evaluates to true and another tactic otherwise. *)
  val cond : context -> Probe.probe -> tactic -> tactic -> tactic

  (** Create a tactic that keeps applying one tactic until the goal is not
      modified anymore or the maximum number of iterations is reached. *)
  val repeat : context -> tactic -> int -> tactic

  (** Create a tactic that just returns the given goal. *)
  val skip : context -> tactic

  (** Create a tactic always fails. *)
  val fail : context -> tactic

  (** Create a tactic that fails if the probe evaluates to false. *)
  val fail_if : context -> Probe.probe -> tactic

  (** Create a tactic that fails if the goal is not trivially satisfiable (i.e., empty)
      or trivially unsatisfiable (i.e., contains `false'). *)
  val fail_if_not_decided : context -> tactic

  (** Create a tactic that applies a tactic using the given set of parameters. *)
  val using_params : context -> tactic -> Params.params -> tactic

  (** Create a tactic that applies a tactic using the given set of parameters.
      Alias for [UsingParams]*)
  val with_ : context -> tactic -> Params.params -> tactic

  (** Create a tactic that applies the given tactics in parallel until one of them succeeds (i.e., the first that doesn't fail). *)
  val par_or : context -> tactic list -> tactic

  (** Create a tactic that applies a tactic to a given goal and then another tactic
      to every subgoal produced by the first one. The subgoals are processed in parallel. *)
  val par_and_then : context -> tactic -> tactic -> tactic

  (** Interrupt the execution of a Z3 procedure.
      This procedure can be used to interrupt: solvers, simplifiers and tactics. *)
  val interrupt : context -> unit
end

(** Objects that track statistical information. *)
module Statistics :
sig
  type statistics

  (** Statistical data is organized into pairs of \[Key, Entry\], where every
      Entry is either a floating point or integer value. *)
  module Entry :
  sig
    type statistics_entry

    (** The key of the entry. *)
    val get_key : statistics_entry -> string

    (** The int-value of the entry. *)
    val get_int : statistics_entry -> int

    (** The float-value of the entry. *)
    val get_float : statistics_entry -> float

    (** True if the entry is uint-valued. *)
    val is_int : statistics_entry -> bool

    (** True if the entry is float-valued. *)
    val is_float : statistics_entry -> bool

    (** The string representation of the entry's value. *)
    val to_string_value : statistics_entry -> string

    (** The string representation of the entry (key and value) *)
    val to_string : statistics_entry -> string
  end

  (** A string representation of the statistical data. *)
  val to_string : statistics -> string

  (** The number of statistical data. *)
  val get_size : statistics -> int

  (** The data entries. *)
  val get_entries : statistics -> Entry.statistics_entry list

  (**   The statistical counters. *)
  val get_keys : statistics -> string list

  (** The value of a particular statistical counter. *)
  val get : statistics -> string -> Entry.statistics_entry option
end

(** Solvers *)
module Solver :
sig
  type solver
  type status = UNSATISFIABLE | UNKNOWN | SATISFIABLE

  val string_of_status : status -> string

  (** A string that describes all available solver parameters. *)
  val get_help : solver -> string

  (** Sets the solver parameters. *)
  val set_parameters : solver -> Params.params -> unit

  (** Retrieves parameter descriptions for solver. *)
  val get_param_descrs : solver -> Params.ParamDescrs.param_descrs

  (** The current number of backtracking points (scopes).
      {!pop}
      {!push} *)
  val get_num_scopes : solver -> int

  (** Creates a backtracking point.
      {!pop} *)
  val push : solver -> unit

  (** Backtracks a number of backtracking points.
      Note that an exception is thrown if the integer is not smaller than {!get_num_scopes}
      {!push} *)
  val pop : solver -> int -> unit

  (** Resets the Solver.
      This removes all assertions from the solver. *)
  val reset : solver -> unit

  (** Assert a constraint (or multiple) into the solver. *)
  val add : solver -> Expr.expr list -> unit

  (** Assert multiple constraints (cs) into the solver, and track them (in the
      unsat) core using the Boolean constants in ps.
     
      This API is an alternative to {!check} with assumptions for extracting unsat cores.
      Both APIs can be used in the same solver. The unsat core will contain a combination
      of the Boolean variables provided using {!assert_and_track} and the Boolean literals
      provided using {!check} with assumptions. *)
  val assert_and_track_l : solver -> Expr.expr list -> Expr.expr list -> unit

  (** Assert a constraint (c) into the solver, and track it (in the unsat) core
      using the Boolean constant p.
      
      This API is an alternative to {!check} with assumptions for extracting unsat cores. 
      Both APIs can be used in the same solver. The unsat core will contain a combination  
      of the Boolean variables provided using {!assert_and_track} and the Boolean literals 
      provided using {!check} with assumptions. *)
  val assert_and_track : solver -> Expr.expr -> Expr.expr -> unit

  (** The number of assertions in the solver. *)
  val get_num_assertions : solver -> int

  (** The set of asserted formulas. *)
  val get_assertions : solver -> Expr.expr list

  (** Checks whether the assertions in the solver are consistent or not.

      {!Model}
      {!get_unsat_core}
      {!Proof}     *)
  val check : solver -> Expr.expr list -> status

  (** The model of the last [Check].

      The result is [None] if [Check] was not invoked before,
      if its results was not [SATISFIABLE], or if model production is not enabled. *)
  val get_model : solver -> Model.model option

  (** The proof of the last [Check].

      The result is [null] if [Check] was not invoked before,
      if its results was not [UNSATISFIABLE], or if proof production is disabled. *)
  val get_proof : solver -> Expr.expr option

  (** The unsat core of the last [Check].

      The unsat core is a subset of [Assertions]
      The result is empty if [Check] was not invoked before,
      if its results was not [UNSATISFIABLE], or if core production is disabled. *)
  val get_unsat_core : solver -> Expr.expr list

  (** A brief justification of why the last call to [Check] returned [UNKNOWN]. *)
  val get_reason_unknown : solver -> string

  (** Solver statistics. *)
  val get_statistics : solver -> Statistics.statistics

  (** Creates a new (incremental) solver.

      This solver also uses a set of builtin tactics for handling the first
      check-sat command, and check-sat commands that take more than a given
      number of milliseconds to be solved.  *)
  val mk_solver : context -> Symbol.symbol option -> solver

  (** Creates a new (incremental) solver.
      {!mk_solver} *)
  val mk_solver_s : context -> string -> solver

  (** Creates a new (incremental) solver.  *)
  val mk_simple_solver : context -> solver

  (** Creates a solver that is implemented using the given tactic.

      The solver supports the commands [Push] and [Pop], but it
      will always solve each check from scratch. *)
  val mk_solver_t : context -> Tactic.tactic -> solver

  (** Create a clone of the current solver with respect to a context. *)
  val translate : solver -> context -> solver

  (** A string representation of the solver. *)
  val to_string : solver -> string
end

(** Fixedpoint solving *)
module Fixedpoint :
sig
  type fixedpoint

  (** A string that describes all available fixedpoint solver parameters. *)
  val get_help : fixedpoint -> string

  (** Sets the fixedpoint solver parameters. *)
  val set_parameters : fixedpoint -> Params.params -> unit

  (** Retrieves parameter descriptions for Fixedpoint solver. *)
  val get_param_descrs : fixedpoint -> Params.ParamDescrs.param_descrs

  (** Assert a constraints into the fixedpoint solver. *)
  val add : fixedpoint -> Expr.expr list -> unit

  (** Register predicate as recursive relation. *)
  val register_relation : fixedpoint -> FuncDecl.func_decl -> unit

  (** Add rule into the fixedpoint solver. *)
  val add_rule : fixedpoint -> Expr.expr -> Symbol.symbol option -> unit

  (** Add table fact to the fixedpoint solver. *)
  val add_fact : fixedpoint -> FuncDecl.func_decl -> int list -> unit

  (** Query the fixedpoint solver.
      A query is a conjunction of constraints. The constraints may include the recursively defined relations.
      The query is satisfiable if there is an instance of the query variables and a derivation for it.
      The query is unsatisfiable if there are no derivations satisfying the query variables.  *)
  val query : fixedpoint -> Expr.expr -> Solver.status

  (** Query the fixedpoint solver.
      A query is an array of relations.
      The query is satisfiable if there is an instance of some relation that is non-empty.
      The query is unsatisfiable if there are no derivations satisfying any of the relations. *)
  val query_r : fixedpoint -> FuncDecl.func_decl list -> Solver.status

  (** Update named rule into in the fixedpoint solver. *)
  val update_rule : fixedpoint -> Expr.expr -> Symbol.symbol -> unit

  (** Retrieve satisfying instance or instances of solver,
      or definitions for the recursive predicates that show unsatisfiability. *)
  val get_answer : fixedpoint -> Expr.expr option

  (** Retrieve explanation why fixedpoint engine returned status Unknown. *)
  val get_reason_unknown : fixedpoint -> string

  (** Retrieve the number of levels explored for a given predicate. *)
  val get_num_levels : fixedpoint -> FuncDecl.func_decl -> int

  (** Retrieve the cover of a predicate. *)
  val get_cover_delta : fixedpoint -> int -> FuncDecl.func_decl -> Expr.expr option

  (** Add <tt>property</tt> about the <tt>predicate</tt>.
      The property is added at <tt>level</tt>. *)
  val add_cover : fixedpoint -> int -> FuncDecl.func_decl -> Expr.expr -> unit

  (** Retrieve internal string representation of fixedpoint object. *)
  val to_string : fixedpoint -> string

  (** Instrument the Datalog engine on which table representation to use for recursive predicate. *)
  val set_predicate_representation : fixedpoint -> FuncDecl.func_decl -> Symbol.symbol list -> unit

  (** Convert benchmark given as set of axioms, rules and queries to a string. *)
  val to_string_q : fixedpoint -> Expr.expr list -> string

  (** Retrieve set of rules added to fixedpoint context. *)
  val get_rules : fixedpoint -> Expr.expr list

  (** Retrieve set of assertions added to fixedpoint context. *)
  val get_assertions : fixedpoint -> Expr.expr list

  (** Create a Fixedpoint context. *)
  val mk_fixedpoint : context -> fixedpoint

  (** Retrieve statistics information from the last call to #Z3_fixedpoint_query. *)
  val get_statistics : fixedpoint -> Statistics.statistics

  (** Parse an SMT-LIB2 string with fixedpoint rules.
      Add the rules to the current fixedpoint context.
      Return the set of queries in the string. *)
  val parse_string : fixedpoint -> string -> Expr.expr list

  (** Parse an SMT-LIB2 file with fixedpoint rules.
      Add the rules to the current fixedpoint context.
      Return the set of queries in the file. *)
  val parse_file : fixedpoint -> string -> Expr.expr list
end

(** Optimization *)
module Optimize :
sig
  type optimize
  type handle

  (** Create a Optimize context. *)
  val mk_opt : context -> optimize

  (** A string that describes all available optimize solver parameters. *)
  val get_help : optimize -> string

  (** Sets the optimize solver parameters. *)
  val set_parameters : optimize -> Params.params -> unit

  (** Retrieves parameter descriptions for Optimize solver. *)
  val get_param_descrs : optimize -> Params.ParamDescrs.param_descrs

  (** Assert a constraints into the optimize solver. *)
  val add : optimize -> Expr.expr list -> unit

  (** Assert a soft constraint.
      Supply integer weight and string that identifies a group
      of soft constraints. *)
  val add_soft : optimize -> Expr.expr -> string -> Symbol.symbol -> handle

  (** Add maximization objective. *)
  val maximize : optimize -> Expr.expr -> handle

  (** Add minimization objective. *)
  val minimize : optimize -> Expr.expr -> handle

  (** Checks whether the assertions in the context are satisfiable and solves objectives. *)
  val check : optimize -> Solver.status

  (** Retrieve model from satisfiable context *)
  val get_model : optimize -> Model.model option

  (** Retrieve lower bound in current model for handle *)
  val get_lower : handle -> Expr.expr

  (** Retrieve upper bound in current model for handle *)
  val get_upper : handle -> Expr.expr

  (** Creates a backtracking point. {!pop} *)
  val push : optimize -> unit

  (** Backtrack one backtracking point.
      Note that an exception is thrown if Pop is called without a corresponding [Push]
      {!push} *)
  val pop : optimize -> unit

  (** Retrieve explanation why optimize engine returned status Unknown. *)
  val get_reason_unknown : optimize -> string

  (** Retrieve SMT-LIB string representation of optimize object. *)
  val to_string : optimize -> string

  (** Retrieve statistics information from the last call to check *)
  val get_statistics : optimize -> Statistics.statistics

  (** Parse an SMT-LIB2 file with assertions, soft constraints and optimization
      objectives. Add the parsed constraints and objectives to the optimization 
      context. *)
  val from_file : optimize -> string -> unit

  (** Parse an SMT-LIB2 string with assertions, soft constraints and optimization 
      objectives. Add the parsed constraints and objectives to the optimization 
      context. *)
  val from_string : optimize -> string -> unit
                                            
  (** Return the set of asserted formulas on the optimization context. *) 
  val get_assertions : optimize -> Expr.expr list

  (** Return objectives on the optimization context. If the objective function 
      is a max-sat objective it is returned as a Pseudo-Boolean (minimization) 
      sum of the form (+ (if f1 w1 0) (if f2 w2 0) ...). If the objective 
      function is entered as a maximization objective, then return the 
      corresponding minimization objective. In this way the resulting 
      objective function is always returned as a minimization objective. *)
  val get_objectives : optimize -> Expr.expr list
end


(** Functions for handling SMT and SMT2 expressions and files *)
module SMT :
sig
  (** Convert a benchmark into an SMT-LIB formatted string.

      @return A string representation of the benchmark. *)
  val benchmark_to_smtstring : context -> string -> string -> string -> string -> Expr.expr list -> Expr.expr -> string

  (** Parse the given string using the SMT-LIB2 parser.

      @return A conjunction of assertions in the scope (up to push/pop) at the end of the string. *)
  val parse_smtlib2_string : context -> string -> Symbol.symbol list -> Sort.sort list -> Symbol.symbol list -> FuncDecl.func_decl list -> AST.ASTVector.ast_vector

  (** Parse the given file using the SMT-LIB2 parser. *)
  val parse_smtlib2_file : context -> string -> Symbol.symbol list -> Sort.sort list -> Symbol.symbol list -> FuncDecl.func_decl list -> AST.ASTVector.ast_vector
end


(** Set a global (or module) parameter, which is shared by all Z3 contexts.

    When a Z3 module is initialized it will use the value of these parameters
    when Z3_params objects are not provided.
    The name of parameter can be composed of characters [a-z][A-Z], digits [0-9], '-' and '_'.
    The character '.' is a delimiter (more later).
    The parameter names are case-insensitive. The character '-' should be viewed as an "alias" for '_'.
    Thus, the following parameter names are considered equivalent: "pp.decimal-precision"  and "PP.DECIMAL_PRECISION".
    This function can be used to set parameters for a specific Z3 module.
    This can be done by using <module-name>.<parameter-name>.
    For example:
    (set_global_param "pp.decimal" "true")
    will set the parameter "decimal" in the module "pp" to true.
*)
val set_global_param : string -> string -> unit

(** Get a global (or module) parameter.

    Returns None if the parameter does not exist.
    The caller must invoke #Z3_global_param_del_value to delete the value returned at param_value.
    This function cannot be invoked simultaneously from different threads without synchronization.
    The result string stored in param_value is stored in a shared location.
*)
val get_global_param : string -> string option

(** Restore the value of all global (and module) parameters.

    This command will not affect already created objects (such as tactics and solvers)
    {!set_global_param}
*)

val global_param_reset_all : unit -> unit

(** Enable/disable printing of warning messages to the console.

    Note that this function is static and effects the behaviour of
    all contexts globally. *)
val toggle_warning_messages : bool -> unit

(**
   Enable tracing messages tagged as `tag' when Z3 is compiled in debug mode.

   Remarks: It is a NOOP otherwise.
*)
val enable_trace : string -> unit

(**
   Disable tracing messages tagged as `tag' when Z3 is compiled in debug mode.

   Remarks: It is a NOOP otherwise.
*)
val disable_trace : string -> unit


(** Memory management **)
module Memory :
sig
  (** Reset all allocated resources **)
  val reset : unit -> unit
end
