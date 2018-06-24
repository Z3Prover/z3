(**
   The Z3 ML/OCaml Interface.

   Copyright (C) 2012 Microsoft Corporation
   @author CM Wintersteiger (cwinter) 2012-12-17
*)

open Z3enums

exception Error of string
let _ = Callback.register_exception "Z3EXCEPTION" (Error "")

type context = Z3native.context

module Log =
struct
  let open_ filename =
    lbool_of_int (Z3native.open_log filename) = L_TRUE
  let close = Z3native.close_log
  let append = Z3native.append_log
end


module Version =
struct
  let (major, minor, build, revision) = Z3native.get_version ()

  let full_version : string = Z3native.get_full_version()
                                                             
  let to_string =
    string_of_int major ^ "." ^
    string_of_int minor ^ "." ^
    string_of_int build ^ "." ^
    string_of_int revision
end

let mk_list f n =
  let rec mk_list' i accu =
    if i >= n then
      List.rev accu
    else
      mk_list' (i + 1) ((f i)::accu)
  in
  mk_list' 0 []

let mk_context (settings:(string * string) list) =
  let cfg = Z3native.mk_config () in
  let f e = Z3native.set_param_value cfg (fst e) (snd e) in
  List.iter f settings;
  let res = Z3native.mk_context_rc cfg in
  Z3native.del_config cfg;
  Z3native.set_ast_print_mode res (Z3enums.int_of_ast_print_mode PRINT_SMTLIB2_COMPLIANT);
  Z3native.set_internal_error_handler res;
  res

module Symbol =
struct
  type symbol = Z3native.symbol
  let gc = Z3native.context_of_symbol

  let kind o = symbol_kind_of_int (Z3native.get_symbol_kind (gc o) o)
  let is_int_symbol o = kind o = INT_SYMBOL
  let is_string_symbol o = kind o = STRING_SYMBOL
  let get_int o = Z3native.get_symbol_int (gc o) o
  let get_string o = Z3native.get_symbol_string (gc o) o
  let to_string o =
    match kind o with
    | INT_SYMBOL -> string_of_int (Z3native.get_symbol_int (gc o) o)
    | STRING_SYMBOL -> Z3native.get_symbol_string (gc o) o

  let mk_int = Z3native.mk_int_symbol
  let mk_string = Z3native.mk_string_symbol

  let mk_ints ctx names = List.map (mk_int ctx) names
  let mk_strings ctx names = List.map (mk_string ctx) names
end

module rec AST :
sig
  type ast = Z3native.ast
  val gc : ast -> context
  module ASTVector :
  sig
    type ast_vector = Z3native.ast_vector
    val mk_ast_vector : context -> ast_vector
    val get_size : ast_vector -> int
    val get : ast_vector -> int -> ast
    val set : ast_vector -> int -> ast -> unit
    val resize : ast_vector -> int -> unit
    val push : ast_vector -> ast -> unit
    val translate : ast_vector -> context -> ast_vector
    val to_list : ast_vector -> ast list
    val to_expr_list : ast_vector -> Expr.expr list
    val to_string : ast_vector -> string
  end
  module ASTMap :
  sig
    type ast_map = Z3native.ast_map
    val mk_ast_map : context -> ast_map
    val contains : ast_map -> ast -> bool
    val find : ast_map -> ast -> ast
    val insert : ast_map -> ast -> ast -> unit
    val erase : ast_map -> ast -> unit
    val reset : ast_map -> unit
    val get_size : ast_map -> int
    val get_keys : ast_map -> ast list
    val to_string : ast_map -> string
  end
  val hash : ast -> int
  val get_id : ast -> int
  val get_ast_kind : ast -> Z3enums.ast_kind
  val is_expr : ast -> bool
  val is_app : ast -> bool
  val is_var : ast -> bool
  val is_quantifier : ast -> bool
  val is_sort : ast -> bool
  val is_func_decl : ast -> bool
  val to_string : ast -> string
  val to_sexpr : ast -> string
  val equal : ast -> ast -> bool
  val compare : ast -> ast -> int
  val translate : ast -> context -> ast
end = struct
  type ast = Z3native.ast
  let gc = Z3native.context_of_ast

  module ASTVector =
  struct
    type ast_vector = Z3native.ast_vector
    let gc = Z3native.context_of_ast_vector

    let mk_ast_vector = Z3native.mk_ast_vector
    let get_size (x:ast_vector) = Z3native.ast_vector_size (gc x) x
    let get (x:ast_vector) (i:int) = Z3native.ast_vector_get (gc x) x i
    let set (x:ast_vector) (i:int) (value:ast) = Z3native.ast_vector_set (gc x) x i value
    let resize (x:ast_vector) (new_size:int) = Z3native.ast_vector_resize (gc x) x new_size
    let push (x:ast_vector) (a:ast) = Z3native.ast_vector_push (gc x) x a
    let translate (x:ast_vector) (to_ctx:context) = Z3native.ast_vector_translate (gc x) x to_ctx

    let to_list (x:ast_vector) =
      let xs = get_size x in
      let f i = get x i in
      mk_list f xs

    let to_expr_list (x:ast_vector) =
      let xs = get_size x in
      let f i = get x i in
      mk_list f xs

    let to_string x = Z3native.ast_vector_to_string (gc x) x
  end

  module ASTMap =
  struct
    type ast_map = Z3native.ast_map
    let gc = Z3native.context_of_ast_map

    let mk_ast_map = Z3native.mk_ast_map
    let contains (x:ast_map) (key:ast) = Z3native.ast_map_contains (gc x) x key
    let find (x:ast_map) (key:ast) = Z3native.ast_map_find (gc x) x key
    let insert (x:ast_map) (key:ast) (value:ast) = Z3native.ast_map_insert (gc x) x key value
    let erase (x:ast_map) (key:ast) = Z3native.ast_map_erase (gc x) x key
    let reset (x:ast_map) = Z3native.ast_map_reset (gc x) x
    let get_size (x:ast_map) = Z3native.ast_map_size (gc x) x

    let get_keys (x:ast_map) =
      let av = Z3native.ast_map_keys (gc x) x in
      ASTVector.to_list av

    let to_string (x:ast_map) = Z3native.ast_map_to_string (gc x) x
  end

  let hash (x:ast) = Z3native.get_ast_hash (gc x) x
  let get_id (x:ast) = Z3native.get_ast_id (gc x) x
  let get_ast_kind (x:ast) = ast_kind_of_int (Z3native.get_ast_kind (gc x) x)

  let is_expr (x:ast) =
    match get_ast_kind x with
    | APP_AST
    | NUMERAL_AST
    | QUANTIFIER_AST
    | VAR_AST -> true
    | _ -> false

  let is_app (x:ast) = get_ast_kind x = APP_AST
  let is_var (x:ast) = get_ast_kind x = VAR_AST
  let is_quantifier (x:ast) = get_ast_kind x = QUANTIFIER_AST
  let is_sort (x:ast) = get_ast_kind x = SORT_AST
  let is_func_decl (x:ast) = get_ast_kind x = FUNC_DECL_AST

  let to_string (x:ast) = Z3native.ast_to_string (gc x) x
  let to_sexpr (x:ast) = Z3native.ast_to_string (gc x) x

  (* The built-in equality uses the custom operations of the C layer *)
  let equal = (=)

  (* The standard comparison uses the custom operations of the C layer *)
  let compare = Pervasives.compare

  let translate (x:ast) (to_ctx:context) =
    if gc x = to_ctx then
      x
    else
      Z3native.translate (gc x) x to_ctx
end

and Sort :
sig
  type sort = AST.ast
  val gc : sort -> context
  val equal : sort -> sort -> bool
  val get_id : sort -> int
  val get_sort_kind : sort -> Z3enums.sort_kind
  val get_name : sort -> Symbol.symbol
  val to_string : sort -> string
  val mk_uninterpreted : context -> Symbol.symbol -> sort
  val mk_uninterpreted_s : context -> string -> sort
end = struct
  type sort = Z3native.sort
  let gc = Z3native.context_of_ast

  let equal a b = (a = b) || (gc a = gc b && Z3native.is_eq_sort (gc a) a b)

  let get_id (x:sort) = Z3native.get_sort_id (gc x) x
  let get_sort_kind (x:sort) = sort_kind_of_int (Z3native.get_sort_kind (gc x) x)
  let get_name (x:sort) = Z3native.get_sort_name (gc x) x
  let to_string (x:sort) = Z3native.sort_to_string (gc x) x
  let mk_uninterpreted = Z3native.mk_uninterpreted_sort
  let mk_uninterpreted_s (ctx:context) (s:string) = mk_uninterpreted ctx (Symbol.mk_string ctx s)
end

and FuncDecl :
sig
  type func_decl = Z3native.func_decl
  val gc : func_decl -> context
  module Parameter :
  sig
    type parameter =
        P_Int of int
      | P_Dbl of float
      | P_Sym of Symbol.symbol
      | P_Srt of Sort.sort
      | P_Ast of AST.ast
      | P_Fdl of func_decl
      | P_Rat of string

    val get_kind : parameter -> Z3enums.parameter_kind
    val get_int : parameter -> int
    val get_float : parameter -> float
    val get_symbol : parameter -> Symbol.symbol
    val get_sort : parameter -> Sort.sort
    val get_ast : parameter -> AST.ast
    val get_func_decl : parameter -> func_decl
    val get_rational : parameter -> string
  end
  val mk_func_decl : context -> Symbol.symbol -> Sort.sort list -> Sort.sort -> func_decl
  val mk_func_decl_s : context -> string -> Sort.sort list -> Sort.sort -> func_decl
  val mk_fresh_func_decl : context -> string -> Sort.sort list -> Sort.sort -> func_decl
  val mk_const_decl : context -> Symbol.symbol -> Sort.sort -> func_decl
  val mk_const_decl_s : context -> string -> Sort.sort -> func_decl
  val mk_fresh_const_decl : context -> string -> Sort.sort -> func_decl
  val equal : func_decl -> func_decl -> bool
  val to_string : func_decl -> string
  val get_id : func_decl -> int
  val get_arity : func_decl -> int
  val get_domain_size : func_decl -> int
  val get_domain : func_decl -> Sort.sort list
  val get_range : func_decl -> Sort.sort
  val get_decl_kind : func_decl -> Z3enums.decl_kind
  val get_name : func_decl -> Symbol.symbol
  val get_num_parameters : func_decl -> int
  val get_parameters : func_decl -> Parameter.parameter list
  val apply : func_decl -> Expr.expr list -> Expr.expr
end = struct
  type func_decl = AST.ast
  let gc = Z3native.context_of_ast

  module Parameter =
  struct
    type parameter =
      | P_Int of int
      | P_Dbl of float
      | P_Sym of Symbol.symbol
      | P_Srt of Sort.sort
      | P_Ast of AST.ast
      | P_Fdl of func_decl
      | P_Rat of string

    let get_kind = function
      | P_Int _ -> PARAMETER_INT
      | P_Dbl _ -> PARAMETER_DOUBLE
      | P_Sym _ -> PARAMETER_SYMBOL
      | P_Srt _ -> PARAMETER_SORT
      | P_Ast _ -> PARAMETER_AST
      | P_Fdl _ -> PARAMETER_FUNC_DECL
      | P_Rat _ -> PARAMETER_RATIONAL

    let get_int = function
      | P_Int x -> x
      | _ -> raise (Error "parameter is not an int")

    let get_float = function
      | P_Dbl x -> x
      | _ -> raise (Error "parameter is not a float")

    let get_symbol = function
      | P_Sym x -> x
      | _ -> raise (Error "parameter is not a symbol")

    let get_sort = function
      | P_Srt x -> x
      | _ -> raise (Error "parameter is not a sort")

    let get_ast = function
      | P_Ast x -> x
      | _ -> raise (Error "parameter is not an ast")

    let get_func_decl = function
      | P_Fdl x -> x
      | _ -> raise (Error "parameter is not a func_decl")

    let get_rational = function
      | P_Rat x -> x
      | _ -> raise (Error "parameter is not a rational string")
  end

  let mk_func_decl (ctx:context) (name:Symbol.symbol) (domain:Sort.sort list) (range:Sort.sort) =
    Z3native.mk_func_decl ctx name (List.length domain) domain range

  let mk_func_decl_s (ctx:context) (name:string) (domain:Sort.sort list) (range:Sort.sort) =
    mk_func_decl ctx (Symbol.mk_string ctx name) domain range

  let mk_fresh_func_decl (ctx:context) (prefix:string) (domain:Sort.sort list) (range:Sort.sort) =
    Z3native.mk_fresh_func_decl ctx prefix (List.length domain) domain range

  let mk_const_decl (ctx:context) (name:Symbol.symbol) (range:Sort.sort) =
    Z3native.mk_func_decl ctx name 0 [] range

  let mk_const_decl_s (ctx:context) (name:string) (range:Sort.sort) =
    Z3native.mk_func_decl ctx (Symbol.mk_string ctx name) 0 [] range

  let mk_fresh_const_decl (ctx:context) (prefix:string) (range:Sort.sort) =
    Z3native.mk_fresh_func_decl ctx prefix 0 [] range

  let equal a b = (a = b) || (gc a = gc b && Z3native.is_eq_func_decl (gc a) a b)

  let to_string (x:func_decl) = Z3native.func_decl_to_string (gc x) x
  let get_id (x:func_decl) = Z3native.get_func_decl_id (gc x) x
  let get_arity (x:func_decl) = Z3native.get_arity (gc x) x
  let get_domain_size (x:func_decl) = Z3native.get_domain_size (gc x) x

  let get_domain (x:func_decl) =
    let n = get_domain_size x in
    let f i = Z3native.get_domain (gc x) x i in
    mk_list f n

  let get_range (x:func_decl) = Z3native.get_range (gc x) x
  let get_decl_kind (x:func_decl) = decl_kind_of_int (Z3native.get_decl_kind (gc x) x)
  let get_name (x:func_decl) = Z3native.get_decl_name (gc x) x
  let get_num_parameters (x:func_decl) = Z3native.get_decl_num_parameters (gc x) x

  let get_parameters (x:func_decl) =
    let n = get_num_parameters x in
    let f i =
      match parameter_kind_of_int (Z3native.get_decl_parameter_kind (gc x) x i) with
      | PARAMETER_INT -> Parameter.P_Int (Z3native.get_decl_int_parameter (gc x) x i)
      | PARAMETER_DOUBLE -> Parameter.P_Dbl (Z3native.get_decl_double_parameter (gc x) x i)
      | PARAMETER_SYMBOL-> Parameter.P_Sym (Z3native.get_decl_symbol_parameter (gc x) x i)
      | PARAMETER_SORT -> Parameter.P_Srt (Z3native.get_decl_sort_parameter (gc x) x i)
      | PARAMETER_AST -> Parameter.P_Ast (Z3native.get_decl_ast_parameter (gc x) x i)
      | PARAMETER_FUNC_DECL -> Parameter.P_Fdl (Z3native.get_decl_func_decl_parameter (gc x) x i)
      | PARAMETER_RATIONAL -> Parameter.P_Rat (Z3native.get_decl_rational_parameter (gc x) x i)
    in
    mk_list f n

  let apply (x:func_decl) (args:Expr.expr list) = Expr.expr_of_func_app (gc x) x args
end


and Params:
sig
  type params = Z3native.params
  module ParamDescrs :
  sig
    type param_descrs = Z3native.param_descrs
    val validate : param_descrs -> params -> unit
    val get_kind : param_descrs -> Symbol.symbol -> Z3enums.param_kind
    val get_names : param_descrs -> Symbol.symbol list
    val get_size : param_descrs -> int
    val to_string : param_descrs -> string
  end
  val add_bool : params -> Symbol.symbol -> bool -> unit
  val add_int : params -> Symbol.symbol -> int -> unit
  val add_float : params -> Symbol.symbol -> float -> unit
  val add_symbol : params -> Symbol.symbol -> Symbol.symbol -> unit
  val mk_params : context -> params
  val to_string : params -> string

  val update_param_value : context -> string -> string -> unit
  val set_print_mode : context -> Z3enums.ast_print_mode -> unit
end = struct
  type params = Z3native.params
  let gc = Z3native.context_of_params

  module ParamDescrs =
  struct
    type param_descrs = Z3native.param_descrs
    let gc = Z3native.context_of_param_descrs

    let validate (x:param_descrs) (p:params) = Z3native.params_validate (gc x) p x
    let get_kind (x:param_descrs) (name:Symbol.symbol) = param_kind_of_int (Z3native.param_descrs_get_kind (gc x) x name)

    let get_names (x:param_descrs) =
      let n = Z3native.param_descrs_size (gc x) x in
      let f i = Z3native.param_descrs_get_name (gc x) x i in
      mk_list f n

    let get_size (x:param_descrs) = Z3native.param_descrs_size (gc x) x
    let to_string (x:param_descrs) = Z3native.param_descrs_to_string (gc x) x
  end

  let add_bool (x:params) (name:Symbol.symbol) (value:bool) = Z3native.params_set_bool (gc x) x name value
  let add_int (x:params)  (name:Symbol.symbol) (value:int) = Z3native.params_set_uint (gc x) x name value
  let add_float (x:params) (name:Symbol.symbol) (value:float) = Z3native.params_set_double (gc x) x name value
  let add_symbol (x:params) (name:Symbol.symbol) (value:Symbol.symbol) = Z3native.params_set_symbol (gc x) x name value
  let mk_params (ctx:context) = Z3native.mk_params ctx
  let to_string (x:params) = Z3native.params_to_string (gc x) x

  let update_param_value (ctx:context) (id:string) (value:string) = Z3native.update_param_value ctx id value
  let set_print_mode (ctx:context) (value:ast_print_mode) = Z3native.set_ast_print_mode ctx (int_of_ast_print_mode value)
end

(** General expressions (terms) *)
and Expr :
sig
  type expr = AST.ast
  val gc : expr -> context
  val ast_of_expr  :  expr -> AST.ast
  val expr_of_ast  :  AST.ast -> expr
  val expr_of_func_app : context -> FuncDecl.func_decl -> expr list -> expr
  val simplify : expr -> Params.params option -> expr
  val get_simplify_help : context -> string
  val get_simplify_parameter_descrs : context -> Params.ParamDescrs.param_descrs
  val get_func_decl : expr -> FuncDecl.func_decl
  val get_num_args : expr -> int
  val get_args : expr -> expr list
  val update : expr -> expr list -> expr
  val substitute : expr -> expr list -> expr list -> expr
  val substitute_one : expr -> expr -> expr -> expr
  val substitute_vars : expr -> expr list -> expr
  val translate : expr -> context -> expr
  val to_string : expr -> string
  val is_numeral : expr -> bool
  val is_well_sorted : expr -> bool
  val get_sort : expr -> Sort.sort
  val is_const : expr -> bool
  val mk_const : context -> Symbol.symbol -> Sort.sort -> expr
  val mk_const_s : context -> string -> Sort.sort -> expr
  val mk_const_f : context -> FuncDecl.func_decl -> expr
  val mk_fresh_const : context -> string -> Sort.sort -> expr
  val mk_app : context -> FuncDecl.func_decl -> expr list -> expr
  val mk_numeral_string : context -> string -> Sort.sort -> expr
  val mk_numeral_int : context -> int -> Sort.sort -> expr
  val equal : expr -> expr -> bool
  val compare : expr -> expr -> int
end = struct
  type expr = AST.ast
  let gc = Z3native.context_of_ast

  let expr_of_ast a =
    let q = Z3enums.ast_kind_of_int (Z3native.get_ast_kind (gc a) a) in
    if q <> Z3enums.APP_AST && q <> VAR_AST && q <> QUANTIFIER_AST && q <> NUMERAL_AST then
      raise (Error "Invalid coercion")
    else
      a

  let ast_of_expr e = e

  let expr_of_func_app ctx f args =
    Z3native.mk_app ctx f (List.length args) args

  let simplify (x:expr) (p:Params.params option) =
    match p with
    | None -> Z3native.simplify (gc x) x
    | Some pp -> Z3native.simplify_ex (gc x) x pp

  let get_simplify_help = Z3native.simplify_get_help
  let get_simplify_parameter_descrs = Z3native.simplify_get_param_descrs
  let get_func_decl (x:expr) = Z3native.get_app_decl (gc x) x
  let get_num_args (x:expr) = Z3native.get_app_num_args (gc x) x
  let get_args (x:expr) =
    let n = get_num_args x in
    let f i = Z3native.get_app_arg (gc x) x i in
    mk_list f n

  let update (x:expr) (args:expr list) =
    if AST.is_app x && List.length args <> get_num_args x then
      raise (Error "Number of arguments does not match")
    else
      Z3native.update_term (gc x) x (List.length args) args

  let substitute (x:expr) (from:expr list) (to_:expr list) =
    let len = List.length from in
    if List.length to_ <> len then
      raise (Error "Argument sizes do not match")
    else
      Z3native.substitute (gc x) x len from to_

  let substitute_one x from to_ = substitute x [ from ] [ to_ ]
  let substitute_vars x to_ =
    Z3native.substitute_vars (gc x) x (List.length to_) to_

  let translate (x:expr) to_ctx =
    if gc x = to_ctx then
      x
    else
      Z3native.translate (gc x) x to_ctx

  let to_string (x:expr) = Z3native.ast_to_string (gc x) x
  let is_numeral (x:expr) = Z3native.is_numeral_ast (gc x) x
  let is_well_sorted (x:expr) = Z3native.is_well_sorted (gc x) x
  let get_sort (x:expr) = Z3native.get_sort (gc x) x
  let is_const (x:expr) =
    AST.is_app x
    && get_num_args x = 0
    && FuncDecl.get_domain_size (get_func_decl x) = 0

  let mk_const (ctx:context) (name:Symbol.symbol) (range:Sort.sort) = Z3native.mk_const ctx name range
  let mk_const_s (ctx:context) (name:string) (range:Sort.sort) = mk_const ctx (Symbol.mk_string ctx name) range
  let mk_const_f (ctx:context) (f:FuncDecl.func_decl) = expr_of_func_app ctx f []
  let mk_fresh_const (ctx:context) (prefix:string) (range:Sort.sort) = Z3native.mk_fresh_const ctx prefix range
  let mk_app (ctx:context) (f:FuncDecl.func_decl) (args:expr list) = expr_of_func_app ctx f args
  let mk_numeral_string (ctx:context) (v:string) (ty:Sort.sort) = Z3native.mk_numeral ctx v ty
  let mk_numeral_int (ctx:context) (v:int) (ty:Sort.sort) = Z3native.mk_int ctx v ty
  let equal (a:expr) (b:expr) = AST.equal a b
  let compare (a:expr) (b:expr) = AST.compare a b
end

open FuncDecl
open Expr

module Boolean =
struct
  let mk_sort = Z3native.mk_bool_sort
  let mk_const (ctx:context) (name:Symbol.symbol) = Expr.mk_const ctx name (mk_sort ctx)
  let mk_const_s (ctx:context) (name:string) = mk_const ctx (Symbol.mk_string ctx name)
  let mk_true = Z3native.mk_true
  let mk_false = Z3native.mk_false
  let mk_val (ctx:context) (value:bool) = if value then mk_true ctx else mk_false ctx
  let mk_not = Z3native.mk_not
  let mk_ite = Z3native.mk_ite
  let mk_iff = Z3native.mk_iff
  let mk_implies = Z3native.mk_implies
  let mk_xor = Z3native.mk_xor

  let mk_and ctx args = Z3native.mk_and ctx (List.length args) args

  let mk_or ctx args = Z3native.mk_or ctx (List.length args) args

  let mk_eq = Z3native.mk_eq
  let mk_distinct ctx args = Z3native.mk_distinct ctx (List.length args) args

  let get_bool_value x = lbool_of_int (Z3native.get_bool_value (gc x) x)

  let is_bool x =
    AST.is_expr x
    && Z3native.is_eq_sort (gc x) (Z3native.mk_bool_sort (gc x)) (Z3native.get_sort (gc x) x)

  let is_true x = AST.is_app x && FuncDecl.get_decl_kind (get_func_decl x) = OP_TRUE
  let is_false x = AST.is_app x && FuncDecl.get_decl_kind (get_func_decl x) = OP_FALSE
  let is_eq x = AST.is_app x && FuncDecl.get_decl_kind (get_func_decl x) = OP_EQ
  let is_distinct x = AST.is_app x && FuncDecl.get_decl_kind (get_func_decl x) = OP_DISTINCT
  let is_ite x = AST.is_app x && FuncDecl.get_decl_kind (get_func_decl x) = OP_ITE
  let is_and x = AST.is_app x && FuncDecl.get_decl_kind (get_func_decl x) = OP_AND
  let is_or x = AST.is_app x && FuncDecl.get_decl_kind (get_func_decl x) = OP_OR
  let is_iff x = AST.is_app x && FuncDecl.get_decl_kind (get_func_decl x) = OP_IFF
  let is_xor x = AST.is_app x && FuncDecl.get_decl_kind (get_func_decl x) = OP_XOR
  let is_not x = AST.is_app x && FuncDecl.get_decl_kind (get_func_decl x) = OP_NOT
  let is_implies x = AST.is_app x && FuncDecl.get_decl_kind (get_func_decl x) = OP_IMPLIES
end


module Quantifier =
struct
  type quantifier = AST.ast
  let gc = Z3native.context_of_ast

  let expr_of_quantifier q = q

  let quantifier_of_expr e =
    let q = Z3enums.ast_kind_of_int (Z3native.get_ast_kind (gc e) e) in
    if q <> Z3enums.QUANTIFIER_AST then
      raise (Error "Invalid coercion")
    else
      e

  module Pattern =
  struct
    type pattern = Z3native.pattern
    let gc = Z3native.context_of_ast

    let get_num_terms x = Z3native.get_pattern_num_terms (gc x) x

    let get_terms x =
      let n = get_num_terms x in
      let f i = Z3native.get_pattern (gc x) x i in
      mk_list f n

    let to_string x = Z3native.pattern_to_string (gc x) x
  end

  let get_index (x:expr) =
    if not (AST.is_var x) then
      raise (Error "Term is not a bound variable.")
    else
      Z3native.get_index_value (gc x) x

  let is_universal x = Z3native.is_quantifier_forall (gc x) x
  let is_existential x = not (is_universal x)
  let get_weight x = Z3native.get_quantifier_weight (gc x) x
  let get_num_patterns x = Z3native.get_quantifier_num_patterns (gc x) x
  let get_patterns x =
    let n = get_num_patterns x in
    let f i = Z3native.get_quantifier_pattern_ast (gc x) x i in
    mk_list f n

  let get_num_no_patterns x = Z3native.get_quantifier_num_no_patterns (gc x) x

  let get_no_patterns x =
    let n = get_num_patterns x in
    let f i = Z3native.get_quantifier_no_pattern_ast (gc x) x i in
    mk_list f n

  let get_num_bound x = Z3native.get_quantifier_num_bound (gc x) x

  let get_bound_variable_names x =
    let n = get_num_bound x in
    let f i = Z3native.get_quantifier_bound_name (gc x) x i in
    mk_list f n

  let get_bound_variable_sorts x =
    let n = get_num_bound x in
    let f i = Z3native.get_quantifier_bound_sort (gc x) x i in
    mk_list f n

  let get_body x = Z3native.get_quantifier_body (gc x) x
  let mk_bound = Z3native.mk_bound

  let mk_pattern ctx terms =
    let len = List.length terms in
    if len = 0 then
      raise (Error "Cannot create a pattern from zero terms")
    else
      Z3native.mk_pattern ctx len terms

  let _internal_mk_quantifier ~universal ctx sorts names body weight patterns nopatterns quantifier_id skolem_id =
    let len = List.length sorts in
    if List.length names <> len then
      raise (Error "Number of sorts does not match number of names")
    else
      match nopatterns, quantifier_id, skolem_id with
      | [], None, None ->
        Z3native.mk_quantifier ctx universal
          (match weight with | None -> 1 | Some x -> x)
          (List.length patterns) patterns
          len sorts
          names body
      | _ ->
        Z3native.mk_quantifier_ex ctx universal
          (match weight with | None -> 1 | Some x -> x)
          (match quantifier_id with | None -> Z3native.mk_null_symbol ctx | Some x -> x)
          (match skolem_id with | None -> Z3native.mk_null_symbol ctx | Some x -> x)
          (List.length patterns) patterns
          (List.length nopatterns) nopatterns
          len sorts
          names body

  let _internal_mk_quantifier_const ~universal ctx bound_constants body weight patterns nopatterns quantifier_id skolem_id =
    match nopatterns, quantifier_id, skolem_id with
    | [], None, None ->
      Z3native.mk_quantifier_const ctx universal
        (match weight with | None -> 1 | Some x -> x)
        (List.length bound_constants) bound_constants
        (List.length patterns) patterns
        body
    | _ ->
      Z3native.mk_quantifier_const_ex ctx universal
        (match weight with | None -> 1 | Some x -> x)
        (match quantifier_id with | None -> Z3native.mk_null_symbol ctx | Some x -> x)
        (match skolem_id with | None -> Z3native.mk_null_symbol ctx | Some x -> x)
        (List.length bound_constants) bound_constants
        (List.length patterns) patterns
        (List.length nopatterns) nopatterns
        body

  let mk_forall = _internal_mk_quantifier ~universal:true
  let mk_forall_const = _internal_mk_quantifier_const ~universal:true
  let mk_exists = _internal_mk_quantifier ~universal:false
  let mk_exists_const = _internal_mk_quantifier_const ~universal:false

  let mk_quantifier (ctx:context) (universal:bool) (sorts:Sort.sort list) (names:Symbol.symbol list) (body:expr) (weight:int option) (patterns:Pattern.pattern list) (nopatterns:expr list) (quantifier_id:Symbol.symbol option) (skolem_id:Symbol.symbol option) =
    if universal then
      mk_forall ctx sorts names body weight patterns nopatterns quantifier_id skolem_id
    else
      mk_exists ctx sorts names body weight patterns nopatterns quantifier_id skolem_id

  let mk_quantifier (ctx:context) (universal:bool) (bound_constants:expr list) (body:expr) (weight:int option) (patterns:Pattern.pattern list) (nopatterns:expr list) (quantifier_id:Symbol.symbol option) (skolem_id:Symbol.symbol option) =
    if universal then
      mk_forall_const ctx bound_constants body weight patterns nopatterns quantifier_id skolem_id
    else
      mk_exists_const ctx bound_constants body weight patterns nopatterns quantifier_id skolem_id

  let to_string x = Expr.to_string x
end

module Z3Array =
struct
  let mk_sort = Z3native.mk_array_sort
  let is_store x = AST.is_app x && FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_STORE
  let is_select x = AST.is_app x && FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_SELECT
  let is_constant_array x = AST.is_app x && FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_CONST_ARRAY
  let is_default_array x = AST.is_app x && FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_ARRAY_DEFAULT
  let is_array_map x = AST.is_app x && FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_ARRAY_MAP
  let is_as_array x = AST.is_app x && FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_AS_ARRAY

  let is_array x =
    Z3native.is_app (Expr.gc x) x &&
    sort_kind_of_int (Z3native.get_sort_kind (Expr.gc x) (Z3native.get_sort (Expr.gc x) x)) = ARRAY_SORT

  let get_domain x = Z3native.get_array_sort_domain (Sort.gc x) x
  let get_range x = Z3native.get_array_sort_range (Sort.gc x) x

  let mk_const ctx name domain range = Expr.mk_const ctx name (mk_sort ctx domain range)

  let mk_const_s ctx name domain range = mk_const ctx (Symbol.mk_string ctx name) domain range

  let mk_select = Z3native.mk_select
  let mk_store = Z3native.mk_store
  let mk_const_array = Z3native.mk_const_array

  let mk_map ctx f args =
    Z3native.mk_map ctx f (List.length args) args

  let mk_term_array = Z3native.mk_array_default
  let mk_array_ext = Z3native.mk_array_ext
end


module Set =
struct
  let mk_sort = Z3native.mk_set_sort

  let is_union (x:expr) = AST.is_app x && FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_SET_UNION
  let is_intersect (x:expr) = AST.is_app x && FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_SET_INTERSECT
  let is_difference (x:expr) = AST.is_app x && FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_SET_DIFFERENCE
  let is_complement (x:expr) = AST.is_app x && FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_SET_COMPLEMENT
  let is_subset (x:expr) = AST.is_app x && FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_SET_SUBSET

  let mk_empty = Z3native.mk_empty_set
  let mk_full = Z3native.mk_full_set
  let mk_set_add = Z3native.mk_set_add
  let mk_del = Z3native.mk_set_del
  let mk_union ctx args =
    Z3native.mk_set_union ctx (List.length args) args

  let mk_intersection ctx args =
    Z3native.mk_set_intersect ctx (List.length args) args

  let mk_difference = Z3native.mk_set_difference
  let mk_complement = Z3native.mk_set_complement
  let mk_membership = Z3native.mk_set_member
  let mk_subset = Z3native.mk_set_subset
end


module FiniteDomain =
struct
  let mk_sort = Z3native.mk_finite_domain_sort
  let mk_sort_s ctx name size = mk_sort ctx (Symbol.mk_string ctx name) size

  let is_finite_domain (x:expr) =
    let nc = Expr.gc x in
    Z3native.is_app nc x &&
    sort_kind_of_int (Z3native.get_sort_kind nc (Z3native.get_sort nc x)) = FINITE_DOMAIN_SORT

  let is_lt (x:expr) = AST.is_app x && FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FD_LT

  let get_size x =
    match Z3native.get_finite_domain_sort_size (Sort.gc x) x with
    | true, v -> v
    | false, _ -> raise (Error "Conversion failed.")
end


module Relation =
struct
  let is_relation x =
    let nc = Expr.gc x in
    Z3native.is_app nc x
    && sort_kind_of_int (Z3native.get_sort_kind nc (Z3native.get_sort nc x)) = RELATION_SORT

  let is_store (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_RA_STORE)
  let is_empty (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_RA_EMPTY)
  let is_is_empty (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_RA_IS_EMPTY)
  let is_join (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_RA_JOIN)
  let is_union (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_RA_UNION)
  let is_widen (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_RA_WIDEN)
  let is_project (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_RA_PROJECT)
  let is_filter (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_RA_FILTER)
  let is_negation_filter (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_RA_NEGATION_FILTER)
  let is_rename (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_RA_RENAME)
  let is_complement (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_RA_COMPLEMENT)
  let is_select (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_RA_SELECT)
  let is_clone (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_RA_CLONE)

  let get_arity (x:Sort.sort) = Z3native.get_relation_arity (Sort.gc x) x

  let get_column_sorts (x:Sort.sort) =
    let n = get_arity x in
    let f i = Z3native.get_relation_column (Sort.gc x) x i in
    mk_list f n
end


module Datatype =
struct
  module Constructor =
  struct
    type constructor = Z3native.constructor

    module FieldNumTable = Hashtbl.Make(struct
        type t = AST.ast
        let equal x y = AST.compare x y = 0
        let hash = AST.hash
      end)

    let _field_nums = FieldNumTable.create 0

    let create (ctx:context) (name:Symbol.symbol) (recognizer:Symbol.symbol) (field_names:Symbol.symbol list) (sorts:Sort.sort option list) (sort_refs:int list) =
      let n = List.length field_names in
      if n <> List.length sorts then
        raise (Error "Number of field names does not match number of sorts")
      else
      if n <> List.length sort_refs then
        raise (Error "Number of field names does not match number of sort refs")
      else
        let no = Z3native.mk_constructor ctx name
            recognizer
            n
            field_names
            (let f x = match x with None -> Z3native.mk_null_ast ctx | Some s -> s in
             List.map f sorts)
            sort_refs in
        FieldNumTable.add _field_nums no n;
        no

    let get_num_fields (x:constructor) = FieldNumTable.find _field_nums x

    let get_constructor_decl (x:constructor) =
      let (a, _, _) = (Z3native.query_constructor (gc x) x (get_num_fields x)) in
      a

    let get_tester_decl (x:constructor) =
      let (_, b, _) = (Z3native.query_constructor (gc x) x (get_num_fields x)) in
      b

    let get_accessor_decls (x:constructor) =
      let (_, _, c) = (Z3native.query_constructor (gc x) x (get_num_fields x)) in
      c
  end

  module ConstructorList =
  struct
    type constructor_list = Z3native.constructor_list

    let create (ctx:context) (c:Constructor.constructor list) =
      Z3native.mk_constructor_list ctx (List.length c) c
  end

  let mk_constructor (ctx:context) (name:Symbol.symbol) (recognizer:Symbol.symbol) (field_names:Symbol.symbol list) (sorts:Sort.sort option list) (sort_refs:int list) =
    Constructor.create ctx name recognizer field_names sorts sort_refs

  let mk_constructor_s (ctx:context) (name:string) (recognizer:Symbol.symbol) (field_names:Symbol.symbol list) (sorts:Sort.sort option list) (sort_refs:int list) =
    mk_constructor ctx (Symbol.mk_string ctx name) recognizer field_names sorts sort_refs

  let mk_sort (ctx:context) (name:Symbol.symbol) (constructors:Constructor.constructor list) =
    let (x,_) = Z3native.mk_datatype ctx name (List.length constructors) constructors in
    x

  let mk_sort_s (ctx:context) (name:string) (constructors:Constructor.constructor list) =
    mk_sort ctx (Symbol.mk_string ctx name) constructors

  let mk_sorts (ctx:context) (names:Symbol.symbol list) (c:Constructor.constructor list list) =
    let n = List.length names in
    let f e = ConstructorList.create ctx e in
    let cla = List.map f c in
    let (r, _) = Z3native.mk_datatypes ctx n names cla in
    r

  let mk_sorts_s (ctx:context) (names:string list) (c:Constructor.constructor list list) =
    mk_sorts ctx (List.map (fun x -> Symbol.mk_string ctx x) names) c

  let get_num_constructors (x:Sort.sort) = Z3native.get_datatype_sort_num_constructors (Sort.gc x) x

  let get_constructors (x:Sort.sort) =
    let n = get_num_constructors x in
    let f i = Z3native.get_datatype_sort_constructor (Sort.gc x) x i in
    mk_list f n

  let get_recognizers (x:Sort.sort) =
    let n = (get_num_constructors x) in
    let f i = Z3native.get_datatype_sort_recognizer (Sort.gc x) x i in
    mk_list f n

  let get_accessors (x:Sort.sort) =
    let n = (get_num_constructors x) in
    let f i = (
      let fd = Z3native.get_datatype_sort_constructor (Sort.gc x) x i in
      let ds = Z3native.get_domain_size (FuncDecl.gc fd) fd in
      let g j = Z3native.get_datatype_sort_constructor_accessor (Sort.gc x) x i j in
      mk_list g ds) in
    mk_list f n
end


module Enumeration =
struct
  let mk_sort (ctx:context) (name:Symbol.symbol) (enum_names:Symbol.symbol list) =
    let (a, _, _) = Z3native.mk_enumeration_sort ctx name (List.length enum_names) enum_names in
    a

  let mk_sort_s (ctx:context) (name:string) (enum_names:string list) =
    mk_sort ctx (Symbol.mk_string ctx name) (Symbol.mk_strings ctx enum_names)

  let get_const_decls (x:Sort.sort) =
    let n = Z3native.get_datatype_sort_num_constructors (Sort.gc x) x  in
    let f i = Z3native.get_datatype_sort_constructor (Sort.gc x) x i in
    mk_list f n

  let get_const_decl (x:Sort.sort) (inx:int) = Z3native.get_datatype_sort_constructor (Sort.gc x) x inx

  let get_consts (x:Sort.sort) =
    let n = Z3native.get_datatype_sort_num_constructors (Sort.gc x) x  in
    let f i = Expr.mk_const_f (Sort.gc x) (get_const_decl x i) in
    mk_list f n

  let get_const (x:Sort.sort) (inx:int) = Expr.mk_const_f (Sort.gc x) (get_const_decl x inx)

  let get_tester_decls (x:Sort.sort) =
    let n = Z3native.get_datatype_sort_num_constructors (Sort.gc x) x  in
    let f i = Z3native.get_datatype_sort_recognizer (Sort.gc x) x i in
    mk_list f n

  let get_tester_decl (x:Sort.sort) (inx:int) = Z3native.get_datatype_sort_recognizer (Sort.gc x) x inx
end


module Z3List =
struct
  let mk_sort (ctx:context) (name:Symbol.symbol) (elem_sort:Sort.sort) =
    let (r, _, _, _, _, _, _) = Z3native.mk_list_sort ctx name elem_sort in
    r

  let mk_list_s (ctx:context) (name:string) elem_sort = mk_sort ctx (Symbol.mk_string ctx name) elem_sort
  let get_nil_decl (x:Sort.sort) = Z3native.get_datatype_sort_constructor (Sort.gc x) x 0
  let get_is_nil_decl (x:Sort.sort) = Z3native.get_datatype_sort_recognizer (Sort.gc x) x 0
  let get_cons_decl (x:Sort.sort) = Z3native.get_datatype_sort_constructor (Sort.gc x) x 1
  let get_is_cons_decl (x:Sort.sort) =Z3native.get_datatype_sort_recognizer (Sort.gc x) x 1
  let get_head_decl (x:Sort.sort) = Z3native.get_datatype_sort_constructor_accessor (Sort.gc x) x 1 0
  let get_tail_decl (x:Sort.sort) = Z3native.get_datatype_sort_constructor_accessor (Sort.gc x) x 1 1
  let nil (x:Sort.sort) = expr_of_func_app (Sort.gc x) (get_nil_decl x) []
end


module Tuple =
struct
  let mk_sort (ctx:context) (name:Symbol.symbol) (field_names:Symbol.symbol list) (field_sorts:Sort.sort list) =
    let (r, _, _) = Z3native.mk_tuple_sort ctx name (List.length field_names) field_names field_sorts in
    r

  let get_mk_decl (x:Sort.sort) = Z3native.get_tuple_sort_mk_decl (Sort.gc x) x
  let get_num_fields (x:Sort.sort) = Z3native.get_tuple_sort_num_fields (Sort.gc x) x

  let get_field_decls (x:Sort.sort) =
    let n = get_num_fields x in
    let f i =Z3native.get_tuple_sort_field_decl (Sort.gc x) x i in
    mk_list f n
end


module Arithmetic =
struct
  let is_int (x:expr) =
    ((sort_kind_of_int (Z3native.get_sort_kind (Expr.gc x) (Z3native.get_sort (Expr.gc x) x))) = INT_SORT)

  let is_arithmetic_numeral (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_ANUM)
  let is_le (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_LE)
  let is_ge (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_GE)
  let is_lt (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_LT)
  let is_gt (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_GT)
  let is_add (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_ADD)
  let is_sub (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_SUB)
  let is_uminus (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_UMINUS)
  let is_mul (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_MUL)
  let is_div (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_DIV)
  let is_idiv (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_IDIV)
  let is_remainder (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_REM)
  let is_modulus (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_MOD)
  let is_int2real (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_TO_REAL)
  let is_real2int (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_TO_INT)
  let is_real_is_int (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_IS_INT)
  let is_real (x:expr) = ((sort_kind_of_int (Z3native.get_sort_kind (Expr.gc x) (Z3native.get_sort (Expr.gc x) x))) = REAL_SORT)
  let is_int_numeral (x:expr) = (Expr.is_numeral x) && (is_int x)
  let is_rat_numeral (x:expr) = (Expr.is_numeral x) && (is_real x)
  let is_algebraic_number (x:expr) = Z3native.is_algebraic_number (Expr.gc x) x

  module Integer =
  struct
    let mk_sort = Z3native.mk_int_sort

    let get_int x =
      match Z3native.get_numeral_int (Expr.gc x) x with
      | true, v -> v
      | false, _ -> raise (Error "Conversion failed.")

    let get_big_int (x:expr) =
      if is_int_numeral x then
        let s = (Z3native.get_numeral_string (Expr.gc x) x) in
        Big_int.big_int_of_string s
      else
        raise (Error "Conversion failed.")

    let numeral_to_string (x:expr) = Z3native.get_numeral_string (Expr.gc x) x
    let mk_const (ctx:context) (name:Symbol.symbol) = Expr.mk_const ctx name (mk_sort ctx)
    let mk_const_s (ctx:context) (name:string) = mk_const ctx (Symbol.mk_string ctx name)
    let mk_mod = Z3native.mk_mod
    let mk_rem = Z3native.mk_rem
    let mk_numeral_s (ctx:context) (v:string) = Z3native.mk_numeral ctx v (mk_sort ctx)
    let mk_numeral_i (ctx:context) (v:int) = Z3native.mk_int ctx v (mk_sort ctx)
    let mk_int2real = Z3native.mk_int2real
    let mk_int2bv = Z3native.mk_int2bv
  end

  module Real =
  struct
    let mk_sort = Z3native.mk_real_sort
    let get_numerator x = Z3native.get_numerator (Expr.gc x) x
    let get_denominator x = Z3native.get_denominator (Expr.gc x) x

    let get_ratio x =
      if is_rat_numeral x then
        let s = Z3native.get_numeral_string (Expr.gc x) x in
        Ratio.ratio_of_string s
      else
        raise (Error "Conversion failed.")

    let to_decimal_string (x:expr) (precision:int) = Z3native.get_numeral_decimal_string (Expr.gc x) x precision
    let numeral_to_string (x:expr) = Z3native.get_numeral_string (Expr.gc x) x
    let mk_const (ctx:context) (name:Symbol.symbol) = Expr.mk_const ctx name (mk_sort ctx)
    let mk_const_s (ctx:context) (name:string) = mk_const ctx (Symbol.mk_string ctx name)
    let mk_numeral_nd (ctx:context) (num:int) (den:int) =
      if den = 0 then
        raise (Error "Denominator is zero")
      else
        Z3native.mk_real ctx num den

    let mk_numeral_s (ctx:context) (v:string) = Z3native.mk_numeral ctx v (mk_sort ctx)
    let mk_numeral_i (ctx:context) (v:int) = Z3native.mk_int ctx v (mk_sort ctx)
    let mk_is_integer = Z3native.mk_is_int
    let mk_real2int = Z3native.mk_real2int

    module AlgebraicNumber =
    struct
      let to_upper (x:expr) (precision:int) = Z3native.get_algebraic_number_upper (Expr.gc x) x precision
      let to_lower (x:expr) (precision:int) = Z3native.get_algebraic_number_lower (Expr.gc x) x precision
      let to_decimal_string (x:expr) (precision:int) = Z3native.get_numeral_decimal_string (Expr.gc x) x precision
      let numeral_to_string (x:expr) = Z3native.get_numeral_string (Expr.gc x) x
    end
  end

  let mk_add (ctx:context) (t:expr list) =
    Z3native.mk_add ctx (List.length t) t

  let mk_mul (ctx:context) (t:expr list) =
    Z3native.mk_mul ctx (List.length t) t

  let mk_sub (ctx:context) (t:expr list) =
    Z3native.mk_sub ctx (List.length t) t

  let mk_unary_minus = Z3native.mk_unary_minus
  let mk_div = Z3native.mk_div
  let mk_power = Z3native.mk_power
  let mk_lt = Z3native.mk_lt
  let mk_le = Z3native.mk_le
  let mk_gt = Z3native.mk_gt
  let mk_ge = Z3native.mk_ge
end


module BitVector =
struct
  let mk_sort (ctx:context) size = Z3native.mk_bv_sort ctx size
  let is_bv (x:expr) =
    ((sort_kind_of_int (Z3native.get_sort_kind (Expr.gc x) (Z3native.get_sort (Expr.gc x) x))) = BV_SORT)
  let is_bv_numeral (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BNUM)
  let is_bv_bit1 (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BIT1)
  let is_bv_bit0 (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BIT0)
  let is_bv_uminus (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BNEG)
  let is_bv_add (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BADD)
  let is_bv_sub (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BSUB)
  let is_bv_mul (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BMUL)
  let is_bv_sdiv (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BSDIV)
  let is_bv_udiv (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BUDIV)
  let is_bv_SRem (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BSREM)
  let is_bv_urem (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BUREM)
  let is_bv_smod (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BSMOD)
  let is_bv_sdiv0 (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BSDIV0)
  let is_bv_udiv0 (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BUDIV0)
  let is_bv_srem0 (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BSREM0)
  let is_bv_urem0 (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BUREM0)
  let is_bv_smod0 (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BSMOD0)
  let is_bv_ule (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_ULEQ)
  let is_bv_sle (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_SLEQ)
  let is_bv_uge (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_UGEQ)
  let is_bv_sge (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_SGEQ)
  let is_bv_ult (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_ULT)
  let is_bv_slt (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_SLT)
  let is_bv_ugt (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_UGT)
  let is_bv_sgt (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_SGT)
  let is_bv_and (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BAND)
  let is_bv_or (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BOR)
  let is_bv_not (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BNOT)
  let is_bv_xor (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BXOR)
  let is_bv_nand (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BNAND)
  let is_bv_nor (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BNOR)
  let is_bv_xnor (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BXNOR)
  let is_bv_concat (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_CONCAT)
  let is_bv_signextension (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_SIGN_EXT)
  let is_bv_zeroextension (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_ZERO_EXT)
  let is_bv_extract (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_EXTRACT)
  let is_bv_repeat (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_REPEAT)
  let is_bv_reduceor (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BREDOR)
  let is_bv_reduceand (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BREDAND)
  let is_bv_comp (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BCOMP)
  let is_bv_shiftleft (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BSHL)
  let is_bv_shiftrightlogical (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BLSHR)
  let is_bv_shiftrightarithmetic (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BASHR)
  let is_bv_rotateleft (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_ROTATE_LEFT)
  let is_bv_rotateright (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_ROTATE_RIGHT)
  let is_bv_rotateleftextended (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_EXT_ROTATE_LEFT)
  let is_bv_rotaterightextended (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_EXT_ROTATE_RIGHT)
  let is_int2bv (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_INT2BV)
  let is_bv2int (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_BV2INT)
  let is_bv_carry (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_CARRY)
  let is_bv_xor3 (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_XOR3)
  let get_size (x:Sort.sort) = Z3native.get_bv_sort_size (Sort.gc x) x

  let get_int (x:expr) =
    match Z3native.get_numeral_int (Expr.gc x) x with
    | true, v -> v
    | false, _ -> raise (Error "Conversion failed.")

  let numeral_to_string (x:expr) = Z3native.get_numeral_string (Expr.gc x) x
  let mk_const (ctx:context) (name:Symbol.symbol) (size:int) =
    Expr.mk_const ctx name (mk_sort ctx size)
  let mk_const_s (ctx:context) (name:string) (size:int) =
    mk_const ctx (Symbol.mk_string ctx name) size
  let mk_not = Z3native.mk_bvnot
  let mk_redand = Z3native.mk_bvredand
  let mk_redor = Z3native.mk_bvredor
  let mk_and = Z3native.mk_bvand
  let mk_or = Z3native.mk_bvor
  let mk_xor = Z3native.mk_bvxor
  let mk_nand = Z3native.mk_bvnand
  let mk_nor = Z3native.mk_bvnor
  let mk_xnor = Z3native.mk_bvxnor
  let mk_neg = Z3native.mk_bvneg
  let mk_add = Z3native.mk_bvadd
  let mk_sub = Z3native.mk_bvsub
  let mk_mul = Z3native.mk_bvmul
  let mk_udiv = Z3native.mk_bvudiv
  let mk_sdiv = Z3native.mk_bvsdiv
  let mk_urem = Z3native.mk_bvurem
  let mk_srem = Z3native.mk_bvsrem
  let mk_smod = Z3native.mk_bvsmod
  let mk_ult = Z3native.mk_bvult
  let mk_slt = Z3native.mk_bvslt
  let mk_ule = Z3native.mk_bvule
  let mk_sle = Z3native.mk_bvsle
  let mk_uge = Z3native.mk_bvuge
  let mk_sge = Z3native.mk_bvsge
  let mk_ugt = Z3native.mk_bvugt
  let mk_sgt = Z3native.mk_bvsgt
  let mk_concat = Z3native.mk_concat
  let mk_extract = Z3native.mk_extract
  let mk_sign_ext = Z3native.mk_sign_ext
  let mk_zero_ext = Z3native.mk_zero_ext
  let mk_repeat = Z3native.mk_repeat
  let mk_shl = Z3native.mk_bvshl
  let mk_lshr = Z3native.mk_bvlshr
  let mk_ashr = Z3native.mk_bvashr
  let mk_rotate_left = Z3native.mk_rotate_left
  let mk_rotate_right = Z3native.mk_rotate_right
  let mk_ext_rotate_left = Z3native.mk_ext_rotate_left
  let mk_ext_rotate_right = Z3native.mk_ext_rotate_right
  let mk_bv2int = Z3native.mk_bv2int
  let mk_add_no_overflow = Z3native.mk_bvadd_no_overflow
  let mk_add_no_underflow = Z3native.mk_bvadd_no_underflow
  let mk_sub_no_overflow = Z3native.mk_bvsub_no_overflow
  let mk_sub_no_underflow = Z3native.mk_bvsub_no_underflow
  let mk_sdiv_no_overflow = Z3native.mk_bvsdiv_no_overflow
  let mk_neg_no_overflow = Z3native.mk_bvneg_no_overflow
  let mk_mul_no_overflow = Z3native.mk_bvmul_no_overflow
  let mk_mul_no_underflow = Z3native.mk_bvmul_no_underflow
  let mk_numeral ctx v size = Z3native.mk_numeral ctx v (mk_sort ctx size)
end

module Seq =
struct
  let mk_seq_sort  = Z3native.mk_seq_sort
  let is_seq_sort = Z3native.is_seq_sort 
  let mk_re_sort = Z3native.mk_re_sort
  let is_re_sort = Z3native.is_re_sort
  let mk_string_sort = Z3native.mk_string_sort
  let is_string_sort = Z3native.is_string_sort
  let mk_string = Z3native.mk_string
  let is_string = Z3native.is_string
  let get_string = Z3native.get_string
  let mk_seq_empty = Z3native.mk_seq_empty
  let mk_seq_unit = Z3native.mk_seq_unit
  let mk_seq_concat ctx args = Z3native.mk_seq_concat ctx (List.length args) args
  let mk_seq_prefix = Z3native.mk_seq_prefix
  let mk_seq_suffix = Z3native.mk_seq_suffix
  let mk_seq_contains = Z3native.mk_seq_contains 
  let mk_seq_extract = Z3native.mk_seq_extract
  let mk_seq_replace = Z3native.mk_seq_replace
  let mk_seq_at = Z3native.mk_seq_at
  let mk_seq_length = Z3native.mk_seq_length
  let mk_seq_index = Z3native.mk_seq_index
  let mk_str_to_int = Z3native.mk_str_to_int
  let mk_int_to_str = Z3native.mk_int_to_str
  let mk_seq_to_re = Z3native.mk_seq_to_re
  let mk_seq_in_re = Z3native.mk_seq_in_re
  let mk_re_plus = Z3native.mk_re_plus
  let mk_re_star = Z3native.mk_re_star
  let mk_re_option = Z3native.mk_re_option
  let mk_re_union ctx args = Z3native.mk_re_union ctx (List.length args) args
  let mk_re_concat ctx args = Z3native.mk_re_concat ctx (List.length args) args
  let mk_re_range = Z3native.mk_re_range
  let mk_re_loop = Z3native.mk_re_loop
  let mk_re_intersect = Z3native.mk_re_intersect
  let mk_re_complement = Z3native.mk_re_complement
  let mk_re_empty = Z3native.mk_re_empty
  let mk_re_full = Z3native.mk_re_full
end

module FloatingPoint =
struct
  module RoundingMode =
  struct
    let mk_sort = Z3native.mk_fpa_rounding_mode_sort
    let is_fprm x = Sort.get_sort_kind (Expr.get_sort x) = ROUNDING_MODE_SORT
    let mk_round_nearest_ties_to_even = Z3native.mk_fpa_round_nearest_ties_to_even
    let mk_rne = Z3native.mk_fpa_rne
    let mk_round_nearest_ties_to_away = Z3native.mk_fpa_round_nearest_ties_to_away
    let mk_rna = Z3native.mk_fpa_rna
    let mk_round_toward_positive = Z3native.mk_fpa_round_toward_positive
    let mk_rtp = Z3native.mk_fpa_rtp
    let mk_round_toward_negative = Z3native.mk_fpa_round_toward_negative
    let mk_rtn = Z3native.mk_fpa_rtn
    let mk_round_toward_zero = Z3native.mk_fpa_round_toward_zero
    let mk_rtz = Z3native.mk_fpa_rtz
  end

  let mk_sort = Z3native.mk_fpa_sort
  let mk_sort_half = Z3native.mk_fpa_sort_half
  let mk_sort_16 = Z3native.mk_fpa_sort_16
  let mk_sort_single = Z3native.mk_fpa_sort_single
  let mk_sort_32 = Z3native.mk_fpa_sort_32
  let mk_sort_double = Z3native.mk_fpa_sort_double
  let mk_sort_64 = Z3native.mk_fpa_sort_64
  let mk_sort_quadruple = Z3native.mk_fpa_sort_quadruple
  let mk_sort_128 = Z3native.mk_fpa_sort_128

  let mk_nan = Z3native.mk_fpa_nan
  let mk_inf = Z3native.mk_fpa_inf
  let mk_zero = Z3native.mk_fpa_zero
  let mk_fp = Z3native.mk_fpa_fp
  let mk_numeral_f = Z3native.mk_fpa_numeral_double
  let mk_numeral_i = Z3native.mk_fpa_numeral_int
  let mk_numeral_i_u = Z3native.mk_fpa_numeral_int64_uint64
  let mk_numeral_s = Z3native.mk_numeral

  let is_fp (x:expr) = (Sort.get_sort_kind (Expr.get_sort x)) = FLOATING_POINT_SORT
  let is_abs (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_ABS)
  let is_neg (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_NEG)
  let is_add (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_ADD)
  let is_sub (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_SUB)
  let is_mul (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_MUL)
  let is_div (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_DIV)
  let is_fma (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_FMA)
  let is_sqrt (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_SQRT)
  let is_rem (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_REM)
  let is_round_to_integral (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_ROUND_TO_INTEGRAL)
  let is_min (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_MIN)
  let is_max (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_MAX)
  let is_leq (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_LE)
  let is_lt (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_LT)
  let is_geq (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_GE)
  let is_gt (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_GT)
  let is_eq (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_EQ)
  let is_is_normal (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_IS_NORMAL)
  let is_is_subnormal (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_IS_SUBNORMAL)
  let is_is_zero (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_IS_ZERO)
  let is_is_infinite (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_IS_INF)
  let is_is_nan (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_IS_NAN)
  let is_is_negative (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_IS_NEGATIVE)
  let is_is_positive (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_IS_POSITIVE)
  let is_to_fp (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_TO_FP)
  let is_to_fp_unsigned (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_TO_FP_UNSIGNED)
  let is_to_ubv (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_TO_UBV)
  let is_to_sbv (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_TO_SBV)
  let is_to_real (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_TO_REAL)
  let is_to_ieee_bv (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_FPA_TO_IEEE_BV)

  let numeral_to_string (x:expr) = Z3native.get_numeral_string (Expr.gc x) x

  let mk_const = Expr.mk_const
  let mk_const_s = Expr.mk_const_s

  let mk_abs = Z3native.mk_fpa_abs
  let mk_neg = Z3native.mk_fpa_neg
  let mk_add = Z3native.mk_fpa_add
  let mk_sub = Z3native.mk_fpa_sub
  let mk_mul = Z3native.mk_fpa_mul
  let mk_div = Z3native.mk_fpa_div
  let mk_fma = Z3native.mk_fpa_fma
  let mk_sqrt = Z3native.mk_fpa_sqrt
  let mk_rem = Z3native.mk_fpa_rem
  let mk_round_to_integral = Z3native.mk_fpa_round_to_integral
  let mk_min = Z3native.mk_fpa_min
  let mk_max = Z3native.mk_fpa_max
  let mk_leq = Z3native.mk_fpa_leq
  let mk_lt = Z3native.mk_fpa_lt
  let mk_geq = Z3native.mk_fpa_geq
  let mk_gt = Z3native.mk_fpa_gt
  let mk_eq = Z3native.mk_fpa_eq
  let mk_is_normal = Z3native.mk_fpa_is_normal
  let mk_is_subnormal = Z3native.mk_fpa_is_subnormal
  let mk_is_zero = Z3native.mk_fpa_is_zero
  let mk_is_infinite = Z3native.mk_fpa_is_infinite
  let mk_is_nan = Z3native.mk_fpa_is_nan
  let mk_is_negative = Z3native.mk_fpa_is_negative
  let mk_is_positive = Z3native.mk_fpa_is_positive
  let mk_to_fp_bv = Z3native.mk_fpa_to_fp_bv
  let mk_to_fp_float = Z3native.mk_fpa_to_fp_float
  let mk_to_fp_real = Z3native.mk_fpa_to_fp_real
  let mk_to_fp_signed = Z3native.mk_fpa_to_fp_signed
  let mk_to_fp_unsigned = Z3native.mk_fpa_to_fp_unsigned
  let mk_to_ubv = Z3native.mk_fpa_to_ubv
  let mk_to_sbv = Z3native.mk_fpa_to_sbv
  let mk_to_real = Z3native.mk_fpa_to_real
  let get_ebits = Z3native.fpa_get_ebits
  let get_sbits = Z3native.fpa_get_sbits
  let get_numeral_sign = Z3native.fpa_get_numeral_sign
  let get_numeral_sign_bv = Z3native.fpa_get_numeral_sign_bv
  let get_numeral_exponent_string = Z3native.fpa_get_numeral_exponent_string
  let get_numeral_exponent_int = Z3native.fpa_get_numeral_exponent_int64
  let get_numeral_exponent_bv = Z3native.fpa_get_numeral_exponent_bv
  let get_numeral_significand_string = Z3native.fpa_get_numeral_significand_string
  let get_numeral_significand_uint = Z3native.fpa_get_numeral_significand_uint64
  let get_numeral_significand_bv = Z3native.fpa_get_numeral_significand_bv
  let is_numeral_nan = Z3native.fpa_is_numeral_nan
  let is_numeral_inf = Z3native.fpa_is_numeral_inf
  let is_numeral_zero = Z3native.fpa_is_numeral_zero
  let is_numeral_normal = Z3native.fpa_is_numeral_normal
  let is_numeral_subnormal = Z3native.fpa_is_numeral_subnormal
  let is_numeral_positive = Z3native.fpa_is_numeral_positive
  let is_numeral_negative = Z3native.fpa_is_numeral_negative
  let mk_to_ieee_bv = Z3native.mk_fpa_to_ieee_bv
  let mk_to_fp_int_real = Z3native.mk_fpa_to_fp_int_real
  let numeral_to_string x = Z3native.get_numeral_string (Expr.gc x) x
end


module Proof =
struct
  let is_true (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_TRUE)
  let is_asserted (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_ASSERTED)
  let is_goal (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_GOAL)
  let is_oeq (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_OEQ)
  let is_modus_ponens (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_MODUS_PONENS)
  let is_reflexivity (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_REFLEXIVITY)
  let is_symmetry (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_SYMMETRY)
  let is_transitivity (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_TRANSITIVITY)
  let is_Transitivity_star (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_TRANSITIVITY_STAR)
  let is_monotonicity (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_MONOTONICITY)
  let is_quant_intro (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_QUANT_INTRO)
  let is_distributivity (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_DISTRIBUTIVITY)
  let is_and_elimination (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_AND_ELIM)
  let is_or_elimination (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_NOT_OR_ELIM)
  let is_rewrite (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_REWRITE)
  let is_rewrite_star (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_REWRITE_STAR)
  let is_pull_quant (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_PULL_QUANT)
  let is_push_quant (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_PUSH_QUANT)
  let is_elim_unused_vars (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_ELIM_UNUSED_VARS)
  let is_der (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_DER)
  let is_quant_inst (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_QUANT_INST)
  let is_hypothesis (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_HYPOTHESIS)
  let is_lemma (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_LEMMA)
  let is_unit_resolution (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_UNIT_RESOLUTION)
  let is_iff_true (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_IFF_TRUE)
  let is_iff_false (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_IFF_FALSE)
  let is_commutativity (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_COMMUTATIVITY) (*  *)
  let is_def_axiom (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_DEF_AXIOM)
  let is_def_intro (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_DEF_INTRO)
  let is_apply_def (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_APPLY_DEF)
  let is_iff_oeq (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_IFF_OEQ)
  let is_nnf_pos (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_NNF_POS)
  let is_nnf_neg (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_NNF_NEG)
  let is_skolemize (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_SKOLEMIZE)
  let is_modus_ponens_oeq (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_MODUS_PONENS_OEQ)
  let is_theory_lemma (x:expr) = (AST.is_app x) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) = OP_PR_TH_LEMMA)
end


module Goal =
struct
  type goal = Z3native.goal
  let gc = Z3native.context_of_goal

  let get_precision (x:goal) = goal_prec_of_int (Z3native.goal_precision (gc x) x)
  let is_precise (x:goal) = (get_precision x) = GOAL_PRECISE
  let is_underapproximation (x:goal) = (get_precision x) = GOAL_UNDER
  let is_overapproximation (x:goal) = (get_precision x) = GOAL_OVER
  let is_garbage (x:goal) = (get_precision x) = GOAL_UNDER_OVER

  let add x constraints =
    List.iter (Z3native.goal_assert (gc x) x) constraints

  let is_inconsistent (x:goal) = Z3native.goal_inconsistent (gc x) x
  let get_depth (x:goal) = Z3native.goal_depth (gc x) x
  let reset (x:goal) =  Z3native.goal_reset (gc x) x
  let get_size (x:goal) = Z3native.goal_size (gc x) x

  let get_formulas (x:goal) =
    let n = get_size x in
    let f i = Z3native.goal_formula (gc x) x i in
    mk_list f n

  let get_num_exprs (x:goal) = Z3native.goal_num_exprs (gc x) x
  let is_decided_sat (x:goal) = Z3native.goal_is_decided_sat (gc x) x
  let is_decided_unsat (x:goal) = Z3native.goal_is_decided_unsat (gc x) x
  let translate (x:goal) (to_ctx:context) = Z3native.goal_translate (gc x) x to_ctx

  let simplify (x:goal) (p:Params.params option) =
    let tn = Z3native.mk_tactic (gc x) "simplify" in
    Z3native.tactic_inc_ref (gc x) tn;
    let arn = match p with
      | None -> Z3native.tactic_apply (gc x) tn x
      | Some pn -> Z3native.tactic_apply_ex (gc x) tn x pn
    in
    Z3native.apply_result_inc_ref (gc x) arn;
    let sg = Z3native.apply_result_get_num_subgoals (gc x) arn in
    let res = if sg = 0 then
        raise (Error "No subgoals")
      else
        Z3native.apply_result_get_subgoal (gc x) arn 0 in
    Z3native.apply_result_dec_ref (gc x) arn;
    Z3native.tactic_dec_ref (gc x) tn;
    res

  let mk_goal = Z3native.mk_goal

  let to_string (x:goal) = Z3native.goal_to_string (gc x) x

  let as_expr (x:goal) =
    match get_size x with
    | 0 -> Boolean.mk_true (gc x)
    | 1 -> List.hd (get_formulas x)
    | _ -> Boolean.mk_and (gc x) (get_formulas x)
end


module Model =
struct
  type model = Z3native.model
  let gc = Z3native.context_of_model

  module FuncInterp =
  struct
    type func_interp = Z3native.func_interp
    let gc = Z3native.context_of_func_interp

    module FuncEntry =
    struct
      type func_entry = Z3native.func_entry
      let gc = Z3native.context_of_func_entry

      let get_value (x:func_entry) = Z3native.func_entry_get_value (gc x) x
      let get_num_args (x:func_entry) = Z3native.func_entry_get_num_args (gc x) x

      let get_args (x:func_entry) =
        let n = get_num_args x in
        let f i = Z3native.func_entry_get_arg (gc x) x i in
        mk_list f n

      let to_string (x:func_entry) =
        let a = get_args x in
        let f c p = (p ^ (Expr.to_string c) ^ ", ") in
        "[" ^ List.fold_right f a ((Expr.to_string (get_value x)) ^ "]")
    end

    let get_num_entries (x:func_interp) = Z3native.func_interp_get_num_entries (gc x) x

    let get_entries (x:func_interp) =
      let n = get_num_entries x in
      let f i = Z3native.func_interp_get_entry (gc x) x i in
      mk_list f n

    let get_else (x:func_interp) = Z3native.func_interp_get_else (gc x) x

    let get_arity (x:func_interp) = Z3native.func_interp_get_arity (gc x) x

    let to_string (x:func_interp) =
      let f c p = (
        let n = FuncEntry.get_num_args c in
        p ^
        let g c p = (p ^ (Expr.to_string c) ^ ", ") in
        (if n > 1 then "[" else "") ^
        (List.fold_right
           g
           (FuncEntry.get_args c)
           ((if n > 1 then "]" else "") ^ " -> " ^ (Expr.to_string (FuncEntry.get_value c)) ^ ", "))) in
      List.fold_right f (get_entries x) ("else -> " ^ (Expr.to_string (get_else x)) ^ "]")
  end

  let get_const_interp (x:model) (f:func_decl) =
    if FuncDecl.get_arity f <> 0 ||
       (sort_kind_of_int (Z3native.get_sort_kind (FuncDecl.gc f) (Z3native.get_range (FuncDecl.gc f) f))) = ARRAY_SORT then
      raise (Error "Non-zero arity functions and arrays have FunctionInterpretations as a model. Use FuncInterp.")
    else
      let np = Z3native.model_get_const_interp (gc x) x f  in
      if Z3native.is_null_ast np then
        None
      else
        Some np

  let get_const_interp_e (x:model) (a:expr) = get_const_interp x (Expr.get_func_decl a)

  let rec get_func_interp (x:model) (f:func_decl) =
    let sk = sort_kind_of_int (Z3native.get_sort_kind (gc x) (Z3native.get_range (FuncDecl.gc f) f)) in
    if FuncDecl.get_arity f = 0 then
      let n = Z3native.model_get_const_interp (gc x) x f in
      if Z3native.is_null_ast n then
        None
      else
        match sk with
        | ARRAY_SORT ->
          if not (Z3native.is_as_array (gc x) n) then
            raise (Error "Argument was not an array constant")
          else
            let fd = Z3native.get_as_array_func_decl (gc x) n in
            get_func_interp x fd
        | _ -> raise (Error "Constant functions do not have a function interpretation; use ConstInterp");
    else
      let n = Z3native.model_get_func_interp (gc x) x f in
      if Z3native.is_null_func_interp n then None else Some n

  (** The number of constants that have an interpretation in the model. *)
  let get_num_consts (x:model) = Z3native.model_get_num_consts (gc x) x

  let get_const_decls (x:model) =
    let n = (get_num_consts x) in
    let f i = Z3native.model_get_const_decl (gc x) x i in
    mk_list f n

  let get_num_funcs (x:model) = Z3native.model_get_num_funcs (gc x) x

  let get_func_decls (x:model) =
    let n = (get_num_funcs x) in
    let f i = Z3native.model_get_func_decl (gc x) x i in
    mk_list f n

  let get_decls (x:model) =
    let n_funcs = get_num_funcs x in
    let n_consts = get_num_consts x in
    let f i = Z3native.model_get_func_decl (gc x) x i in
    let g i = Z3native.model_get_const_decl (gc x) x i in
    (mk_list f n_funcs) @ (mk_list g n_consts)

  let eval (x:model) (t:expr) (completion:bool) =
    match Z3native.model_eval (gc x) x t completion with
    | (false, _) -> None
    | (true, v) -> Some v

  let evaluate = eval
  let get_num_sorts (x:model) = Z3native.model_get_num_sorts (gc x) x

  let get_sorts (x:model) =
    let n = get_num_sorts x in
    let f i = Z3native.model_get_sort (gc x) x i in
    mk_list f n

  let sort_universe (x:model) (s:Sort.sort) =
    let av = Z3native.model_get_sort_universe (gc x) x s in
    AST.ASTVector.to_expr_list av

  let to_string (x:model) = Z3native.model_to_string (gc x) x
end


module Probe =
struct
  type probe = Z3native.probe

  let apply (x:probe) (g:Goal.goal) = Z3native.probe_apply (gc x) x g
  let get_num_probes = Z3native.get_num_probes

  let get_probe_names (ctx:context) =
    let n = get_num_probes ctx in
    let f i = Z3native.get_probe_name ctx i in
    mk_list f n

  let get_probe_description = Z3native.probe_get_descr
  let mk_probe = Z3native.mk_probe
  let const = Z3native.probe_const
  let lt = Z3native.probe_lt
  let gt = Z3native.probe_gt
  let le = Z3native.probe_le
  let ge = Z3native.probe_ge
  let eq = Z3native.probe_eq
  let and_ = Z3native.probe_and
  let or_ = Z3native.probe_or
  let not_ = Z3native.probe_not
end


module Tactic =
struct
  type tactic = Z3native.tactic
  let gc = Z3native.context_of_tactic

  module ApplyResult =
  struct
    type apply_result = Z3native.apply_result
    let gc = Z3native.context_of_apply_result

    let get_num_subgoals (x:apply_result) = Z3native.apply_result_get_num_subgoals (gc x) x

    let get_subgoals (x:apply_result) =
      let n = get_num_subgoals x in
      let f i = Z3native.apply_result_get_subgoal (gc x) x i in
      mk_list f n

    let get_subgoal (x:apply_result) (i:int) = Z3native.apply_result_get_subgoal (gc x) x i
    let to_string (x:apply_result) = Z3native.apply_result_to_string (gc x) x
  end

  let get_help (x:tactic) = Z3native.tactic_get_help (gc x) x
  let get_param_descrs (x:tactic) = Z3native.tactic_get_param_descrs (gc x) x

  let apply (x:tactic) (g:Goal.goal) (p:Params.params option) =
    match p with
    | None -> Z3native.tactic_apply (gc x) x g
    | Some pn -> Z3native.tactic_apply_ex (gc x) x g pn

  let get_num_tactics = Z3native.get_num_tactics

  let get_tactic_names (ctx:context) =
    let n = get_num_tactics ctx in
    let f i = Z3native.get_tactic_name ctx i in
    mk_list f n

  let get_tactic_description = Z3native.tactic_get_descr
  let mk_tactic = Z3native.mk_tactic

  let and_then (ctx:context) (t1:tactic) (t2:tactic) (ts:tactic list) =
    let f p c = (match p with
        | None -> Some c
        | Some(x) -> Some (Z3native.tactic_and_then ctx c x)) in
    match (List.fold_left f None ts) with
    | None -> Z3native.tactic_and_then ctx t1 t2
    | Some(x) -> let o = Z3native.tactic_and_then ctx t2 x in
      Z3native.tactic_and_then ctx t1 o

  let or_else = Z3native.tactic_or_else
  let try_for = Z3native.tactic_try_for
  let when_ = Z3native.tactic_when
  let cond = Z3native.tactic_cond
  let repeat = Z3native.tactic_repeat
  let skip = Z3native.tactic_skip
  let fail = Z3native.tactic_fail
  let fail_if = Z3native.tactic_fail_if
  let fail_if_not_decided = Z3native.tactic_fail_if_not_decided
  let using_params = Z3native.tactic_using_params
  let with_ = using_params
  let par_or (ctx:context) (t:tactic list) = Z3native.tactic_par_or ctx (List.length t) t
  let par_and_then = Z3native.tactic_par_and_then
  let interrupt = Z3native.interrupt
end


module Statistics =
struct
  type statistics = Z3native.stats
  let gc = Z3native.context_of_stats

  module Entry =
  struct
    type statistics_entry = {
      m_key:string;
      m_is_int:bool;
      m_is_float:bool;
      m_int:int;
      m_float:float }

    let create_si k v =
      { m_key = k; m_is_int = true; m_is_float = false; m_int = v; m_float = 0.0 }

    let create_sd k v =
      { m_key = k; m_is_int = false; m_is_float = true; m_int = 0; m_float = v }

    let get_key (x:statistics_entry) = x.m_key
    let get_int (x:statistics_entry) = x.m_int
    let get_float (x:statistics_entry) = x.m_float
    let is_int (x:statistics_entry) = x.m_is_int
    let is_float (x:statistics_entry) = x.m_is_float
    let to_string_value (x:statistics_entry) =
      if is_int x then
        string_of_int (get_int x)
      else if is_float x then
        string_of_float (get_float x)
      else
        raise (Error "Unknown statistical entry type")
    let to_string (x:statistics_entry) = (get_key x) ^ ": " ^ (to_string_value x)
  end

  let to_string (x:statistics) = Z3native.stats_to_string (gc x) x
  let get_size (x:statistics) = Z3native.stats_size (gc x) x

  let get_entries (x:statistics) =
    let n = get_size x in
    let f i =
      let k = Z3native.stats_get_key (gc x) x i in
      if Z3native.stats_is_uint (gc x) x i then
        Entry.create_si k (Z3native.stats_get_uint_value (gc x) x i)
      else
        Entry.create_sd k (Z3native.stats_get_double_value (gc x) x i)
    in
    mk_list f n

  let get_keys (x:statistics) =
    let n = get_size x in
    let f i = Z3native.stats_get_key (gc x) x i in
    mk_list f n

  let get (x:statistics) (key:string) =
    try Some(List.find (fun c -> Entry.get_key c = key) (get_entries x)) with
    | Not_found -> None
end


module Solver =
struct
  type solver = Z3native.solver
  type status = UNSATISFIABLE | UNKNOWN | SATISFIABLE
  let gc = Z3native.context_of_solver

  let string_of_status (s:status) = match s with
    | UNSATISFIABLE -> "unsatisfiable"
    | SATISFIABLE -> "satisfiable"
    | _ -> "unknown"

  let get_help (x:solver) = Z3native.solver_get_help (gc x) x
  let set_parameters (x:solver) (p:Params.params) = Z3native.solver_set_params (gc x) x p
  let get_param_descrs (x:solver) = Z3native.solver_get_param_descrs (gc x) x
  let get_num_scopes (x:solver) = Z3native.solver_get_num_scopes (gc x) x
  let push (x:solver) = Z3native.solver_push (gc x) x
  let pop (x:solver) (n:int) = Z3native.solver_pop (gc x) x n
  let reset (x:solver) = Z3native.solver_reset (gc x) x

  let add x constraints =
    List.iter (Z3native.solver_assert (gc x) x) constraints

  let assert_and_track_l x cs ps =
    try List.iter2 (Z3native.solver_assert_and_track (gc x) x) cs ps with
    | Invalid_argument _ -> raise (Error "Argument size mismatch")

  let assert_and_track x = Z3native.solver_assert_and_track (gc x) x

  let get_num_assertions x =
    let a = Z3native.solver_get_assertions (gc x) x in
    AST.ASTVector.get_size a

  let get_assertions x =
    let av = Z3native.solver_get_assertions (gc x) x in
    AST.ASTVector.to_expr_list av

  let check (x:solver) (assumptions:expr list) =
    let result =
      match assumptions with
      | [] -> Z3native.solver_check (gc x) x
      | _::_ ->
        Z3native.solver_check_assumptions (gc x) x (List.length assumptions) assumptions
    in
    match lbool_of_int result with
    | L_TRUE -> SATISFIABLE
    | L_FALSE -> UNSATISFIABLE
    | _ -> UNKNOWN

  let get_model x =
    let q = Z3native.solver_get_model (gc x) x in
    if Z3native.is_null_model q then None else Some q

  let get_proof x =
    let q = Z3native.solver_get_proof (gc x) x in
    if Z3native.is_null_ast q then None else Some q

  let get_unsat_core x =
    let av = Z3native.solver_get_unsat_core (gc x) x in
    AST.ASTVector.to_expr_list av

  let get_reason_unknown x =  Z3native.solver_get_reason_unknown (gc x) x
  let get_statistics x = Z3native.solver_get_statistics (gc x) x

  let mk_solver ctx logic =
    match logic with
    | None -> Z3native.mk_solver ctx
    | Some x -> Z3native.mk_solver_for_logic ctx x

  let mk_solver_s ctx logic = mk_solver ctx (Some (Symbol.mk_string ctx logic))
  let mk_simple_solver = Z3native.mk_simple_solver
  let mk_solver_t = Z3native.mk_solver_from_tactic
  let translate x = Z3native.solver_translate (gc x) x
  let to_string x = Z3native.solver_to_string (gc x) x
end


module Fixedpoint =
struct
  type fixedpoint = Z3native.fixedpoint
  let gc = Z3native.context_of_fixedpoint

  let get_help x = Z3native.fixedpoint_get_help (gc x) x
  let set_parameters x = Z3native.fixedpoint_set_params (gc x) x
  let get_param_descrs x = Z3native.fixedpoint_get_param_descrs (gc x) x

  let add x constraints =
    List.iter (Z3native.fixedpoint_assert (gc x) x) constraints

  let register_relation x = Z3native.fixedpoint_register_relation (gc x) x

  let add_rule (x:fixedpoint) (rule:expr) (name:Symbol.symbol option) =
    match name with
    | None -> Z3native.fixedpoint_add_rule (gc x) x rule (Z3native.mk_null_symbol (gc x))
    | Some y -> Z3native.fixedpoint_add_rule (gc x) x rule y

  let add_fact (x:fixedpoint) (pred:func_decl) (args:int list) =
    Z3native.fixedpoint_add_fact (gc x) x pred (List.length args) args

  let query (x:fixedpoint) (query:expr) =
    match lbool_of_int (Z3native.fixedpoint_query (gc x) x query) with
    | L_TRUE -> Solver.SATISFIABLE
    | L_FALSE -> Solver.UNSATISFIABLE
    | _ -> Solver.UNKNOWN

  let query_r (x:fixedpoint) (relations:func_decl list) =
    match lbool_of_int (Z3native.fixedpoint_query_relations (gc x) x (List.length relations) relations) with
    | L_TRUE -> Solver.SATISFIABLE
    | L_FALSE -> Solver.UNSATISFIABLE
    | _ -> Solver.UNKNOWN

  let push x = Z3native.fixedpoint_push (gc x) x
  let pop x = Z3native.fixedpoint_pop (gc x) x
  let update_rule x = Z3native.fixedpoint_update_rule (gc x) x

  let get_answer x =
    let q = Z3native.fixedpoint_get_answer (gc x) x in
    if Z3native.is_null_ast q then None else Some q

  let get_reason_unknown x = Z3native.fixedpoint_get_reason_unknown (gc x) x
  let get_num_levels x = Z3native.fixedpoint_get_num_levels (gc x) x

  let get_cover_delta (x:fixedpoint) (level:int) (predicate:func_decl) =
    let q = Z3native.fixedpoint_get_cover_delta (gc x) x level predicate in
    if Z3native.is_null_ast q then None else Some q

  let add_cover (x:fixedpoint) (level:int) (predicate:func_decl) (property:expr) =
    Z3native.fixedpoint_add_cover (gc x) x level predicate property

  let to_string (x:fixedpoint) = Z3native.fixedpoint_to_string (gc x) x 0 []

  let set_predicate_representation (x:fixedpoint) (f:func_decl) (kinds:Symbol.symbol list) =
    Z3native.fixedpoint_set_predicate_representation (gc x) x f (List.length kinds) kinds

  let to_string_q (x:fixedpoint) (queries:expr list) =
    Z3native.fixedpoint_to_string (gc x) x (List.length queries) queries

  let get_rules (x:fixedpoint) =
    let av = Z3native.fixedpoint_get_rules (gc x) x in
    AST.ASTVector.to_expr_list av

  let get_assertions (x:fixedpoint) =
    let av = Z3native.fixedpoint_get_assertions (gc x) x in
    (AST.ASTVector.to_expr_list av)

  let mk_fixedpoint (ctx:context) = Z3native.mk_fixedpoint ctx
  let get_statistics (x:fixedpoint) = Z3native.fixedpoint_get_statistics (gc x) x

  let parse_string (x:fixedpoint) (s:string) =
    let av = Z3native.fixedpoint_from_string (gc x) x s in
    AST.ASTVector.to_expr_list av

  let parse_file (x:fixedpoint) (filename:string) =
    let av = Z3native.fixedpoint_from_file (gc x) x filename in
    AST.ASTVector.to_expr_list av
end


module Optimize =
struct
  type optimize = Z3native.optimize
  type handle = { opt:optimize; h:int }

  let mk_handle opt h = { opt; h }

  let mk_opt (ctx:context) = Z3native.mk_optimize ctx
  let get_help (x:optimize) = Z3native.optimize_get_help (gc x) x
  let set_parameters (x:optimize) (p:Params.params) = Z3native.optimize_set_params (gc x) x p
  let get_param_descrs (x:optimize) = Z3native.optimize_get_param_descrs (gc x) x

  let add x constraints =
    List.iter (Z3native.optimize_assert (gc x) x) constraints

  let add_soft (x:optimize) (e:Expr.expr) (w:string) (s:Symbol.symbol) =
    mk_handle x (Z3native.optimize_assert_soft (gc x) x e w s)

  let maximize (x:optimize) (e:Expr.expr) = mk_handle x (Z3native.optimize_maximize (gc x) x e)
  let minimize (x:optimize) (e:Expr.expr) = mk_handle x (Z3native.optimize_minimize (gc x) x e)

  let check (x:optimize) =
    let r = lbool_of_int (Z3native.optimize_check (gc x) x) in
    match r with
    | L_TRUE -> Solver.SATISFIABLE
    | L_FALSE -> Solver.UNSATISFIABLE
    | _ -> Solver.UNKNOWN

  let get_model (x:optimize) =
    let q = Z3native.optimize_get_model (gc x) x in
    if Z3native.is_null_model q then None else Some q

  let get_lower (x:handle) = Z3native.optimize_get_lower (gc x.opt) x.opt x.h
  let get_upper (x:handle) = Z3native.optimize_get_upper (gc x.opt) x.opt x.h
  let push (x:optimize) = Z3native.optimize_push (gc x) x
  let pop (x:optimize) = Z3native.optimize_pop (gc x) x
  let get_reason_unknown (x:optimize) = Z3native.optimize_get_reason_unknown (gc x) x
  let to_string (x:optimize) = Z3native.optimize_to_string (gc x) x
  let get_statistics (x:optimize) = Z3native.optimize_get_statistics (gc x) x
  let from_file (x:optimize) (s:string) = Z3native.optimize_from_file (gc x) x s
  let from_string (x:optimize) (s:string) = Z3native.optimize_from_string (gc x) x s
  let get_assertions (x:optimize) = AST.ASTVector.to_expr_list (Z3native.optimize_get_assertions (gc x) x)
  let get_objectives (x:optimize) = AST.ASTVector.to_expr_list (Z3native.optimize_get_objectives (gc x) x)
end


module SMT =
struct
  let benchmark_to_smtstring (ctx:context) (name:string) (logic:string) (status:string) (attributes:string) (assumptions:expr list) (formula:expr) =
    Z3native.benchmark_to_smtlib_string ctx name logic status attributes
      (List.length assumptions) assumptions
      formula

  let parse_smtlib2_string (ctx:context) (str:string) (sort_names:Symbol.symbol list) (sorts:Sort.sort list) (decl_names:Symbol.symbol list) (decls:func_decl list) =
    let csn = List.length sort_names in
    let cs = List.length sorts in
    let cdn = List.length decl_names in
    let cd = List.length decls in
    if csn <> cs || cdn <> cd then
      raise (Error "Argument size mismatch")
    else
      Z3native.parse_smtlib2_string ctx str
        cs sort_names sorts cd decl_names decls

  let parse_smtlib2_file (ctx:context) (file_name:string) (sort_names:Symbol.symbol list) (sorts:Sort.sort list) (decl_names:Symbol.symbol list) (decls:func_decl list) =
    let csn = List.length sort_names in
    let cs = List.length sorts in
    let cdn = List.length decl_names in
    let cd = List.length decls in
    if csn <> cs || cdn <> cd then
      raise (Error "Argument size mismatch")
    else
      Z3native.parse_smtlib2_file ctx file_name
        cs sort_names sorts cd decl_names decls
end


let set_global_param = Z3native.global_param_set

let get_global_param id =
  match Z3native.global_param_get id with
  | (false, _) -> None
  | (true, v) -> Some v

let global_param_reset_all = Z3native.global_param_reset_all

let toggle_warning_messages = Z3native.toggle_warning_messages

let enable_trace = Z3native.enable_trace

let disable_trace = Z3native.enable_trace
