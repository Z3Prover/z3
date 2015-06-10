(**
   The Z3 ML/OCaml Interface.

   Copyright (C) 2012 Microsoft Corporation
   @author CM Wintersteiger (cwinter) 2012-12-17
*)

open Z3enums

exception Error = Z3native.Exception

(* Some helpers. *)
let null = Z3native.mk_null()
let is_null o = (Z3native.is_null o)

(* Internal types *)
type z3_native_context = { m_n_ctx : Z3native.z3_context; m_n_obj_cnt: int; } 
type context = z3_native_context

type z3_native_object = { 
  m_ctx : context ; 
  mutable m_n_obj : Z3native.ptr ; 
  inc_ref : Z3native.z3_context -> Z3native.ptr -> unit;
  dec_ref : Z3native.z3_context -> Z3native.ptr -> unit }

(** Internal stuff *)
module Internal =
struct
  let dispose_context ctx = 
    if ctx.m_n_obj_cnt == 0 then (
      (Z3native.del_context ctx.m_n_ctx)
    ) else (
      Printf.printf "ERROR: NOT DISPOSING CONTEXT (because it still has %d objects alive)\n" ctx.m_n_obj_cnt;
    )

  let create_context settings =
    let cfg = Z3native.mk_config () in
    let f e = (Z3native.set_param_value cfg (fst e) (snd e)) in
    (List.iter f settings) ;
    let v = Z3native.mk_context_rc cfg in
    Z3native.del_config(cfg) ;
    Z3native.set_ast_print_mode v (int_of_ast_print_mode PRINT_SMTLIB2_COMPLIANT) ;
    Z3native.set_internal_error_handler v ;
    let res = { m_n_ctx = v; m_n_obj_cnt = 0 } in
    let f = fun o -> dispose_context o in
    Gc.finalise f res;
    res

  let context_add1 ctx = ignore (ctx.m_n_obj_cnt = ctx.m_n_obj_cnt + 1)
  let context_sub1 ctx = ignore (ctx.m_n_obj_cnt = ctx.m_n_obj_cnt - 1)
  let context_gno ctx = ctx.m_n_ctx


  let z3obj_gc o = o.m_ctx
  let z3obj_gnc o = (context_gno o.m_ctx)

  let z3obj_gno o = o.m_n_obj
  let z3obj_sno o ctx no =
    (context_add1 ctx) ;
    o.inc_ref (context_gno ctx) no ;
    (
      if not (is_null o.m_n_obj) then
	o.dec_ref (context_gno ctx) o.m_n_obj ; 
      (context_sub1 ctx)
    ) ;
    o.m_n_obj <- no

  let z3obj_dispose o =
    if not (is_null o.m_n_obj) then
      (
	o.dec_ref (z3obj_gnc o) o.m_n_obj ;
	(context_sub1 (z3obj_gc o))
      ) ;
    o.m_n_obj <- null
      
  let z3obj_create o = 
    let f = fun o -> (z3obj_dispose o) in
    Gc.finalise f o

  let z3obj_nil_ref x y = ()

  let z3_native_object_of_ast_ptr : context -> Z3native.ptr -> z3_native_object = fun ctx no ->
    let res : z3_native_object = { m_ctx = ctx ;
				   m_n_obj = null ;
				   inc_ref = Z3native.inc_ref ;
				   dec_ref = Z3native.dec_ref } in
    (z3obj_sno res ctx no) ;
    (z3obj_create res) ;
    res  	        
end

open Internal

module Log = 
struct
  let open_ filename = ((lbool_of_int (Z3native.open_log filename)) == L_TRUE)
  let close = Z3native.close_log
  let append s = Z3native.append_log s
end


module Version =
struct
  let major = let (x, _, _, _) = Z3native.get_version () in x
  let minor = let (_, x, _, _) = Z3native.get_version () in x
  let build = let (_, _, x, _) = Z3native.get_version () in x
  let revision = let (_, _, _, x) = Z3native.get_version () in x
  let to_string = 
    let (mj, mn, bld, rev) = Z3native.get_version () in
    string_of_int mj ^ "." ^
      string_of_int mn ^ "." ^
      string_of_int bld ^ "." ^
      string_of_int rev
end


let mk_list ( f : int -> 'a ) ( n : int ) =
  let rec mk_list' ( f : int -> 'a ) ( i : int ) ( n : int )  ( tail : 'a list ) : 'a list =       
    if (i >= n) then 
      tail
    else
      (f i) :: (mk_list' f (i+1) n tail)
  in
  mk_list' f 0 n []

let list_of_array ( x : _ array ) =
  let f i = (Array.get x i) in
  mk_list f (Array.length x)

let mk_context ( cfg : ( string * string ) list ) =
  create_context cfg


module Symbol =
struct
  type symbol = z3_native_object

  let create_i ( ctx : context ) ( no : Z3native.ptr ) = 
    let res : symbol = { m_ctx = ctx ;
			 m_n_obj = null ;
			 inc_ref = z3obj_nil_ref ;
			 dec_ref = z3obj_nil_ref } in
    (z3obj_sno res ctx no) ;
    (z3obj_create res) ;
    res
      
  let create_s ( ctx : context ) ( no : Z3native.ptr ) = 
    let res : symbol = { m_ctx = ctx ;
			 m_n_obj = null ;
			 inc_ref = z3obj_nil_ref ;
			 dec_ref = z3obj_nil_ref } in
    (z3obj_sno res ctx no) ;
    (z3obj_create res) ;
    res

  let create ( ctx : context ) ( no : Z3native.ptr ) =
    match (symbol_kind_of_int (Z3native.get_symbol_kind (context_gno ctx) no)) with
      | INT_SYMBOL -> (create_i ctx no)
      | STRING_SYMBOL -> (create_s ctx no)	

  let gc ( x : symbol ) = (z3obj_gc x)
  let gnc ( x : symbol ) = (z3obj_gnc x)
  let gno ( x : symbol ) = (z3obj_gno x)

  let symbol_lton ( a : symbol list ) =
    let f ( e : symbol ) = (gno e) in 
    Array.of_list (List.map f a)
      
  let kind ( o : symbol ) = (symbol_kind_of_int (Z3native.get_symbol_kind (gnc o) (gno o)))   
  let is_int_symbol ( o : symbol ) = (kind o) == INT_SYMBOL
  let is_string_symbol ( o : symbol ) = (kind o) == STRING_SYMBOL
  let get_int (o : symbol) = Z3native.get_symbol_int (z3obj_gnc o) (z3obj_gno o)
  let get_string (o : symbol ) = Z3native.get_symbol_string (z3obj_gnc o) (z3obj_gno o)
  let to_string ( o : symbol ) = 
    match (kind o) with
      | INT_SYMBOL -> (string_of_int (Z3native.get_symbol_int (gnc o) (gno o)))
      | STRING_SYMBOL -> (Z3native.get_symbol_string (gnc o) (gno o))

  let mk_int ( ctx : context ) ( i : int ) = 
    (create_i ctx (Z3native.mk_int_symbol (context_gno ctx) i))
      
  let mk_string ( ctx : context ) ( s : string ) =
    (create_s ctx (Z3native.mk_string_symbol (context_gno ctx) s))

  let mk_ints ( ctx : context ) ( names : int list ) =
    let f elem = mk_int ( ctx : context ) elem in
    (List.map f names)

  let mk_strings ( ctx : context ) ( names : string list ) =
    let f elem = mk_string ( ctx : context ) elem in
    (List.map f names)      
end


module rec AST :
sig
  type ast = z3_native_object
  val context_of_ast : ast -> context
  val nc_of_ast : ast -> Z3native.z3_context
  val ptr_of_ast : ast -> Z3native.ptr
  val ast_of_ptr : context -> Z3native.ptr -> ast
  module ASTVector :
  sig
    type ast_vector = z3_native_object
    val create : context -> Z3native.ptr -> ast_vector
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
    type ast_map = z3_native_object
    val create : context -> Z3native.ptr -> ast_map
    val mk_ast_map : context -> ast_map
    val contains : ast_map -> ast -> bool
    val find : ast_map -> ast -> ast
    val insert : ast_map -> ast -> ast -> unit
    val erase : ast_map -> ast -> unit
    val reset : ast_map -> unit
    val get_size : ast_map -> int
    val get_keys : ast_map -> Expr.expr list
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
  val unwrap_ast : ast -> Z3native.ptr
  val wrap_ast : context -> Z3native.z3_ast -> ast
end = struct    
  type ast = z3_native_object

  let context_of_ast ( x : ast ) = (z3obj_gc x)
  let nc_of_ast ( x : ast ) = (z3obj_gnc x)
  let ptr_of_ast ( x : ast ) = (z3obj_gno x)  
    
  let rec ast_of_ptr : context -> Z3native.ptr -> ast = fun ctx no -> 
    match (ast_kind_of_int (Z3native.get_ast_kind (context_gno ctx) no)) with
      | FUNC_DECL_AST 
      | SORT_AST 
      | QUANTIFIER_AST
      | APP_AST
      | NUMERAL_AST
      | VAR_AST -> z3_native_object_of_ast_ptr ctx no
      | UNKNOWN_AST -> raise (Z3native.Exception "Cannot create asts of type unknown")

  module ASTVector = 
  struct
    type ast_vector = z3_native_object
	
    let create ( ctx : context ) ( no : Z3native.ptr ) = 
      let res : ast_vector = { m_ctx = ctx ;
			                   m_n_obj = null ;
			                   inc_ref = Z3native.ast_vector_inc_ref ;
			                   dec_ref = Z3native.ast_vector_dec_ref } in
      (z3obj_sno res ctx no) ;
      (z3obj_create res) ;
      res
	    
    let mk_ast_vector ( ctx : context ) = (create ctx (Z3native.mk_ast_vector (context_gno ctx)))
      
    let get_size ( x : ast_vector ) =
      Z3native.ast_vector_size (z3obj_gnc x) (z3obj_gno x)

    let get ( x : ast_vector ) ( i : int ) =
      ast_of_ptr (z3obj_gc x) (Z3native.ast_vector_get (z3obj_gnc x) (z3obj_gno x) i)

    let set ( x : ast_vector ) ( i : int ) ( value : ast ) =
      Z3native.ast_vector_set (z3obj_gnc x) (z3obj_gno x) i (z3obj_gno value)

    let resize ( x : ast_vector ) ( new_size : int ) =
      Z3native.ast_vector_resize (z3obj_gnc x) (z3obj_gno x) new_size
	
    let push ( x : ast_vector ) ( a : ast )  =
      Z3native.ast_vector_push (z3obj_gnc x) (z3obj_gno x) (z3obj_gno a)
	
    let translate ( x : ast_vector ) ( to_ctx : context ) =
      create to_ctx (Z3native.ast_vector_translate (z3obj_gnc x) (z3obj_gno x) (context_gno to_ctx))

    let to_list ( x : ast_vector ) =
	  let xs = (get_size x) in
      let f i = (get x i) in
      mk_list f xs

    let to_expr_list ( x : ast_vector ) =
	  let xs = (get_size x) in
      let f i = (Expr.expr_of_ptr (z3obj_gc x) (z3obj_gno (get x i))) in
      mk_list f xs
	
    let to_string ( x : ast_vector ) =
      Z3native.ast_vector_to_string (z3obj_gnc x) (z3obj_gno x)
  end

  module ASTMap =
  struct	
    type ast_map = z3_native_object
	
    let create ( ctx : context ) ( no : Z3native.ptr ) = 
      let res : ast_map  = { m_ctx = ctx ;
			                 m_n_obj = null ;
			                 inc_ref = Z3native.ast_map_inc_ref ;
			                 dec_ref = Z3native.ast_map_dec_ref } in
      (z3obj_sno res ctx no) ;
      (z3obj_create res) ;
      res	
	
    let mk_ast_map ( ctx : context ) = (create ctx (Z3native.mk_ast_map (context_gno ctx)))

    let astmap_of_ptr ( ctx : context ) ( no : Z3native.ptr ) = 
      let res : ast_map = { m_ctx = ctx ;
			    m_n_obj = null ;
			    inc_ref = Z3native.ast_map_inc_ref ;
			    dec_ref = Z3native.ast_map_dec_ref } in
      (z3obj_sno res ctx no) ;
      (z3obj_create res) ;
      res
	
    let contains ( x : ast_map ) ( key : ast ) =
      Z3native.ast_map_contains (z3obj_gnc x) (z3obj_gno x) (z3obj_gno key)
	
    let find ( x : ast_map ) ( key : ast ) =
      ast_of_ptr (z3obj_gc x) (Z3native.ast_map_find (z3obj_gnc x) (z3obj_gno x) (z3obj_gno key))
	
    let insert ( x : ast_map ) ( key : ast ) ( value : ast ) =
      Z3native.ast_map_insert (z3obj_gnc x) (z3obj_gno x) (z3obj_gno key) (z3obj_gno value)

    let erase ( x : ast_map ) ( key : ast ) =
      Z3native.ast_map_erase (z3obj_gnc x) (z3obj_gno x) (z3obj_gno key)
	
    let reset ( x : ast_map ) =
      Z3native.ast_map_reset (z3obj_gnc x) (z3obj_gno x)

    let get_size ( x : ast_map ) =
      Z3native.ast_map_size (z3obj_gnc x) (z3obj_gno x)
	
    let get_keys ( x : ast_map ) =
      let av = ASTVector.create (z3obj_gc x) (Z3native.ast_map_keys (z3obj_gnc x) (z3obj_gno x)) in
      (ASTVector.to_expr_list av)

    let to_string ( x : ast_map ) =
      Z3native.ast_map_to_string (z3obj_gnc x) (z3obj_gno x)
  end

  let hash ( x : ast ) = Z3native.get_ast_hash (z3obj_gnc x) (z3obj_gno x)
  let get_id ( x : ast ) = Z3native.get_ast_id (z3obj_gnc x) (z3obj_gno x)
  let get_ast_kind ( x : ast ) = (ast_kind_of_int (Z3native.get_ast_kind (z3obj_gnc x) (z3obj_gno x)))
    
  let is_expr ( x : ast ) = 
    match get_ast_kind ( x : ast ) with
      | APP_AST
      | NUMERAL_AST
      | QUANTIFIER_AST
      | VAR_AST -> true
      | _ -> false
	
  let is_app ( x : ast ) = (get_ast_kind x) == APP_AST
  let is_var ( x : ast ) = (get_ast_kind x) == VAR_AST   
  let is_quantifier ( x : ast ) = (get_ast_kind x) == QUANTIFIER_AST
  let is_sort ( x : ast ) = (get_ast_kind x) == SORT_AST
  let is_func_decl ( x : ast ) = (get_ast_kind x) == FUNC_DECL_AST

  let to_string ( x : ast ) = Z3native.ast_to_string (z3obj_gnc x) (z3obj_gno x)
  let to_sexpr ( x : ast ) = Z3native.ast_to_string (z3obj_gnc x) (z3obj_gno x)


  let equal ( a : ast ) ( b : ast ) = (a == b) ||
    if (z3obj_gnc a) != (z3obj_gnc b) then 
      false 
    else 
      Z3native.is_eq_ast (z3obj_gnc a) (z3obj_gno a) (z3obj_gno b)
	
  let compare a b = 
    if (get_id a) < (get_id b) then -1 else
      if (get_id a) > (get_id b) then 1 else
	0
	  
  let translate ( x : ast ) ( to_ctx : context ) = 
    if (z3obj_gnc x) == (context_gno to_ctx) then 
      x
    else
      ast_of_ptr to_ctx (Z3native.translate (z3obj_gnc x) (z3obj_gno x) (context_gno to_ctx))

  let unwrap_ast ( x : ast ) = (z3obj_gno x)
  let wrap_ast ( ctx : context ) ( ptr : Z3native.ptr ) = ast_of_ptr ctx ptr
end

and Sort :
sig
  type sort = Sort of AST.ast
  val ast_of_sort : Sort.sort -> AST.ast
  val sort_of_ptr : context -> Z3native.ptr -> sort
  val gc : sort -> context
  val gnc : sort -> Z3native.ptr
  val gno : sort -> Z3native.ptr
  val sort_lton : sort list -> Z3native.ptr array
  val sort_option_lton : sort option list -> Z3native.ptr array
  val equal : sort -> sort -> bool
  val get_id : sort -> int
  val get_sort_kind : sort -> Z3enums.sort_kind
  val get_name : sort -> Symbol.symbol
  val to_string : sort -> string
  val mk_uninterpreted : context -> Symbol.symbol -> sort
  val mk_uninterpreted_s : context -> string -> sort
end = struct
  type sort = Sort of AST.ast

  let sort_of_ptr : context -> Z3native.ptr -> sort = fun ctx no ->
    if ((Z3enums.ast_kind_of_int (Z3native.get_ast_kind (context_gno ctx) no)) != Z3enums.SORT_AST) then
      raise (Z3native.Exception "Invalid coercion")
    else
      match (sort_kind_of_int (Z3native.get_sort_kind (context_gno ctx) no)) with
        | ARRAY_SORT
        | BOOL_SORT
        | BV_SORT 
        | DATATYPE_SORT 
        | INT_SORT 
        | REAL_SORT 
        | UNINTERPRETED_SORT 
        | FINITE_DOMAIN_SORT 
        | RELATION_SORT 
        | FLOATING_POINT_SORT
        | ROUNDING_MODE_SORT -> Sort(z3_native_object_of_ast_ptr ctx no)
        | UNKNOWN_SORT -> raise (Z3native.Exception "Unknown sort kind encountered")

  let ast_of_sort s = match s with Sort(x) -> x
    
  let gc ( x : sort ) = (match x with Sort(a) -> (z3obj_gc a))
  let gnc ( x : sort ) = (match x with Sort(a) -> (z3obj_gnc a))
  let gno ( x : sort ) = (match x with Sort(a) -> (z3obj_gno a))

  let sort_lton ( a : sort list ) =
    let f ( e : sort ) = match e with Sort(a) -> (AST.ptr_of_ast a) in 
    Array.of_list (List.map f a)

  let sort_option_lton ( a : sort option list ) =
    let f ( e : sort option ) = match e with None -> null | Some(Sort(a)) -> (AST.ptr_of_ast a) in 
    Array.of_list (List.map f a)
      
  let equal : sort -> sort -> bool = fun a b ->
    (a == b) ||
      if (gnc a) != (gnc b) then 
	false 
      else 
	(Z3native.is_eq_sort (gnc a) (gno a) (gno b))
 
	  
  let get_id ( x : sort ) = Z3native.get_sort_id (gnc x) (gno x)
  let get_sort_kind ( x : sort ) = (sort_kind_of_int (Z3native.get_sort_kind (gnc x) (gno x)))
  let get_name ( x : sort ) = (Symbol.create (gc x) (Z3native.get_sort_name (gnc x) (gno x)))    
  let to_string ( x : sort ) = Z3native.sort_to_string (gnc x) (gno x)

  let mk_uninterpreted ( ctx : context ) ( s : Symbol.symbol ) =
    let res = { m_ctx = ctx ;
		m_n_obj = null ;
		inc_ref = Z3native.inc_ref ;
		dec_ref = Z3native.dec_ref } in
    (z3obj_sno res ctx (Z3native.mk_uninterpreted_sort (context_gno ctx) (Symbol.gno s))) ;
    (z3obj_create res) ;
    Sort(res)

  let mk_uninterpreted_s ( ctx : context ) ( s : string ) =
    mk_uninterpreted ctx (Symbol.mk_string ( ctx : context ) s)
end 

and FuncDecl :
sig 
  type func_decl = FuncDecl of AST.ast
  val ast_of_func_decl : FuncDecl.func_decl -> AST.ast
  val func_decl_of_ptr : context -> Z3native.ptr -> func_decl
  val gc : func_decl -> context
  val gnc : func_decl -> Z3native.ptr
  val gno : func_decl -> Z3native.ptr
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
  type func_decl = FuncDecl of AST.ast

  let func_decl_of_ptr : context -> Z3native.ptr -> func_decl = fun ctx no ->
    if ((Z3enums.ast_kind_of_int (Z3native.get_ast_kind (context_gno ctx) no)) != Z3enums.FUNC_DECL_AST) then
      raise (Z3native.Exception "Invalid coercion")
    else
      FuncDecl(z3_native_object_of_ast_ptr ctx no)

  let ast_of_func_decl f = match f with FuncDecl(x) -> x

  let create_ndr ( ctx : context ) ( name : Symbol.symbol ) ( domain : Sort.sort list ) ( range : Sort.sort )  = 
    let res = { m_ctx = ctx ;
		m_n_obj = null ;
		inc_ref = Z3native.inc_ref ;
		dec_ref = Z3native.dec_ref } in
    (z3obj_sno res ctx (Z3native.mk_func_decl (context_gno ctx) (Symbol.gno name) (List.length domain) (Sort.sort_lton domain) (Sort.gno range))) ;
    (z3obj_create res) ;
    FuncDecl(res)
      
  let create_pdr ( ctx : context) ( prefix : string ) ( domain : Sort.sort list ) ( range : Sort.sort ) = 
    let res = { m_ctx = ctx ;
		m_n_obj = null ;
		inc_ref = Z3native.inc_ref ;
		dec_ref = Z3native.dec_ref } in
    (z3obj_sno res ctx (Z3native.mk_fresh_func_decl (context_gno ctx) prefix (List.length domain) (Sort.sort_lton domain) (Sort.gno range))) ;
    (z3obj_create res) ;
    FuncDecl(res)

  let gc ( x : func_decl ) = match x with FuncDecl(a) -> (z3obj_gc a)
  let gnc ( x : func_decl ) = match x with FuncDecl(a) -> (z3obj_gnc a)
  let gno ( x : func_decl ) = match x with FuncDecl(a) -> (z3obj_gno a)     

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
	  
    let get_kind ( x : parameter ) =
      (match x with
	| P_Int(_) -> PARAMETER_INT
	| P_Dbl(_) -> PARAMETER_DOUBLE
	| P_Sym(_) -> PARAMETER_SYMBOL
	| P_Srt(_) -> PARAMETER_SORT
	| P_Ast(_) -> PARAMETER_AST
	| P_Fdl(_) -> PARAMETER_FUNC_DECL
	| P_Rat(_) -> PARAMETER_RATIONAL)
	
    let get_int ( x : parameter ) =
      match x with
	| P_Int(x) -> x
	| _ -> raise (Z3native.Exception "parameter is not an int")
	  
    let get_float ( x : parameter ) = 
      match x with
	| P_Dbl(x) -> x
	| _ -> raise (Z3native.Exception "parameter is not a float")
          
    let get_symbol ( x : parameter ) =
      match x with
	| P_Sym(x) -> x
	| _ -> raise (Z3native.Exception "parameter is not a symbol")
	  
    let get_sort ( x : parameter ) =
      match x with
	| P_Srt(x) -> x
	| _ -> raise (Z3native.Exception "parameter is not a sort")

    let get_ast ( x : parameter ) =
      match x with
	| P_Ast(x) -> x
	| _ -> raise (Z3native.Exception "parameter is not an ast")

    let get_func_decl ( x : parameter ) =
      match x with
	| P_Fdl(x) -> x
	| _ -> raise (Z3native.Exception "parameter is not a func_decl")

    let get_rational ( x : parameter ) =
      match x with
	| P_Rat(x) -> x
	| _ -> raise (Z3native.Exception "parameter is not a rational string")
  end

  let mk_func_decl ( ctx : context ) ( name : Symbol.symbol ) ( domain : Sort.sort list ) ( range : Sort.sort ) =
    create_ndr ctx name domain range

  let mk_func_decl_s ( ctx : context ) ( name : string ) ( domain : Sort.sort list ) ( range : Sort.sort ) =
    mk_func_decl ctx (Symbol.mk_string ctx name) domain range

  let mk_fresh_func_decl ( ctx : context ) ( prefix : string ) ( domain : Sort.sort list ) ( range : Sort.sort ) =
    create_pdr ctx prefix domain range

  let mk_const_decl ( ctx : context ) ( name : Symbol.symbol ) ( range : Sort.sort ) =
    create_ndr ctx name [] range

  let mk_const_decl_s ( ctx : context ) ( name : string ) ( range : Sort.sort ) =
    create_ndr ctx (Symbol.mk_string ctx name) []  range

  let mk_fresh_const_decl ( ctx : context ) ( prefix : string ) ( range : Sort.sort ) =
    create_pdr ctx prefix [] range


  let equal ( a : func_decl ) ( b : func_decl ) = (a == b) ||
    if (gnc a) != (gnc b) then 
      false 
    else 
      (Z3native.is_eq_func_decl (gnc a) (gno a) (gno b))

  let to_string ( x : func_decl ) = Z3native.func_decl_to_string (gnc x) (gno x)
    
  let get_id ( x : func_decl ) = Z3native.get_func_decl_id (gnc x) (gno x)
    
  let get_arity ( x : func_decl ) = Z3native.get_arity (gnc x) (gno x)
    
  let get_domain_size ( x : func_decl ) = Z3native.get_domain_size (gnc x) (gno x)
    
  let get_domain ( x : func_decl ) = 
    let n = (get_domain_size x) in
    let f i = Sort.sort_of_ptr (gc x) (Z3native.get_domain (gnc x) (gno x) i) in
    mk_list f n
      
  let get_range ( x : func_decl ) = 
    Sort.sort_of_ptr (gc x) (Z3native.get_range (gnc x) (gno x))
      
  let get_decl_kind ( x : func_decl ) = (decl_kind_of_int (Z3native.get_decl_kind (gnc x) (gno x)))

  let get_name ( x : func_decl ) = (Symbol.create (gc x) (Z3native.get_decl_name (gnc x) (gno x)))

  let get_num_parameters ( x : func_decl ) = (Z3native.get_decl_num_parameters (gnc x) (gno x))    

  let get_parameters ( x : func_decl ) =
    let n = (get_num_parameters x) in
    let f i = (match (parameter_kind_of_int (Z3native.get_decl_parameter_kind (gnc x) (gno x) i)) with
      | PARAMETER_INT -> Parameter.P_Int (Z3native.get_decl_int_parameter (gnc x) (gno x) i)
      | PARAMETER_DOUBLE -> Parameter.P_Dbl (Z3native.get_decl_double_parameter (gnc x) (gno x) i)
      | PARAMETER_SYMBOL-> Parameter.P_Sym (Symbol.create (gc x) (Z3native.get_decl_symbol_parameter (gnc x) (gno x) i))
      | PARAMETER_SORT -> Parameter.P_Srt (Sort.sort_of_ptr (gc x) (Z3native.get_decl_sort_parameter (gnc x) (gno x) i))
      | PARAMETER_AST -> Parameter.P_Ast (AST.ast_of_ptr (gc x) (Z3native.get_decl_ast_parameter (gnc x) (gno x) i))
      | PARAMETER_FUNC_DECL -> Parameter.P_Fdl (func_decl_of_ptr (gc x) (Z3native.get_decl_func_decl_parameter (gnc x) (gno x) i))
      | PARAMETER_RATIONAL -> Parameter.P_Rat (Z3native.get_decl_rational_parameter (gnc x) (gno x) i)
    ) in
    mk_list f n

  let apply ( x : func_decl ) ( args : Expr.expr list ) = Expr.expr_of_func_app (gc x) x args 
end


and Params : 
sig
  type params = z3_native_object
  module ParamDescrs :
  sig
    type param_descrs 
    val param_descrs_of_ptr : context -> Z3native.ptr -> param_descrs
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
  type params = z3_native_object

  module ParamDescrs = 
  struct    
    type param_descrs = z3_native_object

    let param_descrs_of_ptr ( ctx : context ) ( no : Z3native.ptr ) = 
      let res : param_descrs = { m_ctx = ctx ;
				 m_n_obj = null ;
				 inc_ref = Z3native.param_descrs_inc_ref ;
				 dec_ref = Z3native.param_descrs_dec_ref } in
      (z3obj_sno res ctx no) ;
      (z3obj_create res) ;
      res
	
    let validate ( x : param_descrs ) ( p : params ) = 
      Z3native.params_validate (z3obj_gnc x) (z3obj_gno p) (z3obj_gno x)
	
    let get_kind ( x : param_descrs ) ( name : Symbol.symbol ) = 
      (param_kind_of_int (Z3native.param_descrs_get_kind (z3obj_gnc x) (z3obj_gno x) (Symbol.gno name)))
	
    let get_names ( x : param_descrs ) =
      let n = Z3native.param_descrs_size (z3obj_gnc x) (z3obj_gno x) in
      let f i = Symbol.create (z3obj_gc x) (Z3native.param_descrs_get_name (z3obj_gnc x) (z3obj_gno x) i) in
      mk_list f n

    let get_size ( x : param_descrs ) = Z3native.param_descrs_size (z3obj_gnc x) (z3obj_gno x)    
    let to_string ( x : param_descrs ) = Z3native.param_descrs_to_string (z3obj_gnc x) (z3obj_gno x) 
  end

  let add_bool ( x : params ) ( name : Symbol.symbol ) ( value : bool ) =
    Z3native.params_set_bool (z3obj_gnc x) (z3obj_gno x) (Symbol.gno name) value
      
  let add_int ( x : params )  (name : Symbol.symbol ) ( value : int ) =
    Z3native.params_set_uint (z3obj_gnc x) (z3obj_gno x) (Symbol.gno name) value
      
  let add_float ( x : params ) ( name : Symbol.symbol ) ( value : float ) =
    Z3native.params_set_double (z3obj_gnc x) (z3obj_gno x) (Symbol.gno name) value

  let add_symbol ( x : params ) ( name : Symbol.symbol ) ( value : Symbol.symbol ) =
    Z3native.params_set_symbol (z3obj_gnc x) (z3obj_gno x) (Symbol.gno name) (Symbol.gno value)

  let mk_params ( ctx : context ) =
    let res : params = { m_ctx = ctx ;
			 m_n_obj = null ;
			 inc_ref = Z3native.params_inc_ref ;
			 dec_ref = Z3native.params_dec_ref } in
    (z3obj_sno res ctx (Z3native.mk_params (context_gno ctx))) ;
    (z3obj_create res) ;
    res

  let to_string ( x : params ) = Z3native.params_to_string (z3obj_gnc x) (z3obj_gno x)

  let update_param_value ( ctx : context ) ( id : string) ( value : string )=
    Z3native.update_param_value (context_gno ctx) id value

  let set_print_mode ( ctx : context ) ( value : ast_print_mode ) =
    Z3native.set_ast_print_mode (context_gno ctx) (int_of_ast_print_mode value)
end

(** General expressions (terms) *)
and Expr :
sig
  type expr = Expr of AST.ast
  val expr_of_ptr : context -> Z3native.ptr -> expr
  val gc : expr -> context
  val gnc : expr -> Z3native.ptr
  val gno : expr -> Z3native.ptr
  val expr_lton : expr list -> Z3native.ptr array
  val ast_of_expr : expr -> AST.ast
  val expr_of_ast : AST.ast -> expr
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
  type expr = Expr of AST.ast
      
  let gc e = match e with Expr(a) -> (z3obj_gc a)
  let gnc e = match e with Expr(a) -> (z3obj_gnc a)
  let gno e = match e with Expr(a) -> (z3obj_gno a)

  let expr_of_ptr : context -> Z3native.ptr -> expr = fun ctx no -> 
    if ast_kind_of_int (Z3native.get_ast_kind (context_gno ctx) no) == QUANTIFIER_AST then
      Expr(z3_native_object_of_ast_ptr ctx no)
    else
      let s = Z3native.get_sort (context_gno ctx) no in
      let sk = (sort_kind_of_int (Z3native.get_sort_kind (context_gno ctx) s)) in
      if (Z3native.is_algebraic_number (context_gno ctx) no) then
	Expr(z3_native_object_of_ast_ptr ctx no)
      else
	if (Z3native.is_numeral_ast (context_gno ctx) no) then
	  if (sk == INT_SORT || sk == REAL_SORT || sk == BV_SORT || 
			sk == FLOATING_POINT_SORT || sk == ROUNDING_MODE_SORT) then
	    Expr(z3_native_object_of_ast_ptr ctx no)
	  else
	    raise (Z3native.Exception "Unsupported numeral object")
	else	  
	  Expr(z3_native_object_of_ast_ptr ctx no)

  let expr_of_ast a = 
    let q = (Z3enums.ast_kind_of_int (Z3native.get_ast_kind (z3obj_gnc a) (z3obj_gno a))) in
    if (q != Z3enums.APP_AST && q != VAR_AST && q != QUANTIFIER_AST && q != NUMERAL_AST) then
      raise (Z3native.Exception "Invalid coercion")
    else
      Expr(a)

  let ast_of_expr e = match e with Expr(a) -> a

  let expr_lton ( a : expr list ) =
    let f ( e : expr ) = match e with Expr(a) -> (AST.ptr_of_ast a) in 
    Array.of_list (List.map f a)

  let expr_of_func_app : context -> FuncDecl.func_decl -> expr list -> expr = fun ctx f args ->
    match f with FuncDecl.FuncDecl(fa) ->
      let o = Z3native.mk_app (context_gno ctx) (AST.ptr_of_ast fa) (List.length args) (expr_lton args) in
      expr_of_ptr ctx o

  let simplify ( x : expr ) ( p : Params.params option ) = match p with 
    | None -> expr_of_ptr (Expr.gc x) (Z3native.simplify (gnc x) (gno x))
    | Some pp -> expr_of_ptr (Expr.gc x) (Z3native.simplify_ex (gnc x) (gno x) (z3obj_gno pp))
      
  let get_simplify_help ( ctx : context ) =
    Z3native.simplify_get_help (context_gno ctx)

  let get_simplify_parameter_descrs ( ctx : context ) = 
    Params.ParamDescrs.param_descrs_of_ptr ctx (Z3native.simplify_get_param_descrs (context_gno ctx))
  let get_func_decl ( x : expr ) = FuncDecl.func_decl_of_ptr (Expr.gc x) (Z3native.get_app_decl (gnc x) (gno x))    

  let get_num_args ( x : expr ) = Z3native.get_app_num_args (gnc x) (gno x)
    
  let get_args ( x : expr ) = let n = (get_num_args x) in
			      let f i = expr_of_ptr (Expr.gc x) (Z3native.get_app_arg (gnc x) (gno x) i) in
			      mk_list f n
				
  let update ( x : expr ) ( args : expr list ) =
    if ((AST.is_app (ast_of_expr x)) && (List.length args <> (get_num_args x))) then
      raise (Z3native.Exception "Number of arguments does not match")
    else
      expr_of_ptr (Expr.gc x) (Z3native.update_term (gnc x) (gno x) (List.length args) (expr_lton args))

  let substitute ( x : expr ) from to_ = 
    if (List.length from) <> (List.length to_) then
      raise (Z3native.Exception "Argument sizes do not match")
    else
      expr_of_ptr (Expr.gc x) (Z3native.substitute (gnc x) (gno x) (List.length from) (expr_lton from) (expr_lton to_))
	
  let substitute_one ( x : expr ) from to_ =
    substitute ( x : expr ) [ from ] [ to_ ]
      
  let substitute_vars ( x : expr ) to_ =
    expr_of_ptr (Expr.gc x) (Z3native.substitute_vars (gnc x) (gno x) (List.length to_) (expr_lton to_))
      
  let translate ( x : expr ) to_ctx =
    if (Expr.gc x) == to_ctx then
      x
    else
      expr_of_ptr to_ctx (Z3native.translate (gnc x) (gno x) (context_gno to_ctx))

  let to_string ( x : expr ) = Z3native.ast_to_string (gnc x) (gno x)

  let is_numeral ( x : expr ) = (Z3native.is_numeral_ast (gnc x) (gno x))
    
  let is_well_sorted ( x : expr ) = Z3native.is_well_sorted (gnc x) (gno x)

  let get_sort ( x : expr ) = Sort.sort_of_ptr (Expr.gc x) (Z3native.get_sort (gnc x) (gno x))
    
  let is_const ( x : expr ) = (match x with Expr(a) -> (AST.is_app a)) &&
    (get_num_args x) == 0 &&
    (FuncDecl.get_domain_size (get_func_decl x)) == 0
    
  let mk_const ( ctx : context ) ( name : Symbol.symbol ) ( range : Sort.sort ) =
    expr_of_ptr ctx (Z3native.mk_const (context_gno ctx) (Symbol.gno name) (Sort.gno range))
      
  let mk_const_s ( ctx : context ) ( name : string ) ( range : Sort.sort ) =
    mk_const ctx (Symbol.mk_string ctx name) range

  let mk_const_f ( ctx : context ) ( f : FuncDecl.func_decl ) = Expr.expr_of_func_app ctx f []

  let mk_fresh_const ( ctx : context ) ( prefix : string ) ( range : Sort.sort ) =
    expr_of_ptr ctx (Z3native.mk_fresh_const (context_gno ctx) prefix (Sort.gno range))

  let mk_app ( ctx : context ) ( f : FuncDecl.func_decl ) ( args : expr list ) = expr_of_func_app ctx f args

  let mk_numeral_string ( ctx : context ) ( v : string ) ( ty : Sort.sort ) =
    expr_of_ptr ctx (Z3native.mk_numeral (context_gno ctx) v (Sort.gno ty))

  let mk_numeral_int ( ctx : context ) ( v : int ) ( ty : Sort.sort ) =
    expr_of_ptr ctx (Z3native.mk_int (context_gno ctx) v (Sort.gno ty))

  let equal ( a : expr ) ( b : expr ) = AST.equal (ast_of_expr a) (ast_of_expr b)
    
  let compare a b = AST.compare (ast_of_expr a) (ast_of_expr b)
end

open FuncDecl
open Expr

module Boolean = 
struct      
  let mk_sort ( ctx : context ) =
    (Sort.sort_of_ptr ctx (Z3native.mk_bool_sort (context_gno ctx)))

  let mk_const ( ctx : context ) ( name : Symbol.symbol ) =
    (Expr.mk_const ctx name (mk_sort ctx))
      
  let mk_const_s ( ctx : context ) ( name : string ) =
    mk_const ctx (Symbol.mk_string ctx name)

  let mk_true ( ctx : context ) =
    expr_of_ptr ctx (Z3native.mk_true (context_gno ctx))

  let mk_false ( ctx : context ) =
    expr_of_ptr ctx (Z3native.mk_false (context_gno ctx))

  let mk_val ( ctx : context ) ( value : bool ) =
    if value then mk_true ctx else mk_false ctx
      
  let mk_not ( ctx : context ) ( a : expr ) =
    expr_of_ptr ctx (Z3native.mk_not (context_gno ctx) (gno a))

  let mk_ite ( ctx : context ) ( t1 : expr ) ( t2 : expr ) ( t3 : expr ) =
    expr_of_ptr ctx (Z3native.mk_ite (context_gno ctx) (gno t1) (gno t2) (gno t3))
      
  let mk_iff ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_iff (context_gno ctx) (gno t1) (gno t2))

  let mk_implies ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_implies (context_gno ctx) (gno t1) (gno t2))

  let mk_xor ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_xor (context_gno ctx) (gno t1) (gno t2))

  let mk_and ( ctx : context ) ( args : expr list ) =
    let f x = (Expr.gno (x)) in
    expr_of_ptr ctx (Z3native.mk_and (context_gno ctx) (List.length args) (Array.of_list (List.map f args)))

  let mk_or ( ctx : context ) ( args : expr list ) =
    let f x = (Expr.gno (x)) in
    expr_of_ptr ctx (Z3native.mk_or (context_gno ctx) (List.length args) (Array.of_list(List.map f args)))

  let mk_eq ( ctx : context ) ( x : expr ) ( y : expr ) =
    expr_of_ptr ctx (Z3native.mk_eq (context_gno ctx) (Expr.gno x) (Expr.gno y))

  let mk_distinct ( ctx : context ) ( args : expr list ) =
    expr_of_ptr ctx (Z3native.mk_distinct (context_gno ctx) (List.length args) (expr_lton args))

  let get_bool_value ( x : expr ) = lbool_of_int (Z3native.get_bool_value (gnc x) (gno x))

  let is_bool ( x : expr ) = (match x with Expr(a) -> (AST.is_expr a)) &&
    (Z3native.is_eq_sort (gnc x) 
       (Z3native.mk_bool_sort (gnc x))
       (Z3native.get_sort (gnc x) (gno x)))

  let is_true ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (get_func_decl x) == OP_TRUE)
  let is_false ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (get_func_decl x) == OP_FALSE)
  let is_eq ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (get_func_decl x) == OP_EQ)
  let is_distinct ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (get_func_decl x) == OP_DISTINCT)
  let is_ite ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (get_func_decl x) == OP_ITE)
  let is_and ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (get_func_decl x) == OP_AND)
  let is_or ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (get_func_decl x) == OP_OR)
  let is_iff ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (get_func_decl x) == OP_IFF)
  let is_xor ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (get_func_decl x) == OP_XOR)
  let is_not ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (get_func_decl x) == OP_NOT)
  let is_implies ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (get_func_decl x) == OP_IMPLIES)
end


module Quantifier = 
struct 
  type quantifier = Quantifier of expr

  let expr_of_quantifier e = match e with Quantifier(x) -> x

  let quantifier_of_expr e =
    match e with Expr.Expr(a) ->
      let q = (Z3enums.ast_kind_of_int (Z3native.get_ast_kind (z3obj_gnc a) (z3obj_gno a))) in
      if (q != Z3enums.QUANTIFIER_AST) then
	raise (Z3native.Exception "Invalid coercion")
      else
	Quantifier(e)
	  
  let gc ( x : quantifier ) = match (x) with Quantifier(e) -> (Expr.gc e)
  let gnc ( x : quantifier ) = match (x) with Quantifier(e) -> (Expr.gnc e)
  let gno ( x : quantifier ) = match (x) with Quantifier(e) -> (Expr.gno e)
    
  module Pattern = 
  struct
    type pattern = Pattern of AST.ast
	
    let ast_of_pattern e = match e with Pattern(x) -> x
      
    let pattern_of_ast a =
      (* CMW: Unchecked ok? *)
      Pattern(a)
	
    let gc ( x : pattern ) = match (x) with Pattern(a) -> (z3obj_gc a)
    let gnc ( x : pattern ) = match (x) with Pattern(a) -> (z3obj_gnc a)
    let gno ( x : pattern ) = match (x) with Pattern(a) -> (z3obj_gno a)

    let get_num_terms ( x : pattern ) =
      Z3native.get_pattern_num_terms (gnc x) (gno x)	

    let get_terms ( x : pattern ) =
      let n = (get_num_terms x) in
      let f i = (expr_of_ptr (gc x) (Z3native.get_pattern (gnc x) (gno x) i)) in
      mk_list f n
	
    let to_string ( x : pattern ) = Z3native.pattern_to_string (gnc x) (gno x)
  end

  let get_index ( x : expr ) = 
    if not (AST.is_var (match x with Expr.Expr(a) -> a)) then
      raise (Z3native.Exception "Term is not a bound variable.")
    else
      Z3native.get_index_value (Expr.gnc x) (Expr.gno x)

  let is_universal ( x : quantifier ) =
    Z3native.is_quantifier_forall (gnc x) (gno x)
      
  let is_existential ( x : quantifier ) = not (is_universal x)

  let get_weight ( x : quantifier ) = Z3native.get_quantifier_weight (gnc x) (gno x)
    
  let get_num_patterns ( x : quantifier ) = Z3native.get_quantifier_num_patterns (gnc x) (gno x)
    
  let get_patterns ( x : quantifier ) =
    let n = (get_num_patterns x) in
    let f i = Pattern.Pattern (z3_native_object_of_ast_ptr (gc x) (Z3native.get_quantifier_pattern_ast (gnc x) (gno x) i)) in
    mk_list f n
      
  let get_num_no_patterns ( x : quantifier ) = Z3native.get_quantifier_num_no_patterns (gnc x) (gno x)
    
  let get_no_patterns ( x : quantifier ) =
    let n = (get_num_patterns x) in
    let f i = Pattern.Pattern (z3_native_object_of_ast_ptr (gc x) (Z3native.get_quantifier_no_pattern_ast (gnc x) (gno x) i)) in
    mk_list f n
      
  let get_num_bound ( x : quantifier ) = Z3native.get_quantifier_num_bound (gnc x) (gno x)
    
  let get_bound_variable_names ( x : quantifier ) =
    let n = (get_num_bound x) in
    let f i = (Symbol.create (gc x) (Z3native.get_quantifier_bound_name (gnc x) (gno x) i)) in
    mk_list f n
      
  let get_bound_variable_sorts ( x : quantifier ) =
    let n = (get_num_bound x) in
    let f i = (Sort.sort_of_ptr (gc x) (Z3native.get_quantifier_bound_sort (gnc x) (gno x) i)) in
    mk_list f n
      
  let get_body ( x : quantifier ) =
    expr_of_ptr (gc x) (Z3native.get_quantifier_body (gnc x) (gno x))  

  let mk_bound ( ctx : context ) ( index : int ) ( ty : Sort.sort ) =
    expr_of_ptr ctx (Z3native.mk_bound (context_gno ctx) index (Sort.gno ty))

  let mk_pattern ( ctx : context ) ( terms : expr list ) =
    if (List.length terms) == 0 then
      raise (Z3native.Exception "Cannot create a pattern from zero terms")
    else
      Pattern.Pattern(z3_native_object_of_ast_ptr ctx (Z3native.mk_pattern (context_gno ctx) (List.length terms) (expr_lton terms)))

  let mk_forall ( ctx : context ) ( sorts : Sort.sort list ) ( names : Symbol.symbol list ) ( body : expr ) ( weight : int option ) ( patterns : Pattern.pattern list ) ( nopatterns : expr list ) ( quantifier_id : Symbol.symbol option ) ( skolem_id : Symbol.symbol option ) =
    if (List.length sorts) != (List.length names) then
      raise (Z3native.Exception "Number of sorts does not match number of names")
    else if ((List.length nopatterns) == 0 && quantifier_id == None && skolem_id == None) then
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier (context_gno ctx) true 
				    (match weight with | None -> 1 | Some(x) -> x)
				    (List.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.of_list (List.map f patterns)))
				    (List.length sorts) (Sort.sort_lton sorts)
				    (Symbol.symbol_lton names)
				    (Expr.gno body)))
    else
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier_ex (context_gno ctx) true
				    (match weight with | None -> 1 | Some(x) -> x)
				    (match quantifier_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (match skolem_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (List.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.of_list (List.map f patterns)))
				    (List.length nopatterns) (expr_lton nopatterns)
				    (List.length sorts) (Sort.sort_lton sorts)
				    (Symbol.symbol_lton names)
				    (Expr.gno body)))
	
  let mk_forall_const ( ctx : context ) ( bound_constants : expr list ) ( body : expr ) ( weight : int option ) ( patterns : Pattern.pattern list ) ( nopatterns : expr list ) ( quantifier_id : Symbol.symbol option ) ( skolem_id : Symbol.symbol option ) =
    if ((List.length nopatterns) == 0 && quantifier_id == None && skolem_id == None) then
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier_const (context_gno ctx) true
				    (match weight with | None -> 1 | Some(x) -> x)
				    (List.length bound_constants) (expr_lton bound_constants)
				    (List.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.of_list (List.map f patterns)))
				    (Expr.gno body)))
    else
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier_const_ex (context_gno ctx) true
				    (match weight with | None -> 1 | Some(x) -> x)
				    (match quantifier_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (match skolem_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (List.length bound_constants) (expr_lton bound_constants)
				    (List.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.of_list (List.map f patterns)))
				    (List.length nopatterns) (expr_lton nopatterns)
				    (Expr.gno body)))

  let mk_exists ( ctx : context ) ( sorts : Sort.sort list ) ( names : Symbol.symbol list ) ( body : expr ) ( weight : int option ) ( patterns : Pattern.pattern list ) ( nopatterns : expr list ) ( quantifier_id : Symbol.symbol option ) ( skolem_id : Symbol.symbol option ) =
    if (List.length sorts) != (List.length names) then
      raise (Z3native.Exception "Number of sorts does not match number of names")
    else if ((List.length nopatterns) == 0 && quantifier_id == None && skolem_id == None) then
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier (context_gno ctx) false
				    (match weight with | None -> 1 | Some(x) -> x)
				    (List.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.of_list (List.map f patterns)))
				    (List.length sorts) (Sort.sort_lton sorts)
				    (Symbol.symbol_lton names)
				    (Expr.gno body)))
    else
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier_ex (context_gno ctx) false
				    (match weight with | None -> 1 | Some(x) -> x)
				    (match quantifier_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (match skolem_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (List.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.of_list (List.map f patterns)))
				    (List.length nopatterns) (expr_lton nopatterns)
				    (List.length sorts) (Sort.sort_lton sorts)
				    (Symbol.symbol_lton names)
				    (Expr.gno body)))
	
  let mk_exists_const ( ctx : context ) ( bound_constants : expr list ) ( body : expr ) ( weight : int option ) ( patterns : Pattern.pattern list ) ( nopatterns : expr list ) ( quantifier_id : Symbol.symbol option ) ( skolem_id : Symbol.symbol option ) =
    if ((List.length nopatterns) == 0 && quantifier_id == None && skolem_id == None) then
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier_const (context_gno ctx) false
				    (match weight with | None -> 1 | Some(x) -> x)
				    (List.length bound_constants) (expr_lton bound_constants)
				    (List.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.of_list (List.map f patterns)))
				    (Expr.gno body)))
    else
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier_const_ex (context_gno ctx) false
				    (match weight with | None -> 1 | Some(x) -> x)
				    (match quantifier_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (match skolem_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (List.length bound_constants) (expr_lton bound_constants)
				    (List.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.of_list (List.map f patterns)))
				    (List.length nopatterns) (expr_lton nopatterns)
				    (Expr.gno body)))

  let mk_quantifier ( ctx : context ) ( universal : bool ) ( sorts : Sort.sort list ) ( names : Symbol.symbol list ) ( body : expr ) ( weight : int option ) ( patterns : Pattern.pattern list ) ( nopatterns : expr list ) ( quantifier_id : Symbol.symbol option ) ( skolem_id : Symbol.symbol option ) =
    if (universal) then
      (mk_forall ctx sorts names body weight patterns nopatterns quantifier_id skolem_id)
    else
      (mk_exists ctx sorts names body weight patterns nopatterns quantifier_id skolem_id)

  let mk_quantifier ( ctx : context ) ( universal : bool ) ( bound_constants : expr list ) ( body : expr ) ( weight : int option ) ( patterns : Pattern.pattern list ) ( nopatterns : expr list ) ( quantifier_id : Symbol.symbol option ) ( skolem_id : Symbol.symbol option ) =
    if (universal) then
      mk_forall_const ctx bound_constants body weight patterns nopatterns quantifier_id skolem_id
    else
      mk_exists_const ctx bound_constants body weight patterns nopatterns quantifier_id skolem_id

  let to_string ( x : quantifier ) = (Expr.to_string (expr_of_quantifier x))
end


module Z3Array = 
struct
  let mk_sort ( ctx : context ) ( domain : Sort.sort ) ( range : Sort.sort ) =
    Sort.sort_of_ptr ctx (Z3native.mk_array_sort (context_gno ctx) (Sort.gno domain) (Sort.gno range))

  let is_store ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_STORE)
  let is_select ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SELECT)
  let is_constant_array ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_CONST_ARRAY)
  let is_default_array ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ARRAY_DEFAULT)
  let is_array_map ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ARRAY_MAP)
  let is_as_array ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_AS_ARRAY)       
  let is_array ( x : expr ) =
    (Z3native.is_app (Expr.gnc x) (Expr.gno x)) &&
      ((sort_kind_of_int (Z3native.get_sort_kind (Expr.gnc x) (Z3native.get_sort (Expr.gnc x) (Expr.gno x)))) == ARRAY_SORT)      

  let get_domain ( x : Sort.sort ) = Sort.sort_of_ptr (Sort.gc x) (Z3native.get_array_sort_domain (Sort.gnc x) (Sort.gno x))
  let get_range ( x : Sort.sort ) = Sort.sort_of_ptr (Sort.gc x) (Z3native.get_array_sort_range (Sort.gnc x) (Sort.gno x))

  let mk_const ( ctx : context ) ( name : Symbol.symbol ) ( domain : Sort.sort ) ( range : Sort.sort ) = 
    (Expr.mk_const ctx name (mk_sort ctx domain range))
      
  let mk_const_s ( ctx : context ) ( name : string ) ( domain : Sort.sort ) ( range : Sort.sort ) =	
    mk_const ctx (Symbol.mk_string ctx name) domain range
      
  let mk_select ( ctx : context ) ( a : expr ) ( i : expr ) =
    expr_of_ptr ctx (Z3native.mk_select (context_gno ctx) (Expr.gno a) (Expr.gno i))      

  let mk_store ( ctx : context ) ( a : expr ) ( i : expr ) ( v : expr ) =
    expr_of_ptr ctx (Z3native.mk_store (context_gno ctx) (Expr.gno a) (Expr.gno i) (Expr.gno v))

  let mk_const_array ( ctx : context ) ( domain : Sort.sort ) ( v : expr ) =
    expr_of_ptr ctx (Z3native.mk_const_array (context_gno ctx) (Sort.gno domain) (Expr.gno v))

  let mk_map ( ctx : context ) ( f : func_decl ) ( args : expr list ) =
    let m x = (Expr.gno x) in    
    expr_of_ptr ctx (Z3native.mk_map (context_gno ctx) (FuncDecl.gno f) (List.length args) (Array.of_list (List.map m args)))

  let mk_term_array  ( ctx : context ) ( arg : expr ) =
    expr_of_ptr ctx (Z3native.mk_array_default (context_gno ctx) (Expr.gno arg))
end


module Set = 
struct     
  let mk_sort  ( ctx : context ) ( ty : Sort.sort ) =
    Sort.sort_of_ptr ctx (Z3native.mk_set_sort (context_gno ctx) (Sort.gno ty))

  let is_union ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_UNION)
  let is_intersect ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_INTERSECT)
  let is_difference ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_DIFFERENCE)
  let is_complement ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_COMPLEMENT)
  let is_subset ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_SUBSET)


  let mk_empty ( ctx : context ) ( domain : Sort.sort ) =
    (expr_of_ptr ctx (Z3native.mk_empty_set (context_gno ctx) (Sort.gno domain)))
      
  let mk_full ( ctx : context ) ( domain : Sort.sort ) =
    expr_of_ptr ctx (Z3native.mk_full_set (context_gno ctx) (Sort.gno domain))

  let mk_set_add  ( ctx : context ) ( set : expr ) ( element : expr ) =
    expr_of_ptr ctx (Z3native.mk_set_add (context_gno ctx) (Expr.gno set) (Expr.gno element))
      
  let mk_del  ( ctx : context ) ( set : expr ) ( element : expr ) =
    expr_of_ptr ctx (Z3native.mk_set_del (context_gno ctx) (Expr.gno set) (Expr.gno element))
      
  let mk_union  ( ctx : context ) ( args : expr list ) =
    expr_of_ptr ctx (Z3native.mk_set_union (context_gno ctx) (List.length args) (expr_lton args))
      
  let mk_intersection  ( ctx : context ) ( args : expr list ) =
    expr_of_ptr ctx (Z3native.mk_set_intersect (context_gno ctx) (List.length args) (expr_lton args))

  let mk_difference  ( ctx : context ) ( arg1 : expr ) ( arg2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_set_difference (context_gno ctx) (Expr.gno arg1) (Expr.gno arg2))

  let mk_complement  ( ctx : context ) ( arg : expr ) =
    expr_of_ptr ctx (Z3native.mk_set_complement (context_gno ctx) (Expr.gno arg))

  let mk_membership  ( ctx : context ) ( elem : expr ) ( set : expr ) =
    expr_of_ptr ctx (Z3native.mk_set_member (context_gno ctx) (Expr.gno elem) (Expr.gno set))

  let mk_subset  ( ctx : context ) ( arg1 : expr ) ( arg2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_set_subset (context_gno ctx) (Expr.gno arg1) (Expr.gno arg2))

end


module FiniteDomain = 
struct  
  let mk_sort ( ctx : context ) ( name : Symbol.symbol ) ( size : int ) =
    Sort.sort_of_ptr ctx (Z3native.mk_finite_domain_sort (context_gno ctx) (Symbol.gno name) size)
      
  let mk_sort_s ( ctx : context ) ( name : string ) ( size : int ) =
    mk_sort ctx (Symbol.mk_string ctx name) size

  let is_finite_domain ( x : expr ) =
    let nc = (Expr.gnc x) in
    (Z3native.is_app (Expr.gnc x) (Expr.gno x)) &&
      (sort_kind_of_int (Z3native.get_sort_kind nc (Z3native.get_sort nc (Expr.gno x))) == FINITE_DOMAIN_SORT)

  let is_lt ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FD_LT)

  let get_size ( x : Sort.sort ) = 
    let (r, v) = (Z3native.get_finite_domain_sort_size (Sort.gnc x) (Sort.gno x)) in
    if r then v
    else raise (Z3native.Exception "Conversion failed.")
end


module Relation = 
struct
  let is_relation ( x : expr ) =
    let nc = (Expr.gnc x) in
    ((Z3native.is_app (Expr.gnc x) (Expr.gno x)) &&
	(sort_kind_of_int (Z3native.get_sort_kind nc (Z3native.get_sort nc (Expr.gno x))) == RELATION_SORT))

  let is_store ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_STORE)
  let is_empty ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_EMPTY)
  let is_is_empty ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_IS_EMPTY)
  let is_join ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_JOIN)
  let is_union ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_UNION)
  let is_widen ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_WIDEN)
  let is_project ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_PROJECT)
  let is_filter ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_FILTER)
  let is_negation_filter ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_NEGATION_FILTER)
  let is_rename ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_RENAME)
  let is_complement ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_COMPLEMENT)
  let is_select ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_SELECT)
  let is_clone ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_CLONE)

  let get_arity ( x : Sort.sort ) = Z3native.get_relation_arity (Sort.gnc x) (Sort.gno x)

  let get_column_sorts ( x : Sort.sort ) = 
    let n = get_arity x in
    let f i = (Sort.sort_of_ptr (Sort.gc x) (Z3native.get_relation_column (Sort.gnc x) (Sort.gno x) i)) in
    mk_list f n
end
  

module Datatype = 
struct
  module Constructor = 
  struct
    type constructor = z3_native_object
	
    module FieldNumTable = Hashtbl.Make(struct 
      type t = AST.ast
      let equal x y = AST.compare x y = 0
      let hash = AST.hash
    end)

    let _field_nums = FieldNumTable.create 0

    let create ( ctx : context ) ( name : Symbol.symbol ) ( recognizer : Symbol.symbol ) ( field_names : Symbol.symbol list ) ( sorts : Sort.sort option list ) ( sort_refs : int list ) =
      let n = (List.length field_names) in
      if n != (List.length sorts) then
	raise (Z3native.Exception "Number of field names does not match number of sorts")
      else
	if n != (List.length sort_refs) then
	  raise (Z3native.Exception "Number of field names does not match number of sort refs")
	else
          let ptr = (Z3native.mk_constructor (context_gno ctx) (Symbol.gno name) 
		       (Symbol.gno recognizer) 
		       n
		       (Symbol.symbol_lton field_names)
		       (Sort.sort_option_lton sorts)
		       (Array.of_list sort_refs)) in
	  let no : constructor = { m_ctx = ctx ;
				   m_n_obj = null ;
				   inc_ref = z3obj_nil_ref ;
				   dec_ref = z3obj_nil_ref} in
	  (z3obj_sno no ctx ptr) ;
	  (z3obj_create no) ;
	  let f = fun o -> Z3native.del_constructor (z3obj_gnc o) (z3obj_gno o) in
	  Gc.finalise f no ;
	  FieldNumTable.add _field_nums no n ;
	  no    	  
	    
    let get_num_fields ( x : constructor ) = FieldNumTable.find _field_nums x

    let get_constructor_decl ( x : constructor ) = 
      let (a, _, _) = (Z3native.query_constructor (z3obj_gnc x) (z3obj_gno x) (get_num_fields x)) in
      func_decl_of_ptr (z3obj_gc x) a

    let get_tester_decl ( x : constructor ) =
      let (_, b, _) = (Z3native.query_constructor (z3obj_gnc x) (z3obj_gno x) (get_num_fields x)) in
      func_decl_of_ptr (z3obj_gc x) b	

    let get_accessor_decls ( x : constructor ) = 
      let (_, _, c) = (Z3native.query_constructor (z3obj_gnc x) (z3obj_gno x) (get_num_fields x)) in
      let f i = func_decl_of_ptr (z3obj_gc x) (Array.get c i) in
      mk_list f (Array.length c)
	
  end

  module ConstructorList =
  struct
    type constructor_list = z3_native_object 

    let create ( ctx : context ) ( c : Constructor.constructor list ) =
      let res : constructor_list = { m_ctx = ctx ;
				     m_n_obj = null ;
				     inc_ref = z3obj_nil_ref ;
				     dec_ref = z3obj_nil_ref} in
      let f x =(z3obj_gno x) in 
      (z3obj_sno res ctx (Z3native.mk_constructor_list (context_gno ctx) (List.length c) (Array.of_list (List.map f c)))) ;
      (z3obj_create res) ;
      let f = fun o -> Z3native.del_constructor_list (z3obj_gnc o) (z3obj_gno o) in      
      Gc.finalise f res;
      res       
  end
    
  let mk_constructor ( ctx : context ) ( name : Symbol.symbol ) ( recognizer : Symbol.symbol ) ( field_names : Symbol.symbol list ) ( sorts : Sort.sort option list ) ( sort_refs : int list ) =
    Constructor.create ctx name recognizer field_names sorts sort_refs


  let mk_constructor_s ( ctx : context ) ( name : string ) ( recognizer : Symbol.symbol ) ( field_names : Symbol.symbol list ) ( sorts : Sort.sort option list ) ( sort_refs : int list ) =
    mk_constructor ctx (Symbol.mk_string ctx name) recognizer field_names sorts sort_refs

  let mk_sort ( ctx : context ) ( name : Symbol.symbol ) ( constructors : Constructor.constructor list ) =
    let f x = (z3obj_gno x) in 
    let (x,_) = (Z3native.mk_datatype (context_gno ctx) (Symbol.gno name) (List.length constructors) (Array.of_list (List.map f constructors))) in
    Sort.sort_of_ptr ctx x

  let mk_sort_s ( ctx : context ) ( name : string ) ( constructors : Constructor.constructor list ) =
    mk_sort ctx (Symbol.mk_string ctx name) constructors
      
  let mk_sorts ( ctx : context ) ( names : Symbol.symbol list ) ( c : Constructor.constructor list list ) =
    let n = (List.length names) in
    let f e = (AST.ptr_of_ast (ConstructorList.create ctx e)) in
    let cla = (Array.of_list (List.map f c)) in
    let (r, a) = (Z3native.mk_datatypes (context_gno ctx) n (Symbol.symbol_lton names) cla) in
    let g i = (Sort.sort_of_ptr ctx (Array.get r i)) in
    mk_list g (Array.length r)

  let mk_sorts_s ( ctx : context ) ( names : string list ) ( c : Constructor.constructor list list ) =
    mk_sorts ctx 
      ( 
	let f e = (Symbol.mk_string ctx e) in
	List.map f names 
      )
      c

  let get_num_constructors ( x : Sort.sort ) = Z3native.get_datatype_sort_num_constructors (Sort.gnc x) (Sort.gno x)

  let get_constructors ( x : Sort.sort ) = 
    let n = (get_num_constructors x) in
    let f i = func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_constructor (Sort.gnc x) (Sort.gno x) i) in
    mk_list f n

  let get_recognizers ( x : Sort.sort ) = 
    let n = (get_num_constructors x) in
    let f i = func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_recognizer (Sort.gnc x) (Sort.gno x) i) in
    mk_list f n
      
  let get_accessors ( x : Sort.sort ) =
    let n = (get_num_constructors x) in
    let f i = (
      let fd = func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_constructor (Sort.gnc x) (Sort.gno x) i) in
      let ds = Z3native.get_domain_size (FuncDecl.gnc fd) (FuncDecl.gno fd) in
      let g j = func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_constructor_accessor (Sort.gnc x) (Sort.gno x) i j) in
      mk_list g ds
    ) in
    mk_list f n
end


module Enumeration = 
struct 
  let mk_sort ( ctx : context ) ( name : Symbol.symbol ) ( enum_names : Symbol.symbol list ) =
    let (a, _, _) = (Z3native.mk_enumeration_sort (context_gno ctx) (Symbol.gno name) (List.length enum_names) (Symbol.symbol_lton enum_names)) in
    Sort.sort_of_ptr ctx a

  let mk_sort_s ( ctx : context ) ( name : string ) ( enum_names : string list ) =
    mk_sort ctx (Symbol.mk_string ctx name) (Symbol.mk_strings ctx enum_names)

  let get_const_decls ( x : Sort.sort ) =
    let n = Z3native.get_datatype_sort_num_constructors (Sort.gnc x) (Sort.gno x)  in
    let f i = (func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_constructor (Sort.gnc x) (Sort.gno x)  i)) in
    mk_list f n

  let get_const_decl ( x : Sort.sort ) ( inx : int ) =
    func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_constructor (Sort.gnc x) (Sort.gno x) inx)

  let get_consts ( x : Sort.sort ) =
    let n = Z3native.get_datatype_sort_num_constructors (Sort.gnc x) (Sort.gno x)  in
    let f i = (Expr.mk_const_f (Sort.gc x) (get_const_decl x i)) in
    mk_list f n

  let get_const ( x : Sort.sort ) ( inx : int ) =
    Expr.mk_const_f (Sort.gc x) (get_const_decl x inx)

  let get_tester_decls ( x : Sort.sort ) = 
    let n = Z3native.get_datatype_sort_num_constructors (Sort.gnc x) (Sort.gno x)  in
    let f i = (func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_recognizer (Sort.gnc x) (Sort.gno x) i)) in
    mk_list f n
      
  let get_tester_decl ( x : Sort.sort ) ( inx : int ) = 
    func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_recognizer (Sort.gnc x) (Sort.gno x) inx)
end


module Z3List = 
struct     
  let mk_sort ( ctx : context ) ( name : Symbol.symbol ) ( elem_sort : Sort.sort ) =
    let (r, _, _, _, _, _, _) = (Z3native.mk_list_sort (context_gno ctx) (Symbol.gno name) (Sort.gno elem_sort)) in
    Sort.sort_of_ptr ctx r 
      
  let mk_list_s ( ctx : context ) ( name : string ) elem_sort =
    mk_sort ctx (Symbol.mk_string ctx name) elem_sort

  let get_nil_decl ( x : Sort.sort ) = 
    func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_constructor (Sort.gnc x) (Sort.gno x)  0)

  let get_is_nil_decl ( x : Sort.sort ) = 
    func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_recognizer (Sort.gnc x) (Sort.gno x)  0)

  let get_cons_decl ( x : Sort.sort ) = 
    func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_constructor (Sort.gnc x) (Sort.gno x)  1)

  let get_is_cons_decl ( x : Sort.sort ) =
    func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_recognizer (Sort.gnc x) (Sort.gno x)  1)

  let get_head_decl ( x : Sort.sort )  = 
    func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_constructor_accessor (Sort.gnc x) (Sort.gno x) 1 0)

  let get_tail_decl ( x : Sort.sort ) =
    func_decl_of_ptr (Sort.gc x) (Z3native.get_datatype_sort_constructor_accessor (Sort.gnc x) (Sort.gno x) 1 1)

  let nil ( x : Sort.sort ) = expr_of_func_app (Sort.gc x) (get_nil_decl x) []
end


module Tuple = 
struct
  let mk_sort ( ctx : context ) ( name : Symbol.symbol ) ( field_names : Symbol.symbol list ) ( field_sorts : Sort.sort list ) =
    let (r, _, _) = (Z3native.mk_tuple_sort (context_gno ctx) (Symbol.gno name) (List.length field_names) (Symbol.symbol_lton field_names) (Sort.sort_lton field_sorts)) in 
    Sort.sort_of_ptr ctx r

  let get_mk_decl ( x : Sort.sort ) =
    func_decl_of_ptr (Sort.gc x) (Z3native.get_tuple_sort_mk_decl (Sort.gnc x) (Sort.gno x))

  let get_num_fields ( x : Sort.sort ) = Z3native.get_tuple_sort_num_fields (Sort.gnc x) (Sort.gno x)
    
  let get_field_decls ( x : Sort.sort ) = 
    let n = get_num_fields x in
    let f i = func_decl_of_ptr (Sort.gc x) (Z3native.get_tuple_sort_field_decl (Sort.gnc x) (Sort.gno x) i) in
    mk_list f n
end


module Arithmetic =
struct
  let is_int ( x : expr ) =
    (Z3native.is_numeral_ast (Expr.gnc x) (Expr.gno x)) &&
      ((sort_kind_of_int (Z3native.get_sort_kind (Expr.gnc x) (Z3native.get_sort (Expr.gnc x) (Expr.gno x)))) == INT_SORT)
      
  let is_arithmetic_numeral ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ANUM)

  let is_le ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_LE)

  let is_ge ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_GE)

  let is_lt ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_LT)

  let is_gt ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_GT)

  let is_add ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ADD)

  let is_sub ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SUB)

  let is_uminus ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_UMINUS)

  let is_mul ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_MUL)

  let is_div ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_DIV)

  let is_idiv ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_IDIV)

  let is_remainder ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_REM)

  let is_modulus ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_MOD)

  let is_int2real ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_TO_REAL)

  let is_real2int ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_TO_INT)

  let is_real_is_int ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_IS_INT)

  let is_real ( x : expr ) =
    ((sort_kind_of_int (Z3native.get_sort_kind (Expr.gnc x) (Z3native.get_sort (Expr.gnc x) (Expr.gno x)))) == REAL_SORT)
      
  let is_int_numeral ( x : expr ) = (Expr.is_numeral x) && (is_int x)

  let is_rat_numeral ( x : expr ) = (Expr.is_numeral x) && (is_real x)
    
  let is_algebraic_number ( x : expr ) = Z3native.is_algebraic_number (Expr.gnc x) (Expr.gno x)

  module Integer =
  struct     
    let mk_sort ( ctx : context ) =
      Sort.sort_of_ptr ctx (Z3native.mk_int_sort (context_gno ctx))

    let get_int ( x : expr ) = 
      let (r, v) = Z3native.get_numeral_int (Expr.gnc x) (Expr.gno x) in
      if r then v
      else raise (Z3native.Exception "Conversion failed.")

    let get_big_int ( x : expr ) = 
      if (is_int_numeral x) then 
	let s = (Z3native.get_numeral_string (Expr.gnc x) (Expr.gno x)) in
	(Big_int.big_int_of_string s)
      else raise (Z3native.Exception "Conversion failed.")
	
    let numeral_to_string ( x : expr ) = Z3native.get_numeral_string (Expr.gnc x) (Expr.gno x)

    let mk_const ( ctx : context ) ( name : Symbol.symbol ) =
      Expr.mk_const ctx name (mk_sort ctx) 
	
    let mk_const_s ( ctx : context ) ( name : string )  =
      mk_const ctx (Symbol.mk_string ctx name)
	
    let mk_mod ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =    
      expr_of_ptr ctx (Z3native.mk_mod (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
	
    let mk_rem ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
      expr_of_ptr  ctx (Z3native.mk_rem (context_gno ctx) (Expr.gno t1) (Expr.gno t2))

    let mk_numeral_s ( ctx : context ) ( v : string ) =
      expr_of_ptr ctx (Z3native.mk_numeral (context_gno ctx) v (Sort.gno (mk_sort ctx)))
	
    let mk_numeral_i ( ctx : context ) ( v : int ) =
      expr_of_ptr ctx (Z3native.mk_int (context_gno ctx) v (Sort.gno (mk_sort ctx)))

    let mk_int2real ( ctx : context ) ( t : expr ) =
      (Expr.expr_of_ptr ctx (Z3native.mk_int2real (context_gno ctx) (Expr.gno t)))

    let mk_int2bv ( ctx : context ) ( n : int ) ( t : expr ) =
      (Expr.expr_of_ptr ctx (Z3native.mk_int2bv (context_gno ctx) n (Expr.gno t)))
  end

  module Real =
  struct  
    let mk_sort ( ctx : context ) =
      Sort.sort_of_ptr ctx (Z3native.mk_real_sort (context_gno ctx))	

    let get_numerator ( x : expr ) =
      expr_of_ptr (Expr.gc x) (Z3native.get_numerator (Expr.gnc x) (Expr.gno x))
	
    let get_denominator ( x : expr ) =
      expr_of_ptr (Expr.gc x) (Z3native.get_denominator (Expr.gnc x) (Expr.gno x))
	
    let get_ratio ( x : expr ) = 
      if (is_rat_numeral x)  then
	let s = (Z3native.get_numeral_string (Expr.gnc x) (Expr.gno x)) in
	(Ratio.ratio_of_string s)
      else raise (Z3native.Exception "Conversion failed.")

    let to_decimal_string ( x : expr ) ( precision : int ) = 
      Z3native.get_numeral_decimal_string (Expr.gnc x) (Expr.gno x) precision
	
    let numeral_to_string ( x : expr ) = Z3native.get_numeral_string (Expr.gnc x) (Expr.gno x)

    let mk_const ( ctx : context ) ( name : Symbol.symbol )  =
      Expr.mk_const ctx name (mk_sort ctx)
	
    let mk_const_s ( ctx : context ) ( name : string )  =
      mk_const ctx (Symbol.mk_string ctx name)

    let mk_numeral_nd ( ctx : context ) ( num : int ) ( den : int ) =
      if (den == 0) then 
	raise (Z3native.Exception "Denominator is zero")
      else      
	expr_of_ptr ctx (Z3native.mk_real (context_gno ctx) num den)
	  
    let mk_numeral_s ( ctx : context ) ( v : string ) =
      expr_of_ptr ctx (Z3native.mk_numeral (context_gno ctx) v (Sort.gno (mk_sort ctx)))
	
    let mk_numeral_i ( ctx : context ) ( v : int ) =
      expr_of_ptr ctx (Z3native.mk_int (context_gno ctx) v (Sort.gno (mk_sort ctx)))
	
    let mk_is_integer ( ctx : context ) ( t : expr ) =
      (expr_of_ptr ctx (Z3native.mk_is_int (context_gno ctx) (Expr.gno t)))
	
    let mk_real2int ( ctx : context ) ( t : expr ) =
      (expr_of_ptr ctx (Z3native.mk_real2int (context_gno ctx) (Expr.gno t)))

    module AlgebraicNumber =
    struct    
      let to_upper ( x : expr ) ( precision : int ) =
	    expr_of_ptr (Expr.gc x) (Z3native.get_algebraic_number_upper (Expr.gnc x) (Expr.gno x) precision)
	      
      let to_lower ( x : expr ) precision =
	    expr_of_ptr (Expr.gc x) (Z3native.get_algebraic_number_lower (Expr.gnc x) (Expr.gno x) precision)
	      
      let to_decimal_string ( x : expr ) ( precision : int ) = 
	    Z3native.get_numeral_decimal_string (Expr.gnc x) (Expr.gno x) precision	
	      
      let numeral_to_string ( x : expr ) = Z3native.get_numeral_string (Expr.gnc x) (Expr.gno x)      
    end
  end

  let mk_add ( ctx : context ) ( t : expr list ) =
    let f x = (Expr.gno x) in
    (expr_of_ptr ctx (Z3native.mk_add (context_gno ctx) (List.length t) (Array.of_list (List.map f t))))

  let mk_mul ( ctx : context ) ( t : expr list ) =
    let f x = (Expr.gno x) in
    (expr_of_ptr ctx (Z3native.mk_mul (context_gno ctx) (List.length t) (Array.of_list (List.map f t))))

  let mk_sub ( ctx : context ) ( t : expr list ) =
    let f x = (Expr.gno x) in
    (expr_of_ptr ctx (Z3native.mk_sub (context_gno ctx) (List.length t) (Array.of_list (List.map f t))))
      
  let mk_unary_minus ( ctx : context ) ( t : expr ) =     
    (expr_of_ptr ctx (Z3native.mk_unary_minus (context_gno ctx) (Expr.gno t)))

  let mk_div ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_div (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))

  let mk_power ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =     
    (expr_of_ptr ctx (Z3native.mk_power (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))

  let mk_lt ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_lt (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))

  let mk_le ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_le (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))
      
  let mk_gt ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_gt (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))

  let mk_ge ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_ge (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))
end


module BitVector =
struct  
  let mk_sort ( ctx : context ) size =
    Sort.sort_of_ptr ctx (Z3native.mk_bv_sort (context_gno ctx) size)
  let is_bv ( x : expr ) =
    ((sort_kind_of_int (Z3native.get_sort_kind (Expr.gnc x) (Z3native.get_sort (Expr.gnc x) (Expr.gno x)))) == BV_SORT)
  let is_bv_numeral ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNUM)
  let is_bv_bit1 ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BIT1)
  let is_bv_bit0 ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BIT0)
  let is_bv_uminus ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNEG)
  let is_bv_add ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BADD)
  let is_bv_sub ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSUB)
  let is_bv_mul ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BMUL)
  let is_bv_sdiv ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSDIV)
  let is_bv_udiv ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BUDIV)
  let is_bv_SRem ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSREM)
  let is_bv_urem ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BUREM)
  let is_bv_smod ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSMOD)
  let is_bv_sdiv0 ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSDIV0)
  let is_bv_udiv0 ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BUDIV0)
  let is_bv_srem0 ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSREM0)
  let is_bv_urem0 ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BUREM0)
  let is_bv_smod0 ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSMOD0)
  let is_bv_ule ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ULEQ)
  let is_bv_sle ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SLEQ)
  let is_bv_uge ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_UGEQ)
  let is_bv_sge ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SGEQ)
  let is_bv_ult ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ULT)
  let is_bv_slt ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SLT)
  let is_bv_ugt ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_UGT)
  let is_bv_sgt ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SGT)
  let is_bv_and ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BAND)
  let is_bv_or ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BOR)
  let is_bv_not ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNOT)
  let is_bv_xor ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BXOR)
  let is_bv_nand ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNAND)
  let is_bv_nor ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNOR)
  let is_bv_xnor ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BXNOR)
  let is_bv_concat ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_CONCAT)
  let is_bv_signextension ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SIGN_EXT)
  let is_bv_zeroextension ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ZERO_EXT)
  let is_bv_extract ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_EXTRACT)
  let is_bv_repeat ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_REPEAT)
  let is_bv_reduceor ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BREDOR)
  let is_bv_reduceand ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BREDAND)
  let is_bv_comp ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BCOMP)
  let is_bv_shiftleft ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSHL)
  let is_bv_shiftrightlogical ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BLSHR)
  let is_bv_shiftrightarithmetic ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BASHR)
  let is_bv_rotateleft ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ROTATE_LEFT)
  let is_bv_rotateright ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ROTATE_RIGHT)
  let is_bv_rotateleftextended ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_EXT_ROTATE_LEFT)
  let is_bv_rotaterightextended ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_EXT_ROTATE_RIGHT) 
  let is_int2bv ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_INT2BV)
  let is_bv2int ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BV2INT)
  let is_bv_carry ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_CARRY)
  let is_bv_xor3 ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_XOR3)
  let get_size (x : Sort.sort ) = Z3native.get_bv_sort_size (Sort.gnc x) (Sort.gno x)
  let get_int ( x : expr ) = 
    let (r, v) = Z3native.get_numeral_int (Expr.gnc x) (Expr.gno x) in
    if r then v
    else raise (Z3native.Exception "Conversion failed.")
  let numeral_to_string ( x : expr ) = Z3native.get_numeral_string (Expr.gnc x) (Expr.gno x)
  let mk_const ( ctx : context ) ( name : Symbol.symbol ) ( size : int ) =
    Expr.mk_const ctx name (mk_sort ctx size) 
  let mk_const_s ( ctx : context ) ( name : string ) ( size : int ) =
    mk_const ctx (Symbol.mk_string ctx name) size
  let mk_not  ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvnot (context_gno ctx) (Expr.gno t))
  let mk_redand  ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvredand (context_gno ctx) (Expr.gno t))
  let mk_redor  ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvredor (context_gno ctx) (Expr.gno t))
  let mk_and  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvand (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_or  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvor (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_xor  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvxor (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_nand  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvnand (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_nor  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvnor (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_xnor  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvxnor (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_neg  ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvneg (context_gno ctx) (Expr.gno t))
  let mk_add  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvadd (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_sub  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvsub (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_mul  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvmul (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_udiv  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvudiv (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_sdiv  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvsdiv (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_urem  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvurem (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_srem  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvsrem (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_smod  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvsmod (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_ult  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_bvult (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))  
  let mk_slt  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_bvslt (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))
  let mk_ule  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_bvule (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))
  let mk_sle  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_bvsle (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))
  let mk_uge  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_bvuge (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))
  let mk_sge  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_bvsge (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))
  let mk_ugt  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_bvugt (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))   		  
  let mk_sgt  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_bvsgt (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))   		  
  let mk_concat ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_concat (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_extract ( ctx : context ) ( high : int ) ( low : int ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_extract (context_gno ctx) high low (Expr.gno t))
  let mk_sign_ext  ( ctx : context ) ( i : int ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_sign_ext (context_gno ctx) i (Expr.gno t))
  let mk_zero_ext  ( ctx : context ) ( i : int ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_zero_ext (context_gno ctx) i (Expr.gno t))
  let mk_repeat  ( ctx : context ) ( i : int ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_repeat (context_gno ctx) i (Expr.gno t))
  let mk_shl  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvshl (context_gno ctx) (Expr.gno t1) (Expr.gno t2))	  
  let mk_lshr  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_bvlshr (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_ashr  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =    
    expr_of_ptr ctx  (Z3native.mk_bvashr (context_gno ctx) (Expr.gno t1) (Expr.gno t2))  
  let mk_rotate_left  ( ctx : context ) ( i : int ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_rotate_left (context_gno ctx) i (Expr.gno t))
  let mk_rotate_right ( ctx : context ) ( i : int ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_rotate_right (context_gno ctx) i (Expr.gno t))
  let mk_ext_rotate_left ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_ext_rotate_left (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_ext_rotate_right ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_ext_rotate_right (context_gno ctx) (Expr.gno t1) (Expr.gno t2))	  
  let mk_bv2int ( ctx : context ) ( t : expr ) ( signed : bool ) =
    expr_of_ptr ctx (Z3native.mk_bv2int (context_gno ctx) (Expr.gno t) signed)
  let mk_add_no_overflow  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) ( signed : bool) =
    (expr_of_ptr ctx (Z3native.mk_bvadd_no_overflow (context_gno ctx) (Expr.gno t1) (Expr.gno t2) signed))
  let mk_add_no_underflow  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_bvadd_no_underflow (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))	  
  let mk_sub_no_overflow  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_bvsub_no_overflow (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))		  
  let mk_sub_no_underflow  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) ( signed : bool) =
    (expr_of_ptr ctx (Z3native.mk_bvsub_no_underflow (context_gno ctx) (Expr.gno t1) (Expr.gno t2) signed))
  let mk_sdiv_no_overflow  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_bvsdiv_no_overflow (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))
  let mk_neg_no_overflow  ( ctx : context ) ( t : expr ) =
    (expr_of_ptr ctx (Z3native.mk_bvneg_no_overflow (context_gno ctx) (Expr.gno t)))
  let mk_mul_no_overflow  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) ( signed : bool) =
    (expr_of_ptr ctx (Z3native.mk_bvmul_no_overflow (context_gno ctx) (Expr.gno t1) (Expr.gno t2) signed))
  let mk_mul_no_underflow  ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    (expr_of_ptr ctx (Z3native.mk_bvmul_no_underflow (context_gno ctx) (Expr.gno t1) (Expr.gno t2)))	  
  let mk_numeral ( ctx : context ) ( v : string ) ( size : int ) =
    expr_of_ptr ctx (Z3native.mk_numeral (context_gno ctx) v (Sort.gno (mk_sort ctx size)))
end


module FloatingPoint = 
struct
  module RoundingMode = 
  struct
	let mk_sort ( ctx : context ) =
	  (Sort.sort_of_ptr ctx (Z3native.mk_fpa_rounding_mode_sort (context_gno ctx)))
	let is_fprm ( x : expr ) =
	  (Sort.get_sort_kind (Expr.get_sort(x))) == ROUNDING_MODE_SORT
	let mk_round_nearest_ties_to_even ( ctx : context ) = 
	  (expr_of_ptr ctx (Z3native.mk_fpa_round_nearest_ties_to_even (context_gno ctx)))
	let mk_rne ( ctx : context ) =
	  (expr_of_ptr ctx (Z3native.mk_fpa_rne (context_gno ctx)))
	let mk_round_nearest_ties_to_away ( ctx : context ) = 
	  (expr_of_ptr ctx (Z3native.mk_fpa_round_nearest_ties_to_away (context_gno ctx)))
	let mk_rna ( ctx : context ) =
	  (expr_of_ptr ctx (Z3native.mk_fpa_rna (context_gno ctx)))
	let mk_round_toward_positive ( ctx : context ) = 
	  (expr_of_ptr ctx (Z3native.mk_fpa_round_toward_positive (context_gno ctx)))
	let mk_rtp ( ctx : context ) =
	  (expr_of_ptr ctx (Z3native.mk_fpa_rtp (context_gno ctx)))
	let mk_round_toward_negative ( ctx : context ) = 
	  (expr_of_ptr ctx (Z3native.mk_fpa_round_toward_negative  (context_gno ctx)))
	let mk_rtn ( ctx : context ) =
	  (expr_of_ptr ctx (Z3native.mk_fpa_rtn (context_gno ctx)))
	let mk_round_toward_zero ( ctx : context ) = 
	  (expr_of_ptr ctx (Z3native.mk_fpa_round_toward_zero (context_gno ctx)))
	let mk_rtz ( ctx : context ) =
	  (expr_of_ptr ctx (Z3native.mk_fpa_rtz (context_gno ctx)))		
  end
	
  let mk_sort ( ctx : context ) ( ebits : int ) ( sbits : int ) =
	(Sort.sort_of_ptr ctx (Z3native.mk_fpa_sort (context_gno ctx) ebits sbits))
  let mk_sort_half ( ctx : context ) =
	(Sort.sort_of_ptr ctx (Z3native.mk_fpa_sort_half (context_gno ctx)))
  let mk_sort_16 ( ctx : context ) =
	(Sort.sort_of_ptr ctx (Z3native.mk_fpa_sort_16 (context_gno ctx)))
  let mk_sort_single ( ctx : context ) =
	(Sort.sort_of_ptr ctx (Z3native.mk_fpa_sort_single (context_gno ctx)))
  let mk_sort_32 ( ctx : context ) =
	(Sort.sort_of_ptr ctx (Z3native.mk_fpa_sort_32 (context_gno ctx)))
  let mk_sort_double ( ctx : context ) =
	(Sort.sort_of_ptr ctx (Z3native.mk_fpa_sort_double (context_gno ctx)))
  let mk_sort_64 ( ctx : context ) =
	(Sort.sort_of_ptr ctx (Z3native.mk_fpa_sort_64 (context_gno ctx)))
  let mk_sort_quadruple ( ctx : context ) =
	(Sort.sort_of_ptr ctx (Z3native.mk_fpa_sort_quadruple (context_gno ctx)))
  let mk_sort_128 ( ctx : context ) =
	(Sort.sort_of_ptr ctx (Z3native.mk_fpa_sort_128 (context_gno ctx)))

  let mk_nan ( ctx : context ) ( s : Sort.sort ) =
	(expr_of_ptr ctx (Z3native.mk_fpa_nan (context_gno ctx) (Sort.gno s)))
  let mk_inf ( ctx : context ) ( s : Sort.sort ) ( negative : bool ) =
	(expr_of_ptr ctx (Z3native.mk_fpa_inf (context_gno ctx) (Sort.gno s) negative))
  let mk_zero ( ctx : context ) ( s : Sort.sort ) ( negative : bool ) =
	(expr_of_ptr ctx (Z3native.mk_fpa_zero (context_gno ctx) (Sort.gno s) negative))

  let mk_fp ( ctx : context ) ( sign : expr ) ( exponent : expr ) ( significand : expr ) =
	(expr_of_ptr ctx (Z3native.mk_fpa_fp (context_gno ctx) (Expr.gno sign) (Expr.gno exponent) (Expr.gno significand)))
  let mk_numeral_f ( ctx : context ) ( value : float ) ( s : Sort.sort ) =
	(expr_of_ptr ctx (Z3native.mk_fpa_numeral_double (context_gno ctx) value (Sort.gno s)))
  let mk_numeral_i ( ctx : context ) ( value : int ) ( s : Sort.sort ) =
	(expr_of_ptr ctx (Z3native.mk_fpa_numeral_int (context_gno ctx) value (Sort.gno s)))
  let mk_numeral_i_u ( ctx : context ) ( sign : bool ) ( exponent : int ) ( significand : int ) ( s : Sort.sort ) =
	(expr_of_ptr ctx (Z3native.mk_fpa_numeral_int64_uint64 (context_gno ctx) sign exponent significand (Sort.gno s)))
  let mk_numeral_s ( ctx : context ) ( v : string ) ( s : Sort.sort ) =
    (expr_of_ptr ctx (Z3native.mk_numeral (context_gno ctx) v (Sort.gno s)))

  let is_fp ( x : expr ) = (Sort.get_sort_kind (Expr.get_sort x)) == FLOATING_POINT_SORT
  let is_abs ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_ABS)
  let is_neg ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_NEG)
  let is_add ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_ADD)
  let is_sub ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_SUB)
  let is_mul ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_MUL)
  let is_div ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_DIV)
  let is_fma ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_FMA)
  let is_sqrt ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_SQRT)
  let is_rem ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_REM)
  let is_round_to_integral ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_ROUND_TO_INTEGRAL)
  let is_min ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_MIN)
  let is_max ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_MAX)
  let is_leq ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_LE)
  let is_lt ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_LT)
  let is_geq ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_GE)
  let is_gt ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_GT)
  let is_eq ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_EQ)
  let is_is_normal ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_IS_NORMAL)
  let is_is_subnormal ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_IS_SUBNORMAL)
  let is_is_zero ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_IS_ZERO)
  let is_is_infinite ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_IS_INF)
  let is_is_nan ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_IS_NAN)
  let is_is_negative ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_IS_NEGATIVE)
  let is_is_positive ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_IS_POSITIVE)
  let is_to_fp ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_TO_FP)
  let is_to_fp_unsigned ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_TO_FP_UNSIGNED)
  let is_to_ubv ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_TO_UBV)
  let is_to_sbv ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_TO_SBV)
  let is_to_real ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_TO_REAL)
  let is_to_ieee_bv ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FPA_TO_IEEE_BV)
	
  let numeral_to_string ( x : expr ) = Z3native.get_numeral_string (Expr.gnc x) (Expr.gno x)
  let mk_const ( ctx : context ) ( name : Symbol.symbol ) ( s : Sort.sort ) =
    Expr.mk_const ctx name s
  let mk_const_s ( ctx : context ) ( name : string ) ( s : Sort.sort ) =
    mk_const ctx (Symbol.mk_string ctx name) s

  let mk_abs ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_abs (context_gno ctx) (Expr.gno t))
  let mk_neg ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_neg (context_gno ctx) (Expr.gno t))
  let mk_add ( ctx : context ) ( rm : expr ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_add (context_gno ctx) (Expr.gno rm) (Expr.gno t1) (Expr.gno t2))
  let mk_sub ( ctx : context ) ( rm : expr ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_sub (context_gno ctx) (Expr.gno rm) (Expr.gno t1) (Expr.gno t2))
  let mk_mul ( ctx : context ) ( rm : expr ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_mul (context_gno ctx) (Expr.gno rm) (Expr.gno t1) (Expr.gno t2))
  let mk_div ( ctx : context ) ( rm : expr ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_div (context_gno ctx) (Expr.gno rm) (Expr.gno t1) (Expr.gno t2))
  let mk_fma ( ctx : context ) ( rm : expr ) ( t1 : expr ) ( t2 : expr ) ( t3 : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_fma (context_gno ctx) (Expr.gno rm) (Expr.gno t1) (Expr.gno t2) (Expr.gno t3))
  let mk_sqrt ( ctx : context ) ( rm : expr ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_sqrt (context_gno ctx) (Expr.gno rm) (Expr.gno t))
  let mk_rem ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_rem (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_round_to_integral  ( ctx : context ) ( rm : expr ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_round_to_integral (context_gno ctx) (Expr.gno rm) (Expr.gno t))
  let mk_min ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_min (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_max ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_max (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_leq ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_leq (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_lt ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_lt (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_geq ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_geq (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_gt ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_gt (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_eq ( ctx : context ) ( t1 : expr ) ( t2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_eq (context_gno ctx) (Expr.gno t1) (Expr.gno t2))
  let mk_is_normal ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_is_normal (context_gno ctx) (Expr.gno t))
  let mk_is_subnormal ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_is_subnormal (context_gno ctx) (Expr.gno t))
  let mk_is_zero ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_is_zero (context_gno ctx) (Expr.gno t))
  let mk_is_infinite  ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_is_infinite (context_gno ctx) (Expr.gno t))
  let mk_is_nan ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_is_nan (context_gno ctx) (Expr.gno t))
  let mk_is_negative  ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_is_negative (context_gno ctx) (Expr.gno t))
  let mk_is_positive ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_is_positive (context_gno ctx) (Expr.gno t))
  let mk_to_fp_bv ( ctx : context ) ( t : expr ) ( s : Sort.sort ) =
    expr_of_ptr ctx (Z3native.mk_fpa_to_fp_bv (context_gno ctx) (Expr.gno t) (Sort.gno s))
  let mk_to_fp_float ( ctx : context ) ( rm : expr) ( t : expr ) ( s : Sort.sort ) =
    expr_of_ptr ctx (Z3native.mk_fpa_to_fp_float (context_gno ctx) (Expr.gno rm) (Expr.gno t) (Sort.gno s))
  let mk_to_fp_real ( ctx : context ) ( rm : expr ) ( t : expr ) ( s : Sort.sort ) =
    expr_of_ptr ctx (Z3native.mk_fpa_to_fp_real (context_gno ctx) (Expr.gno rm) (Expr.gno t) (Sort.gno s))
  let mk_to_fp_signed  ( ctx : context ) ( rm : expr) ( t : expr ) ( s : Sort.sort ) =
    expr_of_ptr ctx (Z3native.mk_fpa_to_fp_signed (context_gno ctx) (Expr.gno rm) (Expr.gno t) (Sort.gno s))
  let mk_to_fp_unsigned  ( ctx : context ) ( rm : expr) ( t : expr ) ( s : Sort.sort ) =
    expr_of_ptr ctx (Z3native.mk_fpa_to_fp_unsigned (context_gno ctx) (Expr.gno rm) (Expr.gno t) (Sort.gno s))
  let mk_to_ubv ( ctx : context ) ( rm : expr) ( t : expr ) ( size : int ) =
    expr_of_ptr ctx (Z3native.mk_fpa_to_ubv (context_gno ctx) (Expr.gno rm) (Expr.gno t) size)
  let mk_to_sbv ( ctx : context ) ( rm : expr) ( t : expr ) ( size : int ) =
    expr_of_ptr ctx (Z3native.mk_fpa_to_sbv (context_gno ctx) (Expr.gno rm) (Expr.gno t) size)
  let mk_to_real ( ctx : context ) ( t : expr ) =
    expr_of_ptr ctx (Z3native.mk_fpa_to_real (context_gno ctx) (Expr.gno t))

  let get_ebits ( ctx : context ) ( s : Sort.sort ) =
	(Z3native.fpa_get_ebits (context_gno ctx) (Sort.gno s))
  let get_sbits ( ctx : context ) ( s : Sort.sort ) =
	(Z3native.fpa_get_sbits (context_gno ctx) (Sort.gno s))
  let get_numeral_sign ( ctx : context ) ( t : expr ) =
	(Z3native.fpa_get_numeral_sign (context_gno ctx) (Expr.gno t))
  let get_numeral_significand_string ( ctx : context ) ( t : expr ) =
	(Z3native.fpa_get_numeral_significand_string (context_gno ctx) (Expr.gno t))
  let get_numeral_significand_uint ( ctx : context ) ( t : expr ) =
	(Z3native.fpa_get_numeral_significand_uint64 (context_gno ctx) (Expr.gno t))
  let get_numeral_exponent_string ( ctx : context ) ( t : expr ) =
	(Z3native.fpa_get_numeral_exponent_string (context_gno ctx) (Expr.gno t))
  let get_numeral_exponent_int ( ctx : context ) ( t : expr ) =
	(Z3native.fpa_get_numeral_exponent_int64 (context_gno ctx) (Expr.gno t))

  let mk_to_ieee_bv ( ctx : context ) ( t : expr ) =
	(expr_of_ptr ctx (Z3native.mk_fpa_to_ieee_bv (context_gno ctx) (Expr.gno t)))
  let mk_to_fp_int_real ( ctx : context ) ( rm : expr ) ( exponent : expr ) ( significand : expr ) ( s : Sort.sort ) =
	(expr_of_ptr ctx (Z3native.mk_fpa_to_fp_int_real (context_gno ctx) (Expr.gno rm) (Expr.gno exponent) (Expr.gno significand) (Sort.gno s)))

  let numeral_to_string ( x : expr ) = Z3native.get_numeral_string (Expr.gnc x) (Expr.gno x)
end


module Proof = 
struct
  let is_true ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_TRUE)
  let is_asserted ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_ASSERTED)
  let is_goal ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_GOAL)
  let is_oeq ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_OEQ)
  let is_modus_ponens ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_MODUS_PONENS)
  let is_reflexivity ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_REFLEXIVITY)
  let is_symmetry ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_SYMMETRY)
  let is_transitivity ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_TRANSITIVITY)
  let is_Transitivity_star ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_TRANSITIVITY_STAR)
  let is_monotonicity ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_MONOTONICITY)
  let is_quant_intro ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_QUANT_INTRO)
  let is_distributivity ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_DISTRIBUTIVITY)
  let is_and_elimination ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_AND_ELIM)
  let is_or_elimination ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_NOT_OR_ELIM)
  let is_rewrite ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_REWRITE)
  let is_rewrite_star ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_REWRITE_STAR)
  let is_pull_quant ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_PULL_QUANT)
  let is_pull_quant_star ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_PULL_QUANT_STAR)
  let is_push_quant ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_PUSH_QUANT)
  let is_elim_unused_vars ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_ELIM_UNUSED_VARS)
  let is_der ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_DER)
  let is_quant_inst ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_QUANT_INST)
  let is_hypothesis ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_HYPOTHESIS)
  let is_lemma ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_LEMMA)
  let is_unit_resolution ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_UNIT_RESOLUTION)
  let is_iff_true ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_IFF_TRUE)
  let is_iff_false ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_IFF_FALSE)
  let is_commutativity ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_COMMUTATIVITY) (*  *)
  let is_def_axiom ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_DEF_AXIOM)
  let is_def_intro ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_DEF_INTRO)
  let is_apply_def ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_APPLY_DEF)
  let is_iff_oeq ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_IFF_OEQ)
  let is_nnf_pos ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_NNF_POS)
  let is_nnf_neg ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_NNF_NEG)
  let is_nnf_star ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_NNF_STAR)
  let is_cnf_star ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_CNF_STAR)
  let is_skolemize ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_SKOLEMIZE)
  let is_modus_ponens_oeq ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_MODUS_PONENS_OEQ)
  let is_theory_lemma ( x : expr ) = (AST.is_app (Expr.ast_of_expr x)) && (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_TH_LEMMA)
end


module Goal =
struct      
  type goal = z3_native_object

  let create ( ctx : context ) ( no : Z3native.ptr ) = 
    let res : goal = { m_ctx = ctx ;
		       m_n_obj = null ;
		       inc_ref = Z3native.goal_inc_ref ;
		       dec_ref = Z3native.goal_dec_ref } in
    (z3obj_sno res ctx no) ;
    (z3obj_create res) ;
    res
      
  let get_precision ( x : goal ) =
    goal_prec_of_int (Z3native.goal_precision (z3obj_gnc x) (z3obj_gno x))
      
  let is_precise ( x : goal ) =
    (get_precision x) == GOAL_PRECISE
      
  let is_underapproximation ( x : goal ) =
    (get_precision x) == GOAL_UNDER

  let is_overapproximation ( x : goal ) =
    (get_precision x) == GOAL_OVER
      
  let is_garbage ( x : goal ) = 
    (get_precision x) == GOAL_UNDER_OVER
      
  let add ( x : goal ) ( constraints : expr list ) =
    let f e = Z3native.goal_assert (z3obj_gnc x) (z3obj_gno x) (Expr.gno e) in
    ignore (List.map f constraints) ;
    ()
      
  let is_inconsistent ( x : goal ) =
    Z3native.goal_inconsistent (z3obj_gnc x) (z3obj_gno x)

  let get_depth ( x : goal ) = Z3native.goal_depth (z3obj_gnc x) (z3obj_gno x)
    
  let reset ( x : goal ) =  Z3native.goal_reset (z3obj_gnc x) (z3obj_gno x)
    
  let get_size ( x : goal ) = Z3native.goal_size (z3obj_gnc x) (z3obj_gno x)

  let get_formulas ( x : goal ) =
    let n = get_size x in 
    let f i = ((expr_of_ptr (z3obj_gc x) 
		  (Z3native.goal_formula (z3obj_gnc x) (z3obj_gno x) i))) in
    mk_list f n

  let get_num_exprs ( x : goal ) =  Z3native.goal_num_exprs (z3obj_gnc x) (z3obj_gno x)
    
  let is_decided_sat ( x : goal ) = 
    Z3native.goal_is_decided_sat (z3obj_gnc x) (z3obj_gno x)
      
  let is_decided_unsat ( x : goal ) =
    Z3native.goal_is_decided_unsat (z3obj_gnc x) (z3obj_gno x)
      
  let translate ( x : goal ) ( to_ctx : context ) =
    create to_ctx (Z3native.goal_translate (z3obj_gnc x) (z3obj_gno x) (context_gno to_ctx))

  let simplify ( x : goal ) ( p : Params.params option ) =
    let tn = Z3native.mk_tactic (z3obj_gnc x) "simplify" in
    Z3native.tactic_inc_ref (z3obj_gnc x) tn ;
    let arn = match p with
      | None -> Z3native.tactic_apply (z3obj_gnc x) tn (z3obj_gno x) 
      | Some(pn) -> Z3native.tactic_apply_ex (z3obj_gnc x) tn (z3obj_gno x) (z3obj_gno pn)
    in
    Z3native.apply_result_inc_ref (z3obj_gnc x) arn ;
    let sg = Z3native.apply_result_get_num_subgoals (z3obj_gnc x) arn in
    let res = if sg == 0 then 
	raise (Z3native.Exception "No subgoals") 
      else 
	Z3native.apply_result_get_subgoal (z3obj_gnc x) arn 0 in
    Z3native.apply_result_dec_ref (z3obj_gnc x) arn ;
    Z3native.tactic_dec_ref (z3obj_gnc x) tn ;
    create (z3obj_gc x) res

  let mk_goal ( ctx : context ) ( models : bool ) ( unsat_cores : bool ) ( proofs : bool ) = 
    create ctx (Z3native.mk_goal (context_gno ctx) models unsat_cores proofs)

  let to_string ( x : goal ) = Z3native.goal_to_string (z3obj_gnc x) (z3obj_gno x)

  let as_expr ( x : goal ) = 
	let n = get_size x in
	if n = 0 then 
	  (Boolean.mk_true (z3obj_gc x)) 
	else if n = 1 then
	  (List.hd (get_formulas x))
	else
	  (Boolean.mk_and (z3obj_gc x) (get_formulas x))
end  


module Model =
struct
  type model = z3_native_object

  let create ( ctx : context ) ( no : Z3native.ptr ) = 
    let res : model = { m_ctx = ctx ;
			m_n_obj = null ;
			inc_ref = Z3native.model_inc_ref ;
			dec_ref = Z3native.model_dec_ref } in
    (z3obj_sno res ctx no) ;
    (z3obj_create res) ;
    res
      
  module FuncInterp =
  struct
    type func_interp = z3_native_object

    let create ( ctx : context ) ( no : Z3native.ptr ) = 
      let res : func_interp = { m_ctx = ctx ;
				m_n_obj = null ;
				inc_ref = Z3native.func_interp_inc_ref ;
				dec_ref = Z3native.func_interp_dec_ref } in
      (z3obj_sno res ctx no) ;
      (z3obj_create res) ;
      res
	
    module FuncEntry =
    struct	  
      type func_entry = z3_native_object
	  
      let create ( ctx : context ) ( no : Z3native.ptr ) = 
	let res : func_entry = { m_ctx = ctx ;
				 m_n_obj = null ;
				 inc_ref = Z3native.func_entry_inc_ref ;
				 dec_ref = Z3native.func_entry_dec_ref } in
	(z3obj_sno res ctx no) ;
	(z3obj_create res) ;
	res
	  
      let get_value ( x : func_entry ) =
	expr_of_ptr (z3obj_gc x) (Z3native.func_entry_get_value (z3obj_gnc x) (z3obj_gno x))

      let get_num_args ( x : func_entry ) = Z3native.func_entry_get_num_args (z3obj_gnc x) (z3obj_gno x)
	
      let get_args ( x : func_entry ) =
	let n = (get_num_args x) in
	let f i = (expr_of_ptr (z3obj_gc x) (Z3native.func_entry_get_arg (z3obj_gnc x) (z3obj_gno x) i)) in
	mk_list f n
	  
      let to_string ( x : func_entry ) =
	let a = (get_args x) in
	let f c p = (p ^ (Expr.to_string c) ^ ", ") in
	"[" ^ List.fold_right f a ((Expr.to_string (get_value x)) ^ "]")
    end

    let get_num_entries ( x: func_interp ) = Z3native.func_interp_get_num_entries (z3obj_gnc x) (z3obj_gno x)

    let get_entries ( x : func_interp ) =
      let n = (get_num_entries x) in
      let f i = (FuncEntry.create (z3obj_gc x) (Z3native.func_interp_get_entry (z3obj_gnc x) (z3obj_gno x) i)) in
      mk_list f n

    let get_else ( x : func_interp ) = expr_of_ptr (z3obj_gc x) (Z3native.func_interp_get_else (z3obj_gnc x) (z3obj_gno x))

    let get_arity ( x : func_interp ) = Z3native.func_interp_get_arity (z3obj_gnc x) (z3obj_gno x)

    let to_string ( x : func_interp ) =     
      let f c p = (
	let n = (FuncEntry.get_num_args c) in
	p ^ 
	  let g c p = (p ^ (Expr.to_string c) ^ ", ") in
	  (if n > 1 then "[" else "") ^
	    (List.fold_right 
	       g 
	       (FuncEntry.get_args c) 
	       ((if n > 1 then "]" else "") ^ " -> " ^ (Expr.to_string (FuncEntry.get_value c)) ^ ", "))
      ) in
      List.fold_right f (get_entries x) ("else -> " ^ (Expr.to_string (get_else x)) ^ "]")
  end
    
  let get_const_interp ( x : model ) ( f : func_decl ) =
    if (FuncDecl.get_arity f) != 0 ||
      (sort_kind_of_int (Z3native.get_sort_kind (FuncDecl.gnc f) (Z3native.get_range (FuncDecl.gnc f) (FuncDecl.gno f)))) == ARRAY_SORT then
      raise (Z3native.Exception "Non-zero arity functions and arrays have FunctionInterpretations as a model. Use FuncInterp.")
    else
      let np = Z3native.model_get_const_interp (z3obj_gnc x) (z3obj_gno x) (FuncDecl.gno f) in
      if (Z3native.is_null np) then
	None
      else
	Some (expr_of_ptr (z3obj_gc x) np)

  let get_const_interp_e ( x : model ) ( a : expr ) = get_const_interp x (Expr.get_func_decl a)


  let rec get_func_interp ( x : model ) ( f : func_decl ) =
    let sk = (sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc x) (Z3native.get_range (FuncDecl.gnc f) (FuncDecl.gno f)))) in
    if (FuncDecl.get_arity f) == 0 then
      let n = Z3native.model_get_const_interp (z3obj_gnc x) (z3obj_gno x) (FuncDecl.gno f) in      
      if (Z3native.is_null n) then
	None 
      else 
	match sk with
	  | ARRAY_SORT ->	    
	    if not (Z3native.is_as_array (z3obj_gnc x) n) then
	      raise (Z3native.Exception "Argument was not an array constant")
	    else
	      let fd = Z3native.get_as_array_func_decl (z3obj_gnc x) n in
              get_func_interp x (func_decl_of_ptr (z3obj_gc x) fd)
	  | _ -> raise (Z3native.Exception "Constant functions do not have a function interpretation; use ConstInterp");
    else
      let n = (Z3native.model_get_func_interp (z3obj_gnc x) (z3obj_gno x) (FuncDecl.gno f)) in
      if (Z3native.is_null n) then None else Some (FuncInterp.create (z3obj_gc x) n)
	
  (** The number of constants that have an interpretation in the model. *)
  let get_num_consts ( x : model ) = Z3native.model_get_num_consts (z3obj_gnc x) (z3obj_gno x)
    
  let get_const_decls ( x : model ) = 
    let n = (get_num_consts x) in
    let f i = func_decl_of_ptr (z3obj_gc x) (Z3native.model_get_const_decl (z3obj_gnc x) (z3obj_gno x) i) in
    mk_list f n
      
  let get_num_funcs ( x : model ) = Z3native.model_get_num_funcs (z3obj_gnc x) (z3obj_gno x)
    
  let get_func_decls ( x : model ) = 
    let n = (get_num_funcs x) in
    let f i = func_decl_of_ptr (z3obj_gc x) (Z3native.model_get_func_decl (z3obj_gnc x) (z3obj_gno x) i) in
    mk_list f n
      
  let get_decls ( x : model ) =
    let n_funcs = (get_num_funcs x) in
    let n_consts = (get_num_consts x ) in
    let f i = func_decl_of_ptr (z3obj_gc x) (Z3native.model_get_func_decl (z3obj_gnc x) (z3obj_gno x) i) in
    let g i = func_decl_of_ptr (z3obj_gc x) (Z3native.model_get_const_decl (z3obj_gnc x) (z3obj_gno x) i) in
    (mk_list f n_funcs) @ (mk_list g n_consts)
      
  let eval ( x : model ) ( t : expr ) ( completion : bool ) =
    let (r, v) = (Z3native.model_eval (z3obj_gnc x) (z3obj_gno x) (Expr.gno t) completion) in
    if not r then
      None
    else
      Some(expr_of_ptr (z3obj_gc x) v)

  let evaluate ( x : model ) ( t : expr ) ( completion : bool ) =
    eval x t completion
      
  let get_num_sorts ( x : model ) = Z3native.model_get_num_sorts (z3obj_gnc x) (z3obj_gno x)
    
  let get_sorts ( x : model ) =
    let n = (get_num_sorts x) in
    let f i = (Sort.sort_of_ptr (z3obj_gc x) (Z3native.model_get_sort (z3obj_gnc x) (z3obj_gno x) i)) in
    mk_list f n

  let sort_universe ( x : model ) ( s : Sort.sort ) =
    let av = AST.ASTVector.create (z3obj_gc x) (Z3native.model_get_sort_universe (z3obj_gnc x) (z3obj_gno x) (Sort.gno s)) in
    (AST.ASTVector.to_expr_list av)

  let to_string ( x : model ) = Z3native.model_to_string (z3obj_gnc x) (z3obj_gno x) 
end


module Probe =
struct
  type probe = z3_native_object     

  let create ( ctx : context ) ( no : Z3native.ptr ) = 
    let res : probe = { m_ctx = ctx ;
			m_n_obj = null ;
			inc_ref = Z3native.probe_inc_ref ;
			dec_ref = Z3native.probe_dec_ref } in
    (z3obj_sno res ctx no) ;
    (z3obj_create res) ;
    res
      

  let apply ( x : probe ) ( g : Goal.goal ) =
    Z3native.probe_apply (z3obj_gnc x) (z3obj_gno x) (z3obj_gno g)

  let get_num_probes ( ctx : context ) =
    Z3native.get_num_probes (context_gno ctx)

  let get_probe_names ( ctx : context ) = 
    let n = (get_num_probes ctx) in
    let f i = (Z3native.get_probe_name (context_gno ctx) i) in
    mk_list f n

  let get_probe_description ( ctx : context ) ( name : string ) =
    Z3native.probe_get_descr (context_gno ctx) name

  let mk_probe ( ctx : context ) ( name : string ) =
    (create ctx (Z3native.mk_probe (context_gno ctx) name))

  let const ( ctx : context ) ( v : float ) = 
    (create ctx (Z3native.probe_const (context_gno ctx) v))

  let lt ( ctx : context ) ( p1 : probe ) ( p2 : probe ) =
    (create ctx (Z3native.probe_lt (context_gno ctx) (z3obj_gno p1) (z3obj_gno p2)))

  let gt ( ctx : context ) ( p1 : probe ) ( p2 : probe ) =
    (create ctx (Z3native.probe_gt (context_gno ctx) (z3obj_gno p1) (z3obj_gno p2)))

  let le ( ctx : context ) ( p1 : probe ) ( p2 : probe ) = 
    (create ctx (Z3native.probe_le (context_gno ctx) (z3obj_gno p1) (z3obj_gno p2)))

  let ge ( ctx : context ) ( p1 : probe ) ( p2 : probe ) =
    (create ctx (Z3native.probe_ge (context_gno ctx) (z3obj_gno p1) (z3obj_gno p2)))

  let eq ( ctx : context ) ( p1 : probe ) ( p2 : probe ) =
    (create ctx (Z3native.probe_eq (context_gno ctx) (z3obj_gno p1) (z3obj_gno p2)))

  let and_ ( ctx : context ) ( p1 : probe ) ( p2 : probe ) =
    (create ctx (Z3native.probe_and (context_gno ctx) (z3obj_gno p1) (z3obj_gno p2)))

  let or_ ( ctx : context ) ( p1 : probe ) ( p2 : probe ) =
    (create ctx (Z3native.probe_or (context_gno ctx) (z3obj_gno p1) (z3obj_gno p2)))

  let not_ ( ctx : context ) ( p : probe ) =
    (create ctx (Z3native.probe_not (context_gno ctx) (z3obj_gno p)))
end


module Tactic =
struct      
  type tactic = z3_native_object

  let create ( ctx : context ) ( no : Z3native.ptr ) = 
    let res : tactic = { m_ctx = ctx ;
			 m_n_obj = null ;
			 inc_ref = Z3native.tactic_inc_ref ;
			 dec_ref = Z3native.tactic_dec_ref } in
    (z3obj_sno res ctx no) ;
    (z3obj_create res) ;
    res
      
  module ApplyResult =
  struct 
    type apply_result = z3_native_object
	
    let create ( ctx : context ) ( no : Z3native.ptr ) = 
      let res : apply_result = { m_ctx = ctx ;
				 m_n_obj = null ;
				 inc_ref = Z3native.apply_result_inc_ref ;
				 dec_ref = Z3native.apply_result_dec_ref } in
      (z3obj_sno res ctx no) ;
      (z3obj_create res) ;
      res
	
    let get_num_subgoals ( x : apply_result ) =
      Z3native.apply_result_get_num_subgoals (z3obj_gnc x) (z3obj_gno x)
	
    let get_subgoals ( x : apply_result ) =
      let n = (get_num_subgoals x) in
      let f i = Goal.create (z3obj_gc x) (Z3native.apply_result_get_subgoal (z3obj_gnc x) (z3obj_gno x) i) in
      mk_list f n
	
    let get_subgoal ( x : apply_result ) ( i : int ) =
      Goal.create (z3obj_gc x) (Z3native.apply_result_get_subgoal (z3obj_gnc x) (z3obj_gno x) i)
	
    let convert_model ( x : apply_result ) ( i : int ) ( m : Model.model ) =
      Model.create (z3obj_gc x) (Z3native.apply_result_convert_model (z3obj_gnc x) (z3obj_gno x) i (z3obj_gno m))
	
    let to_string ( x : apply_result ) = Z3native.apply_result_to_string (z3obj_gnc x) (z3obj_gno x)
  end

  let get_help ( x : tactic ) = Z3native.tactic_get_help (z3obj_gnc x) (z3obj_gno x)

  let get_param_descrs ( x : tactic ) =
    Params.ParamDescrs.param_descrs_of_ptr (z3obj_gc x) (Z3native.tactic_get_param_descrs (z3obj_gnc x) (z3obj_gno x))
      
  let apply ( x : tactic ) ( g : Goal.goal ) ( p : Params.params option ) =
    match p with 
      | None -> (ApplyResult.create (z3obj_gc x) (Z3native.tactic_apply (z3obj_gnc x) (z3obj_gno x) (z3obj_gno g)))
      | Some (pn) -> (ApplyResult.create (z3obj_gc x) (Z3native.tactic_apply_ex (z3obj_gnc x) (z3obj_gno x) (z3obj_gno g) (z3obj_gno pn)))

  let get_num_tactics ( ctx : context ) = Z3native.get_num_tactics (context_gno ctx)

  let get_tactic_names ( ctx : context ) =
    let n = (get_num_tactics ctx ) in
    let f i = (Z3native.get_tactic_name (context_gno ctx) i) in
    mk_list f n

  let get_tactic_description ( ctx : context ) ( name : string ) =
    Z3native.tactic_get_descr (context_gno ctx) name

  let mk_tactic ( ctx : context ) ( name : string ) =
    create ctx (Z3native.mk_tactic (context_gno ctx) name)

  let and_then ( ctx : context ) ( t1 : tactic ) ( t2 : tactic ) ( ts : tactic list ) =
    let f p c = (match p with 
      | None -> (Some (z3obj_gno c)) 
      | Some(x) -> (Some (Z3native.tactic_and_then (context_gno ctx) (z3obj_gno c) x))) in
    match (List.fold_left f None ts) with
      | None -> 
	create ctx (Z3native.tactic_and_then (context_gno ctx) (z3obj_gno t1) (z3obj_gno t2))
      | Some(x) ->
	let o = (Z3native.tactic_and_then (context_gno ctx) (z3obj_gno t2) x) in
	create ctx (Z3native.tactic_and_then (context_gno ctx) (z3obj_gno t1) o)

  let or_else ( ctx : context ) ( t1 : tactic ) ( t2 : tactic ) =
    create ctx (Z3native.tactic_or_else (context_gno ctx) (z3obj_gno t1) (z3obj_gno t2))

  let try_for ( ctx : context ) ( t : tactic ) ( ms : int ) =
    create ctx (Z3native.tactic_try_for (context_gno ctx) (z3obj_gno t) ms)

  let when_ ( ctx : context ) ( p : Probe.probe ) ( t : tactic ) =
    create ctx (Z3native.tactic_when (context_gno ctx) (z3obj_gno p) (z3obj_gno t))

  let cond ( ctx : context ) ( p : Probe.probe ) ( t1 : tactic ) ( t2 : tactic ) =
    create ctx (Z3native.tactic_cond (context_gno ctx) (z3obj_gno p) (z3obj_gno t1) (z3obj_gno t2))

  let repeat ( ctx : context ) ( t : tactic ) ( max : int ) =
    create ctx (Z3native.tactic_repeat (context_gno ctx) (z3obj_gno t) max)

  let skip ( ctx : context ) =
    create ctx (Z3native.tactic_skip (context_gno ctx))

  let fail ( ctx : context ) =
    create ctx (Z3native.tactic_fail (context_gno ctx))

  let fail_if ( ctx : context ) ( p : Probe.probe ) =
    create ctx (Z3native.tactic_fail_if (context_gno ctx) (z3obj_gno p))

  let fail_if_not_decided ( ctx : context ) =
    create ctx (Z3native.tactic_fail_if_not_decided (context_gno ctx))

  let using_params ( ctx : context ) ( t : tactic ) ( p : Params.params ) =
    create ctx (Z3native.tactic_using_params (context_gno ctx) (z3obj_gno t) (z3obj_gno p))

  let with_ ( ctx : context ) ( t : tactic ) ( p : Params.params ) =
    using_params ctx t p

  let par_or ( ctx : context ) ( t : tactic list ) =
    let f e = (z3obj_gno e) in
    create ctx (Z3native.tactic_par_or (context_gno ctx) (List.length t) (Array.of_list (List.map f t)))

  let par_and_then ( ctx : context ) ( t1 : tactic ) ( t2 : tactic ) =
    create ctx (Z3native.tactic_par_and_then (context_gno ctx) (z3obj_gno t1) (z3obj_gno t2))

  let interrupt ( ctx : context ) =
    Z3native.interrupt (context_gno ctx)
end


module Statistics =
struct	
  type statistics = z3_native_object

  let create ( ctx : context ) ( no : Z3native.ptr ) = 
    let res : statistics = { m_ctx = ctx ;
			                 m_n_obj = null ;
			                 inc_ref = Z3native.stats_inc_ref ;
			                 dec_ref = Z3native.stats_dec_ref } in
    (z3obj_sno res ctx no) ;
    (z3obj_create res) ;
    res
      

  module Entry =
  struct
    type statistics_entry = { 
	  mutable m_key : string; 
	  mutable m_is_int : bool ; 
	  mutable m_is_float : bool ; 
	  mutable m_int : int ; 
	  mutable m_float : float }
	    
    let create_si k v = 
	  let res : statistics_entry = { 
	    m_key = k ;
	    m_is_int = true ;
	    m_is_float = false ;
	    m_int = v ;
	    m_float = 0.0
	  } in
	  res

    let create_sd k v = 
	  let res : statistics_entry = { 
	    m_key = k ;
	    m_is_int = false ;
	    m_is_float = true ;
	    m_int = 0 ;
	    m_float = v
	  } in
	  res
	    

    let get_key (x : statistics_entry) = x.m_key
    let get_int (x : statistics_entry) = x.m_int	
    let get_float (x : statistics_entry) = x.m_float
    let is_int (x : statistics_entry) = x.m_is_int
    let is_float (x : statistics_entry) = x.m_is_float
    let to_string_value (x : statistics_entry) = 
	  if (is_int x) then
	    string_of_int (get_int x)
	  else if (is_float x) then 
	    string_of_float (get_float x)
	  else
        raise (Z3native.Exception "Unknown statistical entry type")
    let to_string ( x : statistics_entry ) = (get_key x) ^ ": " ^ (to_string_value x)
  end

  let to_string ( x : statistics ) = Z3native.stats_to_string (z3obj_gnc x) (z3obj_gno x)
    
  let get_size ( x : statistics ) = Z3native.stats_size (z3obj_gnc x) (z3obj_gno x)
    
  let get_entries ( x : statistics ) =
    let n = (get_size x ) in
    let f i = (
	  let k = Z3native.stats_get_key (z3obj_gnc x) (z3obj_gno x) i in
	  if (Z3native.stats_is_uint (z3obj_gnc x) (z3obj_gno x) i) then
	    (Entry.create_si k (Z3native.stats_get_uint_value (z3obj_gnc x) (z3obj_gno x) i))
	  else 
	    (Entry.create_sd k (Z3native.stats_get_double_value (z3obj_gnc x) (z3obj_gno x) i))
    ) in
    mk_list f n

  let get_keys ( x : statistics ) =
    let n = (get_size x) in
    let f i = (Z3native.stats_get_key (z3obj_gnc x) (z3obj_gno x) i) in
    mk_list f n
	  
  let get ( x : statistics ) ( key : string ) =
    let f p c = (if ((Entry.get_key c) == key) then (Some c) else p) in
    List.fold_left f None (get_entries x)
end


module Solver =
struct      
  type solver = z3_native_object
  type status = UNSATISFIABLE | UNKNOWN | SATISFIABLE

  let create ( ctx : context ) ( no : Z3native.ptr ) = 
    let res : solver = { m_ctx = ctx ;
			 m_n_obj = null ;
			 inc_ref = Z3native.solver_inc_ref ;
			 dec_ref = Z3native.solver_dec_ref } in
    (z3obj_sno res ctx no) ;
    (z3obj_create res) ;
    res
      
  let string_of_status ( s : status) = match s with
    | UNSATISFIABLE -> "unsatisfiable"
    | SATISFIABLE -> "satisfiable" 
    | _ -> "unknown"

  let get_help ( x : solver ) = Z3native.solver_get_help (z3obj_gnc x) (z3obj_gno x)

  let set_parameters ( x : solver ) ( p : Params.params )=
    Z3native.solver_set_params (z3obj_gnc x) (z3obj_gno x) (z3obj_gno p)

  let get_param_descrs ( x : solver ) =
    Params.ParamDescrs.param_descrs_of_ptr (z3obj_gc x) (Z3native.solver_get_param_descrs (z3obj_gnc x) (z3obj_gno x))

  let get_num_scopes ( x : solver ) = Z3native.solver_get_num_scopes (z3obj_gnc x) (z3obj_gno x)

  let push ( x : solver ) = Z3native.solver_push (z3obj_gnc x) (z3obj_gno x)

  let pop ( x : solver ) ( n : int ) = Z3native.solver_pop (z3obj_gnc x) (z3obj_gno x) n

  let reset ( x : solver ) = Z3native.solver_reset (z3obj_gnc x) (z3obj_gno x)

  let add ( x : solver ) ( constraints : expr list ) =
    let f e = (Z3native.solver_assert (z3obj_gnc x) (z3obj_gno x) (Expr.gno e)) in
    ignore (List.map f constraints)

  let assert_and_track_l ( x : solver ) ( cs : expr list ) ( ps : expr list ) =
    if ((List.length cs) != (List.length ps)) then
      raise (Z3native.Exception "Argument size mismatch")
    else
      let f a b = (Z3native.solver_assert_and_track (z3obj_gnc x) (z3obj_gno x) (Expr.gno a) (Expr.gno b)) in
      ignore (List.iter2 f cs ps)
	
  let assert_and_track ( x : solver ) ( c : expr ) ( p : expr ) =    
    Z3native.solver_assert_and_track (z3obj_gnc x) (z3obj_gno x) (Expr.gno c) (Expr.gno p)

  let get_num_assertions ( x : solver ) =
    let a = AST.ASTVector.create (z3obj_gc x) (Z3native.solver_get_assertions (z3obj_gnc x) (z3obj_gno x)) in
    (AST.ASTVector.get_size a)

  let get_assertions ( x : solver ) =
    let av = AST.ASTVector.create (z3obj_gc x) (Z3native.solver_get_assertions (z3obj_gnc x) (z3obj_gno x)) in
    (AST.ASTVector.to_expr_list av)

  let check ( x : solver ) ( assumptions : expr list ) =
    let r = 
      if ((List.length assumptions) == 0) then
	lbool_of_int (Z3native.solver_check (z3obj_gnc x) (z3obj_gno x))
      else
	let f x = (Expr.gno x) in
	lbool_of_int (Z3native.solver_check_assumptions (z3obj_gnc x) (z3obj_gno x) (List.length assumptions) (Array.of_list (List.map f assumptions)))
    in
    match r with 
      | L_TRUE -> SATISFIABLE
      | L_FALSE -> UNSATISFIABLE
      | _ -> UNKNOWN
	
  let get_model ( x : solver ) =
    let q = Z3native.solver_get_model (z3obj_gnc x) (z3obj_gno x) in
    if (Z3native.is_null q) then
      None
    else 
      Some (Model.create (z3obj_gc x) q)
	
  let get_proof ( x : solver ) =
    let q = Z3native.solver_get_proof (z3obj_gnc x) (z3obj_gno x) in
    if (Z3native.is_null q) then
      None
    else
      Some (expr_of_ptr (z3obj_gc x) q)
	
  let get_unsat_core ( x : solver ) =
    let av = AST.ASTVector.create (z3obj_gc x) (Z3native.solver_get_unsat_core (z3obj_gnc x) (z3obj_gno x)) in 
    (AST.ASTVector.to_expr_list av)

  let get_reason_unknown ( x : solver ) =  Z3native.solver_get_reason_unknown (z3obj_gnc x) (z3obj_gno x)

  let get_statistics ( x : solver ) =
    (Statistics.create (z3obj_gc x) (Z3native.solver_get_statistics (z3obj_gnc x) (z3obj_gno x)))

  let mk_solver ( ctx : context ) ( logic : Symbol.symbol option ) =
    match logic with
      | None -> (create ctx (Z3native.mk_solver (context_gno ctx)))
      | Some (x) -> (create ctx (Z3native.mk_solver_for_logic (context_gno ctx) (Symbol.gno x)))

  let mk_solver_s ( ctx : context ) ( logic : string ) =
    mk_solver ctx (Some (Symbol.mk_string ctx logic))

  let mk_simple_solver ( ctx : context ) =
    (create ctx (Z3native.mk_simple_solver (context_gno ctx)))

  let mk_solver_t ( ctx : context ) ( t : Tactic.tactic ) = 
    (create ctx (Z3native.mk_solver_from_tactic (context_gno ctx) (z3obj_gno t)))

  let to_string ( x : solver ) = Z3native.solver_to_string (z3obj_gnc x) (z3obj_gno x)
end


module Fixedpoint =
struct
  type fixedpoint = z3_native_object
      
  let create ( ctx : context ) = 
    let res : fixedpoint = { m_ctx = ctx ;
			     m_n_obj = null ;
			     inc_ref = Z3native.fixedpoint_inc_ref ;
			     dec_ref = Z3native.fixedpoint_dec_ref } in
    (z3obj_sno res ctx (Z3native.mk_fixedpoint (context_gno ctx))) ;
    (z3obj_create res) ;
    res
      

  let get_help ( x : fixedpoint ) =
    Z3native.fixedpoint_get_help (z3obj_gnc x) (z3obj_gno x)
      
  let set_params ( x : fixedpoint ) ( p : Params.params )=
    Z3native.fixedpoint_set_params (z3obj_gnc x) (z3obj_gno x) (z3obj_gno p)
      
  let get_param_descrs ( x : fixedpoint ) =
    Params.ParamDescrs.param_descrs_of_ptr (z3obj_gc x) (Z3native.fixedpoint_get_param_descrs (z3obj_gnc x) (z3obj_gno x))
      
  let add ( x : fixedpoint ) ( constraints : expr list ) =
    let f e = (Z3native.fixedpoint_assert (z3obj_gnc x) (z3obj_gno x) (Expr.gno e)) in
    ignore (List.map f constraints) ;
    ()

  let register_relation ( x : fixedpoint ) ( f : func_decl ) =
    Z3native.fixedpoint_register_relation (z3obj_gnc x) (z3obj_gno x) (FuncDecl.gno f)
      
  let add_rule ( x : fixedpoint ) ( rule : expr ) ( name : Symbol.symbol option ) =
    match name with 
      | None -> Z3native.fixedpoint_add_rule (z3obj_gnc x) (z3obj_gno x) (Expr.gno rule) null
      | Some(y) -> Z3native.fixedpoint_add_rule (z3obj_gnc x) (z3obj_gno x) (Expr.gno rule) (Symbol.gno y)

  let add_fact ( x : fixedpoint ) ( pred : func_decl ) ( args : int list ) =
    Z3native.fixedpoint_add_fact (z3obj_gnc x) (z3obj_gno x) (FuncDecl.gno pred) (List.length args) (Array.of_list args)

  let query ( x : fixedpoint ) ( query : expr ) =
    match (lbool_of_int (Z3native.fixedpoint_query (z3obj_gnc x) (z3obj_gno x) (Expr.gno query))) with
      | L_TRUE -> Solver.SATISFIABLE
      | L_FALSE -> Solver.UNSATISFIABLE
      | _ -> Solver.UNKNOWN

  let query_r ( x : fixedpoint ) ( relations : func_decl list ) =
    let f x = AST.ptr_of_ast (ast_of_func_decl x) in
    match (lbool_of_int (Z3native.fixedpoint_query_relations (z3obj_gnc x) (z3obj_gno x) (List.length relations) (Array.of_list (List.map f relations)))) with
      | L_TRUE -> Solver.SATISFIABLE
      | L_FALSE -> Solver.UNSATISFIABLE
      | _ -> Solver.UNKNOWN
	
  let push ( x : fixedpoint ) =
    Z3native.fixedpoint_push (z3obj_gnc x) (z3obj_gno x)
      
  let pop ( x : fixedpoint ) =
    Z3native.fixedpoint_pop (z3obj_gnc x) (z3obj_gno x)

  let update_rule ( x : fixedpoint ) ( rule : expr ) ( name : Symbol.symbol ) =
    Z3native.fixedpoint_update_rule (z3obj_gnc x) (z3obj_gno x) (Expr.gno rule) (Symbol.gno name)

  let get_answer ( x : fixedpoint ) =
    let q = (Z3native.fixedpoint_get_answer (z3obj_gnc x) (z3obj_gno x)) in
    if (Z3native.is_null q) then
      None
    else
      Some (expr_of_ptr (z3obj_gc x) q)

  let get_reason_unknown ( x : fixedpoint ) =
    Z3native.fixedpoint_get_reason_unknown (z3obj_gnc x) (z3obj_gno x)

  let get_num_levels ( x : fixedpoint ) ( predicate : func_decl ) =
    Z3native.fixedpoint_get_num_levels (z3obj_gnc x) (z3obj_gno x) (FuncDecl.gno predicate)

  let get_cover_delta ( x : fixedpoint ) ( level : int ) ( predicate : func_decl ) =
    let q = (Z3native.fixedpoint_get_cover_delta (z3obj_gnc x) (z3obj_gno x) level (FuncDecl.gno predicate)) in
    if (Z3native.is_null q) then
      None
    else
      Some (expr_of_ptr (z3obj_gc x) q)
	
  let add_cover ( x : fixedpoint ) ( level : int ) ( predicate : func_decl ) ( property : expr ) =
    Z3native.fixedpoint_add_cover (z3obj_gnc x) (z3obj_gno x) level (FuncDecl.gno predicate) (Expr.gno property)
      
  let to_string ( x : fixedpoint ) = Z3native.fixedpoint_to_string (z3obj_gnc x) (z3obj_gno x) 0 [||]
    
  let set_predicate_representation ( x : fixedpoint ) ( f : func_decl ) ( kinds : Symbol.symbol list ) =
    Z3native.fixedpoint_set_predicate_representation (z3obj_gnc x) (z3obj_gno x) (FuncDecl.gno f) (List.length kinds) (Symbol.symbol_lton kinds)

  let to_string_q ( x : fixedpoint ) ( queries : expr list ) =
    let f x = Expr.gno x in
    Z3native.fixedpoint_to_string (z3obj_gnc x) (z3obj_gno x) (List.length queries) (Array.of_list (List.map f queries))

  let get_rules ( x : fixedpoint ) = 
    let av = (AST.ASTVector.create (z3obj_gc x) (Z3native.fixedpoint_get_rules (z3obj_gnc x) (z3obj_gno x))) in
    (AST.ASTVector.to_expr_list av)

  let get_assertions ( x : fixedpoint ) = 
    let av = (AST.ASTVector.create (z3obj_gc x) (Z3native.fixedpoint_get_assertions (z3obj_gnc x) (z3obj_gno x))) in
    (AST.ASTVector.to_expr_list av)

  let mk_fixedpoint ( ctx : context ) = create ctx

  let get_statistics ( x : fixedpoint ) =
    let s = Z3native.fixedpoint_get_statistics (z3obj_gnc x) (z3obj_gno x) in
    (Statistics.create (z3obj_gc x) s)

  let parse_string ( x : fixedpoint ) ( s : string ) =
    let av = (AST.ASTVector.create (z3obj_gc x) (Z3native.fixedpoint_from_string (z3obj_gnc x) (z3obj_gno x) s)) in
    (AST.ASTVector.to_expr_list av)

  let parse_file ( x : fixedpoint ) ( filename : string ) =
    let av = (AST.ASTVector.create (z3obj_gc x) (Z3native.fixedpoint_from_file (z3obj_gnc x) (z3obj_gno x) filename)) in
    (AST.ASTVector.to_expr_list av)
end


module SMT =
struct
  let benchmark_to_smtstring ( ctx : context ) ( name : string ) ( logic : string ) ( status : string ) ( attributes : string ) ( assumptions : expr list ) ( formula : expr ) =
    Z3native.benchmark_to_smtlib_string (context_gno ctx) name logic status attributes
      (List.length assumptions) (let f x = Expr.gno (x) in (Array.of_list (List.map f assumptions)))
      (Expr.gno formula)

  let parse_smtlib_string ( ctx : context ) ( str : string ) ( sort_names : Symbol.symbol list ) ( sorts : Sort.sort list ) ( decl_names : Symbol.symbol list ) ( decls : func_decl list ) =
    let csn = (List.length sort_names) in
    let cs = (List.length sorts) in
    let cdn = (List.length decl_names) in
    let cd = (List.length decls) in
    if (csn != cs || cdn != cd) then 
      raise (Z3native.Exception "Argument size mismatch")
    else
      Z3native.parse_smtlib_string (context_gno ctx) str 
	    cs 
	    (Symbol.symbol_lton sort_names)
	    (Sort.sort_lton sorts)
	    cd 
	    (Symbol.symbol_lton decl_names)
	    (let f x = FuncDecl.gno x in (Array.of_list (List.map f decls)))
	
  let parse_smtlib_file ( ctx : context ) ( file_name : string ) ( sort_names : Symbol.symbol list ) ( sorts : Sort.sort list ) ( decl_names : Symbol.symbol list ) ( decls : func_decl list ) =
    let csn = (List.length sort_names) in
    let cs = (List.length sorts) in
    let cdn = (List.length decl_names) in
    let cd = (List.length decls) in
    if (csn != cs || cdn != cd) then 
      raise (Z3native.Exception "Argument size mismatch")
    else
      Z3native.parse_smtlib_file (context_gno ctx) file_name
	    cs 
	    (Symbol.symbol_lton sort_names)
	    (Sort.sort_lton sorts)
	    cd 
	    (Symbol.symbol_lton decl_names)
	    (let f x = FuncDecl.gno x in (Array.of_list (List.map f decls)))
        
  let get_num_smtlib_formulas ( ctx : context ) = Z3native.get_smtlib_num_formulas (context_gno ctx)

  let get_smtlib_formulas ( ctx : context ) =
    let n = (get_num_smtlib_formulas ctx ) in
    let f i =(expr_of_ptr ctx (Z3native.get_smtlib_formula (context_gno ctx) i)) in
    mk_list f n 

  let get_num_smtlib_assumptions ( ctx : context ) = Z3native.get_smtlib_num_assumptions (context_gno ctx)

  let get_smtlib_assumptions ( ctx : context ) =
    let n = (get_num_smtlib_assumptions ctx ) in
    let f i = (expr_of_ptr ctx (Z3native.get_smtlib_assumption (context_gno ctx) i)) in
    mk_list f n

  let get_num_smtlib_decls ( ctx : context ) = Z3native.get_smtlib_num_decls (context_gno ctx)

  let get_smtlib_decls ( ctx : context ) = 
    let n = (get_num_smtlib_decls ctx) in
    let f i = func_decl_of_ptr ctx (Z3native.get_smtlib_decl (context_gno ctx) i) in
    mk_list f n

  let get_num_smtlib_sorts ( ctx : context )  = Z3native.get_smtlib_num_sorts (context_gno ctx)
    
  let get_smtlib_sorts ( ctx : context ) = 
    let n = (get_num_smtlib_sorts ctx) in
    let f i = (Sort.sort_of_ptr ctx (Z3native.get_smtlib_sort (context_gno ctx) i)) in
    mk_list f n

  let parse_smtlib2_string ( ctx : context ) ( str : string ) ( sort_names : Symbol.symbol list ) ( sorts : Sort.sort list ) ( decl_names : Symbol.symbol list ) ( decls : func_decl list ) =
    let csn = (List.length sort_names) in
    let cs = (List.length sorts) in
    let cdn = (List.length decl_names) in
    let cd = (List.length decls) in
    if (csn != cs || cdn != cd) then 
      raise (Z3native.Exception "Argument size mismatch")
    else
      (expr_of_ptr ctx (Z3native.parse_smtlib2_string (context_gno ctx) str 
			              cs 
			              (Symbol.symbol_lton sort_names)
			              (Sort.sort_lton sorts)
			              cd 
			              (Symbol.symbol_lton decl_names)
			              (let f x = FuncDecl.gno x in (Array.of_list (List.map f decls)))))
	    
  let parse_smtlib2_file ( ctx : context ) ( file_name : string ) ( sort_names : Symbol.symbol list ) ( sorts : Sort.sort list ) ( decl_names : Symbol.symbol list ) ( decls : func_decl list ) =
    let csn = (List.length sort_names) in
    let cs = (List.length sorts) in
    let cdn = (List.length decl_names) in
    let cd = (List.length decls) in
    if (csn != cs || cdn != cd) then 
      raise (Z3native.Exception "Argument size mismatch")
    else
      (expr_of_ptr ctx (Z3native.parse_smtlib2_string (context_gno ctx) file_name
			              cs 
			              (Symbol.symbol_lton sort_names)
			              (Sort.sort_lton sorts)
			              cd 
			              (Symbol.symbol_lton decl_names)
			              (let f x = FuncDecl.gno x in (Array.of_list (List.map f decls)))))
end

module Interpolation = 
struct
  let mk_interpolant ( ctx : context ) ( a : expr ) =
    (expr_of_ptr ctx (Z3native.mk_interpolant (context_gno ctx) (Expr.gno a)))
    
  let mk_interpolation_context ( settings : ( string * string ) list ) =
    let cfg = Z3native.mk_config () in
    let f e = (Z3native.set_param_value cfg (fst e) (snd e)) in
    (List.iter f settings) ;
    let v = Z3native.mk_interpolation_context cfg in
    Z3native.del_config(cfg) ;
    Z3native.set_ast_print_mode v (int_of_ast_print_mode PRINT_SMTLIB2_COMPLIANT) ;
    Z3native.set_internal_error_handler v ;
    let res = { m_n_ctx = v; m_n_obj_cnt = 0 } in
    let f = fun o -> dispose_context o in
    Gc.finalise f res;
    res

  let get_interpolant ( ctx : context ) ( pf : expr ) ( pat: expr ) ( p : Params.params ) =
    let av = (AST.ASTVector.create ctx (Z3native.get_interpolant (context_gno ctx) (Expr.gno pf) (Expr.gno pat) (z3obj_gno p))) in
    AST.ASTVector.to_expr_list av
      
  let compute_interpolant ( ctx : context ) ( pat : expr ) ( p : Params.params ) =
    let (r, interp, model) = (Z3native.compute_interpolant (context_gno ctx) (Expr.gno pat) (z3obj_gno p)) in
    let res = (lbool_of_int r) in
    match res with
      | L_TRUE -> (res, None, Some(Model.create ctx model))
      | L_FALSE -> (res, Some((AST.ASTVector.to_expr_list (AST.ASTVector.create ctx interp))), None)
      | _ -> (res, None, None)
       
  let get_interpolation_profile ( ctx : context ) =
    (Z3native.interpolation_profile (context_gno ctx))
      
  let read_interpolation_problem ( ctx : context ) ( filename : string ) =
    let (r, num, cnsts, parents, error, num_theory, theory) = (Z3native.read_interpolation_problem (context_gno ctx) filename) in
    match r with 
      | 0 -> raise (Z3native.Exception "Interpolation problem could not be read.")
      | _ ->
	let f1 i = (expr_of_ptr ctx (Array.get cnsts i)) in
	let f2 i = (Array.get parents i) in
	let f3 i = (expr_of_ptr ctx (Array.get theory i)) in 
	((mk_list f1 num),
	 (mk_list f2 num),
	 (mk_list f3 num_theory))
          
  let check_interpolant ( ctx : context ) ( num : int ) ( cnsts : Expr.expr list ) ( parents : int list ) ( interps : Expr.expr list ) ( num_theory : int ) ( theory : Expr.expr list ) =
    let (r, str) = (Z3native.check_interpolant (context_gno ctx) 
		      num
		      (let f x = Expr.gno x in (Array.of_list (List.map f cnsts)))
		      (Array.of_list parents)
		      (let f x = Expr.gno x in (Array.of_list (List.map f interps)))
		      num_theory
		      (let f x = Expr.gno x in (Array.of_list (List.map f theory)))) in
    match (lbool_of_int r) with
      | L_UNDEF -> raise (Z3native.Exception "Interpolant could not be verified.")
      | L_FALSE -> raise (Z3native.Exception "Interpolant could not be verified.")
      | _ -> ()

  let write_interpolation_problem ( ctx : context ) ( num : int ) ( cnsts : Expr.expr list ) ( parents : int list ) ( filename : string ) ( num_theory : int ) ( theory : Expr.expr list ) =
    (Z3native.write_interpolation_problem (context_gno ctx) num (expr_lton cnsts) (Array.of_list parents) filename num_theory (expr_lton theory)) ;
    ()
end

let set_global_param ( id : string ) ( value : string ) =
  (Z3native.global_param_set id value)

let get_global_param ( id : string ) =
  let (r, v) = (Z3native.global_param_get id) in
  if not r then
    None
  else 
    Some v

let global_param_reset_all =
  Z3native.global_param_reset_all

let toggle_warning_messages ( enabled : bool ) =
  Z3native.toggle_warning_messages enabled

let enable_trace ( tag : string ) =
  (Z3native.enable_trace tag)

let disable_trace ( tag : string ) =
  (Z3native.enable_trace tag)


