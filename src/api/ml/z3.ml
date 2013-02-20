(**
   The Z3 ML/Ocaml Interface.

   Copyright (C) 2012 Microsoft Corporation
   @author CM Wintersteiger (cwinter) 2012-12-17
*)

open Z3enums

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
    let cfg = Z3native.mk_config in
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

  let array_to_native a =
    let f e = (z3obj_gno e) in 
    Array.map f a

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
  let major = let (x, _, _, _) = Z3native.get_version in x
  let minor = let (_, x, _, _) = Z3native.get_version in x
  let build = let (_, _, x, _) = Z3native.get_version in x
  let revision = let (_, _, _, x) = Z3native.get_version in x
  let to_string = 
    let (mj, mn, bld, rev) = Z3native.get_version in
    string_of_int mj ^ "." ^
      string_of_int mn ^ "." ^
      string_of_int bld ^ "." ^
      string_of_int rev ^ "."
end


let mk_list ( f : int -> 'a ) ( n : int ) =
  let rec mk_list' ( f : int -> 'a ) ( i : int ) ( n : int )  ( tail : 'a list ) : 'a list =       
    if (i >= n) then 
      tail
    else
      (mk_list' f (i+1) n ((f i) :: tail))
  in
  mk_list' f 0 n []


let mk_context ( cfg : ( string * string ) list ) =
  create_context cfg


module Symbol =
struct
  (* Symbol types *)
  type int_symbol = z3_native_object
  type string_symbol = z3_native_object
      
  type symbol = 
    | S_Int of int_symbol
    | S_Str of string_symbol 


  let create_i ( ctx : context ) ( no : Z3native.ptr ) = 
    let res : int_symbol = { m_ctx = ctx ;
			     m_n_obj = null ;
			     inc_ref = z3obj_nil_ref ;
			     dec_ref = z3obj_nil_ref } in
    (z3obj_sno res ctx no) ;
    (z3obj_create res) ;
    res

  let create_s ( ctx : context ) ( no : Z3native.ptr ) = 
    let res : string_symbol = { m_ctx = ctx ;
				m_n_obj = null ;
				inc_ref = z3obj_nil_ref ;
				dec_ref = z3obj_nil_ref } in
    (z3obj_sno res ctx no) ;
    (z3obj_create res) ;
    res

  let create ( ctx : context ) ( no : Z3native.ptr ) =
    match (symbol_kind_of_int (Z3native.get_symbol_kind (context_gno ctx) no)) with
      | INT_SYMBOL -> S_Int (create_i ctx no)
      | STRING_SYMBOL -> S_Str (create_s ctx no)	

  let gc ( x : symbol ) = 
    match x with
      | S_Int(n) -> (z3obj_gc n)
      | S_Str(n) -> (z3obj_gc n)
	
  let gnc ( x : symbol ) = 
    match x with
      | S_Int(n) -> (z3obj_gnc n)
      | S_Str(n) -> (z3obj_gnc n)
	
  let gno ( x : symbol ) = 
    match x with
      | S_Int(n) -> (z3obj_gno n)
      | S_Str(n) -> (z3obj_gno n)
       	
  let kind ( o : symbol ) = (symbol_kind_of_int (Z3native.get_symbol_kind (gnc o) (gno o)))   
  let is_int_symbol ( o : symbol ) = (kind o) == INT_SYMBOL
  let is_string_symbol ( o : symbol ) = (kind o) == STRING_SYMBOL
  let get_int (o : int_symbol) = Z3native.get_symbol_int (z3obj_gnc o) (z3obj_gno o)
  let get_string (o : string_symbol) = Z3native.get_symbol_string (z3obj_gnc o) (z3obj_gno o)
  let to_string ( o : symbol ) = 
    match (kind o) with
      | INT_SYMBOL -> (string_of_int (Z3native.get_symbol_int (gnc o) (gno o)))
      | STRING_SYMBOL -> (Z3native.get_symbol_string (gnc o) (gno o))

  let mk_int ( ctx : context ) ( i : int ) = 
    S_Int (create_i ctx (Z3native.mk_int_symbol (context_gno ctx) i))
      
  let mk_string ( ctx : context ) ( s : string ) =
    S_Str (create_s ctx (Z3native.mk_string_symbol (context_gno ctx) s))

  let mk_ints ( ctx : context ) ( names : int array ) =
    let f elem = mk_int ( ctx : context ) elem in
    (Array.map f names)

  let mk_strings ( ctx : context ) ( names : string array ) =
    let f elem = mk_string ( ctx : context ) elem in
    (Array.map f names)      
end


module AST =
struct    
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
    
    let ast_vector_of_ptr ( ctx : context ) ( no : Z3native.ptr ) = 
      let res : ast_vector = { m_ctx = ctx ;
			       m_n_obj = null ;
			       inc_ref = Z3native.ast_vector_inc_ref ;
			       dec_ref = Z3native.ast_vector_dec_ref } in
      (z3obj_sno res ctx no) ;
      (z3obj_create res) ;
      res
	
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
      ast_vector_of_ptr to_ctx (Z3native.ast_vector_translate (z3obj_gnc x) (z3obj_gno x) (context_gno to_ctx))
	
    let to_string ( x : ast_vector ) =
      Z3native.ast_vector_to_string (z3obj_gnc x) (z3obj_gno x)
  end

  module ASTMap =
  struct	
    type ast_map = z3_native_object
    
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
	
    let insert ( x : ast_map ) ( key : ast ) ( value : ast) =
      Z3native.ast_map_insert (z3obj_gnc x) (z3obj_gno x) (z3obj_gno key) (z3obj_gno value)

    let erase ( x : ast_map ) ( key : ast ) =
      Z3native.ast_map_erase (z3obj_gnc x) (z3obj_gno x) (z3obj_gno key)
	
    let reset ( x : ast_map ) =
      Z3native.ast_map_reset (z3obj_gnc x) (z3obj_gno x)

    let get_size ( x : ast_map ) =
      Z3native.ast_map_size (z3obj_gnc x) (z3obj_gno x)
	
    let get_keys ( x : ast_map ) =
      ASTVector.ast_vector_of_ptr (z3obj_gc x) (Z3native.ast_map_keys (z3obj_gnc x) (z3obj_gno x))

    let to_string ( x : ast_map ) =
      Z3native.ast_map_to_string (z3obj_gnc x) (z3obj_gno x)
  end

  let get_hash_code ( x : ast ) = Z3native.get_ast_hash (z3obj_gnc x) (z3obj_gno x)
  let get_id ( x : ast ) = Z3native.get_ast_id (z3obj_gnc x) (z3obj_gno x)
  let get_ast_kind ( x : ast ) = (ast_kind_of_int (Z3native.get_ast_kind (z3obj_gnc x) (z3obj_gno x)))
    
  let is_expr ( x : ast ) = 
    match get_ast_kind ( x : ast ) with
      | APP_AST
      | NUMERAL_AST
      | QUANTIFIER_AST
      | VAR_AST -> true
      | _ -> false
	
  let is_var ( x : ast ) = (get_ast_kind x) == VAR_AST   
  let is_quantifier ( x : ast ) = (get_ast_kind x) == QUANTIFIER_AST
  let is_sort ( x : ast ) = (get_ast_kind x) == SORT_AST
  let is_func_decl ( x : ast ) = (get_ast_kind x) == FUNC_DECL_AST

  let to_string ( x : ast ) = Z3native.ast_to_string (z3obj_gnc x) (z3obj_gno x)
  let to_sexpr ( x : ast ) = Z3native.ast_to_string (z3obj_gnc x) (z3obj_gno x)


  let ( = ) ( a : ast ) ( b : ast ) = (a == b) ||
    if (z3obj_gnc a) != (z3obj_gnc b) then 
      false 
    else 
      Z3native.is_eq_ast (z3obj_gnc a) (z3obj_gno a) (z3obj_gno b)
	
  let compare a b = 
    if (get_id a) < (get_id b) then -1 else
      if (get_id a) > (get_id b) then 1 else
	0
	  
  let ( < ) (a : ast) (b : ast) = (compare a b)
    
  let translate ( x : ast ) ( to_ctx : context ) = 
    if (z3obj_gnc x) == (context_gno to_ctx) then 
      x
    else
      ast_of_ptr to_ctx (Z3native.translate (z3obj_gnc x) (z3obj_gno x) (context_gno to_ctx))

  let wrap_ast ( ctx : context ) ( ptr : Z3native.ptr ) = ast_of_ptr ctx ptr
  let unwrap_ast ( x : ast ) = (z3obj_gno x)      
end

open AST


module Sort = 
struct
  type sort = Sort of AST.ast
  type uninterpreted_sort = UninterpretedSort of sort

  let sort_of_ptr : context -> Z3native.ptr -> sort = fun ctx no ->
    let q = (z3_native_object_of_ast_ptr ctx no) in
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
	| RELATION_SORT -> Sort(q)
	| UNKNOWN_SORT -> raise (Z3native.Exception "Unknown sort kind encountered")

  let ast_of_sort s = match s with Sort(x) -> x
  let sort_of_uninterpreted_sort s = match s with UninterpretedSort(x) -> x

  let uninterpreted_sort_of_sort s = match s with Sort(a) ->
    if ((Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) (z3obj_gno a))) != Z3enums.UNINTERPRETED_SORT) then
      raise (Z3native.Exception "Invalid coercion")
    else
      UninterpretedSort(s)       


  let gc ( x : sort ) = (match x with Sort(a) -> (z3obj_gc a))
  let gnc ( x : sort ) = (match x with Sort(a) -> (z3obj_gnc a))
  let gno ( x : sort ) = (match x with Sort(a) -> (z3obj_gno a))
    
  let ( = ) : sort -> sort -> bool = fun a b ->
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
    UninterpretedSort(Sort(res))

  let mk_uninterpreted_s ( ctx : context ) ( s : string ) =
    mk_uninterpreted ctx (Symbol.mk_string ( ctx : context ) s)
end 

open Sort


module rec FuncDecl :
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
  val mk_func_decl : context -> Symbol.symbol -> Sort.sort array -> Sort.sort -> func_decl
  val mk_func_decl_s : context -> string -> Sort.sort array -> Sort.sort -> func_decl
  val mk_fresh_func_decl : context -> string -> Sort.sort array -> Sort.sort -> func_decl
  val mk_const_decl : context -> Symbol.symbol -> Sort.sort -> func_decl
  val mk_const_decl_s : context -> string -> Sort.sort -> func_decl
  val mk_fresh_const_decl : context -> string -> Sort.sort -> func_decl
  val ( = ) : func_decl -> func_decl -> bool
  val to_string : func_decl -> string
  val get_id : func_decl -> int
  val get_arity : func_decl -> int
  val get_domain_size : func_decl -> int
  val get_domain : func_decl -> Sort.sort array
  val get_range : func_decl -> Sort.sort
  val get_decl_kind : func_decl -> Z3enums.decl_kind
  val get_name : func_decl -> Symbol.symbol
  val get_num_parameters : func_decl -> int
  val get_parameters : func_decl -> Parameter.parameter list
  val apply : func_decl -> Expr.expr array -> Expr.expr
end = struct
  type func_decl = FuncDecl of AST.ast

  let func_decl_of_ptr : context -> Z3native.ptr -> func_decl = fun ctx no ->
    if ((Z3enums.ast_kind_of_int (Z3native.get_ast_kind (context_gno ctx) no)) != Z3enums.FUNC_DECL_AST) then
      raise (Z3native.Exception "Invalid coercion")
    else
      FuncDecl(z3_native_object_of_ast_ptr ctx no)

  let ast_of_func_decl f = match f with FuncDecl(x) -> x

  let create_ndr ( ctx : context ) ( name : Symbol.symbol ) ( domain : sort array ) ( range : sort )  = 
    let res = { m_ctx = ctx ;
		m_n_obj = null ;
		inc_ref = Z3native.inc_ref ;
		dec_ref = Z3native.dec_ref } in
    let f x = (AST.ptr_of_ast (ast_of_sort x)) in
    (z3obj_sno res ctx (Z3native.mk_func_decl (context_gno ctx) (Symbol.gno name) (Array.length domain) (Array.map f domain) (Sort.gno range))) ;
    (z3obj_create res) ;
    FuncDecl(res)
      
  let create_pdr ( ctx : context) ( prefix : string ) ( domain : sort array ) ( range : sort ) = 
    let res = { m_ctx = ctx ;
		m_n_obj = null ;
		inc_ref = Z3native.inc_ref ;
		dec_ref = Z3native.dec_ref } in
    let f x = (AST.ptr_of_ast (ast_of_sort x)) in
    (z3obj_sno res ctx (Z3native.mk_fresh_func_decl (context_gno ctx) prefix (Array.length domain) (Array.map f domain) (Sort.gno range))) ;
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
	| _ -> raise (Z3native.Exception "parameter is not a double")
          
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

  let mk_func_decl ( ctx : context ) ( name : Symbol.symbol ) ( domain : sort array ) ( range : sort ) =
    create_ndr ctx name domain range

  let mk_func_decl_s ( ctx : context ) ( name : string ) ( domain : sort array ) ( range : sort ) =
    mk_func_decl ctx (Symbol.mk_string ctx name) domain range

  let mk_fresh_func_decl ( ctx : context ) ( prefix : string ) ( domain : sort array ) ( range : sort ) =
    create_pdr ctx prefix domain range

  let mk_const_decl ( ctx : context ) ( name : Symbol.symbol ) ( range : sort ) =
    create_ndr ctx name [||] range

  let mk_const_decl_s ( ctx : context ) ( name : string ) ( range : sort ) =
    create_ndr ctx (Symbol.mk_string ctx name) [||]  range

  let mk_fresh_const_decl ( ctx : context ) ( prefix : string ) ( range : sort ) =
    create_pdr ctx prefix [||] range


  let ( = ) ( a : func_decl ) ( b : func_decl ) = (a == b) ||
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
    let f i = sort_of_ptr (gc x) (Z3native.get_domain (gnc x) (gno x) i) in
    Array.init n f
      
  let get_range ( x : func_decl ) = 
    sort_of_ptr (gc x) (Z3native.get_range (gnc x) (gno x))
      
  let get_decl_kind ( x : func_decl ) = (decl_kind_of_int (Z3native.get_decl_kind (gnc x) (gno x)))

  let get_name ( x : func_decl ) = (Symbol.create (gc x) (Z3native.get_decl_name (gnc x) (gno x)))

  let get_num_parameters ( x : func_decl ) = (Z3native.get_decl_num_parameters (gnc x) (gno x))    

  let get_parameters ( x : func_decl ) =
    let n = (get_num_parameters x) in
    let f i = (match (parameter_kind_of_int (Z3native.get_decl_parameter_kind (gnc x) (gno x) i)) with
      | PARAMETER_INT -> Parameter.P_Int (Z3native.get_decl_int_parameter (gnc x) (gno x) i)
      | PARAMETER_DOUBLE -> Parameter.P_Dbl (Z3native.get_decl_double_parameter (gnc x) (gno x) i)
      | PARAMETER_SYMBOL-> Parameter.P_Sym (Symbol.create (gc x) (Z3native.get_decl_symbol_parameter (gnc x) (gno x) i))
      | PARAMETER_SORT -> Parameter.P_Srt (sort_of_ptr (gc x) (Z3native.get_decl_sort_parameter (gnc x) (gno x) i))
      | PARAMETER_AST -> Parameter.P_Ast (AST.ast_of_ptr (gc x) (Z3native.get_decl_ast_parameter (gnc x) (gno x) i))
      | PARAMETER_FUNC_DECL -> Parameter.P_Fdl (func_decl_of_ptr (gc x) (Z3native.get_decl_func_decl_parameter (gnc x) (gno x) i))
      | PARAMETER_RATIONAL -> Parameter.P_Rat (Z3native.get_decl_rational_parameter (gnc x) (gno x) i)
    ) in
    mk_list f n

  let apply ( x : func_decl ) ( args : Expr.expr array ) = Expr.expr_of_func_app (gc x) x args 
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
    val get_names : param_descrs -> Symbol.symbol array
    val get_size : param_descrs -> int
    val to_string : param_descrs -> string
  end
  val add_bool : params -> Symbol.symbol -> bool -> unit
  val add_int : params -> Symbol.symbol -> int -> unit
  val add_double : params -> Symbol.symbol -> float -> unit
  val add_symbol : params -> Symbol.symbol -> Symbol.symbol -> unit
  val add_s_bool : params -> string -> bool -> unit
  val add_s_int : params -> string -> int -> unit
  val add_s_double : params -> string -> float -> unit
  val add_s_symbol : params -> string -> Symbol.symbol -> unit
  val mk_params : context -> params
  val to_string : params -> string
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
      Array.init n f

    let get_size ( x : param_descrs ) = Z3native.param_descrs_size (z3obj_gnc x) (z3obj_gno x)    
    let to_string ( x : param_descrs ) = Z3native.param_descrs_to_string (z3obj_gnc x) (z3obj_gno x) 
  end

  let add_bool ( x : params ) ( name : Symbol.symbol ) ( value : bool ) =
    Z3native.params_set_bool (z3obj_gnc x) (z3obj_gno x) (Symbol.gno name) value
      
  let add_int ( x : params )  (name : Symbol.symbol ) ( value : int ) =
    Z3native.params_set_uint (z3obj_gnc x) (z3obj_gno x) (Symbol.gno name) value
      
  let add_double ( x : params ) ( name : Symbol.symbol ) ( value : float ) =
    Z3native.params_set_double (z3obj_gnc x) (z3obj_gno x) (Symbol.gno name) value

  let add_symbol ( x : params ) ( name : Symbol.symbol ) ( value : Symbol.symbol ) =
    Z3native.params_set_symbol (z3obj_gnc x) (z3obj_gno x) (Symbol.gno name) (Symbol.gno value)

  let add_s_bool ( x : params ) ( name : string ) ( value : bool ) =
    add_bool x (Symbol.mk_string (z3obj_gc x) name) value
      
  let add_s_int ( x : params) ( name : string ) ( value : int ) =
    add_int x (Symbol.mk_string (z3obj_gc x) name) value
      
  let add_s_double ( x : params ) ( name : string ) ( value : float ) =
    add_double x (Symbol.mk_string (z3obj_gc x) name) value

  let add_s_symbol ( x : params ) ( name : string ) ( value : Symbol.symbol ) =
    add_symbol x (Symbol.mk_string (z3obj_gc x) name) value

  let mk_params ( ctx : context ) =
    let res : params = { m_ctx = ctx ;
			 m_n_obj = null ;
			 inc_ref = Z3native.params_inc_ref ;
			 dec_ref = Z3native.params_dec_ref } in
    (z3obj_sno res ctx (Z3native.mk_params (context_gno ctx))) ;
    (z3obj_create res) ;
    res

  let to_string ( x : params ) = Z3native.params_to_string (z3obj_gnc x) (z3obj_gno x)
end

(** General expressions (terms) *)
and Expr :
sig
  type expr = Expr of AST.ast
  val expr_of_ptr : context -> Z3native.ptr -> expr
  val c_of_expr : expr -> context
  val nc_of_expr : expr -> Z3native.ptr
  val ptr_of_expr : expr -> Z3native.ptr
  val expr_aton : expr array -> Z3native.ptr array
  val ast_of_expr : expr -> AST.ast
  val expr_of_ast : AST.ast -> expr
  val expr_of_func_app : context -> FuncDecl.func_decl -> expr array -> expr
  val simplify : expr -> Params.params option -> expr
  val get_simplify_help : context -> string
  val get_simplify_parameter_descrs : context -> Params.ParamDescrs.param_descrs
  val get_func_decl : expr -> FuncDecl.func_decl
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
  val get_sort : expr -> Sort.sort
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
  val is_label_lit : expr -> bool
  val is_oeq : expr -> bool
  val mk_const : context -> Symbol.symbol -> Sort.sort -> expr
  val mk_const_s : context -> string -> Sort.sort -> expr
  val mk_const_f : context -> FuncDecl.func_decl -> expr
  val mk_fresh_const : context -> string -> Sort.sort -> expr
  val mk_app : context -> FuncDecl.func_decl -> expr array -> expr
  val mk_numeral_string : context -> string -> Sort.sort -> expr
  val mk_numeral_int : context -> int -> Sort.sort -> expr
end = struct  
  type expr = Expr of AST.ast
      
  let c_of_expr e = match e with Expr(a) -> (z3obj_gc a)
  let nc_of_expr e = match e with Expr(a) -> (z3obj_gnc a)
  let ptr_of_expr e = match e with Expr(a) -> (z3obj_gno a)

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
	  if (sk == INT_SORT or sk == REAL_SORT or sk == BV_SORT) then
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

  let expr_aton ( a : expr array ) =
    let f ( e : expr ) = match e with Expr(a) -> (AST.ptr_of_ast a) in 
    Array.map f a

  let expr_of_func_app : context -> FuncDecl.func_decl -> expr array -> expr = fun ctx f args ->
    match f with FuncDecl.FuncDecl(fa) ->
      let o = Z3native.mk_app (context_gno ctx) (AST.ptr_of_ast fa) (Array.length args) (expr_aton args) in
      expr_of_ptr ctx o

  let simplify ( x : expr ) ( p : Params.params option ) = match p with 
    | None -> expr_of_ptr (c_of_expr x) (Z3native.simplify (nc_of_expr x) (ptr_of_expr x))
    | Some pp -> expr_of_ptr (c_of_expr x) (Z3native.simplify_ex (nc_of_expr x) (ptr_of_expr x) (z3obj_gno pp))
      
  let get_simplify_help ( ctx : context ) =
    Z3native.simplify_get_help (context_gno ctx)

  let get_simplify_parameter_descrs ( ctx : context ) = 
    Params.ParamDescrs.param_descrs_of_ptr ctx (Z3native.simplify_get_param_descrs (context_gno ctx))
  let get_func_decl ( x : expr ) = FuncDecl.func_decl_of_ptr (c_of_expr x) (Z3native.get_app_decl (nc_of_expr x) (ptr_of_expr x))
    
  let get_bool_value ( x : expr ) = lbool_of_int (Z3native.get_bool_value (nc_of_expr x) (ptr_of_expr x))

  let get_num_args ( x : expr ) = Z3native.get_app_num_args (nc_of_expr x) (ptr_of_expr x)
    
  let get_args ( x : expr ) = let n = (get_num_args x) in
			      let f i = expr_of_ptr (c_of_expr x) (Z3native.get_app_arg (nc_of_expr x) (ptr_of_expr x) i) in
			      Array.init n f
				
  let update ( x : expr ) args =
    if (Array.length args <> (get_num_args x)) then
      raise (Z3native.Exception "Number of arguments does not match")
    else
      expr_of_ptr (c_of_expr x) (Z3native.update_term (nc_of_expr x) (ptr_of_expr x) (Array.length args) (expr_aton args))

  let substitute ( x : expr ) from to_ = 
    if (Array.length from) <> (Array.length to_) then
      raise (Z3native.Exception "Argument sizes do not match")
    else
      expr_of_ptr (c_of_expr x) (Z3native.substitute (nc_of_expr x) (ptr_of_expr x) (Array.length from) (expr_aton from) (expr_aton to_))
	
  let substitute_one ( x : expr ) from to_ =
    substitute ( x : expr ) [| from |] [| to_ |]
      
  let substitute_vars ( x : expr ) to_ =
    expr_of_ptr (c_of_expr x) (Z3native.substitute_vars (nc_of_expr x) (ptr_of_expr x) (Array.length to_) (expr_aton to_))
      
  let translate ( x : expr ) to_ctx =
    if (c_of_expr x) == to_ctx then
      x
    else
      expr_of_ptr to_ctx (Z3native.translate (nc_of_expr x) (ptr_of_expr x) (context_gno to_ctx))

  let to_string ( x : expr ) = Z3native.ast_to_string (nc_of_expr x) (ptr_of_expr x)

  let is_numeral ( x : expr ) = (Z3native.is_numeral_ast (nc_of_expr x) (ptr_of_expr x))
    
  let is_well_sorted ( x : expr ) = Z3native.is_well_sorted (nc_of_expr x) (ptr_of_expr x)

  let get_sort ( x : expr ) = sort_of_ptr (c_of_expr x) (Z3native.get_sort (nc_of_expr x) (ptr_of_expr x))
    
  let is_bool ( x : expr ) = (match x with Expr(a) -> (AST.is_expr a)) &&
    (Z3native.is_eq_sort (nc_of_expr x) 
       (Z3native.mk_bool_sort (nc_of_expr x))
       (Z3native.get_sort (nc_of_expr x) (ptr_of_expr x)))
    
  let is_const ( x : expr ) = (match x with Expr(a) -> (AST.is_expr a)) &&
    (get_num_args x) == 0 &&
    (FuncDecl.get_domain_size (get_func_decl x)) == 0
   
  let is_true ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_TRUE)
  let is_false ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_FALSE)
  let is_eq ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_EQ)
  let is_distinct ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_DISTINCT)
  let is_ite ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_ITE)
  let is_and ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_AND)
  let is_or ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_OR)
  let is_iff ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_IFF)
  let is_xor ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_XOR)
  let is_not ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_NOT)
  let is_implies ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_IMPLIES)
  let is_label ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_LABEL)
  let is_label_lit ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_LABEL_LIT)
  let is_oeq ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_OEQ)

  let mk_const ( ctx : context ) ( name : Symbol.symbol ) ( range : sort ) =
    expr_of_ptr ctx (Z3native.mk_const (context_gno ctx) (Symbol.gno name) (Sort.gno range))
      
  let mk_const_s ( ctx : context ) ( name : string ) ( range : sort ) =
    mk_const ctx (Symbol.mk_string ctx name) range

  let mk_const_f ( ctx : context ) ( f : FuncDecl.func_decl ) = Expr.expr_of_func_app ctx f [||]

  let mk_fresh_const ( ctx : context ) ( prefix : string ) ( range : sort ) =
    expr_of_ptr ctx (Z3native.mk_fresh_const (context_gno ctx) prefix (Sort.gno range))

  let mk_app ( ctx : context ) ( f : FuncDecl.func_decl ) ( args : expr array ) = expr_of_func_app ctx f args

  let mk_numeral_string ( ctx : context ) ( v : string ) ( ty : sort ) =
    expr_of_ptr ctx (Z3native.mk_numeral (context_gno ctx) v (Sort.gno ty))

  let mk_numeral_int ( ctx : context ) ( v : int ) ( ty : sort ) =
    expr_of_ptr ctx (Z3native.mk_int (context_gno ctx) v (Sort.gno ty))
end

open FuncDecl
open Expr

module Boolean = 
struct      
  type bool_sort = BoolSort of Sort.sort
  type bool_expr = BoolExpr of Expr.expr
 
  let bool_expr_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
    let a = (AST.ast_of_ptr ctx no) in
    BoolExpr(Expr.Expr(a))

  let bool_expr_of_expr e =
    match e with Expr.Expr(a) -> 
      let s = Z3native.get_sort (z3obj_gnc a) (z3obj_gno a) in
      let q = (Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) s)) in
      if (q != Z3enums.BOOL_SORT) then
	raise (Z3native.Exception "Invalid coercion")
      else
	BoolExpr(e)	  

  let bool_sort_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
    BoolSort(sort_of_ptr ctx no)

  let sort_of_bool_sort s = match s with BoolSort(x) -> x

  let bool_sort_of_sort s = match s with Sort(a) ->
    if ((Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) (z3obj_gno a))) != Z3enums.BOOL_SORT) then
      raise (Z3native.Exception "Invalid coercion")
    else
      BoolSort(s)

  let expr_of_bool_expr e = match e with BoolExpr(x) -> x

  let gc ( x : bool_expr ) = match x with BoolExpr(e) -> (Expr.c_of_expr e)
  let gnc ( x : bool_expr ) = match x with BoolExpr(e) -> (Expr.nc_of_expr e)
  let gno ( x : bool_expr ) = match x with BoolExpr(e) -> (Expr.ptr_of_expr e)

  let mk_sort ( ctx : context ) =
    BoolSort(sort_of_ptr ctx (Z3native.mk_bool_sort (context_gno ctx)))

  let mk_const ( ctx : context ) ( name : Symbol.symbol ) =
    let s = (match (mk_sort ctx) with BoolSort(q) -> q) in
    BoolExpr(Expr.mk_const ctx name s)
      
  let mk_const_s ( ctx : context ) ( name : string ) =
    mk_const ctx (Symbol.mk_string ctx name)

  let mk_true ( ctx : context ) =
    bool_expr_of_ptr ctx (Z3native.mk_true (context_gno ctx))

  let mk_false ( ctx : context ) =
    bool_expr_of_ptr ctx (Z3native.mk_false (context_gno ctx))

  let mk_val ( ctx : context ) ( value : bool ) =
    if value then mk_true ctx else mk_false ctx

  let mk_eq ( ctx : context ) ( x : expr ) ( y : expr ) =
    bool_expr_of_ptr ctx (Z3native.mk_eq (context_gno ctx) (ptr_of_expr x) (ptr_of_expr y))

  let mk_distinct ( ctx : context ) ( args : expr array ) =
    bool_expr_of_ptr ctx (Z3native.mk_distinct (context_gno ctx) (Array.length args) (expr_aton args))
      
  let mk_not ( ctx : context ) ( a : bool_expr ) =
    bool_expr_of_ptr ctx (Z3native.mk_not (context_gno ctx) (gno a))

  let mk_ite ( ctx : context ) ( t1 : bool_expr ) ( t2 : bool_expr ) ( t3 : bool_expr ) =
    bool_expr_of_ptr ctx (Z3native.mk_ite (context_gno ctx) (gno t1) (gno t2) (gno t3))
      
  let mk_iff ( ctx : context ) ( t1 : bool_expr ) ( t2 : bool_expr ) =
    bool_expr_of_ptr ctx (Z3native.mk_iff (context_gno ctx) (gno t1) (gno t2))

  let mk_implies ( ctx : context ) ( t1 : bool_expr ) ( t2 : bool_expr ) =
    bool_expr_of_ptr ctx (Z3native.mk_implies (context_gno ctx) (gno t1) (gno t2))

  let mk_xor ( ctx : context ) ( t1 : bool_expr ) ( t2 : bool_expr ) =
    bool_expr_of_ptr ctx (Z3native.mk_xor (context_gno ctx) (gno t1) (gno t2))

  let mk_and ( ctx : context ) ( args : bool_expr array ) =
    let f x = (ptr_of_expr (expr_of_bool_expr x)) in
    bool_expr_of_ptr ctx (Z3native.mk_and (context_gno ctx) (Array.length args) (Array.map f args))

  let mk_or ( ctx : context ) ( args : bool_expr array ) =
    let f x = (ptr_of_expr (expr_of_bool_expr x)) in
    bool_expr_of_ptr ctx (Z3native.mk_or (context_gno ctx) (Array.length args) (Array.map f args))
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
  
  let gc ( x : quantifier ) = match (x) with Quantifier(e) -> (c_of_expr e)
  let gnc ( x : quantifier ) = match (x) with Quantifier(e) -> (nc_of_expr e)
  let gno ( x : quantifier ) = match (x) with Quantifier(e) -> (ptr_of_expr e)
    
  module Pattern = 
  struct
    type pattern = Pattern of ast
  
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
      Array.init n f
	
    let to_string ( x : pattern ) = Z3native.pattern_to_string (gnc x) (gno x)
  end

  let get_index ( x : expr ) = 
    if not (AST.is_var (match x with Expr.Expr(a) -> a)) then
      raise (Z3native.Exception "Term is not a bound variable.")
    else
      Z3native.get_index_value (nc_of_expr x) (ptr_of_expr x)

  let is_universal ( x : quantifier ) =
    Z3native.is_quantifier_forall (gnc x) (gno x)
      
  let is_existential ( x : quantifier ) = not (is_universal x)

  let get_weight ( x : quantifier ) = Z3native.get_quantifier_weight (gnc x) (gno x)
    
  let get_num_patterns ( x : quantifier ) = Z3native.get_quantifier_num_patterns (gnc x) (gno x)
    
  let get_patterns ( x : quantifier ) =
    let n = (get_num_patterns x) in
    let f i = Pattern.Pattern (z3_native_object_of_ast_ptr (gc x) (Z3native.get_quantifier_pattern_ast (gnc x) (gno x) i)) in
    Array.init n f
      
  let get_num_no_patterns ( x : quantifier ) = Z3native.get_quantifier_num_no_patterns (gnc x) (gno x)
    
  let get_no_patterns ( x : quantifier ) =
    let n = (get_num_patterns x) in
    let f i = Pattern.Pattern (z3_native_object_of_ast_ptr (gc x) (Z3native.get_quantifier_no_pattern_ast (gnc x) (gno x) i)) in
    Array.init n f
      
  let get_num_bound ( x : quantifier ) = Z3native.get_quantifier_num_bound (gnc x) (gno x)
    
  let get_bound_variable_names ( x : quantifier ) =
    let n = (get_num_bound x) in
    let f i = (Symbol.create (gc x) (Z3native.get_quantifier_bound_name (gnc x) (gno x) i)) in
    Array.init n f
      
  let get_bound_variable_sorts ( x : quantifier ) =
    let n = (get_num_bound x) in
    let f i = (sort_of_ptr (gc x) (Z3native.get_quantifier_bound_sort (gnc x) (gno x) i)) in
    Array.init n f
      
  let get_body ( x : quantifier ) =
    Boolean.bool_expr_of_ptr (gc x) (Z3native.get_quantifier_body (gnc x) (gno x))  

  let mk_bound ( ctx : context ) ( index : int ) ( ty : sort ) =
    expr_of_ptr ctx (Z3native.mk_bound (context_gno ctx) index (Sort.gno ty))

  let mk_pattern ( ctx : context ) ( terms : expr array ) =
    if (Array.length terms) == 0 then
      raise (Z3native.Exception "Cannot create a pattern from zero terms")
    else
      Pattern.Pattern(z3_native_object_of_ast_ptr ctx (Z3native.mk_pattern (context_gno ctx) (Array.length terms) (expr_aton terms)))

  let mk_forall ( ctx : context ) ( sorts : sort array ) ( names : Symbol.symbol array ) ( body : expr ) ( weight : int option ) ( patterns : Pattern.pattern array ) ( nopatterns : expr array ) ( quantifier_id : Symbol.symbol option ) ( skolem_id : Symbol.symbol option ) =
    if (Array.length sorts) != (Array.length names) then
      raise (Z3native.Exception "Number of sorts does not match number of names")
    else if ((Array.length nopatterns) == 0 && quantifier_id == None && skolem_id == None) then
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier (context_gno ctx) true 
				    (match weight with | None -> 1 | Some(x) -> x)
				    (Array.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.map f patterns))
				    (Array.length sorts) (let f x = (AST.ptr_of_ast (ast_of_sort x)) in (Array.map f sorts))
				    (let f x = (Symbol.gno x) in (Array.map f names))
				    (ptr_of_expr body)))
    else
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier_ex (context_gno ctx) true
				    (match weight with | None -> 1 | Some(x) -> x)
				    (match quantifier_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (match skolem_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (Array.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.map f patterns))
				    (Array.length nopatterns) (expr_aton nopatterns)
				    (Array.length sorts) (let f x = (AST.ptr_of_ast (ast_of_sort x)) in (Array.map f sorts))
				    (let f x = (Symbol.gno x) in (Array.map f names))
				    (ptr_of_expr body)))
	
  let mk_forall_const ( ctx : context ) ( bound_constants : expr array ) ( body : expr ) ( weight : int option ) ( patterns : Pattern.pattern array ) ( nopatterns : expr array ) ( quantifier_id : Symbol.symbol option ) ( skolem_id : Symbol.symbol option ) =
    if ((Array.length nopatterns) == 0 && quantifier_id == None && skolem_id == None) then
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier_const (context_gno ctx) true
				    (match weight with | None -> 1 | Some(x) -> x)
				    (Array.length bound_constants) (expr_aton bound_constants)
				    (Array.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.map f patterns))
				    (ptr_of_expr body)))
    else
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier_const_ex (context_gno ctx) true
				    (match weight with | None -> 1 | Some(x) -> x)
				    (match quantifier_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (match skolem_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (Array.length bound_constants) (expr_aton bound_constants)
				    (Array.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.map f patterns))
				    (Array.length nopatterns) (expr_aton nopatterns)
				    (ptr_of_expr body)))

  let mk_exists ( ctx : context ) ( sorts : sort array ) ( names : Symbol.symbol array ) ( body : expr ) ( weight : int option ) ( patterns : Pattern.pattern array ) ( nopatterns : expr array ) ( quantifier_id : Symbol.symbol option ) ( skolem_id : Symbol.symbol option ) =
    if (Array.length sorts) != (Array.length names) then
      raise (Z3native.Exception "Number of sorts does not match number of names")
    else if ((Array.length nopatterns) == 0 && quantifier_id == None && skolem_id == None) then
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier (context_gno ctx) false
				    (match weight with | None -> 1 | Some(x) -> x)
				    (Array.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.map f patterns))
				    (Array.length sorts) (let f x = (AST.ptr_of_ast (ast_of_sort x)) in (Array.map f sorts))
				    (let f x = (Symbol.gno x) in (Array.map f names))
				    (ptr_of_expr body)))
    else
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier_ex (context_gno ctx) false
				    (match weight with | None -> 1 | Some(x) -> x)
				    (match quantifier_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (match skolem_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (Array.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.map f patterns))
				    (Array.length nopatterns) (expr_aton nopatterns)
				    (Array.length sorts) (let f x = (AST.ptr_of_ast (ast_of_sort x)) in (Array.map f sorts))
				    (let f x = (Symbol.gno x) in (Array.map f names))
				    (ptr_of_expr body)))
	
  let mk_exists_const ( ctx : context ) ( bound_constants : expr array ) ( body : expr ) ( weight : int option ) ( patterns : Pattern.pattern array ) ( nopatterns : expr array ) ( quantifier_id : Symbol.symbol option ) ( skolem_id : Symbol.symbol option ) =
    if ((Array.length nopatterns) == 0 && quantifier_id == None && skolem_id == None) then
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier_const (context_gno ctx) false
				    (match weight with | None -> 1 | Some(x) -> x)
				    (Array.length bound_constants) (expr_aton bound_constants)
				    (Array.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.map f patterns))
				    (ptr_of_expr body)))
    else
      Quantifier(expr_of_ptr ctx (Z3native.mk_quantifier_const_ex (context_gno ctx) false
				    (match weight with | None -> 1 | Some(x) -> x)
				    (match quantifier_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (match skolem_id with | None -> null | Some(x) -> (Symbol.gno x))
				    (Array.length bound_constants) (expr_aton bound_constants)
				    (Array.length patterns) (let f x = (AST.ptr_of_ast (Pattern.ast_of_pattern x)) in (Array.map f patterns))
				    (Array.length nopatterns) (expr_aton nopatterns)
				    (ptr_of_expr body)))

  let mk_quantifier ( ctx : context ) ( universal : bool ) ( sorts : sort array ) ( names : Symbol.symbol array ) ( body : expr ) ( weight : int option ) ( patterns : Pattern.pattern array ) ( nopatterns : expr array ) ( quantifier_id : Symbol.symbol option ) ( skolem_id : Symbol.symbol option ) =
    if (universal) then
      (mk_forall ctx sorts names body weight patterns nopatterns quantifier_id skolem_id)
    else
      (mk_exists ctx sorts names body weight patterns nopatterns quantifier_id skolem_id)

  let mk_quantifier ( ctx : context ) ( universal : bool ) ( bound_constants : expr array ) ( body : expr ) ( weight : int option ) ( patterns : Pattern.pattern array ) ( nopatterns : expr array ) ( quantifier_id : Symbol.symbol option ) ( skolem_id : Symbol.symbol option ) =
    if (universal) then
      mk_forall_const ctx bound_constants body weight patterns nopatterns quantifier_id skolem_id
    else
      mk_exists_const ctx bound_constants body weight patterns nopatterns quantifier_id skolem_id
end


module Array_ = 
struct
  type array_sort = ArraySort of sort
  type array_expr = ArrayExpr of expr
  
  let array_expr_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
    let e = (expr_of_ptr ctx no) in
    ArrayExpr(e)

  let array_sort_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
    let s = (sort_of_ptr ctx no) in
    ArraySort(s)

  let sort_of_array_sort s = match s with ArraySort(x) -> x

  let array_sort_of_sort s = match s with Sort(a) ->
    if ((Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) (z3obj_gno a))) != Z3enums.ARRAY_SORT) then
      raise (Z3native.Exception "Invalid coercion")
    else
      ArraySort(s)

  let array_expr_of_expr e =
    match e with Expr(a) -> 
      let s = Z3native.get_sort (z3obj_gnc a) (z3obj_gno a) in
      let q = (Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) s)) in
      if (q != Z3enums.ARRAY_SORT) then
	raise (Z3native.Exception "Invalid coercion")
      else
	ArrayExpr(e)

  let expr_of_array_expr e = match e with ArrayExpr(x) -> x
      
  let sgc ( x : array_sort ) = match (x) with ArraySort(Sort(s)) -> (z3obj_gc s)
  let sgnc ( x : array_sort ) = match (x) with ArraySort(Sort(s)) -> (z3obj_gnc s)
  let sgno ( x : array_sort ) = match (x) with ArraySort(Sort(s)) -> (z3obj_gno s)

  let egc ( x : array_expr ) = match (x) with ArrayExpr(Expr(e)) -> (z3obj_gc e)
  let egnc ( x : array_expr ) = match (x) with ArrayExpr(Expr(e)) -> (z3obj_gnc e)
  let egno ( x : array_expr ) = match (x) with ArrayExpr(Expr(e)) -> (z3obj_gno e)

  let mk_sort ( ctx : context ) ( domain : sort ) ( range : sort ) =
    array_sort_of_ptr ctx (Z3native.mk_array_sort (context_gno ctx) (Sort.gno domain) (Sort.gno range))

  let is_store ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_STORE)
  let is_select ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SELECT)
  let is_constant_array ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_CONST_ARRAY)
  let is_default_array ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ARRAY_DEFAULT)
  let is_array_map ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ARRAY_MAP)
  let is_as_array ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_AS_ARRAY)       
  let is_array ( x : expr ) =
    (Z3native.is_app (nc_of_expr x) (ptr_of_expr x)) &&
      ((sort_kind_of_int (Z3native.get_sort_kind (nc_of_expr x) (Z3native.get_sort (nc_of_expr x) (ptr_of_expr x)))) == ARRAY_SORT)      

  let get_domain ( x : array_sort ) = Sort.sort_of_ptr (sgc x) (Z3native.get_array_sort_domain (sgnc x) (sgno x))
  let get_range ( x : array_sort ) = Sort.sort_of_ptr (sgc x) (Z3native.get_array_sort_range (sgnc x) (sgno x))

  let mk_const ( ctx : context ) ( name : Symbol.symbol ) ( domain : sort ) ( range : sort ) = 
    ArrayExpr(Expr.mk_const ctx name (match (mk_sort ctx domain range) with ArraySort(s) -> s))
      
  let mk_const_s ( ctx : context ) ( name : string ) ( domain : sort ) ( range : sort ) =	
    mk_const ctx (Symbol.mk_string ctx name) domain range
      
  let mk_select ( ctx : context ) ( a : array_expr ) ( i : expr ) =
    array_expr_of_ptr ctx (Z3native.mk_select (context_gno ctx) (egno a) (ptr_of_expr i))      

  let mk_store ( ctx : context ) ( a : array_expr ) ( i : expr ) ( v : expr ) =
    array_expr_of_ptr ctx (Z3native.mk_store (context_gno ctx) (egno a) (ptr_of_expr i) (ptr_of_expr v))

  let mk_const_array ( ctx : context ) ( domain : sort ) ( v : expr ) =
    array_expr_of_ptr ctx (Z3native.mk_const_array (context_gno ctx) (Sort.gno domain) (ptr_of_expr v))

  let mk_map ( ctx : context ) ( f : func_decl ) ( args : array_expr array ) =
    let m x = (ptr_of_expr (expr_of_array_expr x)) in    
    array_expr_of_ptr ctx (Z3native.mk_map (context_gno ctx) (FuncDecl.gno f) (Array.length args) (Array.map m args))

  let mk_term_array  ( ctx : context ) ( arg : array_expr ) =
    array_expr_of_ptr ctx (Z3native.mk_array_default (context_gno ctx) (egno arg))
end


module Set = 
struct     
  type set_sort = SetSort of sort

  let set_sort_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
    let s = (sort_of_ptr ctx no) in
    SetSort(s)

  let sort_of_set_sort s = match s with SetSort(x) -> x

  let mk_sort  ( ctx : context ) ( ty : sort ) =
    set_sort_of_ptr ctx (Z3native.mk_set_sort (context_gno ctx) (Sort.gno ty))

  let is_union ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_UNION)
  let is_intersect ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_INTERSECT)
  let is_difference ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_DIFFERENCE)
  let is_complement ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_COMPLEMENT)
  let is_subset ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_SUBSET)


  let mk_empty ( ctx : context ) ( domain : sort ) =
    (expr_of_ptr ctx (Z3native.mk_empty_set (context_gno ctx) (Sort.gno domain)))
      
  let mk_full ( ctx : context ) ( domain : sort ) =
    expr_of_ptr ctx (Z3native.mk_full_set (context_gno ctx) (Sort.gno domain))

  let mk_set_add  ( ctx : context ) ( set : expr ) ( element : expr ) =
    expr_of_ptr ctx (Z3native.mk_set_add (context_gno ctx) (ptr_of_expr set) (ptr_of_expr element))
      
  let mk_del  ( ctx : context ) ( set : expr ) ( element : expr ) =
    expr_of_ptr ctx (Z3native.mk_set_del (context_gno ctx) (ptr_of_expr set) (ptr_of_expr element))
      
  let mk_union  ( ctx : context ) ( args : expr array ) =
    expr_of_ptr ctx (Z3native.mk_set_union (context_gno ctx) (Array.length args) (expr_aton args))
      
  let mk_intersection  ( ctx : context ) ( args : expr array ) =
    expr_of_ptr ctx (Z3native.mk_set_intersect (context_gno ctx) (Array.length args) (expr_aton args))

  let mk_difference  ( ctx : context ) ( arg1 : expr ) ( arg2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_set_difference (context_gno ctx) (ptr_of_expr arg1) (ptr_of_expr arg2))

  let mk_complement  ( ctx : context ) ( arg : expr ) =
    expr_of_ptr ctx (Z3native.mk_set_complement (context_gno ctx) (ptr_of_expr arg))

  let mk_membership  ( ctx : context ) ( elem : expr ) ( set : expr ) =
    expr_of_ptr ctx (Z3native.mk_set_member (context_gno ctx) (ptr_of_expr elem) (ptr_of_expr set))

  let mk_subset  ( ctx : context ) ( arg1 : expr ) ( arg2 : expr ) =
    expr_of_ptr ctx (Z3native.mk_set_subset (context_gno ctx) (ptr_of_expr arg1) (ptr_of_expr arg2))

end


module FiniteDomain = 
struct  
  type finite_domain_sort = FiniteDomainSort of sort

  let sort_of_finite_domain_sort s = match s with FiniteDomainSort(x) -> x

  let finite_domain_sort_of_sort s = match s with Sort(a) ->
    if ((Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) (z3obj_gno a))) != Z3enums.FINITE_DOMAIN_SORT) then
      raise (Z3native.Exception "Invalid coercion")
    else
      FiniteDomainSort(s)

  let gc ( x : finite_domain_sort ) = match (x) with FiniteDomainSort(Sort(s)) -> (z3obj_gc s)
  let gnc ( x : finite_domain_sort ) = match (x) with FiniteDomainSort(Sort(s)) -> (z3obj_gnc s)
  let gno ( x : finite_domain_sort ) = match (x) with FiniteDomainSort(Sort(s))-> (z3obj_gno s)
    
  let mk_sort ( ctx : context ) ( name : Symbol.symbol ) ( size : int ) =
    let s = (sort_of_ptr ctx (Z3native.mk_finite_domain_sort (context_gno ctx) (Symbol.gno name) size)) in
    FiniteDomainSort(s)
      
  let mk_sort_s ( ctx : context ) ( name : string ) ( size : int ) =
    mk_sort ctx (Symbol.mk_string ctx name) size


  let is_finite_domain ( x : expr ) =
    let nc = (nc_of_expr x) in
    (Z3native.is_app (nc_of_expr x) (ptr_of_expr x)) &&
      (sort_kind_of_int (Z3native.get_sort_kind nc (Z3native.get_sort nc (ptr_of_expr x))) == FINITE_DOMAIN_SORT)

  let is_lt ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FD_LT)

  let get_size ( x : finite_domain_sort ) = 
    let (r, v) = (Z3native.get_finite_domain_sort_size (gnc x) (gno x)) in
    if r then v
    else raise (Z3native.Exception "Conversion failed.")
end


module Relation = 
struct
  type relation_sort = RelationSort of sort

  let sort_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
    let s = (sort_of_ptr ctx no) in
    RelationSort(s)           

  let sort_of_relation_sort s = match s with RelationSort(x) -> x

  let relation_sort_of_sort s = match s with Sort(a) ->
    if ((Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) (z3obj_gno a))) != Z3enums.RELATION_SORT) then
      raise (Z3native.Exception "Invalid coercion")
    else
      RelationSort(s)

  let gc ( x : relation_sort ) = match (x) with RelationSort(Sort(s)) -> (z3obj_gc s)
  let gnc ( x : relation_sort ) = match (x) with RelationSort(Sort(s)) -> (z3obj_gnc s)
  let gno ( x : relation_sort ) = match (x) with RelationSort(Sort(s))-> (z3obj_gno s)
    

  let is_relation ( x : expr ) =
    let nc = (nc_of_expr x) in
    ((Z3native.is_app (nc_of_expr x) (ptr_of_expr x)) &&
	(sort_kind_of_int (Z3native.get_sort_kind nc (Z3native.get_sort nc (ptr_of_expr x))) == RELATION_SORT))

  let is_store ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_STORE)
  let is_empty ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_EMPTY)
  let is_is_empty ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_IS_EMPTY)
  let is_join ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_JOIN)
  let is_union ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_UNION)
  let is_widen ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_WIDEN)
  let is_project ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_PROJECT)
  let is_filter ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_FILTER)
  let is_negation_filter ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_NEGATION_FILTER)
  let is_rename ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_RENAME)
  let is_complement ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_COMPLEMENT)
  let is_select ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_SELECT)
  let is_clone ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_CLONE)

  let get_arity ( x : relation_sort ) = Z3native.get_relation_arity (gnc x) (gno x)

  let get_column_sorts ( x : relation_sort ) = 
    let n = get_arity x in
    let f i = (sort_of_ptr (gc x) (Z3native.get_relation_column (gnc x) (gno x) i)) in
    Array.init n f

end
  

module Datatype = 
struct
  type datatype_sort = DatatypeSort of sort
  type datatype_expr = DatatypeExpr of expr
    
  let sort_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
    let s = (sort_of_ptr ctx no) in
    DatatypeSort(s)

  let sort_of_datatype_sort s = match s with DatatypeSort(x) -> x

  let datatype_sort_of_sort s = match s with Sort(a) ->
    if ((Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) (z3obj_gno a))) != Z3enums.DATATYPE_SORT) then
      raise (Z3native.Exception "Invalid coercion")
    else
      DatatypeSort(s)

  let datatype_expr_of_expr e =
    match e with Expr(a) -> 
      let s = Z3native.get_sort (z3obj_gnc a) (z3obj_gno a) in
      let q = (Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) s)) in
      if (q != Z3enums.DATATYPE_SORT) then
	raise (Z3native.Exception "Invalid coercion")
      else
	DatatypeExpr(e)

  let expr_of_datatype_expr e = match e with DatatypeExpr(x) -> x

  let sgc ( x : datatype_sort ) = match (x) with DatatypeSort(Sort(s)) -> (z3obj_gc s)
  let sgnc ( x : datatype_sort ) = match (x) with DatatypeSort(Sort(s)) -> (z3obj_gnc s)
  let sgno ( x : datatype_sort ) = match (x) with DatatypeSort(Sort(s))-> (z3obj_gno s)
    
  module Constructor = 
  struct
    type constructor = z3_native_object

    let create ( ctx : context ) ( name : Symbol.symbol ) ( recognizer : Symbol.symbol ) ( field_names : Symbol.symbol array ) ( sorts : sort array ) ( sort_refs : int array ) =
      let n = (Array.length field_names) in
      if n != (Array.length sorts) then
	raise (Z3native.Exception "Number of field names does not match number of sorts")
      else
	if n != (Array.length sort_refs) then
	  raise (Z3native.Exception "Number of field names does not match number of sort refs")
	else
          let ptr = (Z3native.mk_constructor (context_gno ctx) (Symbol.gno name) 
		       (Symbol.gno recognizer) 
		       n
		       (let f x = (Symbol.gno x) in (Array.map f field_names))
		       (let f x = (AST.ptr_of_ast (ast_of_sort x)) in  (Array.map f sorts))
		       sort_refs) in	  
	  let no : constructor = { m_ctx = ctx ;
				   m_n_obj = null ;
				   inc_ref = z3obj_nil_ref ;
				   dec_ref = z3obj_nil_ref} in
	  (z3obj_sno no ctx ptr) ;
	  (z3obj_create no) ;
	  let f = fun o -> Z3native.del_constructor (z3obj_gnc o) (z3obj_gno o) in
	  Gc.finalise f no ;
	  no    	  
	
    let get_num_fields ( x : constructor ) = Z3native.get_arity (z3obj_gnc x) (z3obj_gno x)

    let get_constructor_decl ( x : constructor ) = 
      let (a, _, _) = (Z3native.query_constructor (z3obj_gnc x) (z3obj_gno x) (get_num_fields x)) in
      func_decl_of_ptr (z3obj_gc x) a

    let get_tester_decl ( x : constructor ) =
      let (_, b, _) = (Z3native.query_constructor (z3obj_gnc x) (z3obj_gno x) (get_num_fields x)) in
      func_decl_of_ptr (z3obj_gc x) b	

    let get_accessor_decls ( x : constructor ) = 
      let (_, _, c) = (Z3native.query_constructor (z3obj_gnc x) (z3obj_gno x) (get_num_fields x)) in
      let f y = func_decl_of_ptr (z3obj_gc x) y in
      Array.map f c
	
  end

  module ConstructorList =
  struct
    type constructor_list = z3_native_object 

    let create ( ctx : context ) ( c : Constructor.constructor array ) =
      let res : constructor_list = { m_ctx = ctx ;
				     m_n_obj = null ;
				     inc_ref = z3obj_nil_ref ;
				     dec_ref = z3obj_nil_ref} in
      let f x =(z3obj_gno x) in 
      (z3obj_sno res ctx (Z3native.mk_constructor_list (context_gno ctx) (Array.length c) (Array.map f c))) ;
      (z3obj_create res) ;
      let f = fun o -> Z3native.del_constructor_list (z3obj_gnc o) (z3obj_gno o) in      
      Gc.finalise f res;
      res       
  end
    
  let mk_constructor ( ctx : context ) ( name : Symbol.symbol ) ( recognizer : Symbol.symbol ) ( field_names : Symbol.symbol array ) ( sorts : sort array ) ( sort_refs : int array ) =
    Constructor.create ctx name recognizer field_names sorts sort_refs


  let mk_constructor_s ( ctx : context ) ( name : string ) ( recognizer : Symbol.symbol ) ( field_names : Symbol.symbol array ) ( sorts : sort array ) ( sort_refs : int array ) =
    mk_constructor ctx (Symbol.mk_string ctx name) recognizer field_names sorts sort_refs

  let mk_sort ( ctx : context ) ( name : Symbol.symbol ) ( constructors : Constructor.constructor array ) =
    let f x = (z3obj_gno x) in 
    let (x,_) = (Z3native.mk_datatype (context_gno ctx) (Symbol.gno name) (Array.length constructors) (Array.map f constructors)) in
    sort_of_ptr ctx x

  let mk_sort_s ( ctx : context ) ( name : string ) ( constructors : Constructor.constructor array ) =
    mk_sort ctx (Symbol.mk_string ctx name) constructors
      
  let mk_sorts ( ctx : context ) ( names : Symbol.symbol array ) ( c : Constructor.constructor array array ) =
    let n = (Array.length names) in
    let f e = (AST.ptr_of_ast (ConstructorList.create ctx e)) in
    let cla = (Array.map f c) in
    let f2 x = (Symbol.gno x) in
    let (r, a) = (Z3native.mk_datatypes (context_gno ctx) n (Array.map f2 names) cla) in
    let g e = (sort_of_ptr ctx e) in
    (Array.map g r)

  let mk_sorts_s ( ctx : context ) ( names : string array ) ( c : Constructor.constructor array array ) =
    mk_sorts ctx 
      ( 
	let f e = (Symbol.mk_string ctx e) in
	Array.map f names 
      )
      c

  let get_num_constructors ( x : datatype_sort ) = Z3native.get_datatype_sort_num_constructors (sgnc x) (sgno x)

  let get_constructors ( x : datatype_sort ) = 
    let n = (get_num_constructors x) in
    let f i = func_decl_of_ptr (sgc x) (Z3native.get_datatype_sort_constructor (sgnc x) (sgno x) i) in
    Array.init n f

  let get_recognizers ( x : datatype_sort ) = 
    let n = (get_num_constructors x) in
    let f i = func_decl_of_ptr (sgc x) (Z3native.get_datatype_sort_recognizer (sgnc x) (sgno x) i) in
    Array.init n f
      
  let get_accessors ( x : datatype_sort ) =
    let n = (get_num_constructors x) in
    let f i = (
      let fd = func_decl_of_ptr (sgc x) (Z3native.get_datatype_sort_constructor (sgnc x) (sgno x) i) in
      let ds = Z3native.get_domain_size (FuncDecl.gnc fd) (FuncDecl.gno fd) in
      let g j = func_decl_of_ptr (sgc x) (Z3native.get_datatype_sort_constructor_accessor (sgnc x) (sgno x) i j) in
      Array.init ds g
    ) in
    Array.init n f
end


module Enumeration = 
struct 
  type enum_sort = EnumSort of sort
    
  let sort_of_ptr ( ctx : context ) ( no : Z3native.ptr ) ( cdecls : Z3native.z3_func_decl array ) ( tdecls : Z3native.z3_func_decl array ) =
    let s = (sort_of_ptr ctx no) in
    let res = EnumSort(s) in
    res

  let sort_of_enum_sort s = match s with EnumSort(x) -> x

  let sgc ( x : enum_sort ) = match (x) with EnumSort(Sort(s)) -> (z3obj_gc s)
  let sgnc ( x : enum_sort ) = match (x) with EnumSort(Sort(s)) -> (z3obj_gnc s)
  let sgno ( x : enum_sort ) = match (x) with EnumSort(Sort(s))-> (z3obj_gno s)  

  let mk_sort ( ctx : context ) ( name : Symbol.symbol ) ( enum_names : Symbol.symbol array ) =
    let f x = Symbol.gno x in
    let (a, b, c) = (Z3native.mk_enumeration_sort (context_gno ctx) (Symbol.gno name) (Array.length enum_names) (Array.map f enum_names)) in
    sort_of_ptr ctx a b c

  let mk_sort_s ( ctx : context ) ( name : string ) ( enum_names : string array ) =
    mk_sort ctx (Symbol.mk_string ctx name) (Symbol.mk_strings ctx enum_names)

  let get_const_decls ( x : enum_sort ) =
    let n = Z3native.get_datatype_sort_num_constructors (sgnc x) (sgno x)  in
    let f i = (func_decl_of_ptr (sgc x) (Z3native.get_datatype_sort_constructor (sgnc x) (sgno x)  i)) in
    Array.init n f

  let get_tester_decls ( x : enum_sort ) = 
    let n = Z3native.get_datatype_sort_num_constructors (sgnc x) (sgno x)  in
    let f i = (func_decl_of_ptr (sgc x) (Z3native.get_datatype_sort_recognizer (sgnc x) (sgno x)  i)) in
    Array.init n f
      
end


module List_ = 
struct
  type list_sort = ListSort of sort
    
  let sort_of_ptr ( ctx : context ) ( no : Z3native.ptr ) ( nildecl : Z3native.ptr ) ( is_nildecl : Z3native.ptr ) ( consdecl : Z3native.ptr ) ( is_consdecl : Z3native.ptr ) ( headdecl : Z3native.ptr ) ( taildecl : Z3native.ptr ) =
    let s = (sort_of_ptr ctx no) in
    let res = ListSort(s) in
    res

  let sort_of_list_sort s = match s with ListSort(x) -> x
      
  let sgc ( x : list_sort ) = match (x) with ListSort(Sort(s)) -> (z3obj_gc s)
  let sgnc ( x : list_sort ) = match (x) with ListSort(Sort(s)) -> (z3obj_gnc s)
  let sgno ( x : list_sort ) = match (x) with ListSort(Sort(s))-> (z3obj_gno s)
      
  let mk_sort ( ctx : context ) ( name : Symbol.symbol ) ( elem_sort : sort ) =
    let (r, a, b, c, d, e, f) = (Z3native.mk_list_sort (context_gno ctx) (Symbol.gno name) (Sort.gno elem_sort)) in
    sort_of_ptr ctx r a b c d e f
      
  let mk_list_s ( ctx : context ) (name : string) elem_sort =
    mk_sort ctx (Symbol.mk_string ctx name) elem_sort

  let get_nil_decl ( x : list_sort ) = 
    func_decl_of_ptr (sgc x) (Z3native.get_datatype_sort_constructor (sgnc x) (sgno x)  0)

  let get_is_nil_decl ( x : list_sort ) = 
    func_decl_of_ptr (sgc x) (Z3native.get_datatype_sort_recognizer (sgnc x) (sgno x)  0)

  let get_cons_decl ( x : list_sort ) = 
    func_decl_of_ptr (sgc x) (Z3native.get_datatype_sort_constructor (sgnc x) (sgno x)  1)

  let get_is_cons_decl ( x : list_sort ) =
    func_decl_of_ptr (sgc x) (Z3native.get_datatype_sort_recognizer (sgnc x) (sgno x)  1)

  let get_head_decl ( x : list_sort )  = 
    func_decl_of_ptr (sgc x) (Z3native.get_datatype_sort_constructor_accessor (sgnc x) (sgno x) 1 0)

  let get_tail_decl ( x : list_sort ) =
    func_decl_of_ptr (sgc x) (Z3native.get_datatype_sort_constructor_accessor (sgnc x) (sgno x) 1 1)

  let nil ( x : list_sort ) = expr_of_func_app (sgc x) (get_nil_decl x) [||]
end


module Tuple = 
struct
  type tuple_sort = TupleSort of sort

  let sort_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
    let s = (sort_of_ptr ctx no) in    
    TupleSort(s)

  let sort_of_tuple_sort s = match s with TupleSort(x) -> x

  let sgc ( x : tuple_sort ) = match (x) with TupleSort(Sort(s)) -> (z3obj_gc s)
  let sgnc ( x : tuple_sort ) = match (x) with TupleSort(Sort(s)) -> (z3obj_gnc s)
  let sgno ( x : tuple_sort ) = match (x) with TupleSort(Sort(s))-> (z3obj_gno s)
    
  let mk_sort ( ctx : context ) ( name : Symbol.symbol ) ( field_names : Symbol.symbol array ) ( field_sorts : sort array ) =
    let f x = Symbol.gno x in 
    let f2 x = ptr_of_ast (ast_of_sort x) in 
    let (r, _, _) = (Z3native.mk_tuple_sort (context_gno ctx) (Symbol.gno name) (Array.length field_names) (Array.map f field_names) (Array.map f2 field_sorts)) in 
    sort_of_ptr ctx r

  let get_mk_decl ( x : tuple_sort ) =
    func_decl_of_ptr (sgc x) (Z3native.get_tuple_sort_mk_decl (sgnc x) (sgno x))

  let get_num_fields ( x : tuple_sort ) = Z3native.get_tuple_sort_num_fields (sgnc x) (sgno x)
    
  let get_field_decls ( x : tuple_sort ) = 
    let n = get_num_fields x in
    let f i = func_decl_of_ptr (sgc x) (Z3native.get_tuple_sort_field_decl (sgnc x) (sgno x) i) in
    Array.init n f
end


module rec Arithmetic :
sig
  type arith_sort = ArithSort of Sort.sort
  type arith_expr = ArithExpr of Expr.expr
      
  val sort_of_arith_sort : arith_sort -> Sort.sort
  val arith_sort_of_sort : Sort.sort -> arith_sort
  val expr_of_arith_expr : arith_expr -> Expr.expr
  val arith_expr_of_expr : Expr.expr -> arith_expr

  module rec Integer :
  sig
    type int_sort = IntSort of arith_sort
    type int_expr = IntExpr of arith_expr
    type int_num = IntNum of int_expr

    val int_expr_of_ptr : context -> Z3native.ptr -> int_expr
    val int_num_of_ptr : context -> Z3native.ptr -> int_num

    val arith_sort_of_int_sort : Integer.int_sort -> arith_sort
    val int_sort_of_arith_sort : arith_sort -> int_sort
    val arith_expr_of_int_expr : int_expr -> arith_expr
    val int_expr_of_int_num : int_num -> int_expr
    val int_expr_of_arith_expr : arith_expr -> int_expr
    val int_num_of_int_expr : int_expr -> int_num
      
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

    val real_expr_of_ptr : context -> Z3native.ptr -> real_expr
    val rat_num_of_ptr : context -> Z3native.ptr -> rat_num

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

    val arith_expr_of_algebraic_num : algebraic_num -> arith_expr
    val algebraic_num_of_arith_expr : arith_expr -> algebraic_num
    
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
end = struct
  type arith_sort = ArithSort of sort
  type arith_expr = ArithExpr of expr

  let arith_expr_of_expr e =
    match e with Expr(a) -> 
      let s = Z3native.get_sort (z3obj_gnc a) (z3obj_gno a) in
      let q = (Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) s)) in
      if (q != Z3enums.INT_SORT && q != Z3enums.REAL_SORT) then
	raise (Z3native.Exception "Invalid coercion")
      else
	ArithExpr(e)

  let arith_expr_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
    arith_expr_of_expr (expr_of_ptr ctx no)      

  let sort_of_arith_sort s = match s with ArithSort(x) -> x
  let expr_of_arith_expr e = match e with ArithExpr(x) -> x  

  let arith_sort_of_sort s = match s with Sort(a) ->
    let q = (Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) (z3obj_gno a))) in
    if (q != Z3enums.INT_SORT && q != Z3enums.REAL_SORT) then
      raise (Z3native.Exception "Invalid coercion")
    else
      ArithSort(s)

  let arith_sort_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
    arith_sort_of_sort (sort_of_ptr ctx no)

  let sgc ( x : arith_sort ) = match (x) with ArithSort(Sort(s)) -> (z3obj_gc s)
  let sgnc ( x : arith_sort ) = match (x) with ArithSort(Sort(s)) -> (z3obj_gnc s)
  let sgno ( x : arith_sort ) = match (x) with ArithSort(Sort(s)) -> (z3obj_gno s)
  let egc ( x : arith_expr ) = match (x) with ArithExpr(e) -> (c_of_expr e)
  let egnc ( x : arith_expr ) = match (x) with ArithExpr(e) -> (nc_of_expr e)
  let egno ( x : arith_expr ) = match (x) with ArithExpr(e) -> (ptr_of_expr e)

  module rec Integer :
  sig
    type int_sort = IntSort of arith_sort
    type int_expr = IntExpr of arith_expr
    type int_num = IntNum of int_expr

    val int_expr_of_ptr : context -> Z3native.ptr -> int_expr
    val int_num_of_ptr : context -> Z3native.ptr -> int_num

    val arith_sort_of_int_sort : Integer.int_sort -> arith_sort
    val int_sort_of_arith_sort : arith_sort -> int_sort
    val arith_expr_of_int_expr : int_expr -> arith_expr
    val int_expr_of_int_num : int_num -> int_expr
    val int_expr_of_arith_expr : arith_expr -> int_expr
    val int_num_of_int_expr : int_expr -> int_num
      
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
  end = struct     
    type int_sort = IntSort of arith_sort    
    type int_expr = IntExpr of arith_expr
    type int_num = IntNum of int_expr
	
    let int_expr_of_arith_expr e =
      match e with ArithExpr(Expr(a)) -> 
	let s = Z3native.get_sort (z3obj_gnc a) (z3obj_gno a) in
	let q = (Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) s)) in
	if (q != Z3enums.INT_SORT) then
	  raise (Z3native.Exception "Invalid coercion")
	else
	  IntExpr(e)

    let int_expr_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
      int_expr_of_arith_expr (arith_expr_of_expr (Expr.expr_of_ptr ctx no))
	    
    let int_num_of_int_expr e =
      match e with IntExpr(ArithExpr(Expr(a))) -> 
	if (not (Z3native.is_numeral_ast (z3obj_gnc a) (z3obj_gno a))) then
	  raise (Z3native.Exception "Invalid coercion")
	else
	  IntNum(e)

    let int_num_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
      int_num_of_int_expr (int_expr_of_ptr ctx no)      
	    
    let arith_sort_of_int_sort s = match s with IntSort(x) -> x
    let arith_expr_of_int_expr e = match e with IntExpr(x) -> x
    let int_expr_of_int_num e = match e with IntNum(x) -> x 

    let int_sort_of_arith_sort s = match s with ArithSort(Sort(a)) ->
      if ((Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) (z3obj_gno a))) != Z3enums.INT_SORT) then
	raise (Z3native.Exception "Invalid coercion")
      else
	IntSort(s)	 

    let int_sort_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
      int_sort_of_arith_sort (arith_sort_of_sort (Sort.sort_of_ptr ctx no)) 	

    let sgc ( x : int_sort ) = match (x) with IntSort(s) -> (sgc s)
    let sgnc ( x : int_sort ) = match (x) with IntSort(s) -> (sgnc s)
    let sgno ( x : int_sort ) = match (x) with IntSort(s) -> (sgno s)      
    let egc ( x : int_expr ) = match (x) with IntExpr(e) -> (egc e)
    let egnc ( x : int_expr ) = match (x) with IntExpr(e) -> (egnc e)
    let egno ( x : int_expr ) = match (x) with IntExpr(e) -> (egno e)
    let ngc ( x : int_num ) = match (x) with IntNum(e) -> (egc e)
    let ngnc ( x : int_num ) = match (x) with IntNum(e) -> (egnc e)
    let ngno ( x : int_num ) = match (x) with IntNum(e) -> (egno e)      
      
    let mk_sort ( ctx : context ) =
      int_sort_of_ptr ctx (Z3native.mk_int_sort (context_gno ctx))

    let get_int ( x : int_num ) = 
      let (r, v) = Z3native.get_numeral_int (ngnc x) (ngno x) in
      if r then v
      else raise (Z3native.Exception "Conversion failed.")
	
    let to_string ( x : int_num ) = Z3native.get_numeral_string (ngnc x) (ngno x)

    let mk_int_const ( ctx : context ) ( name : Symbol.symbol ) =
      IntExpr(ArithExpr(Expr.mk_const ctx name (match (mk_sort ctx) with IntSort(ArithSort(s)) -> s)))
	
    let mk_int_const_s ( ctx : context ) ( name : string )  =
      mk_int_const ctx (Symbol.mk_string ctx name)
	
    let mk_mod ( ctx : context ) ( t1 : int_expr ) ( t2 : int_expr ) =    
      int_expr_of_ptr ctx (Z3native.mk_mod (context_gno ctx) (egno t1) (egno t2))
	
    let mk_rem ( ctx : context ) ( t1 : int_expr ) ( t2 : int_expr ) =
      int_expr_of_ptr  ctx (Z3native.mk_rem (context_gno ctx) (egno t1) (egno t2))

    let mk_int_numeral_s ( ctx : context ) ( v : string ) =
      int_num_of_ptr ctx (Z3native.mk_numeral (context_gno ctx) v (sgno (mk_sort ctx)))
	
    let mk_int_numeral_i ( ctx : context ) ( v : int ) =
      int_num_of_ptr ctx (Z3native.mk_int (context_gno ctx) v (sgno (mk_sort ctx)))

    let mk_int2real ( ctx : context ) ( t : int_expr ) =
      Real.real_expr_of_arith_expr (arith_expr_of_expr (Expr.expr_of_ptr ctx (Z3native.mk_int2real (context_gno ctx) (egno t))))

    let mk_int2bv ( ctx : context ) ( n : int ) ( t : int_expr ) =
      BitVector.bitvec_expr_of_expr (Expr.expr_of_ptr ctx (Z3native.mk_int2bv (context_gno ctx) n (egno t)))
  end

  and Real :
  sig 
    type real_sort = RealSort of arith_sort
    type real_expr = RealExpr of arith_expr
    type rat_num = RatNum of real_expr

    val real_expr_of_ptr : context -> Z3native.ptr -> real_expr
    val rat_num_of_ptr : context -> Z3native.ptr -> rat_num

    val arith_sort_of_real_sort : real_sort -> arith_sort
    val real_sort_of_arith_sort : arith_sort -> real_sort
    val arith_expr_of_real_expr : real_expr -> arith_expr
    val real_expr_of_rat_num : rat_num -> real_expr
    val real_expr_of_arith_expr : arith_expr -> real_expr
    val rat_num_of_real_expr : real_expr -> rat_num      

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
  end = struct  
    type real_sort = RealSort of arith_sort      
    type real_expr = RealExpr of arith_expr
    type rat_num = RatNum of real_expr
	
    let arith_sort_of_real_sort s = match s with RealSort(x) -> x
    let arith_expr_of_real_expr e = match e with RealExpr(x) -> x
    let real_expr_of_rat_num e = match e with RatNum(x) -> x

    let real_expr_of_arith_expr e =
      match e with ArithExpr(Expr(a)) -> 
	let s = Z3native.get_sort (z3obj_gnc a) (z3obj_gno a) in
	let q = (Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) s)) in
	if (q != Z3enums.REAL_SORT) then
	  raise (Z3native.Exception "Invalid coercion")
	else
	  RealExpr(e)

    let real_expr_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
      real_expr_of_arith_expr (arith_expr_of_expr (Expr.expr_of_ptr ctx no))
	    
    let rat_num_of_real_expr e =
      match e with RealExpr(ArithExpr(Expr(a))) -> 
	if (not (Z3native.is_numeral_ast (z3obj_gnc a) (z3obj_gno a))) then
	  raise (Z3native.Exception "Invalid coercion")
	else
	  RatNum(e)

    let rat_num_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
      rat_num_of_real_expr (real_expr_of_ptr ctx no)       
	    
    let real_sort_of_arith_sort s = match s with ArithSort(Sort(a)) ->
      if ((Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) (z3obj_gno a))) != Z3enums.REAL_SORT) then
	raise (Z3native.Exception "Invalid coercion")
      else
	RealSort(s)

    let real_sort_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
      real_sort_of_arith_sort (arith_sort_of_sort (sort_of_ptr ctx no)) 	
	
    let sgc ( x : real_sort ) = match (x) with RealSort(s) -> (sgc s)
    let sgnc ( x : real_sort ) = match (x) with RealSort(s) -> (sgnc s)
    let sgno ( x : real_sort ) = match (x) with RealSort(s) -> (sgno s)
    let egc ( x : real_expr ) = match (x) with RealExpr(e) -> (egc e)
    let egnc ( x : real_expr ) = match (x) with RealExpr(e) -> (egnc e)
    let egno ( x : real_expr ) = match (x) with RealExpr(e) -> (egno e)
    let ngc ( x : rat_num ) = match (x) with RatNum(e) -> (egc e)
    let ngnc ( x : rat_num ) = match (x) with RatNum(e) -> (egnc e)
    let ngno ( x : rat_num ) = match (x) with RatNum(e) -> (egno e)
      
      
    let mk_sort ( ctx : context ) =
      real_sort_of_ptr ctx (Z3native.mk_real_sort (context_gno ctx))	

    let get_numerator ( x : rat_num ) =
      Integer.int_num_of_ptr (ngc x) (Z3native.get_numerator (ngnc x) (ngno x))
	
    let get_denominator ( x : rat_num ) =
      Integer.int_num_of_ptr (ngc x) (Z3native.get_denominator (ngnc x) (ngno x))
	
    let to_decimal_string ( x : rat_num ) ( precision : int ) = 
      Z3native.get_numeral_decimal_string (ngnc x) (ngno x) precision
	
    let to_string ( x : rat_num ) = Z3native.get_numeral_string (ngnc x) (ngno x)

    let mk_real_const ( ctx : context ) ( name : Symbol.symbol )  =
      RealExpr(ArithExpr(Expr.mk_const ctx name (match (mk_sort ctx) with RealSort(ArithSort(s)) -> s)))
	
    let mk_real_const_s ( ctx : context ) ( name : string )  =
      mk_real_const ctx (Symbol.mk_string ctx name)

    let mk_numeral_nd ( ctx : context ) ( num : int ) ( den : int) =
      if (den == 0) then 
	raise (Z3native.Exception "Denominator is zero")
      else      
	rat_num_of_ptr ctx (Z3native.mk_real (context_gno ctx) num den)
	  
    let mk_numeral_s ( ctx : context ) ( v : string ) =
      rat_num_of_ptr ctx (Z3native.mk_numeral (context_gno ctx) v (sgno (mk_sort ctx)))
	
    let mk_numeral_i ( ctx : context ) ( v : int ) =
      rat_num_of_ptr ctx (Z3native.mk_int (context_gno ctx) v (sgno (mk_sort ctx)))
	
    let mk_is_integer ( ctx : context ) ( t : real_expr ) =
      Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_is_int (context_gno ctx) (egno t)))
	
    let mk_real2int ( ctx : context ) ( t : real_expr ) =
      Integer.int_expr_of_arith_expr (arith_expr_of_expr (expr_of_ptr ctx (Z3native.mk_real2int (context_gno ctx) (egno t))))
  end

  and AlgebraicNumber :
  sig
    type algebraic_num = AlgebraicNum of arith_expr

    val arith_expr_of_algebraic_num : algebraic_num -> arith_expr
    val algebraic_num_of_arith_expr : arith_expr -> algebraic_num
    
    val to_upper : algebraic_num -> int -> Real.rat_num
    val to_lower : algebraic_num -> int -> Real.rat_num
    val to_decimal_string : algebraic_num -> int -> string
    val to_string : algebraic_num -> string
  end = struct    
    type algebraic_num = AlgebraicNum of arith_expr

    let arith_expr_of_algebraic_num e = match e with AlgebraicNum(x) -> x

    let algebraic_num_of_arith_expr e =
      match e with ArithExpr(Expr(a)) -> 
	if (not (Z3native.is_algebraic_number (z3obj_gnc a) (z3obj_gno a))) then
	  raise (Z3native.Exception "Invalid coercion")
	else
	  AlgebraicNum(e)

    let algebraic_num_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
      algebraic_num_of_arith_expr (arith_expr_of_expr (expr_of_ptr ctx no))
	    
    let ngc ( x : algebraic_num ) = match (x) with AlgebraicNum(e) -> (egc e)
    let ngnc ( x : algebraic_num ) = match (x) with AlgebraicNum(e) -> (egnc e)
    let ngno ( x : algebraic_num ) = match (x) with AlgebraicNum(e) -> (egno e)
      

    let to_upper ( x : algebraic_num ) ( precision : int ) =
      Real.rat_num_of_ptr (ngc x) (Z3native.get_algebraic_number_upper (ngnc x) (ngno x) precision)
	
    let to_lower ( x : algebraic_num ) precision =
      Real.rat_num_of_ptr (ngc x) (Z3native.get_algebraic_number_lower (ngnc x) (ngno x) precision)
	
    let to_decimal_string ( x : algebraic_num ) ( precision : int ) = 
      Z3native.get_numeral_decimal_string (ngnc x) (ngno x) precision	

    let to_string ( x : algebraic_num ) = Z3native.get_numeral_string (ngnc x) (ngno x)      
  end

  let is_int ( x : expr ) =
    (Z3native.is_numeral_ast (nc_of_expr x) (nc_of_expr x)) &&
      ((sort_kind_of_int (Z3native.get_sort_kind (nc_of_expr x) (Z3native.get_sort (nc_of_expr x) (nc_of_expr x)))) == INT_SORT)
      
  let is_arithmetic_numeral ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ANUM)

  let is_le ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_LE)

  let is_ge ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_GE)

  let is_lt ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_LT)

  let is_gt ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_GT)

  let is_add ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ADD)

  let is_sub ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SUB)

  let is_uminus ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_UMINUS)

  let is_mul ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_MUL)

  let is_div ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_DIV)

  let is_idiv ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_IDIV)

  let is_remainder ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_REM)

  let is_modulus ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_MOD)

  let is_inttoreal ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_TO_REAL)

  let is_real_to_int ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_TO_INT)

  let is_real_is_int ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_IS_INT)

  let is_real ( x : expr ) =
    ((sort_kind_of_int (Z3native.get_sort_kind (nc_of_expr x) (Z3native.get_sort (nc_of_expr x) (nc_of_expr x)))) == REAL_SORT)
  let is_int_numeral ( x : expr ) = (Expr.is_numeral x) && (is_int x)

  let is_rat_num ( x : expr ) = (Expr.is_numeral x) && (is_real x)
    
  let is_algebraic_number ( x : expr ) = Z3native.is_algebraic_number (nc_of_expr x) (nc_of_expr x)

  let mk_add ( ctx : context ) ( t : arith_expr array ) =
    let f x = (ptr_of_expr (expr_of_arith_expr x)) in
    arith_expr_of_expr (expr_of_ptr ctx (Z3native.mk_add (context_gno ctx) (Array.length t) (Array.map f t)))

  let mk_mul ( ctx : context ) ( t : arith_expr array ) =
    let f x = (ptr_of_expr (expr_of_arith_expr x)) in
    arith_expr_of_expr (expr_of_ptr ctx (Z3native.mk_mul (context_gno ctx) (Array.length t) (Array.map f t)))

  let mk_sub ( ctx : context ) ( t : arith_expr array ) =
    let f x = (ptr_of_expr (expr_of_arith_expr x)) in
    arith_expr_of_expr (expr_of_ptr ctx (Z3native.mk_sub (context_gno ctx) (Array.length t) (Array.map f t)))
      
  let mk_unary_minus ( ctx : context ) ( t : arith_expr ) =     
    arith_expr_of_expr (expr_of_ptr ctx (Z3native.mk_unary_minus (context_gno ctx) (egno t)))

  let mk_div ( ctx : context ) ( t1 : arith_expr ) ( t2 : arith_expr ) =
    arith_expr_of_expr (expr_of_ptr ctx (Z3native.mk_div (context_gno ctx) (egno t1) (egno t2)))

  let mk_power ( ctx : context ) ( t1 : arith_expr ) ( t2 : arith_expr ) =     
    arith_expr_of_expr (expr_of_ptr ctx (Z3native.mk_power (context_gno ctx) (egno t1) (egno t2)))

  let mk_lt ( ctx : context ) ( t1 : arith_expr ) ( t2 : arith_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_lt (context_gno ctx) (egno t1) (egno t2)))

  let mk_le ( ctx : context ) ( t1 : arith_expr ) ( t2 : arith_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_le (context_gno ctx) (egno t1) (egno t2)))
      
  let mk_gt ( ctx : context ) ( t1 : arith_expr ) ( t2 : arith_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_gt (context_gno ctx) (egno t1) (egno t2)))

  let mk_ge ( ctx : context ) ( t1 : arith_expr ) ( t2 : arith_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_ge (context_gno ctx) (egno t1) (egno t2)))
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
  val mk_rotate_left : context -> int -> bitvec_expr -> bitvec_expr
  val mk_rotate_right : context -> int -> bitvec_expr -> bitvec_expr
  val mk_ext_rotate_left : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
  val mk_ext_rotate_right : context -> bitvec_expr -> bitvec_expr -> bitvec_expr
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
end = struct  
  type bitvec_sort = BitVecSort of sort
  type bitvec_expr = BitVecExpr of expr
  type bitvec_num = BitVecNum of bitvec_expr

  let sort_of_bitvec_sort s = match s with BitVecSort(x) -> x

  let bitvec_sort_of_sort s = match s with Sort(a) ->
    if ((Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) (z3obj_gno a))) != Z3enums.BV_SORT) then
      raise (Z3native.Exception "Invalid coercion")
    else
      BitVecSort(s)

  let bitvec_sort_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
    bitvec_sort_of_sort (sort_of_ptr ctx no)

  let bitvec_expr_of_expr e =
    match e with Expr(a) -> 
      let s = Z3native.get_sort (z3obj_gnc a) (z3obj_gno a) in
      let q = (Z3enums.sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc a) s)) in
      if (q != Z3enums.BV_SORT) then
	raise (Z3native.Exception "Invalid coercion")
      else
	BitVecExpr(e)

  let bitvec_expr_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
    bitvec_expr_of_expr (expr_of_ptr ctx no)

  let bitvec_num_of_bitvec_expr e =
    match e with BitVecExpr(Expr(a)) -> 
      if (not (Z3native.is_numeral_ast (z3obj_gnc a) (z3obj_gno a))) then
	raise (Z3native.Exception "Invalid coercion")
      else
	BitVecNum(e)

  let bitvec_num_of_ptr ( ctx : context ) ( no : Z3native.ptr ) =
    bitvec_num_of_bitvec_expr (bitvec_expr_of_expr (expr_of_ptr ctx no))

  let expr_of_bitvec_expr e = match e with BitVecExpr(x) -> x
  let bitvec_expr_of_bitvec_num e = match e with BitVecNum(x) -> x


  let sgc ( x : bitvec_sort ) = match (x) with BitVecSort(s) -> (Sort.gc s)
  let sgnc ( x : bitvec_sort ) = match (x) with BitVecSort(s) -> (Sort.gnc s)
  let sgno ( x : bitvec_sort ) = match (x) with BitVecSort(s) -> (Sort.gno s)
  let egc ( x : bitvec_expr ) = match (x) with BitVecExpr(e) -> (c_of_expr e)
  let egnc ( x : bitvec_expr ) = match (x) with BitVecExpr(e) -> (nc_of_expr e)
  let egno ( x : bitvec_expr ) = match (x) with BitVecExpr(e) -> (ptr_of_expr e)
  let ngc ( x : bitvec_num ) = match (x) with BitVecNum(e) -> (egc e)
  let ngnc ( x : bitvec_num ) = match (x) with BitVecNum(e) -> (egnc e)
  let ngno ( x : bitvec_num ) = match (x) with BitVecNum(e) -> (egno e)
    

  let mk_sort ( ctx : context ) size =
    bitvec_sort_of_ptr ctx (Z3native.mk_bv_sort (context_gno ctx) size)
  let is_bv ( x : expr ) =
    ((sort_kind_of_int (Z3native.get_sort_kind (nc_of_expr x) (Z3native.get_sort (nc_of_expr x) (ptr_of_expr x)))) == BV_SORT)
  let is_bv_numeral ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNUM)
  let is_bv_bit1 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BIT1)
  let is_bv_bit0 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BIT0)
  let is_bv_uminus ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNEG)
  let is_bv_add ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BADD)
  let is_bv_sub ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSUB)
  let is_bv_mul ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BMUL)
  let is_bv_sdiv ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSDIV)
  let is_bv_udiv ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BUDIV)
  let is_bv_SRem ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSREM)
  let is_bv_urem ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BUREM)
  let is_bv_smod ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSMOD)
  let is_bv_sdiv0 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSDIV0)
  let is_bv_udiv0 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BUDIV0)
  let is_bv_srem0 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSREM0)
  let is_bv_urem0 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BUREM0)
  let is_bv_smod0 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSMOD0)
  let is_bv_ule ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ULEQ)
  let is_bv_sle ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SLEQ)
  let is_bv_uge ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_UGEQ)
  let is_bv_sge ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SGEQ)
  let is_bv_ult ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ULT)
  let is_bv_slt ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SLT)
  let is_bv_ugt ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_UGT)
  let is_bv_sgt ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SGT)
  let is_bv_and ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BAND)
  let is_bv_or ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BOR)
  let is_bv_not ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNOT)
  let is_bv_xor ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BXOR)
  let is_bv_nand ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNAND)
  let is_bv_nor ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNOR)
  let is_bv_xnor ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BXNOR)
  let is_bv_concat ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_CONCAT)
  let is_bv_signextension ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SIGN_EXT)
  let is_bv_zeroextension ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ZERO_EXT)
  let is_bv_extract ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_EXTRACT)
  let is_bv_repeat ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_REPEAT)
  let is_bv_reduceor ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BREDOR)
  let is_bv_reduceand ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BREDAND)
  let is_bv_comp ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BCOMP)
  let is_bv_shiftleft ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSHL)
  let is_bv_shiftrightlogical ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BLSHR)
  let is_bv_shiftrightarithmetic ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BASHR)
  let is_bv_rotateleft ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ROTATE_LEFT)
  let is_bv_rotateright ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ROTATE_RIGHT)
  let is_bv_rotateleftextended ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_EXT_ROTATE_LEFT)
  let is_bv_rotaterightextended ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_EXT_ROTATE_RIGHT) 
  let is_int_to_bv ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_INT2BV)
  let is_bv_to_int ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BV2INT)
  let is_bv_carry ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_CARRY)
  let is_bv_xor3 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_XOR3)
  let get_size (x : bitvec_sort ) = Z3native.get_bv_sort_size (sgnc x) (sgno x)
  let get_int ( x : bitvec_num ) = 
    let (r, v) = Z3native.get_numeral_int (ngnc x) (ngno x) in
    if r then v
    else raise (Z3native.Exception "Conversion failed.")
  let to_string ( x : bitvec_num ) = Z3native.get_numeral_string (ngnc x) (ngno x)
  let mk_const ( ctx : context ) ( name : Symbol.symbol ) ( size : int ) =
    BitVecExpr(Expr.mk_const ctx name (match (BitVector.mk_sort ctx size) with BitVecSort(s) -> s))
  let mk_const_s ( ctx : context ) ( name : string ) ( size : int ) =
    mk_const ctx (Symbol.mk_string ctx name) size
  let mk_not  ( ctx : context ) ( t : bitvec_expr ) =
    expr_of_ptr ctx (Z3native.mk_bvnot (context_gno ctx) (egno t))
  let mk_redand  ( ctx : context ) ( t : bitvec_expr) =
    expr_of_ptr ctx (Z3native.mk_bvredand (context_gno ctx) (egno t))
  let mk_redor  ( ctx : context ) ( t : bitvec_expr) =
    expr_of_ptr ctx (Z3native.mk_bvredor (context_gno ctx) (egno t))
  let mk_and  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvand (context_gno ctx) (egno t1) (egno t2))
  let mk_or  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvor (context_gno ctx) (egno t1) (egno t2))
  let mk_xor  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvxor (context_gno ctx) (egno t1) (egno t2))
  let mk_nand  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvnand (context_gno ctx) (egno t1) (egno t2))
  let mk_nor  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvnor (context_gno ctx) (egno t1) (egno t2))
  let mk_xnor  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvxnor (context_gno ctx) (egno t1) (egno t2))
  let mk_neg  ( ctx : context ) ( t : bitvec_expr) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvneg (context_gno ctx) (egno t))
  let mk_add  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvadd (context_gno ctx) (egno t1) (egno t2))
  let mk_sub  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvsub (context_gno ctx) (egno t1) (egno t2))
  let mk_mul  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvmul (context_gno ctx) (egno t1) (egno t2))
  let mk_udiv  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvudiv (context_gno ctx) (egno t1) (egno t2))
  let mk_sdiv  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvsdiv (context_gno ctx) (egno t1) (egno t2))
  let mk_urem  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvurem (context_gno ctx) (egno t1) (egno t2))
  let mk_srem  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvsrem (context_gno ctx) (egno t1) (egno t2))
  let mk_smod  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvsmod (context_gno ctx) (egno t1) (egno t2))
  let mk_ult  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvult (context_gno ctx) (egno t1) (egno t2)))  
  let mk_slt  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvslt (context_gno ctx) (egno t1) (egno t2)))
  let mk_ule  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvule (context_gno ctx) (egno t1) (egno t2)))
  let mk_sle  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvsle (context_gno ctx) (egno t1) (egno t2)))
  let mk_uge  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvuge (context_gno ctx) (egno t1) (egno t2)))
  let mk_sge  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvsge (context_gno ctx) (egno t1) (egno t2)))
  let mk_ugt  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvugt (context_gno ctx) (egno t1) (egno t2)))   		  
  let mk_sgt  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvsgt (context_gno ctx) (egno t1) (egno t2)))   		  
  let mk_concat ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_concat (context_gno ctx) (egno t1) (egno t2))
  let mk_extract ( ctx : context ) ( high : int ) ( low : int ) ( t : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_extract (context_gno ctx) high low (egno t))
  let mk_sign_ext  ( ctx : context ) ( i : int ) ( t : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_sign_ext (context_gno ctx) i (egno t))
  let mk_zero_ext  ( ctx : context ) ( i : int ) ( t : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_zero_ext (context_gno ctx) i (egno t))
  let mk_repeat  ( ctx : context ) ( i : int ) ( t : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_repeat (context_gno ctx) i (egno t))
  let mk_shl  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvshl (context_gno ctx) (egno t1) (egno t2))	  
  let mk_lshr  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_bvlshr (context_gno ctx) (egno t1) (egno t2))
  let mk_ashr  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =    
    bitvec_expr_of_ptr ctx  (Z3native.mk_bvashr (context_gno ctx) (egno t1) (egno t2))  
  let mk_rotate_left  ( ctx : context ) ( i : int ) ( t : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_rotate_left (context_gno ctx) i (egno t))
  let mk_rotate_right ( ctx : context ) ( i : int ) ( t : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_rotate_right (context_gno ctx) i (egno t))
  let mk_ext_rotate_left ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_ext_rotate_left (context_gno ctx) (egno t1) (egno t2))
  let mk_ext_rotate_right ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    bitvec_expr_of_ptr ctx (Z3native.mk_ext_rotate_right (context_gno ctx) (egno t1) (egno t2))	  
  let mk_bv2int  ( ctx : context ) ( t : bitvec_expr ) ( signed : bool ) =
    Arithmetic.Integer.int_expr_of_ptr ctx (Z3native.mk_bv2int (context_gno ctx) (egno t) signed)
  let mk_add_no_overflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) ( signed : bool) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvadd_no_overflow (context_gno ctx) (egno t1) (egno t2) signed))
  let mk_add_no_underflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvadd_no_underflow (context_gno ctx) (egno t1) (egno t2)))	  
  let mk_sub_no_overflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvsub_no_overflow (context_gno ctx) (egno t1) (egno t2)))		  
  let mk_sub_no_underflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) ( signed : bool) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvsub_no_underflow (context_gno ctx) (egno t1) (egno t2) signed))
  let mk_sdiv_no_overflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvsdiv_no_overflow (context_gno ctx) (egno t1) (egno t2)))
  let mk_neg_no_overflow  ( ctx : context ) ( t : bitvec_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvneg_no_overflow (context_gno ctx) (egno t)))
  let mk_mul_no_overflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) ( signed : bool) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvmul_no_overflow (context_gno ctx) (egno t1) (egno t2) signed))
  let mk_mul_no_underflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.mk_bvmul_no_underflow (context_gno ctx) (egno t1) (egno t2)))	  
  let mk_numeral ( ctx : context ) ( v : string ) ( size : int) =
    bitvec_num_of_ptr ctx (Z3native.mk_numeral (context_gno ctx) v (sgno (BitVector.mk_sort ctx size)))
end


module Proof = 
struct
  let is_true ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_TRUE)
  let is_asserted ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_ASSERTED)
  let is_goal ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_GOAL)
  let is_modus_ponens ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_MODUS_PONENS)
  let is_reflexivity ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_REFLEXIVITY)
  let is_symmetry ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_SYMMETRY)
  let is_transitivity ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_TRANSITIVITY)
  let is_Transitivity_star ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_TRANSITIVITY_STAR)
  let is_monotonicity ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_MONOTONICITY)
  let is_quant_intro ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_QUANT_INTRO)
  let is_distributivity ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_DISTRIBUTIVITY)
  let is_and_elimination ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_AND_ELIM)
  let is_or_elimination ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_NOT_OR_ELIM)
  let is_rewrite ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_REWRITE)
  let is_rewrite_star ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_REWRITE_STAR)
  let is_pull_quant ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_PULL_QUANT)
  let is_pull_quant_star ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_PULL_QUANT_STAR)
  let is_push_quant ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_PUSH_QUANT)
  let is_elim_unused_vars ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_ELIM_UNUSED_VARS)
  let is_der ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_DER)
  let is_quant_inst ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_QUANT_INST)
  let is_hypothesis ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_HYPOTHESIS)
  let is_lemma ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_LEMMA)
  let is_unit_resolution ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_UNIT_RESOLUTION)
  let is_iff_true ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_IFF_TRUE)
  let is_iff_false ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_IFF_FALSE)
  let is_commutativity ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_COMMUTATIVITY) (*  *)
  let is_def_axiom ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_DEF_AXIOM)
  let is_def_intro ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_DEF_INTRO)
  let is_apply_def ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_APPLY_DEF)
  let is_iff_oeq ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_IFF_OEQ)
  let is_nnf_pos ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_NNF_POS)
  let is_nnf_neg ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_NNF_NEG)
  let is_nnf_star ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_NNF_STAR)
  let is_cnf_star ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_CNF_STAR)
  let is_skolemize ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_SKOLEMIZE)
  let is_modus_ponens_oeq ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_MODUS_PONENS_OEQ)
  let is_theory_lemma ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_TH_LEMMA)
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
      
  let assert_ ( x : goal ) ( constraints : Boolean.bool_expr array ) =
    let f e = Z3native.goal_assert (z3obj_gnc x) (z3obj_gno x) (Boolean.gno e) in
    ignore (Array.map f constraints) ;
    ()
      
  let is_inconsistent ( x : goal ) =
    Z3native.goal_inconsistent (z3obj_gnc x) (z3obj_gno x)

  let get_depth ( x : goal ) = Z3native.goal_depth (z3obj_gnc x) (z3obj_gno x)
    
  let reset ( x : goal ) =  Z3native.goal_reset (z3obj_gnc x) (z3obj_gno x)
    
  let get_size ( x : goal ) = Z3native.goal_size (z3obj_gnc x) (z3obj_gno x)

  let get_formulas ( x : goal ) =
    let n = get_size x in 
    let f i = (Boolean.bool_expr_of_expr (expr_of_ptr (z3obj_gc x) 
				    (Z3native.goal_formula (z3obj_gnc x) (z3obj_gno x) i))) in
    Array.init n f

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
	Array.init n f
	  
      let to_string ( x : func_entry ) =
	let a = (get_args x) in
	let f c p = (p ^ (Expr.to_string c) ^ ", ") in
	"[" ^ Array.fold_right f a ((Expr.to_string (get_value x)) ^ "]")
    end

    let get_num_entries ( x: func_interp ) = Z3native.func_interp_get_num_entries (z3obj_gnc x) (z3obj_gno x)

    let get_entries ( x : func_interp ) =
      let n = (get_num_entries x) in
      let f i = (FuncEntry.create (z3obj_gc x) (Z3native.func_interp_get_entry (z3obj_gnc x) (z3obj_gno x) i)) in
      Array.init n f

    let get_else ( x : func_interp ) = expr_of_ptr (z3obj_gc x) (Z3native.func_interp_get_else (z3obj_gnc x) (z3obj_gno x))

    let get_arity ( x : func_interp ) = Z3native.func_interp_get_arity (z3obj_gnc x) (z3obj_gno x)

    let to_string ( x : func_interp ) =     
      let f c p = (
	let n = (FuncEntry.get_num_args c) in
	p ^ 
	  let g c p = (p ^ (Expr.to_string c) ^ ", ") in
	  (if n > 1 then "[" else "") ^
	    (Array.fold_right 
	       g 
	       (FuncEntry.get_args c) 
	       ((if n > 1 then "]" else "") ^ " -> " ^ (Expr.to_string (FuncEntry.get_value c)) ^ ", "))
      ) in
      Array.fold_right f (get_entries x) ("else -> " ^ (Expr.to_string (get_else x)) ^ "]")
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
    Array.init n f
      
  let get_num_funcs ( x : model ) = Z3native.model_get_num_funcs (z3obj_gnc x) (z3obj_gno x)
    
  let get_func_decls ( x : model ) = 
    let n = (get_num_consts x) in
    let f i = func_decl_of_ptr (z3obj_gc x) (Z3native.model_get_func_decl (z3obj_gnc x) (z3obj_gno x) i) in
    Array.init n f
      
  let get_decls ( x : model ) =
    let n_funcs = (get_num_funcs x) in
    let n_consts = (get_num_consts x ) in
    let f i = func_decl_of_ptr (z3obj_gc x) (Z3native.model_get_func_decl (z3obj_gnc x) (z3obj_gno x) i) in
    let g i = func_decl_of_ptr (z3obj_gc x) (Z3native.model_get_const_decl (z3obj_gnc x) (z3obj_gno x) i) in
    Array.append (Array.init n_funcs f) (Array.init n_consts g)
      
  exception ModelEvaluationFailedException of string
      
  let eval ( x : model ) ( t : expr ) ( completion : bool ) =
    let (r, v) = (Z3native.model_eval (z3obj_gnc x) (z3obj_gno x) (ptr_of_expr t) completion) in
    if not r then
      raise (ModelEvaluationFailedException "evaluation failed")
    else
      expr_of_ptr (z3obj_gc x) v

  let evaluate ( x : model ) ( t : expr ) ( completion : bool ) =
    eval x t completion
      
  let get_num_sorts ( x : model ) = Z3native.model_get_num_sorts (z3obj_gnc x) (z3obj_gno x)
    
  let get_sorts ( x : model ) =
    let n = (get_num_sorts x) in
    let f i = (sort_of_ptr (z3obj_gc x) (Z3native.model_get_sort (z3obj_gnc x) (z3obj_gno x) i)) in
    Array.init n f

  let sort_universe ( x : model ) ( s : sort ) =
    let n_univ = AST.ASTVector.ast_vector_of_ptr (z3obj_gc x) (Z3native.model_get_sort_universe (z3obj_gnc x) (z3obj_gno x) (Sort.gno s)) in
    let n = (AST.ASTVector.get_size n_univ) in
    let f i = (AST.ASTVector.get n_univ i) in
    Array.init n f

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
    Array.init n f

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
      Array.init n f
	
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
    Array.init n f

  let get_tactic_description ( ctx : context ) ( name : string ) =
    Z3native.tactic_get_descr (context_gno ctx) name

  let mk_tactic ( ctx : context ) ( name : string ) =
    create ctx (Z3native.mk_tactic (context_gno ctx) name)

  let and_then ( ctx : context ) ( t1 : tactic ) ( t2 : tactic ) ( ts : tactic array ) =
    let f p c = (match p with 
      | None -> (Some (z3obj_gno c)) 
      | Some(x) -> (Some (Z3native.tactic_and_then (context_gno ctx) (z3obj_gno c) x))) in
    match (Array.fold_left f None ts) with
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

  let par_or ( ctx : context ) ( t : tactic array ) =
    create ctx (Z3native.tactic_par_or (context_gno ctx) (Array.length t) (array_to_native t))

  let par_and_then ( ctx : context ) ( t1 : tactic ) ( t2 : tactic ) =
    create ctx (Z3native.tactic_par_and_then (context_gno ctx) (z3obj_gno t1) (z3obj_gno t2))

  let interrupt ( ctx : context ) =
    Z3native.interrupt (context_gno ctx)
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
      Array.init n f

    let get_keys ( x : statistics ) =
      let n = (get_size x) in
      let f i = (Z3native.stats_get_key (z3obj_gnc x) (z3obj_gno x) i) in
      Array.init n f
	
    let get ( x : statistics ) ( key : string ) =
      let f p c = (if ((Entry.get_key c) == key) then (Some c) else p) in
      Array.fold_left f None (get_entries x)
  end

  let get_help ( x : solver ) = Z3native.solver_get_help (z3obj_gnc x) (z3obj_gno x)

  let set_parameters ( x : solver ) ( p : Params.params )=
    Z3native.solver_set_params (z3obj_gnc x) (z3obj_gno x) (z3obj_gno p)

  let get_param_descrs ( x : solver ) =
    Params.ParamDescrs.param_descrs_of_ptr (z3obj_gc x) (Z3native.solver_get_param_descrs (z3obj_gnc x) (z3obj_gno x))

  let get_num_scopes ( x : solver ) = Z3native.solver_get_num_scopes (z3obj_gnc x) (z3obj_gno x)

  let push ( x : solver ) = Z3native.solver_push (z3obj_gnc x) (z3obj_gno x)

  let pop ( x : solver ) ( n : int ) = Z3native.solver_pop (z3obj_gnc x) (z3obj_gno x) n

  let reset ( x : solver ) = Z3native.solver_reset (z3obj_gnc x) (z3obj_gno x)

  let assert_ ( x : solver ) ( constraints : Boolean.bool_expr array ) =
    let f e = (Z3native.solver_assert (z3obj_gnc x) (z3obj_gno x) (Boolean.gno e)) in
    ignore (Array.map f constraints)

  let assert_and_track_a ( x : solver ) ( cs : Boolean.bool_expr array ) ( ps : Boolean.bool_expr array ) =
    if ((Array.length cs) != (Array.length ps)) then
      raise (Z3native.Exception "Argument size mismatch")
    else
      let f i e = (Z3native.solver_assert_and_track (z3obj_gnc x) (z3obj_gno x) (Boolean.gno e) (Boolean.gno (Array.get ps i))) in
      ignore (Array.iteri f cs)
	
  let assert_and_track ( x : solver ) ( c : Boolean.bool_expr ) ( p : Boolean.bool_expr ) =    
    Z3native.solver_assert_and_track (z3obj_gnc x) (z3obj_gno x) (Boolean.gno c) (Boolean.gno p)

  let get_num_assertions ( x : solver ) =
    let a = AST.ASTVector.ast_vector_of_ptr (z3obj_gc x) (Z3native.solver_get_assertions (z3obj_gnc x) (z3obj_gno x)) in
    (AST.ASTVector.get_size a)

  let get_assertions ( x : solver ) =
    let a = AST.ASTVector.ast_vector_of_ptr (z3obj_gc x) (Z3native.solver_get_assertions (z3obj_gnc x) (z3obj_gno x)) in
    let n = (AST.ASTVector.get_size a) in
    let f i = Boolean.bool_expr_of_expr (expr_of_ptr (z3obj_gc x) (z3obj_gno (AST.ASTVector.get a i))) in
    Array.init n f

  let check ( x : solver ) ( assumptions : Boolean.bool_expr array) =
    let r = 
      if ((Array.length assumptions) == 0) then
	lbool_of_int (Z3native.solver_check (z3obj_gnc x) (z3obj_gno x))
      else
	let f x = (ptr_of_expr (Boolean.expr_of_bool_expr x)) in
	lbool_of_int (Z3native.solver_check_assumptions (z3obj_gnc x) (z3obj_gno x) (Array.length assumptions) (Array.map f assumptions))
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
    let cn = AST.ASTVector.ast_vector_of_ptr (z3obj_gc x) (Z3native.solver_get_unsat_core (z3obj_gnc x) (z3obj_gno x)) in 
    let n = (AST.ASTVector.get_size cn) in
    let f i = (AST.ASTVector.get cn i) in
    Array.init n f

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
      
  let assert_ ( x : fixedpoint ) ( constraints : Boolean.bool_expr array ) =
    let f e = (Z3native.fixedpoint_assert (z3obj_gnc x) (z3obj_gno x) (Boolean.gno e)) in
    ignore (Array.map f constraints) ;
    ()

  let register_relation ( x : fixedpoint ) ( f : func_decl ) =
    Z3native.fixedpoint_register_relation (z3obj_gnc x) (z3obj_gno x) (FuncDecl.gno f)
      
  let add_rule ( x : fixedpoint ) ( rule : Boolean.bool_expr ) ( name : Symbol.symbol option ) =
    match name with 
      | None -> Z3native.fixedpoint_add_rule (z3obj_gnc x) (z3obj_gno x) (Boolean.gno rule) null
      | Some(y) -> Z3native.fixedpoint_add_rule (z3obj_gnc x) (z3obj_gno x) (Boolean.gno rule) (Symbol.gno y)

  let add_fact ( x : fixedpoint ) ( pred : func_decl ) ( args : int array ) =
    Z3native.fixedpoint_add_fact (z3obj_gnc x) (z3obj_gno x) (FuncDecl.gno pred) (Array.length args) args

  let query ( x : fixedpoint ) ( query : Boolean.bool_expr ) =
    match (lbool_of_int (Z3native.fixedpoint_query (z3obj_gnc x) (z3obj_gno x) (Boolean.gno query))) with
      | L_TRUE -> Solver.SATISFIABLE
      | L_FALSE -> Solver.UNSATISFIABLE
      | _ -> Solver.UNKNOWN

  let query_r ( x : fixedpoint ) ( relations : func_decl array ) =
    let f x = ptr_of_ast (ast_of_func_decl x) in
    match (lbool_of_int (Z3native.fixedpoint_query_relations (z3obj_gnc x) (z3obj_gno x) (Array.length relations) (Array.map f relations))) with
      | L_TRUE -> Solver.SATISFIABLE
      | L_FALSE -> Solver.UNSATISFIABLE
      | _ -> Solver.UNKNOWN
	
  let push ( x : fixedpoint ) =
    Z3native.fixedpoint_push (z3obj_gnc x) (z3obj_gno x)
      
  let pop ( x : fixedpoint ) =
    Z3native.fixedpoint_pop (z3obj_gnc x) (z3obj_gno x)

  let update_rule ( x : fixedpoint ) ( rule : Boolean.bool_expr ) ( name : Symbol.symbol ) =
    Z3native.fixedpoint_update_rule (z3obj_gnc x) (z3obj_gno x) (Boolean.gno rule) (Symbol.gno name)

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
    Z3native.fixedpoint_add_cover (z3obj_gnc x) (z3obj_gno x) level (FuncDecl.gno predicate) (ptr_of_expr property)
      
  let to_string ( x : fixedpoint ) = Z3native.fixedpoint_to_string (z3obj_gnc x) (z3obj_gno x) 0 [||]
    
  let set_predicate_representation ( x : fixedpoint ) ( f : func_decl ) ( kinds : Symbol.symbol array ) =
    let f2 x = (Symbol.gno x) in
    Z3native.fixedpoint_set_predicate_representation (z3obj_gnc x) (z3obj_gno x) (FuncDecl.gno f) (Array.length kinds) (Array.map f2 kinds)

  let to_string_q ( x : fixedpoint ) ( queries : Boolean.bool_expr array ) =
    let f x = ptr_of_expr (Boolean.expr_of_bool_expr x) in
    Z3native.fixedpoint_to_string (z3obj_gnc x) (z3obj_gno x) (Array.length queries) (Array.map f queries)

  let get_rules ( x : fixedpoint ) = 
    let v = (AST.ASTVector.ast_vector_of_ptr (z3obj_gc x) (Z3native.fixedpoint_get_rules (z3obj_gnc x) (z3obj_gno x))) in
    let n = (AST.ASTVector.get_size v) in
    let f i = Boolean.bool_expr_of_expr (expr_of_ptr (z3obj_gc x) (z3obj_gno (AST.ASTVector.get v i))) in
    Array.init n f

  let get_assertions ( x : fixedpoint ) = 
    let v = (AST.ASTVector.ast_vector_of_ptr (z3obj_gc x) (Z3native.fixedpoint_get_assertions (z3obj_gnc x) (z3obj_gno x))) in
    let n = (AST.ASTVector.get_size v) in
    let f i = Boolean.bool_expr_of_expr (expr_of_ptr (z3obj_gc x) (z3obj_gno (AST.ASTVector.get v i))) in
    Array.init n f

  let mk_fixedpoint ( ctx : context ) = create ctx
end

module Options =
struct

  let update_param_value ( ctx : context ) ( id : string) ( value : string )=
    Z3native.update_param_value (context_gno ctx) id value

  let get_param_value ( ctx : context ) ( id : string ) =
    let (r, v) = (Z3native.get_param_value (context_gno ctx) id) in
    if not r then
      None
    else 
      Some v

  let set_print_mode ( ctx : context ) ( value : ast_print_mode ) =
    Z3native.set_ast_print_mode (context_gno ctx) (int_of_ast_print_mode value)

  let toggle_warning_messages ( enabled: bool ) =
    Z3native.toggle_warning_messages enabled
end


module SMT =
struct
  let benchmark_to_smtstring ( ctx : context ) ( name : string ) ( logic : string ) ( status : string ) ( attributes : string ) ( assumptions : Boolean.bool_expr array ) ( formula : Boolean.bool_expr ) =
    Z3native.benchmark_to_smtlib_string (context_gno ctx) name logic status attributes
      (Array.length assumptions) (let f x = ptr_of_expr (Boolean.expr_of_bool_expr x) in (Array.map f assumptions))
      (Boolean.gno formula)

  let parse_smtlib_string ( ctx : context ) ( str : string ) ( sort_names : Symbol.symbol array ) ( sorts : sort array ) ( decl_names : Symbol.symbol array ) ( decls : func_decl array ) =
    let csn = (Array.length sort_names) in
    let cs = (Array.length sorts) in
    let cdn = (Array.length decl_names) in
    let cd = (Array.length decls) in
    if (csn != cs || cdn != cd) then 
      raise (Z3native.Exception "Argument size mismatch")
    else
      Z3native.parse_smtlib_string (context_gno ctx) str 
	cs 
	(let f x = Symbol.gno x in (Array.map f sort_names))
	(let f x = Sort.gno x in (Array.map f sorts))
	cd 
	(let f x = Symbol.gno x in (Array.map f decl_names))
	(let f x = FuncDecl.gno x in (Array.map f decls))
	
  let parse_smtlib_file ( ctx : context ) ( file_name : string ) ( sort_names : Symbol.symbol array ) ( sorts : sort array ) ( decl_names : Symbol.symbol array ) ( decls : func_decl array ) =
    let csn = (Array.length sort_names) in
    let cs = (Array.length sorts) in
    let cdn = (Array.length decl_names) in
    let cd = (Array.length decls) in
    if (csn != cs || cdn != cd) then 
      raise (Z3native.Exception "Argument size mismatch")
    else
      Z3native.parse_smtlib_file (context_gno ctx) file_name
	cs 
	(let f x = Symbol.gno x in (Array.map f sort_names))
	(let f x = Sort.gno x in (Array.map f sorts))
	cd 
	(let f x = Symbol.gno x in (Array.map f decl_names))
	(let f x = FuncDecl.gno x in (Array.map f decls))

  let get_num_smtlib_formulas ( ctx : context ) = Z3native.get_smtlib_num_formulas (context_gno ctx)

  let get_smtlib_formulas ( ctx : context ) =
    let n = (get_num_smtlib_formulas ctx ) in
    let f i = Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.get_smtlib_formula (context_gno ctx) i)) in
    Array.init n f 

  let get_num_smtlib_assumptions ( ctx : context ) = Z3native.get_smtlib_num_assumptions (context_gno ctx)

  let get_smtlib_assumptions ( ctx : context ) =
    let n = (get_num_smtlib_assumptions ctx ) in
    let f i =  Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.get_smtlib_assumption (context_gno ctx) i)) in
    Array.init n f

  let get_num_smtlib_decls ( ctx : context ) = Z3native.get_smtlib_num_decls (context_gno ctx)

  let get_smtlib_decls ( ctx : context ) = 
    let n = (get_num_smtlib_decls ctx) in
    let f i = func_decl_of_ptr ctx (Z3native.get_smtlib_decl (context_gno ctx) i) in
    Array.init n f

  let get_num_smtlib_sorts ( ctx : context )  = Z3native.get_smtlib_num_sorts (context_gno ctx)
 
  let get_smtlib_sorts ( ctx : context ) = 
    let n = (get_num_smtlib_sorts ctx) in
    let f i = (sort_of_ptr ctx (Z3native.get_smtlib_sort (context_gno ctx) i)) in
    Array.init n f

  let parse_smtlib2_string ( ctx : context ) ( str : string ) ( sort_names : Symbol.symbol array ) ( sorts : sort array ) ( decl_names : Symbol.symbol array ) ( decls : func_decl array ) =
    let csn = (Array.length sort_names) in
    let cs = (Array.length sorts) in
    let cdn = (Array.length decl_names) in
    let cd = (Array.length decls) in
    if (csn != cs || cdn != cd) then 
      raise (Z3native.Exception "Argument size mismatch")
    else
      Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.parse_smtlib2_string (context_gno ctx) str 
					    cs 
					    (let f x = Symbol.gno x in (Array.map f sort_names))
					    (let f x = Sort.gno x in (Array.map f sorts))
					    cd 
					    (let f x = Symbol.gno x in (Array.map f decl_names))
					    (let f x = FuncDecl.gno x in (Array.map f decls))))

  let parse_smtlib2_file ( ctx : context ) ( file_name : string ) ( sort_names : Symbol.symbol array ) ( sorts : sort array ) ( decl_names : Symbol.symbol array ) ( decls : func_decl array ) =
    let csn = (Array.length sort_names) in
    let cs = (Array.length sorts) in
    let cdn = (Array.length decl_names) in
    let cd = (Array.length decls) in
    if (csn != cs || cdn != cd) then 
      raise (Z3native.Exception "Argument size mismatch")
    else
      Boolean.bool_expr_of_expr (expr_of_ptr ctx (Z3native.parse_smtlib2_string (context_gno ctx) file_name
					    cs 
					    (let f x = Symbol.gno x in (Array.map f sort_names))
					    (let f x = Sort.gno x in (Array.map f sorts))
					    cd 
					    (let f x = Symbol.gno x in (Array.map f decl_names))
					    (let f x = FuncDecl.gno x in (Array.map f decls))))
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
