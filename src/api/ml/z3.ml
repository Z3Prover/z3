(**
   The Z3 ML/Ocaml Interface.

   Copyright (C) 2012 Microsoft Corporation
   @author CM Wintersteiger (cwinter) 2012-12-17
*)

open Z3enums

type context = { m_n_ctx : Z3native.z3_context; m_n_obj_cnt: int; } 

(**/**) 

let null = Z3native.mk_null()
let is_null o = (Z3native.is_null o)

let context_dispose ctx = 
  if ctx.m_n_obj_cnt == 0 then (
    (* Printf.printf "Disposing context \n" ; *)
    (Z3native.del_context ctx.m_n_ctx)
  ) else (
    Printf.printf "NOT DISPOSING context because it still has %d objects alive\n" ctx.m_n_obj_cnt;
    (* re-queue for finalization? *)
  )

let context_cnstr settings =
  let cfg = Z3native.mk_config in
  let f e = (Z3native.set_param_value cfg (fst e) (snd e)) in
  (List.iter f settings) ;
  let v = Z3native.mk_context_rc cfg in
  Z3native.del_config(cfg) ;
  Z3native.set_ast_print_mode v (int_of_ast_print_mode PRINT_SMTLIB2_COMPLIANT) ;
  (* Printf.printf "Installing finalizer on context \n" ; *)
  let res = { m_n_ctx = v; m_n_obj_cnt = 0 } in
  let f = fun o -> context_dispose o in
  Gc.finalise f res;
  res
(* CMW: Install error handler here! 
   m_n_err_handler = new Z3native.error_handler(NativeErrorHandler);  keep reference so it doesn't get collected.
   Z3native.set_error_handler(m_ctx, m_n_err_handler);
  GC.SuppressFinalize(this);
*)

let context_add1 ctx = ignore (ctx.m_n_obj_cnt = ctx.m_n_obj_cnt + 1)
let context_sub1 ctx = ignore (ctx.m_n_obj_cnt = ctx.m_n_obj_cnt - 1)
let context_gno ctx = ctx.m_n_ctx

(**/**)

(** Create a context object. 

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
let mk_context ( cfg : ( string * string ) list ) =
  context_cnstr cfg


(* type z3object = { m_ctx : context; m_n_obj : Z3native.ptr option; } *)

(**/**)
class virtual z3object ctx_init obj_init =
object (self)
  val mutable m_ctx : context = ctx_init
  val mutable m_n_obj : Z3native.ptr option = obj_init
    
  initializer 
    (match m_n_obj with 
      | Some (x) -> self#incref (context_gno m_ctx) x;
	(context_add1 m_ctx)
      | None -> ()
    );
    (* Printf.printf "Installing finalizer on z3object %d \n" (Oo.id self) ; *)
    let f = fun o -> o#dispose in
    let v = self in
    Gc.finalise f v

  method virtual incref : Z3native.ptr -> Z3native.ptr -> unit
  method virtual decref : Z3native.ptr -> Z3native.ptr -> unit
    
  method dispose =
    (* Printf.printf "Disposing z3object %d \n" (Oo.id self) ; *)
    (match m_n_obj with
      | Some (x) -> 
	self#decref (context_gno m_ctx) x; 
	(context_sub1 m_ctx) ;
	m_n_obj <- None; 
      | None -> ()
    ); 

  method gno = match m_n_obj with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Z3 object lost")

  method sno (ctx : context) o =
    (context_add1 m_ctx) ;
    self#incref (context_gno ctx) o ;
    (match m_n_obj with
      | Some(x) -> self#decref (context_gno ctx) x ; (context_sub1 m_ctx)
      | None -> ()
    );
    m_n_obj <- Some o

  method gc = m_ctx
  method gnc = (context_gno m_ctx)
end


(** Parameter set objects *)
class params ctx = 
object (self)
  inherit z3object ctx None as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method incref nc o = Z3native.params_inc_ref nc o
  method decref nc o = Z3native.params_dec_ref nc o
end


(** Symbol objects *)
class symbol ctx =
object (self)
  inherit z3object ctx None as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method incref nc o = ()
  method decref nc o = ()
end

(** Int symbol objects *)
class int_symbol ctx =
object(self)
  inherit symbol ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method cnstr_int i = (self#sno ctx (Z3native.mk_int_symbol (context_gno ctx) i)) ; self
end

(** String symbol objects *)
class string_symbol ctx =
object(self)
  inherit symbol ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method cnstr_string name = (self#sno ctx (Z3native.mk_string_symbol (context_gno ctx) name)) ; self
end

let symbolaton (a : symbol array) =
  let f (e : symbol) = e#gno in 
  Array.map f a

let create_symbol ctx no =
  match (symbol_kind_of_int (Z3native.get_symbol_kind (context_gno ctx) no)) with
    | INT_SYMBOL -> (((new int_symbol ctx)#cnstr_obj no) :> symbol)
    | STRING_SYMBOL -> (((new string_symbol ctx)#cnstr_obj no) :> symbol)
      
(** AST objects *)
class ast ctx =
object (self)
  inherit z3object ctx None as super (* CMW: derive from icomparable? *)  
  method cnstr_obj obj = (self#sno ctx obj) ; self

  method incref nc o = Z3native.inc_ref nc o
  method decref nc o = Z3native.dec_ref nc o       
end
  
let astaton (a : ast array) =
  let f (e : ast) = e#gno in 
  Array.map f a

(** Sort objects *)
class sort ctx =
object (self)
  inherit ast ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

let sortaton (a : sort array) =
  let f (e : sort) = e#gno in 
  Array.map f a

(** Arithmetic sort objects, i.e., Int or Real. *)
class arith_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Array sorts objects *)
class array_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method cnstr_dr (domain : sort) (range : sort) = (self#sno ctx (Z3native.mk_array_sort (context_gno ctx) domain#gno range#gno)) ; self
end

(** Bit-vector sort objects *)
class bitvec_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Boolean sort objects *)
class bool_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Int sort objects *)
class int_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Real sort objects *)
class real_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Uninterpreted sort objects *)
class uninterpreted_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method cnstr_s (s : symbol) = (self #sno ctx (Z3native.mk_uninterpreted_sort (context_gno ctx) s#gno)) ; self
end

(** Finite domain sort objects *)
class finite_domain_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method cnstr_si (s : symbol) ( sz : int )= (self #sno ctx (Z3native.mk_finite_domain_sort (context_gno ctx) s#gno sz)) ; self
end

(** Relation sort objects *)
class relation_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Set sort objects *)
class set_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method cnstr_s (s : sort) = (self#sno ctx s#gno) ; self
end

(** Tuple sort objects *)
class tuple_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method cnstr_siss (name : symbol) (num_fields: int) (field_names : symbol array) (field_sorts : sort array) =
    let (x,_,_) = (Z3native.mk_tuple_sort (context_gno ctx) name#gno num_fields (symbolaton field_names) (astaton field_sorts)) in
    (self#sno ctx x) ;
    self
end


(** Function declaration objects *)
class func_decl ctx =
object (self)
  inherit ast ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method cnstr_ndr (name : symbol) (domain : sort array) (range : sort)  = (self#sno ctx (Z3native.mk_func_decl (context_gno ctx) name#gno (Array.length domain) (astaton domain) range#gno)) ; self
  method cnstr_pdr (prefix : string) (domain : sort array) (range : sort) = (self#sno ctx (Z3native.mk_fresh_func_decl (context_gno ctx) prefix (Array.length domain) (astaton domain) range#gno)) ; self

  method incref nc o = super#incref nc o
  method decref nc o = super#decref nc o
end

let func_declaton (a : func_decl array) =
  let f (e : func_decl) = e#gno in 
  Array.map f a

class parameter =
object (self)
  val mutable m_kind : parameter_kind = PARAMETER_INT;
  val mutable m_i : int = 0
  val mutable m_d : float = 0.0
  val mutable m_sym : symbol option = None
  val mutable m_srt : sort option = None
  val mutable m_ast : ast option = None
  val mutable m_fd : func_decl option = None
  val mutable m_r : string = ""

  method cnstr_int i = m_kind <- PARAMETER_INT; m_i <- i
  method cnstr_double d = m_kind <- PARAMETER_DOUBLE; m_d <- d
  method cnstr_symbol sym = m_kind <- PARAMETER_SYMBOL; m_sym <- sym
  method cnstr_sort srt = m_kind <- PARAMETER_SORT; m_srt <- srt
  method cnstr_ast ast = m_kind <- PARAMETER_AST; m_ast <- ast
  method cnstr_func_decl fd = m_kind <- PARAMETER_FUNC_DECL; m_fd <- fd
  method cnstr_rational r = m_kind <- PARAMETER_RATIONAL; m_r <- r

  method kind = m_kind
  method int = m_i
  method double = m_d
  method symbol = match m_sym with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing parameter symbol")
  method sort = match m_srt with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing parameter sort")
  method ast = match m_ast with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing parameter ast")
  method func_decl = match m_fd with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing parameter func_decl")
  method rational = m_r
end


(** Enum sort objects *)
class enum_sort ctx =
object (self)
  inherit sort ctx as super
  val mutable _constdecls : func_decl array option = None
  val mutable _testerdecls : func_decl array option = None
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method cnstr_ss (name : symbol) (enum_names : symbol array) = 
    let (r, a, b) = (Z3native.mk_enumeration_sort (context_gno ctx) name#gno (Array.length enum_names) (symbolaton enum_names)) in
    _constdecls <- Some (let f e = (new func_decl ctx)#cnstr_obj e in (Array.map f a)) ;
    _testerdecls <- Some (let f e = (new func_decl ctx)#cnstr_obj e in (Array.map f b)) ;
    (self#sno ctx r) ; 
    self

  method const_decls = match _constdecls with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing const decls")

  method tester_decls = match _testerdecls with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing tester decls")
end

(** List sort objects *)
class list_sort ctx =
object (self)
  inherit sort ctx as super    
  val mutable _nildecl : func_decl option = None
  val mutable _is_nildecl : func_decl option = None
  val mutable _consdecl : func_decl option = None
  val mutable _is_consdecl : func_decl option = None
  val mutable _headdecl : func_decl option = None
  val mutable _taildecl : func_decl option = None
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method cnstr_ss (name : symbol) (elem_sort : sort) =
    let (r, a, b, c, d, e, f) = (Z3native.mk_list_sort (context_gno ctx) name#gno elem_sort#gno) in
    _nildecl <- Some ((new func_decl ctx)#cnstr_obj a) ;
    _is_nildecl <- Some ((new func_decl ctx)#cnstr_obj b) ;
    _consdecl <- Some ((new func_decl ctx)#cnstr_obj c) ;
    _is_consdecl <- Some ((new func_decl ctx)#cnstr_obj d) ;
    _headdecl <- Some ((new func_decl ctx)#cnstr_obj e) ;
    _taildecl <- Some ((new func_decl ctx)#cnstr_obj f) ;
    (self#sno ctx r) ;
    self

  method nil_decl = match _nildecl with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing nil decl")

  method is_nil_decl = match _is_nildecl with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing is_nil decl")

  method cons_decl = match _consdecl with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing cons decl")

  method is_cons_decl = match _is_consdecl with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing is_cons decl")

  method head_decl = match _headdecl with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing head decl")

  method tail_decl = match _taildecl with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing tail decl")
end

(** Constructor objects *)
class constructor ctx =
object (self)
  inherit z3object ctx None as super
  val mutable m_n : int = 0
  val mutable m_tester_decl : func_decl option = None
  val mutable m_constructor_decl : func_decl  option = None
  val mutable m_accessor_decls : func_decl array option = None
  method incref nc o = ()
  method decref nc o = ()
  initializer 
  let f = fun o -> Z3native.del_constructor o#gnc o#gno in
  let v = self in
  Gc.finalise f v

  method cnstr_ssssi (name : symbol) (recognizer : symbol) (field_names : symbol array) (sorts : sort array) (sort_refs : int array) =
    m_n <- (Array.length field_names) ;
    if m_n != (Array.length sorts) then
      raise (Z3native.Exception "Number of field names does not match number of sorts")
    else
      if m_n != (Array.length sort_refs) then
	raise (Z3native.Exception "Number of field names does not match number of sort refs")
      else
        let o = (Z3native.mk_constructor (context_gno ctx) name#gno recognizer#gno m_n (symbolaton field_names)
		   (sortaton sorts)
		   sort_refs) in
	self#sno ctx o ; 
	self

  method private init =
    match m_tester_decl with
      | None -> 
	let (a, b, c) = (Z3native.query_constructor self#gnc self#gno m_n) in
	m_constructor_decl <- Some ((new func_decl ctx)#cnstr_obj a) ;
	m_tester_decl <- Some ((new func_decl ctx)#cnstr_obj b) ;	
	m_accessor_decls <- Some (let f e = ((new func_decl ctx)#cnstr_obj e) in Array.map f c) ;
	()
      | _ -> ()

  method get_n = m_n
    
  method tester_decl = match m_tester_decl with
    | Some(x) -> x
    | None -> self#init ; self#tester_decl

  method constructor_decl = match m_constructor_decl with
    | Some(x) -> x
    | None -> self#init ; self#constructor_decl

  method accessor_decls = match m_accessor_decls with
    | Some(x) -> x
    | None -> self#init ; self#accessor_decls
end

let constructoraton (a : constructor array) =
  let f (e : constructor) = e#gno in 
  Array.map f a

(** Constructor list objects *)
class constructor_list ctx =
object (self)
  inherit z3object ctx None
  method incref nc o = ()
  method decref nc o = ()    
  initializer 
  let f = fun o -> Z3native.del_constructor_list o#gnc o#gno in
  let v = self in
  Gc.finalise f v
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method cnstr_ca ( c : constructor array ) =
    self#sno ctx (Z3native.mk_constructor_list (context_gno ctx) (Array.length c) (constructoraton c)) ;
    self
end

let constructor_listaton (a : constructor_list array) =
  let f (e : constructor_list) = e#gno in 
  Array.map f a

(** Datatype sort objects *)
class datatype_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method cnstr_sc (name : symbol) (constructors : constructor array) = (self#sno ctx (fst (Z3native.mk_datatype (context_gno ctx) name#gno (Array.length constructors) (constructoraton constructors)))) ; self
end

let create_sort ctx obj =
  match (sort_kind_of_int (Z3native.get_sort_kind (context_gno ctx) obj)) with
    | ARRAY_SORT -> (((new array_sort ctx)#cnstr_obj obj) :> sort)
    | BOOL_SORT -> (((new bool_sort ctx)#cnstr_obj obj) :> sort)
    | BV_SORT -> (((new bitvec_sort ctx)#cnstr_obj obj) :> sort)
    | DATATYPE_SORT -> (((new datatype_sort ctx)#cnstr_obj obj) :> sort)
    | INT_SORT -> (((new int_sort ctx)#cnstr_obj obj) :> sort)
    | REAL_SORT -> (((new real_sort ctx)#cnstr_obj obj) :> sort)
    | UNINTERPRETED_SORT -> (((new uninterpreted_sort ctx)#cnstr_obj obj) :> sort)
    | FINITE_DOMAIN_SORT -> (((new finite_domain_sort ctx)#cnstr_obj obj) :> sort)
    | RELATION_SORT -> (((new relation_sort ctx)#cnstr_obj obj) :> sort)
    | UNKNOWN_SORT -> raise (Z3native.Exception "Unknown sort kind encountered")

(** AST vector objects *)
class ast_vector ctx =
object (self)
  inherit z3object ctx None
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method incref nc o = Z3native.ast_vector_inc_ref nc o
  method decref nc o = Z3native.ast_vector_dec_ref nc o
end


(** AST map objects *)
class ast_map ctx =
object (self)
  inherit z3object ctx None
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method incref nc o = Z3native.ast_map_inc_ref nc o
  method decref nc o = Z3native.ast_map_dec_ref nc o
end


(** Expression objects *)
class expr ctx =
object(self)
  inherit ast ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self    
end

let expraton (a : expr array) =
  let f (e : expr) = e#gno in 
  Array.map f a

(** Boolean expression objects *)
class bool_expr ctx =
object (self)
  inherit expr ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Arithmetic expression objects (int/real) *)
class arith_expr ctx =
object (self)
  inherit expr ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Int expression objects *)
class int_expr ctx =
object (self)
  inherit arith_expr ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Real expression objects *)
class real_expr ctx =
object (self)
  inherit arith_expr ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Bit-vector expression objects *)
class bitvec_expr ctx =
object (self)
  inherit expr ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Array expression objects *)
class array_expr ctx =
object (self)
  inherit expr ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Datatype expression objects *)
class datatype_expr ctx =
object (self)
  inherit expr ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Integer numeral expression objects *)
class int_num ctx =
object (self)
  inherit int_expr ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Rational numeral expression objects *)
class rat_num ctx =
object (self)
  inherit real_expr ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Bit-vector numeral expression objects *)
class bitvec_num ctx =
object (self)
  inherit bitvec_expr ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Algebraic numeral expression objects *)
class algebraic_num ctx =
object (self)
  inherit arith_expr ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Quantifier objects *)
class quantifier ctx =
object (self)
  inherit expr ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

(** Quantifier pattern objects *)
class pattern ctx =
object (self)
  inherit ast ctx as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
end

let patternaton (a : pattern array) =
  let f (e : pattern) = e#gno in 
  Array.map f a

(** Parameter description objects *)
class param_descrs ctx =
object (self)
  inherit z3object ctx None as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method incref nc o = Z3native.param_descrs_inc_ref nc o
  method decref nc o = Z3native.param_descrs_dec_ref nc o
end

(** Goal objects *)
class goal ctx =
object (self)
  inherit z3object ctx None as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method incref nc o = Z3native.goal_inc_ref nc o
  method decref nc o = Z3native.goal_dec_ref nc o
end

(** Tactic objects *)
class tactic ctx =
object (self)
  inherit z3object ctx None as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method incref nc o = Z3native.tactic_inc_ref nc o
  method decref nc o = Z3native.tactic_dec_ref nc o
end

let tacticaton (a : tactic array) =
  let f (e : tactic) = e#gno in 
  Array.map f a

(** Function interpretation entry objects *)
class func_entry ctx =
object (self)
  inherit z3object ctx None as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method incref nc o = Z3native.func_entry_inc_ref nc o
  method decref nc o = Z3native.func_entry_dec_ref nc o
end

(** Function interpretation objects *)
class func_interp ctx =
object (self)
  inherit z3object ctx None as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method incref nc o = Z3native.func_interp_inc_ref nc o
  method decref nc o = Z3native.func_interp_dec_ref nc o
end

(** Tactic application result objects *)
class apply_result ctx =
object (self)
  inherit z3object ctx None as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method incref nc o = Z3native.apply_result_inc_ref nc o
  method decref nc o = Z3native.apply_result_dec_ref nc o
end

(** Probe objects *)
class probe ctx =
object (self)
  inherit z3object ctx None as super
  method cnstr_obj obj = (self#sno ctx obj) ; self
  method incref nc o = Z3native.probe_inc_ref nc o
  method decref nc o = Z3native.probe_dec_ref nc o
end

(** Statistical value objects *)
class statistics_entry =
object (self)  
  val mutable m_key : string = ""
  val mutable m_is_int = false
  val mutable m_is_float = false
  val mutable m_int = 0
  val mutable m_float = 0.0
    
  method cnstr_si k v = 
    m_key <- k;
    m_is_int <- true;
    m_int <- v;
    self
      
  method cnstr_sd k v = 
    m_key <- k;
    m_is_float <- true;
    m_float <- v;
    self

  method key = m_key
  method int = m_int
  method float = m_float
  method is_int = m_is_int
  method is_float = m_is_float
end


type z3_native_object = { 
  m_ctx : context ; 
  mutable m_n_obj : Z3native.ptr ; 
  inc_ref : Z3native.z3_context -> Z3native.ptr -> unit;
  dec_ref : Z3native.z3_context -> Z3native.ptr -> unit }

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
    
let z3obj_cnstr o = 
  let f = fun o -> (z3obj_dispose o) in
  Gc.finalise f o

(**/**)


(** Interaction logging for Z3

    Note that this is a global, static log and if multiple Context 
    objects are created, it logs the interaction with all of them. *)
module Log = 
struct
  (** Open an interaction log file. 
      @param filename the name of the file to open.
      @return True if opening the log file succeeds, false otherwise.
  *)
  (* CMW: "open" seems to be a reserved keyword? *)
  let open_ filename = ((lbool_of_int (Z3native.open_log filename)) == L_TRUE)

  (** Closes the interaction log. *)
  let close = Z3native.close_log

  (** Appends a user-provided string to the interaction log.
      @param s the string to append*)
  let append s = Z3native.append_log s
end

(** Version information *)
module Version =
struct
  (** The major version. *)
  let major = let (x, _, _, _) = Z3native.get_version in x

  (** The minor version. *)
  let minor = let (_, x, _, _) = Z3native.get_version in x

  (** The build version. *)
  let build = let (_, _, x, _) = Z3native.get_version in x

  (** The revision. *)
  let revision = let (_, _, _, x) = Z3native.get_version in x

  (** A string representation of the version information. *)
  let to_string = 
    let (mj, mn, bld, rev) = Z3native.get_version in
    string_of_int mj ^ "." ^
      string_of_int mn ^ "." ^
      string_of_int bld ^ "." ^
      string_of_int rev ^ "."
end

(** Symbols are used to name several term and type constructors *)
module Symbol =
struct	
  (** The kind of the symbol (int or string) *)
  let kind (o : symbol) = (symbol_kind_of_int (Z3native.get_symbol_kind o#gnc o#gno))

  (** Indicates whether the symbol is of Int kind *)
  let is_int_symbol (o : symbol) = (kind o) == INT_SYMBOL

  (** Indicates whether the symbol is of string kind. *)
  let is_string_symbol (o : symbol) = (kind o) == STRING_SYMBOL

  (** The int value of the symbol. *)
  let get_int (o : int_symbol) = Z3native.get_symbol_int o#gnc o#gno

  (** The string value of the symbol. *)
  let get_string (o : string_symbol) = Z3native.get_symbol_string o#gnc o#gno

  (** A string representation of the symbol. *)
  let to_string (o : symbol) = 
    match (kind o) with
      | INT_SYMBOL -> (string_of_int (Z3native.get_symbol_int o#gnc o#gno))
      | STRING_SYMBOL -> (Z3native.get_symbol_string o#gnc o#gno)

  (**
     Creates a new symbol using an integer.
     
     Not all integers can be passed to this function.
     The legal range of unsigned integers is 0 to 2^30-1.
  *)
  let mk_int ( ctx : context ) i = 
    (new int_symbol ctx)#cnstr_int i
      
  (** Creates a new symbol using a string. *)
  let mk_string ( ctx : context ) s =
    (new string_symbol ctx)#cnstr_string s

  (**
     Create an array of symbols.
  *)
  let mk_ints ( ctx : context ) ( names : int array ) =
    let f elem = mk_int ( ctx : context ) elem in
    (Array.map f names)

  (**
     Create an array of symbols.
  *)
  let mk_strings ( ctx : context ) ( names : string array ) =
    let f elem = mk_string ( ctx : context ) elem in
    (Array.map f names)      
end


(** The Sort module implements type information for ASTs *)
module Sort =
struct
  (**
     Comparison operator.
     @param a A sort
     @param b A sort
     @return True if <paramref name="a"/> and <paramref name="b"/> are from the same context 
     and represent the same sort; false otherwise.
  *)
  let ( = ) (a : sort) (b : sort) = (a == b) ||
    if a#gnc != b#gnc then 
      false 
    else 
      (Z3native.is_eq_sort a#gnc a#gno b#gno)
	
  (**
     Returns a unique identifier for the sort.
  *)
  let get_id (x : sort) = Z3native.get_sort_id x#gnc x#gno
    
  (**
     The kind of the sort.
  *)
  let get_sort_kind (x : sort) = (sort_kind_of_int (Z3native.get_sort_kind x#gnc x#gno))

  (**
     The name of the sort
  *)
  let get_name (x : sort) = (create_symbol x#gc (Z3native.get_sort_name x#gnc x#gno))    
    
  (**
     A string representation of the sort.
  *)
  let to_string (x : sort) = Z3native.sort_to_string x#gnc x#gno

  (**
     Create a new Boolean sort.
  *)
  let mk_bool ( ctx : context ) =
    (new bool_sort ctx)#cnstr_obj (Z3native.mk_bool_sort (context_gno ctx))
      
  (**
     Create a new uninterpreted sort.
  *)
  let mk_uninterpreted ( ctx : context ) (s : symbol) =
    (new uninterpreted_sort ctx)#cnstr_s s

  (**
     Create a new uninterpreted sort.
  *)
  let mk_uninterpreted_s ( ctx : context ) (s : string) =
    mk_uninterpreted ctx ((Symbol.mk_string ( ctx : context ) s) :> symbol)
end 

(**/**)
let create_expr ctx obj =
  if ast_kind_of_int (Z3native.get_ast_kind (context_gno ctx) obj) == QUANTIFIER_AST then
    (((new quantifier ctx)#cnstr_obj obj) :> expr)
  else
    let s = Z3native.get_sort (context_gno ctx) obj in
    let sk = (sort_kind_of_int (Z3native.get_sort_kind (context_gno ctx) s)) in    
    if (Z3native.is_algebraic_number (context_gno ctx) obj) then
      (((new algebraic_num ctx)#cnstr_obj obj) :> expr)
    else
      if (Z3native.is_numeral_ast (context_gno ctx) obj) &&
	(sk == INT_SORT or sk == REAL_SORT or sk == BV_SORT) then
	match sk with
	  | INT_SORT -> (((new int_num ctx)#cnstr_obj obj) :> expr)
          | REAL_SORT -> (((new rat_num ctx)#cnstr_obj obj) :> expr)
          | BV_SORT -> (((new bitvec_num ctx)#cnstr_obj obj) :> expr)
	  | _ -> raise (Z3native.Exception "Unsupported numeral object")
      else
	match sk with
	  | BOOL_SORT -> (((new bool_expr ctx)#cnstr_obj obj) :> expr)
          | INT_SORT -> (((new int_expr ctx)#cnstr_obj obj) :> expr)
          | REAL_SORT -> (((new real_expr ctx)#cnstr_obj obj) :> expr)
	  | BV_SORT -> (((new bitvec_expr ctx)#cnstr_obj obj) :> expr)
          | ARRAY_SORT -> (((new array_expr ctx)#cnstr_obj obj) :> expr)
          | DATATYPE_SORT -> (((new datatype_expr ctx)#cnstr_obj obj) :> expr)
          | _ -> (new expr ctx)#cnstr_obj obj

let create_expr_fa (ctx : context) (f : func_decl) (args : expr array) =
  let o = Z3native.mk_app (context_gno ctx) f#gno (Array.length args) (astaton args) in
  create_expr ctx o

let create_ast ctx no =
  match (ast_kind_of_int (Z3native.get_ast_kind (context_gno ctx) no)) with
    | FUNC_DECL_AST -> (((new func_decl ctx)#cnstr_obj no) :> ast)
    | QUANTIFIER_AST -> (((new quantifier ctx)#cnstr_obj no) :> ast)
    | SORT_AST -> ((create_sort ctx no) :> ast)
    | APP_AST
    | NUMERAL_AST
    | VAR_AST -> ((create_expr ctx no) :> ast)
    | UNKNOWN_AST -> raise (Z3native.Exception "Cannot create asts of type unknown")
(**/**)

(** Function declarations *)
module FuncDecl =
struct
  (** Parameters of Func_Decls *)
  module Parameter =
  struct
    (**
       The kind of the parameter.
    *)
    let get_kind (x : parameter) = x#kind

    (**The int value of the parameter.*)
    let get_int (x : parameter) = 
      if (x#kind != PARAMETER_INT) then 
	raise (Z3native.Exception "parameter is not an int") 
      else 
	x#int

    (**The double value of the parameter.*)
    let get_double (x : parameter) = 
      if (x#kind != PARAMETER_DOUBLE) then 
	raise (Z3native.Exception "parameter is not a double") 
      else 
	x#double

    (**The Symbol value of the parameter.*)
    let get_symbol (x : parameter) = 
      if (x#kind != PARAMETER_SYMBOL) then 
	raise (Z3native.Exception "parameter is not a symbol") 
      else 
	x#symbol

    (**The Sort value of the parameter.*)
    let get_sort (x : parameter) = 
      if (x#kind != PARAMETER_SORT) then 
	raise (Z3native.Exception "parameter is not a sort") 
      else 
	x#sort

    (**The AST value of the parameter.*)
    let get_ast (x : parameter) = 
      if (x#kind != PARAMETER_AST) then 
	raise (Z3native.Exception "parameter is not an ast") 
      else 
	x#ast

    (**The FunctionDeclaration value of the parameter.*)
    let get_ast (x : parameter) = 
      if (x#kind != PARAMETER_FUNC_DECL) then 
	raise (Z3native.Exception "parameter is not an function declaration") 
      else 
	x#func_decl

    (**The rational string value of the parameter.*)
    let get_rational (x : parameter) = 
      if (x#kind != PARAMETER_RATIONAL) then 
	raise (Z3native.Exception "parameter is not a ratinoal string") 
      else 
	x#rational
  end

    (**
       Creates a new function declaration.
    *)
    let mk_func_decl ( ctx : context ) ( name : symbol ) ( domain : sort array ) ( range : sort) =
      (new func_decl ctx)#cnstr_ndr name domain range

    (**
       Creates a new function declaration.
    *)
    let mk_func_decl_s ( ctx : context ) ( name : string ) ( domain : sort array ) ( range : sort) =
      mk_func_decl ctx ((Symbol.mk_string ctx name) :> symbol) domain range

    (**
       Creates a fresh function declaration with a name prefixed with <paramref name="prefix"/>.
       <seealso cref="MkFunc_Decl(string,Sort,Sort)"/>
       <seealso cref="MkFunc_Decl(string,Sort[],Sort)"/>
    *)
    let mk_fresh_func_decl ( ctx : context ) ( prefix : string ) ( domain : sort array ) ( range : sort) =
      (new func_decl ctx)#cnstr_pdr prefix domain range

    (**
       Creates a new constant function declaration.
    *)
    let mk_const_decl ( ctx : context ) ( name : symbol ) ( range : sort) =
      (new func_decl ctx)#cnstr_ndr name [||]  range


    (**
       Creates a new constant function declaration.
    *)
    let mk_const_decl_s ( ctx : context ) ( name : string ) ( range : sort) =
      (new func_decl ctx)#cnstr_ndr ((Symbol.mk_string ctx name) :> symbol) [||]  range

    (**
       Creates a fresh constant function declaration with a name prefixed with <paramref name="prefix"/>.
       <seealso cref="MkFunc_Decl(string,Sort,Sort)"/>
       <seealso cref="MkFunc_Decl(string,Sort[],Sort)"/>
    *)
    let mk_fresh_const_decl ( ctx : context ) ( prefix : string ) ( range : sort) =
      (new func_decl ctx)#cnstr_pdr prefix [||] range


  (**
     Comparison operator.
     @param a A func_decl
     @param b A func_decl
     @return True if <paramref name="a"/> and <paramref name="b"/> are from the same context 
     and represent the same func_decl; false otherwise.
  *)
  let ( = ) (a : func_decl) (b : func_decl) = (a == b) ||
    if a#gnc == a#gnc then 
      false 
    else 
      (Z3native.is_eq_func_decl a#gnc a#gno b#gno)
  (**
     A string representations of the function declaration.
  *)
  let to_string (x : func_decl) = Z3native.func_decl_to_string x#gnc x#gno
    
  (**
     Returns a unique identifier for the function declaration.
  *)
  let get_id (x : func_decl) = Z3native.get_func_decl_id x#gnc x#gno
    
  (**
     The arity of the function declaration
  *)
  let get_arity (x : func_decl) = Z3native.get_arity x#gnc x#gno
    
  (**
     The size of the domain of the function declaration
     <seealso cref="Arity"/>
  *)
  let get_domain_size (x : func_decl) = Z3native.get_domain_size x#gnc x#gno
    
  (**
     The domain of the function declaration
  *)
  let get_domain (x : func_decl) = 
    let n = (get_domain_size x) in
    let f i = create_sort x#gc (Z3native.get_domain x#gnc x#gno i) in
    Array.init n f
      
  (**
     The range of the function declaration
  *)
  let get_range (x : func_decl) = 
    create_sort x#gc (Z3native.get_range x#gnc x#gno)
      
  (**
     The kind of the function declaration.
  *)
  let get_decl_kind (x : func_decl) = (decl_kind_of_int (Z3native.get_decl_kind x#gnc x#gno))

  (**
     The name of the function declaration
  *)
  let get_name (x : func_decl) = (create_symbol x#gc (Z3native.get_decl_name x#gnc x#gno))

  (**
     The number of parameters of the function declaration
  *)
  let get_num_parameters (x : func_decl) = (Z3native.get_decl_num_parameters x#gnc x#gno)

  (**
     The parameters of the function declaration
  *)
  let get_parameters (x : func_decl) = 
    let n = (get_num_parameters x) in
    let f i = (
      match (parameter_kind_of_int (Z3native.get_decl_parameter_kind x#gnc x#gno i)) with
	| PARAMETER_INT -> (new parameter)#cnstr_int (Z3native.get_decl_int_parameter x#gnc x#gno i)
	| PARAMETER_DOUBLE -> (new parameter)#cnstr_double (Z3native.get_decl_double_parameter x#gnc x#gno i)
	| PARAMETER_SYMBOL-> (new parameter)#cnstr_symbol (Some (create_symbol x#gc (Z3native.get_decl_symbol_parameter x#gnc x#gno i)))
        | PARAMETER_SORT -> (new parameter)#cnstr_sort (Some (create_sort x#gc (Z3native.get_decl_sort_parameter x#gnc x#gno i)))
	| PARAMETER_AST -> (new parameter)#cnstr_ast (Some (create_ast x#gc (Z3native.get_decl_ast_parameter x#gnc x#gno i)))
        | PARAMETER_FUNC_DECL -> (new parameter)#cnstr_func_decl (Some ((new func_decl x#gc)#cnstr_obj (Z3native.get_decl_func_decl_parameter x#gnc x#gno i)))
        | PARAMETER_RATIONAL -> (new parameter)#cnstr_rational (Z3native.get_decl_rational_parameter x#gnc x#gno i)
    ) in
    Array.init n f                         

  (**
     Create expression that applies function to arguments.
     @param args The arguments
  *)	   
  let apply (x : func_decl) (args : expr array) = create_expr_fa x#gc x args

end

(** The abstract syntax tree (AST) module *)
module AST =
struct
  (** Vectors of ASTs *)
  module ASTVector = 
  struct
    (** The size of the vector *)
    let get_size ( x : ast_vector ) =
      Z3native.ast_vector_size x#gnc x#gno

    (** 
	Retrieves the i-th object in the vector.
	@param i Index
	@return An AST
    *)
    let get ( x : ast_vector ) ( i : int ) =
      create_ast x#gc (Z3native.ast_vector_get x#gnc x#gno i)

    (** Sets the i-th object in the vector. *)
    let set ( x : ast_vector ) ( i : int ) ( value : ast ) =
      Z3native.ast_vector_set x#gnc x#gno i value#gno

    (** Resize the vector to <paramref name="newSize"/>. 
	@param newSize The new size of the vector. *)
    let resize ( x : ast_vector ) ( new_size : int ) =
      Z3native.ast_vector_resize x#gnc x#gno new_size
	
    (**
       Add the AST <paramref name="a"/> to the back of the vector. The size
       is increased by 1.
       @param a An AST
    *)
    let push ( x : ast_vector ) ( a : ast )  =
      Z3native.ast_vector_push x#gnc x#gno a#gno
	
    (**
       Translates all ASTs in the vector to <paramref name="to_ctx"/>.
       @param to_ctx A context
       @return A new ASTVector
    *)
    let translate ( x : ast_vector ) ( to_ctx : context ) =
      (new ast_vector to_ctx)#cnstr_obj (Z3native.ast_vector_translate x#gnc x#gno (context_gno to_ctx))
	
    (** Retrieves a string representation of the vector. *)    
    let to_string ( x : ast_vector ) =
      Z3native.ast_vector_to_string x#gnc x#gno
  end

  (**  Map from AST to AST *)
  module ASTMap =
  struct
    (** Checks whether the map contains the key <paramref name="k"/>.
	@param k An AST
	@return True if <paramref name="k"/> is a key in the map, false otherwise. *)
    let contains ( m : ast_map ) ( key : ast ) =
      (Z3native.ast_map_contains m#gnc m#gno key#gno)
	
    (** Finds the value associated with the key <paramref name="k"/>.
	<remarks>
	This function signs an error when <paramref name="k"/> is not a key in the map.
	@param k An AST 
    *)
    let find ( m : ast_map ) ( key : ast ) =
      create_ast m#gc (Z3native.ast_map_find m#gnc m#gno key#gno)
	
    (**
       Stores or replaces a new key/value pair in the map.
       @param k The key AST
       @param v The value AST
    *)
    let insert ( m : ast_map ) ( key : ast ) ( value : ast) =
      Z3native.ast_map_insert m#gnc m#gno key#gno value#gno

    (**
       Erases the key <paramref name="k"/> from the map.
       @param k An AST
    *)
    let erase ( m : ast_map ) ( key : ast ) =
      Z3native.ast_map_erase m#gnc m#gno key#gno
	
    (**  Removes all keys from the map. *)
    let reset ( m : ast_map ) =
      Z3native.ast_map_reset m#gnc m#gno

    (** The size of the map *)
    let get_size ( m : ast_map ) =
      Z3native.ast_map_size m#gnc m#gno
	
    (** The keys stored in the map. *)
    let get_keys ( m : ast_map ) =
      (new ast_vector m#gc)#cnstr_obj (Z3native.ast_map_keys m#gnc m#gno)

    (** Retrieves a string representation of the map.*)
    let to_strnig ( m : ast_map ) =
      Z3native.ast_map_to_string m#gnc m#gno
  end

  (**
     The AST's hash code.
     @return A hash code
  *)
  let get_hash_code ( x : ast) = Z3native.get_ast_hash x#gnc x#gno

  (**
     A unique identifier for the AST (unique among all ASTs).
  *)
  let get_id ( x : ast) = Z3native.get_ast_id x#gnc x#gno

  (**
     The kind of the AST.
  *)    
  let get_ast_kind ( x : ast) = (ast_kind_of_int (Z3native.get_ast_kind x#gnc x#gno))
    
  (**
     Indicates whether the AST is an Expr
  *)
  let is_expr ( x : ast) = 
    match get_ast_kind ( x : ast) with
      | APP_AST
      | NUMERAL_AST
      | QUANTIFIER_AST
      | VAR_AST -> true
      | _ -> false
	
  (**
     Indicates whether the AST is a bound variable
  *)
  let is_var ( x : ast) = (get_ast_kind x) == VAR_AST   

  (**
     Indicates whether the AST is a Quantifier
  *)
  let is_quantifier ( x : ast) = (get_ast_kind x) == QUANTIFIER_AST


  (**
     Indicates whether the AST is a Sort
  *)
  let is_sort ( x : ast) = (get_ast_kind x) == SORT_AST

  (**
     Indicates whether the AST is a FunctionDeclaration
  *)
  let is_func_decl ( x : ast) = (get_ast_kind x) == FUNC_DECL_AST

  (**
     A string representation of the AST.
  *)
  let to_string ( x : ast) = Z3native.ast_to_string x#gnc x#gno

  (**
     A string representation of the AST in s-expression notation.
  *)
  let to_sexpr ( x : ast) = Z3native.ast_to_string x#gnc x#gno

  (**
     Comparison operator.
     @param a An AST
     @param b An AST
     @return True if <paramref name="a"/> and <paramref name="b"/> are from the same context 
     and represent the same sort; false otherwise.
  *)
  let ( = ) (a : expr) (b : expr) = (a == b) ||
    if a#gnc == b#gnc then 
      false 
    else 
      (Z3native.is_eq_ast a#gnc a#gno b#gno)
	
  (**
     Object Comparison.
     @param other Another ast
     @return Negative if the object should be sorted before <paramref name="other"/>, positive if after else zero.
  *)
  let compare a b = 
    if (get_id a) < (get_id b) then -1 else
      if (get_id a) > (get_id b) then 1 else
	0
	  
  (** Operator < *)
  let ( < ) (a : ast) (b : ast) = (compare a b)
    
  (**
     Translates (copies) the AST to the Context <paramref name="ctx"/>.
     @param ctx A context
     @return A copy of the AST which is associated with <paramref name="ctx"/>
  *)
  let translate ( x : ast) to_ctx = 
    if x#gc == to_ctx then 
      x
    else
      (create_ast to_ctx (Z3native.translate x#gnc x#gno (context_gno to_ctx)))

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
  let wrap ( ctx : context ) ( ptr : Z3native.ptr ) =
      create_ast ctx ptr

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
  let unwrap_ast ( a : ast ) = a#gno
end

(** General expressions (terms), including Boolean logic *)
module Expr =
struct
  (**
     Returns a simplified version of the expression.
     @param p A set of parameters to configure the simplifier
     <seealso cref="Context.SimplifyHelp"/>
  *)
  let simplify ( x : expr ) ( p : params option ) = match p with 
    | None -> create_expr x#gc (Z3native.simplify x#gnc x#gno)
    | Some pp -> create_expr x#gc (Z3native.simplify_ex x#gnc x#gno pp#gno)
      
(**
   a string describing all available parameters to <c>Expr.Simplify</c>.
*)
  let get_simplify_help ( ctx : context ) =
    Z3native.simplify_get_help (context_gno ctx)

(**
   Retrieves parameter descriptions for simplifier.
*)
   let get_simplify_parameter_descrs ( ctx : context ) = 
     (new param_descrs ctx)#cnstr_obj (Z3native.simplify_get_param_descrs (context_gno ctx))

  (**
     The function declaration of the function that is applied in this expression.
  *)
  let get_func_decl ( x : expr ) = (new func_decl x#gc)#cnstr_obj (Z3native.get_app_decl x#gnc x#gno)
    
  (**
     Indicates whether the expression is the true or false expression
     or something else (L_UNDEF).
  *)
  let get_bool_value ( x : expr ) = lbool_of_int (Z3native.get_bool_value x#gnc x#gno)

  (**
     The number of arguments of the expression.
  *)
  let get_num_args ( x : expr ) = Z3native.get_app_num_args x#gnc x#gno
    
  (**
     The arguments of the expression.
  *)        
  let get_args ( x : expr ) = let n = (get_num_args x) in
			      let f i = create_expr x#gc (Z3native.get_app_arg x#gnc x#gno i) in
			      Array.init n f
				
  (**
     Update the arguments of the expression using the arguments <paramref name="args"/>
     The number of new arguments should coincide with the current number of arguments.
  *)
  let update ( x : expr ) args =
    if (Array.length args <> (get_num_args x)) then
      raise (Z3native.Exception "Number of arguments does not match")
    else
      x#sno x#gc (Z3native.update_term x#gnc x#gno (Array.length args) (expraton args))

  (**
     Substitute every occurrence of <c>from[i]</c> in the expression with <c>to[i]</c>, for <c>i</c> smaller than <c>num_exprs</c>.
     <remarks>
     The result is the new expression. The arrays <c>from</c> and <c>to</c> must have size <c>num_exprs</c>.
     For every <c>i</c> smaller than <c>num_exprs</c>, we must have that 
     sort of <c>from[i]</c> must be equal to sort of <c>to[i]</c>.
  *)
  let substitute ( x : expr ) from to_ = 
    if (Array.length from) <> (Array.length to_) then
      raise (Z3native.Exception "Argument sizes do not match")
    else
      create_expr x#gc (Z3native.substitute x#gnc x#gno (Array.length from) (expraton from) (expraton to_))
	
  (**
     Substitute every occurrence of <c>from</c> in the expression with <c>to</c>.
     <seealso cref="Substitute(Expr[],Expr[])"/>
  *)
  let substitute_one ( x : expr ) from to_ =
    substitute ( x : expr ) [| from |] [| to_ |]
      
  (**
     Substitute the free variables in the expression with the expressions in <paramref name="to"/>
     <remarks>
     For every <c>i</c> smaller than <c>num_exprs</c>, the variable with de-Bruijn index <c>i</c> is replaced with term <c>to[i]</c>.
  *)
  let substitute_vars ( x : expr ) to_ =
    create_expr x#gc (Z3native.substitute_vars x#gnc x#gno (Array.length to_) (expraton to_))
      

  (**
     Translates (copies) the term to the Context <paramref name="ctx"/>.
     @param ctx A context
     @return A copy of the term which is associated with <paramref name="ctx"/>
  *)
  let translate ( x : expr ) to_ctx =
    if x#gc == to_ctx then
      x
    else
      create_expr to_ctx (Z3native.translate x#gnc x#gno (context_gno to_ctx))

  (**
     Returns a string representation of the expression.
  *)    
  let to_string ( x : expr ) = Z3native.ast_to_string x#gnc x#gno

  (**
     Indicates whether the term is a numeral
  *)
  let is_numeral ( x : expr ) = (Z3native.is_numeral_ast x#gnc x#gno)
    
  (**
     Indicates whether the term is well-sorted.
     @return True if the term is well-sorted, false otherwise.
  *)   
  let is_well_sorted ( x : expr ) = Z3native.is_well_sorted x#gnc x#gno

  (**
     The Sort of the term.
  *)
  let get_sort ( x : expr ) = create_sort x#gc (Z3native.get_sort x#gnc x#gno)
    
  (**
     Indicates whether the term has Boolean sort.
  *)
  let is_bool ( x : expr ) = (AST.is_expr x) &&
    (Z3native.is_eq_sort x#gnc 
       (Z3native.mk_bool_sort x#gnc)
       (Z3native.get_sort x#gnc x#gno))

  (**
     Indicates whether the term represents a constant.
  *)
  let is_const ( x : expr ) = (AST.is_expr x) &&
    (get_num_args x) == 0 &&
    FuncDecl.get_domain_size(get_func_decl x) == 0
    
  (**
     Indicates whether the term is the constant true.
  *)
  let is_true ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_TRUE)

  (**
     Indicates whether the term is the constant false.
  *)
  let is_false ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_FALSE)

  (**
     Indicates whether the term is an equality predicate.
  *)
  let is_eq ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_EQ)

  (**
     Indicates whether the term is an n-ary distinct predicate (every argument is mutually distinct).
  *)
  let is_distinct ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_DISTINCT)

  (**
     Indicates whether the term is a ternary if-then-else term
  *)
  let is_ite ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_ITE)

  (**
     Indicates whether the term is an n-ary conjunction
  *)
  let is_and ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_AND)

  (**
     Indicates whether the term is an n-ary disjunction
  *)
  let is_or ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_OR)

  (**
     Indicates whether the term is an if-and-only-if (Boolean equivalence, binary)
  *)
  let is_iff ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_IFF)

  (**
     Indicates whether the term is an exclusive or
  *)
  let is_xor ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_XOR)

  (**
     Indicates whether the term is a negation
  *)
  let is_not ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_NOT)

  (**
     Indicates whether the term is an implication
  *)
  let is_implies ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_IMPLIES)

  (**
     Indicates whether the term is a label (used by the Boogie Verification condition generator).
     <remarks>The label has two parameters, a string and a Boolean polarity. It takes one argument, a formula.
  *)
  let is_label ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_LABEL)

  (**
     Indicates whether the term is a label literal (used by the Boogie Verification condition generator).                     
     <remarks>A label literal has a set of string parameters. It takes no arguments.
     let is_label_lit ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_LABEL_LIT)
  *)

  (**
     Indicates whether the term is a binary equivalence modulo namings. 
     <remarks>This binary predicate is used in proof terms.
     It captures equisatisfiability and equivalence modulo renamings.
  *)
  let is_oeq ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_OEQ)

  (**
     Creates a new Constant of sort <paramref name="range"/> and named <paramref name="name"/>.
  *)
  let mk_const ( ctx : context ) ( name : symbol ) ( range : sort ) =
    create_expr ctx (Z3native.mk_const (context_gno ctx) name#gno range#gno)
      

  (**
     Creates a new Constant of sort <paramref name="range"/> and named <paramref name="name"/>.
  *)
  let mk_const_s ( ctx : context ) ( name : string ) ( range : sort ) =
    mk_const ctx ((Symbol.mk_string ctx name) :> symbol) range


  (**
     Creates a  constant from the func_decl  <paramref name="f"/>.
     @param f An expression of a 0-arity function
  *)
  let mk_const_f ( ctx : context ) ( f : func_decl ) =
    create_expr_fa ctx f [||]

  (**
     Creates a fresh constant of sort <paramref name="range"/> and a 
     name prefixed with <paramref name="prefix"/>.
  *)
  let mk_fresh_const ( ctx : context ) ( prefix : string ) ( range : sort) =
    create_expr ctx (Z3native.mk_fresh_const (context_gno ctx) prefix range#gno)

  (**
     Create a Boolean constant.
  *)        
  let mk_bool_const ( ctx : context ) ( name : symbol ) =
    ((mk_const ctx name (Sort.mk_bool ctx)) :> bool_expr)
      
  (**
     Create a Boolean constant.
  *)        
  let mk_bool_const_s ( ctx : context ) ( name : string ) =
    mk_bool_const ctx ((Symbol.mk_string ctx name) :> symbol)

  (**
     Create a new function application.
  *)
  let mk_app ( ctx : context ) ( f : func_decl ) ( args : expr array ) =
    create_expr_fa ctx f args

  (**
     The true Term.
  *)    
  let mk_true ( ctx : context ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_true (context_gno ctx))

  (**
     The false Term.
  *)    
  let mk_false ( ctx : context ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_false (context_gno ctx))

  (**
     Creates a Boolean value.
  *)        
  let mk_bool ( ctx : context ) ( value : bool) =
    if value then mk_true ctx else mk_false ctx

  (**
     Creates the equality <paramref name="x"/> = <paramref name="y"/>.
  *)
  let mk_eq ( ctx : context ) ( x : expr ) ( y : expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_eq (context_gno ctx) x#gno y#gno)

  (**
     Creates a <c>distinct</c> term.
  *)
  let mk_distinct ( ctx : context ) ( args : expr array ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_distinct (context_gno ctx) (Array.length args) (astaton args))
      
  (**
     Mk an expression representing <c>not(a)</c>.
  *)    
  let mk_not ( ctx : context ) ( a : bool_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_not (context_gno ctx) a#gno)

  (**    
	 Create an expression representing an if-then-else: <c>ite(t1, t2, t3)</c>.
	 @param t1 An expression with Boolean sort
	 @param t2 An expression 
	 @param t3 An expression with the same sort as <paramref name="t2"/>
  *)
  let mk_ite ( ctx : context ) ( t1 : bool_expr ) ( t2 : bool_expr ) ( t3 : bool_expr ) =
    create_expr ctx (Z3native.mk_ite (context_gno ctx) t1#gno t2#gno t3#gno)
      
  (**
     Create an expression representing <c>t1 iff t2</c>.
  *)
  let mk_iff ( ctx : context ) ( t1 : bool_expr ) ( t2 : bool_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_iff (context_gno ctx) t1#gno t2#gno)

  (**
     Create an expression representing <c>t1 -> t2</c>.
  *)
  let mk_implies ( ctx : context ) ( t1 : bool_expr ) ( t2 : bool_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_implies (context_gno ctx) t1#gno t2#gno)

  (**
     Create an expression representing <c>t1 xor t2</c>.
  *)
  let mk_xor ( ctx : context ) ( t1 : bool_expr ) ( t2 : bool_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_xor (context_gno ctx) t1#gno t2#gno)

  (**
     Create an expression representing the AND of args
  *)
  let mk_and ( ctx : context ) ( args : bool_expr array ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_and (context_gno ctx) (Array.length args) (astaton args))

  (**
     Create an expression representing the OR of args
  *)
  let mk_or ( ctx : context ) ( args : bool_expr array ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_or (context_gno ctx) (Array.length args) (astaton args))

  (**
     Create a numeral of a given sort.         
     @param v A string representing the Term value in decimal notation. If the given sort is a real, then the Term can be a rational, that is, a string of the form <c>[num]* / [num]*</c>.
     @param ty The sort of the numeral. In the current implementation, the given sort can be an int, real, or bit-vectors of arbitrary size. 
     @return A Term with value <paramref name="v"/> and sort <paramref name="ty"/> 
  *)
  let mk_numeral_string ( ctx : context ) ( v : string ) ( ty : sort ) =
    create_expr ctx (Z3native.mk_numeral (context_gno ctx) v ty#gno)

  (**
     Create a numeral of a given sort. This function can be use to create numerals that fit in a machine integer.
     It is slightly faster than <c>MakeNumeral</c> since it is not necessary to parse a string.       
     @param v Value of the numeral
     @param ty Sort of the numeral
     @return A Term with value <paramref name="v"/> and type <paramref name="ty"/>
  *)
  let mk_numeral_int ( ctx : context ) ( v : int ) ( ty : sort ) =
    create_expr ctx (Z3native.mk_int (context_gno ctx) v ty#gno)
end

(** Quantifier expressions *)
module Quantifiers =
struct
  (**
     The de-Burijn index of a bound variable.
     <remarks>
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
     index.
  *)
  let get_index ( x : expr ) = 
    if not (AST.is_var x) then
      raise (Z3native.Exception "Term is not a bound variable.")
    else
      Z3native.get_index_value x#gnc x#gno

  (** Quantifier patterns

      Patterns comprise a list of terms. The list should be
      non-empty.  If the list comprises of more than one term, it is
      also called a multi-pattern.
  *)
  module Pattern =
  struct
    (**
       The number of terms in the pattern.
    *)
    let get_num_terms ( x : pattern ) =
      Z3native.get_pattern_num_terms x#gnc x#gno
	
    (**
       The terms in the pattern.
    *)
    let get_terms ( x : pattern ) =
      let n = (get_num_terms x) in
      let f i = (create_expr x#gc (Z3native.get_pattern x#gnc x#gno i)) in
      Array.init n f
	
    (**
       A string representation of the pattern.
    *)
    let to_string ( x : pattern ) = Z3native.pattern_to_string x#gnc x#gno
  end

  (**
     Indicates whether the quantifier is universal.
  *)
  let is_universal ( x : quantifier ) =
    Z3native.is_quantifier_forall x#gnc x#gno
      
  (**
     Indicates whether the quantifier is existential.
  *)
  let is_existential ( x : quantifier ) = not (is_universal x)

  (**
     The weight of the quantifier.
  *)
  let get_weight ( x : quantifier ) = Z3native.get_quantifier_weight x#gnc x#gno
    
  (**
     The number of patterns.
  *)
  let get_num_patterns ( x : quantifier ) = Z3native.get_quantifier_num_patterns x#gnc x#gno
    
  (**
     The patterns.
  *)
  let get_patterns ( x : quantifier ) =
    let n = (get_num_patterns x) in
    let f i = ((new pattern x#gc)#cnstr_obj (Z3native.get_quantifier_pattern_ast x#gnc  x#gno i)) in
    Array.init n f
      
  (**
     The number of no-patterns.
  *)
  let get_num_no_patterns ( x : quantifier ) = Z3native.get_quantifier_num_no_patterns x#gnc x#gno
    
  (**
     The no-patterns.
  *)
  let get_no_patterns ( x : quantifier ) =
    let n = (get_num_patterns x) in
    let f i = ((new pattern x#gc)#cnstr_obj (Z3native.get_quantifier_no_pattern_ast x#gnc  x#gno i)) in
    Array.init n f
      
  (**
     The number of bound variables.
  *)
  let get_num_bound ( x : quantifier ) = Z3native.get_quantifier_num_bound x#gnc  x#gno
    
  (**
     The symbols for the bound variables.
  *)
  let get_bound_variable_names ( x : quantifier ) =
    let n = (get_num_bound x) in
    let f i = (create_symbol x#gc (Z3native.get_quantifier_bound_name x#gnc x#gno i)) in
    Array.init n f
      
  (**
     The sorts of the bound variables.
  *)
  let get_bound_variable_sorts ( x : quantifier ) =
    let n = (get_num_bound x) in
    let f i = (create_sort x#gc (Z3native.get_quantifier_bound_sort x#gnc x#gno i)) in
    Array.init n f
      
  (**
     The body of the quantifier.
  *)
  let get_body ( x : quantifier ) =
    (new bool_expr x#gc)#cnstr_obj (Z3native.get_quantifier_body x#gnc x#gno)  

  (**
     Creates a new bound variable.
     @param index The de-Bruijn index of the variable
     @param ty The sort of the variable
  *)
  let mk_bound ( ctx : context ) ( index : int ) ( ty : sort ) =
    create_expr ctx (Z3native.mk_bound (context_gno ctx) index ty#gno)

  (**
     Create a quantifier pattern.
  *)
  let mk_pattern ( ctx : context ) ( terms : expr array ) =
    if (Array.length terms) == 0 then
      raise (Z3native.Exception "Cannot create a pattern from zero terms")
    else
      (new pattern ctx)#cnstr_obj (Z3native.mk_pattern (context_gno ctx) (Array.length terms) (astaton terms))

  (**
     Create a universal Quantifier.
     <remarks>
     Creates a forall formula, where <paramref name="weight"/> is the weight, 
     <paramref name="patterns"/> is an array of patterns, <paramref name="sorts"/> is an array
     with the sorts of the bound variables, <paramref name="names"/> is an array with the
     'names' of the bound variables, and <paramref name="body"/> is the body of the
     quantifier. Quantifiers are associated with weights indicating
     the importance of using the quantifier during instantiation. 

     @param sorts the sorts of the bound variables.
     @param names names of the bound variables
     @param body the body of the quantifier.
     @param weight quantifiers are associated with weights indicating the importance of using the quantifier during instantiation. By default, pass the weight 0.
     @param patterns array containing the patterns created using <c>MkPattern</c>.
     @param noPatterns array containing the anti-patterns created using <c>MkPattern</c>.
     @param quantifierID optional symbol to track quantifier.
     @param skolemID optional symbol to track skolem constants.
  *)
  let mk_forall ( ctx : context ) ( sorts : sort array ) ( names : symbol array ) ( body : expr) ( weight : int option ) ( patterns : pattern array ) ( nopatterns : pattern array ) ( quantifier_id : symbol option ) ( skolem_id : symbol option ) =
    if (Array.length sorts) != (Array.length names) then
      raise (Z3native.Exception "Number of sorts does not match number of names")
    else if ((Array.length nopatterns) == 0 && quantifier_id == None && skolem_id == None) then
      (new quantifier ctx)#cnstr_obj (Z3native.mk_quantifier (context_gno ctx) true 
					(match weight with | None -> 1 | Some(x) -> x)
					(Array.length patterns) (patternaton patterns)
					(Array.length sorts) (astaton sorts)
					(astaton names)
					body#gno)
    else
      (new quantifier ctx)#cnstr_obj (Z3native.mk_quantifier_ex (context_gno ctx) true
					(match weight with | None -> 1 | Some(x) -> x)
					(match quantifier_id with | None -> null | Some(x) -> x#gno)
					(match skolem_id with | None -> null | Some(x) -> x#gno)
					(Array.length patterns) (patternaton patterns)
					(Array.length nopatterns) (patternaton nopatterns)
					(Array.length sorts) (astaton sorts)
					(astaton names)
					body#gno)

  (**
     Create a universal Quantifier.
  *)
  let mk_forall_const ( ctx : context ) ( bound_constants : expr array ) ( body : expr) ( weight : int option ) ( patterns : pattern array ) ( nopatterns : pattern array ) ( quantifier_id : symbol option ) ( skolem_id : symbol option ) =
    if ((Array.length nopatterns) == 0 && quantifier_id == None && skolem_id == None) then
      (new quantifier ctx)#cnstr_obj (Z3native.mk_quantifier_const (context_gno ctx) true
					(match weight with | None -> 1 | Some(x) -> x)
					(Array.length bound_constants) (expraton bound_constants)
					(Array.length patterns) (patternaton patterns)
					body#gno)
    else
      (new quantifier ctx)#cnstr_obj (Z3native.mk_quantifier_const_ex (context_gno ctx) true
					(match weight with | None -> 1 | Some(x) -> x)
					(match quantifier_id with | None -> null | Some(x) -> x#gno)
					(match skolem_id with | None -> null | Some(x) -> x#gno)
					(Array.length bound_constants) (expraton bound_constants)
					(Array.length patterns) (patternaton patterns)
					(Array.length nopatterns) (patternaton nopatterns)
					body#gno)
  (**
     Create an existential Quantifier.
     <seealso cref="MkForall(Sort[],Symbol[],Expr,uint,Pattern[],Expr[],Symbol,Symbol)"/>
  *)
  let mk_exists ( ctx : context ) ( sorts : sort array ) ( names : symbol array ) ( body : expr) ( weight : int option ) ( patterns : pattern array ) ( nopatterns : pattern array ) ( quantifier_id : symbol option ) ( skolem_id : symbol option ) =
    if (Array.length sorts) != (Array.length names) then
      raise (Z3native.Exception "Number of sorts does not match number of names")
    else if ((Array.length nopatterns) == 0 && quantifier_id == None && skolem_id == None) then
      (new quantifier ctx)#cnstr_obj (Z3native.mk_quantifier (context_gno ctx) false
					(match weight with | None -> 1 | Some(x) -> x)
					(Array.length patterns) (patternaton patterns)
					(Array.length sorts) (astaton sorts)
					(astaton names)
					body#gno)
    else
      (new quantifier ctx)#cnstr_obj (Z3native.mk_quantifier_ex (context_gno ctx) false
					(match weight with | None -> 1 | Some(x) -> x)
					(match quantifier_id with | None -> null | Some(x) -> x#gno)
					(match skolem_id with | None -> null | Some(x) -> x#gno)
					(Array.length patterns) (patternaton patterns)
					(Array.length nopatterns) (patternaton nopatterns)
					(Array.length sorts) (astaton sorts)
					(astaton names)
					body#gno)

  (**
     Create an existential Quantifier.
  *)
  let mk_exists_const ( ctx : context ) ( bound_constants : expr array ) ( body : expr) ( weight : int option ) ( patterns : pattern array ) ( nopatterns : pattern array ) ( quantifier_id : symbol option ) ( skolem_id : symbol option ) =
    if ((Array.length nopatterns) == 0 && quantifier_id == None && skolem_id == None) then
      (new quantifier ctx)#cnstr_obj (Z3native.mk_quantifier_const (context_gno ctx) false
					(match weight with | None -> 1 | Some(x) -> x)
					(Array.length bound_constants) (expraton bound_constants)
					(Array.length patterns) (patternaton patterns)
					body#gno)
    else
      (new quantifier ctx)#cnstr_obj (Z3native.mk_quantifier_const_ex (context_gno ctx) false
					(match weight with | None -> 1 | Some(x) -> x)
					(match quantifier_id with | None -> null | Some(x) -> x#gno)
					(match skolem_id with | None -> null | Some(x) -> x#gno)
					(Array.length bound_constants) (expraton bound_constants)
					(Array.length patterns) (patternaton patterns)
					(Array.length nopatterns) (patternaton nopatterns)
					body#gno)

  (**
     Create a Quantifier.
  *)
  let mk_quantifier ( ctx : context ) ( universal : bool ) ( sorts : sort array ) ( names : symbol array ) ( body : expr) ( weight : int option ) ( patterns : pattern array ) ( nopatterns : pattern array ) ( quantifier_id : symbol option ) ( skolem_id : symbol option ) =
    if (universal) then
      (mk_forall ctx sorts names body weight patterns nopatterns quantifier_id skolem_id)
    else
      (mk_exists ctx sorts names body weight patterns nopatterns quantifier_id skolem_id)


  (**
     Create a Quantifier.
  *)
  let mk_quantifier ( ctx : context ) ( universal : bool ) ( bound_constants : expr array ) ( body : expr) ( weight : int option ) ( patterns : pattern array ) ( nopatterns : pattern array ) ( quantifier_id : symbol option ) ( skolem_id : symbol option ) =
    if (universal) then
      mk_forall_const ctx bound_constants body weight patterns nopatterns quantifier_id skolem_id
    else
      mk_exists_const ctx bound_constants body weight patterns nopatterns quantifier_id skolem_id
end

(** Functions to manipulate Array expressions *)
module Arrays =
struct
  (**
     Create a new array sort.
  *)
  let mk_sort ( ctx : context ) domain range =
    (new array_sort ctx)#cnstr_dr domain range

  (**
     Indicates whether the term is an array store.        
     <remarks>It satisfies select(store(a,i,v),j) = if i = j then v else select(a,j). 
     Array store takes at least 3 arguments. 
  *)
  let is_store ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_STORE)

  (**
     Indicates whether the term is an array select.
  *)
  let is_select ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SELECT)

  (**
     Indicates whether the term is a constant array.        
     <remarks>For example, select(const(v),i) = v holds for every v and i. The function is unary.
  *)
  let is_constant_array ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_CONST_ARRAY)

  (**
     Indicates whether the term is a default array.        
     <remarks>For example default(const(v)) = v. The function is unary.
  *)
  let is_default_array ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ARRAY_DEFAULT)

  (**
     Indicates whether the term is an array map.     
     <remarks>It satisfies map[f](a1,..,a_n)[i] = f(a1[i],...,a_n[i]) for every i.
  *)
  let is_array_map ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ARRAY_MAP)

  (**
     Indicates whether the term is an as-array term.        
     <remarks>An as-array term is n array value that behaves as the function graph of the 
     function passed as parameter.
  *)
  let is_as_array ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_AS_ARRAY)       

  (**
     Indicates whether the term is of an array sort.
  *)
  let is_array ( x : expr ) =
    (Z3native.is_app x#gnc x#gno) &&
      ((sort_kind_of_int (Z3native.get_sort_kind x#gnc (Z3native.get_sort x#gnc x#gno))) == ARRAY_SORT)      

  (** The domain of the array sort. *)
  let get_domain (x : array_sort) = create_sort x#gc (Z3native.get_array_sort_domain x#gnc x#gno)

  (** The range of the array sort. *)
  let get_range (x : array_sort) = create_sort x#gc (Z3native.get_array_sort_range x#gnc x#gno)


  (**
     Create an array constant.
  *)        
  let mk_const ( ctx : context ) ( name : symbol ) ( domain : sort ) ( range : sort ) =	
    ((Expr.mk_const ctx name ((mk_sort ctx domain range) :> sort)) :> array_expr)
      
  (**
     Create an array constant.
  *)        
  let mk_const_s ( ctx : context ) ( name : string ) ( domain : sort ) ( range : sort ) =	
    mk_const ctx ((Symbol.mk_string ctx name) :> symbol) domain range
      
  (**
     Array read.       
     <remarks>
     The argument <c>a</c> is the array and <c>i</c> is the index 
     of the array that gets read.      
     
     The node <c>a</c> must have an array sort <c>[domain -> range]</c>, 
     and <c>i</c> must have the sort <c>domain</c>.
     The sort of the result is <c>range</c>.
     <seealso cref="MkArraySort"/>
     <seealso cref="MkStore"/>
  *)
  let mk_select ( ctx : context ) ( a : array_expr ) ( i : expr ) =
    ((create_expr ctx (Z3native.mk_select (context_gno ctx) a#gno i#gno)) :> array_expr)
      
  (**
     Array update.       
     <remarks>
     The node <c>a</c> must have an array sort <c>[domain -> range]</c>, 
     <c>i</c> must have sort <c>domain</c>,
     <c>v</c> must have sort range. The sort of the result is <c>[domain -> range]</c>.
     The semantics of this function is given by the theory of arrays described in the SMT-LIB
     standard. See http://smtlib.org for more details.
     The result of this function is an array that is equal to <c>a</c> 
     (with respect to <c>select</c>)
     on all indices except for <c>i</c>, where it maps to <c>v</c> 
     (and the <c>select</c> of <c>a</c> with 
     respect to <c>i</c> may be a different value).
     <seealso cref="MkArraySort"/>
     <seealso cref="MkSelect"/>
  *)
  let mk_select ( ctx : context ) ( a : array_expr ) ( i : expr ) ( v : expr) =
    (new array_expr ctx)#cnstr_obj (Z3native.mk_store (context_gno ctx) a#gno i#gno v#gno)

  (**
     Create a constant array.
     <remarks>
     The resulting term is an array, such that a <c>select</c>on an arbitrary index 
     produces the value <c>v</c>.
     <seealso cref="MkArraySort"/>
     <seealso cref="MkSelect"/>
  *)
  let mk_const_array ( ctx : context ) ( domain : sort ) ( v : expr ) =
    (new array_expr ctx)#cnstr_obj (Z3native.mk_const_array (context_gno ctx) domain#gno v#gno)

  (**
     Maps f on the argument arrays.
     <remarks>
     Eeach element of <c>args</c> must be of an array sort <c>[domain_i -> range_i]</c>.
     The function declaration <c>f</c> must have type <c> range_1 .. range_n -> range</c>.
     <c>v</c> must have sort range. The sort of the result is <c>[domain_i -> range]</c>.
     <seealso cref="MkArraySort"/>
     <seealso cref="MkSelect"/>
     <seealso cref="MkStore"/>
  *)
  let mk_map ( ctx : context ) ( f : func_decl ) ( args : array_expr array ) =
    ((create_expr ctx (Z3native.mk_map (context_gno ctx) f#gno (Array.length args) (astaton args))) :> array_expr)

  (**
     Access the array default value.
     <remarks>
     Produces the default range value, for arrays that can be represented as 
     finite maps with a default range value.    
  *)
  let mk_term_array  ( ctx : context ) ( arg : array_expr ) =
    ((create_expr ctx (Z3native.mk_array_default (context_gno ctx) arg#gno)) :> array_expr)
end

(** Functions to manipulate Set expressions *)
module Sets = 
struct
  (**
     Indicates whether the term is set union
  *)
  let is_union ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_UNION)

  (**
     Indicates whether the term is set intersection
  *)
  let is_intersect ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_INTERSECT)

  (**
     Indicates whether the term is set difference
  *)
  let is_difference ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_DIFFERENCE)

  (**
     Indicates whether the term is set complement
  *)
  let is_complement ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_COMPLEMENT)

  (**
     Indicates whether the term is set subset
  *)
  let is_subset ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SET_SUBSET)

  (**
     Create a set type.
  *)
  let mk_sort  ( ctx : context ) ( ty : sort) =
    (new set_sort ctx)#cnstr_s ty

  (**
     Create an empty set.
  *)
  let mk_empty ( ctx : context ) ( domain : sort ) =
    (create_expr ctx (Z3native.mk_empty_set (context_gno ctx) domain#gno))
      
  (**
     Create the full set.
  *)
  let mk_full ( ctx : context ) ( domain : sort ) =
    create_expr ctx (Z3native.mk_full_set (context_gno ctx) domain#gno)

  (**
     Add an element to the set.
  *)
  let mk_set_add  ( ctx : context ) ( set : expr ) ( element : expr ) =
    create_expr ctx (Z3native.mk_set_add (context_gno ctx) set#gno element#gno)
      
  (**
     Remove an element from a set.
  *)
  let mk_del  ( ctx : context ) ( set : expr ) ( element : expr ) =
    create_expr ctx (Z3native.mk_set_del (context_gno ctx) set#gno element#gno)
      
  (**
     Take the union of a list of sets.
  *)
  let mk_union  ( ctx : context ) ( args : expr array ) =
    create_expr ctx (Z3native.mk_set_union (context_gno ctx) (Array.length args) (astaton args))
      
  (**
     Take the intersection of a list of sets.
  *)
  let mk_intersection  ( ctx : context ) ( args : expr array ) =
    create_expr ctx (Z3native.mk_set_intersect (context_gno ctx) (Array.length args) (astaton args))

  (**
     Take the difference between two sets.
  *)
  let mk_difference  ( ctx : context ) ( arg1 : expr ) ( arg2 : expr) =
    create_expr ctx (Z3native.mk_set_difference (context_gno ctx) arg1#gno arg2#gno)

  (**
     Take the complement of a set.
  *)
  let mk_complement  ( ctx : context ) ( arg : expr ) =
    create_expr ctx (Z3native.mk_set_complement (context_gno ctx) arg#gno)

  (**
     Check for set membership.
  *)
  let mk_membership  ( ctx : context ) ( elem : expr ) ( set : expr ) =
    create_expr ctx (Z3native.mk_set_member (context_gno ctx) elem#gno set#gno)

  (**
     Check for subsetness of sets.
  *)
  let mk_subset  ( ctx : context ) ( arg1 : expr ) ( arg2 : expr) =
    create_expr ctx (Z3native.mk_set_subset (context_gno ctx) arg1#gno arg2#gno)

end

(** Functions to manipulate Finite Domain expressions *)
module FiniteDomains =
struct
  (**
     Create a new finite domain sort.
  *)
  let mk_sort ( ctx : context ) ( name : symbol ) size =
    (new finite_domain_sort ctx)#cnstr_si name size
      
  (**
     Create a new finite domain sort.
  *)
  let mk_sort_s ( ctx : context ) ( name : string ) size =
    (new finite_domain_sort ctx)#cnstr_si ((Symbol.mk_string ctx name) :> symbol) size


  (**
     Indicates whether the term is of an array sort.
  *)
  let is_finite_domain ( x : expr ) =
    (Z3native.is_app x#gnc x#gno) &&
      (sort_kind_of_int (Z3native.get_sort_kind x#gnc (Z3native.get_sort x#gnc x#gno)) == FINITE_DOMAIN_SORT)

  (**
     Indicates whether the term is a less than predicate over a finite domain.
  *)
  let is_lt ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_FD_LT)

  (** The size of the finite domain sort. *)
  let get_size (x : finite_domain_sort) = 
    let (r, v) = Z3native.get_finite_domain_sort_size x#gnc x#gno in
    if r then v
    else raise (Z3native.Exception "Conversion failed.")
end

(** Functions to manipulate Relation expressions *)
module Relations =
struct
  (**
     Indicates whether the term is of a relation sort.
  *)
  let is_relation ( x : expr ) =
    ((Z3native.is_app x#gnc x#gno) &&
	(sort_kind_of_int (Z3native.get_sort_kind x#gnc (Z3native.get_sort x#gnc x#gno)) == RELATION_SORT))

  (**
     Indicates whether the term is an relation store
     <remarks>
     Insert a record into a relation.
     The function takes <c>n+1</c> arguments, where the first argument is the relation and the remaining <c>n</c> elements 
     correspond to the <c>n</c> columns of the relation.
  *)
  let is_store ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_STORE)

  (**
     Indicates whether the term is an empty relation
  *)
  let is_empty ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_EMPTY)

  (**
     Indicates whether the term is a test for the emptiness of a relation
  *)
  let is_is_empty ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_IS_EMPTY)

  (**
     Indicates whether the term is a relational join
  *)
  let is_join ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_JOIN)

  (**
     Indicates whether the term is the union or convex hull of two relations. 
     <remarks>The function takes two arguments.
  *)
  let is_union ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_UNION)

  (**
     Indicates whether the term is the widening of two relations
     <remarks>The function takes two arguments.
  *)
  let is_widen ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_WIDEN)

  (**
     Indicates whether the term is a projection of columns (provided as numbers in the parameters).
     <remarks>The function takes one argument.
  *)
  let is_project ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_PROJECT)

  (**
     Indicates whether the term is a relation filter
     <remarks>
     Filter (restrict) a relation with respect to a predicate.
     The first argument is a relation. 
     The second argument is a predicate with free de-Brujin indices
     corresponding to the columns of the relation.
     So the first column in the relation has index 0.
  *)
  let is_filter ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_FILTER)

  (**
     Indicates whether the term is an intersection of a relation with the negation of another.
     <remarks>
     Intersect the first relation with respect to negation
     of the second relation (the function takes two arguments).
     Logically, the specification can be described by a function
     
     target = filter_by_negation(pos, neg, columns)
     
     where columns are pairs c1, d1, .., cN, dN of columns from pos and neg, such that
     target are elements in ( x : expr ) in pos, such that there is no y in neg that agrees with
     ( x : expr ) on the columns c1, d1, .., cN, dN.
  *)
  let is_negation_filter ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_NEGATION_FILTER)

  (**
     Indicates whether the term is the renaming of a column in a relation
     <remarks>    
     The function takes one argument.
     The parameters contain the renaming as a cycle.
  *)
  let is_rename ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_RENAME)

  (**
     Indicates whether the term is the complement of a relation
  *)
  let is_complement ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_COMPLEMENT)

  (**
     Indicates whether the term is a relational select
     <remarks>
     Check if a record is an element of the relation.
     The function takes <c>n+1</c> arguments, where the first argument is a relation,
     and the remaining <c>n</c> arguments correspond to a record.
  *)
  let is_select ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_SELECT)

  (**
     Indicates whether the term is a relational clone (copy)
     <remarks>
     Create a fresh copy (clone) of a relation. 
     The function is logically the identity, but
     in the context of a register machine allows 
     for terms of kind <seealso cref="IsRelationUnion"/> 
     to perform destructive updates to the first argument.
  *)
  let is_clone ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_RA_CLONE)

  (** The arity of the relation sort. *)
  let get_arity (x : relation_sort) = Z3native.get_relation_arity x#gnc x#gno

  (** The sorts of the columns of the relation sort. *)
  let get_column_sorts (x : relation_sort) = 
    let n = get_arity x in
    let f i = create_sort x#gc (Z3native.get_relation_column x#gnc x#gno i) in
    Array.init n f

end
  
(** Functions to manipulate Datatype expressions *)
module Datatypes =
struct
  (** Constructors *)
  module Constructor =
  struct
    (** The number of fields of the constructor. *)
    let get_num_fields ( x : constructor ) = x#get_n
      
    (** The function declaration of the constructor. *)
    let get_constructor_decl ( x : constructor ) = x#constructor_decl
      
    (** The function declaration of the tester. *)
    let get_tester_decl ( x : constructor ) = x#tester_decl
      
    (** The function declarations of the accessors *)
    let get_accessor_decls ( x : constructor ) = x#accessor_decls
  end

  (* DATATYPES *)
  (**
     Create a datatype constructor.
     @param name constructor name
     @param recognizer name of recognizer function.
     @param fieldNames names of the constructor fields.
     @param sorts field sorts, 0 if the field sort refers to a recursive sort.
     @param sortRefs reference to datatype sort that is an argument to the constructor; 
     if the corresponding sort reference is 0, then the value in sort_refs should be an index 
     referring to one of the recursive datatypes that is declared.
  *)
  let mk_constructor ( ctx : context ) ( name : symbol ) ( recognizer : symbol ) ( field_names : symbol array ) ( sorts : sort array ) ( sort_refs : int array) =
    (new constructor ctx)#cnstr_ssssi name recognizer field_names sorts sort_refs


  (**
     Create a datatype constructor.
     @param name constructor name
     @param recognizer name of recognizer function.
     @param fieldNames names of the constructor fields.
     @param sorts field sorts, 0 if the field sort refers to a recursive sort.
     @param sortRefs reference to datatype sort that is an argument to the constructor; 
     if the corresponding sort reference is 0, then the value in sort_refs should be an index 
     referring to one of the recursive datatypes that is declared.
  *)
  let mk_constructor_s ( ctx : context ) ( name : string ) ( recognizer : symbol ) ( field_names : symbol array ) ( sorts : sort array ) ( sort_refs : int array) =
    mk_constructor ctx ((Symbol.mk_string ctx name) :> symbol) recognizer field_names sorts sort_refs


  (**
     Create a new datatype sort.
  *)
  let mk_sort ( ctx : context ) ( name : symbol ) ( constructors : constructor array) =
    (new datatype_sort ctx)#cnstr_sc name constructors

  (**
     Create a new datatype sort.
  *)
  let mk_sort_s ( ctx : context ) ( name : string ) ( constructors : constructor array) =
    mk_sort ctx ((Symbol.mk_string ctx name) :> symbol) constructors
      
  (**
     Create mutually recursive datatypes.
     @param names names of datatype sorts
     @param c list of constructors, one list per sort.
  *)
  let mk_sorts ( ctx : context ) ( names : symbol array ) ( c : constructor array array ) =
    let n = (Array.length names) in
    let f e = ( (new constructor_list ctx)#cnstr_ca e ) in
    let cla = (Array.map f c) in
    let (r, a) = (Z3native.mk_datatypes (context_gno ctx) n (symbolaton names) (constructor_listaton cla)) in
    let g e = ( (new datatype_sort ctx)#cnstr_obj e) in
    (Array.map g r)

  (** Create mutually recursive data-types. *)
  let mk_sorts_s ( ctx : context ) ( names : string array ) ( c : constructor array array ) =
    mk_sorts ctx 
      ( 
	let f e = ((Symbol.mk_string ctx e) :> symbol) in
	Array.map f names 
      )
      c

  (** The number of constructors of the datatype sort. *)
  let get_num_constructors (x : datatype_sort) = Z3native.get_datatype_sort_num_constructors x#gnc x#gno

  (** The range of the array sort. *)
  let get_constructors (x : datatype_sort) = 
    let n = (get_num_constructors x) in
    let f i = (new func_decl x#gc)#cnstr_obj (Z3native.get_datatype_sort_constructor x#gnc x#gno i) in
    Array.init n f

  (** The recognizers. *)
  let get_recognizers (x : datatype_sort) = 
    let n = (get_num_constructors x) in
    let f i = (new func_decl x#gc)#cnstr_obj (Z3native.get_datatype_sort_recognizer x#gnc x#gno i) in
    Array.init n f
      
  (** The constructor accessors. *)
  let get_accessors (x : datatype_sort) =
    let n = (get_num_constructors x) in
    let f i = (
      let fd = ((new func_decl x#gc)#cnstr_obj (Z3native.get_datatype_sort_constructor x#gnc x#gno i)) in
      let ds = (Z3native.get_domain_size fd#gnc fd#gno) in
      let g j = (new func_decl x#gc)#cnstr_obj (Z3native.get_datatype_sort_constructor_accessor x#gnc x#gno i j) in
      Array.init ds g
    ) in
    Array.init n f
end

(** Functions to manipulate Enumeration expressions *)
module Enumerations =
struct
  (**
     Create a new enumeration sort.
  *)
  let mk_sort ( ctx : context ) name enum_names =
    (new enum_sort ctx)#cnstr_ss name enum_names

  (**
     Create a new enumeration sort.
  *)
  let mk_sort_s ( ctx : context ) name enum_names =
    (new enum_sort ctx)#cnstr_ss 
      ((Symbol.mk_string ( ctx : context ) name) :> symbol) 
      (let f e = (e :> symbol) in
       (Array.map f (Symbol.mk_strings ( ctx : context ) enum_names))
      )

  (** The function declarations of the constants in the enumeration. *)
  let get_const_decls (x : enum_sort) = x#const_decls

  (** The test predicates for the constants in the enumeration. *)
  let get_tester_decls (x : enum_sort) = x#tester_decls
end

(** Functions to manipulate List expressions *)
module Lists =
struct
  (**
     Create a new list sort.
  *)
  let mk_sort ( ctx : context ) (name : symbol) elem_sort =
    (new list_sort ctx)#cnstr_ss name elem_sort
      
  (**
     Create a new list sort.
  *)
  let mk_list_s ( ctx : context ) (name : string) elem_sort =
    mk_sort ctx ((Symbol.mk_string ctx name) :> symbol) elem_sort


  (** The declaration of the nil function of this list sort. *)
  let get_nil_decl (x : list_sort) = x#nil_decl

  (** The declaration of the isNil function of this list sort. *)
  let get_is_nil_decl (x : list_sort) = x#is_nil_decl

  (** The declaration of the cons function of this list sort. *)
  let get_cons_decl (x : list_sort) = x#cons_decl

  (** The declaration of the isCons function of this list sort. *)
  let get_is_cons_decl (x : list_sort) = x#is_cons_decl

  (** The declaration of the head function of this list sort. *)
  let get_head_decl (x : list_sort)  = x#head_decl

  (** The declaration of the tail function of this list sort. *)
  let get_tail_decl (x : list_sort) = x#tail_decl

  (** The empty list. *)
  let nil (x : list_sort) = create_expr_fa x#gc (get_nil_decl x) [||]
end

(** Functions to manipulate Tuple expressions *)
module Tuples =
struct
  (**
     Create a new tuple sort.
  *)    
  let mk_sort ( ctx : context ) name field_names field_sorts =
    (new tuple_sort ctx)#cnstr_siss name (Array.length field_names) field_names field_sorts

  (**  The constructor function of the tuple. *)
  let get_mk_decl (x : tuple_sort) = 
    (new func_decl x#gc)#cnstr_obj (Z3native.get_tuple_sort_mk_decl x#gnc x#gno)    

  (** The number of fields in the tuple. *)
  let get_num_fields (x : tuple_sort) = Z3native.get_tuple_sort_num_fields x#gnc x#gno
    
  (** The field declarations. *)
  let get_field_decls (x : tuple_sort) = 
    let n = get_num_fields x in
    let f i = ((new func_decl x#gc)#cnstr_obj (Z3native.get_tuple_sort_field_decl x#gnc x#gno i)) in
    Array.init n f
end

(** Functions to manipulate arithmetic expressions *)
module Arithmetic =  
struct
  (**
     Create a new integer sort.
  *)
  let mk_int_sort ( ctx : context ) =
    (new int_sort ctx)#cnstr_obj (Z3native.mk_int_sort (context_gno ctx))

  (**
     Create a real sort.
  *)    
  let mk_real_sort ( ctx : context ) =
    (new real_sort ctx)#cnstr_obj (Z3native.mk_real_sort (context_gno ctx))

  (**
     Indicates whether the term is of integer sort.
  *)
  let is_int ( x : expr ) =
    (Z3native.is_numeral_ast x#gnc x#gno) &&
      ((sort_kind_of_int (Z3native.get_sort_kind x#gnc (Z3native.get_sort x#gnc x#gno))) == INT_SORT)
      
  (**
     Indicates whether the term is an arithmetic numeral.
  *)
  let is_arithmetic_numeral ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ANUM)

  (**
     Indicates whether the term is a less-than-or-equal
  *)
  let is_le ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_LE)

  (**
     Indicates whether the term is a greater-than-or-equal
  *)
  let is_ge ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_GE)

  (**
     Indicates whether the term is a less-than
  *)
  let is_lt ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_LT)

  (**
     Indicates whether the term is a greater-than
  *)
  let is_gt ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_GT)

  (**
     Indicates whether the term is addition (binary)
  *)
  let is_add ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ADD)

  (**
     Indicates whether the term is subtraction (binary)
  *)
  let is_sub ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SUB)

  (**
     Indicates whether the term is a unary minus
  *)
  let is_uminus ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_UMINUS)

  (**
     Indicates whether the term is multiplication (binary)
  *)
  let is_mul ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_MUL)

  (**
     Indicates whether the term is division (binary)
  *)
  let is_div ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_DIV)

  (**
     Indicates whether the term is integer division (binary)
  *)
  let is_idiv ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_IDIV)

  (**
     Indicates whether the term is remainder (binary)
  *)
  let is_remainder ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_REM)

  (**
     Indicates whether the term is modulus (binary)
  *)
  let is_modulus ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_MOD)

  (**
     Indicates whether the term is a coercion of integer to real (unary)
  *)
  let is_inttoreal ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_TO_REAL)

  (**
     Indicates whether the term is a coercion of real to integer (unary)
  *)
  let is_real_to_int ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_TO_INT)

  (**
     Indicates whether the term is a check that tests whether a real is integral (unary)
  *)
  let is_real_is_int ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_IS_INT)

  (**
     Indicates whether the term is of sort real.
  *)
  let is_real ( x : expr ) =
    ((sort_kind_of_int (Z3native.get_sort_kind x#gnc (Z3native.get_sort x#gnc x#gno))) == REAL_SORT)

  (**
     Indicates whether the term is an integer numeral.
  *)
  let is_int_numeral ( x : expr ) = (Expr.is_numeral x) && (is_int x)

  (**
     Indicates whether the term is a real numeral.
  *)
  let is_rat_num ( x : expr ) = (Expr.is_numeral x) && (is_real x)
    
  (**
     Indicates whether the term is an algebraic number
  *)
  let is_algebraic_number ( x : expr ) = Z3native.is_algebraic_number x#gnc x#gno

  (**  Retrieve the int value. *)
  let get_int ( x : int_num ) = 
    let (r, v) = Z3native.get_numeral_int x#gnc x#gno in
    if r then v
    else raise (Z3native.Exception "Conversion failed.")
				  
  (** Returns a string representation of the numeral. *)
  let to_string ( x : int_num ) = Z3native.get_numeral_string x#gnc x#gno		      

  (** The numerator of a rational numeral. *)
  let get_numerator ( x : rat_num ) =
    (new int_num x#gc)#cnstr_obj (Z3native.get_numerator x#gnc x#gno)
      
  (** The denominator of a rational numeral. *)
  let get_denominator ( x : rat_num ) =
    (new int_num x#gc)#cnstr_obj (Z3native.get_denominator x#gnc x#gno)
      
  (** Returns a string representation in decimal notation. 
      <remarks>The result has at most <paramref name="precision"/> decimal places.*)
  let to_decimal_string ( x : rat_num ) (precision : int) = 
    Z3native.get_numeral_decimal_string x#gnc x#gno precision
      
  (** Returns a string representation of the numeral. *)
  let to_string ( x : rat_num ) = Z3native.get_numeral_string x#gnc x#gno

  (**
     Creates an integer constant.
  *)        
  let mk_int_const ( ctx : context ) ( name : symbol ) =
    ((Expr.mk_const ctx name (mk_int_sort ctx)) :> int_expr)

  (**
     Creates an integer constant.
  *)
  let mk_int_const_s ( ctx : context ) ( name : string )  =
    mk_int_const ctx ((Symbol.mk_string ctx name) :> symbol)

  (**
     Creates a real constant.
  *)
  let mk_real_const ( ctx : context ) ( name : symbol )  =
    ((Expr.mk_const ctx name (mk_real_sort ctx)) :> real_expr)
      
  (**
     Creates a real constant.
  *)
  let mk_real_const_s ( ctx : context ) ( name : string )  =
    mk_real_const ctx ((Symbol.mk_string ctx name) :> symbol)

  (**
     Create an expression representing <c>t[0] + t[1] + ...</c>.
  *)    
  let mk_add ( ctx : context ) ( t : arith_expr array ) =
    (create_expr ctx (Z3native.mk_add (context_gno ctx) (Array.length t) (astaton t)) :> arith_expr)

  (**
     Create an expression representing <c>t[0] * t[1] * ...</c>.
  *)    
  let mk_mul ( ctx : context ) ( t : arith_expr array ) =
    (create_expr ctx (Z3native.mk_mul (context_gno ctx) (Array.length t) (astaton t)) :> arith_expr)

  (**
     Create an expression representing <c>t[0] - t[1] - ...</c>.
  *)    
  let mk_sub ( ctx : context ) ( t : arith_expr array ) =
    (create_expr ctx (Z3native.mk_sub (context_gno ctx) (Array.length t) (astaton t)) :> arith_expr)
      
  (**
     Create an expression representing <c>-t</c>.
  *)    
  let mk_unary_minus ( ctx : context ) ( t : arith_expr ) =     
    (create_expr ctx (Z3native.mk_unary_minus (context_gno ctx) t#gno) :> arith_expr)

  (**
     Create an expression representing <c>t1 / t2</c>.
  *)    
  let mk_div ( ctx : context ) ( t1 : arith_expr ) ( t2 : arith_expr ) =
    (create_expr ctx (Z3native.mk_div (context_gno ctx) t1#gno t2#gno) :> arith_expr)

  (**
     Create an expression representing <c>t1 mod t2</c>.
     <remarks>The arguments must have int type.
  *)
  let mk_mod ( ctx : context ) ( t1 : int_expr ) ( t2 : int_expr ) =    
    (new int_expr ctx)#cnstr_obj (Z3native.mk_mod (context_gno ctx) t1#gno t2#gno)

  (**
     Create an expression representing <c>t1 rem t2</c>.
     <remarks>The arguments must have int type.
  *)
  let mk_rem ( ctx : context ) ( t1 : int_expr ) ( t2 : int_expr ) =
    (new int_expr ctx)#cnstr_obj (Z3native.mk_rem (context_gno ctx) t1#gno t2#gno)

  (**
     Create an expression representing <c>t1 ^ t2</c>.
  *)    
  let mk_Power ( ctx : context ) ( t1 : int_expr ) ( t2 : int_expr ) =     
    (create_expr ctx (Z3native.mk_power (context_gno ctx) t1#gno t2#gno) :> arith_expr)

  (**
     Create an expression representing <c>t1 < t2</c>
  *)    
  let mk_lt ( ctx : context ) ( t1 : int_expr ) ( t2 : int_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_lt (context_gno ctx) t1#gno t2#gno)

  (**
     Create an expression representing <c>t1 <= t2</c>
  *)    
  let mk_le ( ctx : context ) ( t1 : int_expr ) ( t2 : int_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_le (context_gno ctx) t1#gno t2#gno)
      
  (**
     Create an expression representing <c>t1 > t2</c>
  *)    
  let mk_gt ( ctx : context ) ( t1 : int_expr ) ( t2 : int_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_gt (context_gno ctx) t1#gno t2#gno)

  (**
     Create an expression representing <c>t1 >= t2</c>
  *)    
  let mk_ge ( ctx : context ) ( t1 : int_expr ) ( t2 : int_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_ge (context_gno ctx) t1#gno t2#gno)

  (**
     Coerce an integer to a real.

     <remarks>
     There is also a converse operation exposed. It follows the semantics prescribed by the SMT-LIB standard.

     You can take the floor of a real by creating an auxiliary integer Term <c>k</c> and
     and asserting <c>MakeInt2Real(k) <= t1 < MkInt2Real(k)+1</c>.
     The argument must be of integer sort.
  *)
  let mk_int2real ( ctx : context ) ( t : int_expr ) =
    (new real_expr ctx)#cnstr_obj (Z3native.mk_int2real (context_gno ctx) t#gno)

  (**
     Coerce a real to an integer.

     <remarks>
     The semantics of this function follows the SMT-LIB standard for the function to_int.
     The argument must be of real sort.
  *)
  let mk_real2int ( ctx : context ) ( t : real_expr ) =
    (new int_expr ctx)#cnstr_obj (Z3native.mk_real2int (context_gno ctx) t#gno)

  (**
     Creates an expression that checks whether a real number is an integer.
  *)
  let mk_is_integer ( ctx : context ) ( t : real_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_is_int (context_gno ctx) t#gno)

  (**
     Return a upper bound for a given real algebraic number. 
     The interval isolating the number is smaller than 1/10^<paramref name="precision"/>.    
     <seealso cref="Expr.IsAlgebraicNumber"/>   
     @param precision the precision of the result
     @return A numeral Expr of sort Real
  *)
  let to_upper ( x : algebraic_num ) ( precision : int ) =
    (new rat_num x#gc)#cnstr_obj (Z3native.get_algebraic_number_upper x#gnc x#gno precision)

  (**
     Return a lower bound for the given real algebraic number. 
     The interval isolating the number is smaller than 1/10^<paramref name="precision"/>.    
     <seealso cref="Expr.IsAlgebraicNumber"/>
     @param precision the precision of the result
     @return A numeral Expr of sort Real
  *)
  let to_lower ( x : algebraic_num ) precision =
    (new rat_num x#gc)#cnstr_obj (Z3native.get_algebraic_number_lower x#gnc x#gno precision)
      
  (** Returns a string representation in decimal notation. 
      <remarks>The result has at most <paramref name="precision"/> decimal places.*)
  let to_decimal_string ( x : algebraic_num ) ( precision : int ) = 
    Z3native.get_numeral_decimal_string x#gnc x#gno precision

  (**
     Create a real from a fraction.

     @param num numerator of rational.
     @param den denominator of rational.
     @return A Term with value <paramref name="num"/>/<paramref name="den"/> and sort Real
     <seealso cref="MkNumeral(string, Sort)"/>
  *)
  let mk_real_numeral_nd ( ctx : context ) ( num : int ) ( den : int) =
    if (den == 0) then 
      raise (Z3native.Exception "Denominator is zero")
    else
      
      (new rat_num ctx)#cnstr_obj (Z3native.mk_real (context_gno ctx) num den)
	
  (**
     Create a real numeral.
     @param v A string representing the Term value in decimal notation.
     @return A Term with value <paramref name="v"/> and sort Real
  *)
  let mk_real_numeral_s ( ctx : context ) ( v : string ) =
    (new rat_num ctx)#cnstr_obj (Z3native.mk_numeral (context_gno ctx) v (mk_real_sort ctx)#gno)

  (**
     Create a real numeral.

     @param v value of the numeral.    
     @return A Term with value <paramref name="v"/> and sort Real
  *)
  let mk_real_numeral_i ( ctx : context ) ( v : int ) =
    (new rat_num ctx)#cnstr_obj (Z3native.mk_int (context_gno ctx) v (mk_real_sort ctx)#gno)

  (**
     Create an integer numeral.
     @param v A string representing the Term value in decimal notation.
  *)
  let mk_int_numeral_s ( ctx : context ) ( v : string ) =
    (new int_num ctx)#cnstr_obj (Z3native.mk_numeral (context_gno ctx) v (mk_int_sort ctx)#gno)

  (**
     Create an integer numeral.
     @param v value of the numeral.    
     @return A Term with value <paramref name="v"/> and sort Integer
  *)
  let mk_int_numeral_i ( ctx : context ) ( v : int ) =
    (new int_num ctx)#cnstr_obj (Z3native.mk_int (context_gno ctx) v (mk_int_sort ctx)#gno)

  (** Returns a string representation of the numeral. *)
  let to_string ( x : algebraic_num ) = Z3native.get_numeral_string x#gnc x#gno
end


(** Functions to manipulate bit-vector expressions *)
module BitVectors =
struct
  (**
     Create a new bit-vector sort.
  *)
  let mk_sort ( ctx : context ) size =
    (new bitvec_sort ctx)#cnstr_obj (Z3native.mk_bv_sort (context_gno ctx) size)

  (**
     Indicates whether the terms is of bit-vector sort.
  *)
  let is_bv ( x : expr ) =
    ((sort_kind_of_int (Z3native.get_sort_kind x#gnc (Z3native.get_sort x#gnc x#gno))) == BV_SORT)

  (**
     Indicates whether the term is a bit-vector numeral
  *)
  let is_bv_numeral ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNUM)

  (**
     Indicates whether the term is a one-bit bit-vector with value one
  *)
  let is_bv_bit1 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BIT1)

  (**
     Indicates whether the term is a one-bit bit-vector with value zero
  *)
  let is_bv_bit0 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BIT0)

  (**
     Indicates whether the term is a bit-vector unary minus
  *)
  let is_bv_uminus ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNEG)

  (**
     Indicates whether the term is a bit-vector addition (binary)
  *)
  let is_bv_add ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BADD)

  (**
     Indicates whether the term is a bit-vector subtraction (binary)
  *)
  let is_bv_sub ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSUB)

  (**
     Indicates whether the term is a bit-vector multiplication (binary)
  *)
  let is_bv_mul ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BMUL)

  (**
     Indicates whether the term is a bit-vector signed division (binary)
  *)
  let is_bv_sdiv ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSDIV)

  (**
     Indicates whether the term is a bit-vector unsigned division (binary)
  *)
  let is_bv_udiv ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BUDIV)

  (**
     Indicates whether the term is a bit-vector signed remainder (binary)
  *)
  let is_bv_SRem ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSREM)

  (**
     Indicates whether the term is a bit-vector unsigned remainder (binary)
  *)
  let is_bv_urem ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BUREM)

  (**
     Indicates whether the term is a bit-vector signed modulus
  *)
  let is_bv_smod ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSMOD)

  (**
     Indicates whether the term is a bit-vector signed division by zero
  *)
  let is_bv_sdiv0 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSDIV0)

  (**
     Indicates whether the term is a bit-vector unsigned division by zero
  *)
  let is_bv_udiv0 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BUDIV0)

  (**
     Indicates whether the term is a bit-vector signed remainder by zero
  *)
  let is_bv_srem0 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSREM0)

  (**
     Indicates whether the term is a bit-vector unsigned remainder by zero
  *)
  let is_bv_urem0 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BUREM0)

  (**
     Indicates whether the term is a bit-vector signed modulus by zero
  *)
  let is_bv_smod0 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSMOD0)

  (**
     Indicates whether the term is an unsigned bit-vector less-than-or-equal
  *)
  let is_bv_ule ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ULEQ)

  (**
     Indicates whether the term is a signed bit-vector less-than-or-equal
  *)
  let is_bv_sle ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SLEQ)

  (**
     Indicates whether the term is an unsigned bit-vector greater-than-or-equal
  *)
  let is_bv_uge ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_UGEQ)

  (**
     Indicates whether the term is a signed bit-vector greater-than-or-equal
  *)
  let is_bv_sge ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SGEQ)

  (**
     Indicates whether the term is an unsigned bit-vector less-than
  *)
  let is_bv_ult ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ULT)

  (**
     Indicates whether the term is a signed bit-vector less-than
  *)
  let is_bv_slt ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SLT)

  (**
     Indicates whether the term is an unsigned bit-vector greater-than
  *)
  let is_bv_ugt ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_UGT)

  (**
     Indicates whether the term is a signed bit-vector greater-than
  *)
  let is_bv_sgt ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SGT)

  (**
     Indicates whether the term is a bit-wise AND
  *)
  let is_bv_and ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BAND)

  (**
     Indicates whether the term is a bit-wise OR
  *)
  let is_bv_or ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BOR)

  (**
     Indicates whether the term is a bit-wise NOT
  *)
  let is_bv_not ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNOT)

  (**
     Indicates whether the term is a bit-wise XOR
  *)
  let is_bv_xor ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BXOR)

  (**
     Indicates whether the term is a bit-wise NAND
  *)
  let is_bv_nand ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNAND)

  (**
     Indicates whether the term is a bit-wise NOR
  *)
  let is_bv_nor ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BNOR)

  (**
     Indicates whether the term is a bit-wise XNOR
  *)
  let is_bv_xnor ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BXNOR)

  (**
     Indicates whether the term is a bit-vector concatenation (binary)
  *)
  let is_bv_concat ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_CONCAT)

  (**
     Indicates whether the term is a bit-vector sign extension
  *)
  let is_bv_signextension ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_SIGN_EXT)

  (**
     Indicates whether the term is a bit-vector zero extension
  *)
  let is_bv_zeroextension ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ZERO_EXT)

  (**
     Indicates whether the term is a bit-vector extraction
  *)
  let is_bv_extract ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_EXTRACT)

  (**
     Indicates whether the term is a bit-vector repetition
  *)
  let is_bv_repeat ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_REPEAT)

  (**
     Indicates whether the term is a bit-vector reduce OR
  *)
  let is_bv_reduceor ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BREDOR)

  (**
     Indicates whether the term is a bit-vector reduce AND
  *)
  let is_bv_reduceand ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BREDAND)

  (**
     Indicates whether the term is a bit-vector comparison
  *)
  let is_bv_comp ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BCOMP)

  (**
     Indicates whether the term is a bit-vector shift left
  *)
  let is_bv_shiftleft ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BSHL)

  (**
     Indicates whether the term is a bit-vector logical shift right
  *)
  let is_bv_shiftrightlogical ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BLSHR)

  (**
     Indicates whether the term is a bit-vector arithmetic shift left
  *)
  let is_bv_shiftrightarithmetic ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BASHR)

  (**
     Indicates whether the term is a bit-vector rotate left
  *)
  let is_bv_rotateleft ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ROTATE_LEFT)

  (**
     Indicates whether the term is a bit-vector rotate right
  *)
  let is_bv_rotateright ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_ROTATE_RIGHT)

  (**
     Indicates whether the term is a bit-vector rotate left (extended)
     <remarks>Similar to Z3_OP_ROTATE_LEFT, but it is a binary operator instead of a parametric one.
  *)
  let is_bv_rotateleftextended ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_EXT_ROTATE_LEFT)

  (**
     Indicates whether the term is a bit-vector rotate right (extended)
     <remarks>Similar to Z3_OP_ROTATE_RIGHT, but it is a binary operator instead of a parametric one.
  *)
  let is_bv_rotaterightextended ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_EXT_ROTATE_RIGHT)

  (**
     Indicates whether the term is a coercion from integer to bit-vector
     <remarks>This function is not supported by the decision procedures. Only the most 
     rudimentary simplification rules are applied to this function.
  *)
  let is_int_to_bv ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_INT2BV)

  (**
     Indicates whether the term is a coercion from bit-vector to integer
     <remarks>This function is not supported by the decision procedures. Only the most 
     rudimentary simplification rules are applied to this function.
  *)
  let is_bv_to_int ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_BV2INT)

  (**
     Indicates whether the term is a bit-vector carry
     <remarks>Compute the carry bit in a full-adder.  The meaning is given by the 
     equivalence (carry l1 l2 l3) <=> (or (and l1 l2) (and l1 l3) (and l2 l3)))
  *)
  let is_bv_carry ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_CARRY)

  (**
     Indicates whether the term is a bit-vector ternary XOR
     <remarks>The meaning is given by the equivalence (xor3 l1 l2 l3) <=> (xor (xor l1 l2) l3)
  *)
  let is_bv_xor3 ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_XOR3)

  (** The size of a bit-vector sort. *)
  let get_size (x : bitvec_sort) = Z3native.get_bv_sort_size x#gnc x#gno

  (**  Retrieve the int value. *)
  let get_int ( x : bitvec_num ) = 
    let (r, v) = Z3native.get_numeral_int x#gnc x#gno in
    if r then v
    else raise (Z3native.Exception "Conversion failed.")
				     
  (** Returns a string representation of the numeral. *)
  let to_string ( x : bitvec_num ) = Z3native.get_numeral_string x#gnc x#gno

  (**
     Creates a bit-vector constant.
  *)
  let mk_const ( ctx : context ) ( name : symbol ) ( size : int ) =
    ((Expr.mk_const ctx name (mk_sort ctx size)) :> bitvec_expr)

  (**
     Creates a bit-vector constant.
  *)
  let mk_const_s ( ctx : context ) ( name : string ) ( size : int ) =
    mk_const ctx ((Symbol.mk_string ctx name) :> symbol) size

  (**
     Bitwise negation.
     <remarks>The argument must have a bit-vector sort.
  *)
  let mk_not  ( ctx : context ) ( t : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvnot (context_gno ctx) t#gno)

  (**
     Take conjunction of bits in a vector,vector of length 1.
     <remarks>The argument must have a bit-vector sort.
  *)
  let mk_redand  ( ctx : context ) ( t : bitvec_expr) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvredand (context_gno ctx) t#gno)

  (**
     Take disjunction of bits in a vector,vector of length 1.
     <remarks>The argument must have a bit-vector sort.
  *)
  let mk_redor  ( ctx : context ) ( t : bitvec_expr) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvredor (context_gno ctx) t#gno)

  (**
     Bitwise conjunction.
     <remarks>The arguments must have a bit-vector sort.
  *)
  let mk_and  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvand (context_gno ctx) t1#gno t2#gno)

  (**
     Bitwise disjunction.
     <remarks>The arguments must have a bit-vector sort.
  *)
  let mk_or  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvor (context_gno ctx) t1#gno t2#gno)

  (**
     Bitwise XOR.
     <remarks>The arguments must have a bit-vector sort.
  *)
  let mk_xor  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvxor (context_gno ctx) t1#gno t2#gno)

  (**
     Bitwise NAND.
     <remarks>The arguments must have a bit-vector sort.
  *)
  let mk_nand  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvnand (context_gno ctx) t1#gno t2#gno)

  (**
     Bitwise NOR.
     <remarks>The arguments must have a bit-vector sort.
  *)
  let mk_nor  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvnor (context_gno ctx) t1#gno t2#gno)

  (**
     Bitwise XNOR.
     <remarks>The arguments must have a bit-vector sort.
  *)
  let mk_xnor  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvxnor (context_gno ctx) t1#gno t2#gno)

  (**
     Standard two's complement unary minus.
     <remarks>The arguments must have a bit-vector sort.
  *)
  let mk_neg  ( ctx : context ) ( t : bitvec_expr) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvneg (context_gno ctx) t#gno)

  (**
     Two's complement addition.
     <remarks>The arguments must have the same bit-vector sort.
  *)
  let mk_add  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvadd (context_gno ctx) t1#gno t2#gno)

  (**
     Two's complement subtraction.
     <remarks>The arguments must have the same bit-vector sort.
  *)
  let mk_sub  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvsub (context_gno ctx) t1#gno t2#gno)

  (**
     Two's complement multiplication.
     <remarks>The arguments must have the same bit-vector sort.
  *)
  let mk_mul  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvmul (context_gno ctx) t1#gno t2#gno)

  (**
     Unsigned division.

     <remarks>
     It is defined as the floor of <c>t1/t2</c> if \c t2 is
     different from zero. If <c>t2</c> is zero, then the result
     is undefined.
     The arguments must have the same bit-vector sort.
  *)
  let mk_udiv  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvudiv (context_gno ctx) t1#gno t2#gno)

  (**
     Signed division.
     <remarks>
     It is defined in the following way:

     - The \c floor of <c>t1/t2</c> if \c t2 is different from zero, and <c>t1*t2 >= 0</c>.

     - The \c ceiling of <c>t1/t2</c> if \c t2 is different from zero, and <c>t1*t2 < 0</c>.

     If <c>t2</c> is zero, then the result is undefined.
     The arguments must have the same bit-vector sort.
  *)
  let mk_sdiv  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvsdiv (context_gno ctx) t1#gno t2#gno)

  (**
     Unsigned remainder.
     <remarks>
     It is defined as <c>t1 - (t1 /u t2) * t2</c>, where <c>/u</c> represents unsigned division.       
     If <c>t2</c> is zero, then the result is undefined.
     The arguments must have the same bit-vector sort.
  *)
  let mk_urem  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvurem (context_gno ctx) t1#gno t2#gno)

  (**
     Signed remainder.
     <remarks>
     It is defined as <c>t1 - (t1 /s t2) * t2</c>, where <c>/s</c> represents signed division.
     The most significant bit (sign) of the result is equal to the most significant bit of \c t1.

     If <c>t2</c> is zero, then the result is undefined.
     The arguments must have the same bit-vector sort.
  *)
  let mk_srem  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvsrem (context_gno ctx) t1#gno t2#gno)

  (**
     Two's complement signed remainder (sign follows divisor).
     <remarks>
     If <c>t2</c> is zero, then the result is undefined.
     The arguments must have the same bit-vector sort.
  *)
  let mk_smod  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvsmod (context_gno ctx) t1#gno t2#gno)

  (**
     Unsigned less-than
     <remarks>    
     The arguments must have the same bit-vector sort.
  *)
  let mk_ult  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvult (context_gno ctx) t1#gno t2#gno)

  (**
     Two's complement signed less-than
     <remarks>    
     The arguments must have the same bit-vector sort.
  *)
  let mk_slt  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvslt (context_gno ctx) t1#gno t2#gno)

  (**
     Unsigned less-than or equal to.
     <remarks>    
     The arguments must have the same bit-vector sort.
  *)
  let mk_ule  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvule (context_gno ctx) t1#gno t2#gno)

  (**
     Two's complement signed less-than or equal to.
     <remarks>    
     The arguments must have the same bit-vector sort.
  *)
  let mk_sle  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvsle (context_gno ctx) t1#gno t2#gno)

  (**
     Unsigned greater than or equal to.
     <remarks>    
     The arguments must have the same bit-vector sort.
  *)
  let mk_uge  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvuge (context_gno ctx) t1#gno t2#gno)

  (**
     Two's complement signed greater than or equal to.
     <remarks>    
     The arguments must have the same bit-vector sort.
  *)
  let mk_SGE  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvsge (context_gno ctx) t1#gno t2#gno)

  (**
     Unsigned greater-than.
     <remarks>    
     The arguments must have the same bit-vector sort.
  *)
  let mk_ugt  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvugt (context_gno ctx) t1#gno t2#gno)

  (**
     Two's complement signed greater-than.
     <remarks>    
     The arguments must have the same bit-vector sort.
  *)
  let mk_sgt  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvsgt (context_gno ctx) t1#gno t2#gno)

  (**
     Bit-vector concatenation.
     <remarks>    
     The arguments must have a bit-vector sort.
     @return 
     The result is a bit-vector of size <c>n1+n2</c>, where <c>n1</c> (<c>n2</c>) 
     is the size of <c>t1</c> (<c>t2</c>).
  *)
  let mk_concat ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_concat (context_gno ctx) t1#gno t2#gno)

  (**
     Bit-vector extraction.
     <remarks>    
     Extract the bits <paramref name="high"/> down to <paramref name="low"/> from a bitvector of
     size <c>m</c> to yield a new bitvector of size <c>n</c>, where 
     <c>n = high - low + 1</c>.
     The argument <paramref name="t"/> must have a bit-vector sort.
  *)
  let mk_extract ( ctx : context ) ( high : int ) ( low : int ) ( t : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_extract (context_gno ctx) high low t#gno)

  (**
     Bit-vector sign extension.
     <remarks>    
     Sign-extends the given bit-vector to the (signed) equivalent bitvector of
     size <c>m+i</c>, where \c m is the size of the given bit-vector.
     The argument <paramref name="t"/> must have a bit-vector sort.
  *)
  let mk_sign_ext  ( ctx : context ) ( i : int ) ( t : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_sign_ext (context_gno ctx) i t#gno)

  (**
     Bit-vector zero extension.
     <remarks>    
     Extend the given bit-vector with zeros to the (unsigned) equivalent
     bitvector of size <c>m+i</c>, where \c m is the size of the
     given bit-vector.
     The argument <paramref name="t"/> must have a bit-vector sort.
  *)
  let mk_zero_ext  ( ctx : context ) ( i : int ) ( t : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_zero_ext (context_gno ctx) i t#gno)

  (**
     Bit-vector repetition.
     <remarks>
     The argument <paramref name="t"/> must have a bit-vector sort.
  *)
  let mk_repeat  ( ctx : context ) ( i : int ) ( t : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_repeat (context_gno ctx) i t#gno)

  (**
     Shift left.

     <remarks>
     It is equivalent to multiplication by <c>2^x</c> where \c x is the value of <paramref name="t2"/>.

     NB. The semantics of shift operations varies between environments. This 
     definition does not necessarily capture directly the semantics of the 
     programming language or assembly architecture you are modeling.

     The arguments must have a bit-vector sort.
  *)
  let mk_shl  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvshl (context_gno ctx) t1#gno t2#gno)

  (**
     Logical shift right
     <remarks>
     It is equivalent to unsigned division by <c>2^x</c> where \c x is the value of <paramref name="t2"/>.

     NB. The semantics of shift operations varies between environments. This 
     definition does not necessarily capture directly the semantics of the 
     programming language or assembly architecture you are modeling.

     The arguments must have a bit-vector sort.
  *)
  let mk_lshr  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvlshr (context_gno ctx) t1#gno t2#gno)

  (**
     Arithmetic shift right
     <remarks>
     It is like logical shift right except that the most significant
     bits of the result always copy the most significant bit of the
     second argument.

     NB. The semantics of shift operations varies between environments. This 
     definition does not necessarily capture directly the semantics of the 
     programming language or assembly architecture you are modeling.

     The arguments must have a bit-vector sort.
  *)
  let mk_ashr  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =    
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_bvashr (context_gno ctx) t1#gno t2#gno)

  (**
     Rotate Left.
     <remarks>
     Rotate bits of \c t to the left \c i times.
     The argument <paramref name="t"/> must have a bit-vector sort.
  *)
  let mk_rotate_left  ( ctx : context ) ( i : int ) ( t : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_rotate_left (context_gno ctx) i t#gno)

  (**
     Rotate Right.
     <remarks>
     Rotate bits of \c t to the right \c i times.
     The argument <paramref name="t"/> must have a bit-vector sort.
  *)
  let mk_rotate_right ( ctx : context ) ( i : int ) ( t : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_rotate_right (context_gno ctx) i t#gno)

  (**
     Rotate Left.
     <remarks>
     Rotate bits of <paramref name="t1"/> to the left <paramref name="t2"/> times.
     The arguments must have the same bit-vector sort.
  *)
  let mk_rotate_left ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_ext_rotate_left (context_gno ctx) t1#gno t2#gno)

  (**
     Rotate Right.

     <remarks>
     Rotate bits of <paramref name="t1"/> to the right<paramref name="t2"/> times.
     The arguments must have the same bit-vector sort.
  *)
  let mk_rotate_right ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_ext_rotate_right (context_gno ctx) t1#gno t2#gno)

  (**
     Create an <paramref name="n"/> bit bit-vector from the integer argument <paramref name="t"/>.

     <remarks>
     NB. This function is essentially treated as uninterpreted. 
     So you cannot expect Z3 to precisely reflect the semantics of this function
     when solving constraints with this function.

     The argument must be of integer sort.
  *)
  let mk_int2bv ( ctx : context ) ( n : int ) ( t : int_expr ) =
    (new bitvec_expr ctx)#cnstr_obj (Z3native.mk_int2bv (context_gno ctx) n t#gno)

  (**
     Create an integer from the bit-vector argument <paramref name="t"/>.

     <remarks>
     If \c is_signed is false, then the bit-vector \c t1 is treated as unsigned. 
     So the result is non-negative and in the range <c>[0..2^N-1]</c>, where 
     N are the number of bits in <paramref name="t"/>.
     If \c is_signed is true, \c t1 is treated as a signed bit-vector.

     NB. This function is essentially treated as uninterpreted. 
     So you cannot expect Z3 to precisely reflect the semantics of this function
     when solving constraints with this function.

     The argument must be of bit-vector sort.
  *)
  let mk_bv2int  ( ctx : context ) ( t : bitvec_expr ) ( signed : bool) =
    (new int_expr ctx)#cnstr_obj (Z3native.mk_bv2int (context_gno ctx) t#gno signed)

  (**
     Create a predicate that checks that the bit-wise addition does not overflow.
     <remarks>
     The arguments must be of bit-vector sort.
  *)
  let mk_add_no_overflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) ( signed : bool) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvadd_no_overflow (context_gno ctx) t1#gno t2#gno signed)

  (**
     Create a predicate that checks that the bit-wise addition does not underflow.
     <remarks>
     The arguments must be of bit-vector sort.
  *)
  let mk_add_no_underflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvadd_no_underflow (context_gno ctx) t1#gno t2#gno)

  (**
     Create a predicate that checks that the bit-wise subtraction does not overflow.
     <remarks>
     The arguments must be of bit-vector sort.
  *)
  let mk_sub_no_overflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvsub_no_overflow (context_gno ctx) t1#gno t2#gno)

  (**
     Create a predicate that checks that the bit-wise subtraction does not underflow.
     <remarks>
     The arguments must be of bit-vector sort.
  *)
  let mk_sub_no_underflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) ( signed : bool) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvsub_no_underflow (context_gno ctx) t1#gno t2#gno signed)

  (**
     Create a predicate that checks that the bit-wise signed division does not overflow.
     <remarks>
     The arguments must be of bit-vector sort.
  *)
  let mk_sdiv_no_overflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvsdiv_no_overflow (context_gno ctx) t1#gno t2#gno)

  (**
     Create a predicate that checks that the bit-wise negation does not overflow.
     <remarks>
     The arguments must be of bit-vector sort.
  *)
  let mk_neg_no_overflow  ( ctx : context ) ( t : bitvec_expr) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvneg_no_overflow (context_gno ctx) t#gno)

  (**
     Create a predicate that checks that the bit-wise multiplication does not overflow.
     <remarks>
     The arguments must be of bit-vector sort.
  *)
  let mk_mul_no_overflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) ( signed : bool) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvmul_no_overflow (context_gno ctx) t1#gno t2#gno signed)

  (**
     Create a predicate that checks that the bit-wise multiplication does not underflow.
     <remarks>
     The arguments must be of bit-vector sort.
  *)
  let mk_mul_no_underflow  ( ctx : context ) ( t1 : bitvec_expr ) ( t2 : bitvec_expr ) =
    (new bool_expr ctx)#cnstr_obj (Z3native.mk_bvmul_no_underflow (context_gno ctx) t1#gno t2#gno)
      
  (**
     Create a bit-vector numeral.
     
     @param v A string representing the value in decimal notation.
     @param size the size of the bit-vector
  *)
  let mk_numeral ( ctx : context ) ( ctx : context ) ( v : string ) ( size : int) =
    (new bitvec_num ctx)#cnstr_obj (Z3native.mk_numeral (context_gno ctx) v (mk_sort ctx size)#gno)
end

(** Functions to manipulate proof expressions *)
module Proofs = 
struct
  (**
     Indicates whether the term is a Proof for the expression 'true'.
  *)
  let is_true ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_TRUE)

  (**
     Indicates whether the term is a proof for a fact asserted by the user.
  *)
  let is_asserted ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_ASSERTED)

  (**
     Indicates whether the term is a proof for a fact (tagged as goal) asserted by the user.
  *)
  let is_goal ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_GOAL)

  (**
     Indicates whether the term is proof via modus ponens
     <remarks>
     Given a proof for p and a proof for (implies p q), produces a proof for q.
     T1: p
     T2: (implies p q)
     [mp T1 T2]: q
     The second antecedents may also be a proof for (iff p q).
  *)
  let is_modus_ponens ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_MODUS_PONENS)

  (**
     Indicates whether the term is a proof for (R t t), where R is a reflexive relation.
     <remarks>This proof object has no antecedents. 
     The only reflexive relations that are used are 
     equivalence modulo namings, equality and equivalence.
     That is, R is either '~', '=' or 'iff'.
  *)
  let is_reflexivity ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_REFLEXIVITY)

  (**
     Indicates whether the term is proof by symmetricity of a relation
     <remarks>
     Given an symmetric relation R and a proof for (R t s), produces a proof for (R s t).
     T1: (R t s)
     [symmetry T1]: (R s t)
     T1 is the antecedent of this proof object.
  *)
  let is_symmetry ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_SYMMETRY)

  (**
     Indicates whether the term is a proof by transitivity of a relation
     <remarks>
     Given a transitive relation R, and proofs for (R t s) and (R s u), produces a proof 
     for (R t u). 
     T1: (R t s)
     T2: (R s u)
     [trans T1 T2]: (R t u)
  *)
  let is_transitivity ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_TRANSITIVITY)

  (**
     Indicates whether the term is a proof by condensed transitivity of a relation
     <remarks>
     Condensed transitivity proof. This proof object is only used if the parameter PROOF_MODE is 1.
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
     antecedent (R a b) as an edge between a and b.
  *)
  let is_Transitivity_star ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_TRANSITIVITY_STAR)


  (**
     Indicates whether the term is a monotonicity proof object.
     <remarks>
     T1: (R t_1 s_1)
     ...
     Tn: (R t_n s_n)
     [monotonicity T1 ... Tn]: (R (f t_1 ... t_n) (f s_1 ... s_n))          
     Remark: if t_i == s_i, then the antecedent Ti is suppressed.
     That is, reflexivity proofs are supressed to save space.
  *)
  let is_monotonicity ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_MONOTONICITY)

  (**
     Indicates whether the term is a quant-intro proof 
     <remarks>
     Given a proof for (~ p q), produces a proof for (~ (forall (x) p) (forall (x) q)).
     T1: (~ p q)
     [quant-intro T1]: (~ (forall (x) p) (forall (x) q))
  *)
  let is_quant_intro ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_QUANT_INTRO)

  (**
     Indicates whether the term is a distributivity proof object.  
     <remarks>
     Given that f (= or) distributes over g (= and), produces a proof for
     (= (f a (g c d))
     (g (f a c) (f a d)))
     If f and g are associative, this proof also justifies the following equality:
     (= (f (g a b) (g c d))
     (g (f a c) (f a d) (f b c) (f b d)))
     where each f and g can have arbitrary number of arguments.
     
     This proof object has no antecedents.
     Remark. This rule is used by the CNF conversion pass and 
     instantiated by f = or, and g = and.
  *)
  let is_distributivity ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_DISTRIBUTIVITY)

  (**
     Indicates whether the term is a proof by elimination of AND
     <remarks>
     Given a proof for (and l_1 ... l_n), produces a proof for l_i
     T1: (and l_1 ... l_n)
     [and-elim T1]: l_i
  *)
  let is_and_elimination ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_AND_ELIM)

  (**
     Indicates whether the term is a proof by eliminiation of not-or
     <remarks>
     Given a proof for (not (or l_1 ... l_n)), produces a proof for (not l_i).
     T1: (not (or l_1 ... l_n))
     [not-or-elim T1]: (not l_i)       
  *)
  let is_or_elimination ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_NOT_OR_ELIM)

  (**
     Indicates whether the term is a proof by rewriting
     <remarks>
     A proof for a local rewriting step (= t s).
     The head function symbol of t is interpreted.
     
     This proof object has no antecedents.
     The conclusion of a rewrite rule is either an equality (= t s), 
     an equivalence (iff t s), or equi-satisfiability (~ t s).
     Remark: if f is bool, then = is iff.
     
     Examples:
     (= (+ ( x : expr ) 0) x)
     (= (+ ( x : expr ) 1 2) (+ 3 x))
     (iff (or ( x : expr ) false) x)          
  *)
  let is_rewrite ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_REWRITE)

  (**
     Indicates whether the term is a proof by rewriting
     <remarks>
     A proof for rewriting an expression t into an expression s.
     This proof object is used if the parameter PROOF_MODE is 1.
     This proof object can have n antecedents.
     The antecedents are proofs for equalities used as substitution rules.
     The object is also used in a few cases if the parameter PROOF_MODE is 2.
     The cases are:
     - When applying contextual simplification (CONTEXT_SIMPLIFIER=true)
     - When converting bit-vectors to Booleans (BIT2BOOL=true)
     - When pulling ite expression up (PULL_CHEAP_ITE_TREES=true)
  *)
  let is_rewrite_star ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_REWRITE_STAR)

  (**
     Indicates whether the term is a proof for pulling quantifiers out.
     <remarks>
     A proof for (iff (f (forall (x) q(x)) r) (forall (x) (f (q x) r))). This proof object has no antecedents.
  *)
  let is_pull_quant ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_PULL_QUANT)

  (**
     Indicates whether the term is a proof for pulling quantifiers out.
     <remarks>
     A proof for (iff P Q) where Q is in prenex normal form. 
     This proof object is only used if the parameter PROOF_MODE is 1.       
     This proof object has no antecedents
  *)
  let is_pull_quant_star ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_PULL_QUANT_STAR)

  (**
     Indicates whether the term is a proof for pushing quantifiers in.
     <remarks>
     A proof for:
     (iff (forall (x_1 ... x_m) (and p_1[x_1 ... x_m] ... p_n[x_1 ... x_m]))
     (and (forall (x_1 ... x_m) p_1[x_1 ... x_m])
     ... 
     (forall (x_1 ... x_m) p_n[x_1 ... x_m])))               
     This proof object has no antecedents
  *)

  let is_push_quant ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_PUSH_QUANT)

  (**
     Indicates whether the term is a proof for elimination of unused variables.
     <remarks>
     A proof for (iff (forall (x_1 ... x_n y_1 ... y_m) p[x_1 ... x_n])
     (forall (x_1 ... x_n) p[x_1 ... x_n])) 
     
     It is used to justify the elimination of unused variables.
     This proof object has no antecedents.
  *)

  let is_elim_unused_vars ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_ELIM_UNUSED_VARS)

  (**
     Indicates whether the term is a proof for destructive equality resolution
     <remarks>
     A proof for destructive equality resolution:
     (iff (forall (x) (or (not (= ( x : expr ) t)) P[x])) P[t])
     if ( x : expr ) does not occur in t.
     
     This proof object has no antecedents.
     
     Several variables can be eliminated simultaneously.
  *)

  let is_der ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_DER)

  (**
     Indicates whether the term is a proof for quantifier instantiation
     <remarks>
     A proof of (or (not (forall (x) (P x))) (P a))
  *)
  let is_quant_inst ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_QUANT_INST)

  (**
     Indicates whether the term is a hypthesis marker.
     <remarks>Mark a hypothesis in a natural deduction style proof.
  *)
  let is_hypothesis ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_HYPOTHESIS)

  (**
     Indicates whether the term is a proof by lemma
     <remarks>
     T1: false
     [lemma T1]: (or (not l_1) ... (not l_n))
     
     This proof object has one antecedent: a hypothetical proof for false.
     It converts the proof in a proof for (or (not l_1) ... (not l_n)),
     when T1 contains the hypotheses: l_1, ..., l_n.
  *)
  let is_lemma ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_LEMMA)

  (**
     Indicates whether the term is a proof by unit resolution
     <remarks>
     T1:      (or l_1 ... l_n l_1' ... l_m')
     T2:      (not l_1)
     ...
     T(n+1):  (not l_n)
     [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m')
  *)
  let is_unit_resolution ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_UNIT_RESOLUTION)

  (**
     Indicates whether the term is a proof by iff-true
     <remarks>
     T1: p
     [iff-true T1]: (iff p true)
  *)
  let is_iff_true ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_IFF_TRUE)

  (**
     Indicates whether the term is a proof by iff-false
     <remarks>
     T1: (not p)
     [iff-false T1]: (iff p false)
  *)
  let is_iff_false ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_IFF_FALSE)

  (**
     Indicates whether the term is a proof by commutativity
     <remarks>
     [comm]: (= (f a b) (f b a))
     
     f is a commutative operator.
     
     This proof object has no antecedents.
     Remark: if f is bool, then = is iff.
  *)
  let is_commutativity ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_COMMUTATIVITY) (*  *)

  (**
     Indicates whether the term is a proof for Tseitin-like axioms
     <remarks>
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
     bounded number of steps (=3).
  *)
  let is_def_axiom ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_DEF_AXIOM)

  (**
     Indicates whether the term is a proof for introduction of a name
     <remarks>
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
     [def-intro]: (= n e)       
  *)
  let is_def_intro ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_DEF_INTRO)

  (**
     Indicates whether the term is a proof for application of a definition
     <remarks>
     [apply-def T1]: F ~ n
     F is 'equivalent' to n, given that T1 is a proof that
     n is a name for F.
  *)
  let is_apply_def ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_APPLY_DEF)

  (**
     Indicates whether the term is a proof iff-oeq
     <remarks>
     T1: (iff p q)
     [iff~ T1]: (~ p q)
  *)
  let is_iff_oeq ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_IFF_OEQ)

  (**
     Indicates whether the term is a proof for a positive NNF step
     <remarks>
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
     over Boolean connectives 'and' and 'or'.
  *)
  let is_nnf_pos ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_NNF_POS)

  (**
     Indicates whether the term is a proof for a negative NNF step
     <remarks>
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
     (and (or r_1 r_2) (or r_1' r_2')))
  *)
  let is_nnf_neg ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_NNF_NEG)

  (**
     Indicates whether the term is a proof for (~ P Q) here Q is in negation normal form.
     <remarks>
     A proof for (~ P Q) where Q is in negation normal form.
     
     This proof object is only used if the parameter PROOF_MODE is 1.       
     
     This proof object may have n antecedents. Each antecedent is a PR_DEF_INTRO.
  *)
  let is_nnf_star ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_NNF_STAR)

  (**
     Indicates whether the term is a proof for (~ P Q) where Q is in conjunctive normal form.
     <remarks>
     A proof for (~ P Q) where Q is in conjunctive normal form.
     This proof object is only used if the parameter PROOF_MODE is 1.       
     This proof object may have n antecedents. Each antecedent is a PR_DEF_INTRO.          
  *)
  let is_cnf_star ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_CNF_STAR)

  (**
     Indicates whether the term is a proof for a Skolemization step
     <remarks>
     Proof for: 
     
     [sk]: (~ (not (forall ( x : expr ) (p ( x : expr ) y))) (not (p (sk y) y)))
     [sk]: (~ (exists ( x : expr ) (p ( x : expr ) y)) (p (sk y) y))
     
     This proof object has no antecedents.
  *)
  let is_skolemize ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_SKOLEMIZE)

  (**
     Indicates whether the term is a proof by modus ponens for equi-satisfiability.
     <remarks>
     Modus ponens style rule for equi-satisfiability.
     T1: p
     T2: (~ p q)
     [mp~ T1 T2]: q  
  *)
  let is_modus_ponens_oeq ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_MODUS_PONENS_OEQ)

  (**
     Indicates whether the term is a proof for theory lemma
     <remarks>
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
     - gcd-test - Indicates an integer linear arithmetic lemma that uses a gcd test.
  *)
  let is_theory_lemma ( x : expr ) = (FuncDecl.get_decl_kind (Expr.get_func_decl x) == OP_PR_TH_LEMMA)
end

(** 
    Parameter sets (of Solvers, Tactics, ...)

    A Params objects represents a configuration in the form of symbol/value pairs.
*)
module Params =
struct
(** ParamDescrs describe sets of parameters (of Solvers, Tactics, ...) *)
module ParamDescrs =
struct

  (** Validate a set of parameters. *)
  let validate ( x : param_descrs ) ( p : params )= Z3native.params_validate x#gnc p#gno x#gno
    
  (** Retrieve kind of parameter. *)
  let get_kind ( x : param_descrs ) ( name : symbol ) = 
    (param_kind_of_int (Z3native.param_descrs_get_kind x#gnc x#gno name#gno))
      
  (** Retrieve all names of parameters. *)
  let get_names ( x : param_descrs ) =
    let n = Z3native.param_descrs_size x#gnc x#gno in
    let f i = create_symbol x#gc (Z3native.param_descrs_get_name x#gnc x#gno i) in
    Array.init n f
      
  (** The size of the ParamDescrs. *)
  let get_size ( x : param_descrs ) = Z3native.param_descrs_size x#gnc x#gno
    
  (** Retrieves a string representation of the ParamDescrs. *)
  let to_string ( x : param_descrs ) = Z3native.param_descrs_to_string x#gnc x#gno 
end

  (**
     Adds a parameter setting.
  *)
  let add_bool (p : params) (name : symbol) (value : bool) =
    Z3native.params_set_bool p#gnc p#gno name#gno value
      
  (**
     Adds a parameter setting.
  *)
  let add_int (p : params) (name : symbol) (value : int) =
    Z3native.params_set_uint p#gnc p#gno name#gno value
      
  (**
     Adds a parameter setting.
  *)
  let add_double (p : params) (name : symbol) (value : float) =
    Z3native.params_set_double p#gnc p#gno name#gno value

  (**
     Adds a parameter setting.
  *)
  let add_symbol (p : params) (name : symbol) (value : symbol) =
    Z3native.params_set_symbol p#gnc p#gno name#gno value#gno

  (**
     Adds a parameter setting.
  *)
  let add_s_bool (p : params) (name : string) (value : bool) =
    add_bool p ((new symbol p#gc)#cnstr_obj (Z3native.mk_string_symbol p#gnc name)) value
      
  (**
     Adds a parameter setting.
  *)
  let add_s_int (p : params) (name : string) (value : int) =
    add_int p ((new symbol p#gc)#cnstr_obj (Z3native.mk_string_symbol p#gnc name)) value
      
  (**
     Adds a parameter setting.
  *)
  let add_s_double (p : params) (name : string) (value : float) =
    add_double p ((new symbol p#gc)#cnstr_obj (Z3native.mk_string_symbol p#gnc name)) value

  (**
     Adds a parameter setting.
  *)
  let add_s_symbol (p : params) (name : string) (value : symbol) =
    add_symbol p ((new symbol p#gc)#cnstr_obj (Z3native.mk_string_symbol p#gnc name)) value

  (**
     Creates a new parameter set
  *)
  let mk_params ( ctx : context ) =
    (new params ctx)#cnstr_obj (Z3native.mk_params (context_gno ctx))

  (**
     A string representation of the parameter set.
  *)
  let to_string (p : params) = Z3native.params_to_string p#gnc p#gno
end

(** Goals 

    A goal (aka problem). A goal is essentially a 
    of formulas, that can be solved and/or transformed using
    tactics and solvers. *)
module Goal =
struct

  (** The precision of the goal. 

      Goals can be transformed using over and under approximations.
      An under approximation is applied when the objective is to find a model for a given goal.
      An over approximation is applied when the objective is to find a proof for a given goal.
  *)
  let get_precision ( x : goal ) =
    goal_prec_of_int (Z3native.goal_precision x#gnc x#gno)
      
  (** Indicates whether the goal is precise. *)
  let is_precise ( x : goal ) =
    (get_precision x) == GOAL_PRECISE
      
  (** Indicates whether the goal is an under-approximation. *)
  let is_underapproximation ( x : goal ) =
    (get_precision x) == GOAL_UNDER

  (** Indicates whether the goal is an over-approximation. *)
  let is_overapproximation ( x : goal ) =
    (get_precision x) == GOAL_OVER
      
  (** Indicates whether the goal is garbage (i.e., the product of over- and under-approximations). *)
  let is_garbage ( x : goal ) = 
    (get_precision x) == GOAL_UNDER_OVER
      
  (** Adds the constraints to the given goal. *)
  (* CMW: assert seems to be a keyword. *)
  let assert_ ( x : goal ) ( constraints : bool_expr array ) =
    let f e = Z3native.goal_assert x#gnc x#gno e#gno in
    ignore (Array.map f constraints) ;
    ()
      
  (** Indicates whether the goal contains `false'. *)
  let is_inconsistent ( x : goal ) =
    Z3native.goal_inconsistent x#gnc x#gno

  (** The depth of the goal.      
      This tracks how many transformations were applied to it. *)
  let get_depth ( x : goal ) = Z3native.goal_depth x#gnc x#gno
    
  (** Erases all formulas from the given goal. *)
  let reset ( x : goal ) =  Z3native.goal_reset x#gnc x#gno
    
  (** The number of formulas in the goal. *)
  let get_size ( x : goal ) = Z3native.goal_size x#gnc x#gno

  (** The formulas in the goal. *)
  let get_formulas ( x : goal ) =
    let n = get_size x in 
    let f i = (new bool_expr x#gc)#cnstr_obj (Z3native.goal_formula x#gnc x#gno i) in
    Array.init n f

  (** The number of formulas, subformulas and terms in the goal. *)
  let get_num_exprs ( x : goal ) =  Z3native.goal_num_exprs x#gnc x#gno
    
  (** Indicates whether the goal is empty, and it is precise or the product of an under approximation. *)
  let is_decided_sat ( x : goal ) = 
    Z3native.goal_is_decided_sat x#gnc x#gno
      
  (** Indicates whether the goal contains `false', and it is precise or the product of an over approximation. *)
  let is_decided_unsat ( x : goal ) =
    Z3native.goal_is_decided_unsat x#gnc x#gno
      
  (**  Translates (copies) the Goal to the target Context <paramref name="to_ctx"/>. *)
  let translate ( x : goal ) ( to_ctx : context ) =
    (new goal to_ctx)#cnstr_obj (Z3native.goal_translate x#gnc x#gno (context_gno to_ctx))

  (** Simplifies the goal. Essentially invokes the `simplify' tactic on the goal. *)
  let simplify ( x : goal ) ( p : params option ) =
    let tn = Z3native.mk_tactic x#gnc "simplify" in
    Z3native.tactic_inc_ref x#gnc tn ;
    let arn = match p with
      | None -> Z3native.tactic_apply x#gnc tn x#gno 
      | Some(pn) -> Z3native.tactic_apply_ex x#gnc tn x#gno pn#gno
    in
    Z3native.apply_result_inc_ref x#gnc arn ;
    let sg = Z3native.apply_result_get_num_subgoals x#gnc arn in
    let res = if sg == 0 then 
	raise (Z3native.Exception "No subgoals") 
      else 
	Z3native.apply_result_get_subgoal x#gnc arn 0 in
    Z3native.apply_result_dec_ref x#gnc arn ;
    Z3native.tactic_dec_ref x#gnc tn ;
    (new goal x#gc)#cnstr_obj res


  (**
     Creates a new Goal.
     <remarks>
     Note that the Context must have been created with proof generation support if 
     <paramref name="proofs"/> is set to true here.
     @param models Indicates whether model generation should be enabled.
     @param unsat_cores Indicates whether unsat core generation should be enabled.
     @param proofs Indicates whether proof generation should be enabled.    
  *)
  let mk_goal ( ctx : context ) ( models : bool ) ( unsat_cores : bool ) ( proofs : bool ) = 
    (new goal ctx)#cnstr_obj (Z3native.mk_goal (context_gno ctx) models unsat_cores proofs)

  (**  A string representation of the Goal. *)
  let to_string ( x : goal ) = Z3native.goal_to_string x#gnc x#gno
end  


(** Models

    A Model contains interpretations (assignments) of constants and functions. *)
module Model =
struct
  type model = z3_native_object
      
  (**/**)
  let model_cnstr ( ctx : context ) ( no : Z3native.ptr ) = 
    let res : model = { m_ctx = ctx ;
			 m_n_obj = null ;
			 inc_ref = Z3native.model_inc_ref ;
			 dec_ref = Z3native.model_dec_ref } in
    (z3obj_sno res ctx no) ;
    (z3obj_cnstr res) ;
    res
  (**/**)

  (** Function interpretations 

      A function interpretation is represented as a finite map and an 'else'.
      Each entry in the finite map represents the value of a function given a set of arguments.  
  *)
  module FuncInterp =
  struct

    (** Function interpretations entries 

	An Entry object represents an element in the finite map used to a function interpretation.
    *)
    module FuncEntry =
    struct
      (**
	 Return the (symbolic) value of this entry.
      *)
      let get_value ( x : func_entry ) =
	create_expr x#gc (Z3native.func_entry_get_value x#gnc x#gno)

      (**
	 The number of arguments of the entry.
      *)
      let get_num_args ( x : func_entry ) = Z3native.func_entry_get_num_args x#gnc x#gno
	
      (**
	 The arguments of the function entry.
      *)
      let get_args ( x : func_entry ) =
	let n = (get_num_args x) in
	let f i = (create_expr x#gc (Z3native.func_entry_get_arg x#gnc x#gno i)) in
	Array.init n f
	  
      (**
	 A string representation of the function entry.
      *)
      let to_string ( x : func_entry ) =
	let a = (get_args x) in
	let f c p = (p ^ (Expr.to_string c) ^ ", ") in
	"[" ^ Array.fold_right f a ((Expr.to_string (get_value x)) ^ "]")
    end

    (**
       The number of entries in the function interpretation.
    *)
    let get_num_entries ( x: func_interp ) = Z3native.func_interp_get_num_entries x#gnc x#gno

    (**
       The entries in the function interpretation
    *)
    let get_entries ( x : func_interp ) =
      let n = (get_num_entries x) in
      let f i = ((new func_entry x#gc)#cnstr_obj (Z3native.func_interp_get_entry x#gnc x#gno i)) in
      Array.init n f

    (**
       The (symbolic) `else' value of the function interpretation.
    *)
    let get_else ( x : func_interp ) = create_expr x#gc (Z3native.func_interp_get_else x#gnc x#gno)

    (**
       The arity of the function interpretation
    *)
    let get_arity ( x : func_interp ) = Z3native.func_interp_get_arity x#gnc x#gno

    (**
       A string representation of the function interpretation.
    *)    
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
    
  (** Retrieves the interpretation (the assignment) of <paramref name="f"/> in the model. 
      <param name="f">A function declaration of zero arity</param>
      <returns>An expression if the function has an interpretation in the model, null otherwise.</returns> *)
  let get_const_interp ( x : model ) ( f : func_decl ) =
    if (FuncDecl.get_arity f) != 0 ||
      (sort_kind_of_int (Z3native.get_sort_kind f#gnc (Z3native.get_range f#gnc f#gno))) == ARRAY_SORT then
      raise (Z3native.Exception "Non-zero arity functions and arrays have FunctionInterpretations as a model. Use FuncInterp.")
    else
      let np = Z3native.model_get_const_interp (z3obj_gnc x) (z3obj_gno x) f#gno in
      if (Z3native.is_null np) then
	None
      else
	Some (create_expr (z3obj_gc x) np)

  (** Retrieves the interpretation (the assignment) of <paramref name="a"/> in the model. 
      <param name="a">A Constant</param>
      <returns>An expression if the constant has an interpretation in the model, null otherwise.</returns>
  *)
  let get_const_interp_e ( x : model ) ( a : expr ) = get_const_interp x (Expr.get_func_decl a)


  (** Retrieves the interpretation (the assignment) of a non-constant <paramref name="f"/> in the model. 
      <param name="f">A function declaration of non-zero arity</param>
      <returns>A FunctionInterpretation if the function has an interpretation in the model, null otherwise.</returns> *)
  let rec get_func_interp ( x : model ) ( f : func_decl ) =
    let sk = (sort_kind_of_int (Z3native.get_sort_kind (z3obj_gnc x) (Z3native.get_range f#gnc f#gno))) in
    if (FuncDecl.get_arity f) == 0 then
      let n = Z3native.model_get_const_interp (z3obj_gnc x) (z3obj_gno x) f#gno in      
      if (Z3native.is_null n) then
	None 
      else 
	match sk with
	  | ARRAY_SORT ->	    
	    if not (Z3native.is_as_array (z3obj_gnc x) n) then
	      raise (Z3native.Exception "Argument was not an array constant")
	    else
	      let fd = Z3native.get_as_array_func_decl (z3obj_gnc x) n in
              get_func_interp x ((new func_decl f#gc)#cnstr_obj fd)
	  | _ -> raise (Z3native.Exception "Constant functions do not have a function interpretation; use ConstInterp");
    else
      let n = (Z3native.model_get_func_interp (z3obj_gnc x) (z3obj_gno x) f#gno) in
      if (Z3native.is_null n) then None else Some ((new func_interp (z3obj_gc x))#cnstr_obj n)
	
  (** The number of constants that have an interpretation in the model. *)
  let get_num_consts ( x : model ) = Z3native.model_get_num_consts (z3obj_gnc x) (z3obj_gno x)
    
  (** The function declarations of the constants in the model. *)
  let get_const_decls ( x : model ) = 
    let n = (get_num_consts x) in
    let f i = (new func_decl (z3obj_gc x))#cnstr_obj (Z3native.model_get_const_decl (z3obj_gnc x) (z3obj_gno x) i) in
    Array.init n f
      
      
  (** The number of function interpretations in the model. *)
  let get_num_funcs ( x : model ) = Z3native.model_get_num_funcs (z3obj_gnc x) (z3obj_gno x)
    
  (** The function declarations of the function interpretations in the model. *)
  let get_func_decls ( x : model ) = 
    let n = (get_num_consts x) in
    let f i = (new func_decl (z3obj_gc x))#cnstr_obj (Z3native.model_get_func_decl (z3obj_gnc x) (z3obj_gno x) i) in
    Array.init n f
      
  (** All symbols that have an interpretation in the model. *)
  let get_decls ( x : model ) =
    let n_funcs = (get_num_funcs x) in
    let n_consts = (get_num_consts x ) in
    let f i = (new func_decl (z3obj_gc x))#cnstr_obj (Z3native.model_get_func_decl (z3obj_gnc x) (z3obj_gno x) i) in
    let g i = (new func_decl (z3obj_gc x))#cnstr_obj (Z3native.model_get_const_decl (z3obj_gnc x) (z3obj_gno x) i) in
    Array.append (Array.init n_funcs f) (Array.init n_consts g)
      
  (** A ModelEvaluationFailedException is thrown when an expression cannot be evaluated by the model. *)
  exception ModelEvaluationFailedException of string
      
  (**
     Evaluates the expression <paramref name="t"/> in the current model.
     
     <remarks>
     This function may fail if <paramref name="t"/> contains quantifiers, 
     is partial (MODEL_PARTIAL enabled), or if <paramref name="t"/> is not well-sorted.
     In this case a <c>ModelEvaluationFailedException</c> is thrown.

     <param name="t">An expression</param>
     <param name="completion">
     When this flag is enabled, a model value will be assigned to any constant 
     or function that does not have an interpretation in the model.
     </param>
     <returns>The evaluation of <paramref name="t"/> in the model.</returns>        
  *)
  let eval ( x : model ) ( t : expr ) ( completion : bool ) =
    let (r, v) = (Z3native.model_eval (z3obj_gnc x) (z3obj_gno x) t#gno completion) in
    if not r then
      raise (ModelEvaluationFailedException "evaluation failed")
    else
      create_expr (z3obj_gc x) v

  (** Alias for <c>eval</c>. *)
  let evaluate ( x : model ) ( t : expr ) ( completion : bool ) =
    eval x t completion
      
  (** The number of uninterpreted sorts that the model has an interpretation for. *)
  let get_num_sorts ( x : model ) = Z3native.model_get_num_sorts (z3obj_gnc x) (z3obj_gno x)
    
  (** The uninterpreted sorts that the model has an interpretation for. 
      <remarks>
      Z3 also provides an intepretation for uninterpreted sorts used in a formula.
      The interpretation for a sort is a finite set of distinct values. We say this finite set is
      the "universe" of the sort.
      <seealso cref="NumSorts"/>
      <seealso cref="SortUniverse"/>
  *)
  let get_sorts ( x : model ) =
    let n = (get_num_sorts x) in
    let f i = (create_sort (z3obj_gc x) (Z3native.model_get_sort (z3obj_gnc x) (z3obj_gno x) i)) in
    Array.init n f


  (** The finite set of distinct values that represent the interpretation for sort <paramref name="s"/>. 
      <seealso cref="Sorts"/>
      <param name="s">An uninterpreted sort</param>
      <returns>An array of expressions, where each is an element of the universe of <paramref name="s"/></returns>
  *)
  let sort_universe ( x : model ) ( s : sort ) =
    let n_univ = (new ast_vector (z3obj_gc x))#cnstr_obj (Z3native.model_get_sort_universe (z3obj_gnc x) (z3obj_gno x) s#gno) in
    let n = (AST.ASTVector.get_size n_univ) in
    let f i = (AST.ASTVector.get n_univ i) in
    Array.init n f
      
  (** Conversion of models to strings. 
      <returns>A string representation of the model.</returns>
  *)
  let to_string ( x : model ) = Z3native.model_to_string (z3obj_gnc x) (z3obj_gno x) 
end


(** Tactics

    Tactics are the basic building block for creating custom solvers for specific problem domains.
    The complete list of tactics may be obtained using <c>Context.get_num_tactics</c> 
    and <c>Context.get_tactic_names</c>.
    It may also be obtained using the command <c>(help-tactics)</c> in the SMT 2.0 front-end.
*)
module Tactic =
struct
(** Tactic application results 
    
    ApplyResult objects represent the result of an application of a 
    tactic to a goal. It contains the subgoals that were produced. *)
module ApplyResult =
struct 
  (** The number of Subgoals. *)
  let get_num_subgoals ( x : apply_result ) =
    Z3native.apply_result_get_num_subgoals x#gnc x#gno
      
  (** Retrieves the subgoals from the apply_result. *)
  let get_subgoals ( x : apply_result ) =
    let n = (get_num_subgoals x) in
    let f i = (new goal x#gc)#cnstr_obj (Z3native.apply_result_get_subgoal x#gnc x#gno i) in
    Array.init n f

  (** Retrieves the subgoals from the apply_result. *)
  let get_subgoal ( x : apply_result ) ( i : int ) =
    (new goal x#gc)#cnstr_obj (Z3native.apply_result_get_subgoal x#gnc x#gno i)
      
  (** Convert a model for the subgoal <paramref name="i"/> into a model for the original 
      goal <c>g</c>, that the ApplyResult was obtained from. 
      #return A model for <c>g</c>
  *)
  let convert_model ( x : apply_result ) ( i : int ) ( m : Model.model ) =
    Model.model_cnstr x#gc (Z3native.apply_result_convert_model x#gnc x#gno i (z3obj_gno m))
      
  (** A string representation of the ApplyResult. *)
  let to_string ( x : apply_result ) = Z3native.apply_result_to_string x#gnc x#gno
end

  (** A string containing a description of parameters accepted by the tactic. *)
  let get_help ( x : tactic ) = Z3native.tactic_get_help x#gnc x#gno


  (** Retrieves parameter descriptions for Tactics. *)
  let get_param_descrs ( x : tactic ) =
    (new param_descrs x#gc)#cnstr_obj (Z3native.tactic_get_param_descrs x#gnc x#gno)
      
  (** Apply the tactic to the goal. *)
  let apply ( x : tactic ) ( g : goal ) ( p : params option ) =
    match p with 
      | None -> (new apply_result x#gc)#cnstr_obj (Z3native.tactic_apply x#gnc x#gno g#gno)
      | Some (pn) -> (new apply_result x#gc)#cnstr_obj (Z3native.tactic_apply_ex x#gnc x#gno g#gno pn#gno)

  (**
     The number of supported tactics.
  *)
  let get_num_tactics ( ctx : context ) = Z3native.get_num_tactics (context_gno ctx)

  (**
     The names of all supported tactics.
  *)
  let get_tactic_names ( ctx : context ) =
    let n = (get_num_tactics ctx ) in
    let f i = (Z3native.get_tactic_name (context_gno ctx) i) in
    Array.init n f


  (**
     Returns a string containing a description of the tactic with the given name.
  *)
  let get_tactic_description ( ctx : context ) ( name : string ) =
    Z3native.tactic_get_descr (context_gno ctx) name

  (**
     Creates a new Tactic.
  *)    
  let mk_tactic ( ctx : context ) ( name : string ) =
    (new tactic ctx)#cnstr_obj (Z3native.mk_tactic (context_gno ctx) name)

  (**
     Create a tactic that applies <paramref name="t1"/> to a Goal and
     then <paramref name="t2"/> to every subgoal produced by <paramref name="t1"/>.
  *)
  let and_then ( ctx : context ) ( t1 : tactic ) ( t2 : tactic ) ( ts : tactic array ) =
    let f p c = (match p with 
      | None -> (Some c#gno) 
      | Some(x) -> (Some (Z3native.tactic_and_then (context_gno ctx) c#gno x))) in
    match (Array.fold_left f None ts) with
      | None -> (new tactic ctx)#cnstr_obj (Z3native.tactic_and_then (context_gno ctx) t1#gno t2#gno)
      | Some(x) ->
	let o = (Z3native.tactic_and_then (context_gno ctx) t2#gno x) in
	(new tactic ctx)#cnstr_obj (Z3native.tactic_and_then (context_gno ctx) t1#gno o)

  (**
     Create a tactic that first applies <paramref name="t1"/> to a Goal and
     if it fails then returns the result of <paramref name="t2"/> applied to the Goal.
  *)
  let or_else ( ctx : context ) ( t1 : tactic ) ( t2 : tactic ) =
    (new tactic ctx)#cnstr_obj (Z3native.tactic_or_else (context_gno ctx) t1#gno t2#gno)

  (**
     Create a tactic that applies <paramref name="t"/> to a goal for <paramref name="ms"/> milliseconds.    
     <remarks>
     If <paramref name="t"/> does not terminate within <paramref name="ms"/> milliseconds, then it fails.
  *)
  let try_for ( ctx : context ) ( t : tactic ) ( ms : int ) =
    (new tactic ctx)#cnstr_obj (Z3native.tactic_try_for (context_gno ctx) t#gno ms)

  (**
     Create a tactic that applies <paramref name="t"/> to a given goal if the probe 
     <paramref name="p"/> evaluates to true. 
     <remarks>
     If <paramref name="p"/> evaluates to false, then the new tactic behaves like the <c>skip</c> tactic. 
  *)
  (* CMW: when is a keyword *)
  let when_ ( ctx : context ) ( p : probe ) ( t : tactic ) =
    (new tactic ctx)#cnstr_obj (Z3native.tactic_when (context_gno ctx) p#gno t#gno)

  (**
     Create a tactic that applies <paramref name="t1"/> to a given goal if the probe 
     <paramref name="p"/> evaluates to true and <paramref name="t2"/> otherwise.
  *)
  let cond ( ctx : context ) ( p : probe ) ( t1 : tactic ) ( t2 : tactic ) =
    (new tactic ctx)#cnstr_obj (Z3native.tactic_cond (context_gno ctx) p#gno t1#gno t2#gno)

  (**
     Create a tactic that keeps applying <paramref name="t"/> until the goal is not 
     modified anymore or the maximum number of iterations <paramref name="max"/> is reached.
  *)
  let repeat ( ctx : context ) ( t : tactic ) ( max : int ) =
    (new tactic ctx)#cnstr_obj (Z3native.tactic_repeat (context_gno ctx) t#gno max)

  (**
     Create a tactic that just returns the given goal.
  *)
  let skip ( ctx : context ) =
    (new tactic ctx)#cnstr_obj (Z3native.tactic_skip (context_gno ctx))

  (**
     Create a tactic always fails.
  *)
  let fail ( ctx : context ) =
    (new tactic ctx)#cnstr_obj (Z3native.tactic_fail (context_gno ctx))

  (**
     Create a tactic that fails if the probe <paramref name="p"/> evaluates to false.
  *)
  let fail_if ( ctx : context ) ( p : probe ) =
    (new tactic ctx)#cnstr_obj (Z3native.tactic_fail_if (context_gno ctx) p#gno)

  (**
     Create a tactic that fails if the goal is not triviall satisfiable (i.e., empty)
     or trivially unsatisfiable (i.e., contains `false').
  *)
  let fail_if_not_decided ( ctx : context ) =
    (new tactic ctx)#cnstr_obj (Z3native.tactic_fail_if_not_decided (context_gno ctx))

  (**
     Create a tactic that applies <paramref name="t"/> using the given set of parameters <paramref name="p"/>.
  *)
  let using_params ( ctx : context ) ( t : tactic ) ( p : params ) =
    (new tactic ctx)#cnstr_obj (Z3native.tactic_using_params (context_gno ctx) t#gno p#gno)

  (**
     Create a tactic that applies <paramref name="t"/> using the given set of parameters <paramref name="p"/>.
     <remarks>Alias for <c>UsingParams</c>*)
  (* CMW: with is a keyword *)
  let with_ ( ctx : context ) ( t : tactic ) ( p : params ) =
    using_params ctx t p

  (**
     Create a tactic that applies the given tactics in parallel.
  *)
  let par_or ( ctx : context ) ( t : tactic array ) =
    (new tactic ctx)#cnstr_obj (Z3native.tactic_par_or (context_gno ctx) (Array.length t) (tacticaton t))

  (**
     Create a tactic that applies <paramref name="t1"/> to a given goal and then <paramref name="t2"/>
     to every subgoal produced by <paramref name="t1"/>. The subgoals are processed in parallel.
  *)
  let par_and_then ( ctx : context ) ( t1 : tactic ) ( t2 : tactic ) =
    (new tactic ctx)#cnstr_obj (Z3native.tactic_par_and_then (context_gno ctx) t1#gno t2#gno)

  (**
     Interrupt the execution of a Z3 procedure.        
     <remarks>This procedure can be used to interrupt: solvers, simplifiers and tactics.
  *)
  let interrupt ( ctx : context ) =
    Z3native.interrupt (context_gno ctx)
end

(** Probes 

    Probes are used to inspect a goal (aka problem) and collect information that may be used to decide
    which solver and/or preprocessing step will be used.
    The complete list of probes may be obtained using the procedures <c>Context.NumProbes</c>
    and <c>Context.ProbeNames</c>.
    It may also be obtained using the command <c>(help-tactics)</c> in the SMT 2.0 front-end.
*)
module Probe =
struct
  (**
     Execute the probe over the goal. 
     <returns>A probe always produce a double value.
     "Boolean" probes return 0.0 for false, and a value different from 0.0 for true.</returns>
  *)
  let apply ( x : probe ) (g : goal) =
    Z3native.probe_apply x#gnc x#gno g#gno

  (**
     The number of supported Probes.
  *)
  let get_num_probes ( ctx : context ) =
    Z3native.get_num_probes (context_gno ctx)

  (**
     The names of all supported Probes.
  *)
  let get_probe_names ( ctx : context ) = 
    let n = (get_num_probes ctx) in
    let f i = (Z3native.get_probe_name (context_gno ctx) i) in
    Array.init n f

  (**
     Returns a string containing a description of the probe with the given name.
  *)
  let get_probe_description ( ctx : context ) ( name : string ) =
    Z3native.probe_get_descr (context_gno ctx) name

  (**
     Creates a new Probe.
  *) 
  let mk_probe ( ctx : context ) ( name : string ) =
    (new probe ctx)#cnstr_obj (Z3native.mk_probe (context_gno ctx) name)

  (**
     Create a probe that always evaluates to <paramref name="val"/>.
  *)
  let const ( ctx : context ) ( v : float ) = 
    (new probe ctx)#cnstr_obj (Z3native.probe_const (context_gno ctx) v)

  (**
     Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
     is less than the value returned by <paramref name="p2"/>
  *)
  let lt ( ctx : context ) ( p1 : probe ) ( p2 : probe ) =
    (new probe ctx)#cnstr_obj (Z3native.probe_lt (context_gno ctx) p1#gno p2#gno)

  (**
     Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
     is greater than the value returned by <paramref name="p2"/>
  *)
  let gt ( ctx : context ) ( p1 : probe ) ( p2 : probe ) =
    (new probe ctx)#cnstr_obj (Z3native.probe_gt (context_gno ctx) p1#gno p2#gno)

  (**
     Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
     is less than or equal the value returned by <paramref name="p2"/>
  *)
  let le ( ctx : context ) ( p1 : probe ) ( p2 : probe ) = 
    (new probe ctx)#cnstr_obj (Z3native.probe_le (context_gno ctx) p1#gno p2#gno)

  (**
     Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
     is greater than or equal the value returned by <paramref name="p2"/>
  *)
  let ge ( ctx : context ) ( p1 : probe ) ( p2 : probe ) =
    (new probe ctx)#cnstr_obj (Z3native.probe_ge (context_gno ctx) p1#gno p2#gno)

  (**
     Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
     is equal to the value returned by <paramref name="p2"/>
  *)
  let eq ( ctx : context ) ( p1 : probe ) ( p2 : probe ) =
    (new probe ctx)#cnstr_obj (Z3native.probe_eq (context_gno ctx) p1#gno p2#gno)

  (**
     Create a probe that evaluates to "true" when the value <paramref name="p1"/>
     and <paramref name="p2"/> evaluate to "true".
  *)
  (* CMW: and is a keyword *)
  let and_ ( ctx : context ) ( p1 : probe ) ( p2 : probe ) =
    (new probe ctx)#cnstr_obj (Z3native.probe_and (context_gno ctx) p1#gno p2#gno)

  (**
     Create a probe that evaluates to "true" when the value <paramref name="p1"/>
     or <paramref name="p2"/> evaluate to "true".
  *)
  (* CMW: or is a keyword *)
  let or_ ( ctx : context ) ( p1 : probe ) ( p2 : probe ) =
    (new probe ctx)#cnstr_obj (Z3native.probe_or (context_gno ctx) p1#gno p2#gno)

  (**
     Create a probe that evaluates to "true" when the value <paramref name="p"/>
     does not evaluate to "true".
  *)
  (* CMW: is not a keyword? *)
  let not_ ( ctx : context ) ( p : probe ) =
    (new probe ctx)#cnstr_obj (Z3native.probe_not (context_gno ctx) p#gno)
end


(** Solvers *)
module Solver =
struct
  type solver = z3_native_object
      
(**/**)
  let solver_cnstr ( ctx : context ) ( no : Z3native.ptr ) = 
    let res : solver = { m_ctx = ctx ;
			 m_n_obj = null ;
			 inc_ref = Z3native.solver_inc_ref ;
			 dec_ref = Z3native.solver_dec_ref } in
    (z3obj_sno res ctx no) ;
    (z3obj_cnstr res) ;
    res
(**/**)

  type status = UNSATISFIABLE | UNKNOWN | SATISFIABLE

  let string_of_status ( s : status) = match s with
    | UNSATISFIABLE -> "unsatisfiable"
    | SATISFIABLE -> "satisfiable" 
    | _ -> "unknown"

  (** Objects that track statistical information about solvers. *)
  module Statistics =
  struct
    type statistics = z3_native_object
	
    (**/**)
    let statistics_cnstr ( ctx : context ) ( no : Z3native.ptr ) = 
      let res : statistics = { m_ctx = ctx ;
			       m_n_obj = null ;
			       inc_ref = Z3native.stats_inc_ref ;
			       dec_ref = Z3native.stats_dec_ref } in
      (z3obj_sno res ctx no) ;
      (z3obj_cnstr res) ;
      res
    (**/**)

    (**
       Statistical data is organized into pairs of [Key, Entry], where every
       Entry is either a <c>DoubleEntry</c> or a <c>UIntEntry</c>
    *)
    module Entry =
    struct
      (** The key of the entry. *)
      let get_key (x : statistics_entry) = x#key
	
      (** The int-value of the entry. *)
      let get_int (x : statistics_entry) = x#int
	
      (** The float-value of the entry. *)
      let get_float (x : statistics_entry) = x#float
	
      (** True if the entry is uint-valued. *)
      let is_int (x : statistics_entry) = x#is_int
	
      (** True if the entry is double-valued. *)
      let is_float (x : statistics_entry) = x#is_float
	
      (** The string representation of the the entry's value. *)
      let to_string_value (x : statistics_entry) = 
	if (is_int x) then
	  string_of_int (get_int x)
	else if (is_float x) then 
	  string_of_float (get_float x)
	else
          raise (Z3native.Exception "Unknown statistical entry type")
	    
      (** The string representation of the entry (key and value) *)
      let to_string ( x : statistics_entry ) = (get_key x) ^ ": " ^ (to_string_value x)
    end

    (** A string representation of the statistical data. *)    
    let to_string ( x : statistics ) = Z3native.stats_to_string (z3obj_gnc x) (z3obj_gno x)
      
    (** The number of statistical data. *)
    let get_size ( x : statistics ) = Z3native.stats_size (z3obj_gnc x) (z3obj_gno x)
      
    (** The data entries. *)
    let get_entries ( x : statistics ) =
      let n = (get_size x ) in
      let f i = (
	let k = Z3native.stats_get_key (z3obj_gnc x) (z3obj_gno x) i in
	if (Z3native.stats_is_uint (z3obj_gnc x) (z3obj_gno x) i) then
	  ((new statistics_entry)#cnstr_si k (Z3native.stats_get_uint_value (z3obj_gnc x) (z3obj_gno x) i))
	else 
	  ((new statistics_entry)#cnstr_sd k (Z3native.stats_get_double_value (z3obj_gnc x) (z3obj_gno x) i))
      ) in
      Array.init n f

    (**
       The statistical counters.
    *)
    let get_keys ( x : statistics ) =
      let n = (get_size x) in
      let f i = (Z3native.stats_get_key (z3obj_gnc x) (z3obj_gno x) i) in
      Array.init n f
	
    (**
       The value of a particular statistical counter.
    *)        
    let get ( x : statistics ) ( key : string ) =
      let f p c = (if (Entry.get_key c) = key then (Some c) else p) in
      Array.fold_left f None (get_entries x)
  end

  (**
     A string that describes all available solver parameters.
  *)
  let get_help ( x : solver ) = Z3native.solver_get_help (z3obj_gnc x) (z3obj_gno x)

  (**
     Sets the solver parameters.
  *)
  let set_parameters ( x : solver ) ( value : params )=
    Z3native.solver_set_params (z3obj_gnc x) (z3obj_gno x) value#gno

  (**
     Retrieves parameter descriptions for solver.
  *)
  let get_param_descrs ( x : solver ) =
    (new param_descrs (z3obj_gc x))#cnstr_obj (Z3native.solver_get_param_descrs (z3obj_gnc x) (z3obj_gno x))

  (**
     The current number of backtracking points (scopes).
     <seealso cref="Pop"/>
     <seealso cref="Push"/>
  *)
  let get_num_scopes ( x : solver ) = Z3native.solver_get_num_scopes (z3obj_gnc x) (z3obj_gno x)

  (**
     Creates a backtracking point.
     <seealso cref="Pop"/>
  *)
  let push ( x : solver ) = Z3native.solver_push (z3obj_gnc x) (z3obj_gno x)

  (**
     Backtracks <paramref name="n"/> backtracking points.
     <remarks>Note that an exception is thrown if <paramref name="n"/> is not smaller than <c>NumScopes</c>
     <seealso cref="Push"/>
  *)
  let pop ( x : solver ) ( n : int ) = Z3native.solver_pop (z3obj_gnc x) (z3obj_gno x) n

  (**
     Resets the Solver.
     <remarks>This removes all assertions from the solver.
  *)
  let reset ( x : solver ) = Z3native.solver_reset (z3obj_gnc x) (z3obj_gno x)

  (**
     Assert a constraint (or multiple) into the solver.
  *)        
  let assert_ ( x : solver ) ( constraints : bool_expr array ) =
    let f e = (Z3native.solver_assert (z3obj_gnc x) (z3obj_gno x) e#gno) in
    ignore (Array.map f constraints) ;
    ()

  (**
     The number of assertions in the solver.
  *)
  let get_num_assertions ( x : solver ) =
    let a = (new ast_vector (z3obj_gc x))#cnstr_obj (Z3native.solver_get_assertions (z3obj_gnc x) (z3obj_gno x)) in
    (AST.ASTVector.get_size a)


  (**
     The set of asserted formulas.
  *)
  let get_assertions ( x : solver ) =
    let a = (new ast_vector (z3obj_gc x))#cnstr_obj (Z3native.solver_get_assertions (z3obj_gnc x) (z3obj_gno x)) in
    let n = (AST.ASTVector.get_size a) in
    let f i = ((new bool_expr (z3obj_gc x))#cnstr_obj (AST.ASTVector.get a i)#gno) in
    Array.init n f

  (**
     Checks whether the assertions in the solver are consistent or not.
     <remarks>
     <seealso cref="Model"/>
     <seealso cref="UnsatCore"/>
     <seealso cref="Proof"/>    
  *)
  let check ( x : solver ) ( assumptions : bool_expr array) =
    let r = 
      if ((Array.length assumptions) == 0) then
	lbool_of_int (Z3native.solver_check (z3obj_gnc x) (z3obj_gno x))
      else
	lbool_of_int (Z3native.solver_check_assumptions (z3obj_gnc x) (z3obj_gno x) (Array.length assumptions) (astaton assumptions))
    in
    match r with 
      | L_TRUE -> SATISFIABLE
      | L_FALSE -> UNSATISFIABLE
      | _ -> UNKNOWN
	
  (**
     The model of the last <c>Check</c>.
     <remarks>
     The result is <c>None</c> if <c>Check</c> was not invoked before,
     if its results was not <c>SATISFIABLE</c>, or if model production is not enabled.
  *)
  let get_model ( x : solver ) =
    let q = Z3native.solver_get_model (z3obj_gnc x) (z3obj_gno x) in
    if (Z3native.is_null q) then
      None
    else 
      Some (Model.model_cnstr (z3obj_gc x) q)
	
  (**
     The proof of the last <c>Check</c>.
     <remarks>    
     The result is <c>null</c> if <c>Check</c> was not invoked before,
     if its results was not <c>UNSATISFIABLE</c>, or if proof production is disabled.
  *)
  let get_proof ( x : solver ) =
    let q = Z3native.solver_get_proof (z3obj_gnc x) (z3obj_gno x) in
    if (Z3native.is_null q) then
      None
    else
      Some (create_expr (z3obj_gc x) q)
	
  (**
     The unsat core of the last <c>Check</c>.
     <remarks>
     The unsat core is a subset of <c>Assertions</c>
     The result is empty if <c>Check</c> was not invoked before,
     if its results was not <c>UNSATISFIABLE</c>, or if core production is disabled.
  *)
  let get_unsat_core ( x : solver ) =
    let cn = (new ast_vector (z3obj_gc x))#cnstr_obj (Z3native.solver_get_unsat_core (z3obj_gnc x) (z3obj_gno x)) in 
    let n = (AST.ASTVector.get_size cn) in
    let f i = (AST.ASTVector.get cn i) in
    Array.init n f

  (**
     A brief justification of why the last call to <c>Check</c> returned <c>UNKNOWN</c>.
  *)
  let get_reason_unknown ( x : solver ) =  Z3native.solver_get_reason_unknown (z3obj_gnc x) (z3obj_gno x)


  (**
     Solver statistics.
  *)
  let get_statistics ( x : solver ) =
    (Statistics.statistics_cnstr (z3obj_gc x) (Z3native.solver_get_statistics (z3obj_gnc x) (z3obj_gno x)))

  (**
     Creates a new (incremental) solver. 
     <remarks>
     This solver also uses a set of builtin tactics for handling the first 
     check-sat command, and check-sat commands that take more than a given 
     number of milliseconds to be solved. 
  *)    
  let mk_solver ( ctx : context ) ( logic : symbol option) =
    match logic with
      | None -> (solver_cnstr ctx (Z3native.mk_solver (context_gno ctx)))
      | Some (x) -> (solver_cnstr ctx (Z3native.mk_solver_for_logic (context_gno ctx) x#gno))

  (**
     Creates a new (incremental) solver.
     <seealso cref="MkSolver(Symbol)"/>
  *)        
  let mk_solver_s ( ctx : context ) ( logic : string ) =
    mk_solver ctx (Some ((Symbol.mk_string ctx logic) :> symbol))

  (**
     Creates a new (incremental) solver. 
  *)
  let mk_simple_solver ( ctx : context ) =
    (solver_cnstr ctx (Z3native.mk_simple_solver (context_gno ctx)))

  (**
     Creates a solver that is implemented using the given tactic.
     <remarks>
     The solver supports the commands <c>Push</c> and <c>Pop</c>, but it
     will always solve each check from scratch.
  *)
  let mk_solver_t ( ctx : context ) ( t : tactic ) = 
    (solver_cnstr ctx (Z3native.mk_solver_from_tactic (context_gno ctx) t#gno))

  (**
     A string representation of the solver.
  *)
  let to_string ( x : solver ) = Z3native.solver_to_string (z3obj_gnc x) (z3obj_gno x)
end


(** Fixedpoint solving *)
module Fixedpoints =
struct
  type fixedpoint = z3_native_object
      
(**/**)
  let fixedpoint_cnstr ( ctx : context ) = 
    let res : fixedpoint = { m_ctx = ctx ;
			     m_n_obj = null ;
			     inc_ref = Z3native.fixedpoint_inc_ref ;
			     dec_ref = Z3native.fixedpoint_dec_ref } in
    (z3obj_sno res ctx (Z3native.mk_fixedpoint (context_gno ctx))) ;
    (z3obj_cnstr res) ;
    res
(**/**)

  (**
     A string that describes all available fixedpoint solver parameters.
  *)
  let get_help ( x : fixedpoint ) =
    Z3native.fixedpoint_get_help (z3obj_gnc x) (z3obj_gno x)
      
  (**
     Sets the fixedpoint solver parameters.
  *)
  let set_params ( x : fixedpoint ) ( p : params )=
    Z3native.fixedpoint_set_params (z3obj_gnc x) (z3obj_gno x) p#gno
      
  (**
     Retrieves parameter descriptions for Fixedpoint solver.
  *)
  let get_param_descrs ( x : fixedpoint ) =
    (new param_descrs (z3obj_gc x))#cnstr_obj (Z3native.fixedpoint_get_param_descrs (z3obj_gnc x) (z3obj_gno x))
      
  (**
     Assert a constraints into the fixedpoint solver.
  *)        
  let assert_ ( x : fixedpoint ) ( constraints : bool_expr array ) =
    let f e = (Z3native.fixedpoint_assert (z3obj_gnc x) (z3obj_gno x) e#gno) in
    ignore (Array.map f constraints) ;
    ()

  (**
     Register predicate as recursive relation.
  *)       
  let register_relation ( x : fixedpoint ) ( f : func_decl ) =
    Z3native.fixedpoint_register_relation (z3obj_gnc x) (z3obj_gno x) f#gno
      
  (**
     Add rule into the fixedpoint solver.
  *)        
  let add_rule ( x : fixedpoint ) ( rule : bool_expr ) ( name : symbol option ) =
    match name with 
      | None -> Z3native.fixedpoint_add_rule (z3obj_gnc x) (z3obj_gno x) rule#gno null
      | Some(y) -> Z3native.fixedpoint_add_rule (z3obj_gnc x) (z3obj_gno x) rule#gno y#gno

  (**
     Add table fact to the fixedpoint solver.
  *)        
  let add_fact ( x : fixedpoint ) ( pred : func_decl ) ( args : int array ) =
    Z3native.fixedpoint_add_fact (z3obj_gnc x) (z3obj_gno x) pred#gno (Array.length args) args

  (**
     Query the fixedpoint solver.
     A query is a conjunction of constraints. The constraints may include the recursively defined relations.
     The query is satisfiable if there is an instance of the query variables and a derivation for it.
     The query is unsatisfiable if there are no derivations satisfying the query variables. 
  *)        
  let query ( x : fixedpoint ) ( query : bool_expr ) =
    match (lbool_of_int (Z3native.fixedpoint_query (z3obj_gnc x) (z3obj_gno x) query#gno)) with
      | L_TRUE -> Solver.SATISFIABLE
      | L_FALSE -> Solver.UNSATISFIABLE
      | _ -> Solver.UNKNOWN

  (**
     Query the fixedpoint solver.
     A query is an array of relations.
     The query is satisfiable if there is an instance of some relation that is non-empty.
     The query is unsatisfiable if there are no derivations satisfying any of the relations.
  *)        
  let query_r ( x : fixedpoint ) ( relations : func_decl array ) =
    match (lbool_of_int (Z3native.fixedpoint_query_relations (z3obj_gnc x) (z3obj_gno x) (Array.length relations) (func_declaton relations))) with
      | L_TRUE -> Solver.SATISFIABLE
      | L_FALSE -> Solver.UNSATISFIABLE
      | _ -> Solver.UNKNOWN
	
  (**
     Creates a backtracking point.
     <seealso cref="Pop"/>
  *)
  let push ( x : fixedpoint ) =
    Z3native.fixedpoint_push (z3obj_gnc x) (z3obj_gno x)
      
  (**
     Backtrack one backtracking point.

     <remarks>Note that an exception is thrown if Pop is called without a corresponding <c>Push</c></remarks>
     <seealso cref="Push"/>
  *)
  let pop ( x : fixedpoint ) =
    Z3native.fixedpoint_pop (z3obj_gnc x) (z3obj_gno x)

  (**
     Update named rule into in the fixedpoint solver.
  *)        
  let update_rule ( x : fixedpoint ) ( rule : bool_expr ) ( name : symbol ) =
    Z3native.fixedpoint_update_rule (z3obj_gnc x) (z3obj_gno x) rule#gno name#gno

  (**
     Retrieve satisfying instance or instances of solver, 
     or definitions for the recursive predicates that show unsatisfiability.
  *)                
  let get_answer ( x : fixedpoint ) =
    let q = (Z3native.fixedpoint_get_answer (z3obj_gnc x) (z3obj_gno x)) in
    if (Z3native.is_null q) then
      None
    else
      Some (create_expr (z3obj_gc x) q)

  (**
     Retrieve explanation why fixedpoint engine returned status Unknown.
  *)                
  let get_reason_unknown ( x : fixedpoint ) =
    Z3native.fixedpoint_get_reason_unknown (z3obj_gnc x) (z3obj_gno x)

  (**
     Retrieve the number of levels explored for a given predicate.
  *)                
  let get_num_levels ( x : fixedpoint ) ( predicate : func_decl ) =
    Z3native.fixedpoint_get_num_levels (z3obj_gnc x) (z3obj_gno x) predicate#gno

  (**
     Retrieve the cover of a predicate.
  *)                
  let get_cover_delta ( x : fixedpoint ) ( level : int ) ( predicate : func_decl ) =
    let q = (Z3native.fixedpoint_get_cover_delta (z3obj_gnc x) (z3obj_gno x) level predicate#gno) in
    if (Z3native.is_null q) then
      None
    else
      Some (create_expr (z3obj_gc x) q)
	
  (**
     Add <tt>property</tt> about the <tt>predicate</tt>.
     The property is added at <tt>level</tt>.
  *)                
  let add_cover ( x : fixedpoint ) ( level : int ) ( predicate : func_decl ) ( property : expr ) =
    Z3native.fixedpoint_add_cover (z3obj_gnc x) (z3obj_gno x) level predicate#gno property#gno
      
  (**
     Retrieve internal string representation of fixedpoint object.
  *)                
  let to_string ( x : fixedpoint ) = Z3native.fixedpoint_to_string (z3obj_gnc x) (z3obj_gno x) 0 [||]
      
  (**
     Instrument the Datalog engine on which table representation to use for recursive predicate.
  *)                
  let set_predicate_representation ( x : fixedpoint ) ( f : func_decl ) ( kinds : symbol array ) =
    Z3native.fixedpoint_set_predicate_representation (z3obj_gnc x) (z3obj_gno x) f#gno (Array.length kinds) (symbolaton kinds)

  (**
     Convert benchmark given as set of axioms, rules and queries to a string.
  *)                
  let to_string_q ( x : fixedpoint ) ( queries : bool_expr array ) =
    Z3native.fixedpoint_to_string (z3obj_gnc x) (z3obj_gno x) (Array.length queries) (astaton queries)

  (**
     Retrieve set of rules added to fixedpoint context.
  *)                
  let get_rules ( x : fixedpoint ) = 
    let v = ((new ast_vector (z3obj_gc x))#cnstr_obj (Z3native.fixedpoint_get_rules (z3obj_gnc x) (z3obj_gno x))) in
    let n = (AST.ASTVector.get_size v) in
    let f i = (new bool_expr (z3obj_gc x))#cnstr_obj (AST.ASTVector.get v i)#gno in
    Array.init n f

  (**
     Retrieve set of assertions added to fixedpoint context.
  *)                
  let get_assertions ( x : fixedpoint ) = 
    let v = ((new ast_vector (z3obj_gc x))#cnstr_obj (Z3native.fixedpoint_get_assertions (z3obj_gnc x) (z3obj_gno x))) in
    let n = (AST.ASTVector.get_size v) in
    let f i = (new bool_expr (z3obj_gc x))#cnstr_obj (AST.ASTVector.get v i)#gno in
    Array.init n f

  (**
     Create a Fixedpoint context.
  *)
  let mk_fixedpoint ( ctx : context ) = fixedpoint_cnstr ctx
end

(** Global and context options
    
    Note: This module contains functions that set parameters/options for context 
    objects as well as functions that set options that are used globally, across 
    contexts.*)
module Options =
struct

(**
   Update a mutable configuration parameter.
   <remarks>
   The list of all configuration parameters can be obtained using the Z3 executable:
   <c>z3.exe -ini?</c>
   Only a few configuration parameters are mutable once the context is created.
   An exception is thrown when trying to modify an immutable parameter.
   <seealso cref="GetParamValue"/>
*)
  let update_param_value ( ctx : context ) ( id : string) ( value : string )=
    Z3native.update_param_value (context_gno ctx) id value

(**
   Get a configuration parameter.
   <remarks>
   Returns None if the parameter value does not exist.
   <seealso cref="UpdateParamValue"/>
*)
  let get_param_value ( ctx : context ) ( id : string ) =
    let (r, v) = (Z3native.get_param_value (context_gno ctx) id) in
    if not r then
      None
    else 
      Some v

  (**
     Selects the format used for pretty-printing expressions.
     <remarks>
     The default mode for pretty printing expressions is to produce
     SMT-LIB style output where common subexpressions are printed 
     at each occurrence. The mode is called PRINT_SMTLIB_FULL.
     To print shared common subexpressions only once, 
     use the PRINT_LOW_LEVEL mode.
     To print in way that conforms to SMT-LIB standards and uses let
     expressions to share common sub-expressions use PRINT_SMTLIB_COMPLIANT.
     <seealso cref="AST.ToString ( ctx : context ) ="/>
     <seealso cref="Pattern.ToString ( ctx : context ) ="/>
     <seealso cref="FuncDecl.ToString ( ctx : context ) ="/>
     <seealso cref="Sort.ToString ( ctx : context ) ="/>
  *)
  let set_print_mode ( ctx : context ) ( value : ast_print_mode ) =
    Z3native.set_ast_print_mode (context_gno ctx) (int_of_ast_print_mode value)

(**
   Enable/disable printing of warning messages to the console.

   <remarks>Note that this function is static and effects the behaviour of 
   all contexts globally.
*)
  let toggle_warning_messages ( enabled: bool ) =
    Z3native.toggle_warning_messages enabled
end

(** Functions for handling SMT and SMT2 expressions and files *)
module SMT =
struct
  (**
     Convert a benchmark into an SMT-LIB formatted string.

     @param name Name of the benchmark. The argument is optional.
     @param logic The benchmark logic. 
     @param status The status string (sat, unsat, or unknown)
     @param attributes Other attributes, such as source, difficulty or category.
     @param assumptions Auxiliary assumptions.
     @param formula Formula to be checked for consistency in conjunction with assumptions.
     @return A string representation of the benchmark.
  *)
  let benchmark_to_smtstring ( ctx : context ) ( name : string ) ( logic : string ) ( status : string ) ( attributes : string ) ( assumptions : bool_expr array ) ( formula : bool_expr ) =
    Z3native.benchmark_to_smtlib_string (context_gno ctx) name logic status attributes
      (Array.length assumptions) (astaton assumptions)
      formula#gno

  (**
     Parse the given string using the SMT-LIB parser. 
     <remarks>
     The symbol table of the parser can be initialized using the given sorts and declarations. 
     The symbols in the arrays <paramref name="sortNames"/> and <paramref name="declNames"/> 
     don't need to match the names of the sorts and declarations in the arrays <paramref name="sorts"/> 
     and <paramref name="decls"/>. This is a useful feature since we can use arbitrary names to 
     reference sorts and declarations.
  *)
  let parse_smtlib_string ( ctx : context ) ( str : string ) ( sort_names : symbol array ) ( sorts : sort array ) ( decl_names : symbol array ) ( decls : func_decl array ) =
    let csn = (Array.length sort_names) in
    let cs = (Array.length sorts) in
    let cdn = (Array.length decl_names) in
    let cd = (Array.length decls) in
    if (csn != cs || cdn != cd) then 
      raise (Z3native.Exception "Argument size mismatch")
    else
      Z3native.parse_smtlib_string (context_gno ctx) str 
	cs 
	(symbolaton sort_names)
	(astaton sorts)
	cd 
	(symbolaton decl_names)
	(func_declaton decls)
	
  (**
     Parse the given file using the SMT-LIB parser. 
     <seealso cref="ParseSMTLIBString"/>
  *)
  let parse_smtlib_file ( ctx : context ) ( file_name : string ) ( sort_names : symbol array ) ( sorts : sort array ) ( decl_names : symbol array ) ( decls : func_decl array ) =
    let csn = (Array.length sort_names) in
    let cs = (Array.length sorts) in
    let cdn = (Array.length decl_names) in
    let cd = (Array.length decls) in
    if (csn != cs || cdn != cd) then 
      raise (Z3native.Exception "Argument size mismatch")
    else
      Z3native.parse_smtlib_file (context_gno ctx) file_name
	cs 
	(symbolaton sort_names)
	(astaton sorts)
	cd 
	(symbolaton decl_names)
	(func_declaton decls)

  (**
     The number of SMTLIB formulas parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
  *)
  let get_num_smtlib_formulas ( ctx : context ) = Z3native.get_smtlib_num_formulas (context_gno ctx)

  (**
     The formulas parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
  *)
  let get_smtlib_formulas ( ctx : context ) =
    let n = (get_num_smtlib_formulas ctx ) in
    let f i = ((create_expr ctx (Z3native.get_smtlib_formula (context_gno ctx) i)) :> bool_expr) in
    Array.init n f 


  (**
     The number of SMTLIB assumptions parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
  *)
  let get_num_smtlib_assumptions ( ctx : context ) = Z3native.get_smtlib_num_assumptions (context_gno ctx)

  (**
     The assumptions parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
  *)
  let get_smtlib_assumptions ( ctx : context ) =
    let n = (get_num_smtlib_assumptions ctx ) in
    let f i =  ((create_expr ctx (Z3native.get_smtlib_assumption (context_gno ctx) i)) :> bool_expr ) in
    Array.init n f

  (**
     The number of SMTLIB declarations parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
  *)
  let get_num_smtlib_decls ( ctx : context ) = Z3native.get_smtlib_num_decls (context_gno ctx)

  (**
     The declarations parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
  *)
  let get_smtlib_decls ( ctx : context ) = 
    let n = (get_num_smtlib_decls ctx) in
    let f i = (new func_decl ctx)#cnstr_obj (Z3native.get_smtlib_decl (context_gno ctx) i) in
    Array.init n f

  (**
     The number of SMTLIB sorts parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
  *)
  let get_num_smtlib_sorts ( ctx : context )  = Z3native.get_smtlib_num_sorts (context_gno ctx)

  (**
     The declarations parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
  *)
  let get_smtlib_sorts ( ctx : context ) = 
    let n = (get_num_smtlib_sorts ctx) in
    let f i = (create_sort ctx (Z3native.get_smtlib_sort (context_gno ctx) i)) in
    Array.init n f

  (**
     Parse the given string using the SMT-LIB2 parser. 

     <seealso cref="ParseSMTLIBString"/>
     @return A conjunction of assertions in the scope (up to push/pop) at the end of the string.
  *)
  let parse_smtlib2_string ( ctx : context ) ( str : string ) ( sort_names : symbol array ) ( sorts : sort array ) ( decl_names : symbol array ) ( decls : func_decl array ) =
    let csn = (Array.length sort_names) in
    let cs = (Array.length sorts) in
    let cdn = (Array.length decl_names) in
    let cd = (Array.length decls) in
    if (csn != cs || cdn != cd) then 
      raise (Z3native.Exception "Argument size mismatch")
    else
      Z3native.parse_smtlib2_string (context_gno ctx) str 
	cs 
	(symbolaton sort_names)
	(astaton sorts)
	cd 
	(symbolaton decl_names)
	(func_declaton decls)

  (**
     Parse the given file using the SMT-LIB2 parser. 
     <seealso cref="ParseSMTLIB2String"/>
  *)
  let parse_smtlib2_file ( ctx : context ) ( file_name : string ) ( sort_names : symbol array ) ( sorts : sort array ) ( decl_names : symbol array ) ( decls : func_decl array ) =
    let csn = (Array.length sort_names) in
    let cs = (Array.length sorts) in
    let cdn = (Array.length decl_names) in
    let cd = (Array.length decls) in
    if (csn != cs || cdn != cd) then 
      raise (Z3native.Exception "Argument size mismatch")
    else
      Z3native.parse_smtlib2_string (context_gno ctx) file_name
	cs 
	(symbolaton sort_names)
	(astaton sorts)
	cd 
	(symbolaton decl_names)
	(func_declaton decls)
end

(*

(**
   A delegate which is executed when an error is raised.
   <remarks>
   Note that it is possible for memory leaks to occur if error handlers
   throw exceptions. 
*)
   public delegate void ErrorHandler(Context ctx, error_code errorCode, string errorString);

   internal Z3native.error_handler m_n_err_handler = null;

   internal void NativeErrorHandler(IntPtr ctx, error_code errorCode)

   Do-nothing error handler. The wrappers in Z3.Native will throw exceptions upon errors.            

*)
