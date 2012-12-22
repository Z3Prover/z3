(**
   The Z3 ML/Ocaml Interface.

   Copyright (C) 2012 Microsoft Corporation
   @author CM Wintersteiger (cwinter) 2012-12-17
*)

open Z3enums

(**/**)

(* Object definitions. These are internal and should be interacted 
   with only via the corresponding functions from modules. *)

class virtual idisposable = 
object
  method virtual dispose : unit
end

(** Context objects *)
class context settings  =
object (self)
  inherit idisposable

  val mutable m_n_ctx : Z3native.z3_context = 
    let cfg = Z3native.mk_config in
    let f e = (Z3native.set_param_value cfg (fst e) (snd e)) in
    (List.iter f settings) ;
    let v = Z3native.mk_context_rc cfg in
    Z3native.del_config(cfg) ;
    v

  val mutable m_refCount : int = 0
    
  initializer 
    Gc.finalise (fun self -> self#dispose) self
      
  method dispose : unit = 
    if m_refCount == 0 then (
      Printf.printf "Disposing context %d \n" (Oo.id self) ;
      (Z3native.del_context m_n_ctx)
    ) else (
    (* re-queue for finalization? *)
    )

  method sub_one_ctx_obj = m_refCount <- m_refCount - 1
  method add_one_ctx_obj = m_refCount <- m_refCount + 1
  method gno = m_n_ctx
end


(** Z3 objects *)
class virtual z3object ctx_init obj_init =
object (self)
  inherit idisposable
  val mutable m_ctx : context = ctx_init
  val mutable m_n_obj : Z3native.ptr option = obj_init
    
  initializer 
    (match m_n_obj with 
      | Some (x) -> self#incref m_ctx#gno x;
	m_ctx#add_one_ctx_obj
      | None -> ()
    );
    Gc.finalise (fun self -> self#dispose) self

  method virtual incref : Z3native.ptr -> Z3native.ptr -> unit
  method virtual decref : Z3native.ptr -> Z3native.ptr -> unit
    
  (* 
     Disposes of the underlying native Z3 object. 
  *)
  method dispose =
    Printf.printf "Disposing z3object %d \n" (Oo.id self) ;
    (match m_n_obj with
      | Some (x) -> self#decref m_ctx#gno x; m_n_obj <- None; m_ctx#sub_one_ctx_obj
      | None -> ()
    ); 

  method gno = match m_n_obj with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Z3 object lost")

  method sno nc o =
    self#incref nc o ;
    (match m_n_obj with
      | Some(x) -> self#decref nc x
      | None -> ()
    );
    m_n_obj <- Some o

  method gc = m_ctx
  method gnc = m_ctx#gno
end


(** Parameter set objects *)
class params ctx obj = 
object (self)
  inherit z3object ctx obj as super
  method incref ctx o = Z3native.params_inc_ref ctx o
  method decref ctx o = Z3native.params_dec_ref ctx o
end


(** Symbol objects *)
class symbol ctx = 
object (self)
  inherit z3object ctx None as super 
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
  method incref ctx o = ()
  method decref ctx o = ()
end

let symbolaton (a : symbol array) =
  let f (e : symbol) = e#gno in 
  Array.map f a

(** Int symbol objects *)
class int_symbol ctx = 
object(self)
  inherit symbol ctx as super 
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
  method cnstr_int i = (self#sno ctx#gno (Z3native.mk_int_symbol ctx#gno i)) ; self 
end

(** String symbol objects *)
class string_symbol ctx = 
object(self)
  inherit symbol ctx as super 
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
  method cnstr_string name = (self#sno ctx#gno (Z3native.mk_string_symbol ctx#gno name)) ; self 
end

let create_symbol ctx no =
  match (int2symbol_kind (Z3native.get_symbol_kind ctx#gno no)) with
    | INT_SYMBOL -> (((new int_symbol ctx)#cnstr_obj no) :> symbol)
    | STRING_SYMBOL -> (((new string_symbol ctx)#cnstr_obj no) :> symbol)
      
(** AST objects *)
class ast ctx =
object (self)
  inherit z3object ctx None as super (* CMW: derive from icomparable? *)  
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self

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
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Arithmetic sort objects, i.e., Int or Real. *)
class arith_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Array sorts objects *)
class array_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
  method cnstr_dr (domain : sort) (range : sort) = (self#sno ctx#gno (Z3native.mk_array_sort ctx#gno domain#gno range#gno)) ; self
end

(** Bit-vector sort objects *)
class bitvec_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Boolean sort objects *)
class bool_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Datatype sort objects *)
class datatype_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
  method cnstr_sc (name : symbol) constructors = (self#sno ctx#gno (fst (Z3native.mk_datatype ctx#gno name#gno (Array.length constructors) (astaton constructors)))) ; self
end

(** Enum sort objects *)
class enum_sort ctx =
object (self)
  inherit sort ctx as super
  val mutable _constdecls = None
  val mutable _testerdecls = None
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
  method cnstr_ss (name : symbol) (enum_names : symbol array) = 
    let (r, a, b) = (Z3native.mk_enumeration_sort ctx#gno name#gno (Array.length enum_names) (symbolaton enum_names)) in
    _constdecls <- Some a ;
    _testerdecls <- Some b ;
    (self#sno ctx#gno r) ; 
    self

  method const_decls = match _constdecls with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing const decls")

  method tester_decls = match _testerdecls with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing tester decls")
end

(** Int sort objects *)
class int_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Real sort objects *)
class real_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Uninterpreted sort objects *)
class uninterpreted_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
  method cnstr_s (s : symbol) = (self #sno ctx#gno (Z3native.mk_uninterpreted_sort ctx#gno s#gno)) ; self
end

(** Finite domain sort objects *)
class finite_domain_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
  method cnstr_si (s : symbol) ( sz : int )= (self #sno ctx#gno (Z3native.mk_finite_domain_sort ctx#gno s#gno sz)) ; self
end

(** Relation sort objects *)
class relation_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** List sort objects *)
class list_sort ctx =
object (self)
  inherit sort ctx as super    
  val mutable _nildecl = None
  val mutable _is_nildecl = None
  val mutable _consdecl = None
  val mutable _is_consdecl = None
  val mutable _headdecl = None
  val mutable _taildecl = None
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
  method cnstr_ss (name : symbol) (elem_sort : sort) =
    let (r, a, b, c, d, e, f) = (Z3native.mk_list_sort ctx#gno name#gno elem_sort#gno) in
    _nildecl <- Some a ;
    _is_nildecl <- Some b ;
    _consdecl <- Some c ;
    _is_consdecl <- Some d ;
    _headdecl <- Some e ;
    _taildecl <- Some f ;
    (self#sno ctx#gno r) ;
    self

  method nil_decl = match _nildecl with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing nil decl")

  method is_nil_decl = match _is_nildecl with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing is_nil decls")

  method cons_decl = match _consdecl with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing cons decls")

  method is_cons_decl = match _is_consdecl with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing is_cons decls")

  method head_decl = match _headdecl with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing head decls")

  method tail_decl = match _taildecl with
    | Some(x) -> x
    | None -> raise (Z3native.Exception "Missing tail decls")

end

(** Set sort objects *)
class set_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
  method cnstr_s (s : sort) = (self#sno ctx#gno s#gno) ; self
end

(** Tuple sort objects *)
class tuple_sort ctx =
object (self)
  inherit sort ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
  method cnstr_siss (name : symbol) (num_fields: int) (field_names : symbol array) (field_sorts : sort array) =
    let (x,_,_) = (Z3native.mk_tuple_sort ctx#gno name#gno num_fields (symbolaton field_names) (astaton field_sorts)) in
    (self#sno ctx#gno x) ;
    self
end

let create_sort ctx obj =
  match (int2sort_kind (Z3native.get_sort_kind ctx#gno obj)) with
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

(** Function declaration objects *)
class func_decl ctx =
object (self)
  inherit ast ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
  method cnstr_ndr (name : symbol) (domain : sort array) (range : sort)  = (self#sno ctx#gno (Z3native.mk_func_decl ctx#gno name#gno (Array.length domain) (astaton domain) range#gno)) ; self
  method cnstr_pdr (prefix : string) (domain : sort array) (range : sort) = (self#sno ctx#gno (Z3native.mk_fresh_func_decl ctx#gno prefix (Array.length domain) (astaton domain) range#gno)) ; self

  method incref nc o = super#incref nc o
  method decref nc o = super#decref nc o
end

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

(** Expression objects *)
class expr ctx =
object(self)
  inherit ast ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self    
end

let expraton (a : expr array) =
  let f (e : expr) = e#gno in 
  Array.map f a

(** Boolean expression objects *)
class bool_expr ctx =
object (self)
  inherit expr ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Arithmetic expression objects (int/real) *)
class arith_expr ctx =
object (self)
  inherit expr ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Int expression objects *)
class int_expr ctx =
object (self)
  inherit arith_expr ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Real expression objects *)
class real_expr ctx =
object (self)
  inherit arith_expr ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Bit-vector expression objects *)
class bitvec_expr ctx =
object (self)
  inherit expr ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Array expression objects *)
class array_expr ctx =
object (self)
  inherit expr ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Datatype expression objects *)
class datatype_expr ctx =
object (self)
  inherit expr ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Integer numeral expression objects *)
class int_num ctx =
object (self)
  inherit int_expr ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Rational numeral expression objects *)
class rat_num ctx =
object (self)
  inherit real_expr ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Bit-vector numeral expression objects *)
class bitvec_num ctx =
object (self)
  inherit bitvec_expr ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end

(** Algebraic numeral expression objects *)
class algebraic_num ctx =
object (self)
  inherit arith_expr ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end


(** Quantifier objects *)
class quantifier ctx =
object (self)
  inherit expr ctx as super
  method cnstr_obj obj = (self#sno ctx#gno obj) ; self
end



(**/**)

(** Interaction logging for Z3.
    Note that this is a global, static log and if multiple Context 
    objects are created, it logs the interaction with all of them. *)
module Log = 
struct
  (** Open an interaction log file. 
      @param filename the name of the file to open.
      @return True if opening the log file succeeds, false otherwise.
  *)
  (* CMW: "open" seems to be a reserved keyword? *)
  let open_ filename = ((int2lbool (Z3native.open_log filename)) == L_TRUE)

  (** Closes the interaction log. *)
  let close = Z3native.close_log

  (** Appends a user-provided string to the interaction log.
      @param s the string to append*)
  let append s = Z3native.append_log s
end

(** Version information. *)
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

(** Symbols are used to name several term and type constructors. *)
module Symbol =
struct	
  (** The kind of the symbol (int or string) *)
  let kind (o : symbol) = (int2symbol_kind (Z3native.get_symbol_kind o#gnc o#gno))

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
end


(**
   The Sort module implements type information for ASTs.
*)
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
      ((int2lbool (Z3native.is_eq_sort a#gnc a#gno b#gno)) == L_TRUE)
	
  (**
     Returns a unique identifier for the sort.
  *)
  let get_id (x : sort) = Z3native.get_sort_id x#gnc x#gno
    
  (**
     The kind of the sort.
  *)
  let get_sort_kind (x : sort) = (int2sort_kind (Z3native.get_sort_kind x#gnc x#gno))

  (**
     The name of the sort
  *)
  let get_name (x : sort) = (create_symbol x#gc (Z3native.get_sort_name x#gnc x#gno))    
    
  (**
     A string representation of the sort.
  *)
  let to_string (x : sort) = Z3native.sort_to_string x#gnc x#gno
end 

(** Array sorts *)
module ArraySort =
struct
  (** The domain of the array sort. *)
  let get_domain (x : array_sort) = create_sort x#gc (Z3native.get_array_sort_domain x#gnc x#gno)

  (** The range of the array sort. *)
  let get_range (x : array_sort) = create_sort x#gc (Z3native.get_array_sort_range x#gnc x#gno)
end

(** Bit-vector sorts *)
module BitVectorSort =
struct
  (** The size of the bit-vector sort. *)
  let get_size (x : bitvec_sort) = Z3native.get_bv_sort_size x#gnc x#gno
end

(** Finite domain sorts. *)
module FiniteDomainSort =
struct
  (** The size of the finite domain sort. *)
  let get_size (x : finite_domain_sort) = 
    let (r, v) = Z3native.get_finite_domain_sort_size x#gnc x#gno in
    if int2lbool(r) == L_TRUE then v
    else raise (Z3native.Exception "Conversion failed.")
end

(** Relation sorts. *)
module RelationSort =
struct
  (** The arity of the relation sort. *)
  let get_arity (x : relation_sort) = Z3native.get_relation_arity x#gnc x#gno

  (** The sorts of the columns of the relation sort. *)
  let get_column_sorts (x : relation_sort) = 
    let n = get_arity x in
    let f i = create_sort x#gc (Z3native.get_relation_column x#gnc x#gno i) in
    Array.init n f

end

(**/**)
let create_expr ctx obj =
  if int2ast_kind (Z3native.get_ast_kind ctx#gno obj) == QUANTIFIER_AST then
    (((new quantifier ctx)#cnstr_obj obj) :> expr)
  else
    let s = Z3native.get_sort ctx#gno obj in
    let sk = (int2sort_kind (Z3native.get_sort_kind ctx#gno s)) in    
    if (int2lbool (Z3native.is_algebraic_number ctx#gno obj) == L_TRUE) then
      (((new algebraic_num ctx)#cnstr_obj obj) :> expr)
    else
      if ((int2lbool (Z3native.is_numeral_ast ctx#gno obj)) == L_TRUE) &&
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
  let o = Z3native.mk_app ctx#gno f#gno (Array.length args) (astaton args) in
  create_expr ctx o

let create_ast ctx no =
  match (int2ast_kind (Z3native.get_ast_kind ctx#gno no)) with
    | FUNC_DECL_AST -> (((new func_decl ctx)#cnstr_obj no) :> ast)
    | QUANTIFIER_AST -> (((new quantifier ctx)#cnstr_obj no) :> ast)
    | SORT_AST -> ((create_sort ctx no) :> ast)
    | APP_AST
    | NUMERAL_AST
    | VAR_AST -> ((create_expr ctx no) :> ast)
    | UNKNOWN_AST -> raise (Z3native.Exception "Cannot create asts of type unknown")
(**/**)

(** Function declarations. *)
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
      ((int2lbool (Z3native.is_eq_func_decl a#gnc a#gno b#gno)) == L_TRUE)
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
  let get_decl_kind (x : func_decl) = (int2decl_kind (Z3native.get_decl_kind x#gnc x#gno))

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
      match (int2parameter_kind (Z3native.get_decl_parameter_kind x#gnc x#gno i)) with
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
     <param name="args"></param>
  *)	   
  let apply (x : func_decl) (args : expr array) = create_expr_fa x#gc x args

end

(** Datatype sorts *)
module DatatypeSort =
struct
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

(** Enumeration sorts. *)
module EnumSort =
struct
  (** The function declarations of the constants in the enumeration. *)
  let get_const_decls (x : enum_sort) = 
    let f e = ((new func_decl x#gc)#cnstr_obj e) in
    Array.map f x#const_decls

  (** The test predicates for the constants in the enumeration. *)
  let get_tester_decls (x : enum_sort) = 
    let f e = ((new func_decl x#gc)#cnstr_obj e) in
    Array.map f x#tester_decls
end

(** List sorts. *)
module ListSort =
struct
  (** The declaration of the nil function of this list sort. *)
  let get_nil_decl (x : list_sort) = (new func_decl x#gc)#cnstr_obj x#nil_decl

  (** The declaration of the isNil function of this list sort. *)
  let get_is_nil_decl (x : list_sort) = (new func_decl x#gc)#cnstr_obj x#is_nil_decl

  (** The declaration of the cons function of this list sort. *)
  let get_cons_decl (x : list_sort) = (new func_decl x#gc)#cnstr_obj x#cons_decl

  (** The declaration of the isCons function of this list sort. *)
  let get_is_cons_decl (x : list_sort) = (new func_decl x#gc)#cnstr_obj x#is_cons_decl

  (** The declaration of the head function of this list sort.*)
  let get_head_decl (x : list_sort)  = (new func_decl x#gc)#cnstr_obj x#head_decl

  (** The declaration of the tail function of this list sort. *)
  let get_tail_decl (x : list_sort) = (new func_decl x#gc)#cnstr_obj x#tail_decl

  (** The empty list. *)
  let nil (x : list_sort) = create_expr_fa x#gc (get_nil_decl x) [||]
end

module TupleSort =
struct
  (**  The constructor function of the tuple.*)
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

(** The abstract syntax tree (AST) module. *)
module AST =
struct
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
  let get_ast_kind ( x : ast) = (int2ast_kind (Z3native.get_ast_kind x#gnc x#gno))
    
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
     Indicates whether the AST is a BoundVariable
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
      ((int2lbool (Z3native.is_eq_ast a#gnc a#gno b#gno)) == L_TRUE)
	
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
      (create_ast to_ctx (Z3native.translate x#gnc x#gno to_ctx#gno))
end

(** 
    Parameter sets     

    A Params objects represents a configuration in the form of Symbol/value pairs.
*)
module Params =
struct
  (**
     Adds a parameter setting.
  *)
  let add_bool (p : params) (name : symbol) (value : bool) =
    Z3native.params_set_bool p#gnc p#gno name#gno (lbool2int (if value then L_TRUE else L_FALSE))
      
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
     A string representation of the parameter set.
  *)
  let to_string (p : params) = Z3native.params_to_string p#gnc p#gno
end

(** Expressions (terms) *)
module Expr =
struct
  (**
     Returns a simplified version of the expression.
     <param name="p">A set of parameters to configure the simplifier</param>
     <seealso cref="Context.SimplifyHelp"/>
  *)
  let simplify ( x : expr ) ( p : params option ) = match p with 
    | None -> create_expr x#gc (Z3native.simplify x#gnc x#gno)
    | Some pp -> create_expr x#gc (Z3native.simplify_ex x#gnc x#gno pp#gno)
      
  (**
     The function declaration of the function that is applied in this expression.
  *)
  let get_func_decl ( x : expr ) = (new func_decl x#gc)#cnstr_obj (Z3native.get_app_decl x#gnc x#gno)
    
  (**
     Indicates whether the expression is the true or false expression
     or something else (Z3_L_UNDEF).
  *)
  let get_bool_value ( x : expr ) = int2lbool (Z3native.get_bool_value x#gnc x#gno)

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
      x#sno x#gnc (Z3native.update_term x#gnc x#gno (Array.length args) (expraton args))

  (**
     Substitute every occurrence of <c>from[i]</c> in the expression with <c>to[i]</c>, for <c>i</c> smaller than <c>num_exprs</c>.
     <remarks>
     The result is the new expression. The arrays <c>from</c> and <c>to</c> must have size <c>num_exprs</c>.
     For every <c>i</c> smaller than <c>num_exprs</c>, we must have that 
     sort of <c>from[i]</c> must be equal to sort of <c>to[i]</c>.
     </remarks>    
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
     </remarks>
  *)
  let substitute_vars ( x : expr ) to_ =
    create_expr x#gc (Z3native.substitute_vars x#gnc x#gno (Array.length to_) (expraton to_))
      

  (**
     Translates (copies) the term to the Context <paramref name="ctx"/>.
     <param name="ctx">A context</param>
     <returns>A copy of the term which is associated with <paramref name="ctx"/></returns>
  *)
  let translate ( x : expr ) to_ctx =
    if x#gc == to_ctx then
      x
    else
      create_expr to_ctx (Z3native.translate x#gnc x#gno to_ctx#gno)

  (**
     Returns a string representation of the expression.
  *)    
  let to_string ( x : expr ) = Z3native.ast_to_string x#gnc x#gno

  (**
     Indicates whether the term is a numeral
  *)
  let is_numeral ( x : expr ) = int2lbool (Z3native.is_numeral_ast x#gnc x#gno) == L_TRUE
    
  (**
     Indicates whether the term is well-sorted.
     <returns>True if the term is well-sorted, false otherwise.</returns>
  *)   
  let is_well_sorted ( x : expr ) = int2lbool (Z3native.is_well_sorted x#gnc x#gno) == L_TRUE

  (**
     The Sort of the term.
  *)
  let get_sort ( x : expr ) = create_sort x#gc (Z3native.get_sort x#gnc x#gno)
    
  (**
     Indicates whether the term has Boolean sort.
  *)
  let is_bool ( x : expr ) = (AST.is_expr x) &&
    (int2lbool (Z3native.is_eq_sort x#gnc 
		  (Z3native.mk_bool_sort x#gnc)
                  (Z3native.get_sort x#gnc x#gno))) == L_TRUE
    
  (**
     Indicates whether the term is of integer sort.
  *)
  let is_int ( x : expr ) =
    ((int2lbool (Z3native.is_numeral_ast x#gnc x#gno)) == L_TRUE) &&
      ((int2sort_kind (Z3native.get_sort_kind x#gnc (Z3native.get_sort x#gnc x#gno))) == INT_SORT)
      
  (**
     Indicates whether the term is of sort real.
  *)
  let is_real ( x : expr ) =
    ((int2sort_kind (Z3native.get_sort_kind x#gnc (Z3native.get_sort x#gnc x#gno))) == REAL_SORT)

  (**
     Indicates whether the term is of an array sort.
  *)
  let is_array ( x : expr ) =
    ((int2lbool (Z3native.is_app x#gnc x#gno)) == L_TRUE) &&
      ((int2sort_kind (Z3native.get_sort_kind x#gnc (Z3native.get_sort x#gnc x#gno))) == ARRAY_SORT)      

  (**
     Indicates whether the term represents a constant.
  *)
  let is_const ( x : expr ) = (AST.is_expr x) &&
    (get_num_args x) == 0 &&
    FuncDecl.get_domain_size(get_func_decl x) == 0
    
  (**
     Indicates whether the term is an integer numeral.
  *)
  let is_int_numeral ( x : expr ) = (is_numeral x) && (is_int x)

  (**
     Indicates whether the term is a real numeral.
  *)
  let is_rat_num ( x : expr ) = (is_numeral x) && (is_real x)
    
  (**
     Indicates whether the term is an algebraic number
  *)
  let is_algebraic_number ( x : expr ) = int2lbool(Z3native.is_algebraic_number x#gnc x#gno) == L_TRUE
    
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
     Indicates whether the term is an arithmetic numeral.
  *)
  let is_arithmetic_numeral ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_ANUM)

  (**
     Indicates whether the term is a less-than-or-equal
  *)
  let is_le ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_LE)

  (**
     Indicates whether the term is a greater-than-or-equal
  *)
  let is_ge ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_GE)

  (**
     Indicates whether the term is a less-than
  *)
  let is_lt ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_LT)

  (**
     Indicates whether the term is a greater-than
  *)
  let is_gt ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_GT)

  (**
     Indicates whether the term is addition (binary)
  *)
  let is_add ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_ADD)

  (**
     Indicates whether the term is subtraction (binary)
  *)
  let is_sub ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_SUB)

  (**
     Indicates whether the term is a unary minus
  *)
  let is_uminus ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_UMINUS)

  (**
     Indicates whether the term is multiplication (binary)
  *)
  let is_mul ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_MUL)

  (**
     Indicates whether the term is division (binary)
  *)
  let is_div ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_DIV)

  (**
     Indicates whether the term is integer division (binary)
  *)
  let is_idiv ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_IDIV)

  (**
     Indicates whether the term is remainder (binary)
  *)
  let is_remainder ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_REM)

  (**
     Indicates whether the term is modulus (binary)
  *)
  let is_modulus ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_MOD)

  (**
     Indicates whether the term is a coercion of integer to real (unary)
  *)
  let is_inttoreal ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_TO_REAL)

  (**
     Indicates whether the term is a coercion of real to integer (unary)
  *)
  let is_real_to_int ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_TO_INT)

  (**
     Indicates whether the term is a check that tests whether a real is integral (unary)
  *)
  let is_real_is_int ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_IS_INT)

  (**
     Indicates whether the term is an array store.        
     <remarks>It satisfies select(store(a,i,v),j) = if i = j then v else select(a,j). 
     Array store takes at least 3 arguments. </remarks>
  *)
  let is_store ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_STORE)

  (**
     Indicates whether the term is an array select.
  *)
  let is_select ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_SELECT)

  (**
     Indicates whether the term is a constant array.        
     <remarks>For example, select(const(v),i) = v holds for every v and i. The function is unary.</remarks>
  *)
  let is_constant_array ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_CONST_ARRAY)

  (**
     Indicates whether the term is a default array.        
     <remarks>For example default(const(v)) = v. The function is unary.</remarks>
  *)
  let is_default_array ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_ARRAY_DEFAULT)

  (**
     Indicates whether the term is an array map.     
     <remarks>It satisfies map[f](a1,..,a_n)[i] = f(a1[i],...,a_n[i]) for every i.</remarks>
  *)
  let is_array_map ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_ARRAY_MAP)

  (**
     Indicates whether the term is an as-array term.        
     <remarks>An as-array term is n array value that behaves as the function graph of the 
     function passed as parameter.</remarks>
  *)
  let is_as_array ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_AS_ARRAY)       

  (**
     Indicates whether the term is set union
  *)
  let is_set_union ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_SET_UNION)

  (**
     Indicates whether the term is set intersection
  *)
  let is_set_intersect ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_SET_INTERSECT)

  (**
     Indicates whether the term is set difference
  *)
  let is_set_difference ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_SET_DIFFERENCE)

  (**
     Indicates whether the term is set complement
  *)
  let is_set_complement ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_SET_COMPLEMENT)

  (**
     Indicates whether the term is set subset
  *)
  let is_set_subset ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_SET_SUBSET)

  (**
     Indicates whether the terms is of bit-vector sort.
  *)
  let is_bv ( x : expr ) =
    ((int2sort_kind (Z3native.get_sort_kind x#gnc (Z3native.get_sort x#gnc x#gno))) == BV_SORT)

  (**
     Indicates whether the term is a bit-vector numeral
  *)
  let is_bv_numeral ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BNUM)

  (**
     Indicates whether the term is a one-bit bit-vector with value one
  *)
  let is_bv_bit1 ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BIT1)

  (**
     Indicates whether the term is a one-bit bit-vector with value zero
  *)
  let is_bv_bit0 ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BIT0)

  (**
     Indicates whether the term is a bit-vector unary minus
  *)
  let is_bv_uminus ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BNEG)

  (**
     Indicates whether the term is a bit-vector addition (binary)
  *)
  let is_bv_add ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BADD)

  (**
     Indicates whether the term is a bit-vector subtraction (binary)
  *)
  let is_bv_sub ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BSUB)

  (**
     Indicates whether the term is a bit-vector multiplication (binary)
  *)
  let is_bv_mul ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BMUL)

  (**
     Indicates whether the term is a bit-vector signed division (binary)
  *)
  let is_bv_sdiv ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BSDIV)

  (**
     Indicates whether the term is a bit-vector unsigned division (binary)
  *)
  let is_bv_udiv ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BUDIV)

  (**
     Indicates whether the term is a bit-vector signed remainder (binary)
  *)
  let is_bv_SRem ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BSREM)

  (**
     Indicates whether the term is a bit-vector unsigned remainder (binary)
  *)
  let is_bv_urem ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BUREM)

  (**
     Indicates whether the term is a bit-vector signed modulus
  *)
  let is_bv_smod ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BSMOD)

  (**
     Indicates whether the term is a bit-vector signed division by zero
  *)
  let is_bv_sdiv0 ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BSDIV0)

  (**
     Indicates whether the term is a bit-vector unsigned division by zero
  *)
  let is_bv_udiv0 ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BUDIV0)

  (**
     Indicates whether the term is a bit-vector signed remainder by zero
  *)
  let is_bv_srem0 ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BSREM0)

  (**
     Indicates whether the term is a bit-vector unsigned remainder by zero
  *)
  let is_bv_urem0 ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BUREM0)

  (**
     Indicates whether the term is a bit-vector signed modulus by zero
  *)
  let is_bv_smod0 ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BSMOD0)

  (**
     Indicates whether the term is an unsigned bit-vector less-than-or-equal
  *)
  let is_bv_ule ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_ULEQ)

  (**
     Indicates whether the term is a signed bit-vector less-than-or-equal
  *)
  let is_bv_sle ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_SLEQ)

  (**
     Indicates whether the term is an unsigned bit-vector greater-than-or-equal
  *)
  let is_bv_uge ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_UGEQ)

  (**
     Indicates whether the term is a signed bit-vector greater-than-or-equal
  *)
  let is_bv_sge ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_SGEQ)

  (**
     Indicates whether the term is an unsigned bit-vector less-than
  *)
  let is_bv_ult ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_ULT)

  (**
     Indicates whether the term is a signed bit-vector less-than
  *)
  let is_bv_slt ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_SLT)

  (**
     Indicates whether the term is an unsigned bit-vector greater-than
  *)
  let is_bv_ugt ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_UGT)

  (**
     Indicates whether the term is a signed bit-vector greater-than
  *)
  let is_bv_sgt ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_SGT)

  (**
     Indicates whether the term is a bit-wise AND
  *)
  let is_bv_and ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BAND)

  (**
     Indicates whether the term is a bit-wise OR
  *)
  let is_bv_or ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BOR)

  (**
     Indicates whether the term is a bit-wise NOT
  *)
  let is_bv_not ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BNOT)

  (**
     Indicates whether the term is a bit-wise XOR
  *)
  let is_bv_xor ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BXOR)

  (**
     Indicates whether the term is a bit-wise NAND
  *)
  let is_bv_nand ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BNAND)

  (**
     Indicates whether the term is a bit-wise NOR
  *)
  let is_bv_nor ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BNOR)

  (**
     Indicates whether the term is a bit-wise XNOR
  *)
  let is_bv_xnor ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BXNOR)

  (**
     Indicates whether the term is a bit-vector concatenation (binary)
  *)
  let is_bv_concat ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_CONCAT)

  (**
     Indicates whether the term is a bit-vector sign extension
  *)
  let is_bv_signextension ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_SIGN_EXT)

  (**
     Indicates whether the term is a bit-vector zero extension
  *)
  let is_bv_zeroextension ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_ZERO_EXT)

  (**
     Indicates whether the term is a bit-vector extraction
  *)
  let is_bv_extract ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_EXTRACT)

  (**
     Indicates whether the term is a bit-vector repetition
  *)
  let is_bv_repeat ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_REPEAT)

  (**
     Indicates whether the term is a bit-vector reduce OR
  *)
  let is_bv_reduceor ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BREDOR)

  (**
     Indicates whether the term is a bit-vector reduce AND
  *)
  let is_bv_reduceand ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BREDAND)

  (**
     Indicates whether the term is a bit-vector comparison
  *)
  let is_bv_comp ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BCOMP)

  (**
     Indicates whether the term is a bit-vector shift left
  *)
  let is_bv_shiftleft ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BSHL)

  (**
     Indicates whether the term is a bit-vector logical shift right
  *)
  let is_bv_shiftrightlogical ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BLSHR)

  (**
     Indicates whether the term is a bit-vector arithmetic shift left
  *)
  let is_bv_shiftrightarithmetic ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BASHR)

  (**
     Indicates whether the term is a bit-vector rotate left
  *)
  let is_bv_rotateleft ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_ROTATE_LEFT)

  (**
     Indicates whether the term is a bit-vector rotate right
  *)
  let is_bv_rotateright ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_ROTATE_RIGHT)

  (**
     Indicates whether the term is a bit-vector rotate left (extended)
     <remarks>Similar to Z3_OP_ROTATE_LEFT, but it is a binary operator instead of a parametric one.</remarks>
  *)
  let is_bv_rotateleftextended ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_EXT_ROTATE_LEFT)

  (**
     Indicates whether the term is a bit-vector rotate right (extended)
     <remarks>Similar to Z3_OP_ROTATE_RIGHT, but it is a binary operator instead of a parametric one.</remarks>
  *)
  let is_bv_rotaterightextended ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_EXT_ROTATE_RIGHT)

  (**
     Indicates whether the term is a coercion from integer to bit-vector
     <remarks>This function is not supported by the decision procedures. Only the most 
     rudimentary simplification rules are applied to this function.</remarks>
  *)
  let is_int_to_bv ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_INT2BV)

  (**
     Indicates whether the term is a coercion from bit-vector to integer
     <remarks>This function is not supported by the decision procedures. Only the most 
     rudimentary simplification rules are applied to this function.</remarks>
  *)
  let is_bv_to_int ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_BV2INT)

  (**
     Indicates whether the term is a bit-vector carry
     <remarks>Compute the carry bit in a full-adder.  The meaning is given by the 
     equivalence (carry l1 l2 l3) &lt;=&gt; (or (and l1 l2) (and l1 l3) (and l2 l3)))</remarks>
  *)
  let is_bv_carry ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_CARRY)

  (**
     Indicates whether the term is a bit-vector ternary XOR
     <remarks>The meaning is given by the equivalence (xor3 l1 l2 l3) &lt;=&gt; (xor (xor l1 l2) l3)</remarks>
  *)
  let is_bv_xor3 ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_XOR3)

  (**
     Indicates whether the term is a label (used by the Boogie Verification condition generator).
     <remarks>The label has two parameters, a string and a Boolean polarity. It takes one argument, a formula.</remarks>
  *)
  let is_label ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_LABEL)

  (**
     Indicates whether the term is a label literal (used by the Boogie Verification condition generator).                     
     <remarks>A label literal has a set of string parameters. It takes no arguments.</remarks>
     let is_label_lit ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_LABEL_LIT)
  *)

  (**
     Indicates whether the term is a binary equivalence modulo namings. 
     <remarks>This binary predicate is used in proof terms.
     It captures equisatisfiability and equivalence modulo renamings.</remarks>
  *)
  let is_oeq ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_OEQ)

  (**
     Indicates whether the term is a Proof for the expression 'true'.
  *)
  let is_proof_true ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_TRUE)

  (**
     Indicates whether the term is a proof for a fact asserted by the user.
  *)
  let is_proof_asserted ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_ASSERTED)

  (**
     Indicates whether the term is a proof for a fact (tagged as goal) asserted by the user.
  *)
  let is_proof_goal ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_GOAL)

  (**
     Indicates whether the term is proof via modus ponens
     <remarks>
     Given a proof for p and a proof for (implies p q), produces a proof for q.
     T1: p
     T2: (implies p q)
     [mp T1 T2]: q
     The second antecedents may also be a proof for (iff p q).</remarks>
  *)
  let is_proof_modus_ponens ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_MODUS_PONENS)

  (**
     Indicates whether the term is a proof for (R t t), where R is a reflexive relation.
     <remarks>This proof object has no antecedents. 
     The only reflexive relations that are used are 
     equivalence modulo namings, equality and equivalence.
     That is, R is either '~', '=' or 'iff'.</remarks>
  *)
  let is_proof_reflexivity ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_REFLEXIVITY)

  (**
     Indicates whether the term is proof by symmetricity of a relation
     <remarks>
     Given an symmetric relation R and a proof for (R t s), produces a proof for (R s t).
     T1: (R t s)
     [symmetry T1]: (R s t)
     T1 is the antecedent of this proof object.
     </remarks>
  *)
  let is_proof_symmetry ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_SYMMETRY)

  (**
     Indicates whether the term is a proof by transitivity of a relation
     <remarks>
     Given a transitive relation R, and proofs for (R t s) and (R s u), produces a proof 
     for (R t u). 
     T1: (R t s)
     T2: (R s u)
     [trans T1 T2]: (R t u)
     </remarks>
  *)
  let is_proof_transitivity ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_TRANSITIVITY)

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
     </remarks>
  *)
  let is_proof_Transitivity_star ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_TRANSITIVITY_STAR)


  (**
     Indicates whether the term is a monotonicity proof object.
     <remarks>
     T1: (R t_1 s_1)
     ...
     Tn: (R t_n s_n)
     [monotonicity T1 ... Tn]: (R (f t_1 ... t_n) (f s_1 ... s_n))          
     Remark: if t_i == s_i, then the antecedent Ti is suppressed.
     That is, reflexivity proofs are supressed to save space.
     </remarks>
  *)
  let is_proof_monotonicity ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_MONOTONICITY)

  (**
     Indicates whether the term is a quant-intro proof 
     <remarks>
     Given a proof for (~ p q), produces a proof for (~ (forall (x) p) (forall (x) q)).
     T1: (~ p q)
     [quant-intro T1]: (~ (forall (x) p) (forall (x) q))
     </remarks>
  *)
  let is_proof_quant_intro ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_QUANT_INTRO)

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
     </remarks>
  *)
  let is_proof_distributivity ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_DISTRIBUTIVITY)

  (**
     Indicates whether the term is a proof by elimination of AND
     <remarks>
     Given a proof for (and l_1 ... l_n), produces a proof for l_i
     T1: (and l_1 ... l_n)
     [and-elim T1]: l_i
     </remarks>
  *)
  let is_proof_and_elimination ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_AND_ELIM)

  (**
     Indicates whether the term is a proof by eliminiation of not-or
     <remarks>
     Given a proof for (not (or l_1 ... l_n)), produces a proof for (not l_i).
     T1: (not (or l_1 ... l_n))
     [not-or-elim T1]: (not l_i)       
     </remarks>
  *)
  let is_proof_or_elimination ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_NOT_OR_ELIM)

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
     </remarks>
  *)
  let is_proof_rewrite ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_REWRITE)

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
     </remarks>
  *)
  let is_proof_rewrite_star ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_REWRITE_STAR)

  (**
     Indicates whether the term is a proof for pulling quantifiers out.
     <remarks>
     A proof for (iff (f (forall (x) q(x)) r) (forall (x) (f (q x) r))). This proof object has no antecedents.
     </remarks>
  *)
  let is_proof_pull_quant ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_PULL_QUANT)

  (**
     Indicates whether the term is a proof for pulling quantifiers out.
     <remarks>
     A proof for (iff P Q) where Q is in prenex normal form. 
     This proof object is only used if the parameter PROOF_MODE is 1.       
     This proof object has no antecedents
     </remarks>
  *)
  let is_proof_pull_quant_star ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_PULL_QUANT_STAR)

  (**
     Indicates whether the term is a proof for pushing quantifiers in.
     <remarks>
     A proof for:
     (iff (forall (x_1 ... x_m) (and p_1[x_1 ... x_m] ... p_n[x_1 ... x_m]))
     (and (forall (x_1 ... x_m) p_1[x_1 ... x_m])
     ... 
     (forall (x_1 ... x_m) p_n[x_1 ... x_m])))               
     This proof object has no antecedents
     </remarks>
  *)
  let is_proof_push_quant ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_PUSH_QUANT)

  (**
     Indicates whether the term is a proof for elimination of unused variables.
     <remarks>
     A proof for (iff (forall (x_1 ... x_n y_1 ... y_m) p[x_1 ... x_n])
     (forall (x_1 ... x_n) p[x_1 ... x_n])) 
     
     It is used to justify the elimination of unused variables.
     This proof object has no antecedents.
     </remarks>
  *)
  let is_proof_elim_unused_vars ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_ELIM_UNUSED_VARS)

  (**
     Indicates whether the term is a proof for destructive equality resolution
     <remarks>
     A proof for destructive equality resolution:
     (iff (forall (x) (or (not (= ( x : expr ) t)) P[x])) P[t])
     if ( x : expr ) does not occur in t.
     
     This proof object has no antecedents.
     
     Several variables can be eliminated simultaneously.
     </remarks>
  *)
  let is_proof_der ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_DER)

  (**
     Indicates whether the term is a proof for quantifier instantiation
     <remarks>
     A proof of (or (not (forall (x) (P x))) (P a))
     </remarks>
  *)
  let is_proof_quant_inst ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_QUANT_INST)

  (**
     Indicates whether the term is a hypthesis marker.
     <remarks>Mark a hypothesis in a natural deduction style proof.</remarks>
  *)
  let is_proof_hypothesis ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_HYPOTHESIS)

  (**
     Indicates whether the term is a proof by lemma
     <remarks>
     T1: false
     [lemma T1]: (or (not l_1) ... (not l_n))
     
     This proof object has one antecedent: a hypothetical proof for false.
     It converts the proof in a proof for (or (not l_1) ... (not l_n)),
     when T1 contains the hypotheses: l_1, ..., l_n.
     </remarks>
  *)
  let is_proof_lemma ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_LEMMA)

  (**
     Indicates whether the term is a proof by unit resolution
     <remarks>
     T1:      (or l_1 ... l_n l_1' ... l_m')
     T2:      (not l_1)
     ...
     T(n+1):  (not l_n)
     [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m')
     </remarks>
  *)
  let is_proof_unit_resolution ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_UNIT_RESOLUTION)

  (**
     Indicates whether the term is a proof by iff-true
     <remarks>
     T1: p
     [iff-true T1]: (iff p true)
     </remarks>
  *)
  let is_proof_iff_true ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_IFF_TRUE)

  (**
     Indicates whether the term is a proof by iff-false
     <remarks>
     T1: (not p)
     [iff-false T1]: (iff p false)
     </remarks>
  *)
  let is_proof_iff_false ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_IFF_FALSE)

  (**
     Indicates whether the term is a proof by commutativity
     <remarks>
     [comm]: (= (f a b) (f b a))
     
     f is a commutative operator.
     
     This proof object has no antecedents.
     Remark: if f is bool, then = is iff.
     </remarks>
  *)
  let is_proof_commutativity ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_COMMUTATIVITY) (*  *)

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
     </remarks>
  *)
  let is_proof_def_axiom ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_DEF_AXIOM)

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
     </remarks>
  *)
  let is_proof_def_intro ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_DEF_INTRO)

  (**
     Indicates whether the term is a proof for application of a definition
     <remarks>
     [apply-def T1]: F ~ n
     F is 'equivalent' to n, given that T1 is a proof that
     n is a name for F.
     </remarks>
  *)
  let is_proof_apply_def ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_APPLY_DEF)

  (**
     Indicates whether the term is a proof iff-oeq
     <remarks>
     T1: (iff p q)
     [iff~ T1]: (~ p q)
     </remarks>
  *)
  let is_proof_iff_oeq ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_IFF_OEQ)

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
     </remarks>
  *)
  let is_proof_nnf_pos ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_NNF_POS)

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
     </remarks>
  *)
  let is_proof_nnf_neg ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_NNF_NEG)

  (**
     Indicates whether the term is a proof for (~ P Q) here Q is in negation normal form.
     <remarks>
     A proof for (~ P Q) where Q is in negation normal form.
     
     This proof object is only used if the parameter PROOF_MODE is 1.       
     
     This proof object may have n antecedents. Each antecedent is a PR_DEF_INTRO.
     </remarks>
  *)
  let is_proof_nnf_star ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_NNF_STAR)

  (**
     Indicates whether the term is a proof for (~ P Q) where Q is in conjunctive normal form.
     <remarks>
     A proof for (~ P Q) where Q is in conjunctive normal form.
     This proof object is only used if the parameter PROOF_MODE is 1.       
     This proof object may have n antecedents. Each antecedent is a PR_DEF_INTRO.          
     </remarks>
  *)
  let is_proof_cnf_star ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_CNF_STAR)

  (**
     Indicates whether the term is a proof for a Skolemization step
     <remarks>
     Proof for: 
     
     [sk]: (~ (not (forall ( x : expr ) (p ( x : expr ) y))) (not (p (sk y) y)))
     [sk]: (~ (exists ( x : expr ) (p ( x : expr ) y)) (p (sk y) y))
     
     This proof object has no antecedents.
     </remarks>
  *)
  let is_proof_skolemize ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_SKOLEMIZE)

  (**
     Indicates whether the term is a proof by modus ponens for equi-satisfiability.
     <remarks>
     Modus ponens style rule for equi-satisfiability.
     T1: p
     T2: (~ p q)
     [mp~ T1 T2]: q  
     </remarks>
  *)
  let is_proof_modus_ponens_oeq ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_MODUS_PONENS_OEQ)

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
     (iff (= t1 t2) (and (&lt;= t1 t2) (&lt;= t2 t1)))
     - gcd-test - Indicates an integer linear arithmetic lemma that uses a gcd test.
     </remarks>
  *)
  let is_proof_theory_lemma ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_PR_TH_LEMMA)

  (**
     Indicates whether the term is of a relation sort.
  *)
  let is_Relation ( x : expr ) =
    ((int2lbool (Z3native.is_app x#gnc x#gno)) == L_TRUE) &&
      (int2sort_kind (Z3native.get_sort_kind x#gnc (Z3native.get_sort x#gnc x#gno)) == RELATION_SORT)

  (**
     Indicates whether the term is an relation store
     <remarks>
     Insert a record into a relation.
     The function takes <c>n+1</c> arguments, where the first argument is the relation and the remaining <c>n</c> elements 
     correspond to the <c>n</c> columns of the relation.
     </remarks>
  *)
  let is_relation_store ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_RA_STORE)

  (**
     Indicates whether the term is an empty relation
  *)
  let is_empty_relation ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_RA_EMPTY)

  (**
     Indicates whether the term is a test for the emptiness of a relation
  *)
  let is_is_empty_relation ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_RA_IS_EMPTY)

  (**
     Indicates whether the term is a relational join
  *)
  let is_relational_join ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_RA_JOIN)

  (**
     Indicates whether the term is the union or convex hull of two relations. 
     <remarks>The function takes two arguments.</remarks>
  *)
  let is_relation_union ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_RA_UNION)

  (**
     Indicates whether the term is the widening of two relations
     <remarks>The function takes two arguments.</remarks>
  *)
  let is_relation_widen ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_RA_WIDEN)

  (**
     Indicates whether the term is a projection of columns (provided as numbers in the parameters).
     <remarks>The function takes one argument.</remarks>
  *)
  let is_relation_project ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_RA_PROJECT)

  (**
     Indicates whether the term is a relation filter
     <remarks>
     Filter (restrict) a relation with respect to a predicate.
     The first argument is a relation. 
     The second argument is a predicate with free de-Brujin indices
     corresponding to the columns of the relation.
     So the first column in the relation has index 0.
     </remarks>
  *)
  let is_relation_filter ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_RA_FILTER)

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
     </remarks>
  *)
  let is_relation_negation_filter ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_RA_NEGATION_FILTER)

  (**
     Indicates whether the term is the renaming of a column in a relation
     <remarks>    
     The function takes one argument.
     The parameters contain the renaming as a cycle.
     </remarks>
  *)
  let is_relation_rename ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_RA_RENAME)

  (**
     Indicates whether the term is the complement of a relation
  *)
  let is_relation_complement ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_RA_COMPLEMENT)

  (**
     Indicates whether the term is a relational select
     <remarks>
     Check if a record is an element of the relation.
     The function takes <c>n+1</c> arguments, where the first argument is a relation,
     and the remaining <c>n</c> arguments correspond to a record.
     </remarks>
  *)
  let is_relation_select ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_RA_SELECT)

  (**
     Indicates whether the term is a relational clone (copy)
     <remarks>
     Create a fresh copy (clone) of a relation. 
     The function is logically the identity, but
     in the context of a register machine allows 
     for terms of kind <seealso cref="IsRelationUnion"/> 
     to perform destructive updates to the first argument.
     </remarks>
  *)
  let is_relation_clone ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_RA_CLONE)

  (**
     Indicates whether the term is of an array sort.
  *)
  let is_finite_domain ( x : expr ) =
    ((int2lbool (Z3native.is_app x#gnc x#gno)) == L_TRUE) &&
      (int2sort_kind (Z3native.get_sort_kind x#gnc (Z3native.get_sort x#gnc x#gno)) == FINITE_DOMAIN_SORT)

  (**
     Indicates whether the term is a less than predicate over a finite domain.
  *)
  let is_finite_domain_lt ( x : expr ) = (FuncDecl.get_decl_kind (get_func_decl x) == OP_FD_LT)

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
     </remarks>
  *)
  let get_index ( x : expr ) = 
    if not (AST.is_var x) then
      raise (Z3native.Exception "Term is not a bound variable.")
    else
      Z3native.get_index_value x#gnc x#gno
end

(* Integer Numerals *)
module IntNum =
struct
  (**  Retrieve the int value. *)
  let get_int ( x : int_num ) = let (r, v) = Z3native.get_numeral_int x#gnc x#gno in
		  if int2lbool(r) == L_TRUE then v
		  else raise (Z3native.Exception "Conversion failed.")

  (** Returns a string representation of the numeral. *)
  let to_string ( x : int_num ) = Z3native.get_numeral_string x#gnc x#gno		    
end

(** Rational Numerals *)
module RatNum =
struct

  (** The numerator of a rational numeral. *)
  let get_numerator ( x : rat_num ) =
    (new int_num x#gc)#cnstr_obj (Z3native.get_numerator x#gnc x#gno)

  (** The denominator of a rational numeral. *)
  let get_denominator ( x : rat_num ) =
    (new int_num x#gc)#cnstr_obj (Z3native.get_denominator x#gnc x#gno)

  (** Returns a string representation in decimal notation. 
      <remarks>The result has at most <paramref name="precision"/> decimal places.</remarks>*)
  let to_decimal_string ( x : rat_num ) (precision : int) = 
    Z3native.get_numeral_decimal_string x#gnc x#gno precision

  (** Returns a string representation of the numeral. *)
  let to_string ( x : rat_num ) = Z3native.get_numeral_string x#gnc x#gno
end

(** Bit-vector numerals *)
module BitVecNum =
struct
  (**  Retrieve the int value. *)
  let get_int ( x : bitvec_num ) = let (r, v) = Z3native.get_numeral_int x#gnc x#gno in
		  if int2lbool(r) == L_TRUE then v
		  else raise (Z3native.Exception "Conversion failed.")
		    
  (** Returns a string representation of the numeral. *)
  let to_string ( x : bitvec_num ) = Z3native.get_numeral_string x#gnc x#gno
end

(** Algebraic numbers *)
module AlgebraicNum =
struct
  (**
     Return a upper bound for a given real algebraic number. 
     The interval isolating the number is smaller than 1/10^<paramref name="precision"/>.    
     <seealso cref="Expr.IsAlgebraicNumber"/>   
     </summary>
     <param name="precision">the precision of the result</param>
     <returns>A numeral Expr of sort Real</returns>
  *)
  let to_upper ( x : algebraic_num ) ( precision : int ) =
    (new rat_num x#gc)#cnstr_obj (Z3native.get_algebraic_number_upper x#gnc x#gno precision)

  (**
     Return a lower bound for the given real algebraic number. 
     The interval isolating the number is smaller than 1/10^<paramref name="precision"/>.    
     <seealso cref="Expr.IsAlgebraicNumber"/>
     </summary>
     <param name="precision"></param>
     <returns>A numeral Expr of sort Real</returns>
  *)
  let to_lower ( x : algebraic_num ) precision =
    (new rat_num x#gc)#cnstr_obj (Z3native.get_algebraic_number_lower x#gnc x#gno precision)
      
  (** Returns a string representation in decimal notation. 
      <remarks>The result has at most <paramref name="precision"/> decimal places.</remarks>*)
  let to_decimal_string ( x : algebraic_num ) ( precision : int ) = 
    Z3native.get_numeral_decimal_string x#gnc x#gno precision
      
  (** Returns a string representation of the numeral. *)
  let to_string ( x : algebraic_num ) = Z3native.get_numeral_string x#gnc x#gno
end
  
(** The main interaction with Z3 happens via the Context module. *)
module Context =
struct

  (* SYMBOLS *)

  (**
     Creates a new symbol using an integer.
     
     Not all integers can be passed to this function.
     The legal range of unsigned integers is 0 to 2^30-1.
  *)
  let mk_symbol_int ( ctx : context ) i = 
    (new int_symbol ctx)#cnstr_int i
      
  (** Creates a new symbol using a string. *)
  let mk_symbol_string ( ctx : context ) s =
    (new string_symbol ctx)#cnstr_string s

  (**
     Create an array of symbols.
  *)
  let mk_symbols_int ( ctx : context ) names =
    let f elem = mk_symbol_int ( ctx : context ) elem in
    (Array.map f names)

  (**
     Create an array of symbols.
  *)
  let mk_symbols_string ( ctx : context ) names =
    let f elem = mk_symbol_string ( ctx : context ) elem in
    (Array.map f names)
      
      
  (* SORTS *)
      
  (**
     Create a new Boolean sort.
  *)
  let mk_bool_sort ( ctx : context ) =
    (new bool_sort ctx)
      
  (**
     Create a new uninterpreted sort.
  *)
  let mk_uninterpreted_sort ( ctx : context ) (s : symbol) =
    (new uninterpreted_sort ctx)#cnstr_s s

  (**
     Create a new uninterpreted sort.
  *)
  let mk_uninterpreted_sort_s ( ctx : context ) (s : string) =
    mk_uninterpreted_sort ctx ((mk_symbol_string ( ctx : context ) s) :> symbol)

  (**
     Create a new integer sort.
  *)
  let mk_int_sort ( ctx : context ) =
    (new int_sort ctx)

  (**
     Create a real sort.
  *)    
  let mk_real_sort ( ctx : context ) =
    (new real_sort ctx)

  (**
     Create a new bit-vector sort.
  *)
  let mk_bitvec_sort ( ctx : context ) size =
    (new bitvec_sort ctx)#cnstr_obj (Z3native.mk_bv_sort ctx#gno size)

  (**
     Create a new array sort.
  *)
  let mk_array_sort ( ctx : context ) domain range =
    (new array_sort ctx)#cnstr_dr domain range

  (**
     Create a new tuple sort.
  *)    
  let mk_tuple_sort ( ctx : context ) name field_names field_sorts =
    (new tuple_sort ctx)#cnstr_siss name (Array.length field_names) field_names field_sorts

  (**
     Create a new enumeration sort.
  *)
  let mk_enum_sort ( ctx : context ) name enum_names =
    (new enum_sort ctx)#cnstr_ss name enum_names

  (**
     Create a new enumeration sort.
  *)
  let mk_enum_sort_s ( ctx : context ) name enum_names =
    (new enum_sort ctx)#cnstr_ss 
      ((mk_symbol_string ( ctx : context ) name) :> symbol) 
      (let f e = (e :> symbol) in
       (Array.map f (mk_symbols_string ( ctx : context ) enum_names))
      )

   (**
      Create a new list sort.
   *)
  let mk_list_sort ( ctx : context ) (name : symbol) elem_sort =
      (new list_sort ctx)#cnstr_ss name elem_sort
      
   (**
      Create a new list sort.
   *)
  let mk_list_sort_s ( ctx : context ) (name : string) elem_sort =
    mk_list_sort ctx ((mk_symbol_string ctx name) :> symbol) elem_sort


   (**
      Create a new finite domain sort.
   *)
  let mk_finite_domain_sort ( ctx : context ) ( name : symbol ) size =
    (new finite_domain_sort ctx)#cnstr_si name size
      
   (**
      Create a new finite domain sort.
   *)
  let mk_finite_domain_sort_s ( ctx : context ) ( name : string ) size =
    (new finite_domain_sort ctx)#cnstr_si ((mk_symbol_string ctx name) :> symbol) size

(**

(* DATATYPES *)
(**
   Create a datatype constructor.
*)
   @param name constructor name
   @param recognizer name of recognizer function.
   @param fieldNames names of the constructor fields.
   @param sorts field sorts, 0 if the field sort refers to a recursive sort.
   @param sortRefs reference to datatype sort that is an argument to the constructor; 
   if the corresponding sort reference is 0, then the value in sort_refs should be an index 
   referring to one of the recursive datatypes that is declared.
   public Constructor MkConstructor(Symbol name, Symbol recognizer, Symbol[] fieldNames = null, Sort[] sorts = null, uint[] sortRefs = null)
   {




   return new Constructor(this, name, recognizer, fieldNames, sorts, sortRefs);
   }

(**
   Create a datatype constructor.
*)
   @param name 
   @param recognizer 
   @param fieldNames 
   @param sorts 
   @param sortRefs 
   @return 
   public Constructor MkConstructor(string name, string recognizer, string[] fieldNames = null, Sort[] sorts = null, uint[] sortRefs = null)
   {


   return new Constructor(this, MkSymbol(name), MkSymbol(recognizer), MkSymbols(fieldNames), sorts, sortRefs);
   }

(**
   Create a new datatype sort.
*)
   let mk_Datatype_Sort(Symbol name, Constructor[] constructors)
   {






   CheckContextMatch(name);
   CheckContextMatch(constructors);
   return new DatatypeSort(this, name, constructors);
   }

(**
   Create a new datatype sort.
*)
   let mk_Datatype_Sort(string name, Constructor[] constructors)
   {




   CheckContextMatch(constructors);
   return new DatatypeSort(this, MkSymbol(name), constructors);
   }

(**
   Create mutually recursive datatypes.
*)
   @param names names of datatype sorts
   @param c list of constructors, one list per sort.
   let mk_Datatype_Sorts(Symbol[] names, Constructor[][] c)
   {







   CheckContextMatch(names);
   uint n = (uint)names.Length;
   ConstructorList[] cla = new ConstructorList[n];
   IntPtr[] n_constr = new IntPtr[n];
   for (uint i = 0; i < n; i++)
   {
   Constructor[] constructor = c[i];

   CheckContextMatch(constructor);
   cla[i] = new ConstructorList(this, constructor);
   n_constr[i] = cla[i].x#gno;
   }
   IntPtr[] n_res = new IntPtr[n];
   Z3native.mk_datatypes(nCtx, n, Symbol.ArrayToNative(names), n_res, n_constr);
   DatatypeSort[] res = new DatatypeSort[n];
   for (uint i = 0; i < n; i++)
   res[i] = new DatatypeSort(this, n_res[i]);
   return res;
   }

(**
   Create mutually recursive data-types.
*)
   @param names 
   @param c 
   @return 
   let mk_Datatype_Sorts(string[] names, Constructor[][] c)
   {







   return MkDatatypeSorts(MkSymbols(names), c);
   }

   
   

(* FUNCTION DECLARATIONS *)
(**
   Creates a new function declaration.
*)
   public Func_Decl MkFunc_Decl(Symbol name, Sort[] domain, Sort range)
   {





   CheckContextMatch(name);
   CheckContextMatch(domain);
   CheckContextMatch(range);
   return new Func_Decl(this, name, domain, range);
   }

(**
   Creates a new function declaration.
*)
   public Func_Decl MkFunc_Decl(Symbol name, Sort domain, Sort range)
   {





   CheckContextMatch(name);
   CheckContextMatch(domain);
   CheckContextMatch(range);
   Sort[] q = new Sort[] { domain };
   return new Func_Decl(this, name, q, range);
   }

(**
   Creates a new function declaration.
*)
   public Func_Decl MkFunc_Decl(string name, Sort[] domain, Sort range)
   {




   CheckContextMatch(domain);
   CheckContextMatch(range);
   return new Func_Decl(this, MkSymbol(name), domain, range);
   }

(**
   Creates a new function declaration.
*)
   public Func_Decl MkFunc_Decl(string name, Sort domain, Sort range)
   {




   CheckContextMatch(domain);
   CheckContextMatch(range);
   Sort[] q = new Sort[] { domain };
   return new Func_Decl(this, MkSymbol(name), q, range);
   }

(**
   Creates a fresh function declaration with a name prefixed with <paramref name="prefix"/>.
*)
   <seealso cref="MkFunc_Decl(string,Sort,Sort)"/>
   <seealso cref="MkFunc_Decl(string,Sort[],Sort)"/>
   let mk_Fresh_Func_Decl(string prefix, Sort[] domain, Sort range)
   {




   CheckContextMatch(domain);
   CheckContextMatch(range);
   return new Func_Decl(this, prefix, domain, range);
   }

(**
   Creates a new constant function declaration.
*)
   let mk_Const_Decl(Symbol name, Sort range)
   {




   CheckContextMatch(name);
   CheckContextMatch(range);
   return new Func_Decl(this, name, null, range);
   }

(**
   Creates a new constant function declaration.
*)
   let mk_Const_Decl(string name, Sort range)
   {



   CheckContextMatch(range);
   return new Func_Decl(this, MkSymbol(name), null, range);
   }

(**
   Creates a fresh constant function declaration with a name prefixed with <paramref name="prefix"/>.
*)
   <seealso cref="MkFunc_Decl(string,Sort,Sort)"/>
   <seealso cref="MkFunc_Decl(string,Sort[],Sort)"/>
   let mk_Fresh_ConstDecl(string prefix, Sort range)
   {



   CheckContextMatch(range);
   return new Func_Decl(this, prefix, null, range);
   }
   

(* BOUND VARIABLES *)
(**
   Creates a new bound variable.
*)
   @param index The de-Bruijn index of the variable
   @param ty The sort of the variable
   public Expr MkBound(uint index, Sort ty)
   {



   return Expr.Create(this, Z3native.mk_bound(nCtx, index, ty.x#gno));
   }
   

(* QUANTIFIER PATTERNS *)
(**
   Create a quantifier pattern.
*)
   public Pattern MkPattern(params Expr[] terms)
   {

   if (terms.Length == 0)
   throw new Z3Exception("Cannot create a pattern from zero terms");





   IntPtr[] termsNative = AST.ArrayToNative(terms);
   return new Pattern(this, Z3native.mk_pattern(nCtx, (uint)terms.Length, termsNative));
   }
   

(* CONSTANTS *)
(**
   Creates a new Constant of sort <paramref name="range"/> and named <paramref name="name"/>.
*)
   public Expr MkConst(Symbol name, Sort range)
   {




   CheckContextMatch(name);
   CheckContextMatch(range);

   return Expr.Create(this, Z3native.mk_const(nCtx, name.x#gno, range.x#gno));
   }

(**
   Creates a new Constant of sort <paramref name="range"/> and named <paramref name="name"/>.
*)
   public Expr MkConst(string name, Sort range)
   {



   return MkConst(MkSymbol(name), range);
   }

(**
   Creates a fresh Constant of sort <paramref name="range"/> and a 
   name prefixed with <paramref name="prefix"/>.
*)
   let mk_Fresh_Const(string prefix, Sort range)
   {



   CheckContextMatch(range);
   return Expr.Create(this, Z3native.mk_fresh_const(nCtx, prefix, range.x#gno));
   }

(**
   Creates a fresh constant from the Func_Decl <paramref name="f"/>.
*)
   @param f A decl of a 0-arity function
   public Expr MkConst(Func_Decl f)
   {



   return MkApp(f);
   }

(**
   Create a Boolean constant.
*)        
   let mk_Bool_Const(Symbol name)
   {



   return (BoolExpr)MkConst(name, BoolSort);
   }

(**
   Create a Boolean constant.
*)        
   let mk_Bool_Const(string name)
   {


   return (BoolExpr)MkConst(MkSymbol(name), BoolSort);
   }

(**
   Creates an integer constant.
*)        
   let mk_Int_Const(Symbol name)
   {



   return (IntExpr)MkConst(name, IntSort);
   }

(**
   Creates an integer constant.
*)
   let mk_Int_Const(string name)
   {



   return (IntExpr)MkConst(name, IntSort);
   }

(**
   Creates a real constant.
*)
   let mk_Real_Const(Symbol name)
   {



   return (RealExpr)MkConst(name, RealSort);
   }

(**
   Creates a real constant.
*)
   let mk_Real_Const(string name)
   {


   return (RealExpr)MkConst(name, RealSort);
   }

(**
   Creates a bit-vector constant.
*)
   let mk_B_VConst(Symbol name, uint size)
   {



   return (BitVecExpr)MkConst(name, MkBitVecSort(size));
   }

(**
   Creates a bit-vector constant.
*)
   let mk_B_VConst(string name, uint size)
   {


   return (BitVecExpr)MkConst(name, MkBitVecSort(size));
   }
   

(* TERMS *)
(**
   Create a new function application.
*)
   public Expr MkApp(Func_Decl f, params Expr[] args)
   {




   CheckContextMatch(f);
   CheckContextMatch(args);
   return Expr.Create(this, f, args);
   }

(* PROPOSITIONAL *)
(**
   The true Term.
*)    
   public BoolExpr MkTrue ( ctx : context ) =
   {


   return new BoolExpr(this, Z3native.mk_true(nCtx));
   }

(**
   The false Term.
*)    
   public BoolExpr MkFalse ( ctx : context ) =
   {


   return new BoolExpr(this, Z3native.mk_false(nCtx));
   }

(**
   Creates a Boolean value.
*)        
   public BoolExpr MkBool(bool value)
   {


   return value ? MkTrue ( ctx : context ) = : MkFalse ( ctx : context ) =;
   }

(**
   Creates the equality <paramref name="x"/> = <paramref name="y"/>.
*)
   public BoolExpr MkEq(Expr x, Expr y)
   {




   CheckContextMatch(x);
   CheckContextMatch(y);
   return new BoolExpr(this, Z3native.mk_eq(nCtx, x.x#gno, y.x#gno));
   }

(**
   Creates a <c>distinct</c> term.
*)
   public BoolExpr MkDistinct(params Expr[] args)
   {





   CheckContextMatch(args);
   return new BoolExpr(this, Z3native.mk_distinct(nCtx, (uint)args.Length, AST.ArrayToNative(args)));
   }

(**
   Mk an expression representing <c>not(a)</c>.
*)    
   public BoolExpr MkNot(BoolExpr a)
   {



   CheckContextMatch(a);
   return new BoolExpr(this, Z3native.mk_not(nCtx, a.x#gno));
   }

(**    
   Create an expression representing an if-then-else: <c>ite(t1, t2, t3)</c>.
*)
   @param t1 An expression with Boolean sort
   @param t2 An expression 
   @param t3 An expression with the same sort as <paramref name="t2"/>
   let mk_I_TE(BoolExpr t1, Expr t2, Expr t3)
   {





   CheckContextMatch(t1);
   CheckContextMatch(t2);
   CheckContextMatch(t3);
   return Expr.Create(this, Z3native.mk_ite(nCtx, t1.x#gno, t2.x#gno, t3.x#gno));
   }

(**
   Create an expression representing <c>t1 iff t2</c>.
*)
   public BoolExpr MkIff(BoolExpr t1, BoolExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_iff(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create an expression representing <c>t1 -> t2</c>.
*)
   public BoolExpr MkImplies(BoolExpr t1, BoolExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_implies(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create an expression representing <c>t1 xor t2</c>.
*)
   public BoolExpr MkXor(BoolExpr t1, BoolExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_xor(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create an expression representing <c>t[0] and t[1] and ...</c>.
*)
   public BoolExpr MkAnd(params BoolExpr[] t)
   {




   CheckContextMatch(t);
   return new BoolExpr(this, Z3native.mk_and(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
   }

(**
   Create an expression representing <c>t[0] or t[1] or ...</c>.
*)
   public BoolExpr MkOr(params BoolExpr[] t)
   {




   CheckContextMatch(t);
   return new BoolExpr(this, Z3native.mk_or(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
   }
   

(* ARITHMETIC *)
(**
   Create an expression representing <c>t[0] + t[1] + ...</c>.
*)    
   public ArithExpr MkAdd(params ArithExpr[] t)
   {




   CheckContextMatch(t);
   return (ArithExpr)Expr.Create(this, Z3native.mk_add(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
   }

(**
   Create an expression representing <c>t[0] * t[1] * ...</c>.
*)    
   public ArithExpr MkMul(params ArithExpr[] t)
   {




   CheckContextMatch(t);
   return (ArithExpr)Expr.Create(this, Z3native.mk_mul(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
   }

(**
   Create an expression representing <c>t[0] - t[1] - ...</c>.
*)    
   public ArithExpr MkSub(params ArithExpr[] t)
   {




   CheckContextMatch(t);
   return (ArithExpr)Expr.Create(this, Z3native.mk_sub(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
   }

(**
   Create an expression representing <c>-t</c>.
*)    
   let mk_Unary_Minus(ArithExpr t)
   {



   CheckContextMatch(t);
   return (ArithExpr)Expr.Create(this, Z3native.mk_unary_minus(nCtx, t.x#gno));
   }

(**
   Create an expression representing <c>t1 / t2</c>.
*)    
   public ArithExpr MkDiv(ArithExpr t1, ArithExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return (ArithExpr)Expr.Create(this, Z3native.mk_div(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create an expression representing <c>t1 mod t2</c>.
*)
   <remarks>The arguments must have int type.</remarks>
   public IntExpr MkMod(IntExpr t1, IntExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new IntExpr(this, Z3native.mk_mod(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create an expression representing <c>t1 rem t2</c>.
*)
   <remarks>The arguments must have int type.</remarks>
   public IntExpr MkRem(IntExpr t1, IntExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new IntExpr(this, Z3native.mk_rem(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create an expression representing <c>t1 ^ t2</c>.
*)    
   public ArithExpr MkPower(ArithExpr t1, ArithExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return (ArithExpr)Expr.Create(this, Z3native.mk_power(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create an expression representing <c>t1 &lt; t2</c>
*)    
   public BoolExpr MkLt(ArithExpr t1, ArithExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_lt(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create an expression representing <c>t1 &lt;= t2</c>
*)    
   public BoolExpr MkLe(ArithExpr t1, ArithExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_le(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create an expression representing <c>t1 &gt; t2</c>
*)    
   public BoolExpr MkGt(ArithExpr t1, ArithExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_gt(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create an expression representing <c>t1 &gt;= t2</c>
*)    
   public BoolExpr MkGe(ArithExpr t1, ArithExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_ge(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Coerce an integer to a real.
*)
   <remarks>
   There is also a converse operation exposed. It follows the semantics prescribed by the SMT-LIB standard.
   
   You can take the floor of a real by creating an auxiliary integer Term <c>k</c> and
   and asserting <c>MakeInt2Real(k) &lt;= t1 &lt; MkInt2Real(k)+1</c>.
   The argument must be of integer sort.
   </remarks>
   public RealExpr MkInt2Real(IntExpr t)
   {



   CheckContextMatch(t);
   return new RealExpr(this, Z3native.mk_int2real(nCtx, t.x#gno));
   }

(**
   Coerce a real to an integer.
*)
   <remarks>
   The semantics of this function follows the SMT-LIB standard for the function to_int.
   The argument must be of real sort.
   </remarks>
   public IntExpr MkReal2Int(RealExpr t)
   {



   CheckContextMatch(t);
   return new IntExpr(this, Z3native.mk_real2int(nCtx, t.x#gno));
   }

(**
   Creates an expression that checks whether a real number is an integer.
*)
   let mk_Is_Integer(RealExpr t)
   {



   CheckContextMatch(t);
   return new BoolExpr(this, Z3native.mk_is_int(nCtx, t.x#gno));
   }
   

(* BIT-VECTORS *)
(**
   Bitwise negation.
*)
   <remarks>The argument must have a bit-vector sort.</remarks>
   let mk_B_VNot(BitVecExpr t)
   {



   CheckContextMatch(t);
   return new BitVecExpr(this, Z3native.mk_bvnot(nCtx, t.x#gno));
   }

(**
   Take conjunction of bits in a vector, return vector of length 1.
*)
   <remarks>The argument must have a bit-vector sort.</remarks>
   let mk_B_VRedAND(BitVecExpr t)
   {



   CheckContextMatch(t);
   return new BitVecExpr(this, Z3native.mk_bvredand(nCtx, t.x#gno));
   }

(**
   Take disjunction of bits in a vector, return vector of length 1.
*)
   <remarks>The argument must have a bit-vector sort.</remarks>
   let mk_B_VRedOR(BitVecExpr t)
   {



   CheckContextMatch(t);
   return new BitVecExpr(this, Z3native.mk_bvredor(nCtx, t.x#gno));
   }

(**
   Bitwise conjunction.
*)
   <remarks>The arguments must have a bit-vector sort.</remarks>
   let mk_B_VAND(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvand(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Bitwise disjunction.
*)
   <remarks>The arguments must have a bit-vector sort.</remarks>
   let mk_B_VOR(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvor(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Bitwise XOR.
*)
   <remarks>The arguments must have a bit-vector sort.</remarks>
   let mk_B_VXOR(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvxor(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Bitwise NAND.
*)
   <remarks>The arguments must have a bit-vector sort.</remarks>
   let mk_B_VNAND(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvnand(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Bitwise NOR.
*)
   <remarks>The arguments must have a bit-vector sort.</remarks>
   let mk_B_VNOR(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvnor(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Bitwise XNOR.
*)
   <remarks>The arguments must have a bit-vector sort.</remarks>
   let mk_B_VXNOR(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvxnor(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Standard two's complement unary minus.
*)
   <remarks>The arguments must have a bit-vector sort.</remarks>
   let mk_B_VNeg(BitVecExpr t)
   {



   CheckContextMatch(t);
   return new BitVecExpr(this, Z3native.mk_bvneg(nCtx, t.x#gno));
   }

(**
   Two's complement addition.
*)
   <remarks>The arguments must have the same bit-vector sort.</remarks>
   let mk_B_VAdd(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvadd(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Two's complement subtraction.
*)
   <remarks>The arguments must have the same bit-vector sort.</remarks>
   let mk_B_VSub(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvsub(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Two's complement multiplication.
*)
   <remarks>The arguments must have the same bit-vector sort.</remarks>
   let mk_B_VMul(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvmul(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Unsigned division.
*)
   <remarks>
   It is defined as the floor of <c>t1/t2</c> if \c t2 is
   different from zero. If <c>t2</c> is zero, then the result
   is undefined.
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VUDiv(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvudiv(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Signed division.
*)
   <remarks>
   It is defined in the following way:
   
   - The \c floor of <c>t1/t2</c> if \c t2 is different from zero, and <c>t1*t2 >= 0</c>.
   
   - The \c ceiling of <c>t1/t2</c> if \c t2 is different from zero, and <c>t1*t2 &lt; 0</c>.
   
   If <c>t2</c> is zero, then the result is undefined.
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VSDiv(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvsdiv(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Unsigned remainder.
*)
   <remarks>
   It is defined as <c>t1 - (t1 /u t2) * t2</c>, where <c>/u</c> represents unsigned division.       
   If <c>t2</c> is zero, then the result is undefined.
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VURem(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvurem(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Signed remainder.
*)
   <remarks>
   It is defined as <c>t1 - (t1 /s t2) * t2</c>, where <c>/s</c> represents signed division.
   The most significant bit (sign) of the result is equal to the most significant bit of \c t1.
   
   If <c>t2</c> is zero, then the result is undefined.
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VSRem(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvsrem(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Two's complement signed remainder (sign follows divisor).
*)
   <remarks>
   If <c>t2</c> is zero, then the result is undefined.
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VSMod(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvsmod(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Unsigned less-than
*)
   <remarks>    
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VULT(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvult(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Two's complement signed less-than
*)
   <remarks>    
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VSLT(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvslt(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Unsigned less-than or equal to.
*)
   <remarks>    
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VULE(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvule(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Two's complement signed less-than or equal to.
*)
   <remarks>    
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VSLE(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvsle(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Unsigned greater than or equal to.
*)
   <remarks>    
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VUGE(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvuge(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Two's complement signed greater than or equal to.
*)
   <remarks>    
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VSGE(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvsge(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Unsigned greater-than.
*)
   <remarks>    
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VUGT(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvugt(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Two's complement signed greater-than.
*)
   <remarks>    
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VSGT(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvsgt(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Bit-vector concatenation.
*)
   <remarks>    
   The arguments must have a bit-vector sort.
   </remarks>
   @return 
   The result is a bit-vector of size <c>n1+n2</c>, where <c>n1</c> (<c>n2</c>) 
   is the size of <c>t1</c> (<c>t2</c>).
   
   public BitVecExpr MkConcat(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_concat(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Bit-vector extraction.
*)
   <remarks>    
   Extract the bits <paramref name="high"/> down to <paramref name="low"/> from a bitvector of
   size <c>m</c> to yield a new bitvector of size <c>n</c>, where 
   <c>n = high - low + 1</c>.
   The argument <paramref name="t"/> must have a bit-vector sort.
   </remarks>
   public BitVecExpr MkExtract(uint high, uint low, BitVecExpr t)
   {



   CheckContextMatch(t);
   return new BitVecExpr(this, Z3native.mk_extract(nCtx, high, low, t.x#gno));
   }

(**
   Bit-vector sign extension.
*)
   <remarks>    
   Sign-extends the given bit-vector to the (signed) equivalent bitvector of
   size <c>m+i</c>, where \c m is the size of the given bit-vector.
   The argument <paramref name="t"/> must have a bit-vector sort.
   </remarks>
   let mk_Sign_Ext(uint i, BitVecExpr t)
   {



   CheckContextMatch(t);
   return new BitVecExpr(this, Z3native.mk_sign_ext(nCtx, i, t.x#gno));
   }

(**
   Bit-vector zero extension.
*)
   <remarks>    
   Extend the given bit-vector with zeros to the (unsigned) equivalent
   bitvector of size <c>m+i</c>, where \c m is the size of the
   given bit-vector.
   The argument <paramref name="t"/> must have a bit-vector sort.
   </remarks>
   let mk_Zero_Ext(uint i, BitVecExpr t)
   {



   CheckContextMatch(t);
   return new BitVecExpr(this, Z3native.mk_zero_ext(nCtx, i, t.x#gno));
   }

(**
   Bit-vector repetition.
*)    
   <remarks>
   The argument <paramref name="t"/> must have a bit-vector sort.
   </remarks>
   public BitVecExpr MkRepeat(uint i, BitVecExpr t)
   {



   CheckContextMatch(t);
   return new BitVecExpr(this, Z3native.mk_repeat(nCtx, i, t.x#gno));
   }

(**
   Shift left.
*)
   <remarks>
   It is equivalent to multiplication by <c>2^x</c> where \c x is the value of <paramref name="t2"/>.
   
   NB. The semantics of shift operations varies between environments. This 
   definition does not necessarily capture directly the semantics of the 
   programming language or assembly architecture you are modeling.
   
   The arguments must have a bit-vector sort.
   </remarks>
   let mk_B_VSHL(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvshl(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Logical shift right
*)
   <remarks>
   It is equivalent to unsigned division by <c>2^x</c> where \c x is the value of <paramref name="t2"/>.
   
   NB. The semantics of shift operations varies between environments. This 
   definition does not necessarily capture directly the semantics of the 
   programming language or assembly architecture you are modeling.
   
   The arguments must have a bit-vector sort.
   </remarks>
   let mk_B_VLSHR(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvlshr(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Arithmetic shift right
*)
   <remarks>
   It is like logical shift right except that the most significant
   bits of the result always copy the most significant bit of the
   second argument.
   
   NB. The semantics of shift operations varies between environments. This 
   definition does not necessarily capture directly the semantics of the 
   programming language or assembly architecture you are modeling.
   
   The arguments must have a bit-vector sort.
   </remarks>
   let mk_B_VASHR(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_bvashr(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Rotate Left.
*)
   <remarks>
   Rotate bits of \c t to the left \c i times.
   The argument <paramref name="t"/> must have a bit-vector sort.
   </remarks>
   let mk_B_VRotateLeft(uint i, BitVecExpr t)
   {



   CheckContextMatch(t);
   return new BitVecExpr(this, Z3native.mk_rotate_left(nCtx, i, t.x#gno));
   }

(**
   Rotate Right.
*)
   <remarks>
   Rotate bits of \c t to the right \c i times.
   The argument <paramref name="t"/> must have a bit-vector sort.
   </remarks>
   let mk_B_VRotateRight(uint i, BitVecExpr t)
   {



   CheckContextMatch(t);
   return new BitVecExpr(this, Z3native.mk_rotate_right(nCtx, i, t.x#gno));
   }

(**
   Rotate Left.
*)
   <remarks>
   Rotate bits of <paramref name="t1"/> to the left <paramref name="t2"/> times.
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VRotateLeft(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_ext_rotate_left(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Rotate Right.
*)
   <remarks>
   Rotate bits of <paramref name="t1"/> to the right<paramref name="t2"/> times.
   The arguments must have the same bit-vector sort.
   </remarks>
   let mk_B_VRotateRight(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BitVecExpr(this, Z3native.mk_ext_rotate_right(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create an <paramref name="n"/> bit bit-vector from the integer argument <paramref name="t"/>.
*)
   <remarks>
   NB. This function is essentially treated as uninterpreted. 
   So you cannot expect Z3 to precisely reflect the semantics of this function
   when solving constraints with this function.
   
   The argument must be of integer sort.
   </remarks>
   public BitVecExpr MkInt2BV(uint n, IntExpr t)
   {



   CheckContextMatch(t);
   return new BitVecExpr(this, Z3native.mk_int2bv(nCtx, n, t.x#gno));
   }

(**
   Create an integer from the bit-vector argument <paramref name="t"/>.
*)
   <remarks>
   If \c is_signed is false, then the bit-vector \c t1 is treated as unsigned. 
   So the result is non-negative and in the range <c>[0..2^N-1]</c>, where 
   N are the number of bits in <paramref name="t"/>.
   If \c is_signed is true, \c t1 is treated as a signed bit-vector.
   
   NB. This function is essentially treated as uninterpreted. 
   So you cannot expect Z3 to precisely reflect the semantics of this function
   when solving constraints with this function.
   
   The argument must be of bit-vector sort.
   </remarks>
   let mk_B_V2Int(BitVecExpr t, bool signed)
   {



   CheckContextMatch(t);
   return new IntExpr(this, Z3native.mk_bv2int(nCtx, t.x#gno, (signed) ? 1 : 0));
   }

(**
   Create a predicate that checks that the bit-wise addition does not overflow.
*)
   <remarks>
   The arguments must be of bit-vector sort.
   </remarks>
   let mk_B_VAddNoOverflow(BitVecExpr t1, BitVecExpr t2, bool isSigned)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvadd_no_overflow(nCtx, t1.x#gno, t2.x#gno, (isSigned) ? 1 : 0));
   }

(**
   Create a predicate that checks that the bit-wise addition does not underflow.
*)
   <remarks>
   The arguments must be of bit-vector sort.
   </remarks>
   let mk_B_VAddNoUnderflow(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvadd_no_underflow(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create a predicate that checks that the bit-wise subtraction does not overflow.
*)
   <remarks>
   The arguments must be of bit-vector sort.
   </remarks>
   let mk_B_VSubNoOverflow(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvsub_no_overflow(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create a predicate that checks that the bit-wise subtraction does not underflow.
*)
   <remarks>
   The arguments must be of bit-vector sort.
   </remarks>
   let mk_B_VSubNoUnderflow(BitVecExpr t1, BitVecExpr t2, bool isSigned)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvsub_no_underflow(nCtx, t1.x#gno, t2.x#gno, (isSigned) ? 1 : 0));
   }

(**
   Create a predicate that checks that the bit-wise signed division does not overflow.
*)
   <remarks>
   The arguments must be of bit-vector sort.
   </remarks>
   let mk_B_VSDivNoOverflow(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvsdiv_no_overflow(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create a predicate that checks that the bit-wise negation does not overflow.
*)
   <remarks>
   The arguments must be of bit-vector sort.
   </remarks>
   let mk_B_VNegNoOverflow(BitVecExpr t)
   {



   CheckContextMatch(t);
   return new BoolExpr(this, Z3native.mk_bvneg_no_overflow(nCtx, t.x#gno));
   }

(**
   Create a predicate that checks that the bit-wise multiplication does not overflow.
*)
   <remarks>
   The arguments must be of bit-vector sort.
   </remarks>
   let mk_B_VMulNoOverflow(BitVecExpr t1, BitVecExpr t2, bool isSigned)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvmul_no_overflow(nCtx, t1.x#gno, t2.x#gno, (isSigned) ? 1 : 0));
   }

(**
   Create a predicate that checks that the bit-wise multiplication does not underflow.
*)
   <remarks>
   The arguments must be of bit-vector sort.
   </remarks>
   let mk_B_VMulNoUnderflow(BitVecExpr t1, BitVecExpr t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new BoolExpr(this, Z3native.mk_bvmul_no_underflow(nCtx, t1.x#gno, t2.x#gno));
   }
   

(* ARRAYS *)
(**
   Create an array constant.
*)        
   let mk_Array_Const(Symbol name, Sort domain, Sort range)
   {





   return (ArrayExpr)MkConst(name, MkArraySort(domain, range));
   }

(**
   Create an array constant.
*)        
   let mk_Array_Const(string name, Sort domain, Sort range)
   {




   return (ArrayExpr)MkConst(MkSymbol(name), MkArraySort(domain, range));
   }

(**
   Array read.       
*)
   <remarks>
   The argument <c>a</c> is the array and <c>i</c> is the index 
   of the array that gets read.      
   
   The node <c>a</c> must have an array sort <c>[domain -> range]</c>, 
   and <c>i</c> must have the sort <c>domain</c>.
   The sort of the result is <c>range</c>.
   <seealso cref="MkArraySort"/>
   <seealso cref="MkStore"/>
   </remarks>
   public Expr MkSelect(ArrayExpr a, Expr i)
   {




   CheckContextMatch(a);
   CheckContextMatch(i);
   return Expr.Create(this, Z3native.mk_select(nCtx, a.x#gno, i.x#gno));
   }

(**
   Array update.       
*)
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
   </remarks>
   public ArrayExpr MkStore(ArrayExpr a, Expr i, Expr v)
   {





   CheckContextMatch(a);
   CheckContextMatch(i);
   CheckContextMatch(v);
   return new ArrayExpr(this, Z3native.mk_store(nCtx, a.x#gno, i.x#gno, v.x#gno));
   }

(**
   Create a constant array.
*)
   <remarks>
   The resulting term is an array, such that a <c>select</c>on an arbitrary index 
   produces the value <c>v</c>.
   <seealso cref="MkArraySort"/>
   <seealso cref="MkSelect"/>
   </remarks>
   let mk_Const_Array(Sort domain, Expr v)
   {




   CheckContextMatch(domain);
   CheckContextMatch(v);
   return new ArrayExpr(this, Z3native.mk_const_array(nCtx, domain.x#gno, v.x#gno));
   }

(**
   Maps f on the argument arrays.
*)
   <remarks>
   Eeach element of <c>args</c> must be of an array sort <c>[domain_i -> range_i]</c>.
   The function declaration <c>f</c> must have type <c> range_1 .. range_n -> range</c>.
   <c>v</c> must have sort range. The sort of the result is <c>[domain_i -> range]</c>.
   <seealso cref="MkArraySort"/>
   <seealso cref="MkSelect"/>
   <seealso cref="MkStore"/>
   </remarks>
   public ArrayExpr MkMap(Func_Decl f, params ArrayExpr[] args)
   {




   CheckContextMatch(f);
   CheckContextMatch(args);
   return (ArrayExpr)Expr.Create(this, Z3native.mk_map(nCtx, f.x#gno, AST.ArrayLength(args), AST.ArrayToNative(args)));
   }

(**
   Access the array default value.
*)
   <remarks>
   Produces the default range value, for arrays that can be represented as 
   finite maps with a default range value.    
   </remarks>
   let mk_Term_Array(ArrayExpr array)
   {



   CheckContextMatch(array);
   return Expr.Create(this, Z3native.mk_array_default(nCtx, array.x#gno));
   }
   

(* SETS *)
(**
   Create a set type.
*)
   let mk_Set_Sort(Sort ty)
   {



   CheckContextMatch(ty);
   return new SetSort(this, ty);
   }

(**
   Create an empty set.
*)
   let mk_Empty_Set(Sort domain)
   {



   CheckContextMatch(domain);
   return Expr.Create(this, Z3native.mk_empty_set(nCtx, domain.x#gno));
   }

(**
   Create the full set.
*)
   let mk_Full_Set(Sort domain)
   {



   CheckContextMatch(domain);
   return Expr.Create(this, Z3native.mk_full_set(nCtx, domain.x#gno));
   }

(**
   Add an element to the set.
*)
   let mk_Set_Add(Expr set, Expr element)
   {




   CheckContextMatch(set);
   CheckContextMatch(element);
   return Expr.Create(this, Z3native.mk_set_add(nCtx, set.x#gno, element.x#gno));
   }


(**
   Remove an element from a set.
*)
   let mk_Set_Del(Expr set, Expr element)
   {




   CheckContextMatch(set);
   CheckContextMatch(element);
   return Expr.Create(this, Z3native.mk_set_del(nCtx, set.x#gno, element.x#gno));
   }

(**
   Take the union of a list of sets.
*)
   let mk_Set_Union(params Expr[] args)
   {



   CheckContextMatch(args);
   return Expr.Create(this, Z3native.mk_set_union(nCtx, (uint)args.Length, AST.ArrayToNative(args)));
   }

(**
   Take the intersection of a list of sets.
*)
   let mk_Set_Intersection(params Expr[] args)
   {




   CheckContextMatch(args);
   return Expr.Create(this, Z3native.mk_set_intersect(nCtx, (uint)args.Length, AST.ArrayToNative(args)));
   }

(**
   Take the difference between two sets.
*)
   let mk_Set_Difference(Expr arg1, Expr arg2)
   {




   CheckContextMatch(arg1);
   CheckContextMatch(arg2);
   return Expr.Create(this, Z3native.mk_set_difference(nCtx, arg1.x#gno, arg2.x#gno));
   }

(**
   Take the complement of a set.
*)
   let mk_Set_Complement(Expr arg)
   {



   CheckContextMatch(arg);
   return Expr.Create(this, Z3native.mk_set_complement(nCtx, arg.x#gno));
   }

(**
   Check for set membership.
*)
   let mk_Set_Membership(Expr elem, Expr set)
   {




   CheckContextMatch(elem);
   CheckContextMatch(set);
   return Expr.Create(this, Z3native.mk_set_member(nCtx, elem.x#gno, set.x#gno));
   }

(**
   Check for subsetness of sets.
*)
   let mk_Set_Subset(Expr arg1, Expr arg2)
   {




   CheckContextMatch(arg1);
   CheckContextMatch(arg2);
   return Expr.Create(this, Z3native.mk_set_subset(nCtx, arg1.x#gno, arg2.x#gno));
   }
   

(* NUMERALS *)

(* GENERAL NUMERALS *)
(**
   Create a Term of a given sort.         
*)
   @param v A string representing the Term value in decimal notation. If the given sort is a real, then the Term can be a rational, that is, a string of the form <c>[num]* / [num]*</c>.
   @param ty The sort of the numeral. In the current implementation, the given sort can be an int, real, or bit-vectors of arbitrary size. 
   @return A Term with value <paramref name="v"/> and sort <paramref name="ty"/> 
   public Expr MkNumeral(string v, Sort ty)
   {



   CheckContextMatch(ty);
   return Expr.Create(this, Z3native.mk_numeral(nCtx, v, ty.x#gno));
   }

(**
   Create a Term of a given sort. This function can be use to create numerals that fit in a machine integer.
   It is slightly faster than <c>MakeNumeral</c> since it is not necessary to parse a string.       
*)
   @param v Value of the numeral
   @param ty Sort of the numeral
   @return A Term with value <paramref name="v"/> and type <paramref name="ty"/>
   public Expr MkNumeral(int v, Sort ty)
   {



   CheckContextMatch(ty);
   return Expr.Create(this, Z3native.mk_int(nCtx, v, ty.x#gno));
   }

(**
   Create a Term of a given sort. This function can be use to create numerals that fit in a machine integer.
   It is slightly faster than <c>MakeNumeral</c> since it is not necessary to parse a string.       
*)
   @param v Value of the numeral
   @param ty Sort of the numeral
   @return A Term with value <paramref name="v"/> and type <paramref name="ty"/>
   public Expr MkNumeral(uint v, Sort ty)
   {



   CheckContextMatch(ty);
   return Expr.Create(this, Z3native.mk_unsigned_int(nCtx, v, ty.x#gno));
   }

(**
   Create a Term of a given sort. This function can be use to create numerals that fit in a machine integer.
   It is slightly faster than <c>MakeNumeral</c> since it is not necessary to parse a string.       
*)
   @param v Value of the numeral
   @param ty Sort of the numeral
   @return A Term with value <paramref name="v"/> and type <paramref name="ty"/>
   public Expr MkNumeral(long v, Sort ty)
   {



   CheckContextMatch(ty);
   return Expr.Create(this, Z3native.mk_int64(nCtx, v, ty.x#gno));
   }

(**
   Create a Term of a given sort. This function can be use to create numerals that fit in a machine integer.
   It is slightly faster than <c>MakeNumeral</c> since it is not necessary to parse a string.       
*)
   @param v Value of the numeral
   @param ty Sort of the numeral
   @return A Term with value <paramref name="v"/> and type <paramref name="ty"/>
   public Expr MkNumeral(ulong v, Sort ty)
   {



   CheckContextMatch(ty);
   return Expr.Create(this, Z3native.mk_unsigned_int64(nCtx, v, ty.x#gno));
   }
   

(* REALS *)
(**
   Create a real from a fraction.
*)
   @param num numerator of rational.
   @param den denominator of rational.
   @return A Term with value <paramref name="num"/>/<paramref name="den"/> and sort Real
   <seealso cref="MkNumeral(string, Sort)"/>
   public RatNum MkReal(int num, int den)
   {
   if (den == 0)
   throw new Z3Exception("Denominator is zero");




   return new RatNum(this, Z3native.mk_real(nCtx, num, den));
   }

(**
   Create a real numeral.
*)
   @param v A string representing the Term value in decimal notation.
   @return A Term with value <paramref name="v"/> and sort Real
   public RatNum MkReal(string v)
   {


   return new RatNum(this, Z3native.mk_numeral(nCtx, v, RealSort.x#gno));
   }

(**
   Create a real numeral.
*)
   @param v value of the numeral.    
   @return A Term with value <paramref name="v"/> and sort Real
   public RatNum MkReal(int v)
   {


   return new RatNum(this, Z3native.mk_int(nCtx, v, RealSort.x#gno));
   }

(**
   Create a real numeral.
*)
   @param v value of the numeral.    
   @return A Term with value <paramref name="v"/> and sort Real
   public RatNum MkReal(uint v)
   {


   return new RatNum(this, Z3native.mk_unsigned_int(nCtx, v, RealSort.x#gno));
   }

(**
   Create a real numeral.
*)
   @param v value of the numeral.    
   @return A Term with value <paramref name="v"/> and sort Real
   public RatNum MkReal(long v)
   {


   return new RatNum(this, Z3native.mk_int64(nCtx, v, RealSort.x#gno));
   }

(**
   Create a real numeral.
*)
   @param v value of the numeral.    
   @return A Term with value <paramref name="v"/> and sort Real
   public RatNum MkReal(ulong v)
   {


   return new RatNum(this, Z3native.mk_unsigned_int64(nCtx, v, RealSort.x#gno));
   }
   

(* INTEGERS *)
(**
   Create an integer numeral.
*)
   @param v A string representing the Term value in decimal notation.
   public IntNum MkInt(string v)
   {


   return new IntNum(this, Z3native.mk_numeral(nCtx, v, IntSort.x#gno));
   }

(**
   Create an integer numeral.
*)
   @param v value of the numeral.    
   @return A Term with value <paramref name="v"/> and sort Integer
   public IntNum MkInt(int v)
   {


   return new IntNum(this, Z3native.mk_int(nCtx, v, IntSort.x#gno));
   }

(**
   Create an integer numeral.
*)
   @param v value of the numeral.    
   @return A Term with value <paramref name="v"/> and sort Integer
   public IntNum MkInt(uint v)
   {


   return new IntNum(this, Z3native.mk_unsigned_int(nCtx, v, IntSort.x#gno));
   }

(**
   Create an integer numeral.
*)
   @param v value of the numeral.    
   @return A Term with value <paramref name="v"/> and sort Integer
   public IntNum MkInt(long v)
   {


   return new IntNum(this, Z3native.mk_int64(nCtx, v, IntSort.x#gno));
   }

(**
   Create an integer numeral.
*)
   @param v value of the numeral.    
   @return A Term with value <paramref name="v"/> and sort Integer
   public IntNum MkInt(ulong v)
   {


   return new IntNum(this, Z3native.mk_unsigned_int64(nCtx, v, IntSort.x#gno));
   }
   

(* BIT-VECTORS *)
(**
   Create a bit-vector numeral.
*)
   @param v A string representing the value in decimal notation.
   @param size the size of the bit-vector
   let mk_B_V(string v, uint size)
   {


   return (BitVecNum)MkNumeral(v, MkBitVecSort(size));
   }

(**
   Create a bit-vector numeral.
*)
   @param v value of the numeral.    
   @param size the size of the bit-vector
   let mk_B_V(int v, uint size)
   {


   return (BitVecNum)MkNumeral(v, MkBitVecSort(size));
   }

(**
   Create a bit-vector numeral.
*)
   @param v value of the numeral.    
   @param size the size of the bit-vector
   let mk_B_V(uint v, uint size)
   {


   return (BitVecNum)MkNumeral(v, MkBitVecSort(size));
   }

(**
   Create a bit-vector numeral.
*)
   @param v value of the numeral.
   @param size the size of the bit-vector
   let mk_B_V(long v, uint size)
   {


   return (BitVecNum)MkNumeral(v, MkBitVecSort(size));
   }

(**
   Create a bit-vector numeral.
*)
   @param v value of the numeral.
   @param size the size of the bit-vector
   let mk_B_V(ulong v, uint size)
   {


   return (BitVecNum)MkNumeral(v, MkBitVecSort(size));
   }
   

   // Numerals

(* QUANTIFIERS *)
(**
   Create a universal Quantifier.
*)
   <remarks>
   Creates a forall formula, where <paramref name="weight"/> is the weight, 
   <paramref name="patterns"/> is an array of patterns, <paramref name="sorts"/> is an array
   with the sorts of the bound variables, <paramref name="names"/> is an array with the
   'names' of the bound variables, and <paramref name="body"/> is the body of the
   quantifier. Quantifiers are associated with weights indicating
   the importance of using the quantifier during instantiation. 
   </remarks>
   @param sorts the sorts of the bound variables.
   @param names names of the bound variables
   @param body the body of the quantifier.
   @param weight quantifiers are associated with weights indicating the importance of using the quantifier during instantiation. By default, pass the weight 0.
   @param patterns array containing the patterns created using <c>MkPattern</c>.
   @param noPatterns array containing the anti-patterns created using <c>MkPattern</c>.
   @param quantifierID optional symbol to track quantifier.
   @param skolemID optional symbol to track skolem constants.
   public Quantifier MkForall(Sort[] sorts, Symbol[] names, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
   {











   return new Quantifier(this, true, sorts, names, body, weight, patterns, noPatterns, quantifierID, skolemID);
   }


(**
   Create a universal Quantifier.
*)
   public Quantifier MkForall(Expr[] boundConstants, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
   {







   return new Quantifier(this, true, boundConstants, body, weight, patterns, noPatterns, quantifierID, skolemID);
   }

(**
   Create an existential Quantifier.
*)
   <seealso cref="MkForall(Sort[],Symbol[],Expr,uint,Pattern[],Expr[],Symbol,Symbol)"/>
   public Quantifier MkExists(Sort[] sorts, Symbol[] names, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
   {










   return new Quantifier(this, false, sorts, names, body, weight, patterns, noPatterns, quantifierID, skolemID);
   }

(**
   Create an existential Quantifier.
*)
   public Quantifier MkExists(Expr[] boundConstants, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
   {






   return new Quantifier(this, false, boundConstants, body, weight, patterns, noPatterns, quantifierID, skolemID);
   }


(**
   Create a Quantifier.
*)
   public Quantifier MkQuantifier(bool universal, Sort[] sorts, Symbol[] names, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
   {











   if (universal)
   return MkForall(sorts, names, body, weight, patterns, noPatterns, quantifierID, skolemID);
   else
   return MkExists(sorts, names, body, weight, patterns, noPatterns, quantifierID, skolemID);
   }


(**
   Create a Quantifier.
*)
   public Quantifier MkQuantifier(bool universal, Expr[] boundConstants, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
   {







   if (universal)
   return MkForall(boundConstants, body, weight, patterns, noPatterns, quantifierID, skolemID);
   else
   return MkExists(boundConstants, body, weight, patterns, noPatterns, quantifierID, skolemID);
   }

   

   // Expr

(* OPTIONS *)

(**
   Selects the format used for pretty-printing expressions.
*)
   <remarks>
   The default mode for pretty printing expressions is to produce
   SMT-LIB style output where common subexpressions are printed 
   at each occurrence. The mode is called Z3_PRINT_SMTLIB_FULL.
   To print shared common subexpressions only once, 
   use the Z3_PRINT_LOW_LEVEL mode.
   To print in way that conforms to SMT-LIB standards and uses let
   expressions to share common sub-expressions use Z3_PRINT_SMTLIB_COMPLIANT.
   </remarks>
   <seealso cref="AST.ToString ( ctx : context ) ="/>
   <seealso cref="Pattern.ToString ( ctx : context ) ="/>
   <seealso cref="FuncDecl.ToString ( ctx : context ) ="/>
   <seealso cref="Sort.ToString ( ctx : context ) ="/>
   public Z3_ast_print_mode PrintMode
   {
   set { Z3native.set_ast_print_mode(nCtx, (uint)value); }
   }
   

(* SMT Files & Strings *)
(**
   Convert a benchmark into an SMT-LIB formatted string.
*)
   @param name Name of the benchmark. The argument is optional.
   @param logic The benchmark logic. 
   @param status The status string (sat, unsat, or unknown)
   @param attributes Other attributes, such as source, difficulty or category.
   @param assumptions Auxiliary assumptions.
   @param formula Formula to be checked for consistency in conjunction with assumptions.
   @return A string representation of the benchmark.
   public string BenchmarkToSMTString(string name, string logic, string status, string attributes,
   BoolExpr[] assumptions, BoolExpr formula)
   {




   return Z3native.benchmark_to_smtlib_string(nCtx, name, logic, status, attributes,
   (uint)assumptions.Length, AST.ArrayToNative(assumptions),
   formula.x#gno);
   }

(**
   Parse the given string using the SMT-LIB parser. 
*)
   <remarks>
   The symbol table of the parser can be initialized using the given sorts and declarations. 
   The symbols in the arrays <paramref name="sortNames"/> and <paramref name="declNames"/> 
   don't need to match the names of the sorts and declarations in the arrays <paramref name="sorts"/> 
   and <paramref name="decls"/>. This is a useful feature since we can use arbitrary names to 
   reference sorts and declarations.
   </remarks>
   public void ParseSMTLIBString(string str, Symbol[] sortNames = null, Sort[] sorts = null, Symbol[] declNames = null, Func_Decl[] decls = null)
   {
   uint csn = Symbol.ArrayLength(sortNames);
   uint cs = Sort.ArrayLength(sorts);
   uint cdn = Symbol.ArrayLength(declNames);
   uint cd = AST.ArrayLength(decls);
   if (csn != cs || cdn != cd)
   throw new Z3Exception("Argument size mismatch");
   Z3native.parse_smtlib_string(nCtx, str,
   AST.ArrayLength(sorts), Symbol.ArrayToNative(sortNames), AST.ArrayToNative(sorts),
   AST.ArrayLength(decls), Symbol.ArrayToNative(declNames), AST.ArrayToNative(decls));
   }

(**
   Parse the given file using the SMT-LIB parser. 
*)
   <seealso cref="ParseSMTLIBString"/>
   public void ParseSMTLIBFile(string fileName, Symbol[] sortNames = null, Sort[] sorts = null, Symbol[] declNames = null, Func_Decl[] decls = null)
   {
   uint csn = Symbol.ArrayLength(sortNames);
   uint cs = Sort.ArrayLength(sorts);
   uint cdn = Symbol.ArrayLength(declNames);
   uint cd = AST.ArrayLength(decls);
   if (csn != cs || cdn != cd)
   throw new Z3Exception("Argument size mismatch");
   Z3native.parse_smtlib_file(nCtx, fileName,
   AST.ArrayLength(sorts), Symbol.ArrayToNative(sortNames), AST.ArrayToNative(sorts),
   AST.ArrayLength(decls), Symbol.ArrayToNative(declNames), AST.ArrayToNative(decls));
   }

(**
   The number of SMTLIB formulas parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
*)
   public uint NumSMTLIBFormulas { get { return Z3native.get_smtlib_num_formulas(nCtx))

(**
   The formulas parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
*)
   public BoolExpr[] SMTLIBFormulas
   {
   get
   {


   uint n = NumSMTLIBFormulas;
   BoolExpr[] res = new BoolExpr[n];
   for (uint i = 0; i < n; i++)
   res[i] = (BoolExpr)Expr.Create(this, Z3native.get_smtlib_formula(nCtx, i));
   return res;
   }
   }

(**
   The number of SMTLIB assumptions parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
*)
   public uint NumSMTLIBAssumptions { get { return Z3native.get_smtlib_num_assumptions(nCtx))

(**
   The assumptions parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
*)
   public BoolExpr[] SMTLIBAssumptions
   {
   get
   {


   uint n = NumSMTLIBAssumptions;
   BoolExpr[] res = new BoolExpr[n];
   for (uint i = 0; i < n; i++)
   res[i] = (BoolExpr)Expr.Create(this, Z3native.get_smtlib_assumption(nCtx, i));
   return res;
   }
   }

(**
   The number of SMTLIB declarations parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
*)
   public uint NumSMTLIBDecls { get { return Z3native.get_smtlib_num_decls(nCtx))

(**
   The declarations parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
*)
   public Func_Decl[] SMTLIBDecls
   {
   get
   {


   uint n = NumSMTLIBDecls;
   Func_Decl[] res = new Func_Decl[n];
   for (uint i = 0; i < n; i++)
   res[i] = new Func_Decl(this, Z3native.get_smtlib_decl(nCtx, i));
   return res;
   }
   }

(**
   The number of SMTLIB sorts parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
*)
   public uint NumSMTLIBSorts { get { return Z3native.get_smtlib_num_sorts(nCtx))

(**
   The declarations parsed by the last call to <c>ParseSMTLIBString</c> or <c>ParseSMTLIBFile</c>.
*)
   public Sort[] SMTLIBSorts
   {
   get
   {


   uint n = NumSMTLIBSorts;
   Sort[] res = new Sort[n];
   for (uint i = 0; i < n; i++)
   res[i] = Sort.Create(this, Z3native.get_smtlib_sort(nCtx, i));
   return res;
   }
   }

(**
   Parse the given string using the SMT-LIB2 parser. 
*)
   <seealso cref="ParseSMTLIBString"/>
   @return A conjunction of assertions in the scope (up to push/pop) at the end of the string.
   public BoolExpr ParseSMTLIB2String(string str, Symbol[] sortNames = null, Sort[] sorts = null, Symbol[] declNames = null, Func_Decl[] decls = null)
   {


   uint csn = Symbol.ArrayLength(sortNames);
   uint cs = Sort.ArrayLength(sorts);
   uint cdn = Symbol.ArrayLength(declNames);
   uint cd = AST.ArrayLength(decls);
   if (csn != cs || cdn != cd)
   throw new Z3Exception("Argument size mismatch");
   return (BoolExpr)Expr.Create(this, Z3native.parse_smtlib2_string(nCtx, str,
   AST.ArrayLength(sorts), Symbol.ArrayToNative(sortNames), AST.ArrayToNative(sorts),
   AST.ArrayLength(decls), Symbol.ArrayToNative(declNames), AST.ArrayToNative(decls)));
   }

(**
   Parse the given file using the SMT-LIB2 parser. 
*)
   <seealso cref="ParseSMTLIB2String"/>
   public BoolExpr ParseSMTLIB2File(string fileName, Symbol[] sortNames = null, Sort[] sorts = null, Symbol[] declNames = null, Func_Decl[] decls = null)
   {


   uint csn = Symbol.ArrayLength(sortNames);
   uint cs = Sort.ArrayLength(sorts);
   uint cdn = Symbol.ArrayLength(declNames);
   uint cd = AST.ArrayLength(decls);
   if (csn != cs || cdn != cd)
   throw new Z3Exception("Argument size mismatch");
   return (BoolExpr)Expr.Create(this, Z3native.parse_smtlib2_file(nCtx, fileName,
   AST.ArrayLength(sorts), Symbol.ArrayToNative(sortNames), AST.ArrayToNative(sorts),
   AST.ArrayLength(decls), Symbol.ArrayToNative(declNames), AST.ArrayToNative(decls)));
   }
   

(* GOALS *)
(**
   Creates a new Goal.
*)
   <remarks>
   Note that the Context must have been created with proof generation support if 
   <paramref name="proofs"/> is set to true here.
   </remarks>
   @param models Indicates whether model generation should be enabled.
   @param unsatCores Indicates whether unsat core generation should be enabled.
   @param proofs Indicates whether proof generation should be enabled.    
   public Goal MkGoal(bool models = true, bool unsatCores = false, bool proofs = false)
   {


   return new Goal(this, models, unsatCores, proofs);
   }
   

(* PARAMETERSETS *)
(**
   Creates a new ParameterSet.
*)
   public Params MkParams ( ctx : context ) =
   {


   return new Params(this);
   }
   

(* TACTICS *)
(**
   The number of supported tactics.
*)
   public uint NumTactics
   {
   get { return Z3native.get_num_tactics(nCtx); }
   }

(**
   The names of all supported tactics.
*)
   public string[] TacticNames
   {
   get
   {


   uint n = NumTactics;
   string[] res = new string[n];
   for (uint i = 0; i < n; i++)
   res[i] = Z3native.get_tactic_name(nCtx, i);
   return res;
   }
   }

(**
   Returns a string containing a description of the tactic with the given name.
*)
   public string TacticDescription(string name)
   {


   return Z3native.tactic_get_descr(nCtx, name);
   }

(**
   Creates a new Tactic.
*)    
   public Tactic MkTactic(string name)
   {


   return new Tactic(this, name);
   }

(**
   Create a tactic that applies <paramref name="t1"/> to a Goal and
   then <paramref name="t2"/> to every subgoal produced by <paramref name="t1"/>.
*)
   public Tactic AndThen(Tactic t1, Tactic t2, params Tactic[] ts)
   {






   CheckContextMatch(t1);
   CheckContextMatch(t2);
   CheckContextMatch(ts);

   IntPtr last = IntPtr.Zero;
   if (ts != null && ts.Length > 0)
   {
   last = ts[ts.Length - 1].x#gno;
   for (int i = ts.Length - 2; i >= 0; i--)
   last = Z3native.tactic_and_then(nCtx, ts[i].x#gno, last);
   }
   if (last != IntPtr.Zero)
   {
   last = Z3native.tactic_and_then(nCtx, t2.x#gno, last);
   return new Tactic(this, Z3native.tactic_and_then(nCtx, t1.x#gno, last));
   }
   else
   return new Tactic(this, Z3native.tactic_and_then(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create a tactic that applies <paramref name="t1"/> to a Goal and
   then <paramref name="t2"/> to every subgoal produced by <paramref name="t1"/>.        
*)
   <remarks>
   Shorthand for <c>AndThen</c>.
   </remarks>
   public Tactic Then(Tactic t1, Tactic t2, params Tactic[] ts)
   {





   return AndThen(t1, t2, ts);
   }

(**
   Create a tactic that first applies <paramref name="t1"/> to a Goal and
   if it fails then returns the result of <paramref name="t2"/> applied to the Goal.
*)
   public Tactic OrElse(Tactic t1, Tactic t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new Tactic(this, Z3native.tactic_or_else(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Create a tactic that applies <paramref name="t"/> to a goal for <paramref name="ms"/> milliseconds.    
*)
   <remarks>
   If <paramref name="t"/> does not terminate within <paramref name="ms"/> milliseconds, then it fails.
   </remarks>
   public Tactic TryFor(Tactic t, uint ms)
   {



   CheckContextMatch(t);
   return new Tactic(this, Z3native.tactic_try_for(nCtx, t.x#gno, ms));
   }

(**
   Create a tactic that applies <paramref name="t"/> to a given goal if the probe 
   <paramref name="p"/> evaluates to true. 
*)
   <remarks>
   If <paramref name="p"/> evaluates to false, then the new tactic behaves like the <c>skip</c> tactic. 
   </remarks>
   public Tactic When(Probe p, Tactic t)
   {




   CheckContextMatch(t);
   CheckContextMatch(p);
   return new Tactic(this, Z3native.tactic_when(nCtx, p.x#gno, t.x#gno));
   }

(**
   Create a tactic that applies <paramref name="t1"/> to a given goal if the probe 
   <paramref name="p"/> evaluates to true and <paramref name="t2"/> otherwise.
*)
   public Tactic Cond(Probe p, Tactic t1, Tactic t2)
   {





   CheckContextMatch(p);
   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new Tactic(this, Z3native.tactic_cond(nCtx, p.x#gno, t1.x#gno, t2.x#gno));
   }

(**
   Create a tactic that keeps applying <paramref name="t"/> until the goal is not 
   modified anymore or the maximum number of iterations <paramref name="max"/> is reached.
*)
   public Tactic Repeat(Tactic t, uint max = uint.MaxValue)
   {



   CheckContextMatch(t);
   return new Tactic(this, Z3native.tactic_repeat(nCtx, t.x#gno, max));
   }

(**
   Create a tactic that just returns the given goal.
*)
   public Tactic Skip ( ctx : context ) =
   {


   return new Tactic(this, Z3native.tactic_skip(nCtx));
   }

(**
   Create a tactic always fails.
*)
   public Tactic Fail ( ctx : context ) =
   {


   return new Tactic(this, Z3native.tactic_fail(nCtx));
   }

(**
   Create a tactic that fails if the probe <paramref name="p"/> evaluates to false.
*)
   public Tactic FailIf(Probe p)
   {



   CheckContextMatch(p);
   return new Tactic(this, Z3native.tactic_fail_if(nCtx, p.x#gno));
   }

(**
   Create a tactic that fails if the goal is not triviall satisfiable (i.e., empty)
   or trivially unsatisfiable (i.e., contains `false').
*)
   public Tactic FailIfNotDecided ( ctx : context ) =
   {


   return new Tactic(this, Z3native.tactic_fail_if_not_decided(nCtx));
   }

(**
   Create a tactic that applies <paramref name="t"/> using the given set of parameters <paramref name="p"/>.
*)
   public Tactic UsingParams(Tactic t, Params p)
   {




   CheckContextMatch(t);
   CheckContextMatch(p);
   return new Tactic(this, Z3native.tactic_using_params(nCtx, t.x#gno, p.x#gno));
   }

(**
   Create a tactic that applies <paramref name="t"/> using the given set of parameters <paramref name="p"/>.
*)
   <remarks>Alias for <c>UsingParams</c></remarks>
   public Tactic With(Tactic t, Params p)
   {




   return UsingParams(t, p);
   }

(**
   Create a tactic that applies the given tactics in parallel.
*)
   public Tactic ParOr(params Tactic[] t)
   {



   CheckContextMatch(t);
   return new Tactic(this, Z3native.tactic_par_or(nCtx, Tactic.ArrayLength(t), Tactic.ArrayToNative(t)));
   }

(**
   Create a tactic that applies <paramref name="t1"/> to a given goal and then <paramref name="t2"/>
   to every subgoal produced by <paramref name="t1"/>. The subgoals are processed in parallel.
*)
   public Tactic ParAndThen(Tactic t1, Tactic t2)
   {




   CheckContextMatch(t1);
   CheckContextMatch(t2);
   return new Tactic(this, Z3native.tactic_par_and_then(nCtx, t1.x#gno, t2.x#gno));
   }

(**
   Interrupt the execution of a Z3 procedure.        
*)
   <remarks>This procedure can be used to interrupt: solvers, simplifiers and tactics.</remarks>
   public void Interrupt ( ctx : context ) =
   {
   Z3native.interrupt(nCtx);
   }
   

(* PROBES *)
(**
   The number of supported Probes.
*)
   public uint NumProbes
   {
   get { return Z3native.get_num_probes(nCtx); }
   }

(**
   The names of all supported Probes.
*)
   public string[] ProbeNames
   {
   get
   {


   uint n = NumProbes;
   string[] res = new string[n];
   for (uint i = 0; i < n; i++)
   res[i] = Z3native.get_probe_name(nCtx, i);
   return res;
   }
   }

(**
   Returns a string containing a description of the probe with the given name.
*)
   public string ProbeDescription(string name)
   {


   return Z3native.probe_get_descr(nCtx, name);
   }

(**
   Creates a new Probe.
*)    
   public Probe MkProbe(string name)
   {


   return new Probe(this, name);
   }

(**
   Create a probe that always evaluates to <paramref name="val"/>.
*)
   public Probe Const(double val)
   {


   return new Probe(this, Z3native.probe_const(nCtx, val));
   }

(**
   Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
   is less than the value returned by <paramref name="p2"/>
*)
   public Probe Lt(Probe p1, Probe p2)
   {




   CheckContextMatch(p1);
   CheckContextMatch(p2);
   return new Probe(this, Z3native.probe_lt(nCtx, p1.x#gno, p2.x#gno));
   }

(**
   Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
   is greater than the value returned by <paramref name="p2"/>
*)
   public Probe Gt(Probe p1, Probe p2)
   {




   CheckContextMatch(p1);
   CheckContextMatch(p2);
   return new Probe(this, Z3native.probe_gt(nCtx, p1.x#gno, p2.x#gno));
   }

(**
   Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
   is less than or equal the value returned by <paramref name="p2"/>
*)
   public Probe Le(Probe p1, Probe p2)
   {




   CheckContextMatch(p1);
   CheckContextMatch(p2);
   return new Probe(this, Z3native.probe_le(nCtx, p1.x#gno, p2.x#gno));
   }

(**
   Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
   is greater than or equal the value returned by <paramref name="p2"/>
*)
   public Probe Ge(Probe p1, Probe p2)
   {




   CheckContextMatch(p1);
   CheckContextMatch(p2);
   return new Probe(this, Z3native.probe_ge(nCtx, p1.x#gno, p2.x#gno));
   }

(**
   Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
   is equal to the value returned by <paramref name="p2"/>
*)
   public Probe Eq(Probe p1, Probe p2)
   {




   CheckContextMatch(p1);
   CheckContextMatch(p2);
   return new Probe(this, Z3native.probe_eq(nCtx, p1.x#gno, p2.x#gno));
   }

(**
   Create a probe that evaluates to "true" when the value <paramref name="p1"/>
   and <paramref name="p2"/> evaluate to "true".
*)
   public Probe And(Probe p1, Probe p2)
   {




   CheckContextMatch(p1);
   CheckContextMatch(p2);
   return new Probe(this, Z3native.probe_and(nCtx, p1.x#gno, p2.x#gno));
   }

(**
   Create a probe that evaluates to "true" when the value <paramref name="p1"/>
   or <paramref name="p2"/> evaluate to "true".
*)
   public Probe Or(Probe p1, Probe p2)
   {




   CheckContextMatch(p1);
   CheckContextMatch(p2);
   return new Probe(this, Z3native.probe_or(nCtx, p1.x#gno, p2.x#gno));
   }

(**
   Create a probe that evaluates to "true" when the value <paramref name="p"/>
   does not evaluate to "true".
*)
   public Probe Not(Probe p)
   {



   CheckContextMatch(p);
   return new Probe(this, Z3native.probe_not(nCtx, p.x#gno));
   }
   

(* SOLVERS *)
(**
   Creates a new (incremental) solver. 
*)
   <remarks>
   This solver also uses a set of builtin tactics for handling the first 
   check-sat command, and check-sat commands that take more than a given 
   number of milliseconds to be solved. 
   </remarks>    
   public Solver MkSolver(Symbol logic = null)
   {


   if (logic == null)
   return new Solver(this, Z3native.mk_solver(nCtx));
   else
   return new Solver(this, Z3native.mk_solver_for_logic(nCtx, logic.x#gno));
   }

(**
   Creates a new (incremental) solver.
*)        
   <seealso cref="MkSolver(Symbol)"/>
   public Solver MkSolver(string logic)
   {


   return MkSolver(MkSymbol(logic));
   }

(**
   Creates a new (incremental) solver. 
*)
   let mk_Simple_Solver ( ctx : context ) =
   {


   return new Solver(this, Z3native.mk_simple_solver(nCtx));
   }

(**
   Creates a solver that is implemented using the given tactic.
*)
   <remarks>
   The solver supports the commands <c>Push</c> and <c>Pop</c>, but it
   will always solve each check from scratch.
   </remarks>
   public Solver MkSolver(Tactic t)
   {



   return new Solver(this, Z3native.mk_solver_from_tactic(nCtx, t.x#gno));
   }
   

(* FIXEDPOINTS *)
(**
   Create a Fixedpoint context.
*)
   public Fixedpoint MkFixedpoint ( ctx : context ) =
   {


   return new Fixedpoint(this);
   }
   


(* MISCELLANEOUS *)
(**
   Wraps an AST.
*)
   <remarks>This function is used for transitions between native and 
   managed objects. Note that <paramref name="nativeObject"/> must be a 
   native object obtained from Z3 (e.g., through <seealso cref="UnwrapAST"/>)
   and that it must have a correct reference count (see e.g., 
   <seealso cref="Z3native.inc_ref"/>.</remarks>
   <seealso cref="UnwrapAST"/>
   @param nativeObject The native pointer to wrap.
   public AST WrapAST(IntPtr nativeObject)
   {

   return AST.Create(this, nativeObject);
   }

(**
   Unwraps an AST.
*)
   <remarks>This function is used for transitions between native and 
   managed objects. It returns the native pointer to the AST. Note that 
   AST objects are reference counted and unwrapping an AST disables automatic
   reference counting, i.e., all references to the IntPtr that is returned 
   must be handled externally and through native calls (see e.g., 
   <seealso cref="Z3native.inc_ref"/>).</remarks>
   <seealso cref="WrapAST"/>
   @param a The AST to unwrap.
   public IntPtr UnwrapAST(AST a)
   {
   return a.x#gno;
   }

(**
   Return a string describing all available parameters to <c>Expr.Simplify</c>.
*)
   public string SimplifyHelp ( ctx : context ) =
   {


   return Z3native.simplify_get_help(nCtx);
   }

(**
   Retrieves parameter descriptions for simplifier.
*)
   public ParamDescrs SimplifyParameterDescriptions
   {
   get { return new ParamDescrs(this, Z3native.simplify_get_param_descrs(nCtx)); }
   }

(**
   Enable/disable printing of warning messages to the console.
*)
   <remarks>Note that this function is static and effects the behaviour of 
   all contexts globally.</remarks>
   public static void ToggleWarningMessages(bool enabled)
   {
   Z3native.toggle_warning_messages((enabled) ? 1 : 0);
   }
   

(* ERROR HANDLING *)
   //(**
   //A delegate which is executed when an error is raised.
   //*)    
   //<remarks>
   //Note that it is possible for memory leaks to occur if error handlers
   //throw exceptions. 
   //</remarks>
   //public delegate void ErrorHandler(Context ctx, Z3_error_code errorCode, string errorString);

   //(**
   //The OnError event.
   //*)
   //public event ErrorHandler OnError = null;
   

(* PARAMETERS *)
(**
   Update a mutable configuration parameter.
*)
   <remarks>
   The list of all configuration parameters can be obtained using the Z3 executable:
   <c>z3.exe -ini?</c>
   Only a few configuration parameters are mutable once the context is created.
   An exception is thrown when trying to modify an immutable parameter.
   </remarks>
   <seealso cref="GetParamValue"/>
   public void UpdateParamValue(string id, string value)
   {
   Z3native.update_param_value(nCtx, id, value);
   }

(**
   Get a configuration parameter.
*)
   <remarks>
   Returns null if the parameter value does not exist.
   </remarks>
   <seealso cref="UpdateParamValue"/>
   public string GetParamValue(string id)
   {
   IntPtr res = IntPtr.Zero;
   int r = Z3native.get_param_value(nCtx, id, out res);
   if (r == (int)Z3_lbool.Z3_L_FALSE)
   return null;
   else
   return Marshal.PtrToStringAnsi(res);
   }

   

(* INTERNAL *)
   internal IntPtr m_ctx = IntPtr.Zero;
   internal Z3native.error_handler m_n_err_handler = null;
   internal IntPtr nCtx { get { return m_ctx)

   internal void NativeErrorHandler(IntPtr ctx, Z3_error_code errorCode)
   {
   // Do-nothing error handler. The wrappers in Z3.Native will throw exceptions upon errors.            
   }

   internal void InitContext ( ctx : context ) =
   {
   PrintMode = Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT;
   m_n_err_handler = new Z3native.error_handler(NativeErrorHandler); // keep reference so it doesn't get collected.
   Z3native.set_error_handler(m_ctx, m_n_err_handler);
   GC.SuppressFinalize(this);
   }
*)
end
