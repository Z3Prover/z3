(**
   The Z3 ML/Ocaml Interface.

   Copyright (C) 2012 Microsoft Corporation
   @author CM Wintersteiger (cwinter) 2012-12-17
*)

open Z3enums
open Z3native

(**/**)

(* Object definitions. These are internal and should be interacted 
   with only via the corresponding functions from modules. *)

class virtual idisposable = 
object
  method virtual dispose : unit
end

class context settings  =
object (self)
  inherit idisposable

  val mutable m_n_ctx : Z3native.z3_context = 
    let cfg = mk_config in
    let f e = (set_param_value cfg (fst e) (snd e)) in
    (List.iter f settings) ;
    let v = mk_context_rc cfg in
    del_config(cfg) ;
    v

  val mutable m_refCount : int = 0
    
  initializer 
    Gc.finalise (fun self -> self#dispose) self
    
  method dispose : unit = 
    if m_refCount == 0 then (
      Printf.printf "Disposing context %d \n" (Oo.id self) ;
      (del_context m_n_ctx)
    ) else (
    (* re-queue for finalization? *)
    )

  method sub_one_ctx_obj = m_refCount <- m_refCount - 1
  method add_one_ctx_obj = m_refCount <- m_refCount + 1
  method gno = m_n_ctx
end

class virtual z3object ctx_init obj_init =
object (self)
  inherit idisposable
  val mutable m_ctx : context = ctx_init
  val mutable m_n_obj : Z3native.ptr option = obj_init
    
  initializer 
    (match m_n_obj with 
      | Some (x) -> self#incref x;
	m_ctx#add_one_ctx_obj
      | None -> ()
    );
    Gc.finalise (fun self -> self#dispose) self

  method virtual incref : Z3native.ptr -> unit
  method virtual decref : Z3native.ptr -> unit
    
  (* 
     Disposes of the underlying native Z3 object. 
  *)
  method dispose =
    Printf.printf "Disposing z3object %d \n" (Oo.id self) ;
    (match m_n_obj with
      | Some (x) -> self#decref x; m_n_obj <- None; m_ctx#sub_one_ctx_obj
      | None -> ()
    ); 

  method gno = m_n_obj

  method sno x =
    (match x with
      | Some(x) -> self#incref x
      | None -> ()
    );
    (match m_n_obj with
      | Some(x) -> self#decref x
      | None -> ()
    );
    m_n_obj <- x

  method get_context = m_ctx
  method gnc = m_ctx#gno

(*
  method array_to_native a =
    let f e = e#gno in 
    (Array.map f a) 

  method array_length a =
    match a with
      | Some(x) -> (Array.length x)
      | None -> 0
*)

end

class symbol ctx obj = 
object (self)
  inherit z3object ctx obj

  method incref o = ()
  method decref o = ()
end

class int_symbol ctx = 
object(self)
  inherit symbol ctx None
  method cnstr_obj obj = (self#sno obj) ; self
  method cnstr_int i = (self#sno (Some (mk_int_symbol ctx#gno i))) ; self
end

class string_symbol ctx = 
object(self)
  inherit symbol ctx None
  method cnstr_obj obj = (self#sno obj) ; self
  method cnstr_string name = (self#sno (Some (mk_string_symbol ctx#gno name))) ; self
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
  let open_ filename = ((int2lbool (open_log filename)) == L_TRUE)

  (** Closes the interaction log. *)
  let close = close_log

  (** Appends a user-provided string to the interaction log.
      @param s the string to append*)
  let append s = append_log s
end

(** Version information. *)
module Version =
struct
  (** The major version. *)
  let major = let (x, _, _, _) = get_version in x

  (** The minor version. *)
  let minor = let (_, x, _, _) = get_version in x

  (** The build version. *)
  let build = let (_, _, x, _) = get_version in x

  (** The revision. *)
  let revision = let (_, _, _, x) = get_version in x

  (** A string representation of the version information. *)
  let to_string = 
    let (mj, mn, bld, rev) = get_version in
    string_of_int mj ^ "." ^
      string_of_int mn ^ "." ^
      string_of_int bld ^ "." ^
      string_of_int rev ^ "."
end

(** Symbols are used to name several term and type constructors. *)
module Symbol =
struct
(**/**)
  let create ctx obj =
    match obj with 
      | Some(x) -> (
	match (int2symbol_kind (get_symbol_kind ctx#gno x)) with
	  | INT_SYMBOL -> (((new int_symbol ctx)#cnstr_obj obj) :> symbol)
          | STRING_SYMBOL -> (((new string_symbol ctx)#cnstr_obj obj) :> symbol)
      )
      | None -> raise (Exception "Can't create null objects")
(**/**)

  (** The kind of the symbol (int or string) *)
  let kind (o : symbol) = match o#gno with
    | Some(x) -> (int2symbol_kind (get_symbol_kind o#gnc x))
    | _ -> raise (Exception "Underlying object lost")

  (** Indicates whether the symbol is of Int kind *)
  let is_int_symbol (o : symbol) = match o#gno with
    | Some(x) -> (kind o) == INT_SYMBOL
    | _ -> false

  (** Indicates whether the symbol is of string kind. *)
  let is_string_symbol (o : symbol) = match o#gno with
    | Some(x) -> (kind o) == STRING_SYMBOL
    | _ -> false

  (** The int value of the symbol. *)
  let get_int (o : int_symbol) = match o#gno with
    | Some(x) -> (get_symbol_int o#gnc x)
    | None -> 0

  (** The string value of the symbol. *)
  let get_string (o : string_symbol) = match o#gno with
    | Some(x) -> (get_symbol_string o#gnc x)
    | None -> ""

  (** A string representation of the symbol. *)
  let to_string (o : symbol) = match o#gno with
    | Some(x) -> 
      (
	match (kind o) with
	  | INT_SYMBOL -> (string_of_int (get_symbol_int o#gnc x))
	  | STRING_SYMBOL -> (get_symbol_string o#gnc x)
      )
    | None -> ""
end

(** The main interaction with Z3 happens via the Context. *)
module Context =
struct
  (**
     Creates a new symbol using an integer.
     
     Not all integers can be passed to this function.
     The legal range of unsigned integers is 0 to 2^30-1.
  *)
  let mk_symbol_int ctx i = 
    (new int_symbol ctx)#cnstr_int i
    
  (** Creates a new symbol using a string. *)
  let mk_symbol_string ctx s =
    (new string_symbol ctx)#cnstr_string s

  (**
     Create an array of symbols.
  *)
  let mk_symbols ctx names =
    let f elem = mk_symbol_string ctx elem in
    (Array.map f names)
      
end
