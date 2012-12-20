(* 
   Copyright (C) 2012 Microsoft Corporation
   Author: CM Wintersteiger (cwinter) 2012-12-17
*)

open Z3enums
open Z3native

module Log = 
struct
  let m_is_open = false
  (* CMW: "open" seems to be an invalid function name*)
  let open_ fn = int2lbool(open_log fn) == L_TRUE
  let close = (close_log)
  let append s = (append_log s)
end
  
class virtual idisposable = 
object
  method virtual dispose : unit
end

class context settings  =
object (self)
  inherit idisposable

  val mutable m_n_ctx : Z3native.z3_context = 
    let cfg = mk_config() in
    let f e = (set_param_value cfg (fst e) (snd e)) in
    (List.iter f settings) ;
    let v = mk_context_rc cfg in
    del_config(cfg) ;
    v

  val mutable m_refCount : int = 0
    
  initializer Gc.finalise (fun self -> self#dispose) self
    
  method dispose : unit = 
    if m_refCount == 0 then (
      Printf.printf "Disposing %d \n" (Oo.id self) ;
      (del_context m_n_ctx)
    ) else (
       (* re-queue for finalization? *)
    )

  method sub_one_ctx_obj = m_refCount <- m_refCount - 1
  method add_one_ctx_obj = m_refCount <- m_refCount + 1
  method get_native = m_n_ctx
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

  method get_native_object = m_n_obj

  method set_native_object x =
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
  method get_native_context = m_ctx#get_native

  (*
    method array_to_native a =
    let f e = e#get_native_object in 
    (Array.map f a) 

    method array_length a =
    match a with
    | Some(x) -> (Array.length x)
    | None -> 0
  *)
end

class symbol ctx_init obj_init = 
object (self)
  inherit z3object ctx_init obj_init

  method incref o = ()
  method decref o = ()

  method kind = match m_n_obj with
    | Some(x) -> (int2symbol_kind (get_symbol_kind self#get_native_context x))
    | _ -> raise (Exception "Underlying object lost")

  method is_int_symbol = match m_n_obj with
    | Some(x) -> self#kind == INT_SYMBOL
    | _ -> false

  method is_string_symbol = match m_n_obj with
    | Some(x) -> self#kind == STRING_SYMBOL
    | _ -> false

  method to_string = match m_n_obj with
    | Some(x) -> 
      (
	match self#kind with
	  | INT_SYMBOL -> (string_of_int (get_symbol_int self#get_native_context x))
	  | STRING_SYMBOL -> (get_symbol_string self#get_native_context x)
      )
    | None -> ""

  method create ctx obj =
    match obj with 
      | Some(x) -> (
	match (int2symbol_kind (get_symbol_kind ctx#get_native x)) with
	  | INT_SYMBOL -> (new intsymbol ctx obj :> symbol)
          | STRING_SYMBOL -> (new stringsymbol ctx obj :> symbol)
      )
      | None -> raise (Exception "Can't create null objects")

end

and intsymbol ctx_init obj_init  = 
object(self)
  inherit symbol ctx_init obj_init

  method get_int = match m_n_obj with
    | Some(x) -> (get_symbol_int m_ctx#get_native x)
    | None -> 0
end

and stringsymbol ctx_init obj_init = 
object(self)
  inherit symbol ctx_init obj_init
end
