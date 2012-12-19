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
  val mutable m_n_ctx : Z3native.z3_context option = None
  val mutable m_refCount : int = 0
    
  initializer 
  let cfg = mk_config() in
  (match settings with
    | Some(x) -> 
      let f e = (set_param_value cfg (fst e) (snd e)) in
      (List.iter f x)
    | _ -> ()	    
  ) ;
  m_n_ctx <- Some (mk_context_rc cfg) ;
  del_config(cfg) ;
  Gc.finalise (fun self -> self#dispose) self
    
  method dispose : unit = 
    if m_refCount == 0 then (
      Printf.printf "Disposing %d \n" (Oo.id self) ;
      match m_n_ctx with
	| Some(x) -> (del_context x)
	| None -> ()
    ) else (
       (* re-queue for finalization? *)
    )

  method sub_one_ctx_obj = m_refCount <- m_refCount - 1
  method add_one_ctx_obj = m_refCount <- m_refCount + 1
end

class virtual z3object ctx_init obj_init =
object (self)
  inherit idisposable
  val mutable m_ctx : context option = ctx_init
  val mutable m_n_obj : Z3native.ptr option = obj_init
    
  initializer 
    (match m_n_obj with 
      | Some (x) -> self#incref x;
	(match m_ctx with
	  | Some(x) -> x#add_one_ctx_obj
	  | None -> ()
	)
      | None -> ()
    );
    Gc.finalise (fun self -> self#dispose) self

  method virtual incref : Z3native.ptr -> unit
  method virtual decref : Z3native.ptr -> unit
    
    (* 
       Disposes of the underlying native Z3 object. 
    *)
  method dispose =
    Printf.printf "Disposing %d \n" (Oo.id self) ;
    (match m_n_obj with
      | Some (x) -> self#decref x; m_n_obj <- None
      | None -> ()
    ); 
    (match m_ctx with
      | Some (x) -> x#sub_one_ctx_obj
      | None -> ()
    );
    m_ctx <- None


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

