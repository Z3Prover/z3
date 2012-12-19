(* 
   Author: CM Wintersteiger
   (C) Microsoft Research, 2012
 *)

open Z3enums
open Z3native

class context =
  object (self)
    val m_n_ctx : Z3native.z3_context option = None
    val mutable m_refCount : int = 0
    initializer Gc.finalise (fun self -> self#dispose ()) self
    method dispose () = 
      Printf.printf "Disposing %d \n" (Oo.id self) ;
      match m_n_ctx with
      | Some(x) -> (del_context x)
      | None -> ()
    method sub_one_ctx_obj = m_refCount <- m_refCount - 1
    method add_one_ctx_obj = m_refCount <- m_refCount + 1
  end

class virtual z3object ctx_init obj_init =
  object (self)
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
      Gc.finalise (fun self -> self#dispose ()) self

    method virtual incref : Z3native.ptr -> unit
    method virtual decref : Z3native.ptr -> unit
	
        (* 
	   Disposes of the underlying native Z3 object. 
	 *)
    method dispose () =
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

    method array_to_native a =
      let f e = e#get_native_object in 
      (Array.map f a) 

    method array_length a =
      match a with
      | Some(x) -> (Array.length x)
      | None -> 0

  end

