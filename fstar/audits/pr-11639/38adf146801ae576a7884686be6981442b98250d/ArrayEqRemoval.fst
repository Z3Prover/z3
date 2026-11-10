module ArrayEqRemoval
(* Arrays modelled as total functions; array equality is extensional (pointwise). *)
type arr (a b:Type) = a -> GTot b
let ext_eq (#a #b:Type) (f g: arr a b) : GTot prop = forall (x:a). f x == g x
let const_arr (#a #b:Type) (v:b) : arr a b = fun _ -> v
let lam (#a #b:Type) (body: a -> GTot b) : arr a b = body

(* O1: the removed const/lambda rule was semantically valid:
   (= (const v) (lambda x. e)) <=> forall x. e == v.  Hence removal cannot be a soundness fix
   or regression in equivalence; it only changes completeness. *)
let o1 (#a #b:Type) (v:b) (e: a -> GTot b)
  : Lemma (ext_eq (const_arr v) (lam e) <==> (forall (x:a). e x == v)) = ()

(* O2: the removed lambda/lambda rule (same sorts) was valid. *)
let o2 (#a #b:Type) (e1 e2: a -> GTot b)
  : Lemma (ext_eq (lam e1) (lam e2) <==> (forall (x:a). e1 x == e2 x)) = ()

(* O3: with the rules deleted, mk_eq_core falls through to the remaining code on the
   same input; model: a rewriter that is identity (no-fire) preserves truth value. *)
let rewrite_sound (p:prop) (r: option prop) = match r with None -> True | Some q -> (p <==> q)
let o3 (p:prop) : Lemma (rewrite_sound p None) = ()
