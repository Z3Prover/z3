module OptIteBoundPR11636
(* Model of src/opt/opt_context.cpp at head bcd5c02b (base 8927ff98).
   Not a proof of C++ execution. *)

type term_kind = | UConst | UApp : n:pos -> term_kind | Other

(* base: is_uninterp(term); head: is_uninterp_const(term) *)
let old_guard (t:term_kind) : bool = UConst? t || UApp? t
let new_guard (t:term_kind) : bool = UConst? t

(* O2: head guard is a strict refinement of the base guard *)
let o2_refines (t:term_kind) : Lemma (new_guard t ==> old_guard t) = ()
let o2_strict : squash (old_guard (UApp 1) /\ ~(new_guard (UApp 1))) = ()

(* O3: simplify_min_max_of_sums early return on recfun definitions *)
let simplify (has_rec:bool) (fires:bool) : bool = if has_rec then false else fires
let o3_rec (f:bool) : Lemma (simplify true f = false) = ()
let o3_norec (f:bool) : Lemma (simplify false f = f) = ()

(* O1: counterexample for base guard. Term f(a); a=b and f(b) = -1 are
   unmarked (they do not contain the AST f(a)). Original: max f(a) s.t.
   f(a) <= ite(c,1,0), a=b, f(b) = -1. Rewrite (k=1): f(a) = ite(p,1,0), a=b,
   f(b) = -1, p => ite(c,1,0) >= 1. *)
let ite_i (b:bool) : int = if b then 1 else 0

(* semantic interpretation: f applied to a and to b with a = b *)
let orig_sat (fa fb:int) (c:bool) (a b:int) : bool =
  fa <= ite_i c && a = b && fb = -1 && (not (a = b) || fa = fb)
let rewritten_sat (fa fb:int) (c p:bool) (a b:int) : bool =
  fa = ite_i p && a = b && fb = -1 && (not (a = b) || fa = fb)
  && (not p || ite_i c >= 1)

let o1_witness : squash (orig_sat (-1) (-1) false 0 0) = ()
let o1_rewrite_unsat (fa fb:int) (c p:bool) (a b:int)
  : Lemma (rewritten_sat fa fb c p a b = false) = ()
