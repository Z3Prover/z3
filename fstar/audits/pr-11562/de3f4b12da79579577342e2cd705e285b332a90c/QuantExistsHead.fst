module QuantExistsHead
(* Abstract model of smt::context::internalize_quantifier, undo_mk_bool_var and
   cache_generation at PR #11562 head de3f4b12. lbool: -1 false, 0 undef, 1 true. *)
type kind = | Forall | Exists
let is_forall (k:kind) : bool = (k = Forall)
let is_exists (k:kind) : bool = (k = Exists)

(* quantifier-manager registration happens exactly for forall (internalize_quantifier) *)
let registers (k:kind) : bool = is_forall k
(* undo_mk_bool_var deletes exactly for forall; cache_generation reads/inserts for forall *)
let deletes (k:kind) : bool = is_forall k
let caches (k:kind) : bool = is_forall k

(* O1: add/del symmetry and cache only reads generation of registered quantifiers *)
let o1 (k:kind) : Lemma (registers k = deletes k /\ (caches k ==> registers k) /\
                         (k = Exists ==> not (registers k || deletes k || caches k))) = ()

(* polarity passes of internalize_quantifier *)
let pos_pass (k:kind) (p:int) : bool = is_exists k && p <> -1
let neg_pass (p:int) : bool = p <> 1

(* O2: exists gets skolem (positive) pass whenever a positive occurrence is possible,
   and negative pass whenever a negative one is possible; forall never gets the positive pass *)
let o2 (p:int{p = -1 \/ p = 0 \/ p = 1}) : Lemma
  ((p <> -1 ==> pos_pass Exists p) /\ (p <> 1 ==> neg_pass p) /\
   (p = -1 ==> not (pos_pass Exists p)) /\ (p = 1 ==> not (neg_pass p)) /\
   (forall (p':int). not (pos_pass Forall p'))) = ()

(* O3: reentry via internalize_quantifier_polarity's seen-set: a failed pass is removed,
   a completed pass is kept, so each (q,polarity) is processed at most once when complete *)
type seen = { pos:bool; neg:bool }
let mark (s:seen) (positive:bool) : seen =
  if positive then { s with pos = true } else { s with neg = true }
let already (s:seen) (positive:bool) : bool = if positive then s.pos else s.neg
let o3 (s:seen) (b:bool) : Lemma (already (mark s b) b /\ mark (mark s b) b = mark s b /\
                                  (forall (c:bool). c <> b ==> already (mark s b) c = already s c)) = ()
