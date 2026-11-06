module QuantPolarityHead2304
(* Abstract model of smt::context::internalize_quantifier / internalize_quantifier_polarity
   at head 2304e7c2 (smt_internalizer.cpp), lbool encoded as in util/lbool.h:
   l_false=-1, l_undef=0, l_true=1, operator~ = integer negation. *)
let l_false : int = -1
let l_undef : int = 0
let l_true  : int = 1
let valid (p:int) : bool = p = -1 || p = 0 || p = 1
let lnot (p:int) : int = 0 - p
let to_lbool (b:bool) : int = (if b then 1 else 0) * 2 - 1

let o1 (p:int{valid p}) (b:bool) : Lemma
  (valid (lnot p) /\ lnot (lnot p) = p /\ lnot l_true = l_false /\ lnot l_false = l_true /\ lnot l_undef = l_undef
   /\ valid (to_lbool b) /\ to_lbool b = (if b then l_true else l_false)) = ()

let may_pos (p:int) : bool = p <> l_false
let may_neg (p:int) : bool = p <> l_true
let do_pos (p:int) : bool = (p = l_undef)
let do_neg (p:int) : bool = (p <> l_true)

let o2 (p:int{valid p}) : Lemma
  (may_pos (lnot p) = may_neg p /\ may_neg (lnot p) = may_pos p /\
   (may_neg p ==> do_neg p) /\ (p = l_undef ==> do_pos p /\ do_neg p)) = ()

type st = { pos:bool; neg:bool }
let step (s:st) (p:int) : st = { pos = s.pos || do_pos p; neg = s.neg || do_neg p }
let covers (s:st) (p:int) : bool = (not (may_neg p) || s.neg) && (p <> l_undef || s.pos)
let o3 (s:st) (p:int{valid p}) (p2:int{valid p2}) : Lemma
  (covers (step s p) p /\ covers (step (step s p) p2) p /\ covers (step (step s p) p2) p2
   /\ step (step s p) p = step s p) = ()

type lit = { v:nat; sign:bool }
let ev (a:nat -> bool) (l:lit) : bool = (a l.v) <> l.sign
let lneg (l:lit) : lit = { l with sign = not l.sign }
let source_val (a:nat -> bool) (q:nat) (positive:bool) : bool = if positive then a q else not (a q)
let o4 (a:nat -> bool) (q:nat) (positive:bool) (r:bool) : Lemma
  (let premise = { v = q; sign = not positive } in
   ev a premise = source_val a q positive /\
   (ev a (lneg premise) || r) = ((not (source_val a q positive)) || r)) = ()

let o5 () : Lemma (do_pos l_undef /\ do_neg l_undef /\ not (do_neg l_true) /\ do_neg l_false /\ not (do_pos l_false)) = ()
