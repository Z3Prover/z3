module QuantPolarityInternalize
(* Abstract model of smt::context::internalize_quantifier / internalize_quantifier_polarity
   at head f66a77ae. lbool polarity, literal(var, sign) and the clause ~premise \/ result. *)
type lbool = | LTrue | LFalse | LUndef
let neg (p:lbool) : lbool = match p with | LTrue -> LFalse | LFalse -> LTrue | LUndef -> LUndef

(* which polarities are processed: internalize_quantifier *)
let do_pos (p:lbool) : bool = (p = LUndef)            (* positive normalization when undef; true-case is the default q *)
let do_neg (p:lbool) : bool = (p <> LTrue)            (* polarity != l_true *)

(* the polarity set an occurrence may take: LTrue -> only positive, etc. *)
let may_pos (p:lbool) : bool = (p <> LFalse)
let may_neg (p:lbool) : bool = (p <> LTrue)

(* Obligation 1: Not flips the occurrence set exactly and is an involution *)
let ob1 (p:lbool) : Lemma
  (neg (neg p) = p /\ may_pos (neg p) = may_neg p /\ may_neg (neg p) = may_pos p) = ()

(* Obligation 2: every possible occurrence polarity of q is covered:
   negative occurrences always get skolem clause; positive ones use q itself (do_pos adds NNF of q when undef) *)
let ob2 (p:lbool) : Lemma
  ((may_neg p ==> do_neg p) /\ (p = LUndef ==> do_pos p /\ do_neg p)) = ()

(* Obligation 3: the clause literal arithmetic: premise = literal(q, !positive);
   clause = ~premise \/ result is exactly (source -> result) *)
type lit = { v:nat; sign:bool }
let ev (a:nat -> bool) (l:lit) : bool = (a l.v) <> l.sign
let lneg (l:lit) : lit = { l with sign = not l.sign }
let source_val (a:nat -> bool) (q:nat) (positive:bool) : bool = if positive then a q else not (a q)
let ob3 (a:nat -> bool) (q:nat) (positive:bool) (r:bool) : Lemma
  (let premise = { v = q; sign = not positive } in
   ev a premise = source_val a q positive /\
   (ev a (lneg premise) || r) = ((not (source_val a q positive)) || r)) = ()
