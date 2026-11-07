module QuantPolarity
(* Abstract model of the polarity dispatch added by PR #11562 in
   smt_internalizer.cpp (head 8f52ea371d6674e3b5bfce7824b0654ff69180e2):
   context::internalize_formula (NOT case), internalize_quantifier. *)

type lbool = | L_true | L_false | L_undef

(* lbool operator~ *)
let lneg (p:lbool) : lbool =
  match p with L_true -> L_false | L_false -> L_true | L_undef -> L_undef

(* occurrence polarities denoted by an lbool: l_undef = may be either *)
type occ = | Pos | Neg
let denotes (p:lbool) (o:occ) : bool =
  match p with L_true -> o = Pos | L_false -> o = Neg | L_undef -> true
let flip (o:occ) : occ = match o with Pos -> Neg | Neg -> Pos

(* guards in internalize_quantifier *)
let adds_pos (p:lbool) : bool = (p = L_undef)
let adds_neg (p:lbool) : bool = (p <> L_true)

(* O1: every occurrence that may be negative gets the negative NNF clause,
   and no negative clause is added when only positive occurrences are possible. *)
let o1 (p:lbool) : Lemma (adds_neg p <==> denotes p Neg) = ()

(* O2: NOT-gate propagation: an occurrence o of (not q) under p is an
   occurrence of q with flipped polarity, and lneg p denotes exactly those. *)
let o2 (p:lbool) (o:occ) : Lemma (denotes (lneg p) (flip o) <==> denotes p o) = ()

(* O3: double negation through gates restores the polarity, and l_undef
   (used for gate children) over-approximates both occurrences. *)
let o3 (p:lbool) : Lemma (lneg (lneg p) = p /\ denotes L_undef Pos /\ denotes L_undef Neg
                          /\ (forall o. denotes p o ==> denotes L_undef o)) = ()

(* Sanity: quantifier under NOT in gate context at top level (l_true)
   -> inner polarity l_false -> negative clause only *)
let witness : unit -> Lemma (adds_neg (lneg L_true) /\ not (adds_pos (lneg L_true))) = fun () -> ()
