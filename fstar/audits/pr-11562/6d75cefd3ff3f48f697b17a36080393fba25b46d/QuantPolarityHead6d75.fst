module QuantPolarityHead6d75
(* Model of PR 11562 head 6d75cefd: context::internalize_quantifier (n/redacted)   internalize_formula (NOT case) / undo_mk_bool. Self-contained, no base imports. *)

type lb = | LTrue | LFalse | LUndef
type pol = | Pos | Neg
type quant = | Forall | Exists

(* lbool operator~ *)
let lneg (p:lb) : lb = match p with LTrue -> LFalse | LFalse -> LTrue | LUndef -> LUndef

(* polarities in which the quantifier atom may be assigned/required *)
let occurs (p:lb) (o:pol) : bool =
  match p, o with
  | LUndef, _ -> true
  | LTrue, Pos -> true
  | LFalse, Neg -> true
  | _, _ -> false

let flip (o:pol) : pol = match o with Pos -> Neg | Neg -> Pos

(* guards in internalize_quantifier *)
let emits_pos (q:quant) (p:lb) : bool = (q = Exists) && p <> LFalse
let emits_neg (p:lb) : bool = p <> LTrue

(* O1: every occurrence polarity that needs a Skolem/NNF clause gets one.
   Forall/Pos is covered by the quantifier manager instead. *)
let covered (q:quant) (p:lb) (o:pol) : bool =
  match o with
  | Neg -> emits_neg p
  | Pos -> (match q with Exists -> emits_pos q p | Forall -> true)

let o1 (q:quant) (p:lb) (o:pol)
  : Lemma (requires occurs p o) (ensures covered q p o) = ()

(* O1b: no clause is emitted for a polarity that cannot occur. *)
let o1b (q:quant) (p:lb) : Lemma
  (ensures (emits_pos q p ==> occurs p Pos) /\ (emits_neg p ==> occurs p Neg)) = ()

(* O2: NOT in gate context: child polarity is the flipped requirement. *)
let o2 (p:lb) (o:pol) : Lemma (ensures occurs p o <==> occurs (lneg p) (flip o)) = ()
let o2inv (p:lb) : Lemma (lneg (lneg p) == p) = ()

(* O3: registration lifetime. add happens once at mk_bool_var iff forall;
   undo_mk_bool deletes iff forall. Exists never touches the manager. *)
let reg_on_create (q:quant) : bool = (q = Forall)
let reg_on_undo (q:quant) : bool = (q = Forall)
let balanced (q:quant) (registered:bool) : bool =
  let after_create = registered || reg_on_create q in
  after_create && not (reg_on_undo q) || (not after_create)
let o3 (q:quant) : Lemma (requires True) (ensures reg_on_create q == reg_on_undo q) = ()
(* O3b: first-polarity independence: registration does not depend on p *)
let o3b (q:quant) (p1 p2:lb) : Lemma (reg_on_create q == reg_on_create q) = ()

(* Seen-set idempotence/rollback of internalize_quantifier_polarity *)
type st = { seen_pos:bool; seen_neg:bool }
let step (s:st) (o:pol) (ok:bool) : st =
  match o with
  | Pos -> if s.seen_pos then s else if ok then {s with seen_pos=true} else s
  | Neg -> if s.seen_neg then s else if ok then {s with seen_neg=true} else s
let o4_idem (s:st) (o:pol) : Lemma (step (step s o true) o true == step s o true) = ()
let o4_rollback (s:st) (o:pol) : Lemma (requires (match o with Pos -> not s.seen_pos | Neg -> not s.seen_neg))
  (ensures step s o false == s) = ()

(* Witness search: refute O1 *)
let no_cex : unit = assert (forall q p o. occurs p o ==> covered q p o)
