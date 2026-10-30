module Z3TptpLiteralAudit
open FStar.List.Tot

type lit = bool & int
type fm = | Atom : int -> fm | Not : fm -> fm | Or : list fm -> fm | And : list fm -> fm
        | Imp : fm -> fm -> fm | T : fm | F : fm

let rec ev (v:int -> bool) (f:fm) : Tot bool (decreases f) =
  match f with
  | Atom a -> v a | Not g -> not (ev v g) | T -> true | F -> false
  | Imp a b -> not (ev v a) || ev v b
  | Or l -> evl true v l | And l -> evl false v l
and evl (is_or:bool) (v:int -> bool) (l:list fm) : Tot bool (decreases l) =
  match l with
  | [] -> not is_or
  | x :: r -> if is_or then ev v x || evl is_or v r else ev v x && evl is_or v r

let ll (v:int -> bool) (l:lit) : bool = let (p,a) = l in if p then v a else not (v a)
let rec cl (v:int -> bool) (ls:list lit) : bool =
  match ls with [] -> false | x :: r -> ll v x || cl v r

// Mirrors Z3Tptp.literals / literal_arguments (positive flag = polarity)
let rec lits (p:bool) (f:fm) : Tot (list lit) (decreases f) =
  match f with
  | Not g -> lits (not p) g
  | Or l -> if p then litl p l else [(p, -1)]
  | And l -> if not p then litl p l else [(p, -1)]
  | Imp a b -> if p then lits false a @ lits true b else [(p, -1)]
  | F -> if p then [] else [(p, -2)]
  | T -> if not p then [] else [(p, -3)]
  | Atom a -> [(p, a)]
and litl (p:bool) (l:list fm) : Tot (list lit) (decreases l) =
  match l with [] -> [] | x :: r -> lits p x @ litl p r

let rec cl_append (v:int -> bool) (a b:list lit)
  : Lemma (ensures cl v (a @ b) = (cl v a || cl v b)) (decreases a) =
  match a with [] -> () | _ :: r -> cl_append v r b

// Obligation 1: flattening is semantically correct for fragments whose opaque cases are excluded
let rec wf (p:bool) (f:fm) : Tot bool (decreases f) =
  match f with
  | Not g -> wf (not p) g
  | Or l -> p && wfl p l
  | And l -> (not p) && wfl p l
  | Imp a b -> p && wf false a && wf true b
  | _ -> true
and wfl (p:bool) (l:list fm) : Tot bool (decreases l) =
  match l with [] -> true | x :: r -> wf p x && wfl p r

let rec lits_ok (v:int -> bool) (p:bool) (f:fm)
  : Lemma (requires wf p f /\ (v (-2) == false /\ v (-3) == true))
          (ensures cl v (lits p f) = (if p then ev v f else not (ev v f)))
          (decreases f) =
  match f with
  | Not g -> lits_ok v (not p) g
  | Or l -> litl_ok v p l
  | And l -> litl_ok v p l
  | Imp a b -> lits_ok v false a; lits_ok v true b; cl_append v (lits false a) (lits true b)
  | _ -> ()
and litl_ok (v:int -> bool) (p:bool) (l:list fm)
  : Lemma (requires wfl p l /\ (v (-2) == false /\ v (-3) == true))
          (ensures cl v (litl p l) = (if p then evl true v l else not (evl false v l)))
          (decreases l) =
  match l with
  | [] -> ()
  | x :: r -> lits_ok v p x; litl_ok v p r; cl_append v (lits p x) (litl p r)

// Obligation 2: same_literals (mutual containment) preserves clause semantics
let has (l:lit) (ys:list lit) : bool = mem l ys
let contained (xs ys:list lit) : bool = for_all (fun x -> has x ys) xs

let rec cl_mem (v:int -> bool) (x:lit) (ys:list lit)
  : Lemma (requires mem x ys /\ ll v x) (ensures cl v ys) (decreases ys) =
  match ys with
  | [] -> ()
  | y :: r -> if y = x then () else cl_mem v x r

let rec cl_contained (v:int -> bool) (xs ys:list lit)
  : Lemma (requires contained xs ys) (ensures cl v xs ==> cl v ys) (decreases xs) =
  match xs with
  | [] -> ()
  | x :: r -> if ll v x then cl_mem v x ys else cl_contained v r ys

let same_literals_sound (v:int -> bool) (a b:list lit)
  : Lemma (requires contained a b /\ contained b a) (ensures cl v a = cl v b) =
  cl_contained v a b; cl_contained v b a

// Obligation 3: equality_reduction drops only negative literals over atoms valid in v
let rec drop (refl:int -> bool) (l:list lit) : list lit =
  match l with
  | [] -> []
  | (p,a) :: r -> if (not p) && refl a then drop refl r else (p,a) :: drop refl r

let rec drop_sound (v refl:int -> bool) (l:list lit)
  : Lemma (requires forall a. refl a ==> v a) (ensures cl v (drop refl l) = cl v l) (decreases l) =
  match l with [] -> () | _ :: r -> drop_sound v refl r
