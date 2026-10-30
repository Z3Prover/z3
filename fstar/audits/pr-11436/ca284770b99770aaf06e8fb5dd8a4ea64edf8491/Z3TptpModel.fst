module Z3TptpModel
module L = FStar.List.Tot

(* Abstract model of the Z3Tptp.fst clause helpers (same_atom, same_literals,
   equality_reduction). Terms are opaque nats; an interpretation maps terms to
   ints and predicates to bools. Equality atoms keep their orientation. *)
type atom =
  | ATrue : atom
  | AEq   : nat -> nat -> atom
  | APred : nat -> atom

type literal = bool & atom
noeq type interp = { tm : nat -> int; pr : nat -> bool }

let eval_atom (i:interp) (a:atom) : bool =
  match a with
  | ATrue -> true
  | AEq s t -> i.tm s = i.tm t
  | APred p -> i.pr p

let eval_lit (i:interp) (l:literal) : bool =
  let (pos, a) = l in if pos then eval_atom i a else not (eval_atom i a)

let rec eval_clause (i:interp) (c:list literal) : bool =
  match c with
  | [] -> false
  | l :: r -> eval_lit i l || eval_clause i r

(* mirrors true_atom / same_atom *)
let true_atom (a:atom) : bool =
  match a with ATrue -> true | AEq s t -> s = t | _ -> false

let same_atom (a b:atom) : bool =
  a = b || (true_atom a && true_atom b) ||
  (match a, b with AEq s t, AEq u v -> s = v && t = u | _ -> false)

(* O1: same_atom is semantically sound *)
let same_atom_sound (i:interp) (a b:atom)
  : Lemma (requires same_atom a b) (ensures eval_atom i a = eval_atom i b) = ()

let rec mem_match (l:literal) (ys:list literal) : bool =
  match ys with
  | [] -> false
  | (o, f) :: r -> (fst l = o && same_atom (snd l) f) || mem_match l r

let rec contained (xs ys:list literal) : bool =
  match xs with
  | [] -> true
  | x :: r -> mem_match x ys && contained r ys

let same_literals (a b:list literal) : bool = contained a b && contained b a

let rec mem_match_sound (i:interp) (l:literal) (ys:list literal)
  : Lemma (requires mem_match l ys) (ensures eval_lit i l ==> eval_clause i ys)
  = match ys with
    | [] -> ()
    | (o, f) :: r ->
      if fst l = o && same_atom (snd l) f then same_atom_sound i (snd l) f
      else mem_match_sound i l r

let rec contained_sound (i:interp) (xs ys:list literal)
  : Lemma (requires contained xs ys) (ensures eval_clause i xs ==> eval_clause i ys)
  = match xs with
    | [] -> ()
    | x :: r -> mem_match_sound i x ys; contained_sound i r ys

(* O2: same_literals preserves clause truth under every interpretation *)
let same_literals_sound (i:interp) (a b:list literal)
  : Lemma (requires same_literals a b) (ensures eval_clause i a = eval_clause i b)
  = contained_sound i a b; contained_sound i b a

(* mirrors equality_reduction's filter: drop negative reflexive equalities *)
let reflexive (a:atom) : bool = match a with AEq s t -> s = t | _ -> false

let rec reduce (c:list literal) (kept:list literal) : Tot (list literal) (decreases c) =
  match c with
  | [] -> kept
  | (pos, e) :: r ->
    if not pos && reflexive e then reduce r kept else reduce r ((pos, e) :: kept)

let rec clause_append (i:interp) (a b:list literal)
  : Lemma (eval_clause i (L.append a b) = (eval_clause i a || eval_clause i b))
  = match a with [] -> () | _ :: r -> clause_append i r b

let rec reduce_sound (i:interp) (c kept:list literal)
  : Lemma (ensures eval_clause i (reduce c kept) = (eval_clause i c || eval_clause i kept))
          (decreases c)
  = match c with
    | [] -> ()
    | (pos, e) :: r -> reduce_sound i r (if not pos && reflexive e then kept else (pos, e) :: kept)

(* O3: equality_reduction's filtered clause is equivalent to the original *)
let equality_reduction_sound (i:interp) (c:list literal)
  : Lemma (eval_clause i (reduce c []) = eval_clause i c)
  = reduce_sound i c []
