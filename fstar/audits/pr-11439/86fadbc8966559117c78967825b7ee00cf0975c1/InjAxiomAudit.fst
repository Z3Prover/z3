module InjAxiomAudit
(* Model of the candidate-recognition loop of simplify_inj_axiom
   (src/ast/rewriter/inj_axiom.cpp, lines 56-80 at head). *)
open FStar.List.Tot

type arg = | V : nat -> arg | C : nat -> arg

(* position i: (c1, c2) = (f1 arg i, f2 arg i); v1,v2 = the two equality vars.
   state: found, seen passive vars (earlier f1 args that were counted vars) *)
type st = { found: bool; seen: list arg }

let is_var (a:arg) = V? a

(* head=true adds the PR's repeated-passive-variable rejection *)
let step (head:bool) (v1 v2:arg) (s:st) (c1 c2:arg) : option st =
  if (c1 = v1 && c2 = v2) || (c1 = v2 && c2 = v1) then
    (if s.found then None else Some ({ s with found = true }))
  else if c1 = c2 && c1 <> v1 && c1 <> v2 then
    (if is_var c1 then
       (if head && mem c1 s.seen then None
        else Some ({ s with seen = c1 :: s.seen }))
     else Some s)
  else None

let rec scan (head:bool) (v1 v2:arg) (s:st) (l:list (arg & arg)) : Tot (option st) (decreases l) =
  match l with
  | [] -> Some s
  | (c1,c2)::tl ->
    (match step head v1 v2 s c1 c2 with
     | None -> None
     | Some s' -> scan head v1 v2 s' tl)

let accepts (head:bool) v1 v2 l =
  match scan head v1 v2 ({found=false; seen=[]}) l with
  | Some s -> s.found | None -> false

let rec nodup (l:list arg) : bool =
  match l with [] -> true | h::t -> not (mem h t) && nodup t

(* O1: witness f(x,z,z) vs f(y,z,z), x=V0,y=V1,z=V2: base accepts, head rejects *)
let args_wit : list (arg & arg) = [ (V 0, V 1); (V 2, V 2); (V 2, V 2) ]
let o1_base_accepts : squash (accepts false (V 0) (V 1) args_wit = true) =
  assert_norm (accepts false (V 0) (V 1) args_wit = true)
let o1_head_rejects : squash (accepts true (V 0) (V 1) args_wit = false) =
  assert_norm (accepts true (V 0) (V 1) args_wit = false)

(* O1 semantic: with the base rewrite, the refined axiom
   forall x z w. inj(z,w,f(x,z,w)) = x (fresh binder per position) is
   inconsistent with a<>b, f(a,a,b)=f(b,a,b), which has a model for the original. *)
let refined_contradicts (#u:Type) (f: u -> u -> u -> u) (inj: u -> u -> u -> u)
    (a b: u)
    (ax: (x:u -> z:u -> w:u -> Lemma (inj z w (f x z w) == x)))
    (h: squash (f a a b == f b a b))
  : Lemma (a == b)
  = ax a a b; ax b a b

(* the original axiom (injective only on f(_,z,z)) has a model with a<>b, f a a b = f b a b *)
let mf (x z w:nat) : nat = if z = w then x else 0
let orig_ok (x y z:nat) : Lemma (mf x z z = mf y z z ==> x = y) = ()
let model_ok : squash (mf 0 0 1 = mf 1 0 1 /\ 0 <> 1) = ()
(* and that same model violates the refined axiom's instance *)
let refined_fails : squash (~(forall (x y z w:nat). mf x z w = mf y z w ==> x = y)) =
  assert (mf 0 0 1 = mf 1 0 1 /\ 0 <> 1)

(* O2: head accepted candidates have pairwise-distinct passive variables *)
let rec scan_inv (v1 v2:arg) (s:st) (l:list (arg & arg)) : Lemma
  (requires nodup s.seen)
  (ensures (match scan true v1 v2 s l with Some s' -> nodup s'.seen | None -> True))
  (decreases l)
  = match l with
    | [] -> ()
    | (c1,c2)::tl ->
      (match step true v1 v2 s c1 c2 with
       | None -> ()
       | Some s' -> scan_inv v1 v2 s' tl)

(* O3: with passive vars distinct, the original axiom instantiates to
   injectivity for every z,w (no extra strength vs. refined axiom, f x z w) *)
let o3 (f: nat -> nat -> nat -> nat)
  (ax: (x:nat -> y:nat -> z:nat -> w:nat -> Lemma (f x z w == f y z w ==> x == y)))
  (x y z w:nat) : Lemma (f x z w == f y z w ==> x == y) = ax x y z w
