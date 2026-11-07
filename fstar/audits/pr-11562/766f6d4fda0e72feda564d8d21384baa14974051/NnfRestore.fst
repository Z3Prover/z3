module NnfRestore
(* Abstract model of asserted_formulas::reduce with the PR's extra nnf step.
   Atoms are opaque; quantifiers range over a Boolean-valued variable (small-domain instance). *)
type f =
  | Atom : nat -> f
  | Not : f -> f
  | And : f -> f -> f
  | Or : f -> f -> f
  | Forall : nat -> f -> f
  | Exists : nat -> f -> f

type env = nat -> bool
let upd (e:env) (i:nat) (b:bool) : env = fun j -> if j = i then b else e j

let rec ev (e:env) (p:f) : Tot bool (decreases p) =
  match p with
  | Atom i -> e i
  | Not q -> not (ev e q)
  | And a b -> ev e a && ev e b
  | Or a b -> ev e a || ev e b
  | Forall i q -> ev (upd e i true) q && ev (upd e i false) q
  | Exists i q -> ev (upd e i true) q || ev (upd e i false) q

(* NNF: negation only on atoms *)
let rec is_nnf (p:f) : Tot bool (decreases p) =
  match p with
  | Atom _ -> true
  | Not (Atom _) -> true
  | Not _ -> false
  | And a b | Or a b -> is_nnf a && is_nnf b
  | Forall _ q | Exists _ q -> is_nnf q

let rec nnf (pos:bool) (p:f) : Tot f (decreases p) =
  match p with
  | Atom i -> if pos then Atom i else Not (Atom i)
  | Not q -> nnf (not pos) q
  | And a b -> if pos then And (nnf true a) (nnf true b) else Or (nnf false a) (nnf false b)
  | Or a b -> if pos then Or (nnf true a) (nnf true b) else And (nnf false a) (nnf false b)
  | Forall i q -> if pos then Forall i (nnf true q) else Exists i (nnf false q)
  | Exists i q -> if pos then Exists i (nnf true q) else Forall i (nnf false q)

(* O1: output is NNF, so negative quantifiers are eliminated *)
let rec nnf_is_nnf (pos:bool) (p:f) : Lemma (ensures is_nnf (nnf pos p)) (decreases p) =
  match p with
  | Atom _ -> ()
  | Not q -> nnf_is_nnf (not pos) q
  | And a b | Or a b -> nnf_is_nnf pos a; nnf_is_nnf pos b
  | Forall _ q | Exists _ q -> nnf_is_nnf pos q

(* O2: equivalence preservation *)
let rec nnf_sound (pos:bool) (p:f) (e:env)
  : Lemma (ensures ev e (nnf pos p) = (if pos then ev e p else not (ev e p))) (decreases p) =
  match p with
  | Atom _ -> ()
  | Not q -> nnf_sound (not pos) q e
  | And a b | Or a b -> nnf_sound pos a e; nnf_sound pos b e
  | Forall i q | Exists i q ->
    nnf_sound pos q (upd e i true); nnf_sound pos q (upd e i false)

(* O3: after any rewriting step r (even one that breaks NNF), re-running nnf yields an
   equivalent NNF formula whenever r is semantics preserving. *)
let restore (r: f -> f) (p:f)
  : Lemma (requires forall e. ev e (r p) = ev e p)
          (ensures is_nnf (nnf true (r p)) /\ (forall e. ev e (nnf true (r p)) = ev e p)) =
  nnf_is_nnf true (r p);
  FStar.Classical.forall_intro (fun e -> nnf_sound true (r p) e)

(* Idempotence on already-NNF input: the added pass is harmless when nothing was broken *)
let rec nnf_idem (p:f) : Lemma (requires is_nnf p) (ensures nnf true p == p) (decreases p) =
  match p with
  | Atom _ | Not (Atom _) -> ()
  | And a b | Or a b -> nnf_idem a; nnf_idem b
  | Forall _ q | Exists _ q -> nnf_idem q
