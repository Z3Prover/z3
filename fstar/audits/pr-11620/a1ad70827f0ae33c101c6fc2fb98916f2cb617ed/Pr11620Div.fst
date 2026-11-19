module Pr11620Div
(* Semantic model of PR 11620 (head a1ad7082) for non-numeral divisor division.
   Terms: Num n | App1 x y (div/idiv/mod application f(x,y)) | Ite c t e.
   Semantic division at model m: dv m x y = if y = 0 then g x y else base x y,
   where g is the model's interpretation of the div0-style function f_ui. *)
type tm =
  | Num : int -> tm
  | App : tm -> tm -> tm            // f(x,y), f partially interpreted
  | G   : tm -> tm -> tm            // f_ui(x,y)
  | IteZ : tm -> tm -> tm -> tm     // ite (0 = y) a b  ; first arg is y

let rec size (t:tm) : Tot nat =
  match t with
  | Num _ -> 1
  | App x y -> 1 + size x + size y
  | G x y -> 1 + size x + size y
  | IteZ y a b -> 1 + size y + size a + size b

(* Environment: semantic value of f given interpretation of f_ui (g) and total base function. *)
let sem_f (g base: int -> int -> int) (x y:int) : int = if y = 0 then g x y else base x y

let rec ev (g base: int -> int -> int) (t:tm) : Tot int (decreases size t) =
  match t with
  | Num n -> n
  | App x y -> sem_f g base (ev g base x) (ev g base y)
  | G x y -> g (ev g base x) (ev g base y)
  | IteZ y a b -> if ev g base y = 0 then ev g base a else ev g base b

(* Old branch output: ite(0 = y, f_ui(x,y), f(x,y)) *)
let old_rewrite (x y:tm) : tm = IteZ y (G x y) (App x y)

(* O1: the old rewrite is meaning-preserving (so the PR's removal changes no semantics:
   leaving f(x,y) in place denotes the same value). *)
let o1 (g base: int -> int -> int) (x y:tm)
  : Lemma (ev g base (old_rewrite x y) == ev g base (App x y)) = ()

(* O2: the old rewrite output strictly contains the input redex f(x,y) as a subterm
   and is strictly larger: re-rewriting its else-branch reproduces the same input, a cycle
   (BR_DONE result re-visited => non-termination witness for the loop the PR fixes). *)
let rec subterm (s t:tm) : Tot bool (decreases size t) =
  if s = t then true else
  match t with
  | Num _ -> false
  | App x y | G x y -> subterm s x || subterm s y
  | IteZ y a b -> subterm s y || subterm s a || subterm s b

let o2 (x y:tm)
  : Lemma (subterm (App x y) (old_rewrite x y) /\ size (old_rewrite x y) > size (App x y)) = ()

(* O3: soundness of the new behaviour at ground divisor values: with the branch removed,
   a ground evaluation of f(x,y) is still determined: the numeral-zero guard
   (is_considered_uninterpreted) yields g, nonzero numeral yields base. *)
let o3 (g base: int -> int -> int) (a b:int)
  : Lemma (ev g base (App (Num a) (Num b)) == (if b = 0 then g a b else base a b)) = ()

(* O4: refactor mk_idiv0/mk_mod0: same (family, kind, domain sorts, range) as inlined code.
   Modelled as record equality of declaration keys. *)
type decl_key = { op:nat; dom:list nat; rng:nat }
let int_s = 0
let old_idiv0 : decl_key = { op=1; dom=[int_s;int_s]; rng=int_s }
let new_idiv0 : decl_key = { op=1; dom=[int_s;int_s]; rng=int_s }
let old_mod0 : decl_key = { op=2; dom=[int_s;int_s]; rng=int_s }
let new_mod0 : decl_key = { op=2; dom=[int_s;int_s]; rng=int_s }
let o4 () : Lemma (old_idiv0 == new_idiv0 /\ old_mod0 == new_mod0) = ()
