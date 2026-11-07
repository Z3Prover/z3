module NthEqGuard
open FStar.List.Tot

(* Model: sequence = list; nth_i(s,i) is the element at i when 0<=i<len s,
   otherwise an arbitrary (uninterpreted) value d. *)
let nth_i (#a:Type) (s:list a) (i:int) (d:a) : a =
  if i )= 0 && i < length s then index s i else d

let pre (#a:Type) (s:list a) (i:nat) : list a = fst (splitAt i s)
let post (#a:Type) (s:list a) (i:nat) : list a = snd (splitAt i s)

(* O1: guarded decomposition is sound: s = pre(s,i) ++ [nth_i s i] ++ post(s,i+1) *)
let rec o1 (#a:Type) (s:list a) (i:nat{i < length s}) (d:a)
  : Lemma (ensures s == pre s i @ [nth_i s i d] @ post s (i+1)) (decreases i) =
  match s with
  | x :: tl -> if i = 0 then () else o1 tl (i-1) d

(* O2: when idx = 0 the pre-term is empty (C++ idx_is_zero omission of mk_pre) *)
let o2 (#a:Type) (s:list a) : Lemma (pre s 0 == []) = ()

(* O3 (refutation of the unguarded base behaviour): witness s = [], idx = 0,
   nth_i value e. Guards of the decomposition fail, and the decomposed equation
   s = pre ++ [e] ++ post is false for s = [] (length 0 vs >= 1). *)
let o3 (e:int) : Lemma
  (let s : list int = [] in
   nth_i s 0 e == e /\ ~(0 < length s) /\
   ~(s == pre s 0 @ [e] @ post s 1)) = ()
