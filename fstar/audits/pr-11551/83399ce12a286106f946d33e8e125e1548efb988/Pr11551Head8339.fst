module Pr11551Head8339
(* Model of the new OP_CONCAT branch in smt2_printer::process_app (ast_smt2_pp.cpp, head 83399ce).
   Bit-vectors are bit lists; concat is append. Printed term = left-nested binary concats. *)
open FStar.List.Tot

type tm = | Leaf : list bool -> tm | Cat : tm -> tm -> tm

let rec eval (t:tm) : list bool = match t with
  | Leaf b -> b
  | Cat a b -> eval a @ eval b

let rec fold_cat (acc:tm) (rest:list tm) : Tot tm (decreases rest) = match rest with
  | [] -> acc
  | x::xs -> fold_cat (Cat acc x) xs

let print_concat (a b:tm) (rest:list tm) : tm = fold_cat (Cat a b) rest

let rec eval_all (l:list tm) : list bool = match l with
  | [] -> []
  | x::xs -> eval x @ eval_all xs

let rec fold_sem (acc:tm) (rest:list tm)
  : Lemma (ensures eval (fold_cat acc rest) == eval acc @ eval_all rest) (decreases rest)
  = match rest with
  | [] -> append_l_nil (eval acc)
  | x::xs -> append_assoc (eval acc) (eval x) (eval_all xs); fold_sem (Cat acc x) xs

let print_sem (a b:tm) (rest:list tm)
  : Lemma (eval (print_concat a b rest) == eval_all (a::b::rest))
  = fold_sem (Cat a b) rest; append_assoc (eval a) (eval b) (eval_all rest)

let rec width_all (l:list tm) : nat = match l with [] -> 0 | x::xs -> length (eval x) + width_all xs
let width_ok (a b:tm) (rest:list tm)
  : Lemma (length (eval (print_concat a b rest)) == width_all (a::b::rest))
  = print_sem a b rest;
    let rec aux (l:list tm) : Lemma (length (eval_all l) == width_all l) =
      match l with [] -> () | x::xs -> append_length (eval x) (eval_all xs); aux xs in
    aux (a::b::rest)

let _ = assert_norm (print_concat (Leaf [true]) (Leaf [false]) [Leaf [true]]
                     == Cat (Cat (Leaf [true]) (Leaf [false])) (Leaf [true]))
