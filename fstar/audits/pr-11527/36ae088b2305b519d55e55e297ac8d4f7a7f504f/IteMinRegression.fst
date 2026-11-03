module IteMinRegression
(* Semantic model of the query in tst_repeated_ite_objective (src/test/opt_bounds.cpp):
   1<=x<=3, 0<=y<=1, y<>1, objective ite(y=0, x, 7), minimize. *)

let feasible (x y:int) : bool = 1 <= x && x <= 3 && 0 <= y && y <= 1 && y <> 1
let obj (x y:int) : int = if y = 0 then x else 7

let o1 (x y:int) : Lemma (requires feasible x y) (ensures y = 0 /\ obj x y = x) = ()

let o2_attained () : Lemma (feasible 1 0 /\ obj 1 0 = 1) = ()
let o2_lower (x y:int) : Lemma (requires feasible x y) (ensures obj x y >= 1) = ()

let o3 () : Lemma (feasible 3 0 /\ obj 3 0 = 3 /\ obj 3 0 > obj 1 0 /\ feasible 1 0) = ()
