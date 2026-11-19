module OptIteBoundAudit
(* Model of opt::context::is_min_max_of_sums (min case, one-bound fragment). *)

let b2i (b:bool) : int = if b then 1 else 0

(* Rewrite output for one threshold: x = ite p 1 0, with (c >= 1) ==> p. *)
let rewritten_feasible (x c:int) (p:bool) : prop = x == b2i p /\ (c >= 1 ==> p)

(* O1 (counterexample on base): hidden constraint x = 5 (via read_x(0)=5, or f(t)=5 with f(0)
   aliasing f(t) since t=0). Original is satisfiable with x=5 >= ite a 1 0, a any;
   after the base rewrite x = ite p 1 0 so the hidden constraint is unsatisfiable. *)
let o1_original_sat () : Lemma (exists (x:int) (a:bool). x == 5 /\ x >= b2i a) =
  assert (5 == 5 /\ 5 >= b2i false)
let o1_rewritten_unsat () : Lemma (forall (x:int) (c:int) (p:bool). x == 5 ==> ~(rewritten_feasible x c p)) = ()

(* O2 (fix guard): rewrite is applied only when no recursive definitions and the objective is a constant. *)
let guard (has_rec_defs is_uninterp_const:bool) : bool = (not has_rec_defs) && is_uninterp_const
let o2_guard_blocks_witness () : Lemma (guard true true == false /\ guard false false == false /\ guard false true == true) = ()

(* O3: for syntactically closed objective, two bounds c1,c2 in [0,2], thresholds k=1,2:
   (c_i>=k ==> p_k); the minimal sum of p's equals max c1 c2, and every feasible sum is >= it. *)
let feas (c1 c2:int) (p1 p2:bool) : bool =
  (not (c1 >= 1 || c2 >= 1) || p1) && (not (c1 >= 2 || c2 >= 2) || p2)
let sumP (p1 p2:bool) : int = b2i p1 + b2i p2
let mx (a b:int) : int = if a > b then a else b
let o3_lower (c1 c2:int{0 <= c1 /\ c1 <= 2 /\ 0 <= c2 /\ c2 <= 2}) (p1 p2:bool)
  : Lemma (requires feas c1 c2 p1 p2) (ensures sumP p1 p2 >= mx c1 c2) = ()
let o3_attained (c1 c2:int{0 <= c1 /\ c1 <= 2 /\ 0 <= c2 /\ c2 <= 2})
  : Lemma (exists (p1 p2:bool). feas c1 c2 p1 p2 /\ sumP p1 p2 == mx c1 c2) =
  let p1 = c1 >= 1 || c2 >= 1 in
  let p2 = c1 >= 2 || c2 >= 2 in
  assert (feas c1 c2 p1 p2 /\ sumP p1 p2 == mx c1 c2)
