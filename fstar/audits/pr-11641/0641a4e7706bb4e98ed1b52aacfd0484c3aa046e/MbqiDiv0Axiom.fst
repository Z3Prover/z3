module MbqiDiv0Axiom
(* Abstract model of PR 11641 smt_model_checker.cpp assert_neg_q_m:
   for each residual partial term t = op(x,y), y non-numeral, assert
   (y = 0) ==> t = F(x,y), where F is the candidate model's interpretation
   of div0/idiv0/mod0. Values are mathematical integers; the semantics of
   op in the candidate model M is: y<>0 -> real op, y=0 -> F x y. *)
type interp = int -> int -> int

let sem_op (real_op: int -> int -> int) (f: interp) (x y: int) : int =
  if y = 0 then f x y else real_op x y

(* axiom asserted in aux context for the term value tv *)
let axiom (f: interp) (x y tv: int) : bool = (y <> 0) || (tv = f x y)

(* O1 (conservative): the axiom holds for the value the candidate model
   assigns, so no genuine counterexample to M is excluded. *)
let o1 (real_op: int -> int -> int) (f: interp) (x y: int)
  : Lemma (axiom f x y (sem_op real_op f x y)) = ()

(* O2 (spurious-cex elimination): any assignment satisfying the axiom with
   y = 0 agrees with M on t. *)
let o2 (real_op: int -> int -> int) (f: interp) (x y tv: int)
  : Lemma (requires axiom f x y tv /\ y = 0)
          (ensures tv = sem_op real_op f x y) = ()

(* O3 (vacuity when divisor nonzero): the axiom puts no constraint on tv. *)
let o3 (f: interp) (x y tv: int)
  : Lemma (requires y <> 0) (ensures axiom f x y tv) = ()
