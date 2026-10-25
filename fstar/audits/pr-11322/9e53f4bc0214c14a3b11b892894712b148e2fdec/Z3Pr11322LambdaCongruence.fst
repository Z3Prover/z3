module Z3Pr11322LambdaCongruence

(* Array model: total functions Int -> Int, as in extensional array semantics. *)
type arr = int -> int

let sel (a:arr) (i:int) : int = a i
let store (a:arr) (i:int) (v:int) : arr = fun k -> if k = i then v else a k
let const_arr (c:int) : arr = fun _ -> c
let lam_id : arr = fun x -> x
let lam_ite : arr = fun x -> if x = 7 then 1 else 3

(* O1: the axiom asserted by assert_congruent_core, n1 = n2 ==> forall k. sel n1 k = sel n2 k,
   is valid for every pair of arrays, hence for each root/member pair the PR queues. *)
let o1_congruence_valid (n1 n2:arr) (k:int)
  : Lemma (requires n1 == n2) (ensures sel n1 k == sel n2 k) = ()

(* O1b: valid for stores over any base, in particular a store over a lambda. *)
let o1b_store_congruence (l c:arr) (i v k:int)
  : Lemma (requires store l i v == store c i v) (ensures sel (store l i v) k == sel (store c i v) k) = ()

(* O2: issue #11267 witness. With the equality store(lambda x.x,7,0) = store(const 3,7,0),
   the instance k = 8 of the congruence axiom gives 8 = 3: the formula is refutable. *)
let o2_issue_instance_contradiction ()
  : Lemma (sel (store lam_id 7 0) 8 == 8 /\ sel (store (const_arr 3) 7 0) 8 == 3 /\ 8 <> 3) = ()

let o2_equality_unsat ()
  : Lemma (requires store lam_id 7 0 == store (const_arr 3) 7 0) (ensures False) =
  assert (sel (store lam_id 7 0) 8 == sel (store (const_arr 3) 7 0) 8)

(* O3: no spurious unsat. For the PR's satisfiable regression, all instances of the axiom
   hold in the model, because the two stores are pointwise equal. *)
let o3_sat_case_consistent (k:int)
  : Lemma (sel (store lam_ite 7 0) k == sel (store (const_arr 3) 7 0) k) = ()
