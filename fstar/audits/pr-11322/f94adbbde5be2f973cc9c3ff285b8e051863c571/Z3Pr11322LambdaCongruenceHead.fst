module Z3Pr11322LambdaCongruenceHead

(* Arrays are modelled as total functions int -> int. *)
type arr = int -> int

let store (a:arr) (i v:int) : arr = fun j -> if j = i then v else a j
let lam : arr = fun x -> x
let konst (c:int) : arr = fun _ -> c

(* assert_congruent(a,b) queues: a = b ==> forall i. a[i] = b[i]. *)
let congruence_axiom (a b:arr) : prop = (forall (i:int). a == b ==> a i == b i)

(* O1: the queued axiom is valid in the functional array semantics. *)
let o1 (a b:arr) : Lemma (congruence_axiom a b) = ()

(* O2: pairs (root, other) from one equivalence class are all equal if the class
   members are equal; the axiom for every such pair follows. *)
let o2 (root x y:arr) : Lemma
  (requires root == x /\ root == y)
  (ensures congruence_axiom root x /\ congruence_axiom root y) = ()

(* O3: for #11267, store(lambda,7,0) = store(const 3,7,0); the new traversal reaches
   the store parent of the lambda root and its class mate, so instantiating the
   axiom at index 8 gives 8 = 3: contradiction, hence unsat. *)
let o3 (s1 s2:arr) : Lemma
  (requires s1 == store lam 7 0 /\ s2 == store (konst 3) 7 0 /\ s1 == s2)
  (ensures False) =
  assert (s1 8 == 8);
  assert (s2 8 == 3)

(* O3b: when the store overwrites the only difference, the stores agree pointwise,
   so the axiom instances are satisfiable (no spurious conflict). *)
let o3b (j:int) : Lemma
  (store lam 7 0 j == store (fun x -> if x = 7 then 7 else x) 7 0 j) = ()
