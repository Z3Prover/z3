module Z3FiniteSetForcedDistinct

(* Semantic model of theory_finite_set::are_forced_distinct (PR 11456, head 3f4492d).
   Sets are membership predicates over an element type (base module Z3FiniteSetTheory).
   A "fact" is a relevant, assigned atom (x in S) whose set argument has the root of a or b. *)

open Z3FiniteSetTheory

type fact (t:eqtype) = { elem: t; value: bool }

(* Facts about a set are sound w.r.t. a model: value == mem s elem *)
let sound (#t:eqtype) (s:fset t) (f:fact t) : prop = (mem s f.elem <==> f.value == true)

(* Obligation 1: a is empty (class contains set.empty), b has a true membership fact => a <> b *)
let ob_empty (#t:eqtype) (a b:fset t) (fb:fact t)
  : Lemma (requires a == empty_set #t /\ sound b fb /\ fb.value == true)
          (ensures ~(a == b))
  = assert (mem b fb.elem);
    assert (~(mem a fb.elem))

(* Symmetric case: b empty, a has true fact *)
let ob_empty_sym (#t:eqtype) (a b:fset t) (fa:fact t)
  : Lemma (requires b == empty_set #t /\ sound a fa /\ fa.value == true)
          (ensures ~(a == b))
  = ob_empty b a fa

(* Obligation 2: roots of the elements coincide (x ~ y, modelled as equal values),
   opposite assigned values => a <> b *)
let ob_conflict (#t:eqtype) (a b:fset t) (fa fb:fact t)
  : Lemma (requires sound a fa /\ sound b fb /\ fa.elem == fb.elem /\ fa.value =!= fb.value)
          (ensures ~(a == b))
  = ()

(* Obligation 3: when the function returns true, the extensionality axiom
   (exists x. x in a xor x in b) is satisfied by the witness, so skipping it
   loses no consequence of a <> b under the current assignment. *)
let ob_witness_extensional (#t:eqtype) (a b:fset t) (fa fb:fact t)
  : Lemma (requires sound a fa /\ sound b fb /\ fa.elem == fb.elem /\ fa.value =!= fb.value)
          (ensures exists (x:t). mem a x =!= mem b x)
  = assert (mem a fa.elem =!= mem b fa.elem)

(* Negative sanity: the empty-set rule needs the *true* polarity; a false fact is no witness. *)
let ob_false_fact_not_witness ()
  : Lemma (exists (a b:fset int) (fb:fact int). a == empty_set #int /\ b == empty_set #int /\ sound b fb /\ fb.value == false /\ a == b)
  = let fb : fact int = {elem=0; value=false} in
    assert (sound (empty_set #int) fb)
