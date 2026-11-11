module Z3RegexCertificateTests

module A = Z3PredicateAlgebra
module T = Z3TransitionTerm
module C = Z3RegexCertificate
module R = Z3RegexTheory

let atom (q x:bool) : bool = q = x
let alg : A.algebra (A.predicate bool) bool = A.free_algebra atom
let positive : A.predicate bool = A.Atom true

let is_empty (q:A.predicate bool) : bool =
  not (alg.holds q false) && not (alg.holds q true)

let lemma_algebra () : Lemma (A.valid alg /\ A.empty_sound alg is_empty) =
  A.lemma_free_algebra_valid atom;
  reveal_opaque (`%A.empty_sound) (A.empty_sound alg is_empty);
  assert (forall (q:A.predicate bool) (x:bool).
    is_empty q ==> not (alg.holds q x))

let tree : T.term (A.predicate bool) nat =
  T.Node positive
    (T.Node (A.Compl positive) (T.Leaf 99) (T.Leaf 1))
    (T.Leaf 0)

let test_operations () : Lemma True =
  assert_norm (T.eval alg.holds tree true = 1);
  assert_norm (T.eval alg.holds tree false = 0);
  assert_norm (T.eval alg.holds (T.lift_unary (fun (n:nat) -> n + 2) tree) true = 3);
  assert_norm (T.eval alg.holds
    (T.lift_binary (fun (n m:nat) -> n + m) tree tree) true = 2);
  assert_norm (T.eval alg.holds
    (T.bind tree (fun n -> T.Node positive (T.Leaf (n + 1)) (T.Leaf n))) true = 2);
  assert_norm (T.restrict alg is_empty tree A.Top =
    T.Node positive (T.Leaf 1) (T.Leaf 0));
  assert_norm (T.check alg is_empty (fun (n:nat) -> n < 2) A.Top tree);
  assert_norm (not (T.check alg A.never_empty (fun (n:nat) -> n < 2) A.Top tree));
  assert_norm (not (T.check alg is_empty (fun (n:nat) -> n = 0) A.Top tree));
  assert_norm (T.check alg is_empty (fun _ -> false) A.Bottom tree)

let machine : C.system (A.predicate bool) int = {
  nullable = (fun q -> q = 2 || q = 3 || q = 4);
  derivative = (fun q ->
    if q = 1 then T.Node positive (T.Leaf 1) (T.Leaf 0)
    else if q = 2 then T.Leaf 2
    else if q = 3 then T.Node positive (T.Leaf 3) (T.Leaf 2)
    else if q = 4 then T.Node positive (T.Leaf 4) (T.Leaf 0)
    else if q = 5 then T.Leaf 2
    else if q = 6 then
      T.Node positive
        (T.Node (A.Compl positive) (T.Leaf 2) (T.Leaf 1))
        (T.Leaf 0)
    else if q = 7 then T.Leaf 1
    else T.Leaf 0)
}

let rec accepts (q:int) (w:list bool) : Tot bool (decreases w) =
  match w with
  | [] -> machine.nullable q
  | x :: rest -> accepts (T.eval alg.holds (machine.derivative q) x) rest

let language (q:int) : R.lang bool = fun w -> accepts q w == true

let lemma_system () : Lemma (C.system_sound alg machine language) = ()

let row (q:int) (label:nat) : C.row int = { state = q; label = label }
let empty_class : C.certificate int = [row 0 10; row 1 10]
let full_class : C.certificate int = [row 2 20; row 3 20]
let pruned_class : C.certificate int = [row 0 10; row 1 10; row 6 10]

let test_cycles () : Lemma True =
  assert_norm (C.check_equivalence alg is_empty machine 0 1 empty_class);
  assert_norm (C.check_equivalence alg A.never_empty machine 0 1 empty_class);
  assert_norm (C.check_equivalence alg is_empty machine 2 3 full_class);
  assert_norm (C.check_equivalence alg is_empty machine 0 6 pruned_class);
  assert_norm (not (C.check_equivalence alg A.never_empty machine 0 6 pruned_class));
  assert_norm (C.check_equivalence alg is_empty machine 0 0 []);
  assert_norm (C.check_equivalence alg is_empty machine 0 7
    [row 0 10; row 7 10; row 1 10])

let test_rejects_bad_certificates () : Lemma True =
  assert_norm (not (C.check_equivalence alg is_empty machine 0 1 []));
  assert_norm (not (C.check_equivalence alg is_empty machine 0 2
    [row 0 10; row 2 10]));
  assert_norm (not (C.check_equivalence alg is_empty machine 0 5
    [row 0 10; row 5 10; row 2 20]));
  assert_norm (not (C.check_equivalence alg is_empty machine 2 4
    [row 2 20; row 4 20; row 0 10]));
  assert_norm (not (C.check_equivalence alg is_empty machine 0 7
    [row 0 10; row 7 10]));
  assert_norm (not (C.check_equivalence alg is_empty machine 0 1
    [row 0 10; row 0 20; row 1 10]));
  assert_norm (not (C.check_equivalence alg is_empty machine 0 1
    [row 0 10; row 1 20]));
  assert_norm (not (C.check_equivalence alg is_empty machine 0 1 full_class))

(* Instantiate the semantic contract, rather than proving soundness only under
   an abstract assumption that could have no model. *)
let test_certificate_soundness (w:list bool) : Lemma
    ((R.mem w (language 0) <==> R.mem w (language 6)) /\
     (R.mem w (language 2) <==> R.mem w (language 3))) =
  lemma_algebra ();
  lemma_system ();
  assert_norm (C.check_equivalence alg is_empty machine 0 6 pruned_class);
  assert_norm (C.check_equivalence alg is_empty machine 2 3 full_class);
  C.lemma_check_equivalence_sound alg is_empty machine language 0 6 pruned_class;
  C.lemma_check_equivalence_sound alg is_empty machine language 2 3 full_class

let test_contract_rejects_fake_emptiness ()
  : Lemma (~(A.empty_sound alg (fun _ -> true))) =
  reveal_opaque (`%A.empty_sound) (A.empty_sound alg (fun _ -> true));
  assert_norm (alg.holds A.Top false)

let test_contract_rejects_wrong_nullability ()
  : Lemma (~(C.system_sound alg { machine with nullable = (fun _ -> true) } language)) =
  assert_norm (not (accepts 0 []))

(* A second inhabited contract uses the existing regex language combinators
   directly, instead of defining the language by executing the machine. *)
let regex_machine : C.system (A.predicate bool) (bool & bool) = {
  nullable = (fun q -> fst q);
  derivative = (fun q ->
    T.Node positive
      (T.Leaf (fst q, not (snd q)))
      (T.Leaf q))
}

let regex_language (q:bool & bool) : R.lang bool =
  if fst q then R.re_full else R.re_empty

let lemma_regex_system ()
  : Lemma (C.system_sound alg regex_machine regex_language) = ()

let regex_classes : C.certificate (bool & bool) =
  [{ C.state = (false, false); label = 0 };
   { C.state = (false, true); label = 0 };
   { C.state = (true, false); label = 1 };
   { C.state = (true, true); label = 1 }]

let test_existing_regex_semantics () : Lemma
    (R.equiv (regex_language (false, false)) (regex_language (false, true)) /\
     R.equiv (regex_language (true, false)) (regex_language (true, true))) =
  lemma_algebra ();
  A.lemma_never_empty_sound alg;
  lemma_regex_system ();
  assert_norm (C.check_equivalence alg A.never_empty regex_machine
    (false, false) (false, true) regex_classes);
  assert_norm (C.check_equivalence alg A.never_empty regex_machine
    (true, false) (true, true) regex_classes);
  C.lemma_check_equivalence_sound alg A.never_empty regex_machine regex_language
    (false, false) (false, true) regex_classes;
  C.lemma_check_equivalence_sound alg A.never_empty regex_machine regex_language
    (true, false) (true, true) regex_classes
