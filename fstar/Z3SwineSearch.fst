module Z3SwineSearch

(* Checked by the parent WSL F* session. Small logical kernel for private phasing.
   Formula predicates range over ORIGINAL valuations; the private Boolean
   is represented separately and is existentially forgotten. *)
#set-options "--fuel 1 --ifuel 0 --z3rlimit 10"

let valid (#a:Type) (lemma:a -> prop) : prop =
  forall (v:a). lemma v

let unsat (#a:Type) (formula:a -> prop) : prop =
  forall (v:a). ~(formula v)

let private_extension (#a:Type) (formula box:a -> prop) (v:a) (phase:bool) : prop =
  formula v /\ (phase ==> box v)

let phase_false_preserves (#a:Type) (formula box:a -> prop) (v:a)
  : Lemma (private_extension formula box v false <==> formula v) = ()

let existential_erasure (#a:Type) (formula box:a -> prop) (v:a)
  : Lemma ((exists (phase:bool). private_extension formula box v phase)
           <==> formula v) =
  assert (formula v ==> private_extension formula box v false)

let global_lemma_preserves (#a:Type) (formula lemma:a -> prop) (v:a)
  : Lemma (requires valid lemma)
          (ensures (formula v /\ lemma v) <==> formula v) = ()

let unsat_after_valid_lemma (#a:Type) (formula lemma:a -> prop)
  : Lemma (requires valid lemma /\ unsat (fun v -> formula v /\ lemma v))
          (ensures unsat formula) = ()

(* Even explicitly blocking the whole current private phase is safe
   UNDER EXISTENTIAL ERASURE. It is not a globally valid arithmetic lemma,
   and UNSAT while assuming phase=true must cause restart, not final UNSAT. *)
let block_private_phase (#a:Type) (formula box:a -> prop) (v:a)
  : Lemma ((exists (phase:bool).
               private_extension formula box v phase /\ phase == false)
           <==> formula v) =
  assert (formula v ==>
    (private_extension formula box v false /\ false == false))

let witness_not_unsat (#a:Type) (formula:a -> prop) (w:a)
  : Lemma (requires formula w) (ensures ~(unsat formula)) =
  if unsat formula then begin
    assert (forall (v:a). ~(formula v));
    assert (~(formula w));
    assert False
  end

let bounded_unsat_is_not_original_unsat ()
  : Lemma (unsat (fun (v:int) -> v == 11 /\ -10 <= v /\ v <= 10) /\
           ~(unsat (fun (v:int) -> v == 11))) =
  witness_not_unsat (fun (v:int) -> v == 11) 11

let rejected_candidate_is_not_unsat ()
  : Lemma ((2 <> 3) /\ ~(unsat (fun (v:int) -> v == 2))) =
  witness_not_unsat (fun (v:int) -> v == 2) 2

(* A core independent of private phase permits original UNSAT only when
   all its remaining constraints follow from the original input. *)
let private_independent_core (#a:Type) (formula core:a -> prop)
  : Lemma (requires (forall (v:a). formula v ==> core v) /\ unsat core)
          (ensures unsat formula) = ()
