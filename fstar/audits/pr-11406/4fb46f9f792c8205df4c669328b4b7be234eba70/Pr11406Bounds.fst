module Pr11406Bounds
(* Model of PR 11406 guards. size/i/nf are unsigned (nat); vectors abstracted as lengths. *)

(* Z3_apply_result_get_subgoal: reads m_subgoals[i] iff guard passes *)
let old_sub_rejects (i size:nat) : bool = i > size
let new_sub_rejects (i size:nat) : bool = i >= size
let reads_in_bounds (i size:nat) : bool = i < size

(* Counterexample for base: reachable witness size=0 (or 3), i=size passes old guard, read is OOB *)
let base_witness_0 : unit =
  assert (not (old_sub_rejects 0 0) /\ not (reads_in_bounds 0 0))
let base_witness_3 : unit =
  assert (not (old_sub_rejects 3 3) /\ not (reads_in_bounds 3 3))

(* O1: head guard is sound: accepted => read in bounds *)
let sub_sound (i size:nat) : Lemma (requires not (new_sub_rejects i size)) (ensures reads_in_bounds i size) = ()
(* O2: head guard is exact: rejected iff out of bounds (valid indices not newly rejected) *)
let sub_exact (i size:nat) : Lemma (ensures new_sub_rejects i size <==> not (reads_in_bounds i size)) = ()

(* Z3_query_constructor: loop i in [0,nf) reads accs[i], writes accessors[i] *)
let qc_rejects (nf size:nat) : bool = nf > size
(* O3: accepted => every loop index is a valid accessor index *)
let qc_sound (nf size i:nat) : Lemma (requires not (qc_rejects nf size) /\ i < nf) (ensures i < size) = ()
(* O4: partial queries nf<=size and zero-field (size=0,nf=0) still accepted *)
let qc_partial (nf size:nat) : Lemma (requires nf <= size) (ensures not (qc_rejects nf size)) = ()
let qc_zero : unit = assert (not (qc_rejects 0 0))
(* Base had no guard: witness size=0, nf=1 loops with i=0 >= size *)
let qc_base_witness : unit = assert (1 > 0 /\ ~(0 < 0))
(* O5: rejection precedes all stores: model as state of writes; rejected => outputs unchanged *)
type outs = { ctor_written:bool; tester_written:bool; nacc_written:nat }
let init : outs = {ctor_written=false; tester_written=false; nacc_written=0}
let run (nf size:nat) (has_c has_t:bool) : outs =
  if qc_rejects nf size then init
  else { ctor_written=has_c; tester_written=has_t; nacc_written=nf }
let qc_atomic_reject (nf size:nat) (c t:bool) : Lemma (requires nf > size) (ensures run nf size c t == init) = ()
