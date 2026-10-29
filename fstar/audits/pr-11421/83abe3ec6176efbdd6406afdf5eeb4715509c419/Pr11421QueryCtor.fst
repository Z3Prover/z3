module Pr11421QueryCtor
(* Model of Z3_query_constructor (src/api/api_datatype.cpp, head 83abe3ec),
   lines ~262-300: bounds check on num_fields vs accessor vector size, hoisted
   before any output write. Outputs modeled as counts of writes. *)

type result = { err: bool; wrote_ctor: bool; wrote_tester: bool; nacc_written: nat }

(* head: check first, then writes *)
let query_new (num_fields n:nat) (has_ctor has_tester:bool) : result =
  if num_fields > n then { err = true; wrote_ctor = false; wrote_tester = false; nacc_written = 0 }
  else { err = false; wrote_ctor = has_ctor; wrote_tester = has_tester; nacc_written = num_fields }

(* previous head: ctor/tester written before the check (per diff context) *)
let query_old (num_fields n:nat) (has_ctor has_tester:bool) : result =
  if num_fields > n then { err = true; wrote_ctor = has_ctor; wrote_tester = has_tester; nacc_written = 0 }
  else query_new num_fields n has_ctor has_tester

(* O1: on error, no output is written *)
let o1_no_write_on_error (nf n:nat) (c t:bool)
  : Lemma (requires nf > n)
          (ensures (let r = query_new nf n c t in r.err /\ not r.wrote_ctor /\ not r.wrote_tester /\ r.nacc_written = 0))
  = ()

(* O2: on success every accessor index read (i < num_fields) is in bounds *)
let o2_indices_in_bounds (nf n:nat) (c t:bool)
  : Lemma (requires nf <= n)
          (ensures (let r = query_new nf n c t in not r.err /\ r.nacc_written = nf /\ (forall (i:nat). i < nf ==> i < n)))
  = ()

(* O3: the old ordering could leave outputs written while reporting an error
   (witness: num_fields=1, 0 accessors, constructor/tester requested). *)
let o3_old_partial_write ()
  : Lemma (let r = query_old 1 0 true true in r.err /\ r.wrote_ctor /\ r.wrote_tester)
  = ()
