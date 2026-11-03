module PrGuards
(* Abstract model of the PR's proof-guard logic. pr: None = null, Some b = proof whose fact is-false = b *)
type pr = option bool

type out = | Throw | Ok : pr -> out

(* smt_tactic.cpp new guards on unsat branch *)
let smt_unsat (proofs:bool) (p:pr) : out =
  if proofs && (None? p || Some?.v p = false) then Throw
  else (match p with | Some false -> Ok None | _ -> Ok p)

(* O1: with proofs enabled, success implies a proof whose fact is false is attached *)
let o1 (p:pr) : Lemma (Ok? (smt_unsat true p) ==> Ok?._0 (smt_unsat true p) == Some true) = ()

(* O2: without proofs, never throws, and attached proof is never a non-false-fact proof *)
let o2 (p:pr) : Lemma (Ok? (smt_unsat false p) /\ (Ok?._0 (smt_unsat false p) == Some false) == false) = ()

(* solver2tactic: throw if proofs and assumptions nonempty; on unsat require proof of false *)
let s2t (proofs:bool) (nassum:nat) (p:pr) : out =
  if proofs && nassum > 0 then Throw
  else if proofs && (None? p || Some?.v p = false) then Throw
  else Ok p

(* O3: proofs enabled success implies no unsat-core assumptions and proof of false *)
let o3 (n:nat) (p:pr) : Lemma (Ok? (s2t true n p) ==> n == 0 /\ Ok?._0 (s2t true n p) == Some true) = ()
