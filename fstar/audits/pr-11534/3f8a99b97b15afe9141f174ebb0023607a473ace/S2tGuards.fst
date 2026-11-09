module S2tGuards
(* Abstract model of solver2tactic::operator() guards at head 3f8a99b.
   Proof terms are abstracted to: option of (fact_is_false) for the backend proof,
   and a per-assertion flag "input proof present and fact == form". *)
open FStar.List.Tot

type outcome =
  | Throw
  | Unsat_replaced   (* goal reset, false asserted with substituted proof *)
  | Goal_unchanged   (* goal untouched, reason_unknown set *)
  | Goal_reset_to_backend (* goal rebuilt from backend assertions / mc *)

let rec all_ok (l:list bool) : bool = match l with | [] -> true | x::t -> x && all_ok t

(* guard at line 109 : proofs && assumptions non-empty -> throw (before any solver call) *)
let entry (proofs:bool) (n_assume:nat) : bool = not (proofs && n_assume > 0)

(* l_false branch, lines 140-154; backend: None = null proof; Some b = fact-is-false flag *)
let l_false (proofs:bool) (backend:option bool) (inputs:list bool) : outcome =
  if proofs then
    (match backend with
     | None -> Throw
     | Some false -> Throw
     | Some true -> if all_ok inputs then Unsat_replaced else Throw)
  else Unsat_replaced

(* l_undef branch, lines 173-183 *)
let l_undef (proofs core:bool) : outcome =
  if not proofs && not core then Goal_reset_to_backend else Goal_unchanged

(* base l_undef condition was: not core *)
let base_undef (core:bool) : outcome = if not core then Goal_reset_to_backend else Goal_unchanged

(* O1: with proofs on, success of UNSAT requires non-null false-fact backend proof and all input proofs matching *)
let o1 (b:option bool) (i:list bool)
  : Lemma (l_false true b i = Unsat_replaced ==> (b = Some true /\ all_ok i = true)) = ()

(* O2: proof-mode UNKNOWN never mutates (republishes) the goal *)
let o2 (core:bool) : Lemma (l_undef true core = Goal_unchanged) = ()

(* O3: with proofs disabled, UNKNOWN behaviour equals base; UNSAT never throws *)
let o3 (core:bool) (b:option bool) (i:list bool)
  : Lemma (l_undef false core = base_undef core /\ l_false false b i = Unsat_replaced) = ()

(* Reachability witness for the one-sided gap: backend proof Some true and inputs ok succeed,
   so nothing here checks that backend asserted leaves are all among the goal's clauses. *)
let witness_success : unit = assert (l_false true (Some true) [true;true] = Unsat_replaced)
