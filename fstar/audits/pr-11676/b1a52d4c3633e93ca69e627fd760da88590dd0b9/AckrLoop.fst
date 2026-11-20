module AckrLoop
open FStar.List.Tot

(* Model of convert_constants' loop. Constants are ids; processing constant c may
   append constants given by [fresh c] (model completion in add_entry). *)
let process (fresh: nat -> list nat) (cs: list nat) (c: nat) : list nat = cs @ fresh c

(* PR head: live bound i < length cs. Returns final list and index reached. *)
let rec live (fresh: nat -> list nat) (cs: list nat) (i: nat) (fuel: nat)
  : Tot (option (list nat & nat)) (decreases fuel) =
  if i >= length cs then Some (cs, i)
  else if fuel = 0 then None
  else live fresh (process fresh cs (index cs i)) (i + 1) (fuel - 1)

(* Base: bound n cached before the loop. *)
let rec cached (fresh: nat -> list nat) (cs: list nat) (i: nat) (n: nat)
  : Tot (list nat & nat) (decreases (if i >= n then 0 else n - i)) =
  if i >= n then (cs, i)
  else if i >= length cs then (cs, i)
  else cached fresh (process fresh cs (index cs i)) (i + 1) n

(* Obligation 1 (counterexample): constant 0 whose completion registers 1. *)
let fresh1 (c: nat) : list nat = if c = 0 then [1] else []
let _ = assert_norm (cached fresh1 [0] 0 (length [0]) == ([0;1], 1))
let base_misses_new_constant : squash (snd (cached fresh1 [0] 0 1) < length (fst (cached fresh1 [0] 0 1))) =
  assert_norm (cached fresh1 [0] 0 1 == ([0;1], 1))

(* Obligation 2: when the live loop terminates, every constant (incl. appended) was visited. *)
#push-options "--fuel 2"
let rec live_complete (fresh: nat -> list nat) (cs: list nat) (i: nat) (fuel: nat)
  : Lemma (requires i <= length cs)
          (ensures (match live fresh cs i fuel with
                    | Some (fin, j) -> j == length fin
                    | None -> True))
          (decreases fuel) =
  if i >= length cs then ()
  else if fuel = 0 then ()
  else (append_length cs (fresh (index cs i));
        live_complete fresh (process fresh cs (index cs i)) (i + 1) (fuel - 1))

#pop-options

(* Obligation 3: same witness under live loop reaches the appended constant. *)
let live_hits_new : squash (live fresh1 [0] 0 5 == Some ([0;1], 2)) =
  assert_norm (live fresh1 [0] 0 5 == Some ([0;1], 2))
