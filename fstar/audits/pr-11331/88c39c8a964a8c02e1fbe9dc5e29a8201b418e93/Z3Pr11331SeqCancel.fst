module Z3Pr11331SeqCancel
open FStar.List.Tot

(* O1: seq_axioms.cpp at_axiom guard. The concrete branch emits k+1 units. *)
let concrete_guard (iv:int) : bool = iv >= 0 && iv <= 4294967295 && iv <= 1024
let units_emitted (k:nat) : nat = k + 1

let o1_bounded (iv:int)
  : Lemma (concrete_guard iv ==> units_emitted iv <= 1025) = ()

let o1_boundaries () : Lemma (concrete_guard 1024 /\ not (concrete_guard 1025) /\
                           not (concrete_guard 4294967295) /\
                           not (concrete_guard 4294967296)) = ()

(* Symbolic branch is the base fallback: for 0 <= i < len s, s = pre ++ (e :: tl)
   with len pre = i and e = s[i]; holds for every i, so large i loses nothing. *)
let rec split_ok (#a:Type) (s:list a) (i:nat{i < length s})
  : Lemma (ensures (let (pre, rest) = splitAt i s in
                    length pre == i /\ Cons? rest /\
                    s == pre @ rest /\ Cons?.hd rest == index s i))
          (decreases i)
  = if i = 0 then () else split_ok (Cons?.tl s) (i-1)

(* O2: fixed_length. State = fixed flag; loop polls inc before each of lo steps.
   fuel = number of polls that return true. Marking happens only after completion. *)
type fl_result = | Cancelled | Done

let fl_run (fixed:bool) (lo:nat) (fuel:nat) : (fl_result & bool) =
  if fuel >= lo then (Done, true) else (Cancelled, fixed)

let o2_cancel_keeps_retry (lo:nat) (fuel:nat)
  : Lemma (requires fuel < lo)
          (ensures fl_run false lo fuel == (Cancelled, false)) = ()

let o2_complete_marks (lo:nat) (fuel:nat)
  : Lemma (requires fuel >= lo) (ensures fl_run false lo fuel == (Done, true)) = ()

(* retry after cancellation with enough fuel completes *)
let o2_retry (lo:nat) (f1 f2:nat)
  : Lemma (requires f1 < lo /\ f2 >= lo)
          (ensures (let (_, fx) = fl_run false lo f1 in fl_run fx lo f2 == (Done, true))) = ()

(* O3: solve_eqs loop. Equations indexed list; solved ones erased, others stay.
   Interruption (fuel exhausted) leaves the unprocessed suffix and raises
   m_new_solution; is_solved requires an empty equation set before FC_DONE. *)
type eq = { id:nat; solvable:bool }

let rec run (eqs:list eq) (fuel:nat) : (list eq & list eq) =   (* (kept, unprocessed) *)
  match eqs with
  | [] -> ([], [])
  | e :: rest ->
    if fuel = 0 then ([], eqs)
    else
      let (k, u) = run rest (fuel - 1) in
      ((if e.solvable then k else e :: k), u)

let flag (u:list eq) : bool = Cons? u
let final_state (eqs:list eq) (fuel:nat) : list eq = let (k,u) = run eqs fuel in k @ u

let rec o3_no_loss (eqs:list eq) (fuel:nat)
  : Lemma (ensures (let (k,u) = run eqs fuel in
                    (forall x. mem x (k@u) ==> mem x eqs) /\
                    (forall x. mem x eqs /\ not x.solvable ==> mem x (k@u))))
          (decreases eqs)
  = match eqs with
    | [] -> ()
    | e :: rest ->
      if fuel = 0 then ()
      else begin
        o3_no_loss rest (fuel-1);
        let (k,u) = run rest (fuel-1) in
        FStar.Classical.forall_intro (FStar.List.Tot.Properties.append_mem k u);
        FStar.Classical.forall_intro (FStar.List.Tot.Properties.append_mem (e::k) u)
      end

(* interruption is signalled: if work remains unprocessed the flag is set *)
let o3_flag_on_interrupt (eqs:list eq) (fuel:nat)
  : Lemma (let (_,u) = run eqs fuel in (fuel < length eqs ==> flag u)) 
  = let rec aux (eqs:list eq) (fuel:nat) : Lemma (ensures (fuel < length eqs ==> Cons? (snd (run eqs fuel)))) (decreases eqs) =
      match eqs with [] -> () | _ :: r -> if fuel = 0 then () else aux r (fuel-1) in
    aux eqs fuel

(* with sufficient fuel nothing is left unprocessed and flag is clear *)
let rec o3_complete (eqs:list eq) (fuel:nat)
  : Lemma (requires fuel >= length eqs) (ensures snd (run eqs fuel) == [])
          (decreases eqs)
  = match eqs with [] -> () | _ :: r -> o3_complete r (fuel-1)

(* soundness gate: sat (FC_DONE) needs m_eqs empty, which is independent of interruption *)
let fc_done_allowed (eqs:list eq) : bool = Nil? eqs
let o3_interrupted_not_done (eqs:list eq) (fuel:nat)
  : Lemma (requires fuel < length eqs)
          (ensures not (fc_done_allowed (final_state eqs fuel)))
  = o3_flag_on_interrupt eqs fuel;
    let (k,u) = run eqs fuel in
    assert (Cons? u);
    FStar.List.Tot.Properties.append_length k u
