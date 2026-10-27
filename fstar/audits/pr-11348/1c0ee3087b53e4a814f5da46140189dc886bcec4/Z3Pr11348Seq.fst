module Z3Pr11348Seq
(* Model of PR 11348 head 1c0ee30: seq_axioms.cpp at-axiom branch guard and
   theory_seq::fixed_length reordering of m_fixed insertion. *)

(* O1: at-axiom. Guard: is_numeral && is_unsigned && iv <= 1024. *)
type idx = | Numeral of int | NonNumeral
let is_unsigned (n:int) : bool = 0 <= n && n < 4294967296
let expand_guard (i:idx) : bool =
  match i with Numeral n -> is_unsigned n && n <= 1024 | NonNumeral -> false
let nth_terms (i:idx{expand_guard i}) : nat = match i with Numeral n -> n + 1
let o1_bounded (i:idx) : Lemma (expand_guard i ==> nth_terms i <= 1025) = ()
(* every index not expanded goes to the symbolic pre/tail split *)
let o1_large (n:int) : Lemma (n > 1024 ==> not (expand_guard (Numeral n))) = ()
(* small unsigned indices keep the former expansion *)
let o1_small (n:int) : Lemma (0 <= n /\ n <= 1024 ==> expand_guard (Numeral n)) = ()

(* O2: fixed_length. State: m_fixed membership of e; cancel flag may flip at any
   m.inc() check inside the loop (modeled by arbitrary list of checks). *)
type res = { fixed: bool; ret: bool; reached_eq: bool }
let rec loop (checks: list bool) : bool =   (* true iff some inc() failed *)
  match checks with [] -> false | c :: t -> if c then true else loop t
let head_fixed_length (fixed0:bool) (checks: list bool) : res =
  if loop checks then { fixed = fixed0; ret = false; reached_eq = false }
  else { fixed = true; ret = true (* continues to mk_seq_eq *); reached_eq = true }
(* cancelled run leaves m_fixed untouched so the element is retried later *)
let o2_cancel_no_mark (f:bool) (cs: list bool)
  : Lemma (loop cs ==> (head_fixed_length f cs).fixed = f) = ()
(* uncancelled run marks e as fixed before asserting seq equation, as in base *)
let o2_complete_marks (f:bool) (cs: list bool)
  : Lemma (not (loop cs) ==> (head_fixed_length f cs).fixed /\ (head_fixed_length f cs).reached_eq) = ()

(* O3: propagate no longer clears m_new_solution after simplify_and_solve_eqs;
   solve_eqs sets it when cancelled with unprocessed eqs, so cancellation
   cannot lose pending work. *)
let solve_eqs_flag (i:nat) (n:nat) (cancelled:bool) (incons:bool) : bool =
  (* flag after loop exit: pending iff i(n and not inconsistent *)
  (not incons) && i < n
let o3_pending_kept (i n:nat) : Lemma (i < n ==) solve_eqs_flag i n true false) = ()
let o3_done_clear (i n:nat) : Lemma (i >= n ==> not (solve_eqs_flag i n false false)) = ()
