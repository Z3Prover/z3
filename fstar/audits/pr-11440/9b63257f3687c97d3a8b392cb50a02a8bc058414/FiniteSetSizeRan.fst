module FiniteSetSizeRan
(* Abstract model of theory_finite_set_size solver lifecycle (m_solver, m_solver_ran,
   exhausted state of the sub-context, trail scopes). Base vs PR head 9b63257. *)
open FStar.List.Tot

type st = { solver: bool; ran: bool; exh: bool; scopes: list (bool & option bool) }
(* scope = (clear_solver trail entry present, value_trail old value of m_solver_ran) *)

let init0 : st = { solver=false; ran=false; exh=false; scopes=[(false,None)] }

let upd_top (s:st) (f:(bool & option bool) -> (bool & option bool)) : st =
  match s.scopes with | h::t -> {s with scopes = f h :: t} | [] -> s

let push (s:st) : st = {s with scopes = (false,None) :: s.scopes}

(* pop: undo trail of the top scope in reverse push order: restore-ran entry, then clear *)
let pop (s:st) : st =
  match s.scopes with
  | (c,rr)::(x::t) ->
    let s1 = (match rr with Some v -> {s with ran=v} | None -> s) in
    let s2 = if c then {s1 with solver=false; ran=false; exh=false} else s1 in
    {s2 with scopes = x::t}
  | _ -> s

(* initialize_solver: only when no solver *)
let init (s:st) : st =
  if s.solver then s else upd_top ({s with solver=true; exh=false}) (fun (_,rr) -> (true,rr))

(* run_solver reaching l_false: exhausts the sub-solver, sets ran.
   base pushes value_trail(old ran); head does not *)
let run_base (s:st) : st =
  if s.solver && not s.ran then
    upd_top ({s with ran=true; exh=true}) (fun (c,_) -> (c, Some s.ran))
  else s
let run_head (s:st) : st =
  if s.solver && not s.ran then {s with ran=true; exh=true} else s

(* final_check calls run_solver exactly when solver && not ran; property P: then not exh *)
let p_ok (s:st) : bool = not (s.solver && not s.ran && s.exh)

(* O1: counterexample in BASE: init@scope1; run@scope2; pop -> solver kept, ran=false, exhausted *)
let witness_base : st =
  pop (run_base (push (init (push init0))))
let o1 : unit =
  assert_norm (witness_base.solver = true /\ witness_base.ran = false /\ witness_base.exh = true);
  assert_norm (p_ok witness_base = false)

(* Same trace under HEAD preserves P *)
let witness_head : st = pop (run_head (push (init (push init0))))
let o2 : unit = assert_norm (p_ok witness_head = true /\ witness_head.ran = true)

(* O3: inductive invariant for HEAD over all push/pop/init/run sequences *)
let rec nclear (l:list (bool & option bool)) : nat =
  match l with [] -> 0 | (c,_)::t -> (if c then 1 else 0) + nclear t
let rec no_rr (l:list (bool & option bool)) : bool =
  match l with [] -> true | (_,r)::t -> None? r && no_rr t

let inv (s:st) : bool =
  Cons? s.scopes && no_rr s.scopes &&
  (if s.solver then nclear s.scopes = 1 else (nclear s.scopes = 0 && not s.ran && not s.exh)) &&
  (not s.exh || s.ran)

type op = | Push | Pop | Init | Run
let step (o:op) (s:st) : st =
  match o with Push -> push s | Pop -> pop s | Init -> init s | Run -> run_head s

let step_inv (o:op) (s:st) : Lemma (requires inv s) (ensures inv (step o s)) = ()

let rec run_ops (l:list op) (s:st) : st =
  match l with [] -> s | o::t -> run_ops t (step o s)

let rec reach_inv (l:list op) (s:st) : Lemma (requires inv s) (ensures inv (run_ops l s)) (decreases l) =
  match l with [] -> () | o::t -> step_inv o s; reach_inv t (step o s)

(* Consequence: in HEAD, run_solver's precondition never sees an exhausted sub-solver *)
let head_safe (l:list op) : Lemma (ensures p_ok (run_ops l init0)) =
  assert_norm (inv init0); reach_inv l init0
