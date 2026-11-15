module CrossNestedReport
(* Model of cross_nested::report_result (PR #11710, head e487449e) *)
type st = { done_: bool; lim: bool; reported: int }

type out = | Conflict | NoConflict   (* result of m_call_on_result / check_nex *)

let old_report (s:st) (r:bool) : st =
  let rep = if r then s.reported else s.reported + 1 in
  { s with done_ = r || rep > 100; reported = rep }

let new_report (s:st) (canceled:bool) (r:bool) : st =
  if canceled then { s with lim = true }
  else old_report s r

(* O1: when not canceled, new behaviour equals the old behaviour *)
let o1 (s:st) (r:bool) : Lemma (new_report s false r == old_report s r) = ()

(* O2: when canceled, no spurious done and no counter bump; lim is set;
   a previously set done is not cleared *)
let o2 (s:st) (r:bool) : Lemma
  (let s' = new_report s true r in
   s'.lim == true /\ s'.done_ == s.done_ /\ s'.reported == s.reported) = ()

(* O3: check_nex under cancellation (exception path) returns false, i.e. never
   claims a conflict; non-exception path is unchanged. *)
type nex_res = | Exn | Ret of bool
let check_nex (r:nex_res) : bool = match r with | Exn -> false | Ret b -> b
let o3 (r:nex_res) : Lemma ((Exn? r ==> check_nex r == false) /\ (Ret? r ==> check_nex r == Ret?._0 r)) = ()
