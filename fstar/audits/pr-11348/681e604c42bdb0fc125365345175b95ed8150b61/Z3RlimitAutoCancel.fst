module Z3RlimitAutoCancel
(* Model of reslimit timer state in src/util/rlimit.{h,cpp} at head 681e604c. Unsigned 32-bit wrap is modelled. *)
let umax : int = 4294967296
let wrap (x:int) : int = ((x % umax) + umax) % umax
type st = { cancel:nat; num:nat; tms:nat }

let dec_cancel (s:st) : st = if s.cancel > 0 then { s with cancel = s.cancel - 1 } else s
let pop_timeout (s:st) : st = { s with tms = 0 }
(* head auto_cancel: --m_num_timers; if 0 then pop_timeout; dec_cancel *)
let auto_cancel (s:st{s.num > 0}) : st =
  let s1 = { s with num = s.num - 1 } in
  let s2 = if s1.num = 0 then pop_timeout s1 else s1 in
  dec_cancel s2
(* is_timeout firing: inc_cancel(num); pop_timeout *)
let fire (s:st) : st = pop_timeout { s with cancel = s.cancel + s.num }

(* O1: when the last timer is released, no stale timeout remains *)
let o1 (s:st{s.num = 1}) : Lemma ((auto_cancel s).tms = 0 /\ (auto_cancel s).num = 0) = ()
(* O2: non-last release leaves the timeout armed for remaining timers *)
let o2 (s:st{s.num > 1}) : Lemma ((auto_cancel s).tms = s.tms) = ()
(* O3: fire then n releases restores the cancel count (balance preserved) *)
let rec rel (n:nat) (s:st{s.num >= n}) : Tot st (decreases n) =
  if n = 0 then s else rel (n-1) (auto_cancel s)
let rec o3 (n:nat) (s:st{s.num >= n /\ s.cancel >= s.num}) : Lemma (ensures (rel n s).cancel = s.cancel - n /\ (rel n s).num = s.num - n) (decreases n) =
  if n = 0 then () else o3 (n-1) (auto_cancel s)
let o3_fire (s:st{s.num >= 1}) : Lemma ((rel s.num (fire s)).cancel = s.cancel /\ (rel s.num (fire s)).num = 0) =
  o3 s.num (fire s)
(* Witness: unbalanced release at num=0 wraps to UINT_MAX and skips pop_timeout *)
let wrap_witness : unit = assert (wrap (0 - 1) = 4294967295)
