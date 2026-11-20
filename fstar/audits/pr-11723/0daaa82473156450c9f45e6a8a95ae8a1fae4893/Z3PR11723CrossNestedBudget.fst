module Z3PR11723CrossNestedBudget
open FStar.List.Tot

type st = { budget:nat; exc:bool }

(* cross_nested::checkpoint(cost): inc(cost) modeled as budget test; failure sets m_limit_exceeded *)
let ck (c:nat) (s:st) : bool & st =
  if (not s.exc) && s.budget >= c then (true, {budget = s.budget - c; exc = s.exc})
  else (false, {s with exc = true})

let rec orig_div (j:nat) (rows: list (list nat)) : bool =
  match rows with [] -> true | r::t -> mem j r && orig_div j t

let rec divides (j:nat) (rows: list (list nat)) (s:st) : bool & st =
  match rows with
  | [] -> (true, s)
  | r::t ->
    let (ok, s1) = ck (length r) s in
    if not ok then (false, s1)
    else if mem j r then divides j t s1 else (false, s1)

let rec orig_hcf (vars: list nat) (rows: list (list nat)) : bool =
  match vars with [] -> false | j::t -> orig_div j rows || orig_hcf t rows

(* has_common_factor over ch[1..]; returns false immediately on exhaustion *)
let rec hcf (vars: list nat) (rows: list (list nat)) (s:st) : bool & st =
  match vars with
  | [] -> (false, s)
  | j::t ->
    let (b, s1) = divides j rows s in
    if b then (true, s1) else if s1.exc then (false, s1) else hcf t rows s1

(* O3: exhaustion flag is monotone *)
let rec divides_mono (j:nat) rows (s:st)
  : Lemma (ensures s.exc ==> (snd (divides j rows s)).exc) (decreases rows) =
  match rows with [] -> () | r::t ->
    let (ok,s1) = ck (length r) s in
    if ok && mem j r then divides_mono j t s1 else ()

(* O1: divides never returns a spurious answer unless flagged exhausted *)
let rec divides_sound (j:nat) rows (s:st)
  : Lemma (ensures (let (b,s') = divides j rows s in
                    (b ==> orig_div j rows) /\ ((not b) /\ (not s'.exc) ==> not (orig_div j rows))))
          (decreases rows) =
  match rows with [] -> () | r::t ->
    let (ok,s1) = ck (length r) s in
    if ok && mem j r then divides_sound j t s1 else ()

(* O2: hcf true => original true; hcf false with no exhaustion => original false *)
let rec hcf_sound (vars: list nat) rows (s:st)
  : Lemma (ensures (let (b,s') = hcf vars rows s in
                    (b ==> orig_hcf vars rows) /\ ((not b) /\ (not s'.exc) ==> not (orig_hcf vars rows))))
          (decreases vars) =
  match vars with [] -> () | j::t ->
    divides_sound j rows s;
    let (b,s1) = divides j rows s in
    if b || s1.exc then () else hcf_sound t rows s1

(* split_with_var guard after PR: proceeds only if not exhausted and no common factor *)
let split_proceeds (hb:bool) (exc:bool) : bool = not (hb || exc)

let split_guard_sound (vars: list nat) rows (s:st)
  : Lemma (let (b,s') = hcf vars rows s in
           split_proceeds b s'.exc ==> not (orig_hcf vars rows)) =
  hcf_sound vars rows s
