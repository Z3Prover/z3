module CardinalityRefactor
(* Model of is_lower_bound/is_upper_bound in context::is_min_max_of_sums
   (src/opt/opt_context.cpp, base 1a1d88d vs head 63737fe).
   Inputs: ok_shape = a.is_le/is_ge matched, xt = (x == term), marked = mark.is_marked(y),
   zo = is_zero_one(y), add = a.is_add(y), allzo = all_of(args, is_zero_one), n = num_args.
   State: (max, min) cardinality; result: option of new state (None = returns false). *)
type st = { mx: nat; mn: nat }

let old_pred (ok_shape xt marked zo add allzo: bool) (n: nat) (s: st) : option st =
  if not ok_shape then None
  else if not xt then None
  else if marked then None
  else if (not add) && (not zo) then None
  else if (not zo) && (not allzo) then None
  else
    let c = if zo then 1 else n in
    Some ({ mx = (if s.mx > c then s.mx else c); mn = (if s.mn < c then s.mn else c) })

let is_cardinality (marked zo add allzo: bool) (n: nat) (s: st) : option st =
  if marked then None
  else if (not zo) && (not add) then None
  else if (not zo) && (not allzo) then None
  else
    let c = if zo then 1 else n in
    Some ({ mx = (if s.mx > c then s.mx else c); mn = (if s.mn < c then s.mn else c) })

let new_pred (ok_shape xt marked zo add allzo: bool) (n: nat) (s: st) : option st =
  if ok_shape && xt then is_cardinality marked zo add allzo n s else None

(* Obligation 1/2: lower and upper bound refactorings are equivalent (same guards, same state update) *)
let equiv (a b c d e f: bool) (n: nat) (s: st)
  : Lemma (old_pred a b c d e f n s == new_pred a b c d e f n s) = ()

(* Obligation 3: accepted case implies the cardinality state invariant mn <= mx preserved/established
   when starting from the initial state is not assumed; instead: update never loses earlier maxima *)
let monotone (a b c d e f: bool) (n: nat) (s: st)
  : Lemma (match new_pred a b c d e f n s with
           | None -> True
           | Some s' -> s'.mx >= s.mx /\ s'.mn <= s.mn) = ()
