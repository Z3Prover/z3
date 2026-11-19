module Z3OptIteSumPr11585
(* Semantic model of src/opt/opt_context.cpp is_min_max_of_sums at head 4a53e6b8.
   c_i are the values of the 0/1-ite sums; N is num_thresholds. *)
open FStar.List.Tot

let rec count (p: pos -> bool) (n: nat) : nat =
  if n = 0 then 0 else count p (n - 1) + (if p n then 1 else 0)

let rec maxl (cs: list nat) : nat = match cs with [] -> 0 | c :: t -> if c > maxl t then c else maxl t
let rec minl (cs: list nat) : nat = match cs with [] -> 0 | [c] -> c | c :: t -> if c < minl t then c else minl t

(* minimization: forall i, k in 1..N. c_i >= k => p_k *)
let feas_min (cs: list nat) (n: nat) (p: pos -> bool) =
  forall (c: nat) (k: pos). memP c cs /\ k <= n /\ c >= k ==> p k
(* maximization: forall i, k in 1..N. p_k => c_i >= k *)
let feas_max (cs: list nat) (n: nat) (p: pos -> bool) =
  forall (c: nat) (k: pos). memP c cs /\ k <= n /\ p k ==> c >= k

let rec maxl_ge (cs: list nat) (c: nat) : Lemma (requires memP c cs) (ensures c <= maxl cs) =
  match cs with [] -> () | h :: t -> if h = c then () else maxl_ge t c
let rec maxl_mem (cs: list nat) : Lemma (requires Cons? cs) (ensures memP (maxl cs) cs) =
  match cs with [_] -> () | h :: t -> maxl_mem t
let rec minl_le (cs: list nat) (c: nat) : Lemma (requires memP c cs) (ensures minl cs <= c) =
  match cs with [] -> () | [_] -> () | h :: t -> if h = c then () else minl_le t c
let rec minl_mem (cs: list nat) : Lemma (requires Cons? cs) (ensures memP (minl cs) cs) =
  match cs with [_] -> () | h :: t -> minl_mem t

(* count of a predicate true exactly on 1..m, restricted to 1..n, is min m n *)
let rec count_prefix (m: nat) (n: nat) : Lemma (ensures count (fun k -> k <= m) n = (if m < n then m else n)) =
  if n = 0 then () else count_prefix m (n - 1)

let rec count_mono (p q: pos -> bool) (n: nat)
  : Lemma (requires forall k. k <= n /\ p k ==> q k) (ensures count p n <= count q n) =
  if n = 0 then () else count_mono p q (n - 1)

(* O1: minimization. Canonical p_k = (k <= max c) is feasible with sum = max c;
   every feasible p has sum >= max c (needs max c <= N, from c_i <= len_i <= max_cardinality). *)
let o1_canonical_feasible (cs: list nat) (n: nat)
  : Lemma (requires Cons? cs /\ maxl cs <= n)
          (ensures feas_min cs n (fun k -> k <= maxl cs) /\ count (fun k -> k <= maxl cs) n = maxl cs) =
  count_prefix (maxl cs) n;
  let aux (c: nat) (k: pos) : Lemma (requires memP c cs /\ k <= n /\ c >= k) (ensures k <= maxl cs) = maxl_ge cs c in
  FStar.Classical.forall_intro_2 (fun c k -> FStar.Classical.move_requires_2 aux c k)

let o1_lower_bound (cs: list nat) (n: nat) (p: pos -> bool)
  : Lemma (requires Cons? cs /\ maxl cs <= n /\ feas_min cs n p) (ensures count p n >= maxl cs) =
  maxl_mem cs;
  count_prefix (maxl cs) n;
  count_mono (fun k -> k <= maxl cs) p n

(* O2: maximization with N = min length; min c <= N. Canonical p_k = (k <= min c). *)
let o2_canonical_feasible (cs: list nat) (n: nat)
  : Lemma (requires Cons? cs /\ minl cs <= n)
          (ensures feas_max cs n (fun k -> k <= minl cs) /\ count (fun k -> k <= minl cs) n = minl cs) =
  count_prefix (minl cs) n;
  let aux (c: nat) (k: pos) : Lemma (requires memP c cs /\ k <= n /\ k <= minl cs) (ensures c >= k) = minl_le cs c in
  FStar.Classical.forall_intro_2 (fun c k -> FStar.Classical.move_requires_2 aux c k)

let o2_upper_bound (cs: list nat) (n: nat) (p: pos -> bool)
  : Lemma (requires Cons? cs /\ minl cs <= n /\ feas_max cs n p) (ensures count p n <= minl cs) =
  minl_mem cs;
  count_prefix (minl cs) n;
  count_mono p (fun k -> k <= minl cs) n

(* O3: range fact justifying the threshold bounds: a sum of 0/1 terms is <= its length. *)
let rec sum01 (bs: list (n:nat{n <= 1})) : nat = match bs with [] -> 0 | b :: t -> b + sum01 t
let rec sum01_le_len (bs: list (n:nat{n <= 1})) : Lemma (ensures sum01 bs <= length bs) =
  match bs with [] -> () | _ :: t -> sum01_le_len t

(* Combined: x = sum p_k together with the min-feasibility gives x >= every c_i (original bound). *)
let o4_bound_preserved (cs: list nat) (n: nat) (p: pos -> bool) (c: nat)
  : Lemma (requires Cons? cs /\ maxl cs <= n /\ feas_min cs n p /\ memP c cs) (ensures count p n >= c) =
  o1_lower_bound cs n p; maxl_ge cs c
