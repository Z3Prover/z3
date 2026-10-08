module Z3PbTheory

(*
   F star formalization of the core truth-preserving normalization
   identities in src/ast/rewriter/pb_rewriter.cpp /
   src/ast/rewriter/pb_rewriter_def.h -- Z3's pseudo-Boolean (PB)
   constraint rewriter.

   A PB constraint `c_1*l_1 + c_2*l_2 + ... + c_n*l_n >= k` (after
   `mk_app_core` normalizes `<=`/at-most-k into `>=`/at-least-k by
   negating coefficients and `k`) is modeled here as a list of
   (coefficient, 0/1-literal-value) pairs plus a threshold `k`, all over
   `int` (mirroring the `.cpp`'s `rational` coefficients, specialized to
   the integer case `normalize` itself reduces to). We prove that several
   of `unique`/`normalize`/`mk_app_core`'s rewriting steps preserve the
   truth value of the constraint for every Boolean assignment to the
   literals:

     - `unique`'s negative-coefficient flip (`c*l + rest >= k` becomes
       `-c*(not l) + rest >= k - c`);
     - `normalize`'s trivial-true detection (`k <= 0`) and trivial-false /
       infeasibility detection (`sum of coefficients < k`);
     - `normalize`'s "tight inequality" step (`sum of coefficients = k`
       implies the constraint holds iff *every* literal is true) -- which
       also directly justifies `mk_app_core`'s final `slack == k` /
       `all_unit && k == sz` branches (`mk_and`);
     - `mk_app_core`'s `all_unit && k == 1` branch (`mk_or`): with unit
       coefficients, `sum >= 1` iff at least one literal is true;
     - `normalize`'s "ensure the largest coefficient is not larger than
       k" capping step, for a single selected coefficient against an
       arbitrary (nonnegative-coefficient) remainder;
     - `normalize`'s `g.is_zero()` branch (all coefficients equal `k`):
       `sum k*l_i >= k` iff at least one literal is true, generalizing
       the unit-coefficient case to an arbitrary positive common
       coefficient;
     - `normalize`'s coefficient-range heuristic (`k/n <= ... <
       k/(n-1)`): if every coefficient lies in `[lo,hi]` and `n*hi < k
       <= (n+1)*lo`, the constraint holds iff at least `n+1` literals
       are true, justifying the collapse of every coefficient to `1`;
     - `normalize`'s gcd-based cutting-plane reduction: for `g > 1`,
       `k > 0`, with every coefficient either equal to `k` or an exact
       multiple of `g`, replacing each `c == k` coefficient by
       `ceil_div k g` and each other coefficient `c` by `c / g`
       (and `k` by `ceil_div k g`) preserves the constraint's truth
       value.

   Deferred to a future follow-up pass (see PB_REWRITER_REPORT.md):
   `mk_app_core`'s general (non-unit) slack-based conjunction/
   disjunction/recursive-`mk_ge` construction, and the
   `translate_pb2lia`/`mk_validate_rewrite` self-validation
   infrastructure (not itself a rewrite rule).
*)

(* ----------------------------------------------------------------- *)
(* Representation                                                     *)
(* ----------------------------------------------------------------- *)

/// A single PB term: an integer coefficient paired with a literal's
/// current 0/1 (Boolean) value.
type pb_arg = int & bool

/// The value contributed by one term: `c` if the literal is true, `0`
/// otherwise -- i.e. `c * (if x then 1 else 0)`.
let term_val (c:int) (x:bool) : int = if x then c else 0

/// The value of a PB sum `c_1*l_1 + ... + c_n*l_n` under a fixed
/// assignment (the booleans paired with each coefficient).
let rec pb_sum (args:list pb_arg) : int =
  match args with
  | [] -> 0
  | (c, x) :: tl -> term_val c x + pb_sum tl

/// The sum of all coefficients, i.e. the value of the PB sum when every
/// literal is assigned true (its maximum achievable value, assuming all
/// coefficients are nonnegative).
let rec coeff_sum (args:list pb_arg) : int =
  match args with
  | [] -> 0
  | (c, _) :: tl -> c + coeff_sum tl

let rec all_nonneg (args:list pb_arg) : prop =
  match args with
  | [] -> True
  | (c, _) :: tl -> c >= 0 /\ all_nonneg tl

let rec all_pos (args:list pb_arg) : prop =
  match args with
  | [] -> True
  | (c, _) :: tl -> c > 0 /\ all_pos tl

let rec all_true (args:list pb_arg) : prop =
  match args with
  | [] -> True
  | (_, x) :: tl -> x == true /\ all_true tl

let rec any_true (args:list pb_arg) : prop =
  match args with
  | [] -> False
  | (_, x) :: tl -> x == true \/ any_true tl

let rec all_unit (args:list pb_arg) : prop =
  match args with
  | [] -> True
  | (c, _) :: tl -> c == 1 /\ all_unit tl

/// Positive coefficients are in particular nonnegative.
let rec lemma_all_pos_nonneg (args:list pb_arg{all_pos args})
  : Lemma (ensures all_nonneg args) (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl -> lemma_all_pos_nonneg tl

(* ----------------------------------------------------------------- *)
(* `unique`'s negative-coefficient flip                                *)
(* ----------------------------------------------------------------- *)

/// `c*l + rest >= k  <=>  (-c)*(not l) + rest >= k - c` -- `unique`'s
/// rewrite of a negative-coefficient literal into a positive-coefficient
/// negated literal (`args[i].first = negate(l); k -= c; args[i].second =
/// -c`). A purely local algebraic identity: `term_val (-c) (not x) ==
/// c - term_val c x` for every `c`/`x`, so adding the same `rest` and
/// comparing to `k` vs. `k - c` is the same inequality shifted by `c` on
/// both sides.
let lemma_negate_flip (c:int) (x:bool) (rest k:int)
  : Lemma ((term_val c x + rest >= k) <==> (term_val (-c) (not x) + rest >= k - c))
  = ()

(* ----------------------------------------------------------------- *)
(* Basic bounds: 0 <= pb_sum <= coeff_sum (nonnegative coefficients)   *)
(* ----------------------------------------------------------------- *)

let rec lemma_pb_sum_nonneg (args:list pb_arg{all_nonneg args})
  : Lemma (ensures pb_sum args >= 0) (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl -> lemma_pb_sum_nonneg tl

let rec lemma_pb_sum_le_total (args:list pb_arg{all_nonneg args})
  : Lemma (ensures pb_sum args <= coeff_sum args) (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl -> lemma_pb_sum_le_total tl

(* ----------------------------------------------------------------- *)
(* `normalize`'s trivial-true / trivial-false (infeasibility) detection *)
(* ----------------------------------------------------------------- *)

/// `normalize`: `k <= 0` (non-equality constraints) makes the constraint
/// a tautology, since a sum of nonnegative-coefficient terms is always
/// `>= 0 >= k`.
let lemma_trivial_true (args:list pb_arg{all_nonneg args}) (k:int{k <= 0})
  : Lemma (pb_sum args >= k)
  = lemma_pb_sum_nonneg args

/// `normalize`: `sum of coefficients < k` makes the constraint
/// unsatisfiable, since the sum can never exceed the total of its
/// (nonnegative) coefficients.
let lemma_trivial_false (args:list pb_arg{all_nonneg args}) (k:int{coeff_sum args < k})
  : Lemma (~ (pb_sum args >= k))
  = lemma_pb_sum_le_total args

(* ----------------------------------------------------------------- *)
(* `normalize`'s "tight inequality" step / `mk_app_core`'s `slack == k`  *)
(* and `all_unit && k == sz` branches (`mk_and`)                       *)
(* ----------------------------------------------------------------- *)

/// With strictly positive coefficients summing to exactly `k`, the
/// constraint `pb_sum >= k` holds iff *every* literal is true: any single
/// false literal already drops the achievable sum strictly below the
/// total (hence below `k`), and conversely setting every literal true
/// reaches the sum exactly.
let rec lemma_tight_iff_all_true (args:list pb_arg{all_pos args})
  : Lemma (ensures (pb_sum args >= coeff_sum args) <==> all_true args) (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl ->
      lemma_all_pos_nonneg tl;
      lemma_pb_sum_le_total tl;
      lemma_tight_iff_all_true tl

(* ----------------------------------------------------------------- *)
(* `mk_app_core`'s `all_unit && k == 1` branch (`mk_or`)               *)
(* ----------------------------------------------------------------- *)

/// With all-unit coefficients, `pb_sum >= 1` iff at least one literal is
/// true -- exactly `mk_app_core`'s `all_unit && k.is_one()` fast path
/// rewriting the constraint to `mk_or(args)`.
/// Unit coefficients are in particular nonnegative.
let rec lemma_all_unit_nonneg (args:list pb_arg{all_unit args})
  : Lemma (ensures all_nonneg args) (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl -> lemma_all_unit_nonneg tl

let rec lemma_unit_at_least_one (args:list pb_arg{all_unit args})
  : Lemma (ensures (pb_sum args >= 1) <==> any_true args) (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl ->
      lemma_all_unit_nonneg tl;
      lemma_pb_sum_nonneg tl;
      lemma_unit_at_least_one tl

(* ----------------------------------------------------------------- *)
(* `normalize`'s "ensure the largest coefficient is not larger than k"  *)
(* capping step, for a single selected term                            *)
(* ----------------------------------------------------------------- *)

let min_int (a b:int) : int = if a < b then a else b

/// Capping a single term's coefficient `c` down to `k` (when `c >= k >
/// 0`) preserves the truth value of `>= k` against an arbitrary
/// nonnegative-coefficient remainder: if the literal is true, both the
/// original (`c >= k`) and capped (`k`) contributions alone already meet
/// the threshold against the nonnegative remainder; if the literal is
/// false, both contribute `0` and the comparison reduces to the same
/// `rest >= k`.
let lemma_cap_single (c:int) (k:int{k > 0}) (x:bool) (rest:int{rest >= 0})
  : Lemma (requires c >= k)
          (ensures (term_val c x + rest >= k) <==> (term_val (min_int c k) x + rest >= k))
  = ()

/// Lifted to the head of a PB-term list: capping the head coefficient
/// (when it is `>= k > 0`) preserves the truth value of the whole
/// constraint, since the (nonnegative-coefficient) tail's contribution is
/// always `>= 0` (`lemma_pb_sum_nonneg`).
let lemma_cap_head (c:int) (k:int{k > 0}) (x:bool) (tl:list pb_arg{all_nonneg tl})
  : Lemma (requires c >= k)
          (ensures (pb_sum ((c, x) :: tl) >= k) <==> (pb_sum ((min_int c k, x) :: tl) >= k))
  = lemma_pb_sum_nonneg tl;
    lemma_cap_single c k x (pb_sum tl)

(* ----------------------------------------------------------------- *)
(* `normalize`'s "all coefficients equal to k" branch (`g.is_zero()`)  *)
(* ----------------------------------------------------------------- *)

/// A degenerate special case of the gcd cutting-plane step: when
/// *every* coefficient equals the threshold `k` itself (the loop
/// computing `g` never updates it, since it only accumulates over
/// terms with `c != k`), the constraint `sum k*l_i >= k` (for `k > 0`)
/// holds iff at least one literal is true -- exactly `normalize`'s
/// `g.is_zero()` branch, replacing every coefficient by `1` and `k` by
/// `1`. This generalizes `lemma_unit_at_least_one` from a fixed unit
/// coefficient `1` to an arbitrary positive coefficient `k`.
let rec all_coeff_eq (k:int) (args:list pb_arg) : prop =
  match args with
  | [] -> True
  | (c, _) :: tl -> c == k /\ all_coeff_eq k tl

let rec lemma_all_coeff_eq_nonneg (k:int{k >= 0}) (args:list pb_arg{all_coeff_eq k args})
  : Lemma (ensures all_nonneg args) (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl -> lemma_all_coeff_eq_nonneg k tl

let rec lemma_all_coeff_eq_at_least_one (k:int{k > 0}) (args:list pb_arg{all_coeff_eq k args})
  : Lemma (ensures (pb_sum args >= k) <==> any_true args) (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl ->
      lemma_all_coeff_eq_nonneg k tl;
      lemma_pb_sum_nonneg tl;
      lemma_all_coeff_eq_at_least_one k tl

(* ----------------------------------------------------------------- *)
(* `normalize`'s coefficient-range heuristic (`k/n <= ... < k/(n-1)`)   *)
(* ----------------------------------------------------------------- *)

/// The number of true literals in a PB-term list -- the quantity
/// `normalize`'s range heuristic ultimately reduces the constraint to a
/// threshold on, once every coefficient is collapsed to `1`.
let rec count_true (args:list pb_arg) : int =
  match args with
  | [] -> 0
  | (_, x) :: tl -> (if x then 1 else 0) + count_true tl

let rec all_in_range (lo hi:int) (args:list pb_arg) : prop =
  match args with
  | [] -> True
  | (c, _) :: tl -> lo <= c /\ c <= hi /\ all_in_range lo hi tl

/// Every true literal contributes at most `hi` and every (true or
/// false) literal contributes at most `hi` times its 0/1 indicator, so
/// the whole sum is bounded by `hi * count_true` (the predicate's lower
/// bound `lo` is irrelevant to this direction; it is carried only so
/// the hypothesis matches `all_in_range`'s one combined predicate).
let rec lemma_pb_sum_le_max_count (lo hi:int) (args:list pb_arg{all_in_range lo hi args})
  : Lemma (ensures pb_sum args <= hi * count_true args) (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl -> lemma_pb_sum_le_max_count lo hi tl

/// Dually, every true literal contributes at least `lo` (and every
/// coefficient is `>= lo` by `all_in_range`), so the whole sum is
/// bounded below by `lo * count_true`.
let rec lemma_pb_sum_ge_min_count (lo hi:int) (args:list pb_arg{all_in_range lo hi args})
  : Lemma (ensures pb_sum args >= lo * count_true args) (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl -> lemma_pb_sum_ge_min_count lo hi tl

/// The core soundness argument for `normalize`'s coefficient-range
/// collapse: if every coefficient lies in `[lo,hi]` (`lo > 0`) and the
/// range is narrow enough relative to `k` that `n*hi < k <= (n+1)*lo`
/// for some `n`, then the constraint `sum >= k` holds iff *at least*
/// `n+1` of the literals are true -- regardless of which specific
/// literals those are (only their count matters), because any `t <= n`
/// true literals can contribute at most `t*hi <= n*hi < k`, while any
/// `t >= n+1` true literals already contribute at least `t*lo >=
/// (n+1)*lo >= k`. This is exactly `normalize`'s final step: when `n1
/// == n2` (`floor(k/max) == ceil(k/min) - 1`) it replaces every
/// coefficient by `1` and `k` by `n1 + 1`.
let lemma_range_collapse (lo hi:int{lo > 0 /\ hi >= lo}) (n:int{n >= 0}) (k:int)
    (args:list pb_arg{all_in_range lo hi args})
  : Lemma (requires n * hi < k /\ k <= (n + 1) * lo)
          (ensures (pb_sum args >= k) <==> (count_true args >= n + 1))
  = lemma_pb_sum_le_max_count lo hi args;
    lemma_pb_sum_ge_min_count lo hi args;
    let t = count_true args in
    (* `hi >= lo > 0` (from `all_in_range`'s first term, if any; vacuously
       for `[]`, where both sides of the goal are immediate) lets Z3's
       linear-arithmetic-with-known-sign multiplication handle
       `t <= n ==> hi * t <= hi * n` and `t >= n + 1 ==> lo * t >=
       lo * (n + 1)` once `hi`/`lo`'s nonnegativity is in scope; spelling
       out the two directions explicitly avoids relying on it finding
       the case split on its own. *)
    if t <= n then begin
      assert (hi * t <= hi * n)
    end else begin
      assert (t >= n + 1);
      assert (lo * t >= lo * (n + 1))
    end
    (* `count_true args <= n` gives `pb_sum args <= hi * count_true args
       <= hi * n < k` (strict, from the hypothesis), so `pb_sum >= k`
       forces `count_true args >= n + 1`; conversely `count_true args >=
       n + 1` gives `pb_sum args >= lo * count_true args >= lo * (n + 1)
       >= k` (from the hypothesis). Both directions of the `<==>` follow
       from these two linear facts plus `count_true`'s integrality
       (always either `<= n` or `>= n + 1`), all within Z3's linear
       integer arithmetic reach. *)

(* ----------------------------------------------------------------- *)
(* `normalize`'s gcd-based cutting-plane reduction                     *)
(* ----------------------------------------------------------------- *)

/// The ceiling of `k / g` for positive `k`, `g` -- `normalize`'s
/// `k_new` (`div(k,g)`, incremented when `k % g <> 0`).
let ceil_div (k:int{k > 0}) (g:int{g > 0}) : int = (k + g - 1) / g

/// `g * ceil_div(k,g) >= k`, and this is the least such multiple of
/// `g`: `g * (ceil_div(k,g) - 1) < k`. The defining property that makes
/// `ceil_div` the right replacement threshold.
let lemma_ceil_div_spec (k:int{k > 0}) (g:int{g > 0})
  : Lemma (ensures g * ceil_div k g >= k /\ g * (ceil_div k g - 1) < k)
  = ()

/// The scalar cutting-plane identity: for a nonnegative multiple `g*m`
/// of `g > 0`, `g*m >= k <=> m >= ceil_div(k,g)`. This is the single
/// arithmetic fact the whole list-level reduction below reduces to.
let lemma_ceil_div_iff (k:int{k > 0}) (g:int{g > 0}) (m:int)
  : Lemma (ensures (g * m >= k) <==> (m >= ceil_div k g))
  = lemma_ceil_div_spec k g

/// `cut_coeff g k c` is `normalize`'s per-coefficient rewrite: a
/// coefficient equal to `k` becomes the new threshold `ceil_div(k,g)`
/// (that single literal, alone, was already enough to satisfy the
/// original constraint, so it must remain, alone, enough to satisfy the
/// new one); any other coefficient (always an exact multiple of `g`,
/// by construction of `g` as the gcd of exactly those coefficients) is
/// divided by `g`.
let cut_coeff (g:int{g > 0}) (k:int{k > 0}) (c:int) : int =
  if c = k then ceil_div k g else c / g

let rec cut_args (g:int{g > 0}) (k:int{k > 0}) (args:list pb_arg) : list pb_arg =
  match args with
  | [] -> []
  | (c, x) :: tl -> (cut_coeff g k c, x) :: cut_args g k tl

/// The side condition `normalize` maintains on every coefficient before
/// applying the cutting-plane step: either it equals `k` exactly
/// (handled by the `ceil_div` branch above), or it is a positive exact
/// multiple of `g` (`c % g == 0`, so `cut_coeff`'s division is exact,
/// with no rounding/truncation loss).
let rec cuttable (g:int{g > 0}) (k:int) (args:list pb_arg) : prop =
  match args with
  | [] -> True
  | (c, _) :: tl -> c > 0 /\ (c == k \/ c % g == 0) /\ cuttable g k tl

/// Decomposing `pb_sum` by whether each term's coefficient equals `k`:
/// the terms with `c = k` contribute `k` times their true-count, and
/// the remaining terms contribute their own (unscaled) sum -- a
/// routine additive regrouping, needed to isolate the single global
/// application of `lemma_ceil_div_iff` from the per-term bookkeeping.
let rec k_true_count (k:int) (args:list pb_arg) : int =
  match args with
  | [] -> 0
  | (c, x) :: tl -> (if c = k && x then 1 else 0) + k_true_count k tl

let rec rest_sum (k:int) (args:list pb_arg) : int =
  match args with
  | [] -> 0
  | (c, x) :: tl -> (if c = k then 0 else term_val c x) + rest_sum k tl

let rec lemma_pb_sum_decompose (k:int) (args:list pb_arg)
  : Lemma (ensures pb_sum args == k * k_true_count k args + rest_sum k args) (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl -> lemma_pb_sum_decompose k tl

/// `rest_sum` (the `c <> k` sub-sum) is always a nonnegative multiple of
/// `g`, under `cuttable` -- needed so dividing it by `g` loses no
/// information, and so `lemma_ceil_div_iff` applies to it directly.
let lemma_mod_add_zero (g:int{g > 0}) (a b:int)
  : Lemma (requires a % g == 0 /\ b % g == 0) (ensures (a + b) % g == 0)
  = FStar.Math.Lemmas.lemma_mod_plus_distr_l a b g

let rec lemma_rest_sum_multiple_of_g (g k:int{g > 0}) (args:list pb_arg{cuttable g k args})
  : Lemma (ensures rest_sum k args % g == 0 /\ rest_sum k args >= 0) (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl ->
      lemma_rest_sum_multiple_of_g g k tl;
      if c = k then ()
      else lemma_mod_add_zero g (term_val c x) (rest_sum k tl)

/// `cut_args`'s own `pb_sum` decomposes the same way, with the `c = k`
/// group now scaled by `ceil_div(k,g)` and the rest group exactly
/// divided by `g` -- matching `k_true_count`/`rest_sum`'s decomposition
/// of the original list, since `cut_coeff` preserves which terms are in
/// which group (`cut_coeff g k c = k <=>` false whenever `c <> k`,
/// since `ceil_div k g <> k` is not assumed in general, but `cut_args`'s
/// grouping below is read off the *original* `args`, not re-examined
/// post-cut, so no such assumption is needed).
let rec lemma_cut_pb_sum_decompose (g:int{g > 0}) (k:int{k > 0}) (args:list pb_arg{cuttable g k args})
  : Lemma (ensures pb_sum (cut_args g k args)
                   == ceil_div k g * k_true_count k args + rest_sum k args / g)
          (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl ->
      lemma_cut_pb_sum_decompose g k tl;
      lemma_rest_sum_multiple_of_g g k tl
      (* `rest_sum k tl == g * q` for some `q`, so `rest_sum k tl / g ==
         q` exactly (no truncation), and prepending one more term either
         adds `ceil_div k g` to both the `k`-group count and sum (if
         `c = k`) or adds one more exact-multiple-of-`g` term `c`,
         with `c / g` on the cut side matching `(c + rest_sum k tl) / g
         == c/g + rest_sum k tl / g` by exact divisibility of both
         summands -- routine integer-division arithmetic Z3 discharges
         directly. *)

/// The main cutting-plane theorem: under `cuttable g k args` (`g > 1`,
/// `k > 0`), `normalize`'s division step preserves the truth value of
/// the constraint for every Boolean assignment:
/// ```
/// pb_sum args >= k  <=>  pb_sum (cut_args g k args) >= ceil_div k g
/// ```
/// Proof: decompose both sums via `lemma_pb_sum_decompose`/
/// `lemma_cut_pb_sum_decompose` into a "`k`-group" part (scaled by `k`
/// vs. `ceil_div k g`, with the *same* true-count `A` on both sides,
/// since `cut_args` never changes which literals are true) and a
/// "rest" part (exactly `g`-scaled). If `A >= 1`, both sides are
/// unconditionally true (`k*A >= k` and `ceil_div(k,g)*A >= ceil_div
/// k g`, since both `k` and `ceil_div k g` are positive, and the
/// nonnegative rest/rest-divided-by-g summand only helps); if `A ==
/// 0`, both sides reduce to exactly `lemma_ceil_div_iff`'s scalar fact
/// applied to the (nonnegative, exactly-`g`-divisible) rest sum.
let rec lemma_k_true_count_nonneg (k:int) (args:list pb_arg)
  : Lemma (ensures k_true_count k args >= 0) (decreases args)
  = match args with
    | [] -> ()
    | (c, x) :: tl -> lemma_k_true_count_nonneg k tl

let lemma_cutting_plane (g k:int{g > 1 /\ k > 0}) (args:list pb_arg{cuttable g k args})
  : Lemma (ensures (pb_sum args >= k) <==> (pb_sum (cut_args g k args) >= ceil_div k g))
  = lemma_pb_sum_decompose k args;
    lemma_cut_pb_sum_decompose g k args;
    lemma_rest_sum_multiple_of_g g k args;
    lemma_ceil_div_iff k g (rest_sum k args / g);
    lemma_ceil_div_spec k g;
    lemma_k_true_count_nonneg k args;
    let kn = ceil_div k g in
    let a = k_true_count k args in
    let r = rest_sum k args in
    (* `kn` is strictly positive: `g * (kn - 1) < k` and `k > 0` force
       `kn > 0` whenever `g * (kn - 1) < k <= g * kn` could have
       `kn <= 0`, but then `g * (kn - 1) < 0 <= ...`; spelled out via
       `lemma_ceil_div_spec` together with `g > 0`. *)
    if a >= 1 then begin
      assert (k * a >= k);
      assert (kn * a >= kn)
    end else
      assert (a = 0)
    (* With `a >= 1`: `pb_sum args == k*a + r >= k` (since `k*a>=k`,
       `r>=0`) and `pb_sum (cut_args...) == kn*a + r/g >= kn` (since
       `kn*a>=kn`, `r/g>=0`, both from the two assertions above combined
       with the nonnegativity facts already in scope) -- both sides of
       the goal `<==>` hold unconditionally, so the biconditional is
       trivially true. With `a == 0`: `pb_sum args == r` and
       `pb_sum (cut_args...) == r/g`, so the goal reduces to exactly
       `lemma_ceil_div_iff k g (r/g)` (`r = g*(r/g)` exactly, since
       `lemma_rest_sum_multiple_of_g` gives `r % g == 0`), already
       invoked above. *)
