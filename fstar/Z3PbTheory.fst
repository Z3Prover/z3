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
       arbitrary (nonnegative-coefficient) remainder.

   Deferred to a future follow-up pass (see PB_REWRITER_REPORT.md):
   the gcd-based cutting-plane reduction, the `k/n <= ... < k/(n-1)`
   coefficient-range normalization heuristic, `mk_app_core`'s general
   (non-unit) slack-based conjunction/disjunction/recursive-`mk_ge`
   construction, and the `translate_pb2lia`/`mk_validate_rewrite`
   self-validation infrastructure (not itself a rewrite rule).
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
