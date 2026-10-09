(*
   Z3SeqRewrites.fst

   Statements and F* proofs of equality-preservation for the core
   rewrite rules of Z3's sequence rewriter,
   src/ast/rewriter/seq_rewriter.cpp, with respect to the
   axiomatization in Z3SeqTheory.fst.

   Each lemma below is annotated with the Z3 function and rule (and, 
   where applicable, source comment) that it formalizes.
*)
module Z3SeqRewrites

open Z3SeqTheory

(* ================================================================= *)
(* Helper lemmas (structural properties needed by the rules below)    *)
(* ================================================================= *)

(* concat is associative.
   Z3: seq_rewriter.cpp mk_seq_concat, comment "(a + b) + c = a + (b + c)" *)
let rec lemma_concat_assoc (#a:eqtype) (s t u:seq a)
  : Lemma (concat (concat s t) u == concat s (concat t u))
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_concat_assoc s' t u

(* s ++ [] == s.
   Z3: seq_rewriter.cpp mk_seq_concat, comment "a + \"\" = a" *)
let rec lemma_concat_empty_r (#a:eqtype) (s:seq a)
  : Lemma (concat s empty == s)
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_concat_empty_r s'

(* [] ++ s == s.
   Z3: seq_rewriter.cpp mk_seq_concat, comment "\"\" + a = a" *)
let lemma_concat_empty_l (#a:eqtype) (s:seq a)
  : Lemma (concat empty s == s)
  = ()

(* ================================================================= *)
(* Length                                                              *)
(* ================================================================= *)

(* len(a ++ b) = len(a) + len(b).
   Z3: mk_seq_length flattens str.++ and sums lengths of the pieces. *)
let rec lemma_len_concat (#a:eqtype) (s t:seq a)
  : Lemma (len (concat s t) == len s + len t)
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_len_concat s' t

(* len(unit x) = 1. Z3: mk_seq_length base case via min_length. *)
let lemma_len_unit (#a:eqtype) (x:a)
  : Lemma (len (unit x) == 1)
  = ()

(* len(empty) = 0. *)
let lemma_len_empty (#a:eqtype)
  : Lemma (len (empty #a) == 0)
  = ()

(* len(s^n) = n * len(s) for n >= 0.
   Z3: mk_seq_length, comment "len(s^n) = n * len(s) for n >= 0" *)
let rec lemma_len_power_nat (#a:eqtype) (s:seq a) (n:nat)
  : Lemma (len (power_nat s n) == n * len s)
  = if n = 0 then ()
    else begin
      lemma_len_power_nat s (n - 1);
      lemma_len_concat s (power_nat s (n - 1))
    end

let lemma_len_power (#a:eqtype) (s:seq a) (n:int)
  : Lemma (requires n >= 0) (ensures len (power s n) == n * len s)
  = if n = 0 then () else lemma_len_power_nat s n

(* ================================================================= *)
(* power                                                               *)
(* ================================================================= *)

(* s^n = empty, for n <= 0.
   Z3: mk_seq_power, "s^n = \"\" if n <= 0" *)
let lemma_power_nonpos (#a:eqtype) (s:seq a) (n:int)
  : Lemma (requires n <= 0) (ensures power s n == empty)
  = ()

(* s^1 = s.
   Z3: mk_seq_power, special-cased via `is_num && n.is_one()`. *)
let lemma_power_one (#a:eqtype) (s:seq a)
  : Lemma (power s 1 == s)
  = lemma_concat_empty_r s

(* power distributes over addition of (natural) exponents:
   s^(k1+k2) = s^k1 ++ s^k2. Auxiliary lemma used to justify
   (s^k)^n = s^(k*n). *)
let rec lemma_power_nat_add (#a:eqtype) (s:seq a) (k1 k2:nat)
  : Lemma (power_nat s (k1 + k2) == concat (power_nat s k1) (power_nat s k2))
  = if k1 = 0 then ()
    else begin
      lemma_power_nat_add s (k1 - 1) k2;
      lemma_concat_assoc s (power_nat s (k1 - 1)) (power_nat s k2)
    end

(* (s^k)^n = s^(k*n), for k, n >= 0.
   Z3: mk_seq_power, comment "(s^k)^n = s^(k*n) whenever k or n is a
   positive numeral" -- we prove the natural-number case which covers
   all instances where the rewrite actually fires (both exponents are
   numerals at rewrite time). *)
let rec lemma_power_mul (#a:eqtype) (s:seq a) (k n:nat)
  : Lemma (power_nat (power_nat s k) n == power_nat s (k * n))
  = if n = 0 then ()
    else begin
      lemma_power_mul s k (n - 1);
      lemma_power_nat_add s k (k * (n - 1))
    end

(* ================================================================= *)
(* extract / substr                                                   *)
(* ================================================================= *)

(* pos < 0 or ln <= 0 ==> extract s pos ln = empty.
   Z3: mk_seq_extract, "case 1: pos < 0 or len <= 0 -> rewrite to \"\"" *)
let lemma_extract_neg_or_nonpos_len (#a:eqtype) (s:seq a) (pos ln:int)
  : Lemma (requires pos < 0 || ln <= 0) (ensures extract s pos ln == empty)
  = ()

(* pos >= len s ==> extract s pos ln = empty.
   Z3: mk_seq_extract, "case 1.1: pos >= length(base) -> rewrite to \"\"" *)
let rec lemma_extract_pos_ge_len (#a:eqtype) (s:seq a) (pos ln:int)
  : Lemma (requires pos >= len s) (ensures extract s pos ln == empty)
  = if pos < 0 || ln <= 0 then ()
    else
      match s with
      | [] -> ()
      | _ :: s' -> lemma_extract_pos_ge_len s' (pos - 1) ln

(* extract s 0 (len s) = s: an extract spanning the whole sequence is
   the identity. Auxiliary lemma used below (replace / prefix). *)
let rec lemma_extract_full (#a:eqtype) (s:seq a)
  : Lemma (extract_nat s 0 (len s) == s)
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_extract_full s'

(* extract s pos 1 = at s pos, for 0 <= pos < len s.
   Z3: mk_seq_extract, "if (constantLen && len == 1) result = str().mk_at(a,b)" *)
let rec lemma_extract_len1_is_at (#a:eqtype) (s:seq a) (pos:int)
  : Lemma (requires 0 <= pos /\ pos < len s)
          (ensures extract s pos 1 == at s pos)
  = match s with
    | x :: s' -> if pos = 0 then () else lemma_extract_len1_is_at s' (pos - 1)

(* extract_nat s pos 0 == empty, for any pos. *)
let rec lemma_extract_nat_zero_len (#a:eqtype) (s:seq a) (pos:nat)
  : Lemma (extract_nat s pos 0 == empty)
  = match s with
    | [] -> ()
    | _ :: s' -> if pos > 0 then lemma_extract_nat_zero_len s' (pos - 1) else ()

(* ---- take/drop algebra, used to prove extract composition ---- *)

(* extract_nat s pos ln == take (drop s pos) ln : `extract` is exactly
   "drop the first `pos` elements, then take the next `ln`". *)
let rec lemma_extract_nat_eq_take_drop (#a:eqtype) (s:seq a) (pos ln:nat)
  : Lemma (extract_nat s pos ln == take (drop s pos) ln)
  = match s with
    | [] -> ()
    | x :: s' ->
      if pos > 0 then lemma_extract_nat_eq_take_drop s' (pos - 1) ln
      else if ln = 0 then ()
      else lemma_extract_nat_eq_take_drop s' 0 (ln - 1)

(* drop (drop s m) n == drop s (m + n). *)
let rec lemma_drop_drop (#a:eqtype) (s:seq a) (m n:nat)
  : Lemma (drop (drop s m) n == drop s (m + n))
  = if m = 0 then ()
    else
      match s with
      | [] -> ()
      | _ :: s' -> lemma_drop_drop s' (m - 1) n

(* take (take s m) n == take s (min m n). *)
let rec lemma_take_take (#a:eqtype) (s:seq a) (m n:nat)
  : Lemma (take (take s m) n == take s (if m < n then m else n))
  = match s with
    | [] -> ()
    | _ :: s' ->
      if m = 0 then ()
      else if n = 0 then ()
      else lemma_take_take s' (m - 1) (n - 1)

(* m <= n ==> drop (take s n) m == take (drop s m) (n - m). *)
let rec lemma_drop_take_comm (#a:eqtype) (s:seq a) (n m:nat)
  : Lemma (requires m <= n) (ensures drop (take s n) m == take (drop s m) (n - m))
  = match s with
    | [] -> ()
    | _ :: s' ->
      if n = 0 then ()
      else if m = 0 then ()
      else lemma_drop_take_comm s' (n - 1) (m - 1)

(* extract (extract s p1 l1) p2 l2 = extract s (p1+p2) (min (l1-p2) l2)
   whenever 0 <= p2 <= l1 (and 0 <= p1).
   Z3: mk_seq_extract,
     "// pos2 <= len1 // 0 <= pos1
      // extract(extract(x, pos1, len1), pos2, len2)
      // = extract(x, pos1 + pos2, min(len1 - pos2, len2))"

   Proved via the take/drop algebra above:
     extract s p1 l1              == take (drop s p1) l1
     extract (..) p2 l2           == take (drop (take (drop s p1) l1) p2) l2
     drop (take (drop s p1) l1) p2 == take (drop (drop s p1) p2) (l1 - p2)
     drop (drop s p1) p2          == drop s (p1 + p2)
     take (take u (l1-p2)) l2     == take u (min (l1-p2) l2)              *)
let lemma_extract_compose_nat
    (#a:eqtype) (s:seq a) (p1:nat) (l1:nat) (p2:nat) (l2:nat)
  : Lemma (requires p2 <= l1)
          (ensures
            extract_nat (extract_nat s p1 l1) p2 l2
            == extract_nat s (p1 + p2) (if l1 - p2 < l2 then l1 - p2 else l2))
  = lemma_extract_nat_eq_take_drop s p1 l1;
    lemma_extract_nat_eq_take_drop (take (drop s p1) l1) p2 l2;
    lemma_drop_take_comm (drop s p1) l1 p2;
    lemma_drop_drop s p1 p2;
    lemma_take_take (drop s (p1 + p2)) (l1 - p2) l2;
    lemma_extract_nat_eq_take_drop s (p1 + p2) (if l1 - p2 < l2 then l1 - p2 else l2)

let lemma_extract_compose
    (#a:eqtype) (s:seq a) (p1 l1 p2 l2:int)
  : Lemma (requires p1 >= 0 /\ l1 > 0 /\ p2 >= 0 /\ p2 <= l1 /\ l2 > 0)
          (ensures
            extract (extract s p1 l1) p2 l2
            == extract s (p1 + p2) (if l1 - p2 < l2 then l1 - p2 else l2))
  = lemma_extract_compose_nat s p1 l1 p2 l2;
    assert (extract s p1 l1 == extract_nat s p1 l1);
    assert (extract (extract_nat s p1 l1) p2 l2 == extract_nat (extract_nat s p1 l1) p2 l2);
    let ln2 = if l1 - p2 < l2 then l1 - p2 else l2 in
    if ln2 <= 0 then begin
      assert (ln2 = 0);
      lemma_extract_nat_zero_len s (p1 + p2);
      assert (extract_nat s (p1 + p2) ln2 == empty);
      assert (extract s (p1 + p2) ln2 == empty)
    end else
      assert (extract s (p1 + p2) ln2 == extract_nat s (p1 + p2) ln2)

(* ---- length of an extract (general position) ---- *)

(* pos <= len s ==> len(extract_nat s pos ln) = min(ln, len s - pos). *)
let rec lemma_len_extract_nat (#a:eqtype) (s:seq a) (pos:nat) (ln:nat)
  : Lemma (requires pos <= len s)
          (ensures len (extract_nat s pos ln) == (if ln < len s - pos then ln else len s - pos))
  = match s with
    | [] -> ()
    | _ :: s' ->
      if pos > 0 then lemma_len_extract_nat s' (pos - 1) ln
      else if ln = 0 then ()
      else lemma_len_extract_nat s' 0 (ln - 1)

(* len(extract(x, 0, z)) = min(z, len(x)), for z >= 0.
   Z3: mk_seq_length, comment "len(extract(x, 0, z)) = min(z, len(x))" *)
let lemma_len_extract_from_zero (#a:eqtype) (s:seq a) (z:int)
  : Lemma (requires z >= 0)
          (ensures len (extract s 0 z) == (if z < len s then z else len s))
  = if z = 0 then ()
    else begin
      assert (extract s 0 z == extract_nat s 0 z);
      lemma_len_extract_nat s 0 z
    end

(* ---- element access through an extract ---- *)

(* pos + i < len s /\ i < ln ==> nth(extract_nat s pos ln) i = nth s (pos+i).
   Z3: mk_seq_nth, comment
     "nth(s[k, |s| - k], b) = ... b + k < |s| -> nth(s, b + k) ..." *)
let rec lemma_nth_extract_nat (#a:eqtype) (s:seq a) (pos:nat) (ln:nat) (i:nat{i < len (extract_nat s pos ln)})
  : Lemma (requires pos + i < len s)
          (ensures nth (extract_nat s pos ln) i == nth s (pos + i))
  = match s with
    | x :: s' ->
      if pos > 0 then lemma_nth_extract_nat s' (pos - 1) ln i
      else if i = 0 then ()
      else lemma_nth_extract_nat s' 0 (ln - 1) (i - 1)

(* pos < len s /\ ln > 0 ==> extract_nat s pos ln is nonempty. *)
let rec lemma_extract_nat_nonempty (#a:eqtype) (s:seq a) (pos:nat) (ln:nat)
  : Lemma (requires pos < len s /\ ln > 0) (ensures len (extract_nat s pos ln) > 0)
  = match s with
    | _ :: s' -> if pos > 0 then lemma_extract_nat_nonempty s' (pos - 1) ln else ()

(* ================================================================= *)
(* at                                                                  *)
(* ================================================================= *)

(* i < 0 or i >= len s ==> at s i = empty.
   Z3: mk_seq_at, "(str.at s i), constants s/i, i < 0 or i >= |s| ==>
   (str.at s i) = \"\"" *)
let lemma_at_oob (#a:eqtype) (s:seq a) (i:int)
  : Lemma (requires i < 0 \/ i >= len s) (ensures at s i == empty)
  = ()

(* 0 <= i < len s ==> at s i = unit (nth s i). This is the defining
   equation of `at`, restated as a standalone lemma for use in proofs
   that go through `at` abstractly. *)
let lemma_at_in_range (#a:eqtype) (s:seq a) (i:int)
  : Lemma (requires 0 <= i /\ i < len s) (ensures at s i == unit (nth s i))
  = ()

(* nth (unit x) 0 == x.
   Z3: mk_seq_nth, "if (str().is_unit(a,s) && pos1.is_zero()) result = s",
   and mk_seq_nth_i's loop base case for the unit at offset 0. *)
let lemma_nth_unit (#a:eqtype) (x:a)
  : Lemma (nth (unit x) 0 == x)
  = ()

(* ================================================================= *)
(* first / rest / last / butlast                                      *)
(*                                                                      *)
(* mk_seq_first/rest/last/butlast (seq_rewriter.cpp 653-736) all        *)
(* assume |t| > 0 and reduce to `at`/`extract` on the underlying        *)
(* sequence whenever t itself is (syntactically) an `extract`. These    *)
(* reductions are exactly the following `nth`/`extract`-of-`extract`    *)
(* identities.                                                          *)
(* ================================================================= *)

(* first(extract(s,pos,ln)) = at(s,pos), for 0 <= pos < len s, ln > 0.
   Z3: mk_seq_first, "if t = substring(s,j,..) then simplifies to
   nth(s,j)" *)
let lemma_first_of_extract (#a:eqtype) (s:seq a) (pos ln:int)
  : Lemma (requires 0 <= pos /\ pos < len s /\ ln > 0)
          (ensures at (extract s pos ln) 0 == at s pos)
  = assert (extract s pos ln == extract_nat s pos ln);
    lemma_extract_nat_nonempty s pos ln;
    lemma_at_in_range (extract s pos ln) 0;
    lemma_nth_extract_nat s pos ln 0;
    lemma_at_in_range s pos

(* rest(extract(s,pos,ln)) = extract(s,pos+1,ln-1), for pos >= 0, ln > 0.
   Z3: mk_seq_rest, "if t = substring(s,j,k) then simplifies to
   substring(s,j+1,k-1)".

   An immediate corollary of `lemma_extract_compose` (p2 = 1); the
   ln = 1 edge case (both sides empty) is handled separately since
   `lemma_extract_compose` requires l2 > 0. *)
let lemma_rest_of_extract (#a:eqtype) (s:seq a) (pos ln:int)
  : Lemma (requires pos >= 0 /\ ln > 0)
          (ensures extract (extract s pos ln) 1 (ln - 1) == extract s (pos + 1) (ln - 1))
  = if ln = 1 then ()
    else lemma_extract_compose s pos ln 1 (ln - 1)

(* last(extract(s,pos,ln)) = at(s, pos+ln-1), when the extract reaches
   exactly the end of s, i.e. ln = len s - pos (pos < len s).
   Z3: mk_seq_last, "if t = substring(s,j,k), j >= 0, k = |s|-j then
   simplifies to nth(s,|s|-1)" *)
let lemma_last_of_extract (#a:eqtype) (s:seq a) (pos ln:int)
  : Lemma (requires 0 <= pos /\ pos < len s /\ ln == len s - pos)
          (ensures at (extract s pos ln) (ln - 1) == at s (len s - 1))
  = assert (extract s pos ln == extract_nat s pos ln);
    lemma_len_extract_nat s pos ln;
    // len (extract_nat s pos ln) == ln, so index (ln - 1) is in range
    lemma_at_in_range (extract s pos ln) (ln - 1);
    lemma_nth_extract_nat s pos ln (ln - 1);
    lemma_at_in_range s (len s - 1)

(* butlast(extract(s,pos,ln)) = extract(s,pos,ln-1), for ln > 0.
   Z3: mk_seq_butlast always computes extract(t,0,len(t)-1); when t
   itself is extract(s,pos,ln) this is an instance of
   `lemma_extract_compose` (p2 = 0), i.e. "drop the last element of an
   extract". The code comment notes this is *not* a case the rewriter
   special-cases (unlike first/rest/last above) -- it is included here
   for completeness and because it reuses the same composition lemma. *)
let lemma_butlast_of_extract (#a:eqtype) (s:seq a) (pos ln:int)
  : Lemma (requires pos >= 0 /\ ln > 1)
          (ensures extract (extract s pos ln) 0 (ln - 1) == extract s pos (ln - 1))
  = lemma_extract_compose s pos ln 0 (ln - 1)

(* ================================================================= *)
(* reverse                                                             *)
(* ================================================================= *)

(* reverse (unit x) = unit x: a one-element sequence is its own reverse.
   Z3: mk_seq_reverse, "a one-element sequence is its own reverse" *)
let lemma_reverse_unit (#a:eqtype) (x:a)
  : Lemma (reverse (unit x) == unit x)
  = ()

(* reverse(a ++ b) = reverse(b) ++ reverse(a). *)
let rec lemma_reverse_concat (#a:eqtype) (s t:seq a)
  : Lemma (reverse (concat s t) == concat (reverse t) (reverse s))
  = match s with
    | [] -> lemma_concat_empty_r (reverse t)
    | x :: s' ->
      lemma_reverse_concat s' t;
      lemma_concat_assoc (reverse t) (reverse s') (unit x)

(* reverse(reverse(s)) = s.
   Z3: mk_seq_reverse computes an involutive operation on concatenations
   of units / string literals; this is the semantic justification. *)
let rec lemma_reverse_reverse (#a:eqtype) (s:seq a)
  : Lemma (reverse (reverse s) == s)
  = match s with
    | [] -> ()
    | x :: s' ->
      lemma_reverse_concat (reverse s') (unit x);
      lemma_reverse_reverse s'

(* ================================================================= *)
(* prefix / suffix                                                     *)
(* ================================================================= *)

(* is_prefix empty s.
   Z3: mk_seq_prefix, "if (str().is_empty(a)) result = true" *)
let lemma_prefix_empty (#a:eqtype) (s:seq a)
  : Lemma (is_prefix empty s == true)
  = ()

(* is_prefix p [] <=> p == []. Auxiliary characterization. *)
let lemma_prefix_of_empty (#a:eqtype) (p:seq a)
  : Lemma (is_prefix p empty == (p = empty))
  = match p with
    | [] -> ()
    | _ :: _ -> ()

(* is_prefix s s (reflexivity). *)
let rec lemma_prefix_reflexive (#a:eqtype) (s:seq a)
  : Lemma (is_prefix s s == true)
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_prefix_reflexive s'

(* is_prefix a (a ++ b).
   Z3: implicit in str.prefixof semantics / used by several rewrites,
   e.g. mk_seq_prefix's case `a == a1` returning true, and
   mk_seq_contains's `str().is_extract(b,x,y,z) && x == a` case. *)
let rec lemma_prefix_concat_intro (#a:eqtype) (s t:seq a)
  : Lemma (is_prefix s (concat s t) == true)
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_prefix_concat_intro s' t

(* is_prefix p s reconstructs s: s == p ++ (drop s (len p)) whenever p
   is a prefix of s. Auxiliary lemma used for `replace`. *)
let rec lemma_prefix_extract_reconstruct (#a:eqtype) (p s:seq a)
  : Lemma (requires is_prefix p s) (ensures s == concat p (drop s (len p)))
  = match p with
    | [] -> ()
    | _ :: p' ->
      (match s with
       | _ :: s' -> lemma_prefix_extract_reconstruct p' s')

(* is_suffix empty s.
   Z3: mk_seq_suffix, "if (str().is_empty(a)) result = true" (`a` is
   the needle in mk_seq_suffix(a,b)). *)
let lemma_suffix_empty (#a:eqtype) (s:seq a)
  : Lemma (is_suffix empty s == true)
  = ()

(* is_suffix b (a ++ b).
   Z3: dual of lemma_prefix_concat_intro, used implicitly wherever
   str.suffixof is reduced on a known concatenation. *)
let lemma_suffix_concat_intro (#a:eqtype) (s t:seq a)
  : Lemma (is_suffix t (concat s t) == true)
  = lemma_reverse_concat s t;
    lemma_prefix_concat_intro (reverse t) (reverse s)

(* ================================================================= *)
(* contains                                                            *)
(* ================================================================= *)

(* contains s empty.
   Z3: mk_seq_contains, "if (bs.empty()) { result = true }" *)
let lemma_contains_empty_needle (#a:eqtype) (s:seq a)
  : Lemma (contains s empty == true)
  = lemma_prefix_empty s

(* contains empty t <=> t == empty.
   Z3: mk_seq_contains, "if (as.empty()) { result = is_empty(b) }" *)
let lemma_contains_empty_haystack (#a:eqtype) (t:seq a)
  : Lemma (contains empty t == (t = empty))
  = lemma_prefix_of_empty t

(* A sequence contains any of its own prefixes-of-a-suffix, i.e. any
   contiguous sub-block obtained via `extract`/`drop`+`take`.
   Z3: mk_seq_contains, "if (str().is_extract(b, x, y, z) && x == a)
   { result = true }" -- `a` always contains `extract(a, y, z)`. *)
let rec lemma_drop_prefix_contains (#a:eqtype) (s t:seq a) (i:nat)
  : Lemma (requires i <= len s /\ is_prefix t (drop s i))
          (ensures contains s t)
  = if i = 0 then ()
    else
      match s with
      | _ :: s' -> lemma_drop_prefix_contains s' t (i - 1)

let rec lemma_take_is_prefix (#a:eqtype) (s:seq a) (n:nat)
  : Lemma (is_prefix (take s n) s == true)
  = match s with
    | [] -> ()
    | _ :: s' -> if n = 0 then () else lemma_take_is_prefix s' (n - 1)

let lemma_contains_extract (#a:eqtype) (s:seq a) (pos ln:int)
  : Lemma (contains s (extract s pos ln) == true)
  = if pos < 0 || ln <= 0 then lemma_contains_empty_needle s
    else if pos >= len s then begin
      lemma_extract_pos_ge_len s pos ln;
      lemma_contains_empty_needle s
    end else begin
      lemma_extract_nat_eq_take_drop s pos ln;
      lemma_take_is_prefix (drop s pos) ln;
      lemma_drop_prefix_contains s (take (drop s pos) ln) pos
    end

(* ================================================================= *)
(* replace                                                             *)
(* ================================================================= *)

(* replace s [] rep = rep ++ s.
   Z3: mk_seq_replace, "if (str().is_empty(b)) { result =
   str().mk_concat(c, a); }" *)
let lemma_replace_empty_pat (#a:eqtype) (s rep:seq a)
  : Lemma (replace s empty rep == concat rep s)
  = lemma_extract_full s

(* pat == rep ==> replace s pat rep = s.
   Z3: mk_seq_replace, "if (b == c) { result = a; }" *)
let rec lemma_replace_eq (#a:eqtype) (s pat:seq a)
  : Lemma (replace s pat pat == s)
  = if is_prefix pat s then lemma_prefix_extract_reconstruct pat s
    else
      match s with
      | [] -> ()
      | _ :: s' -> lemma_replace_eq s' pat

(* ~(contains s pat) /\ pat <> empty ==> replace s pat rep = s.
   Z3: mk_seq_replace falls through to BR_FAILED (left unrewritten,
   i.e. semantically unchanged) whenever `pat` does not occur in `s`. *)
let rec lemma_replace_not_contains (#a:eqtype) (s pat rep:seq a)
  : Lemma (requires (~ (contains s pat == true)))
          (ensures replace s pat rep == s)
  = if is_prefix pat s then lemma_prefix_concat_intro_contains_absurd s pat
    else
      match s with
      | [] -> ()
      | _ :: s' -> lemma_replace_not_contains s' pat rep

(* `is_prefix pat s` always implies `contains s pat`; used above to
   derive a contradiction from the hypothesis `~(contains s pat)`. *)
and lemma_prefix_concat_intro_contains_absurd (#a:eqtype) (s pat:seq a)
  : Lemma (requires is_prefix pat s /\ (~ (contains s pat == true)))
          (ensures False)
  = ()
