(*
   Z3StoiTheory.fst

   Soundness proofs for the `str.to_int`/`str.from_int` (itos/stoi)
   axioms of src/ast/seq/seq_axioms.cpp (`seq::axioms::itos_axiom`,
   `stoi_axiom`). These axioms relate a Z3 string to the (mathematical)
   natural number it spells out in decimal, so unlike the rest of the
   seq_axioms.cpp development (which stays at the abstract `seq a`
   level), a concrete digit model is needed here:

     - `digit`      : the refined element type 0..9 ("a decimal digit").
     - `digits_of_nat`/`nat_of_digits` : the (MSB-first) round-trip
       between a `nat` and its canonical digit-sequence spelling,
       giving a ground-truth model of `str.from_int` on `seq digit`.
     - `stoi_core`  : a generic left-to-right parse of an arbitrary
       character sequence into an int, parametrized by an abstract
       `is_digit`/`digit_val` pair (mirroring Z3's `is_digit`/
       `mk_digit2int`), giving a ground-truth model of `str.to_int`
       for *any* element type, not just `digit` itself.

   Not covered (documented, not formalized):
     - `stoi_axiom_re` (seq_axioms.cpp, regex-based non-negativity via
       membership in `[0-9]+`): a variant encoding of the same
       `stoi(s) >= 0 <=> ...` fact via `Z3RegexMembership`'s `in_re`
       rather than character-by-character recursion; out of scope here.
     - `stoi_axiom(e,k)`/`itos_axiom(s,k)` (the exact-length-k
       overloads, seq_axioms.cpp ~900+): these only refine *how* the
       same `stoi`/`itos` values are computed incrementally (via a
       Skolemized `seq.stoi(s,i)` family for bounded unrolling), not
       *what* they compute; `stoi_core`/`itos` above already pin down
       the latter.
*)
module Z3StoiTheory

open Z3SeqTheory
open Z3SeqRewrites

(* ================================================================= *)
(* Digits and their round-trip with naturals                           *)
(* ================================================================= *)

type digit = d:int{0 <= d /\ d <= 9}

let rec pow10 (k:nat) : Tot nat (decreases k) =
  if k = 0 then 1 else 10 * pow10 (k - 1)

let lemma_pow10_succ (k:nat)
  : Lemma (ensures pow10 (k + 1) == 10 * pow10 k)
  = ()

(* MSB-first decimal spelling of a natural number; always nonempty
   (itos(0) = "0", a single '0' digit, not the empty string). *)
let rec digits_of_nat (n:nat) : Tot (seq digit) (decreases n)
  = if n < 10 then unit (n <: digit)
    else concat (digits_of_nat (n / 10)) (unit ((n % 10) <: digit))

let rec lemma_digits_of_nat_nonempty (n:nat)
  : Lemma (ensures digits_of_nat n <> empty)
          (decreases n)
  = if n < 10 then ()
    else lemma_digits_of_nat_nonempty (n / 10)

(* The value spelled out by a (MSB-first) digit sequence. *)
let rec nat_of_digits (ds:seq digit) : Tot nat (decreases ds)
  = match ds with
    | [] -> 0
    | d :: ds' -> d * pow10 (len ds') + nat_of_digits ds'

(* Appending one more (least-significant) digit multiplies the running
   value by 10 and adds the new digit. *)
let rec lemma_nat_of_digits_append (ds:seq digit) (d:digit)
  : Lemma (ensures nat_of_digits (concat ds (unit d)) == 10 * nat_of_digits ds + d)
          (decreases ds)
  = match ds with
    | [] -> ()
    | x :: ds' ->
      lemma_nat_of_digits_append ds' d;
      lemma_len_concat ds' (unit d);
      lemma_pow10_succ (len ds')

(* Round-trip: spelling out `n` in decimal and reading it back gives
   `n` again. *)
let rec lemma_digits_of_nat_round_trip (n:nat)
  : Lemma (ensures nat_of_digits (digits_of_nat n) == n)
          (decreases n)
  = if n < 10 then ()
    else begin
      lemma_digits_of_nat_round_trip (n / 10);
      lemma_nat_of_digits_append (digits_of_nat (n / 10)) ((n % 10) <: digit)
    end

(* The canonical spelling of a positive number never starts with the
   digit 0 (no leading zeros); this is what distinguishes the
   canonical spelling from an arbitrary digit sequence that also
   round-trips to the same value. *)
let rec lemma_digits_of_nat_head_nonzero (n:nat{n > 0})
  : Lemma (ensures (match digits_of_nat n with
                     | d :: _ -> d <> 0
                     | [] -> False))
          (decreases n)
  = if n < 10 then ()
    else begin
      lemma_digits_of_nat_nonempty (n / 10);
      lemma_digits_of_nat_head_nonzero (n / 10)
    end

(* `itos` : seq_axioms.cpp's `str.from_int`, as a total function
   `int -> seq digit` (empty string for negative inputs). *)
let itos (n:int) : seq digit =
  if n < 0 then empty else digits_of_nat n

(* ================================================================= *)
(* itos_axiom, seq_axioms.cpp (`axioms::itos_axiom`)                    *)
(* ================================================================= *)

(* itos(n) = "" <=> n < 0. *)
let lemma_itos_empty_iff_neg (n:int)
  : Lemma (ensures (itos n == empty) == (n < 0))
  = if n >= 0 then lemma_digits_of_nat_nonempty n

(* len(itos(n)) >= 0 : trivial (lengths are natural numbers), included
   only for parity with the C++ clause `add_clause(mk_ge(mk_len(e),0))`. *)
let lemma_itos_len_nonneg (n:int)
  : Lemma (ensures len (itos n) >= 0)
  = ()

(* n = 0 ==> itos(n) = "0". *)
let lemma_itos_zero (n:int)
  : Lemma (requires n == 0)
          (ensures itos n == unit (0 <: digit))
  = ()

(* itos(n) does not start with "0" when n > 0 : i.e. whenever
   at(itos(n), 0) = "0", n must be 0. *)
let lemma_itos_no_leading_zero (n:int)
  : Lemma (requires n > 0)
          (ensures at (itos n) 0 <> unit (0 <: digit))
  = lemma_digits_of_nat_nonempty n;
    lemma_digits_of_nat_head_nonzero n

(* ================================================================= *)
(* stoi_core : a generic left-to-right digit-string parser, over any   *)
(* element type `a` equipped with an `is_digit`/`digit_val` pair       *)
(* (mirroring Z3's `is_digit`/`mk_digit2int`). This is the ground-     *)
(* truth model for `str.to_int` used to justify `stoi_axiom`.          *)
(* ================================================================= *)

(* Accumulate digits left-to-right (MSB first); -1 permanently once a
   non-digit character is seen (matching seq_axioms.cpp's
   `stoi(s,i-1) < 0 ==> stoi(s,i) = -1` propagation). *)
let rec stoi_acc (#a:eqtype) (is_digit:a -> bool) (digit_val:(c:a{is_digit c}) -> digit)
                  (s:seq a) (acc:int)
  : Tot int (decreases s)
  = match s with
    | [] -> acc
    | c :: s' ->
      if not (is_digit c) then -1
      else stoi_acc is_digit digit_val s' (10 * acc + digit_val c)

let stoi_core (#a:eqtype) (is_digit:a -> bool) (digit_val:(c:a{is_digit c}) -> digit)
              (s:seq a)
  : int
  = match s with
    | [] -> -1
    | c :: s' -> if not (is_digit c) then -1 else stoi_acc is_digit digit_val s' (digit_val c)

(* ================================================================= *)
(* stoi_axiom, seq_axioms.cpp (`axioms::stoi_axiom`)                    *)
(* ================================================================= *)

(* stoi_acc never produces a result below -1 (indeed, starting from a
   nonnegative accumulator it always stays nonnegative). *)
let rec lemma_stoi_acc_ge_m1 (#a:eqtype) (is_digit:a -> bool) (digit_val:(c:a{is_digit c}) -> digit)
                              (s:seq a) (acc:int)
  : Lemma (requires acc >= 0)
          (ensures stoi_acc is_digit digit_val s acc >= -1)
          (decreases s)
  = match s with
    | [] -> ()
    | c :: s' ->
      if not (is_digit c) then ()
      else lemma_stoi_acc_ge_m1 is_digit digit_val s' (10 * acc + digit_val c)

(* stoi(s) >= -1. *)
let lemma_stoi_ge_m1 (#a:eqtype) (is_digit:a -> bool) (digit_val:(c:a{is_digit c}) -> digit)
                      (s:seq a)
  : Lemma (ensures stoi_core is_digit digit_val s >= -1)
  = match s with
    | [] -> ()
    | c :: s' -> if not (is_digit c) then () else lemma_stoi_acc_ge_m1 is_digit digit_val s' (digit_val c)

(* stoi("") = -1. *)
let lemma_stoi_empty (#a:eqtype) (is_digit:a -> bool) (digit_val:(c:a{is_digit c}) -> digit)
  : Lemma (ensures stoi_core is_digit digit_val empty == -1)
  = ()

(* stoi(s) >= 0 ==> is_digit(nth(s,0)) /\ len(s) >= 1. *)
let lemma_stoi_nonneg_implies_first_digit
      (#a:eqtype) (is_digit:a -> bool) (digit_val:(c:a{is_digit c}) -> digit) (s:seq a)
  : Lemma (requires stoi_core is_digit digit_val s >= 0)
          (ensures len s >= 1 /\ is_digit (nth s 0))
  = match s with
    | [] -> ()
    | c :: s' -> ()

(* ================================================================= *)
(* Round-trip : stoi(itos(n)) = n for n >= 0, instantiated at the      *)
(* digit sequence itself (a := digit, is_digit = const true,           *)
(* digit_val = id). This is the Z3 clause                              *)
(*   "n >= 0 => stoi(itos(n)) = n"                                     *)
(* from `itos_axiom`.                                                  *)
(* ================================================================= *)

let digit_is_digit (_:digit) : bool = true
let digit_digit_val (c:digit{digit_is_digit c}) : digit = c

let stoi_d (s:seq digit) : int = stoi_core digit_is_digit digit_digit_val s

let rec lemma_stoi_acc_d_digits (ds:seq digit) (acc:nat)
  : Lemma (ensures stoi_acc digit_is_digit digit_digit_val ds acc
                   == acc * pow10 (len ds) + nat_of_digits ds)
          (decreases ds)
  = match ds with
    | [] -> ()
    | d :: ds' ->
      lemma_stoi_acc_d_digits ds' (10 * acc + d);
      lemma_pow10_succ (len ds')

let lemma_stoi_d_digits (ds:seq digit{ds <> empty})
  : Lemma (ensures stoi_d ds == nat_of_digits ds)
  = match ds with
    | d :: ds' -> lemma_stoi_acc_d_digits ds' d

let lemma_itos_stoi_round_trip (n:int)
  : Lemma (requires n >= 0)
          (ensures stoi_d (itos n) == n)
  = lemma_digits_of_nat_nonempty n;
    lemma_stoi_d_digits (digits_of_nat n);
    lemma_digits_of_nat_round_trip n
