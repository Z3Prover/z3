(*
   Z3LenAbsTheory.fst

   A formalization of `src/util/len_abs.h`/`len_abs.cpp`'s ultimately
   periodic abstraction of a set of word lengths, and a proof that it
   is a sound over-approximation of the length set of a regular
   language (`Z3RegexTheory.fst`), connecting back to the same
   `lang a`/`re_*` combinators `Z3RegexInfo.fst` already formalizes
   `get_info`'s `nullable`/`[min_length, max_length]` fields against.

   Correspondence with `len_abs.h`:

     len_abs          ~  `len_abs { lo, hi, period, residues }`: the
                         concrete set this abstracts is
                         `{ n : lo <= n <= hi, (n mod period) in residues }`
                         (the class's own doc comment, verbatim).
     gamma            ~  the "containment Lambda subseteq value"
                         relation the header documents as the only
                         contract every operation must uphold.
     la_sound         ~  the length-set soundness contract `get_info`
                         itself is built on (`info_sound` in
                         Z3RegexInfo.fst, generalized from a plain
                         interval to this richer periodic domain).

   Representation simplification: `residues` is modeled as an
   unbounded predicate `nat -> prop` (exactly as `Z3RegexTheory.fst`'s
   `lang a = seq a -> prop` models a language) rather than a 64-bit
   bitmask, and `period` as an arbitrary positive `nat` rather than
   one capped at `len_abs::max_period = 64`. Both are
   implementation/storage constraints (so that `len_abs` fits in two
   machine words), not semantic ones; dropping them lets the
   abstraction's *mathematical* content be stated and proved without
   reproducing bit-level masking arithmetic.

   Scope reduction for `star`/`plus`/`loop`: the real `len_abs::gcd()`
   computes the tightest period for which every element of the
   abstracted set is a multiple, for an *arbitrary* residue pattern
   (e.g. period 6, residues {0,2,3,4} still has gcd 1, but period 4,
   residues {0} has gcd 4), via a bounded scan whose termination
   argument is itself a nontrivial periodic-set fact. This module
   instead takes the target period/gcd `g` as an explicit parameter
   together with the proof obligation `only_multiples_of abs g`
   ("every length `abs` contains is a multiple of `g`") -- i.e. it
   proves the soundness property `len_abs::gcd()` is *used for*
   generically, for whatever `g` a caller can justify, rather than
   reconstructing the scanning algorithm that finds the tightest such
   `g` from `(lo, hi, period, residues)` alone.
   `lemma_only_multiples_of_period` discharges this obligation for
   exactly the header's own motivating shape ("(a^4)* ... bounds
   [0, oo), yet |z| in 4N"): an abstraction whose only possible
   residue is 0.

   `concat`/`unite`/`meet`/`opt`, by contrast, are formalized in full
   generality (arbitrary periods and residue sets on both operands),
   matching `len_abs.cpp`'s own formulas up to the choice of common
   modulus: this module always combines via the *product* of the two
   periods (always a valid common multiple, see `bounded_lcm`'s doc
   comment in `len_abs.cpp` for why the real code prefers the tighter
   `lcm`/`gcd`-adaptive modulus instead) rather than the real
   `common_period`'s lcm-or-gcd choice -- again a precision, not a
   soundness, simplification: using a looser common multiple can only
   make the resulting residue set less selective, never cause it to
   omit a length that is actually reachable.
*)
module Z3LenAbsTheory

open Z3SeqTheory
open Z3RegexTheory
open Z3RegexBounds
open FStar.Math.Euclid
module Classical = FStar.Classical
module ML = FStar.Math.Lemmas

#set-options "--z3rlimit 40"

(* ----------------------------------------------------------------- *)
(* A plain, non-negative `gcd` on `nat`, and the divisibility-chaining *)
(* lemmas needed to propagate a per-operand periodicity fact through  *)
(* `unite`/`meet`/`concat`'s combined residue sets below -- this is    *)
(* the number-theoretic core of `len_abs::gcd()`'s *use*, even though  *)
(* the scanning algorithm that *computes* the tightest such value is   *)
(* still not reconstructed (see `la_period_for_star` further down).    *)
(* ----------------------------------------------------------------- *)

let gcd_witness (a b:nat) : int =
  let (_, _, d) = euclid_gcd a b in d

let lemma_gcd_witness_is_gcd (a b:nat) : Lemma (is_gcd a b (gcd_witness a b)) = ()

unfold let ngcd (a b:nat) : nat =
  let d = gcd_witness a b in
  if d >= 0 then d else -d

let lemma_is_gcd_negate (a b d:int)
  : Lemma (requires is_gcd a b d) (ensures is_gcd a b (-d))
  = let aux (x:int) : Lemma (requires x `divides` a /\ x `divides` b) (ensures x `divides` (-d)) =
      divides_minus x d
    in
    divides_opp d a;
    divides_opp d b;
    Classical.forall_intro (Classical.move_requires aux)

#push-options "--z3rlimit 50"
let lemma_ngcd_is_gcd (a b:nat) : Lemma (is_gcd a b (ngcd a b))
  = lemma_gcd_witness_is_gcd a b;
    let d = gcd_witness a b in
    if d < 0 then lemma_is_gcd_negate a b d
#pop-options

(* `ngcd a b` divides any `m` that `a` (resp. `b`) itself divides --
   used to propagate "every length is a multiple of `mult_a`" (or
   `mult_b`) facts down to "... a multiple of `ngcd mult_a mult_b`". *)
let lemma_ngcd_dvd_chain_l (am bm:pos) (m:nat)
  : Lemma (requires ngcd am bm > 0 /\ m % am == 0) (ensures m % (ngcd am bm) == 0)
  = lemma_ngcd_is_gcd am bm;
    mod_divides m am;
    divides_transitive (ngcd am bm) am m;
    divides_mod m (ngcd am bm)

let lemma_ngcd_dvd_chain_r (am bm:pos) (m:nat)
  : Lemma (requires ngcd am bm > 0 /\ m % bm == 0) (ensures m % (ngcd am bm) == 0)
  = lemma_ngcd_is_gcd am bm;
    mod_divides m bm;
    divides_transitive (ngcd am bm) bm m;
    divides_mod m (ngcd am bm)

(* If `ngcd am bm` divides a period `pa` (witnessed by `pa % am == 0`),
   it divides any product `pa * pc` too -- used to show the combined
   period `pa * pb` of `unite`/`meet`/`concat`'s result remains a
   multiple of the chosen combined `mult`. *)
let lemma_ngcd_dvd_period_l (am bm:pos) (pa pc:pos)
  : Lemma (requires ngcd am bm > 0 /\ pa % am == 0)
          (ensures (pa * pc) % (ngcd am bm) == 0)
  = lemma_ngcd_dvd_chain_l am bm pa;
    mod_divides pa (ngcd am bm);
    divides_mult_right pc pa (ngcd am bm);
    divides_mod (pc * pa) (ngcd am bm)

let lemma_ngcd_dvd_period_r (am bm:pos) (pb pc:pos)
  : Lemma (requires ngcd am bm > 0 /\ pb % bm == 0)
          (ensures (pc * pb) % (ngcd am bm) == 0)
  = lemma_ngcd_dvd_chain_r am bm pb;
    mod_divides pb (ngcd am bm);
    divides_mult_right pc pb (ngcd am bm);
    divides_mod (pc * pb) (ngcd am bm)

(* `(n % period) % mult == n % mult`, given `mult` divides `period` --
   the standard "project a finer modulus through a coarser one"
   identity, used to go from a residue-level fact (about `n % period`)
   to an `n`-level one (about `n` itself). *)
let lemma_mod_via_period (period mult:pos) (n:int)
  : Lemma (requires period % mult == 0)
          (ensures (n % period) % mult == n % mult)
  = ML.lemma_div_mod period mult;
    ML.modulo_modulo_lemma n mult (period / mult)

(* Sum of two multiples of `g` is a multiple of `g`. *)
let lemma_mod_add_zero (g:pos) (m n:nat)
  : Lemma (requires m % g == 0 /\ n % g == 0) (ensures (m + n) % g == 0)
  = ML.modulo_distributivity m n g

(* ----------------------------------------------------------------- *)
(* The abstract domain                                                 *)
(* ----------------------------------------------------------------- *)

(* A residue set is modeled as a predicate, exactly as `Z3RegexTheory
   .fst`'s `lang a = seq a -> prop` models a language: this is a purely
   mathematical specification of which length-residues are possible,
   not executable code, so there is no need to reproduce `len_abs.cpp`'s
   64-bit-bitmask representation here. *)
type residue_set = nat -> prop

noeq type len_abs = {
  la_lo       : nat;
  la_hi       : ebound;
  (* `1` ~ `is_trivial()`: no periodicity tracked, `la_residues`
     ignored (mirrors that `len_abs.cpp` only ever consults
     `m_residues` once `m_period > 1`). *)
  la_period   : pos;
  la_residues : residue_set;
  (* `0` ~ "no extra fact known"; else a value such that every length
     `a` contains is provably a multiple of `la_mult` -- a single
     extra divisibility fact, tracked alongside the main
     `(lo,hi,period,residues)` quadruple, that generalizes
     `la_period_for_star`'s old "exact singleton" special case to any
     chain of `unite`/`meet`/`concat`/`star`/`plus`/`loop` of
     already-periodic sub-expressions (see `la_mult_sound` below).
     This does *not* reconstruct `len_abs::gcd()`'s real multi-residue
     scan (which can find periods like `6` for `(aa)*|(aaa)*`'s
     `{0,2,3,4}` from first principles); it only ever propagates a
     *single* divisor fact compositionally. *)
  la_mult     : nat;
}

(* The concrete set of lengths `a` soundly contains, verbatim from
   `len_abs.h`'s own doc comment. *)
let gamma (a:len_abs) (n:nat) : prop =
  a.la_lo <= n /\ eb_le n a.la_hi /\
  (a.la_period <= 1 \/ a.la_residues (n % a.la_period))

(* The fact `len_abs::gcd()` is relied on to establish: every length
   `abs` contains is a multiple of `g`. (Relocated above `la_sound` so
   `la_mult_sound` below can refer to it.) *)
let only_multiples_of (abs:len_abs) (g:pos) : prop =
  forall (n:nat). gamma abs n ==> n % g == 0

(* Soundness of the extra `la_mult` divisibility fact. Deliberately
   stated at two different levels depending on `la_period`:
   - `la_period > 1`: a purely *structural*, window-independent fact
     about the residue formula itself (quantified over `r < period`,
     not over `gamma`/reachability) -- needed because `unite`/
     `meet`/`concat`'s combined residue formulas can admit lengths
     outside either operand's original `[lo,hi]` window, so a
     window-level (`only_multiples_of`) argument alone can't be
     transported compositionally across these binary combinators.
   - `la_period <= 1`: no residue formula is tracked at all, so we
     fall back to the simpler window-level `only_multiples_of`,
     sufficient for the non-periodic base cases (`la_exact`). *)
let la_mult_sound (abs:len_abs) : prop =
  abs.la_mult > 0 ==>
    (if abs.la_period > 1 then
       abs.la_period % abs.la_mult == 0 /\
       (forall (r:nat). r < abs.la_period ==> abs.la_residues r ==> r % abs.la_mult == 0)
     else
       only_multiples_of abs abs.la_mult)

(* "Soundness" of a `len_abs` relative to a language `l`: every word
   `l` accepts has a length `a` contains, and the extra `la_mult` fact
   (if any) soundly holds -- the length-set analogue of `info_sound`
   (Z3RegexInfo.fst), generalized to the periodic domain. *)
let la_sound (#a:eqtype) (abs:len_abs) (l:lang a) : prop =
  (forall (w:seq a). mem w l ==> gamma abs (len w)) /\ la_mult_sound abs

(* Monotonicity: an abstraction sound for `l` remains sound for any
   `l'` whose words are a subset of `l`'s -- used throughout
   `Z3RegexInfo.fst` to carry a sub-expression's `la` field through
   combinators (`inter`/`diff`/`xor`) whose result language is a
   subset of an operand's, without needing a dedicated `len_abs`
   combinator for each one. *)
let lemma_la_sound_monotone (#a:eqtype) (abs:len_abs) (l l':lang a)
  : Lemma (requires la_sound abs l /\ (forall (w:seq a). mem w l' ==> mem w l))
          (ensures la_sound abs l')
  = ()

(* ----------------------------------------------------------------- *)
(* `empty`/`exact`                                                    *)
(* ----------------------------------------------------------------- *)

let la_empty : len_abs = { la_lo = 1; la_hi = Bound 0; la_period = 1; la_residues = (fun _ -> False); la_mult = 0 }

let lemma_gamma_empty (n:nat) : Lemma (~(gamma la_empty n)) = ()

(* Every length this abstraction contains is exactly `n`, so (for
   `n > 0`) it is trivially a multiple of `n` itself -- the simplest
   non-zero `la_mult` fact, and exactly what lets `la_period_for_star`
   recover the header's `(a^4)*` motivating case. *)
let la_exact (n:nat) : len_abs = { la_lo = n; la_hi = Bound n; la_period = 1; la_residues = (fun _ -> False); la_mult = n }

(* A non-periodic abstraction carrying only a plain `[lo, hi]` bound
   -- the `len_abs` analogue of `Z3RegexInfo.fst`'s own
   `min_length`/`max_length` pair, used wherever no periodicity is
   tracked (e.g. `complement`, or any interval already established by
   other means). *)
let la_trivial (lo:nat) (hi:ebound) : len_abs =
  { la_lo = lo; la_hi = hi; la_period = 1; la_residues = (fun _ -> False); la_mult = 0 }

let lemma_la_trivial_sound (#a:eqtype) (lo:nat) (hi:ebound) (l:lang a)
  : Lemma (requires forall (w:seq a). mem w l ==> lo <= len w /\ eb_le (len w) hi)
          (ensures la_sound (la_trivial lo hi) l)
  = ()

let lemma_gamma_exact (n m:nat) : Lemma (gamma (la_exact n) m <==> m == n) = ()

(* ----------------------------------------------------------------- *)
(* `unite`                                                            *)
(* ----------------------------------------------------------------- *)

let la_unite (a b:len_abs) : len_abs =
  let lo = if a.la_lo <= b.la_lo then a.la_lo else b.la_lo in
  let hi = eb_max a.la_hi b.la_hi in
  if a.la_period <= 1 || b.la_period <= 1 then
    { la_lo = lo; la_hi = hi; la_period = 1; la_residues = (fun _ -> False); la_mult = 0 }
  else
    let q = a.la_period * b.la_period in
    let mult = if a.la_mult > 0 && b.la_mult > 0 then ngcd a.la_mult b.la_mult else 0 in
    { la_lo = lo; la_hi = hi; la_period = q;
      la_residues = (fun r -> a.la_residues (r % a.la_period) \/ b.la_residues (r % b.la_period));
      la_mult = mult }

(* Shared structural argument for `unite`'s/`meet`'s/`concat`'s `la_mult`:
   a length `r` that is known reachable via `abs1`'s own residue
   formula at `r % abs1.la_period` is a multiple of `abs1.la_mult`
   (straight from `abs1`'s own `la_mult_sound`), hence also a multiple
   of `ngcd abs1.la_mult abs2.la_mult`. *)
let lemma_mult_via_residue_l (abs1 abs2:len_abs) (r:nat)
  : Lemma (requires la_mult_sound abs1 /\ abs1.la_period > 1 /\ abs1.la_mult > 0 /\ abs2.la_mult > 0 /\
                    ngcd abs1.la_mult abs2.la_mult > 0 /\ abs1.la_residues (r % abs1.la_period))
          (ensures r % (ngcd abs1.la_mult abs2.la_mult) == 0)
  = lemma_mod_via_period abs1.la_period abs1.la_mult r;
    lemma_ngcd_dvd_chain_l abs1.la_mult abs2.la_mult r

let lemma_mult_via_residue_r (abs1 abs2:len_abs) (r:nat)
  : Lemma (requires la_mult_sound abs2 /\ abs2.la_period > 1 /\ abs1.la_mult > 0 /\ abs2.la_mult > 0 /\
                    ngcd abs1.la_mult abs2.la_mult > 0 /\ abs2.la_residues (r % abs2.la_period))
          (ensures r % (ngcd abs1.la_mult abs2.la_mult) == 0)
  = lemma_mod_via_period abs2.la_period abs2.la_mult r;
    lemma_ngcd_dvd_chain_r abs1.la_mult abs2.la_mult r

(* `la_mult_sound` of the combined period `q = p1 * p2`, whenever both
   operands' own `la_mult` facts are known. *)
let lemma_mult_period_combined (abs1 abs2:len_abs)
  : Lemma (requires la_mult_sound abs1 /\ la_mult_sound abs2 /\
                    abs1.la_period > 1 /\ abs2.la_period > 1 /\
                    abs1.la_mult > 0 /\ abs2.la_mult > 0 /\ ngcd abs1.la_mult abs2.la_mult > 0)
          (ensures (abs1.la_period * abs2.la_period) % (ngcd abs1.la_mult abs2.la_mult) == 0)
  = lemma_ngcd_dvd_period_l abs1.la_mult abs2.la_mult abs1.la_period abs2.la_period

(* `la_mult_sound` of `la_unite`'s result, isolated as its own lemma
   (rather than inlined into `lemma_la_unite_sound`) so the SMT query
   stays small and focused. *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 100"
let lemma_la_mult_unite (abs1 abs2:len_abs)
  : Lemma (requires la_mult_sound abs1 /\ la_mult_sound abs2)
          (ensures la_mult_sound (la_unite abs1 abs2))
  = if abs1.la_period > 1 && abs2.la_period > 1 && abs1.la_mult > 0 && abs2.la_mult > 0
       && ngcd abs1.la_mult abs2.la_mult > 0 then begin
      let q = abs1.la_period * abs2.la_period in
      let mult = ngcd abs1.la_mult abs2.la_mult in
      lemma_mult_period_combined abs1 abs2;
      let aux (r:nat)
        : Lemma (requires r < q /\ (abs1.la_residues (r % abs1.la_period) \/ abs2.la_residues (r % abs2.la_period)))
                (ensures r % mult == 0) =
        if abs1.la_residues (r % abs1.la_period) then lemma_mult_via_residue_l abs1 abs2 r
        else lemma_mult_via_residue_r abs1 abs2 r
      in
      Classical.forall_intro (Classical.move_requires aux);
      ML.lemma_mult_lt_left abs1.la_period 1 abs2.la_period;
      assert (q > 1);
      assert ((la_unite abs1 abs2).la_period == q);
      assert ((la_unite abs1 abs2).la_mult == mult);
      assert (forall (r:nat). (la_unite abs1 abs2).la_residues r <==>
                              (abs1.la_residues (r % abs1.la_period) \/ abs2.la_residues (r % abs2.la_period)));
      assert (forall (r:nat). r < q ==> (la_unite abs1 abs2).la_residues r ==> r % mult == 0)
    end
#pop-options

let lemma_la_unite_sound (#a:eqtype) (abs1 abs2:len_abs) (l1 l2:lang a)
  : Lemma (requires la_sound abs1 l1 /\ la_sound abs2 l2)
          (ensures la_sound (la_unite abs1 abs2) (re_union l1 l2))
  = let goal (w:seq a) : Lemma (requires mem w (re_union l1 l2)) (ensures gamma (la_unite abs1 abs2) (len w)) =
      if mem w l1 then begin
        if abs1.la_period > 1 && abs2.la_period > 1 then
          ML.modulo_modulo_lemma (len w) abs1.la_period abs2.la_period
      end else begin
        if abs1.la_period > 1 && abs2.la_period > 1 then
          ML.modulo_modulo_lemma (len w) abs2.la_period abs1.la_period
      end
    in
    Classical.forall_intro (Classical.move_requires goal);
    lemma_la_mult_unite abs1 abs2

(* ----------------------------------------------------------------- *)
(* `meet`                                                             *)
(* ----------------------------------------------------------------- *)

let la_meet (a b:len_abs) : len_abs =
  let lo = if a.la_lo >= b.la_lo then a.la_lo else b.la_lo in
  let hi = eb_min a.la_hi b.la_hi in
  if a.la_period <= 1 || b.la_period <= 1 then
    { la_lo = lo; la_hi = hi; la_period = 1; la_residues = (fun _ -> False); la_mult = 0 }
  else
    let q = a.la_period * b.la_period in
    let mult = if a.la_mult > 0 && b.la_mult > 0 then ngcd a.la_mult b.la_mult else 0 in
    { la_lo = lo; la_hi = hi; la_period = q;
      la_residues = (fun r -> a.la_residues (r % a.la_period) /\ b.la_residues (r % b.la_period));
      la_mult = mult }

(* `la_mult_sound` of `la_meet`'s result, isolated as its own lemma. *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 100"
let lemma_la_mult_meet (abs1 abs2:len_abs)
  : Lemma (requires la_mult_sound abs1 /\ la_mult_sound abs2)
          (ensures la_mult_sound (la_meet abs1 abs2))
  = if abs1.la_period > 1 && abs2.la_period > 1 && abs1.la_mult > 0 && abs2.la_mult > 0
       && ngcd abs1.la_mult abs2.la_mult > 0 then begin
      let q = abs1.la_period * abs2.la_period in
      let mult = ngcd abs1.la_mult abs2.la_mult in
      lemma_mult_period_combined abs1 abs2;
      let aux (r:nat)
        : Lemma (requires r < q /\ (abs1.la_residues (r % abs1.la_period) /\ abs2.la_residues (r % abs2.la_period)))
                (ensures r % mult == 0) =
        lemma_mult_via_residue_l abs1 abs2 r
      in
      Classical.forall_intro (Classical.move_requires aux);
      ML.lemma_mult_lt_left abs1.la_period 1 abs2.la_period;
      assert (q > 1);
      assert ((la_meet abs1 abs2).la_period == q);
      assert ((la_meet abs1 abs2).la_mult == mult);
      assert (forall (r:nat). (la_meet abs1 abs2).la_residues r <==>
                              (abs1.la_residues (r % abs1.la_period) /\ abs2.la_residues (r % abs2.la_period)))
    end
#pop-options

(* `meet` is sound for intersecting two abstractions of *the same*
   language: both bound/period/residue constraints survive, exactly
   `len_abs.h`'s own documented use ("combining two independently
   computed abstractions of the same language"). *)
let lemma_la_meet_sound (#a:eqtype) (abs1 abs2:len_abs) (l:lang a)
  : Lemma (requires la_sound abs1 l /\ la_sound abs2 l)
          (ensures la_sound (la_meet abs1 abs2) l)
  = let goal (w:seq a) : Lemma (requires mem w l) (ensures gamma (la_meet abs1 abs2) (len w)) =
      if abs1.la_period > 1 && abs2.la_period > 1 then begin
        ML.modulo_modulo_lemma (len w) abs1.la_period abs2.la_period;
        ML.modulo_modulo_lemma (len w) abs2.la_period abs1.la_period
      end
    in
    Classical.forall_intro (Classical.move_requires goal);
    lemma_la_mult_meet abs1 abs2

(* ----------------------------------------------------------------- *)
(* `opt`                                                              *)
(* ----------------------------------------------------------------- *)

let la_opt (a:len_abs) : len_abs =
  { la_lo = 0; la_hi = a.la_hi; la_period = a.la_period;
    la_residues = (fun r -> r == 0 \/ a.la_residues r);
    (* `la_opt`'s claimed set at `la_period <= 1` is the *whole*
       `[lo,hi]` interval (no periodicity filter), not just `{0, lo}`
       -- so `a`'s `la_mult` cannot be soundly reused there (e.g.
       `opt(exact n)`'s set is `[0,n]`, not uniformly divisible by
       `n`). Only propagate when `a` itself is genuinely periodic. *)
    la_mult = (if a.la_period > 1 then a.la_mult else 0) }

let lemma_la_mult_opt (abs:len_abs)
  : Lemma (requires la_mult_sound abs) (ensures la_mult_sound (la_opt abs))
  = if abs.la_period > 1 && abs.la_mult > 0 then begin
      let aux (r:nat) : Lemma (requires r < abs.la_period /\ (r == 0 \/ abs.la_residues r))
                               (ensures r % abs.la_mult == 0) = () in
      Classical.forall_intro (Classical.move_requires aux)
    end

let lemma_la_opt_sound (#a:eqtype) (abs:len_abs) (l:lang a)
  : Lemma (requires la_sound abs l) (ensures la_sound (la_opt abs) (re_opt l))
  = let goal (w:seq a) : Lemma (requires mem w (re_opt l)) (ensures gamma (la_opt abs) (len w)) = () in
    Classical.forall_intro (Classical.move_requires goal);
    lemma_la_mult_opt abs

(* ----------------------------------------------------------------- *)
(* `concat`                                                           *)
(* ----------------------------------------------------------------- *)

(* Convolution of the two (lifted) residue sets modulo the common
   period `q`: `r` is reachable iff it is `i + j` (mod `q`) for some
   reachable `i` from `a`'s residues and `j` from `b`'s. *)
let la_concat (a b:len_abs) : len_abs =
  let lo = a.la_lo + b.la_lo in
  let hi = eb_add a.la_hi b.la_hi in
  if a.la_period <= 1 || b.la_period <= 1 then
    { la_lo = lo; la_hi = hi; la_period = 1; la_residues = (fun _ -> False); la_mult = 0 }
  else
    let q = a.la_period * b.la_period in
    let conv (r:nat) : prop =
      exists (i:nat) (j:nat).
        i < q /\ j < q /\ a.la_residues (i % a.la_period) /\ b.la_residues (j % b.la_period) /\ (i + j) % q == r
    in
    let mult = if a.la_mult > 0 && b.la_mult > 0 then ngcd a.la_mult b.la_mult else 0 in
    { la_lo = lo; la_hi = hi; la_period = q; la_residues = conv; la_mult = mult }

#push-options "--fuel 4 --ifuel 4 --z3rlimit 100"
let lemma_la_mult_concat (abs1 abs2:len_abs)
  : Lemma (requires la_mult_sound abs1 /\ la_mult_sound abs2)
          (ensures la_mult_sound (la_concat abs1 abs2))
  = if abs1.la_period > 1 && abs2.la_period > 1 && abs1.la_mult > 0 && abs2.la_mult > 0
       && ngcd abs1.la_mult abs2.la_mult > 0 then begin
      let q = abs1.la_period * abs2.la_period in
      let mult = ngcd abs1.la_mult abs2.la_mult in
      lemma_mult_period_combined abs1 abs2;
      let aux (r:nat)
        : Lemma (requires r < q /\
                          (exists (i:nat) (j:nat).
                             i < q /\ j < q /\ abs1.la_residues (i % abs1.la_period) /\
                             abs2.la_residues (j % abs2.la_period) /\ (i + j) % q == r))
                (ensures r % mult == 0) =
        Classical.exists_elim (r % mult == 0)
          #nat #(fun i -> exists (j:nat). j < q /\ i < q /\
                    abs1.la_residues (i % abs1.la_period) /\ abs2.la_residues (j % abs2.la_period) /\ (i + j) % q == r)
          () (fun i ->
            Classical.exists_elim (r % mult == 0)
              #nat #(fun j -> j < q /\ i < q /\
                        abs1.la_residues (i % abs1.la_period) /\ abs2.la_residues (j % abs2.la_period) /\ (i + j) % q == r)
              () (fun j ->
                lemma_mult_via_residue_l abs1 abs2 i;
                lemma_mult_via_residue_r abs1 abs2 j;
                lemma_mod_add_zero mult i j;
                lemma_mod_via_period q mult (i + j)))
      in
      Classical.forall_intro (Classical.move_requires aux);
      ML.lemma_mult_lt_left abs1.la_period 1 abs2.la_period;
      assert (q > 1);
      assert ((la_concat abs1 abs2).la_period == q);
      assert ((la_concat abs1 abs2).la_mult == mult);
      assert (forall (r:nat). (la_concat abs1 abs2).la_residues r <==>
                              (exists (i:nat) (j:nat).
                                 i < q /\ j < q /\ abs1.la_residues (i % abs1.la_period) /\
                                 abs2.la_residues (j % abs2.la_period) /\ (i + j) % q == r))
    end
#pop-options

let lemma_la_concat_sound (#a:eqtype) (abs1 abs2:len_abs) (l1 l2:lang a)
  : Lemma (requires la_sound abs1 l1 /\ la_sound abs2 l2)
          (ensures la_sound (la_concat abs1 abs2) (re_concat l1 l2))
  = let goal (w:seq a) : Lemma (requires mem w (re_concat l1 l2)) (ensures gamma (la_concat abs1 abs2) (len w)) =
      elim_concat l1 l2 w (gamma (la_concat abs1 abs2) (len w)) (fun w1 w2 ->
        lemma_len_concat w1 w2;
        if abs1.la_period > 1 && abs2.la_period > 1 then begin
          let q = abs1.la_period * abs2.la_period in
          let i = (len w1) % q in
          let j = (len w2) % q in
          ML.modulo_modulo_lemma (len w1) abs1.la_period abs2.la_period;
          ML.modulo_modulo_lemma (len w2) abs2.la_period abs1.la_period;
          ML.modulo_distributivity (len w1) (len w2) q;
          Classical.exists_intro (fun (j':nat) ->
            j' < q /\ i < q /\ abs1.la_residues (i % abs1.la_period) /\ abs2.la_residues (j' % abs2.la_period) /\ (i + j') % q == (len w) % q) j;
          Classical.exists_intro (fun (i':nat) ->
            exists (j':nat). j' < q /\ i' < q /\ abs1.la_residues (i' % abs1.la_period) /\ abs2.la_residues (j' % abs2.la_period) /\ (i' + j') % q == (len w) % q) i
        end)
    in
    Classical.forall_intro (Classical.move_requires goal);
    lemma_la_mult_concat abs1 abs2

(* ----------------------------------------------------------------- *)
(* `star`/`plus`/`loop`: sound for any externally-justified gcd `g`    *)
(* ----------------------------------------------------------------- *)

(* Discharges `only_multiples_of` for exactly `len_abs.h`'s own
   motivating shape: an abstraction whose only possible residue is 0
   (e.g. `(a^4)*`'s operand, period 4, residues {0}). This is the one
   instance `lemma_only_multiples_of_period` needs no scan to
   recognize, since "only residue 0" already *is* the periodicity
   fact being established, rather than something to search for. *)
let lemma_only_multiples_of_period (abs:len_abs)
  : Lemma (requires abs.la_period > 1 /\ (forall (r:nat). 0 < r /\ r < abs.la_period ==> ~(abs.la_residues r)))
          (ensures only_multiples_of abs abs.la_period)
  = ()

(* A fully computable, always-safe choice of `g` for `star`/`plus`/
   `loop`, usable directly by `Z3RegexInfo.fst`'s `compute_info`
   (which cannot carry explicit proof terms): `abs`'s own `la_mult`
   field, whenever it carries a nontrivial (`>1`) fact -- this
   generalizes the old "exact singleton" special case to any chain of
   `unite`/`meet`/`concat`/`star`/`plus`/`loop` of already-periodic
   sub-expressions that `la_mult_sound` has propagated a divisor fact
   through (e.g. `la_exact n`, or `unite (la_exact n) (la_exact m)`'s
   `ngcd n m`). Falls back to `1` (no constraint) otherwise -- the
   real `len_abs::gcd()`'s general multi-residue scan (able to find,
   e.g., period `6` for `(aa)*|(aaa)*`'s residues `{0,2,3,4}` from
   first principles) is still not reconstructed here. *)
let la_period_for_star (abs:len_abs) : pos =
  if abs.la_mult > 1 then abs.la_mult else 1

let lemma_la_period_for_star (abs:len_abs)
  : Lemma (requires la_mult_sound abs) (ensures only_multiples_of abs (la_period_for_star abs))
  = if abs.la_mult > 1 then begin
      if abs.la_period > 1 then begin
        let aux (n:nat) : Lemma (requires gamma abs n) (ensures n % abs.la_mult == 0) =
          lemma_mod_via_period abs.la_period abs.la_mult n
        in
        Classical.forall_intro (Classical.move_requires aux)
      end
    end

(* Every member of `re_pow l n` has a length that is a multiple of
   `g`, given `abs` soundly bounds `l` and every length `abs` contains
   is itself a multiple of `g` -- the key arithmetic fact underlying
   `star`/`plus`/`loop`'s periodicity, proved once by induction on `n`
   and reused by all three combinators below. *)
let rec lemma_pow_gcd_period (#a:eqtype) (abs:len_abs) (g:pos) (l:lang a)
    (hsound: (w:seq a -> Lemma (requires mem w l) (ensures gamma abs (len w))))
    (n:nat) (w:seq a)
  : Lemma (requires only_multiples_of abs g /\ mem w (re_pow l n)) (ensures len w % g == 0)
  = if n = 0 then ()
    else
      elim_concat l (re_pow l (n - 1)) w (len w % g == 0) (fun w1 w2 ->
        hsound w1;
        lemma_pow_gcd_period abs g l hsound (n - 1) w2;
        lemma_len_concat w1 w2;
        lemma_mod_add_zero g (len w1) (len w2))

let la_star (a:len_abs) (g:pos) : len_abs =
  let hi = (match a.la_hi with Bound 0 -> Bound 0 | _ -> Infinite) in
  { la_lo = 0; la_hi = hi; la_period = g; la_residues = (fun r -> r == 0);
    la_mult = (if g > 1 then g else 0) }

let lemma_la_star_sound (#a:eqtype) (abs:len_abs) (g:pos) (l:lang a)
  : Lemma (requires la_sound abs l /\ only_multiples_of abs g)
          (ensures la_sound (la_star abs g) (re_star l))
  = let goal (w:seq a) : Lemma (requires mem w (re_star l)) (ensures gamma (la_star abs g) (len w)) =
      let hsound (w':seq a) : Lemma (requires mem w' l) (ensures gamma abs (len w')) = () in
      Classical.exists_elim (gamma (la_star abs g) (len w)) #nat #(fun n -> mem w (re_pow l n)) ()
        (fun n ->
           lemma_pow_gcd_period abs g l hsound n w;
           (if abs.la_hi = Bound 0 then begin
              let hmax (w':seq a) : Lemma (requires mem w' l) (ensures len w' <= 0) = hsound w' in
              lemma_pow_max_length l 0 hmax n w
            end))
    in
    Classical.forall_intro (Classical.move_requires goal)

let la_plus (a:len_abs) (g:pos) : len_abs =
  let hi = (match a.la_hi with Bound 0 -> Bound 0 | _ -> Infinite) in
  { la_lo = a.la_lo; la_hi = hi; la_period = g; la_residues = (fun r -> r == 0);
    la_mult = (if g > 1 then g else 0) }

let lemma_la_plus_sound (#a:eqtype) (abs:len_abs) (g:pos) (l:lang a)
  : Lemma (requires la_sound abs l /\ only_multiples_of abs g)
          (ensures la_sound (la_plus abs g) (re_plus l))
  = let goal (w:seq a) : Lemma (requires mem w (re_plus l)) (ensures gamma (la_plus abs g) (len w)) =
      let hsound (w':seq a) : Lemma (requires mem w' l) (ensures gamma abs (len w')) = () in
      Classical.exists_elim (gamma (la_plus abs g) (len w)) #(n:nat{n >= 1}) #(fun n -> mem w (re_pow l n)) ()
        (fun n ->
           lemma_pow_gcd_period abs g l hsound n w;
           let hmin (w':seq a) : Lemma (requires mem w' l) (ensures abs.la_lo <= len w') = hsound w' in
           lemma_pow_min_length l abs.la_lo hmin n w;
           ML.lemma_mult_le_right abs.la_lo 1 n;
           (if abs.la_hi = Bound 0 then begin
              let hmax (w':seq a) : Lemma (requires mem w' l) (ensures len w' <= 0) = hsound w' in
              lemma_pow_max_length l 0 hmax n w
            end))
    in
    Classical.forall_intro (Classical.move_requires goal)

let la_loop (a:len_abs) (g:pos) (lo:nat) (hi:ebound) : len_abs =
  let lo' = lo * a.la_lo in
  let hi' = (match hi with Bound h -> eb_scale h a.la_hi | Infinite -> Infinite) in
  { la_lo = lo'; la_hi = hi'; la_period = g; la_residues = (fun r -> r == 0);
    la_mult = (if g > 1 then g else 0) }

let lemma_la_loop_bounded_sound (#a:eqtype) (abs:len_abs) (g:pos) (l:lang a) (lo hi:nat)
  : Lemma (requires la_sound abs l /\ only_multiples_of abs g)
          (ensures la_sound (la_loop abs g lo (Bound hi)) (re_loop l lo hi))
  = let goal (w:seq a) : Lemma (requires mem w (re_loop l lo hi)) (ensures gamma (la_loop abs g lo (Bound hi)) (len w)) =
      let hsound (w':seq a) : Lemma (requires mem w' l) (ensures gamma abs (len w')) = () in
      Classical.exists_elim (gamma (la_loop abs g lo (Bound hi)) (len w)) #(n:nat{lo <= n /\ n <= hi}) #(fun n -> mem w (re_pow l n)) ()
        (fun n ->
           lemma_pow_gcd_period abs g l hsound n w;
           let hmin (w':seq a) : Lemma (requires mem w' l) (ensures abs.la_lo <= len w') = hsound w' in
           lemma_pow_min_length l abs.la_lo hmin n w;
           ML.lemma_mult_le_right abs.la_lo lo n;
           (match abs.la_hi with
            | Bound bnd ->
              let hmax (w':seq a) : Lemma (requires mem w' l) (ensures len w' <= bnd) = hsound w' in
              lemma_pow_max_length l bnd hmax n w;
              ML.lemma_mult_le_right bnd n hi
            | Infinite -> ()))
    in
    Classical.forall_intro (Classical.move_requires goal)

let lemma_la_loop_lo_sound (#a:eqtype) (abs:len_abs) (g:pos) (l:lang a) (lo:nat)
  : Lemma (requires la_sound abs l /\ only_multiples_of abs g)
          (ensures la_sound (la_loop abs g lo Infinite) (re_loop_lo l lo))
  = let hsound (w':seq a) : Lemma (requires mem w' l) (ensures gamma abs (len w')) = () in
    let goal (w:seq a) : Lemma (requires mem w (re_loop_lo l lo)) (ensures gamma (la_loop abs g lo Infinite) (len w)) =
      elim_concat (re_pow l lo) (re_star l) w (gamma (la_loop abs g lo Infinite) (len w)) (fun w1 w2 ->
        lemma_pow_gcd_period abs g l hsound lo w1;
        let hmin (w':seq a) : Lemma (requires mem w' l) (ensures abs.la_lo <= len w') = hsound w' in
        lemma_pow_min_length l abs.la_lo hmin lo w1;
        lemma_len_concat w1 w2;
        Classical.exists_elim ((len w2) % g == 0) #nat #(fun n -> mem w2 (re_pow l n)) ()
          (fun n -> lemma_pow_gcd_period abs g l hsound n w2);
        lemma_mod_add_zero g (len w1) (len w2))
    in
    Classical.forall_intro (Classical.move_requires goal)
