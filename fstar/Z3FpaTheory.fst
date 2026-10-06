(*
   Z3FpaTheory.fst

   A self-contained axiomatization, in F*, of the *value-level* IEEE-754
   special-value case analysis performed symbolically by
   src/ast/rewriter/fpa_rewriter.cpp.

   Scope decision (mirrors the Z3SeqTheory.fst / seq_rewriter.cpp
   scoping): fpa_rewriter.cpp almost never rewrites symbolic *finite*
   floating-point arithmetic -- add/sub/mul/div/rem/sqrt/fma/
   round_to_integral all either (a) constant-fold when both operands
   are concrete `mpf` numerals, by calling into Z3's bit-precise `mpf`
   arithmetic library (which we do not re-verify here -- see
   Z3FpaConverter.fst and the FPA report for the bit-precise encoding
   theory instead), or (b) fall through unrewritten (BR_FAILED). The
   only rules fpa_rewriter.cpp applies to genuinely *symbolic*
   (non-constant) arguments are the special-value case splits: NaN
   propagation/absorption, signed infinity/zero handling, and the
   definitional identities sub = add-of-negation, gt = flip(lt),
   ge = flip(le).

   We therefore model a floating-point value as one of the IEEE-754
   special classes (NaN, signed Infinity, signed Zero) or an opaque
   nonzero finite payload, represented here as a (metaphorical, exact)
   nonzero `int` -- we never compute with this payload beyond equality
   and sign, since fpa_rewriter.cpp never derives a symbolic fact about
   a finite magnitude; only its presence/sign matters for the rules in
   scope.
*)
module Z3FpaTheory

(* ----------------------------------------------------------------- *)
(* Values                                                              *)
(* ----------------------------------------------------------------- *)

(* sign: `false` = positive, `true` = negative (matches the FPA sign
   bit convention: 0 = positive, 1 = negative, used throughout
   fpa_rewriter.cpp / fpa2bv_converter.cpp). *)
type sign = bool

(* A floating-point value, abstracted to the granularity that
   fpa_rewriter.cpp's symbolic rules operate on:
     NaN     ~ (fp.isNaN x)    -- sign-less in IEEE-754 semantics
     Inf s   ~ (fp.isInfinite x), signed
     Zero s  ~ (fp.isZero x), signed
     Fin v   ~ a concrete nonzero finite value; `v:int` stands in for
               "the exact mathematical value" (sign = sign of v). *)
type fp =
  | NaN
  | Inf  : sign -> fp
  | Zero : sign -> fp
  | Fin  : v:int{v <> 0} -> fp

(* ----------------------------------------------------------------- *)
(* Classification predicates                                           *)
(* ----------------------------------------------------------------- *)

let is_nan (x:fp) : bool = match x with NaN -> true | _ -> false
let is_inf (x:fp) : bool = match x with Inf _ -> true | _ -> false
let is_pinf (x:fp) : bool = match x with Inf s -> not s | _ -> false
let is_ninf (x:fp) : bool = match x with Inf s -> s | _ -> false
let is_zero (x:fp) : bool = match x with Zero _ -> true | _ -> false
let is_pzero (x:fp) : bool = match x with Zero s -> not s | _ -> false
let is_nzero (x:fp) : bool = match x with Zero s -> s | _ -> false
let is_fin (x:fp) : bool = match x with Fin _ -> true | _ -> false

(* mk_is_negative / mk_is_positive (fpa_rewriter.cpp 833-856): defined
   over *every* class, including NaN (which is always "not negative"
   and "not positive" -- NaN carries no usable sign for comparisons). *)
let is_negative (x:fp) : bool =
  match x with
  | NaN -> false
  | Inf s -> s
  | Zero s -> s
  | Fin v -> v < 0

let is_positive (x:fp) : bool =
  match x with
  | NaN -> false
  | Inf s -> not s
  | Zero s -> not s
  | Fin v -> v > 0

(* is_normal / is_subnormal (fpa_rewriter.cpp 767-833): the only
   *symbolic* rule fpa_rewriter.cpp applies here concerns
   `to_fp(rm, to_real(int))`, which requires bit-precise exponent
   overflow reasoning (`mk_is_inf_of_int`) that we do not model (see
   the FPA report). We still define these two predicates, parametrized
   by an abstract classifier on the finite payload, purely so that the
   classification-exhaustiveness/disjointness sanity lemmas below can
   be stated for the *full* value space, matching the analogous
   bit-level classification theory in Z3FpaConverter.fst. *)
let is_subnormal (is_subnormal_mag: int -> bool) (x:fp) : bool =
  match x with Fin v -> is_subnormal_mag v | _ -> false

let is_normal (is_subnormal_mag: int -> bool) (x:fp) : bool =
  match x with Fin v -> not (is_subnormal_mag v) | _ -> false

(* ----------------------------------------------------------------- *)
(* neg / abs (fpa_rewriter.cpp mk_neg 323-355, mk_abs 368-384)          *)
(* ----------------------------------------------------------------- *)

let neg (x:fp) : fp =
  match x with
  | NaN -> NaN
  | Inf s -> Inf (not s)
  | Zero s -> Zero (not s)
  | Fin v -> Fin (-v)

let abs_fp (x:fp) : fp =
  match x with
  | NaN -> NaN
  | Inf _ -> Inf false
  | Zero _ -> Zero false
  | Fin v -> Fin (if v < 0 then -v else v)

(* ----------------------------------------------------------------- *)
(* add / sub (fpa_rewriter.cpp mk_add 265-285, mk_sub 286-292)          *)
(*                                                                      *)
(* `add` is left fully abstract (fpa_rewriter.cpp never derives a      *)
(* symbolic law about it beyond constant folding and argument          *)
(* reordering, neither of which this theory needs to re-verify);       *)
(* `sub` is *defined*, exactly as the code does, as addition of a       *)
(* negation.                                                            *)
(* ----------------------------------------------------------------- *)

let sub (add: fp -> fp -> fp -> fp) (rm x y:fp) : fp = add rm x (neg y)

(* ----------------------------------------------------------------- *)
(* min / max (fpa_rewriter.cpp mk_min 384-408, mk_max 408-432)          *)
(*                                                                      *)
(* The only symbolic rule is NaN-absorption; the actual IEEE-754        *)
(* "minimum"/"maximum" of two non-NaN values (including the signed-     *)
(* zero tie-break, which the code deliberately leaves unrewritten,      *)
(* BR_FAILED, when the signs disagree) is left abstract via `base`.    *)
(* ----------------------------------------------------------------- *)

let min_fp (base: fp -> fp -> fp) (x y:fp) : fp =
  if is_nan x then y
  else if is_nan y then x
  else base x y

let max_fp (base: fp -> fp -> fp) (x y:fp) : fp =
  if is_nan x then y
  else if is_nan y then x
  else base x y

(* ----------------------------------------------------------------- *)
(* Comparisons (fpa_rewriter.cpp mk_lt 578-619, mk_gt 619-624,           *)
(* mk_le 624-639, mk_ge 639-644)                                        *)
(*                                                                      *)
(* `lt`/`le` are given a *total* definition here (NaN always            *)
(* comparing false, signed infinities bracketing everything, zero of    *)
(* either sign ranking as 0) so that the early-exit branches coded in   *)
(* mk_lt can be checked against one single authoritative specification. *)
(* `gt`/`ge` are literally defined as the code defines them: flipped    *)
(* calls to `lt`/`le`.                                                  *)
(* ----------------------------------------------------------------- *)

(* A representative rank for ordering purposes: both signed zeros rank
   as 0 (IEEE-754 total order on values, ignoring the sign-of-zero
   distinction that only `fp.eq`/structural equality cares about). *)
let val_of (x:fp{~(is_nan x) /\ ~(is_inf x)}) : int =
  match x with
  | Zero _ -> 0
  | Fin v -> v

let lt (x y:fp) : bool =
  if is_nan x || is_nan y then false
  else if is_ninf x then not (y = Inf true) && not (is_nan y)
  else if is_ninf y then false
  else if is_pinf x then false
  else if is_pinf y then not (x = Inf false) && not (is_nan x)
  else val_of x < val_of y

let gt (x y:fp) : bool = lt y x

let le (x y:fp) : bool =
  if is_nan x || is_nan y then false
  else if is_ninf x then true
  else if is_pinf x then is_pinf y
  else if is_ninf y then false
  else if is_pinf y then true
  else val_of x <= val_of y

let ge (x y:fp) : bool = le y x

(* ----------------------------------------------------------------- *)
(* Equalities: `float_eq` (IEEE-754 `fp.eq`) vs `eq_core` (SMT `=`)     *)
(* (fpa_rewriter.cpp mk_float_eq 557-578, mk_eq_core 857-872)           *)
(*                                                                      *)
(* These deliberately differ on NaN: IEEE-754 `fp.eq` never holds for   *)
(* NaN (not even reflexively), whereas SMT `=` must be a genuine        *)
(* equivalence relation, so two NaN *terms* compare equal under `=`.    *)
(* Both treat +0/-0 specially, but oppositely: `fp.eq` identifies them, *)
(* `=` distinguishes them.                                              *)
(* ----------------------------------------------------------------- *)

let float_eq (x y:fp) : bool =
  if is_nan x || is_nan y then false
  else if is_zero x && is_zero y then true
  else x = y

let eq_core (x y:fp) : bool =
  if is_nan x && is_nan y then true
  else if is_zero x && is_zero y && is_negative x <> is_negative y then false
  else x = y
