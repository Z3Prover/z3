(*
   Z3LraFarkasTheory.fst

   F* formalization of the *theory-lemma* soundness check that
   `src/ast/proofs/proof_checker.cpp` performs for linear-real-
   arithmetic conflicts: `proof_checker::check_arith_literal` /
   `check_arith_proof`, which validate `PR_TH_LEMMA` nodes tagged
   `("arith" "farkas" c1 c2 ... cn)` -- i.e. genuine Farkas'-lemma
   infeasibility certificates: a nonnegative linear combination of
   simultaneously-asserted arithmetic literals that provably collapses
   to a numeral of the wrong sign, proving the literals jointly
   unsatisfiable.

   Ground truth / correspondence (`src/ast/proofs/proof_checker.cpp`,
   the `check_arith_literal`/`check_arith_proof` pair, roughly lines
   1348-1522):

     - `check_arith_literal(is_pos, lit, coeff, sum, is_strict)` takes
       one literal (already possibly wrapped in `not`), a claimed
       rational coefficient, and a running symbolic `sum` (passed by
       reference, accumulated in place via `th_rewriter` after every
       literal); it:
         * strips a leading `not`, flipping its own notion of "is this
           literal being asserted true or false" (`is_pos`) --
           modeled here by `raw_lit.negated` combined with the
           caller-supplied `is_pos` via `effective_pos`;
         * only accepts `<=`/`<`/`>=`/`>`/`=` atoms;
         * for `=`, uses the coefficient's own sign unchanged, and
           does not swap sides based on `is_pos` at all (an equality's
           two sides contribute `coeff*(a0-a1)` either way, since a
           true equality means `a0-a1` is *exactly* zero and so
           contributes 0 to the sum regardless of the coefficient's
           sign -- this is exactly why equalities, uniquely, are
           allowed negative coefficients in a Farkas combination);
         * for every other relation, takes the coefficient's absolute
           value and swaps `a0`/`a1` (equivalently: picks the "oriented
           so that `a0 - a1 <= 0` / `< 0` represents the thing being
           assumed true" canonical direction), accumulating `is_strict
           ||= ...` along the way;
         * accumulates `sum += coeff*(a0 - a1)` (strictly: `+coeff*a0 +
           (-coeff)*a1`, then re-simplified).
     - `check_arith_proof(p)`: if the proof node's tag is bare `"arith"`
       (no `"farkas"` parameter), or its second parameter isn't the
       symbol `"farkas"`, the node is **trusted unconditionally with no
       check at all** (`dump_proof(p); return true;`) -- this is a
       real, audited gap in Z3's own proof checker, documented in
       `LRA_FARKAS_REPORT.md`, not modeled further here (there is
       nothing to model: it is simply "accept"). Otherwise: reads
       rational coefficients `c1..cn` from parameters `[2..]`, scales
       them all by the LCM of their denominators (purely a numerical
       convenience; it does not change which combinations are valid --
       *this is exactly why this file models every coefficient,
       constant, and variable value as a plain F* `int`, not an
       abstract rational*: the real checker itself always reduces to
       an all-integer computation before running the actual
       cancellation check, and working over `int` lets F*'s SMT
       backend's native linear-arithmetic decision procedure discharge
       every arithmetic step directly, with no opaque algebra lemmas
       needed), processes each parent/antecedent proof's fact with
       `is_pos = true`, then processes the conclusion fact with
       `is_pos = false` (if the conclusion is `(or d1 ... dm)`, each
       disjunct `di` is processed individually with its own
       coefficient -- the general "refute the negation of every
       disjunct" resolution-style pattern; if the conclusion is
       literally `false`, nothing further is added -- the common case
       this file focuses on, and the shape of every real certificate
       harvested for `LRA_FARKAS_REPORT.md`). Finally: builds `sum < 0`
       (if any contributing literal was strict) or `sum <= 0`,
       re-simplifies with `th_rewriter`, and requires the result to be
       syntactically `false` -- i.e. the accumulated symbolic sum must
       *provably* (via arithmetic term-level cancellation, not mere
       satisfiability) reduce to a numeral whose sign contradicts the
       derived relation.

   This file formalizes exactly that final check, independent of
   Z3AstTheory's generic `expr`: a dedicated, minimal linear-arithmetic
   term language (`lin_term`: a list of integer-coefficient monomials
   plus a constant, matching how `check_arith_literal`'s `a.mk_add`/
   `a.mk_mul` calls build up `sum` one monomial at a time) is enough to
   state and prove the soundness theorem precisely, without having to
   first build a general nonlinear-arithmetic evaluator. Real,
   benchmark-derived test instances (built from literal Farkas
   certificates Z3 itself emitted) live in
   `Z3PulseLraCheckerTests.fst`; the genuinely imperative, Pulse-level
   executable decision procedure (mirroring `check_arith_proof`'s
   control flow with real mutable state: a running "collected
   monomials" table, not just a counter) lives in
   `Z3PulseLraChecker.fst`.
*)
module Z3LraFarkasTheory

open FStar.List.Tot
module L = FStar.List.Tot

(* ----------------------------------------------------------------- *)
(* Linear terms over integer coefficients                              *)
(* ----------------------------------------------------------------- *)

(* A variable is just a name (matching how real certificates are
   presented below: Z3's own internal terms are `skoX`, `skoY`, etc.,
   so plain strings are a faithful-enough stand-in for the handful of
   atomic leaves a linear arithmetic literal ever mentions). *)
type var = string

(* A linear term: an (unreduced -- not grouped by variable) list of
   `(coefficient, variable)` monomials, plus a constant. This mirrors
   `check_arith_literal`'s own representation exactly: `sum` is built
   by repeated `a.mk_add`/`a.mk_mul` calls, i.e. an unreduced sum of
   monomials that `th_rewriter` only *later* collects/cancels -- the
   same two-phase "build, then simplify" shape is modeled by
   `mono`/`eval_term` versus the cancellation side-condition used by
   the main soundness theorem below (`is_refuting_constant`). *)
noeq
type lin_term = {
  mono : list (int & var);
  cst  : int;
}

let zero_term : lin_term = { mono = []; cst = 0 }

(* `msval` is the "pure sum of monomials" (baseline 0), a direct
   structural recursion over the monomial list; `eval_term` adds the
   constant on top. This (rather than routing through
   `FStar.List.Tot.fold_left`) is purely a proof-engineering choice:
   it makes the two algebraic facts this file needs
   (`lemma_eval_scale`/`lemma_eval_add`, i.e. "`scale`/`add2` evaluate
   exactly as expected") provable by plain structural induction with
   no auxiliary "shift the accumulator" lemmas, while denoting exactly
   the same linear combination `check_arith_literal`'s `sum` term
   does. *)
let rec msval (ms:list (int & var)) (rho:var -> int) : int =
  match ms with
  | [] -> 0
  | (c, v) :: tl -> c * rho v + msval tl rho

let eval_term (t:lin_term) (rho:var -> int) : int = t.cst + msval t.mono rho

let scale (c:int) (t:lin_term) : lin_term =
  { mono = L.map (fun (k, v) -> (c * k, v)) t.mono; cst = c * t.cst }

let add2 (t1 t2:lin_term) : lin_term =
  { mono = t1.mono @ t2.mono; cst = t1.cst + t2.cst }

let sub2 (t1 t2:lin_term) : lin_term = add2 t1 (scale (-1) t2)

(* `scale`/`add2` evaluate exactly as expected -- the basic algebraic
   facts the rest of this file leans on. Proved by plain structural
   induction over the monomial list; F*'s SMT backend discharges the
   integer arithmetic at each step directly (native linear arithmetic,
   no opaque operators). *)
let rec lemma_msval_append (ms1 ms2:list (int & var)) (rho:var -> int)
  : Lemma (ensures msval (ms1 @ ms2) rho == msval ms1 rho + msval ms2 rho)
          (decreases ms1)
  = match ms1 with
    | [] -> ()
    | (_, _) :: tl -> lemma_msval_append tl ms2 rho

let rec lemma_msval_scale (c:int) (ms:list (int & var)) (rho:var -> int)
  : Lemma (ensures msval (L.map (fun (k, v) -> (c * k, v)) ms) rho == c * msval ms rho)
          (decreases ms)
  = match ms with
    | [] -> ()
    | (_, _) :: tl -> lemma_msval_scale c tl rho

let lemma_eval_add (t1 t2:lin_term) (rho:var -> int)
  : Lemma (ensures eval_term (add2 t1 t2) rho == eval_term t1 rho + eval_term t2 rho)
  = lemma_msval_append t1.mono t2.mono rho

let lemma_eval_scale (c:int) (t:lin_term) (rho:var -> int)
  : Lemma (ensures eval_term (scale c t) rho == c * eval_term t rho)
  = lemma_msval_scale c t.mono rho

let lemma_eval_sub (t1 t2:lin_term) (rho:var -> int)
  : Lemma (ensures eval_term (sub2 t1 t2) rho == eval_term t1 rho - eval_term t2 rho)
  = lemma_eval_add t1 (scale (-1) t2) rho; lemma_eval_scale (-1) t2 rho

(* ----------------------------------------------------------------- *)
(* Raw arithmetic literals and their normalization                    *)
(* ----------------------------------------------------------------- *)

(* The five relations `check_arith_literal` accepts
   (`a.is_le`/`is_lt`/`is_ge`/`is_gt`/`m.is_eq`); every other shape is
   rejected by the real code (`return false`), i.e. is simply not
   representable here. *)
type rel =
  | Le
  | Lt
  | Ge
  | Gt
  | Eqr

(* A raw literal `a0 <rel> a1`, optionally wrapped in `not` (`negated`
   -- modeling `check_arith_literal`'s own leading `if (m.is_not(...))`
   unwrap, which flips the *literal's own* sense independent of the
   caller-supplied `is_pos`). *)
noeq
type raw_lit = { a0 : lin_term; a1 : lin_term; rl : rel; negated : bool }

let raw_rel_holds (rl:rel) (x y:int) : prop =
  match rl with
  | Le -> x <= y
  | Lt -> x < y
  | Ge -> x >= y
  | Gt -> x > y
  | Eqr -> x = y

(* The literal's "obvious" ground-truth semantics: what the SMT-LIB
   literal `a0 <rel> a1` (or its negation, if `negated`) actually
   means. *)
let raw_lit_sem (l:raw_lit) (rho:var -> int) : prop =
  let base = raw_rel_holds l.rl (eval_term l.a0 rho) (eval_term l.a1 rho) in
  if l.negated then ~base else base

(* The combined polarity `check_arith_literal` works with when called
   as `check_arith_literal(is_pos, lit, ...)`: `is_pos = true` for
   every genuine antecedent/parent fact (always asserted true), and
   `is_pos = false` when refuting one disjunct of the conclusion
   (assuming its negation). Composed with the literal's own possible
   `not`-wrapping, exactly as the C++ does with its first `if
   (m.is_not(lit0)) { lit0 = ...; is_pos = !is_pos; }`. *)
let effective_pos (is_pos:bool) (l:raw_lit) : bool =
  if l.negated then not is_pos else is_pos

(* The fact actually being assumed to hold, combining both sources of
   polarity: *)
let assumed (is_pos:bool) (l:raw_lit) (rho:var -> int) : prop =
  if is_pos then raw_lit_sem l rho else ~(raw_lit_sem l rho)

(* A *normalized* atom: a canonical "`term <= 0`" (non-strict) or
   "`term < 0`" (strict) fact, or -- for equalities -- "`term = 0`"
   (`is_eq`, for which `strict` is irrelevant and any-sign
   coefficients are later allowed in a combination). *)
noeq
type atom = { term : lin_term; strict : bool; is_eq : bool }

let atom_holds (a:atom) (rho:var -> int) : prop =
  if a.is_eq then eval_term a.term rho = 0
  else if a.strict then eval_term a.term rho < 0
  else eval_term a.term rho <= 0

(* `check_arith_literal`'s normalization, branch for branch: for `Eqr`
   the term is always `a0 - a1` regardless of polarity (matching the
   real code, which never swaps/flips for `m.is_eq`); for every other
   relation, the branch taken is exactly the one that makes
   `assumed is_pos l rho` and `atom_holds (normalize is_pos l) rho`
   agree (checked relation-by-relation in `lemma_normalize_sound`
   below). *)
let normalize (is_pos:bool) (l:raw_lit) : atom =
  let p = effective_pos is_pos l in
  match l.rl with
  | Eqr -> { term = sub2 l.a0 l.a1; strict = false; is_eq = true }
  | Le  -> if p then { term = sub2 l.a0 l.a1; strict = false; is_eq = false }
           else      { term = sub2 l.a1 l.a0; strict = true;  is_eq = false }
  | Lt  -> if p then { term = sub2 l.a0 l.a1; strict = true;  is_eq = false }
           else      { term = sub2 l.a1 l.a0; strict = false; is_eq = false }
  | Ge  -> if p then { term = sub2 l.a1 l.a0; strict = false; is_eq = false }
           else      { term = sub2 l.a0 l.a1; strict = true;  is_eq = false }
  | Gt  -> if p then { term = sub2 l.a1 l.a0; strict = true;  is_eq = false }
           else      { term = sub2 l.a0 l.a1; strict = false; is_eq = false }

(* The faithfulness theorem for `normalize`: it computes exactly the
   same fact as the literal's own combined semantics, for every
   relation/polarity/negation combination -- *except* for one genuine,
   narrow gap this file deliberately exposes rather than silently
   papering over, faithfully mirroring the real code: for `Eqr`,
   `check_arith_literal` never consults `is_pos` at all (confirmed
   against `src/ast/proofs/proof_checker.cpp` lines 1387-1392: the
   `std::swap(a0, a1)` calls are gated on `is_ge`/`is_gt`/`is_le`/
   `is_lt` only, never `m.is_eq`), so it always treats an equality
   literal's contribution as "`a0 - a1 = 0`" even when the *actual*
   fact being assumed is the equality's *negation* (`effective_pos
   is_pos l == false`, i.e. a genuine "`a0 <> a1`" antecedent). That
   would be unsound in general (a disequality does not imply the
   corresponding equality's contribution is legitimately 0) -- this
   theorem therefore requires `effective_pos is_pos l` to be `true`
   whenever `l.rl == Eqr`, exactly the (unchecked, in the real C++)
   side condition that must hold for `check_arith_literal`'s own `Eqr`
   handling to be sound. Every genuine Farkas certificate's equality
   antecedents are always presented positively in practice (LRA
   disequalities are handled by case-splitting elsewhere, not fed
   directly into this combinator) so this is not known to be
   exploitable -- but `check_arith_literal` itself never verifies it,
   exactly like the already-documented `num_params == 1`
   unconditional-trust gap (`LRA_FARKAS_REPORT.md`); this is a second,
   independent, narrower soundness precondition Z3's own proof checker
   relies on without checking. *)
let lemma_normalize_sound (is_pos:bool) (l:raw_lit) (rho:var -> int)
  : Lemma (requires l.rl == Eqr ==> effective_pos is_pos l)
          (ensures assumed is_pos l rho <==> atom_holds (normalize is_pos l) rho)
  = lemma_eval_sub l.a0 l.a1 rho; lemma_eval_sub l.a1 l.a0 rho;
    (* Force the same case split `normalize` itself makes, so the SMT
       encoding sees the actual branch taken instead of an opaque
       inductive value. *)
    match l.rl with
    | Eqr -> ()
    | Le  -> ()
    | Lt  -> ()
    | Ge  -> ()
    | Gt  -> ()

(* ----------------------------------------------------------------- *)
(* Farkas combinations                                                 *)
(* ----------------------------------------------------------------- *)

(* One contribution to a Farkas combination: a normalized atom and the
   integer coefficient `check_arith_proof` claims for it (already
   scaled to clear denominators, as the real code does). *)
noeq
type cert_entry = { a : atom; c : int }

(* Well-formedness of one entry: non-equality atoms must carry a
   nonnegative coefficient (`check_arith_literal` always takes
   `abs(coeff)` for them); equality atoms may use either sign, exactly
   as the real code allows. *)
let wf_entry (e:cert_entry) : prop = e.a.is_eq \/ e.c >= 0

let rec all_wf (cert:list cert_entry) : prop =
  match cert with
  | [] -> True
  | e :: tl -> wf_entry e /\ all_wf tl

let rec all_hold (cert:list cert_entry) (rho:var -> int) : prop =
  match cert with
  | [] -> True
  | e :: tl -> atom_holds e.a rho /\ all_hold tl rho

(* The combined symbolic term `sum` accumulates to, and whether any
   strict inequality with a (necessarily, by `wf_entry`, nonnegative)
   positive coefficient contributed -- matching `check_arith_literal`'s
   `is_strict ||= ...` accumulation exactly (equality atoms never set
   it, matching the real code, which only ever sets `is_strict` inside
   the non-`is_eq` branches). *)
let rec combined_term (cert:list cert_entry) : lin_term =
  match cert with
  | [] -> zero_term
  | e :: tl -> add2 (scale e.c e.a.term) (combined_term tl)

let rec any_strict (cert:list cert_entry) : prop =
  match cert with
  | [] -> False
  | e :: tl -> (~e.a.is_eq /\ e.a.strict /\ e.c > 0) \/ any_strict tl

(* The core mathematical content of Farkas' lemma (soundness
   direction): a well-formed combination of atoms that all actually
   hold evaluates, as a whole, to something `<= 0` (or `< 0` if a
   strict contributor fired) -- by ordinary linear-arithmetic
   reasoning, discharged by F*'s SMT backend term-by-term. *)
let rec lemma_combined_sign (cert:list cert_entry) (rho:var -> int)
  : Lemma (requires all_wf cert /\ all_hold cert rho)
          (ensures (if any_strict cert then eval_term (combined_term cert) rho < 0
                    else eval_term (combined_term cert) rho <= 0))
          (decreases cert)
  = match cert with
    | [] -> ()
    | e :: tl ->
      lemma_combined_sign tl rho;
      lemma_eval_add (scale e.c e.a.term) (combined_term tl) rho;
      lemma_eval_scale e.c e.a.term rho

(* ----------------------------------------------------------------- *)
(* The headline soundness theorem                                     *)
(* ----------------------------------------------------------------- *)

(* What `check_arith_proof`'s final step checks: the combined term's
   evaluation is *the same numeral `k`, for every environment* (the
   semantic content of "`th_rewriter` simplifies `sum` down to a
   numeral" -- a term whose value does not depend on any variable
   assignment at all), and that numeral's sign contradicts what
   `lemma_combined_sign` guarantees for any truly-satisfying `rho`. *)
let is_refuting_constant (cert:list cert_entry) (k:int) : prop =
  (forall (rho:var -> int). eval_term (combined_term cert) rho = k) /\
  (if any_strict cert then k >= 0 else k > 0)

(* If a well-formed certificate's combined term is provably (for every
   environment) a numeral of the wrong sign, then no environment can
   satisfy every atom in the certificate simultaneously -- i.e. the
   certificate proves the literals it was built from are jointly
   unsatisfiable. This is exactly the semantic content of a real
   `(_ th-lemma arith farkas c1 ... cn)` node: `check_arith_proof`
   accepting such a node *is* a proof that its antecedents (each
   already separately established by the surrounding proof DAG) and
   the negation of its conclusion cannot hold together, i.e. the
   conclusion follows. *)
let lemma_farkas_unsat (cert:list cert_entry) (k:int)
  : Lemma (requires all_wf cert /\ is_refuting_constant cert k)
          (ensures forall (rho:var -> int). ~(all_hold cert rho))
  = FStar.Classical.forall_intro (fun (rho:var -> int) ->
      Classical.move_requires (lemma_combined_sign cert) rho)

(* A pointwise corollary (useful when a single `rho` is already fixed,
   e.g. when deriving `False` from a hypothetical satisfying
   assignment, rather than universally quantifying as above). *)
let lemma_farkas_refutes (cert:list cert_entry) (k:int) (rho:var -> int)
  : Lemma (requires all_wf cert /\ all_hold cert rho /\ is_refuting_constant cert k)
          (ensures False)
  = lemma_combined_sign cert rho

(* ----------------------------------------------------------------- *)
(* An executable decision procedure: `farkas_decide`                  *)
(* ----------------------------------------------------------------- *)

(* `lemma_farkas_unsat`/`lemma_farkas_refutes` above are *checkers of a
   supplied witness* `k`: they show a claimed refuting constant really
   does refute, but something still has to produce `k` (and show the
   variable coefficients really do all cancel to 0) in the first
   place. The real `check_arith_proof` does this itself, by actually
   running `th_rewriter` over the accumulated symbolic `sum` after
   every literal and inspecting whether the result is a bare numeral.
   This section ports *that* -- a genuinely executable "collect like
   terms, then check every variable's coefficient is 0" decision
   procedure -- and proves it exactly as sound as the witness-checking
   lemmas above, so nothing has to be taken on faith: `farkas_decide`
   below is a total function from a certificate to `option int`, and
   whenever it returns `Some k`, `all_hold cert rho` is refutable for
   every `rho`, with no separately-supplied witness. This is also
   precisely the pure spec `Z3PulseLraChecker.fst`'s imperative Pulse
   `fn` is proved to compute. *)

(* A running "collected polynomial": an association list from `var`
   to its (already-summed) coefficient. `lookup`/`remove_var` are the
   two primitives `insert_mono` needs; both are plain structural
   recursions with no well-formedness invariant assumed (duplicate
   `var` entries are tolerated by every lemma below, even though
   `insert_mono`/`collect` never themselves introduce one). *)
let rec lookup (v:var) (tbl:list (int & var)) : option int =
  match tbl with
  | [] -> None
  | (c, v') :: tl -> if v' = v then Some c else lookup v tl

let rec remove_var (v:var) (tbl:list (int & var)) : list (int & var) =
  match tbl with
  | [] -> []
  | (c, v') :: tl -> if v' = v then tl else (c, v') :: remove_var v tl

(* `msval tbl rho` splits, around any chosen `v`, into `v`'s own
   (possibly-absent, hence `option`) contribution plus everything
   else's -- the one structural fact `insert_mono`'s correctness
   reduces to. *)
let rec lemma_lookup_remove (v:var) (tbl:list (int & var)) (rho:var -> int)
  : Lemma (ensures msval tbl rho ==
                   (match lookup v tbl with
                    | None -> 0
                    | Some c0 -> c0 * rho v) + msval (remove_var v tbl) rho)
          (decreases tbl)
  = match tbl with
    | [] -> ()
    | (_, v') :: tl -> if v' = v then () else lemma_lookup_remove v tl rho

(* Add one monomial `c * v` into a running table, merging with any
   existing entry for `v` (dropping the entry entirely if the merged
   coefficient cancels to 0, matching `th_rewriter`'s own behavior of
   never leaving an explicit `0 * v` term around). *)
let insert_mono (c:int) (v:var) (tbl:list (int & var)) : list (int & var) =
  match lookup v tbl with
  | None -> if c = 0 then tbl else (c, v) :: tbl
  | Some c0 ->
    let tbl' = remove_var v tbl in
    let c' = c0 + c in
    if c' = 0 then tbl' else (c', v) :: tbl'

let lemma_insert_mono (c:int) (v:var) (tbl:list (int & var)) (rho:var -> int)
  : Lemma (ensures msval (insert_mono c v tbl) rho == c * rho v + msval tbl rho)
  = lemma_lookup_remove v tbl rho

(* Fold an entire monomial list into a running table, one `insert_mono`
   at a time -- this is what `collect` below drives one `cert_entry`'s
   worth of (already-scaled) monomials through. *)
let rec collect (ms:list (int & var)) (tbl:list (int & var)) : list (int & var) =
  match ms with
  | [] -> tbl
  | (c, v) :: tl -> collect tl (insert_mono c v tbl)

let rec lemma_collect (ms:list (int & var)) (tbl:list (int & var)) (rho:var -> int)
  : Lemma (ensures msval (collect ms tbl) rho == msval ms rho + msval tbl rho)
          (decreases ms)
  = match ms with
    | [] -> ()
    | (c, v) :: tl ->
      lemma_insert_mono c v tbl rho;
      lemma_collect tl (insert_mono c v tbl) rho

(* Decidable (`bool`) mirrors of `wf_entry`/`any_strict`/`all_wf`,
   used so `farkas_fold` below can branch on them directly (Pulse
   cannot branch on a `prop`); each is proved logically equivalent to
   its `prop` counterpart above, so every lemma already proved in
   terms of the `prop` versions transfers unchanged. *)
let wf_entry_b (e:cert_entry) : bool = e.a.is_eq || e.c >= 0

let lemma_wf_entry_b (e:cert_entry)
  : Lemma (ensures wf_entry_b e <==> wf_entry e)
  = ()

let rec all_wf_b (cert:list cert_entry) : bool =
  match cert with
  | [] -> true
  | e :: tl -> wf_entry_b e && all_wf_b tl

let rec lemma_all_wf_b (cert:list cert_entry)
  : Lemma (ensures all_wf_b cert <==> all_wf cert)
  = match cert with
    | [] -> ()
    | _ :: tl -> lemma_all_wf_b tl

let any_strict_b1 (e:cert_entry) : bool = not e.a.is_eq && e.a.strict && e.c > 0

let rec any_strict_b (cert:list cert_entry) : bool =
  match cert with
  | [] -> false
  | e :: tl -> any_strict_b1 e || any_strict_b tl

let rec lemma_any_strict_b (cert:list cert_entry)
  : Lemma (ensures any_strict_b cert <==> any_strict cert)
  = match cert with
    | [] -> ()
    | _ :: tl -> lemma_any_strict_b tl


(* The unconditional accumulator fold's result, as a record (rather
   than an anonymous tuple) so every lemma below can refer to its
   three components via plain field projection -- which F*'s SMT
   encoding unfolds through recursive-function calls far more
   reliably than a `let (a, b, c) = ...` tuple destructuring of a
   recursive call's result, which (empirically, in this file) the SMT
   encoding would not automatically relate to the callee's own
   recursive unfolding. *)
noeq
type fold_result = { ftbl : list (int & var); fk : int; fstrict : bool }

(* The unconditional accumulator fold: given a certificate, a
   starting table/constant/strict-flag, computes the result of
   folding every entry's (coefficient-scaled) monomials into the
   table and accumulating the constant/strict-flag, *regardless* of
   well-formedness (an ill-formed entry still contributes its
   coefficient's literal arithmetic effect -- `farkas_fold` below
   layers the well-formedness gate on top, as a separate, independent
   check, rather than interleaving it with the fold itself: this
   split is exactly what makes the value-preservation lemma below a
   plain structural induction, with no `option`/`None`-case threading
   required). *)
let rec fold_raw (cert:list cert_entry) (tbl:list (int & var)) (k:int) (strict:bool)
  : fold_result =
  match cert with
  | [] -> { ftbl = tbl; fk = k; fstrict = strict }
  | e :: tl ->
    let scaled = L.map (fun (c0, v) -> (e.c * c0, v)) e.a.term.mono in
    let tbl' = collect scaled tbl in
    let k' = k + e.c * e.a.term.cst in
    let strict' = strict || any_strict_b1 e in
    fold_raw tl tbl' k' strict'

(* A plain one-step unfolding fact about `fold_raw`'s `Cons` case,
   exposed as its own lemma (rather than relying on callers' own
   `assert`/`assert_norm` of the same equality) because this is
   exactly the fact `Z3PulseLraChecker.fst`'s Pulse `fn rec` needs to
   justify that its own recursive call matches `fold_raw`'s -- and
   Pulse has no direct `assert_norm`, so the fact needs to already
   exist as a callable lemma. *)
let lemma_fold_raw_cons (e:cert_entry) (tl:list cert_entry) (tbl:list (int & var)) (k:int) (strict:bool)
  : Lemma (ensures fold_raw (e :: tl) tbl k strict ==
                   fold_raw tl (collect (L.map (fun (c0, v) -> (e.c * c0, v)) e.a.term.mono) tbl)
                                (k + e.c * e.a.term.cst) (strict || any_strict_b1 e))
  = assert_norm (fold_raw (e :: tl) tbl k strict ==
                 fold_raw tl (collect (L.map (fun (c0, v) -> (e.c * c0, v)) e.a.term.mono) tbl)
                              (k + e.c * e.a.term.cst) (strict || any_strict_b1 e))

(* One per-`rho` fact bundling exactly what the inductive step of
   `lemma_fold_raw` needs: how folding one (coefficient-scaled)
   entry's monomials into `tbl0` changes its value. Stated as a single
   dedicated lemma (rather than inline, sequenced `Lemma` calls inside
   a `forall_intro` closure) because `forall_intro` generalizes only
   the *stated* postcondition of the closure it's given, not whatever
   incidental local facts a multi-step sequenced proof happens to
   establish along the way. *)
#push-options "--z3rlimit 50"
let lemma_step_rho (e:cert_entry) (tbl0:list (int & var)) (tl:list cert_entry) (rho:var -> int)
  : Lemma (ensures msval (collect (L.map (fun (c0, v) -> (e.c * c0, v)) e.a.term.mono) tbl0) rho
                   + e.c * e.a.term.cst + eval_term (combined_term tl) rho
                   == msval tbl0 rho + eval_term (combined_term (e :: tl)) rho)
  = let scaled = L.map (fun (c0, v) -> (e.c * c0, v)) e.a.term.mono in
    lemma_collect scaled tbl0 rho;
    lemma_msval_scale e.c e.a.term.mono rho;
    lemma_eval_scale e.c e.a.term rho;
    lemma_eval_add (scale e.c e.a.term) (combined_term tl) rho;
    assert (msval (collect scaled tbl0) rho == e.c * msval e.a.term.mono rho + msval tbl0 rho);
    assert (eval_term e.a.term rho == e.a.term.cst + msval e.a.term.mono rho);
    assert (eval_term (combined_term (e :: tl)) rho ==
            e.c * eval_term e.a.term rho + eval_term (combined_term tl) rho);
    ()
#pop-options

(* The resulting table/constant/strict-flag triple faithfully
   represents, for the given valuation `rho`, the value of
   `combined_term cert` added onto the starting accumulator, and the
   strict-flag is exactly `any_strict_b cert` combined with the
   starting flag -- unconditionally, regardless of well-formedness.
   (`rho` is taken as an explicit parameter, rather than universally
   quantified inside `ensures`, purely so each recursive/base case can
   be proved by a short, direct chain of lemma applications at that
   one `rho` -- callers needing the "for every `rho`" form get it via
   `FStar.Classical.forall_intro`, as `lemma_farkas_decide_sound`
   below does.) *)
let rec lemma_fold_raw (cert:list cert_entry) (tbl0:list (int & var)) (k0:int) (strict0:bool) (rho:var -> int)
  : Lemma (ensures (fold_raw cert tbl0 k0 strict0).fstrict == (strict0 || any_strict_b cert) /\
                    msval (fold_raw cert tbl0 k0 strict0).ftbl rho + (fold_raw cert tbl0 k0 strict0).fk ==
                    msval tbl0 rho + k0 + eval_term (combined_term cert) rho)
          (decreases cert)
  = match cert with
    | [] -> ()
    | e :: tl ->
      let scaled = L.map (fun (c0, v) -> (e.c * c0, v)) e.a.term.mono in
      let tbl' = collect scaled tbl0 in
      let k' = k0 + e.c * e.a.term.cst in
      let strict' = strict0 || any_strict_b1 e in
      lemma_step_rho e tbl0 tl rho;
      lemma_fold_raw tl tbl' k' strict' rho;
      lemma_fold_raw_cons e tl tbl0 k0 strict0;
      assert ((fold_raw tl tbl' k' strict').fstrict == (strict' || any_strict_b tl));
      assert (msval (fold_raw tl tbl' k' strict').ftbl rho + (fold_raw tl tbl' k' strict').fk ==
              msval tbl' rho + k' + eval_term (combined_term tl) rho);
      ()

(* The final check: every variable's collected coefficient must be
   exactly 0 (the combination is a bare numeral `k`), with the usual
   strict/non-strict sign requirement on that numeral. *)
let rec all_zero (tbl:list (int & var)) : bool =
  match tbl with
  | [] -> true
  | (c, _) :: tl -> (c = 0) && all_zero tl

let rec lemma_all_zero (tbl:list (int & var)) (rho:var -> int)
  : Lemma (requires all_zero tbl) (ensures msval tbl rho == 0)
  = match tbl with
    | [] -> ()
    | (_, _) :: tl -> lemma_all_zero tl rho

(* `farkas_fold` layers the well-formedness gate (checked once, over
   the whole certificate, via `all_wf_b`) on top of the unconditional
   `fold_raw`: `None` exactly when `all_wf_b cert` is false, matching
   `check_arith_literal`'s own `return false` on any malformed
   literal. *)
let farkas_fold (cert:list cert_entry) (tbl:list (int & var)) (k:int) (strict:bool)
  : option fold_result =
  if all_wf_b cert then Some (fold_raw cert tbl k strict) else None

(* The headline executable decision procedure: `Some k` means `cert`
   is a well-formed Farkas combination that collapses to the numeral
   `k`, of a sign that (given the strict/non-strict flag) is
   impossible for a combination of literals that actually all hold --
   i.e. `cert` is a valid refutation, with `k` computed, not supplied.
   This is exactly what `check_arith_proof` computes via
   `th_rewriter` + `is_numeral` + a sign check on the resulting
   numeral, and `farkas_accepts` is exactly its `return true`. *)
let farkas_decide (cert:list cert_entry) : option int =
  if not (all_wf_b cert) then None
  else
    let r = fold_raw cert [] 0 false in
    if all_zero r.ftbl && (if r.fstrict then r.fk >= 0 else r.fk > 0) then Some r.fk else None

let farkas_accepts (cert:list cert_entry) : bool = Some? (farkas_decide cert)

(* The headline theorem: whenever the fully executable `farkas_decide`
   accepts a certificate, that certificate's literals are jointly
   unsatisfiable, for every valuation -- with no externally-supplied
   witness constant and no externally-supplied well-formedness or
   strictness proof: everything `is_refuting_constant`/`all_wf` needed
   as hypotheses in `lemma_farkas_unsat` above is instead *derived*
   here from `cert` alone. *)
let lemma_farkas_decide_sound (cert:list cert_entry) (rho:var -> int)
  : Lemma (requires Some? (farkas_decide cert) /\ all_hold cert rho)
          (ensures False)
  = lemma_fold_raw cert [] 0 false rho;
    lemma_all_wf_b cert;
    lemma_any_strict_b cert;
    let r = fold_raw cert [] 0 false in
    lemma_all_zero r.ftbl rho;
    (* `eval_term (combined_term cert) rho == r.fk` (from `lemma_fold_raw`
       plus `lemma_all_zero`, both at this one `rho`), combined with
       `lemma_combined_sign`'s per-`rho` sign bound for a well-formed,
       all-holding certificate, directly contradicts `farkas_decide`'s
       own sign check on `r.fk` -- no universally-quantified
       `is_refuting_constant` witness is needed here, since both facts
       are already pinned to the same concrete `rho`. *)
    lemma_all_wf_b cert;
    assert (all_wf cert);
    lemma_combined_sign cert rho