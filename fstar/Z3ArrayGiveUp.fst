(*
   Z3ArrayGiveUp.fst

   Targeted audit of `theory_array_full`'s lambda-use "give-up"
   classifier (src/smt/theory_array_full.cpp, ~line 1039), motivated
   by open PR #11162 ("Avoid array-theory give-up for uninterpreted
   uses of lambdas", fixing issue #11154).

   Context: when the array theory introduces a `lambda`-denoted array
   enode `n` (e.g. as a store/map/const normal form), it must be able
   to fully account for every way `n` is subsequently *used* --
   otherwise the model it builds may be unsound or it must honestly
   report incompleteness (`l_undef`, "(incomplete (theory array))")
   rather than risk a wrong `sat`/`unsat`. The classifier at
   theory_array_full.cpp:1039 walks every parent application `p` of
   `n` and flags `p` as requiring a give-up unless it recognizes `p`'s
   shape as one the theory already knows how to handle precisely:
   `is_default`/`is_select` (direct array operations, requiring
   beta-reduction of `n`'s body), `is_array_ext` (extensionality
   witness application), `ctx.is_beta_redex(p, n)` (an already-reduced
   beta redex), or `is_supported_array_eq(p)` (a recognized array
   equality shape).

   The bug: a parent `p` that is simply an *uninterpreted* function
   application `g(n)` (`g` some foreign/opaque symbol unrelated to the
   array theory) matched none of the above shapes, and so was
   (incorrectly) flagged as an unsupported/unsafe use, forcing a
   give-up even though such a `p` poses no actual risk: an
   uninterpreted function's theory reasoning (congruence closure) only
   ever needs to know *which enodes are equal to which*, never how an
   argument's value is internally represented or computed. It never
   needs to "look inside" `n`'s lambda body the way `select`/`store`/
   extensionality do. This exactly matches issue #11154: an
   array-and-quantifier benchmark that passes a lambda-array to an
   uninterpreted function regressed from `sat` to `unknown`.

   The fix is the one-line addition of `!is_uninterp(p->get_expr())`
   to the guard, excluding uninterpreted-function parents from the
   give-up set.

   This file formalizes the classifier itself (an exact transcription
   of the boolean condition, over an abstract enumeration of the
   parent-application shapes it distinguishes) and proves the fix is a
   strict narrowing of the give-up set, located and confined to
   exactly the Uninterp shape -- paralleling the classifier-bug style
   of Z3FpaRTNSelect.fst / Z3MpfExtremeExp.fst. It does *not* attempt a
   full soundness/completeness proof of `theory_array_full.cpp`'s
   model construction (out of scope, as for all other `theory_*`
   decision-procedure files in this audit series) -- see the closing
   "Semantic justification" note for the (informal, not mechanically
   checked) argument for *why* excluding Uninterp is safe.
*)
module Z3ArrayGiveUp

(* The shapes the classifier distinguishes for a parent application
   `p` of a lambda-array enode `n`, exactly as tested by the five
   (pre-fix: five; post-fix: six) `is_*`/`ctx.is_*` predicates at
   theory_array_full.cpp:1039. `Other` stands for any parent shape
   recognized by none of them (the case the classifier is designed to
   catch). *)
type shape =
  | Default      (* is_default(p) *)
  | Select       (* is_select(p) *)
  | ArrayExt     (* is_array_ext(p->get_expr()) *)
  | BetaRedex    (* ctx.is_beta_redex(p, n) *)
  | SupportedEq  (* is_supported_array_eq(p) *)
  | Uninterp     (* is_uninterp(p->get_expr()) -- the fix's new case *)
  | Other

(* OLD classifier (pre-#11162): give up unless one of the original
   five recognized shapes. *)
let old_unsupported (s:shape) : bool =
  not (s = Default || s = Select || s = ArrayExt || s = BetaRedex || s = SupportedEq)

(* NEW classifier (the fix): additionally exempt Uninterp. *)
let new_unsupported (s:shape) : bool =
  old_unsupported s && not (s = Uninterp)

(* ----------------------------------------------------------------- *)
(* Theorem 1 (the fix only narrows, never widens, the give-up set):   *)
(* anything the new classifier still flags, the old one also flagged. *)
(* So the fix cannot introduce a *new* unsound silent success -- it    *)
(* can only convert some previously-incomplete verdicts into complete  *)
(* ones. (Whether that conversion is itself sound is the separate,     *)
(* informal "semantic justification" below -- this theorem only       *)
(* pins down that the *fix's shape* is a pure narrowing, i.e. it        *)
(* changes no other case.)                                            *)
(* ----------------------------------------------------------------- *)
let lemma_new_narrows_old (s:shape)
  : Lemma (requires new_unsupported s) (ensures old_unsupported s)
  = ()

(* ----------------------------------------------------------------- *)
(* Theorem 2 (the bug, precisely located): the classifiers disagree    *)
(* *exactly* at Uninterp -- old flags it (give-up), new does not --     *)
(* and agree on every other shape. This is the formal counterpart of    *)
(* the PR's one-line, single-condition diff. *)
(* ----------------------------------------------------------------- *)
let lemma_differ_only_at_uninterp ()
  : Lemma (old_unsupported Uninterp /\ not (new_unsupported Uninterp))
  = ()

let lemma_agree_off_uninterp (s:shape)
  : Lemma (requires s <> Uninterp)
          (ensures old_unsupported s == new_unsupported s)
  = ()

(* Theorem 3 (no regression on genuinely unsafe shapes): `Other` --
   the catch-all for parent shapes the theory truly does not
   recognize -- is still flagged as unsupported by both classifiers,
   i.e. the fix does not quietly suppress give-up for shapes the
   theory has no specific handling for; only the one, specifically
   justified, Uninterp case is exempted. *)
let lemma_other_still_unsupported ()
  : Lemma (old_unsupported Other /\ new_unsupported Other)
  = ()

(* -----------------------------------------------------------------
   Semantic justification (informal; not mechanically checked here,
   analogous in status to this series' other "Honest limitation"
   notes, e.g. Z3FpaRoundingAudit.fst's closing remark):

   Every one of the five originally-recognized shapes
   (Default/Select/ArrayExt/BetaRedex/SupportedEq) is precisely a
   construct whose *correct* handling requires inspecting `n`'s lambda
   body itself -- `select`/`default` need to beta-reduce it to extract
   a value, `array_ext`/`SupportedEq` need it to instantiate the
   extensionality axiom's witness, and `BetaRedex` is the already-
   reduced result of exactly that process. If `p` is none of these,
   the theory has no established axiom-instantiation pathway for it,
   and must conservatively give up -- *unless* `p`'s own theory
   (here, uninterpreted-function congruence) does not need to inspect
   `n`'s internal structure at all. Congruence closure's only
   obligation for `g(n)` is: whenever some other enode `n'` is proved
   array-theory-equal to `n` (via whatever axiom instantiation the
   array theory performs elsewhere, triggered independently of this
   particular parent `p`), propagate `g(n) = g(n')`. This holds
   regardless of whether `n`/`n'` happen to be lambda-represented,
   store chains, or anything else -- congruence is parametric in the
   argument's *identity* (its equivalence class), not its
   *representation*. Hence an Uninterp parent can never be the
   reason a lambda's denotation goes unaccounted-for: whatever
   accounting is needed for `n` is driven by *other* occurrences (a
   `select`/`store`/`=`) elsewhere in the problem, which remain
   separately (and unconditionally) subject to the still-active
   Default/Select/ArrayExt/BetaRedex/SupportedEq checks. This is
   exactly why issue #11154's regressed benchmark is safe to accept:
   its lambda array is read via `select` elsewhere (triggering normal
   array-axiom handling there) and *also* passed to an uninterpreted
   function (which needs nothing more than congruence).
*)
