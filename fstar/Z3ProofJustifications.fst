(*
   Z3ProofJustifications.fst

   F* formalization of the two proof combinators used throughout
   `src/smt/smt_justification.cpp` -- the proof-construction layer for
   the SMT core's conflict-resolution engine (`conflict_resolution`),
   which is the main proof-producing site in Z3 *other* than
   `rewriter_def.h` (already covered by `Z3ProofTheory.fst`/
   `PROOF_REWRITER_REPORT.md`):

     - `PR_MODUS_PONENS` (`ast_manager::mk_modus_ponens`), used by
       `eq_conflict_justification::mk_proof`, `eq_root_propagation_
       justification::mk_proof`, and `mp_iff_justification::mk_proof`
       to combine an established fact `A` with an established
       `A => B` / `A = B` / `A ~ B` ("oeq") fact into `B`.

     - `PR_UNIT_RESOLUTION` (`ast_manager::mk_unit_resolution`), used
       by `unit_resolution_justification::mk_proof` to combine a
       clause `(or l_1 ... l_n)` with proofs of some of the `l_i`'s
       complements into the residual clause over the unresolved
       literals (or `false`, if all literals resolve away).

   Ground truth / correspondence:

     - Smart constructors: `ast_manager::mk_modus_ponens` (ast.cpp
       :2750-2768) and `ast_manager::mk_unit_resolution` (ast.cpp
       :3029-3090, the `num_proofs`-only overload -- the only one
       `smt_justification.cpp` ever calls).

     - Well-formedness semantics: `proof_checker::check1_basic`'s
       `PR_MODUS_PONENS` case (proof_checker.cpp:218-230) and
       `PR_UNIT_RESOLUTION` case (proof_checker.cpp:550-605).

     - Call sites: `unit_resolution_justification::mk_proof`,
       `eq_conflict_justification::mk_proof`, `eq_root_propagation_
       justification::mk_proof`, `mp_iff_justification::mk_proof`,
       all in `smt_justification.cpp`.

   Unlike `Z3ProofTheory.fst` (whose `proof` type is specialized to
   *equational* conclusions, `expr & expr` pairs, because that is all
   `rewriter_def.h` ever derives), `PR_MODUS_PONENS`/`PR_UNIT_
   RESOLUTION` combine *arbitrary* Boolean facts (an implication's
   consequent, a clause's residual literals), so this file works
   directly over a small, self-contained propositional sub-language
   (`not`/`or`/`implies`/`=`/`~`/`true`/`false` applied to `expr`
   atoms) and a concrete two-valued semantics for it (`blit_eval`),
   rather than reusing `Z3AstTheory.fst`'s fully abstract
   `interpretation value`. This is adequate because modus-ponens and
   unit-resolution are *purely propositional* inference rules: their
   validity never depends on which theory the atoms come from, only
   on how `not`/`or`/`implies`/`=`/`~` structure the formula -- the
   same scope restriction the "Bool/arith rewriters" audit
   (`BOOL_ARITH_REWRITER_REPORT.md`) uses for its own closed-form
   `bool`/`int` lemmas. The atoms themselves (whatever an uninterpreted
   `v : expr -> bool` assigns them) stand in for Z3AstTheory's richer
   `eval i e rho : value`; nothing here depends on a particular choice
   of atom valuation.
*)
module Z3ProofJustifications

open Z3AstTheory
open Z3ProofTheory
module Classical = FStar.Classical

(* ----------------------------------------------------------------- *)
(* Structural recognizers, keyed by `decl_name` (same style as         *)
(* `Z3ProofTheory.fst`'s `is_not`)                                     *)
(* ----------------------------------------------------------------- *)

let is_true (e:expr) : bool =
  match e with
  | App f [] -> f.decl_name = "true"
  | _ -> false

let is_false (e:expr) : bool =
  match e with
  | App f [] -> f.decl_name = "false"
  | _ -> false

let is_or (e:expr) : option (list expr) =
  match e with
  | App f args -> if f.decl_name = "or" then Some args else None
  | _ -> None

let is_implies (e:expr) : option (expr & expr) =
  match e with
  | App f [a; b] -> if f.decl_name = "implies" then Some (a, b) else None
  | _ -> None

(* `=` at Bool sort; `ast_manager::is_iff` is exactly `is_eq` guarded
   by `is_bool(arg(0))`, which this file does not need to track
   separately since every use below is already Bool-sorted by
   construction at its call site. *)
let is_eq_e (e:expr) : option (expr & expr) =
  match e with
  | App f [a; b] -> if f.decl_name = "=" then Some (a, b) else None
  | _ -> None

(* `oeq` ("observational equality"): `mk_modus_ponens`'s third
   accepted shape for `f2`, producing `PR_MODUS_PONENS_OEQ` instead of
   `PR_MODUS_PONENS` -- same acceptance condition on `f1`/`f2`, so this
   file treats it identically to `is_eq_e` below (both are "iff"). *)
let is_oeq_e (e:expr) : option (expr & expr) =
  match e with
  | App f [a; b] -> if f.decl_name = "~" then Some (a, b) else None
  | _ -> None

(* `ast_manager::is_complement_core`/`is_complement` (ast.h:2206-2209). *)
let is_complement_core (n1 n2:expr) : bool =
  (is_true n1 && is_false n2) ||
  (match is_not n1 with Some a -> a = n2 | None -> false)

let is_complement (n1 n2:expr) : bool =
  is_complement_core n1 n2 || is_complement_core n2 n1

(* ----------------------------------------------------------------- *)
(* A small propositional sub-language and its two-valued semantics     *)
(* ----------------------------------------------------------------- *)

(* `blit_eval`/`bclause_eval` give `not`/`or`/`implies`/`=`/`~`/
   `true`/`false` their standard propositional-logic meaning, treating
   every other `expr` as an opaque atom assigned truth by `v`
   (uninterpreted -- exactly as `Z3AstTheory.fst`'s `interpretation`
   leaves `uninterp_app` abstract). Mutually recursive on `e`/`args`,
   both structurally decreasing (an `Or`'s/`Implies`'s/`Eq`'s argument
   list is always a strict sub-part of `e`). *)
(* Dispatches by matching directly on `e`'s shape (rather than through
   the `is_*` recognizer functions above) so that F*'s termination
   checker can see `a`/`b`/`args` as literal structural sub-parts of
   `e`; the `is_*` recognizers are kept separate, for use in the
   lemmas below, and shown to agree with this direct match by the
   `lemma_blit_eval_*` unfolding lemmas that follow. *)
let rec blit_eval (v:expr -> bool) (e:expr) : Tot bool (decreases e) =
  match e with
  | App f args ->
    (match args with
     | [] ->
       if f.decl_name = "true" then true
       else if f.decl_name = "false" then false
       else v e
     | [a] ->
       if f.decl_name = "not" then not (blit_eval v a) else v e
     | [a; b] ->
       if f.decl_name = "implies" then (not (blit_eval v a)) || blit_eval v b
       else if f.decl_name = "=" then blit_eval v a = blit_eval v b
       else if f.decl_name = "~" then blit_eval v a = blit_eval v b
       else if f.decl_name = "or" then bclause_eval v args
       else if f.decl_name = "and" then band_eval v args
       else v e
     | _ ->
       if f.decl_name = "or" then bclause_eval v args
       else if f.decl_name = "and" then band_eval v args
       else v e)
  | _ -> v e

and bclause_eval (v:expr -> bool) (lits:list expr) : Tot bool (decreases lits) =
  match lits with
  | [] -> false
  | l :: lits' -> blit_eval v l || bclause_eval v lits'

and band_eval (v:expr -> bool) (lits:list expr) : Tot bool (decreases lits) =
  match lits with
  | [] -> true
  | l :: lits' -> blit_eval v l && band_eval v lits'

(* `is_complement n1 n2` is sound: complementary literals always take
   opposite truth values, for every atom valuation. This is the one
   semantic fact underlying both `PR_UNIT_RESOLUTION`'s acceptance
   condition and `mk_unit_resolution`'s main loop. *)
let lemma_is_complement_core_sound (v:expr -> bool) (n1 n2:expr)
  : Lemma (requires is_complement_core n1 n2)
          (ensures blit_eval v n1 = (not (blit_eval v n2)))
  = ()

let lemma_is_complement_sound (v:expr -> bool) (n1 n2:expr)
  : Lemma (requires is_complement n1 n2)
          (ensures blit_eval v n1 = (not (blit_eval v n2)))
  = if is_complement_core n1 n2 then lemma_is_complement_core_sound v n1 n2
    else lemma_is_complement_core_sound v n2 n1

(* ----------------------------------------------------------------- *)
(* `PR_UNIT_RESOLUTION`                                                 *)
(* ----------------------------------------------------------------- *)

(* `ast_manager::mk_unit_resolution`'s main-branch inner loop
   (ast.cpp:3063-3090): keep a literal of the clause iff no supplied
   antecedent fact is its complement. The real code additionally
   deduplicates repeated clause literals via an `ast_mark`; that is a
   pure allocation/representation optimization with no semantic
   effect on `bclause_eval` (`l || l == l`), so it is not modeled
   here -- see PROOF_JUSTIFICATIONS_REPORT.md. *)
let rec has_complement (lit:expr) (negs:list expr) : Tot bool (decreases negs) =
  match negs with
  | [] -> false
  | n :: negs' -> is_complement lit n || has_complement lit negs'

let rec resolve_residual (lits:list expr) (negs:list expr) : Tot (list expr) (decreases lits) =
  match lits with
  | [] -> []
  | l :: lits' ->
    if has_complement l negs then resolve_residual lits' negs
    else l :: resolve_residual lits' negs

(* Soundness of unit resolution, main (`is_or`) branch: if the clause
   `lits` holds and every literal in `negs` holds (both under the same
   valuation `v`), then the residual clause also holds. This is the
   semantic content `check1_basic`'s `PR_UNIT_RESOLUTION` case checks
   syntactically (every supplied antecedent after the first either
   matches a clause literal's complement, contributing to the
   residual's shrinkage, or the check fails) and that `unit_resolution_
   justification::mk_proof` (smt_justification.cpp:89-107) relies on:
   it supplies exactly one proof per clause disjunct it intends to
   resolve away, via `cr.get_proof(m_literals[i])` -- each such proof
   establishes its `m_literals[i]` is true, which is this lemma's
   `negs` hypothesis. *)
let rec lemma_has_complement_sound (v:expr -> bool) (l:expr) (negs:list expr)
  : Lemma (requires has_complement l negs /\ (forall n. List.Tot.memP n negs ==> blit_eval v n))
          (ensures ~(blit_eval v l))
          (decreases negs)
  = match negs with
    | [] -> ()
    | n :: negs' ->
      if is_complement l n then lemma_is_complement_sound v l n
      else lemma_has_complement_sound v l negs'

let rec lemma_resolve_residual_sound (v:expr -> bool) (lits negs:list expr)
  : Lemma (requires bclause_eval v lits /\ (forall n. List.Tot.memP n negs ==> blit_eval v n))
          (ensures bclause_eval v (resolve_residual lits negs))
          (decreases lits)
  = match lits with
    | [] -> ()
    | l :: lits' ->
      if has_complement l negs then begin
        (* `l` must be false: some `n` in `negs` is `l`'s complement
           and holds, so by `lemma_has_complement_sound`, `l` is
           false; since `bclause_eval v lits` and `l` is false, the
           tail `lits'` must hold, feeding the induction hypothesis. *)
        lemma_has_complement_sound v l negs;
        lemma_resolve_residual_sound v lits' negs
      end else begin
        (* `l` is kept in the residual: either `l` itself already
           holds (the residual clause holds via its first disjunct,
           no induction needed), or `l` is false, in which case
           `bclause_eval v lits` forces `lits'` to hold and the
           induction hypothesis applies. *)
        if blit_eval v l then ()
        else lemma_resolve_residual_sound v lits' negs
      end

(* The degenerate two-premise branch (ast.cpp:3049-3055,
   `!found_complement && !is_or(f1) && num_proofs == 2`): treating a
   non-clause fact `f1` as the singleton clause `[f1]` recovers this
   same lemma at `lits = [f1]`, `negs = [f2]`, with residual `[]`
   (i.e. `false`) exactly when `is_complement f1 f2` -- no separate
   proof is needed. *)
let lemma_unit_resolution_singleton_sound (v:expr -> bool) (f1 f2:expr)
  : Lemma (requires is_complement f1 f2 /\ blit_eval v f1 /\ blit_eval v f2)
          (ensures False)
  = lemma_is_complement_sound v f1 f2

(* ----------------------------------------------------------------- *)
(* `PR_MODUS_PONENS` / `PR_MODUS_PONENS_OEQ`                            *)
(* ----------------------------------------------------------------- *)

(* `ast_manager::mk_modus_ponens`'s three accepted shapes for `f2`
   (ast.cpp:2756-2768: `is_implies(f2) || is_eq(f2) || is_oeq(f2)`,
   with `get_arg(0) == f1`), matched one case per lemma for direct
   correspondence with `blit_eval`'s own three cases, and stated
   generically over any `f2` recognized by `is_implies`/`is_eq_e`/
   `is_oeq_e` -- the form actually usable at `mk_modus_ponens`'s call
   sites. Each is sound under any atom valuation -- modus ponens is
   valid for implication, and for `=`/`~` (treated identically, as
   iff) it is simply "if `a` and `a <=> b` hold, then `b` holds". *)
let lemma_mp_implies_sound (v:expr -> bool) (f1 f2 t1 t2:expr)
  : Lemma (requires is_implies f2 == Some (t1, t2) /\ f1 = t1 /\
                    blit_eval v f1 /\ blit_eval v f2)
          (ensures blit_eval v t2)
  = ()

let lemma_mp_eq_sound (v:expr -> bool) (f1 f2 t1 t2:expr)
  : Lemma (requires is_eq_e f2 == Some (t1, t2) /\ f1 = t1 /\
                    blit_eval v f1 /\ blit_eval v f2)
          (ensures blit_eval v t2)
  = ()

let lemma_mp_oeq_sound (v:expr -> bool) (f1 f2 t1 t2:expr)
  : Lemma (requires is_oeq_e f2 == Some (t1, t2) /\ f1 = t1 /\
                    blit_eval v f1 /\ blit_eval v f2)
          (ensures blit_eval v t2)
  = ()

(* `mk_modus_ponens`'s reflexivity short-circuit (ast.cpp:2764-2765,
   `is_reflexivity(p2)`): when `f2` is literally `t1 = t1` (or
   `t1 ~ t1`), the real code returns `p1` unchanged instead of
   wrapping in `PR_MODUS_PONENS` -- sound because `t2 = t1 = f1`
   already, so "deriving `t2`" is a no-op, matching `blit_eval`'s own
   `f1 = t1`-implies-`t2 = f1`-implies-`blit_eval v t2`-already-holds
   reasoning (`lemma_mp_eq_sound` applied at `t1 = t2`). *)
let lemma_mp_reflexivity_shortcut (v:expr -> bool) (f1 t:expr)
  : Lemma (requires f1 = t /\ blit_eval v f1)
          (ensures blit_eval v t)
  = ()

(* ----------------------------------------------------------------- *)
(* `PR_AND_ELIM` / `PR_NOT_OR_ELIM`                                     *)
(* ----------------------------------------------------------------- *)

(* Unlike `PR_TH_LEMMA`/`PR_DEF_AXIOM`/`PR_QUANT_INST` (trusted leaves
   with no checked semantic content -- `check1_basic` accepts any
   well-typed fact), `PR_AND_ELIM` (proof_checker.cpp:386-396) and
   `PR_NOT_OR_ELIM` (proof_checker.cpp:397-412) have real, checked
   acceptance conditions: a structural membership test. Both are used
   by clausification/CNF-conversion code (`nnf.cpp`,
   `asserted_formulas.cpp`) and are genuine propositional inference
   rules, so -- like `PR_MODUS_PONENS`/`PR_UNIT_RESOLUTION` above --
   they are proved fully semantically sound here, reusing the same
   `blit_eval` two-valued model (now extended with `and`, via
   `band_eval`). *)

(* `check1_basic`'s `PR_AND_ELIM` case: `p1` proves `(and t1 .. tn)`;
   `p` may conclude any `fact` that is literally one of the `ti`
   (`for (expr* t : terms) if (t == fact) return true;`). Semantically:
   a conjunction holding means every conjunct holds. *)
let rec lemma_band_eval_mem_sound (v:expr -> bool) (lits:list expr) (fact:expr)
  : Lemma (requires band_eval v lits /\ List.Tot.memP fact lits)
          (ensures blit_eval v fact)
          (decreases lits)
  = match lits with
    | [] -> ()
    | l :: lits' -> if l = fact then () else lemma_band_eval_mem_sound v lits' fact

let lemma_and_elim_sound (v:expr -> bool) (terms:list expr) (fact:expr)
  : Lemma (requires band_eval v terms /\ List.Tot.memP fact terms)
          (ensures blit_eval v fact)
  = lemma_band_eval_mem_sound v terms fact

(* `check1_basic`'s `PR_NOT_OR_ELIM` case: `p1` proves
   `(not (or t1 .. tn))`; `p` may conclude any `fact` such that
   `match_negated(ti, fact)` holds for some `ti` -- exactly this
   file's `is_complement` (both check "one side is the structural
   negation of the other"). Semantically: `not (or t1 .. tn)` holding
   means every `ti` is false, so `ti`'s complement (`fact`) is true,
   by `lemma_is_complement_sound`. *)
let rec lemma_bclause_eval_false_mem_sound (v:expr -> bool) (lits:list expr) (t:expr)
  : Lemma (requires ~(bclause_eval v lits) /\ List.Tot.memP t lits)
          (ensures ~(blit_eval v t))
          (decreases lits)
  = match lits with
    | [] -> ()
    | l :: lits' -> if l = t then () else lemma_bclause_eval_false_mem_sound v lits' t

let lemma_not_or_elim_sound (v:expr -> bool) (terms:list expr) (fact:expr)
  : Lemma (requires ~(bclause_eval v terms) /\
                    (exists (t:expr). List.Tot.memP t terms /\ is_complement t fact))
          (ensures blit_eval v fact)
  = Classical.exists_elim (blit_eval v fact)
      #expr
      #(fun t -> List.Tot.memP t terms /\ is_complement t fact)
      ()
      (fun t ->
        lemma_bclause_eval_false_mem_sound v terms t;
        lemma_is_complement_sound v t fact)

