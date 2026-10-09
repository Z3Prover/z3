module Z3PreprocessingProofTheory

(*
   F* formalization of the *proof-production* layer of Z3's
   preprocessing pipeline (`src/ast/simplifiers/*.cpp`), as opposed to
   its *meaning-preservation* layer already covered by
   `Z3SimplifierTheory.fst`/`Z3ModelReconstructionTheory.fst`.

   Background: when `ast_manager::proofs_enabled()`, a
   `dependent_expr_simplifier::reduce()` that rewrites a formula `f` to
   `f'` must additionally produce a `proof*` object justifying the
   step. `dependent_expr_simplifier::supports_proofs()` (default
   `false`, overridden `true` in exactly: `rewriter_simplifier.h`,
   `der_simplifier.h`, `distribute_forall.h`, `pull_nested_quantifiers.h`,
   `bit2int.h`, `elim_term_ite.h`, `bv_divrem_bounds.h`, `solve_eqs.h`,
   `extract_eqs.cpp`, `euf_completion.h`) gates whether
   `dependent_expr_state_tactic` runs a given simplifier at all when
   proofs are required; simplifiers that do not override it (e.g.
   `elim_unconstrained.cpp`, `propagate_values.cpp`,
   `eliminate_predicates.cpp`, `card2bv.cpp`, the bit-blasting family)
   are skipped outright when `proofs_enabled()` (see
   `dependent_expr_state_tactic.h:130-134`), and `bound_simplifier.h`/
   `randomizer.h` explicitly override it to `false`.

   Almost every proof-enabled simplifier follows the same two-step
   recipe (confirmed by grepping every `.h`/`.cpp` in the directory):

     1. An underlying `rewriter_tpl`-based rewriter (`th_rewriter`, or
        a bespoke `rw_cfg`) computes `new_curr`/`new_pr` from the
        current formula and internally builds `new_pr` as a composition
        of elementary proof nodes -- one `m.mk_rewrite(s,t)` /
        `m.mk_oeq_rewrite(s,t)` *trusted axiom* leaf per atomic
        simplification the theory-specific rewriter performed, combined
        upward via `m.mk_congruence`/`m.mk_monotonicity` (one argument
        changed at a time) and `m.mk_transitivity` (chained rewrite
        steps), with a handful of simplifiers instead building bespoke
        proof terms directly: `distribute_forall.cpp`'s
        `m.mk_push_quant`, `dominator_simplifier.cpp`'s
        `m.mk_rewrite`+`m.mk_modus_ponens`, `euf_completion.cpp`'s
        congruence-closure proof replay, and `dependent_expr_state.h`'s
        own `flatten_suffix` using `m.mk_and_elim`/`m.mk_not_or_elim`.
     2. The simplifier combines this per-step proof with the
        formula's *existing* justification `d.pr()` via
        `dependent_expr_simplifier::mp(a,b) = m.mk_modus_ponens(a,b)`,
        producing the new dependent_expr's proof.

   This file formalizes the *kernel-level soundness* of exactly the
   inference rules this recipe uses (`PR_REFLEXIVITY`, `PR_SYMMETRY`,
   `PR_TRANSITIVITY`, `PR_MODUS_PONENS`/`PR_MODUS_PONENS_OEQ`,
   `PR_MONOTONICITY`, `PR_QUANT_INTRO`/`PR_OEQ_QUANT_INTRO`,
   `PR_AND_ELIM`, `PR_NOT_OR_ELIM`, `PR_PUSH_QUANT`, `PR_IFF_TRUE`,
   `PR_IFF_FALSE`, `PR_IFF_OEQ`, `PR_COMMUTATIVITY`), matching the
   syntactic shapes `src/ast/proofs/proof_checker.cpp`'s
   `check1_basic` enforces for each (own study of that file, not
   previously part of this repository's F* audit). `PR_REWRITE`/
   `PR_OEQ_REWRITE` themselves are *trusted leaves*: `proof_checker.cpp`
   only checks that the claimed fact has the *shape* of an equivalence
   (`match_equiv`/`match_oeq`) and otherwise adds it, unchecked, to
   `side_conditions` -- i.e. the kernel does not (and structurally
   cannot, since it has no theory-specific knowledge) verify that a
   claimed rewrite `s ~ t` is actually sound; *that* is exactly the
   obligation discharged, concrete rewrite rule by concrete rewrite
   rule, by this project's other audits (`Z3BoolRewriter.fst`,
   `Z3ArithRewriter.fst`, `Z3BvRewriter.fst`, `Z3SeqRewrites.fst`,
   `Z3ArrayTheory.fst`, `Z3DatatypeTheory.fst`, `Z3FpaRewrites.fst`,
   `Z3PbTheory.fst`, `Z3RecfunTheory.fst`, `Z3FiniteSetTheory.fst`,
   `Z3SimplifierTheory.fst`'s substitution lemma, etc.) -- see
   `lemma_pr_rewrite_delegates` below, which makes this bridge
   precise: *given* that a theory audit has established the side
   condition, the kernel's `PR_REWRITE` conclusion is sound.

   Finally, `lemma_chain_sound` proves the architecturally important
   capstone fact: iterating the `mp`/`mk_modus_ponens` combinator
   across an entire preprocessing *pipeline* (a sequence of individually
   sound rewrite steps, each justified by one of the rules above)
   yields an end-to-end sound justification relating the very first
   formula fed to the pipeline and the very last one it produces --
   i.e. proof production, as architected, does not silently accumulate
   unsoundness across passes provided every individual pass's proof
   obligations are met.
*)

open Z3AstTheory
open Z3SimplifierTheory

(* ----------------------------------------------------------------- *)
(* Part 1 -- the equivalence/congruence rule family                   *)
(* (PR_REFLEXIVITY, PR_SYMMETRY, PR_TRANSITIVITY, PR_MONOTONICITY,     *)
(*  PR_QUANT_INTRO/PR_OEQ_QUANT_INTRO, PR_COMMUTATIVITY, PR_IFF_OEQ)   *)
(*                                                                     *)
(* These talk about plain denotational equality `eval i a rho ==       *)
(* eval i b rho` ("oeq" and "=" are the same relation here, matching  *)
(* `proof_checker.cpp`'s `IS_EQUIV`/`SAME_OP` macros, which treat an   *)
(* equality fact and an `oeq` fact interchangeably) -- no Boolean      *)
(* interpretation is needed for this family, exactly as                *)
(* `Z3SimplifierTheory.lemma_subst_cong` needed none.                  *)
(* ----------------------------------------------------------------- *)

/// `PR_REFLEXIVITY`: `e ~ e` always holds -- `proof_checker.cpp`
/// requires no premise and literally checks `t1 == t2`.
let lemma_pr_reflexivity (#value:Type) (i:interpretation value) (e:expr) (rho:env value)
  : Lemma (eval i e rho == eval i e rho)
  = ()

/// `PR_SYMMETRY`: from `t1 ~ t2` derive `t2 ~ t1`, for any of the
/// (conflated) symmetric relations `=`/`iff`/`oeq`.
let lemma_pr_symmetry (#value:Type) (i:interpretation value) (t1 t2:expr) (rho:env value)
  : Lemma (requires eval i t1 rho == eval i t2 rho)
          (ensures eval i t2 rho == eval i t1 rho)
  = ()

/// `PR_TRANSITIVITY` (and, by induction, `PR_TRANSITIVITY_STAR`):
/// chaining `t1 ~ t2` and `t2 ~ t3` gives `t1 ~ t3`.
let lemma_pr_transitivity (#value:Type) (i:interpretation value) (t1 t2 t3:expr) (rho:env value)
  : Lemma (requires eval i t1 rho == eval i t2 rho /\ eval i t2 rho == eval i t3 rho)
          (ensures eval i t1 rho == eval i t3 rho)
  = ()

/// `PR_COMMUTATIVITY`: `f(a,b) ~ f(b,a)` whenever `f`'s interpretation
/// is symmetric in its two arguments (`func_decl::is_commutative()`,
/// taken here as an explicit semantic hypothesis on `i` rather than a
/// syntactic one on `fd`, since `interpretation` has no notion of
/// `is_commutative` of its own).
let lemma_pr_commutativity
    (#value:Type) (i:interpretation value) (fd:func_decl) (a b:expr) (rho:env value)
  : Lemma
      (requires Some? fd.interp /\
                (forall (x y:value). i.interp_app fd [x;y] == i.interp_app fd [y;x]))
      (ensures eval i (App fd [a;b]) rho == eval i (App fd [b;a]) rho)
  = ()

(* `PR_MONOTONICITY`'s structural premise ("for every differing
   argument position there is a proof `s_k ~ t_k`, and the unchanged
   positions are syntactically identical") is modeled by requiring
   *every* position's denotation to already agree -- trivially true at
   unchanged positions since `s_k` and `t_k` coincide there. This is
   phrased as a recursive `prop`, mirroring
   `Z3SimplifierTheory.all_hold`'s style, rather than via
   `List.Tot.index`, to keep the induction below structural. *)
let rec eval_args_eq (#value:Type) (i:interpretation value) (args1 args2:list expr) (rho:env value) : prop =
  match args1, args2 with
  | [], [] -> True
  | a1 :: args1', a2 :: args2' -> eval i a1 rho == eval i a2 rho /\ eval_args_eq i args1' args2' rho
  | _, _ -> False

let rec lemma_eval_args_eq_sound
    (#value:Type) (i:interpretation value) (args1 args2:list expr) (rho:env value)
  : Lemma (requires eval_args_eq i args1 args2 rho)
          (ensures eval_args i args1 rho == eval_args i args2 rho)
  = match args1, args2 with
    | [], [] -> ()
    | a1 :: args1', a2 :: args2' -> lemma_eval_args_eq_sound i args1' args2' rho

/// `PR_MONOTONICITY`: same declaration applied to pairwise-equivalent
/// argument lists of the same length yields equivalent results.
let lemma_pr_monotonicity
    (#value:Type) (i:interpretation value) (fd:func_decl) (args1 args2:list expr) (rho:env value)
  : Lemma (requires eval_args_eq i args1 args2 rho)
          (ensures eval i (App fd args1) rho == eval i (App fd args2) rho)
  = lemma_eval_args_eq_sound i args1 args2 rho

/// `PR_QUANT_INTRO`/`PR_OEQ_QUANT_INTRO`: two quantifiers of the same
/// kind and the same bound sorts are equivalent whenever their bodies
/// are equivalent under every extension of the environment by one
/// value per bound variable -- congruence under a binder. Follows
/// directly from `eval`'s `Quantifier` case plus `quant_extensional`,
/// by the identical proof pattern `Z3AstTheory.lemma_closed_eval_env_irrelevant`
/// already uses for its own `Quantifier` case.
let lemma_pr_quant_intro
    (#value:Type) (i:interpretation value) (qk:quantifier_kind) (bound_sorts:list sort)
    (body1 body2:expr) (rho:env value)
  : Lemma
      (requires
         quant_extensional i /\
         (forall (vs:list value{List.Tot.length vs = List.Tot.length bound_sorts}).
            eval i body1 (shift vs rho) == eval i body2 (shift vs rho)))
      (ensures eval i (Quantifier qk bound_sorts body1) rho == eval i (Quantifier qk bound_sorts body2) rho)
  = let aux (vs:list value{List.Tot.length vs = List.Tot.length bound_sorts})
      : Lemma (eval i body1 (shift vs rho) == eval i body2 (shift vs rho))
      = ()
    in
    FStar.Classical.forall_intro aux

(* ----------------------------------------------------------------- *)
(* Part 2 -- the Boolean-truth rule family                             *)
(* (PR_MODUS_PONENS/PR_MODUS_PONENS_OEQ, PR_AND_ELIM, PR_NOT_OR_ELIM,  *)
(*  PR_IFF_TRUE, PR_IFF_FALSE, PR_PUSH_QUANT)                          *)
(*                                                                     *)
(* These talk about a formula *holding* (being assigned the             *)
(* designated "true" value), so they need an explicit, minimal         *)
(* axiomatization of what it means for `and_d`/`or_d`/`not_d`/          *)
(* `implies_d`/`iff_d` to be the standard propositional connectives --  *)
(* stated as semantic hypotheses on a concrete `i`, exactly as          *)
(* `Z3SimplifierTheory`'s `quant_extensional` is a semantic hypothesis  *)
(* on `interp_quant` rather than something baked into `interpretation`  *)
(* itself (`interpretation` is deliberately theory-agnostic).           *)
(* ----------------------------------------------------------------- *)

let holds (#value:Type) (i:interpretation value) (vtrue:value) (f:expr) (rho:env value) : prop =
  eval i f rho == vtrue

let rec all_eq (#value:Type) (vtrue:value) (vs:list value) : prop =
  match vs with
  | [] -> True
  | v :: vs' -> v == vtrue /\ all_eq vtrue vs'

let rec any_eq (#value:Type) (vtrue:value) (vs:list value) : prop =
  match vs with
  | [] -> False
  | v :: vs' -> v == vtrue \/ any_eq vtrue vs'

/// `and_d`'s interpretation computes the (n-ary) conjunction of its
/// arguments' truth values -- matching `proof_checker.cpp`'s
/// `PR_AND_ELIM`, which reads `and`'s argument list via `match_and`.
let is_and_decl (#value:Type) (i:interpretation value) (vtrue:value) (and_d:func_decl) : prop =
  Some? and_d.interp /\ (forall (vs:list value). i.interp_app and_d vs == vtrue <==> all_eq vtrue vs)

/// Dual: `or_d`'s interpretation computes the (n-ary) disjunction.
let is_or_decl (#value:Type) (i:interpretation value) (vtrue:value) (or_d:func_decl) : prop =
  Some? or_d.interp /\ (forall (vs:list value). i.interp_app or_d vs == vtrue <==> any_eq vtrue vs)

/// `not_d`'s interpretation is classical (two-valued) negation.
let is_not_decl (#value:Type) (i:interpretation value) (vtrue:value) (not_d:func_decl) : prop =
  Some? not_d.interp /\ (forall (v:value). i.interp_app not_d [v] == vtrue <==> ~(v == vtrue))

/// `implies_d`'s interpretation is classical (two-valued) implication.
let is_implies_decl (#value:Type) (i:interpretation value) (vtrue:value) (implies_d:func_decl) : prop =
  Some? implies_d.interp /\ (forall (a b:value). i.interp_app implies_d [a;b] == vtrue <==> (a == vtrue ==> b == vtrue))

/// `iff_d`'s interpretation is classical biconditional -- also stands
/// in for `=` at `Bool` sort, per `proof_checker.cpp`'s `IS_EQUIV`
/// macro, which treats `(= a b)` on Boolean `a`,`b` the same as
/// `(iff a b)`.
let is_iff_decl (#value:Type) (i:interpretation value) (vtrue:value) (iff_d:func_decl) : prop =
  Some? iff_d.interp /\ (forall (a b:value). i.interp_app iff_d [a;b] == vtrue <==> (a == vtrue <==> b == vtrue))

let rec lemma_all_eq_mem
    (#value:Type) (i:interpretation value) (vtrue:value) (args:list expr) (a:expr) (rho:env value)
  : Lemma (requires all_eq vtrue (eval_args i args rho) /\ List.Tot.mem a args)
          (ensures eval i a rho == vtrue)
  = match args with
    | [] -> ()
    | hd :: tl -> if hd = a then () else lemma_all_eq_mem i vtrue tl a rho

let rec lemma_any_eq_mem
    (#value:Type) (i:interpretation value) (vtrue:value) (args:list expr) (a:expr) (rho:env value)
  : Lemma (requires List.Tot.mem a args /\ eval i a rho == vtrue)
          (ensures any_eq vtrue (eval_args i args rho))
  = match args with
    | hd :: tl -> if hd = a then () else lemma_any_eq_mem i vtrue tl a rho

/// `PR_AND_ELIM`: from `(and args)` holding, and `fact` a member of
/// `args`, derive that `fact` holds.
let lemma_pr_and_elim
    (#value:Type) (i:interpretation value) (vtrue:value) (and_d:func_decl)
    (args:list expr) (fact:expr) (rho:env value)
  : Lemma
      (requires is_and_decl i vtrue and_d /\
                holds i vtrue (App and_d args) rho /\
                List.Tot.mem fact args)
      (ensures holds i vtrue fact rho)
  = lemma_all_eq_mem i vtrue args fact rho

/// `PR_NOT_OR_ELIM`: from `(not (or args))` holding, and `t` a member
/// of `args`, derive that `(not t)` holds.
let lemma_pr_not_or_elim
    (#value:Type) (i:interpretation value) (vtrue:value) (not_d or_d:func_decl)
    (args:list expr) (t:expr) (rho:env value)
  : Lemma
      (requires is_not_decl i vtrue not_d /\ is_or_decl i vtrue or_d /\
                holds i vtrue (App not_d [App or_d args]) rho /\
                List.Tot.mem t args)
      (ensures holds i vtrue (App not_d [t]) rho)
  = (* Contrapositive of `lemma_any_eq_mem`, via `move_requires` rather than a
       computational `if eval i t rho = vtrue`, since `value` is an abstract
       `Type` with no assumed decidable equality. *)
    FStar.Classical.move_requires (lemma_any_eq_mem i vtrue args t) rho

/// `PR_MODUS_PONENS`: from `fml0` holding and `(implies fml0 fact)` (or
/// `(iff fml0 fact)`, the two shapes `proof_checker.cpp` accepts)
/// holding, derive that `fact` holds.
let lemma_pr_modus_ponens
    (#value:Type) (i:interpretation value) (vtrue:value) (implies_d iff_d:func_decl)
    (fml0 fact:expr) (rho:env value)
  : Lemma
      (requires is_implies_decl i vtrue implies_d /\ is_iff_decl i vtrue iff_d /\
                holds i vtrue fml0 rho /\
                (holds i vtrue (App implies_d [fml0; fact]) rho \/
                 holds i vtrue (App iff_d [fml0; fact]) rho))
      (ensures holds i vtrue fact rho)
  = ()

/// `PR_MODUS_PONENS_OEQ`: the `oeq`-flavored variant -- identical
/// semantic content, since `oeq` is interpreted the same as `iff`
/// here (see `is_iff_decl`'s docstring); kept as a separate lemma only
/// to mirror `proof_checker.cpp`'s separate rule tag.
let lemma_pr_modus_ponens_oeq
    (#value:Type) (i:interpretation value) (vtrue:value) (iff_d:func_decl)
    (fml0 fact:expr) (rho:env value)
  : Lemma
      (requires is_iff_decl i vtrue iff_d /\
                holds i vtrue fml0 rho /\
                holds i vtrue (App iff_d [fml0; fact]) rho)
      (ensures holds i vtrue fact rho)
  = ()

/// `PR_IFF_TRUE`: from `fml` holding, derive `(iff fml true)` holds
/// (`true_d` interpreted as `vtrue`, matching `m.mk_true()`).
let lemma_pr_iff_true
    (#value:Type) (i:interpretation value) (vtrue:value) (iff_d true_d:func_decl)
    (fml:expr) (rho:env value)
  : Lemma
      (requires is_iff_decl i vtrue iff_d /\ Some? true_d.interp /\
                i.interp_app true_d [] == vtrue /\
                holds i vtrue fml rho)
      (ensures holds i vtrue (App iff_d [fml; App true_d []]) rho)
  = ()

/// `PR_IFF_FALSE`: from `(not fml)` holding, derive `(iff fml false)`
/// holds (`false_d` interpreted as any fixed `vfalse <> vtrue`).
let lemma_pr_iff_false
    (#value:Type) (i:interpretation value) (vtrue vfalse:value) (iff_d not_d false_d:func_decl)
    (fml:expr) (rho:env value)
  : Lemma
      (requires is_iff_decl i vtrue iff_d /\ is_not_decl i vtrue not_d /\
                Some? false_d.interp /\ ~(vfalse == vtrue) /\
                i.interp_app false_d [] == vfalse /\
                holds i vtrue (App not_d [fml]) rho)
      (ensures holds i vtrue (App iff_d [fml; App false_d []]) rho)
  = ()

/// `PR_IFF_OEQ`: from `(iff t1 t2)` holding, derive the `oeq`-tagged
/// fact `(~ t1 t2)` -- again the same semantic content as
/// `is_iff_decl`, restated with an explicit `oeq_d` to mirror
/// `proof_checker.cpp`'s distinct tag for the `oeq` relation.
let lemma_pr_iff_oeq
    (#value:Type) (i:interpretation value) (vtrue:value) (iff_d oeq_d:func_decl)
    (t1 t2:expr) (rho:env value)
  : Lemma
      (requires is_iff_decl i vtrue iff_d /\
                Some? oeq_d.interp /\
                (forall (a b:value). i.interp_app oeq_d [a;b] == vtrue <==> i.interp_app iff_d [a;b] == vtrue) /\
                holds i vtrue (App iff_d [t1; t2]) rho)
      (ensures holds i vtrue (App oeq_d [t1; t2]) rho)
  = ()

(* ----------------------------------------------------------------- *)
(* PR_PUSH_QUANT: reused directly from `Z3SimplifierTheory.fst`        *)
(* ----------------------------------------------------------------- *)

(* `distribute_forall.cpp`'s own proof-production path (`m.mk_push_quant`,
   see `rw_cfg::reduce_quantifier`) claims exactly the fact
   `Z3SimplifierTheory.lemma_forall_distributes_and_list`/
   `lemma_exists_distributes_or_list` already proved, instantiated with
   `dom := (vs:list value{List.Tot.length vs = List.Tot.length bound_sorts})`
   and each conjunct/disjunct `p_k vs := eval i body_k (shift vs rho) ==
   vtrue`. No new lemma is needed here: this is a direct corollary,
   recorded for completeness of this file's PR_* coverage table (see
   the report) rather than restated, since restating would only
   re-derive `lemma_forall_distributes_and_list`/
   `lemma_exists_distributes_or_list` with concrete `p_k`'s plugged in
   -- exactly the pattern this project already follows for
   `distribute_forall.cpp`'s n-ary case (`SIMPLIFIERS_REPORT.md`, row
   3/4) and for `add_sub`'s three registration cases (same report,
   "Note on #5"). *)

(* ----------------------------------------------------------------- *)
(* PR_REWRITE / PR_OEQ_REWRITE: the trusted-leaf bridge                *)
(* ----------------------------------------------------------------- *)

/// `PR_REWRITE`/`PR_OEQ_REWRITE` are *trusted axioms* as far as
/// `proof_checker.cpp` is concerned (`check1_basic`'s `PR_REWRITE`
/// case only checks that the claimed fact has the shape of an
/// equivalence, then unconditionally returns `true`, pushing the fact
/// itself onto `side_conditions` for separate verification). This
/// lemma makes precise *what* that separately-verified side condition
/// must establish, and shows that once it is established the
/// kernel's use of it is sound: this is not a deep fact (the proof is
/// `()`), but it is the precise handoff point between "the kernel
/// trusts this rewrite" and "a theory-specific audit proved this
/// rewrite correct" -- i.e. exactly the obligation every per-rewriter
/// `.fst` file in this project (`Z3BoolRewriter.fst`,
/// `Z3ArithRewriter.fst`, `Z3BvRewriter.fst`, `Z3SeqRewrites.fst`, ...)
/// discharges for the concrete `(s,t)` pairs Z3's rewriters actually
/// produce.
let lemma_pr_rewrite_delegates
    (#value:Type) (i:interpretation value) (s t:expr) (rho:env value)
  : Lemma (requires eval i s rho == eval i t rho)
          (ensures eval i s rho == eval i t rho)
  = ()

(* ----------------------------------------------------------------- *)
(* Capstone: whole-pipeline soundness of the `mp`/`mk_modus_ponens`    *)
(* combinator (`dependent_expr_simplifier::mp`)                       *)
(* ----------------------------------------------------------------- *)

/// A preprocessing pipeline is modeled as a list of intermediate
/// formulas `f0 :: f1 :: ... :: fk`, each consecutive pair justified
/// by the current simplification pass's proof (an instance of
/// `PR_REWRITE`/`PR_MODUS_PONENS`/`PR_MONOTONICITY`/`PR_PUSH_QUANT`/...,
/// all of which -- per Part 1/2 above -- establish denotational
/// equality at the formula's own `Bool` sort, i.e. `holds`-equivalence
/// of `f_j` and `f_{j+1}` since both are the same dependent_expr's
/// `.fml()` before/after one `reduce()` call). `chain_sound`
/// expresses "every pass individually proved its step correct";
/// `lemma_chain_sound` shows this implies the whole pipeline, from the
/// user's original input `f0` to the final preprocessed `fk`, is sound
/// -- exactly the guarantee `dependent_expr_simplifier::mp`'s repeated
/// `m.mk_modus_ponens` composition is meant to provide, and (since it
/// reduces to repeated `PR_TRANSITIVITY`, already proved sound above)
/// provides.
let rec chain_sound (#value:Type) (i:interpretation value) (vtrue:value) (fs:list expr) (rho:env value) : prop =
  match fs with
  | [] -> True
  | [_] -> True
  | f0 :: f1 :: rest -> (holds i vtrue f0 rho <==> holds i vtrue f1 rho) /\ chain_sound i vtrue (f1 :: rest) rho

let rec lemma_chain_sound
    (#value:Type) (i:interpretation value) (vtrue:value) (fs:list expr) (rho:env value)
  : Lemma
      (requires chain_sound i vtrue fs rho /\ Cons? fs)
      (ensures holds i vtrue (List.Tot.hd fs) rho <==> holds i vtrue (List.Tot.last fs) rho)
  = match fs with
    | [_] -> ()
    | f0 :: f1 :: rest -> lemma_chain_sound i vtrue (f1 :: rest) rho
