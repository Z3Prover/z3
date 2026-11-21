module Z3LpIntegerCut

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open FStar.Real
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open FStar.List.Tot
module A = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed
module P = Z3LinearArithmeticTheory
module G = Z3LpGomory
module L = FStar.List.Tot

(* Integer rounding (Chvatal-Gomory) cuts for refutations over integer atoms.

   A certificate is a list of rounded bounds and a final refutation.
   Every bound is justified by `Z3LinearArithmeticAst.check` from the premises
   and the bounds before it: one weight per premise or earlier bound, then the
   weight of the negated bound. That check rounds a strict inequality over
   Int-sorted terms to a non-strict one (a < b gives a + 1 <= b), which is what
   makes a bound such as `x <= floor (c / g)` a consequence of `g * x <= c`.
   Nothing here is trusted: neither the bounds, their weights, nor the search
   that proposes them. The conclusion is derived only if every replay succeeds. *)

include Z3LpIntegerCutSyntax

let rec check_steps (steps:list step) (facts:list expr) : Tot bool (decreases steps) =
  match steps with
  | [] -> true
  | s :: rest -> A.check s.weights s.bound facts && check_steps rest (facts @ [s.bound])

let rec accumulated (steps:list step) (facts:list expr) : Tot (list expr) (decreases steps) =
  match steps with
  | [] -> facts
  | s :: rest -> accumulated rest (facts @ [s.bound])

let check (c:certificate) (conclusion:expr) (facts:list expr) : bool =
  check_steps c.steps facts && A.check c.refutation conclusion (accumulated c.steps facts)

let rec lemma_steps_sound (steps:list step) (facts:list expr)
                          (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    check_steps steps facts /\ conj_holds i rho facts)
          (ensures conj_holds i rho (accumulated steps facts))
          (decreases steps) =
  match steps with
  | [] -> ()
  | s :: rest ->
    E.lemma_check_with_numeric_model s.weights s.bound facts i rho;
    G.lemma_conj_branch i rho facts s.bound;
    lemma_steps_sound rest (facts @ [s.bound]) i rho

let lemma_check_sound (c:certificate) (conclusion:expr) (facts:list expr)
                      (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    check c conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  lemma_steps_sound c.steps facts i rho;
  E.lemma_check_with_numeric_model c.refutation conclusion (accumulated c.steps facts) i rho

let inferred (conclusion:expr) (facts:list expr) : bool =
  match synthesize conclusion facts with
  | Some c -> check c conclusion facts
  | None -> false

let lemma_inferred_sound (conclusion:expr) (facts:list expr)
                         (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    inferred conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  match synthesize conclusion facts with
  | Some c -> lemma_check_sound c conclusion facts i rho
  | None -> ()
