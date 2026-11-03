module Z3QuantIntroCounterModelTests

(* Counter-models for the false mutants of Z3QuantIntroReplayTests: each
   claim the scoped quant-intro replay refuses there is FALSE in an
   explicitly constructed standard root model (for every u), either as the
   closed root equation (B1 wrong leaf sign, B6 missing congruence premise,
   B7 swapped congruence premises) or, for a corrupted OPEN leaf, at a
   concrete typed environment of the scope the guard assigns it (B12 under
   a VALID closed root, B2 wrong Int target, B3 de Bruijn shift, B13
   iff/negation leaves with the wrong sign, B14 regrouping mutants). So a
   replay that accepted any of them would be unsound; the refusals are the
   checker's own verdicts, proved by normalization in
   Z3QuantIntroReplayTests. D9 also reads the A6 regrouping (the
   Pulse.Checker.Base-1 shape) in every root model.

   The models: TR.standard over free choices that interpret a free Boolean
   symbol by a fixed predicate of its declaration (`pick`), every other free
   symbol by the schema's inhabitant. The Sorted truth over the root
   scalars on top of such a model agrees with its root truth
   (Z3SortedRoot.lemma_truth_agreement); the quantifier laws are derived
   from R1 of the same model (RD.lemma_forall_model). *)

open Z3AstTheory
open Z3ValueTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3Definitions
module L = FStar.List.Tot
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module SP = Z3SortedProof
module NR = Z3NnfReplay
module R = Z3ResolutionProofTheory
module RD = Z3SortedRootDocument
module PT = Z3SortedProofTests
module RDT = Z3SortedRootDocumentTests
module BR = Z3BooleanRewrite
module B = Z3BoundedBoolEquiv
module Q = Z3SortedQuantifier
module QT = Z3QuantIntroReplayTests

(* ---------------------------------------------------------------------- *)
(* Models                                                                   *)
(* ---------------------------------------------------------------------- *)

let uf_pick (u:TR.uninterpreted) (pick:func_decl -> bool) : TR.symbols u PT.core_schema = {
  TR.apply = (fun f _ ->
    if f.range = bool_sort then TR.boolean #u PT.core_schema (pick f)
    else S.value_inhabitant PT.core_schema (TR.default_value u) f.range);
  TR.lambda = (fun bound t _ -> S.value_inhabitant PT.core_schema (TR.default_value u) (ArraySort bound t));
}

let model (u:TR.uninterpreted) (pick:func_decl -> bool) : TR.interp u PT.core_schema =
  TR.standard u PT.core_schema (uf_pick u pick)

(* The free Boolean symbols named P or p are true, all others false. *)
let named (f:func_decl) : bool = f.decl_name = "P" || f.decl_name = "p"

(* Every free Boolean symbol is false. *)
let none (f:func_decl) : bool = false

let st (u:TR.uninterpreted) (pick:func_decl -> bool) (scope:list sort)
       (rho:V.environment (TR.carrier u) (S.signature PT.core_schema) scope) (e:expr) : GTot bool =
  T.truth_at PT.core_schema (TR.booleans u) (SR.root_scalars u) (model u pick) scope rho e

let lemma_model (u:TR.uninterpreted) (pick:func_decl -> bool)
  : Lemma (TR.root_model u PT.core_schema (model u pick) /\
           Q.forall_model PT.core_schema (TR.booleans u) (model u pick)) =
  TR.lemma_standard_root u PT.core_schema (uf_pick u pick);
  RD.lemma_forall_model u PT.core_schema (model u pick)

(* A free Boolean atom reads `pick` at EVERY scope and environment. *)
let lemma_atom (u:TR.uninterpreted) (pick:func_decl -> bool) (scope:list sort)
               (rho:V.environment (TR.carrier u) (S.signature PT.core_schema) scope)
               (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped scope (App f args) /\ f.range == bool_sort /\ f.interp == None /\
                    TR.classify (S.signature PT.core_schema) f == TR.Other)
          (ensures st u pick scope rho (App f args) == pick f) =
  lemma_model u pick;
  SR.lemma_truth_agreement u PT.core_schema (model u pick) scope rho (App f args);
  TR.lemma_eval_free_choice u PT.core_schema (uf_pick u pick) scope rho f args

(* One value of sort Term (the schema's inhabitant), as a binder tuple. *)
let wterm (u:TR.uninterpreted) : V.arguments (TR.carrier u) (S.signature PT.core_schema) (L.rev [QT.term]) =
  assert_norm (L.rev [QT.term] == [QT.term]);
  [S.value_inhabitant PT.core_schema (TR.default_value u) QT.term]

let classified ()
  : Lemma (TR.classify (S.signature PT.core_schema) QT.pd == TR.Other /\
           TR.classify (S.signature PT.core_schema) QT.qd == TR.Other /\
           TR.classify (S.signature PT.core_schema) QT.rd == TR.Other /\
           TR.classify (S.signature PT.core_schema) (QT.symbol "p" [] bool_sort) == TR.Other /\
           TR.classify (S.signature PT.core_schema) (QT.symbol "q" [] bool_sort) == TR.Other /\
           T.classify SP.implies_decl == T.Implication /\ T.classify R.not_decl == T.Negation /\
           T.classify (BR.connective_decl BR.Disjunction [QT.t0; QT.t0]) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Conjunction [QT.t0; QT.t0]) == T.Nary B.And) =
  assert_norm (TR.classify (S.signature PT.core_schema) QT.pd == TR.Other);
  assert_norm (TR.classify (S.signature PT.core_schema) QT.qd == TR.Other);
  assert_norm (TR.classify (S.signature PT.core_schema) QT.rd == TR.Other);
  assert_norm (TR.classify (S.signature PT.core_schema) (QT.symbol "p" [] bool_sort) == TR.Other);
  assert_norm (TR.classify (S.signature PT.core_schema) (QT.symbol "q" [] bool_sort) == TR.Other);
  assert_norm (T.classify SP.implies_decl == T.Implication);
  assert_norm (T.classify R.not_decl == T.Negation);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [QT.t0; QT.t0]) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Conjunction [QT.t0; QT.t0]) == T.Nary B.And)

let scopes ()
  : Lemma (L.rev [QT.term] @ [] == [QT.term] /\
           L.rev [QT.term] @ (L.rev [QT.term] @ []) == [QT.term; QT.term] /\
           D.scoped [QT.term; QT.term] QT.in_l /\ D.scoped [QT.term; QT.term] QT.w_in_r /\
           D.scoped [QT.term; QT.term] (QT.mk_and [QT.q_ QT.t1 QT.t0; QT.r_ QT.t0]) /\
           D.scoped [QT.term; QT.term] (QT.q_ QT.t1 QT.t0) /\ D.scoped [QT.term; QT.term] (QT.r_ QT.t0) /\
           D.scoped [QT.term] QT.out_l /\ D.scoped [QT.term] QT.w_out_r /\
           D.scoped [QT.term] (QT.implies (QT.p_ QT.t0) QT.m_all_r) /\
           D.scoped [QT.term] QT.out_m /\ D.scoped [QT.term] QT.k_m /\
           D.scoped [QT.term] (QT.p_ QT.t0) /\ D.scoped [QT.term] (QT.neg (QT.p_ QT.t0)) /\
           D.scoped [QT.term] QT.all_l /\ D.scoped [QT.term] QT.all_r /\ D.scoped [QT.term] QT.w_all_r /\
           D.scoped [QT.term] QT.m_all_r /\
           D.scoped [QT.term] (QT.implies QT.qc QT.pc) /\ D.scoped [QT.term] QT.pc /\ D.scoped [QT.term] QT.qc /\
           D.scoped [QT.term] (QT.neg QT.pc) /\ D.scoped [QT.term] (QT.neg (QT.neg QT.pc)) /\
           D.scoped [QT.term] (QT.mk_or [QT.qc; QT.qc]) /\
           D.scoped [QT.term] (QT.implies (QT.neg (QT.neg QT.pc)) (QT.mk_or [QT.qc; QT.qc])) /\
           D.scoped [] QT.a1_lhs /\ D.scoped [] QT.b1_rhs /\ D.scoped [] QT.b6_rhs /\
           D.scoped [] QT.b7_lhs /\ D.scoped [] QT.b7_rhs) =
  assert_norm (L.rev [QT.term] @ [] == [QT.term]);
  assert_norm (L.rev [QT.term] @ (L.rev [QT.term] @ []) == [QT.term; QT.term]);
  assert_norm (D.scoped [QT.term; QT.term] QT.in_l /\ D.scoped [QT.term; QT.term] QT.w_in_r);
  assert_norm (D.scoped [QT.term; QT.term] (QT.mk_and [QT.q_ QT.t1 QT.t0; QT.r_ QT.t0]));
  assert_norm (D.scoped [QT.term; QT.term] (QT.q_ QT.t1 QT.t0) /\ D.scoped [QT.term; QT.term] (QT.r_ QT.t0));
  assert_norm (D.scoped [QT.term] QT.out_l /\ D.scoped [QT.term] QT.w_out_r);
  assert_norm (D.scoped [QT.term] (QT.implies (QT.p_ QT.t0) QT.m_all_r));
  assert_norm (D.scoped [QT.term] QT.out_m /\ D.scoped [QT.term] QT.k_m);
  assert_norm (D.scoped [QT.term] (QT.p_ QT.t0) /\ D.scoped [QT.term] (QT.neg (QT.p_ QT.t0)));
  assert_norm (D.scoped [QT.term] QT.all_l /\ D.scoped [QT.term] QT.all_r /\ D.scoped [QT.term] QT.w_all_r);
  assert_norm (D.scoped [QT.term] QT.m_all_r);
  assert_norm (D.scoped [QT.term] (QT.implies QT.qc QT.pc) /\ D.scoped [QT.term] QT.pc /\ D.scoped [QT.term] QT.qc);
  assert_norm (D.scoped [QT.term] (QT.neg QT.pc) /\ D.scoped [QT.term] (QT.neg (QT.neg QT.pc)));
  assert_norm (D.scoped [QT.term] (QT.mk_or [QT.qc; QT.qc]));
  assert_norm (D.scoped [QT.term] (QT.implies (QT.neg (QT.neg QT.pc)) (QT.mk_or [QT.qc; QT.qc])));
  assert_norm (D.scoped [] QT.a1_lhs /\ D.scoped [] QT.b1_rhs /\ D.scoped [] QT.b6_rhs);
  assert_norm (D.scoped [] QT.b7_lhs /\ D.scoped [] QT.b7_rhs)

(* The closed claim `lhs = rhs` is root-false when lhs and rhs have
   different Sorted truth. *)
let lemma_false_claim (u:TR.uninterpreted) (pick:func_decl -> bool) (lhs rhs:expr)
  : Lemma (requires D.scoped [] lhs /\ D.scoped [] rhs /\ get_sort lhs == bool_sort /\ get_sort rhs == bool_sort /\
                    st u pick [] (RD.empty_root u PT.core_schema) lhs <>
                    st u pick [] (RD.empty_root u PT.core_schema) rhs)
          (ensures TR.root_model u PT.core_schema (model u pick) /\
                   not (RD.root_holds u PT.core_schema (model u pick) (QT.eq lhs rhs))) =
  lemma_model u pick;
  T.lemma_boolean_equality_at PT.core_schema (TR.booleans u) (SR.root_scalars u) (model u pick) []
    (RD.empty_root u PT.core_schema) lhs rhs;
  RD.lemma_holds_agreement u PT.core_schema (model u pick) (QT.eq lhs rhs)

(* ---------------------------------------------------------------------- *)
(* The A1 left side is true in the named model (Q is false everywhere)      *)
(* ---------------------------------------------------------------------- *)

let lemma_a1_lhs (u:TR.uninterpreted)
  : Lemma (st u named [] (RD.empty_root u PT.core_schema) QT.a1_lhs == true) =
  let sigma = S.signature PT.core_schema in
  let i = model u named in
  let empty = RD.empty_root u PT.core_schema in
  lemma_model u named; classified (); scopes ();
  Q.lemma_forall_truth PT.core_schema (TR.booleans u) (SR.root_scalars u) i [] empty [QT.term] QT.out_l;
  let outer (vs:V.arguments (TR.carrier u) sigma (L.rev [QT.term]))
    : Lemma (st u named (L.rev [QT.term] @ []) (V.extend sigma [] (L.rev [QT.term]) vs empty) QT.out_l) =
    let r1 = V.extend sigma [] (L.rev [QT.term]) vs empty in
    Q.lemma_forall_truth PT.core_schema (TR.booleans u) (SR.root_scalars u) i (L.rev [QT.term] @ []) r1 [QT.term] QT.in_l;
    let inner (ws:V.arguments (TR.carrier u) sigma (L.rev [QT.term]))
      : Lemma (st u named (L.rev [QT.term] @ (L.rev [QT.term] @ []))
                 (V.extend sigma (L.rev [QT.term] @ []) (L.rev [QT.term]) ws r1) QT.in_l) =
      let r2 = V.extend sigma (L.rev [QT.term] @ []) (L.rev [QT.term]) ws r1 in
      lemma_atom u named (L.rev [QT.term] @ (L.rev [QT.term] @ [])) r2 QT.qd [QT.t1; QT.t0];
      NR.lemma_truth_implies PT.core_schema (TR.booleans u) (SR.root_scalars u) i
        (L.rev [QT.term] @ (L.rev [QT.term] @ [])) r2 SP.implies_decl (QT.q_ QT.t1 QT.t0) (QT.r_ QT.t0) in
    FStar.Classical.forall_intro inner;
    NR.lemma_truth_implies PT.core_schema (TR.booleans u) (SR.root_scalars u) i
      (L.rev [QT.term] @ []) r1 SP.implies_decl (QT.p_ QT.t0) QT.all_l in
  FStar.Classical.forall_intro outer

(* ---------------------------------------------------------------------- *)
(* D1 B1 (wrong leaf sign): the claimed root equation is false              *)
(* ---------------------------------------------------------------------- *)

(* forall x. (or (not (P x)) (forall y. (or (Q x y) (R y)))) is false: P is
   true, Q and R false, at the inhabitant of Term. *)
let lemma_b1_rhs (u:TR.uninterpreted)
  : Lemma (st u named [] (RD.empty_root u PT.core_schema) QT.b1_rhs == false) =
  let sigma = S.signature PT.core_schema in
  let i = model u named in
  let empty = RD.empty_root u PT.core_schema in
  lemma_model u named; classified (); scopes ();
  let r1 = V.extend sigma [] (L.rev [QT.term]) (wterm u) empty in
  let r2 = V.extend sigma (L.rev [QT.term] @ []) (L.rev [QT.term]) (wterm u) r1 in
  lemma_atom u named (L.rev [QT.term] @ (L.rev [QT.term] @ [])) r2 QT.qd [QT.t1; QT.t0];
  lemma_atom u named (L.rev [QT.term] @ (L.rev [QT.term] @ [])) r2 QT.rd [QT.t0];
  NR.lemma_truth_or2 PT.core_schema (TR.booleans u) (SR.root_scalars u) i
    (L.rev [QT.term] @ (L.rev [QT.term] @ [])) r2 (BR.connective_decl BR.Disjunction [QT.t0; QT.t0])
    (QT.q_ QT.t1 QT.t0) (QT.r_ QT.t0) B.Or;
  Q.lemma_forall_truth PT.core_schema (TR.booleans u) (SR.root_scalars u) i (L.rev [QT.term] @ []) r1 [QT.term] QT.w_in_r;
  lemma_atom u named (L.rev [QT.term] @ []) r1 QT.pd [QT.t0];
  NR.lemma_truth_not PT.core_schema (TR.booleans u) (SR.root_scalars u) i (L.rev [QT.term] @ []) r1 R.not_decl (QT.p_ QT.t0);
  NR.lemma_truth_or2 PT.core_schema (TR.booleans u) (SR.root_scalars u) i
    (L.rev [QT.term] @ []) r1 (BR.connective_decl BR.Disjunction [QT.t0; QT.t0])
    (QT.neg (QT.p_ QT.t0)) QT.w_all_r B.Or;
  Q.lemma_forall_truth PT.core_schema (TR.booleans u) (SR.root_scalars u) i [] empty [QT.term] QT.w_out_r

let d1_wrong_leaf_sign (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (model u named) /\
           not (RD.root_holds u PT.core_schema (model u named) (QT.eq QT.a1_lhs QT.b1_rhs))) =
  scopes (); lemma_a1_lhs u; lemma_b1_rhs u;
  lemma_false_claim u named QT.a1_lhs QT.b1_rhs

(* ---------------------------------------------------------------------- *)
(* D3 B6 (missing congruence premise): the claimed root equation is false   *)
(* ---------------------------------------------------------------------- *)

(* forall x. (P x => forall y. (and (Q x y) (R y))) is false: P is true and
   Q false, at the inhabitant of Term. *)
let lemma_b6_rhs (u:TR.uninterpreted)
  : Lemma (st u named [] (RD.empty_root u PT.core_schema) QT.b6_rhs == false) =
  let sigma = S.signature PT.core_schema in
  let i = model u named in
  let empty = RD.empty_root u PT.core_schema in
  lemma_model u named; classified (); scopes ();
  let r1 = V.extend sigma [] (L.rev [QT.term]) (wterm u) empty in
  let r2 = V.extend sigma (L.rev [QT.term] @ []) (L.rev [QT.term]) (wterm u) r1 in
  lemma_atom u named (L.rev [QT.term] @ (L.rev [QT.term] @ [])) r2 QT.qd [QT.t1; QT.t0];
  NR.lemma_truth_or2 PT.core_schema (TR.booleans u) (SR.root_scalars u) i
    (L.rev [QT.term] @ (L.rev [QT.term] @ [])) r2 (BR.connective_decl BR.Conjunction [QT.t0; QT.t0])
    (QT.q_ QT.t1 QT.t0) (QT.r_ QT.t0) B.And;
  Q.lemma_forall_truth PT.core_schema (TR.booleans u) (SR.root_scalars u) i (L.rev [QT.term] @ []) r1 [QT.term]
    (QT.mk_and [QT.q_ QT.t1 QT.t0; QT.r_ QT.t0]);
  lemma_atom u named (L.rev [QT.term] @ []) r1 QT.pd [QT.t0];
  NR.lemma_truth_implies PT.core_schema (TR.booleans u) (SR.root_scalars u) i
    (L.rev [QT.term] @ []) r1 SP.implies_decl (QT.p_ QT.t0) QT.m_all_r;
  Q.lemma_forall_truth PT.core_schema (TR.booleans u) (SR.root_scalars u) i [] empty [QT.term]
    (QT.implies (QT.p_ QT.t0) QT.m_all_r)

let d3_missing_premise (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (model u named) /\
           not (RD.root_holds u PT.core_schema (model u named) (QT.eq QT.a1_lhs QT.b6_rhs))) =
  scopes (); lemma_a1_lhs u; lemma_b6_rhs u;
  lemma_false_claim u named QT.a1_lhs QT.b6_rhs

(* ---------------------------------------------------------------------- *)
(* D4 B7 (swapped congruence premises): the claimed root equation is false  *)
(* ---------------------------------------------------------------------- *)

(* p true, q false: (not (not p)) => (or q q) is false, q => p is true. *)
let lemma_b7 (u:TR.uninterpreted)
  : Lemma (st u named [] (RD.empty_root u PT.core_schema) QT.b7_lhs == false /\
           st u named [] (RD.empty_root u PT.core_schema) QT.b7_rhs == true) =
  let sigma = S.signature PT.core_schema in
  let i = model u named in
  let empty = RD.empty_root u PT.core_schema in
  lemma_model u named; classified (); scopes ();
  let s1 = L.rev [QT.term] @ [] in
  let pdecl = QT.symbol "p" [] bool_sort in
  let qdecl = QT.symbol "q" [] bool_sort in
  Q.lemma_forall_truth PT.core_schema (TR.booleans u) (SR.root_scalars u) i [] empty [QT.term] (QT.implies QT.qc QT.pc);
  let all (vs:V.arguments (TR.carrier u) sigma (L.rev [QT.term]))
    : Lemma (st u named s1 (V.extend sigma [] (L.rev [QT.term]) vs empty) (QT.implies QT.qc QT.pc)) =
    let r = V.extend sigma [] (L.rev [QT.term]) vs empty in
    lemma_atom u named s1 r pdecl [];
    lemma_atom u named s1 r qdecl [];
    NR.lemma_truth_implies PT.core_schema (TR.booleans u) (SR.root_scalars u) i s1 r SP.implies_decl QT.qc QT.pc in
  FStar.Classical.forall_intro all;
  let r1 = V.extend sigma [] (L.rev [QT.term]) (wterm u) empty in
  lemma_atom u named s1 r1 pdecl [];
  lemma_atom u named s1 r1 qdecl [];
  NR.lemma_truth_not PT.core_schema (TR.booleans u) (SR.root_scalars u) i s1 r1 R.not_decl QT.pc;
  NR.lemma_truth_not PT.core_schema (TR.booleans u) (SR.root_scalars u) i s1 r1 R.not_decl (QT.neg QT.pc);
  NR.lemma_truth_or2 PT.core_schema (TR.booleans u) (SR.root_scalars u) i s1 r1
    (BR.connective_decl BR.Disjunction [QT.t0; QT.t0]) QT.qc QT.qc B.Or;
  NR.lemma_truth_implies PT.core_schema (TR.booleans u) (SR.root_scalars u) i s1 r1 SP.implies_decl
    (QT.neg (QT.neg QT.pc)) (QT.mk_or [QT.qc; QT.qc]);
  Q.lemma_forall_truth PT.core_schema (TR.booleans u) (SR.root_scalars u) i [] empty [QT.term]
    (QT.implies (QT.neg (QT.neg QT.pc)) (QT.mk_or [QT.qc; QT.qc]))

let d4_swapped_premises (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (model u named) /\
           not (RD.root_holds u PT.core_schema (model u named) (QT.eq QT.b7_lhs QT.b7_rhs))) =
  scopes (); lemma_b7 u;
  lemma_false_claim u named QT.b7_lhs QT.b7_rhs

(* ---------------------------------------------------------------------- *)
(* D5 B12 (valid closed root, corrupted used internal entry)               *)
(* ---------------------------------------------------------------------- *)

(* The corrupted open leaf (P x => A) = (and (P x) A) of B12 is FALSE at an
   environment of its assigned scope [Term] (every free Boolean false: the
   left side is true, the right side false), although the closed root
   equation it serves is true (A1 certifies it, Z3QuantIntroReplayTests C3).
   Validity at every environment of the assigned scope is exactly what the
   replay demands of each used entry. *)
let d5_corrupted_leaf (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (model u none) /\
           st u none (L.rev [QT.term] @ [])
              (V.extend (S.signature PT.core_schema) [] (L.rev [QT.term]) (wterm u) (RD.empty_root u PT.core_schema))
              QT.out_m == true /\
           st u none (L.rev [QT.term] @ [])
              (V.extend (S.signature PT.core_schema) [] (L.rev [QT.term]) (wterm u) (RD.empty_root u PT.core_schema))
              QT.k_m == false /\
           not (st u none (L.rev [QT.term] @ [])
                  (V.extend (S.signature PT.core_schema) [] (L.rev [QT.term]) (wterm u) (RD.empty_root u PT.core_schema))
                  (QT.eq QT.out_m QT.k_m))) =
  let sigma = S.signature PT.core_schema in
  let i = model u none in
  let s1 = L.rev [QT.term] @ [] in
  let r1 = V.extend sigma [] (L.rev [QT.term]) (wterm u) (RD.empty_root u PT.core_schema) in
  lemma_model u none; classified (); scopes ();
  lemma_atom u none s1 r1 QT.pd [QT.t0];
  NR.lemma_truth_implies PT.core_schema (TR.booleans u) (SR.root_scalars u) i s1 r1 SP.implies_decl (QT.p_ QT.t0) QT.all_r;
  NR.lemma_truth_or2 PT.core_schema (TR.booleans u) (SR.root_scalars u) i s1 r1
    (BR.connective_decl BR.Conjunction [QT.t0; QT.t0]) (QT.p_ QT.t0) QT.all_r B.And;
  T.lemma_boolean_equality_at PT.core_schema (TR.booleans u) (SR.root_scalars u) i s1 r1 QT.out_m QT.k_m

(* ---------------------------------------------------------------------- *)
(* D6/D7 Int leaves: B2 (wrong Int target) and B3 (de Bruijn shift)        *)
(* ---------------------------------------------------------------------- *)

(* Root truth (the root model itself, no Sorted layer) at a scope. *)
let rtruth (u:TR.uninterpreted) (pick:func_decl -> bool) (scope:list sort)
           (rho:V.environment (TR.carrier u) (S.signature PT.core_schema) scope) (e:expr) : GTot bool =
  D.scoped scope e && get_sort e = bool_sort &&
  TR.truth PT.core_schema (V.evaluate (S.signature PT.core_schema) (model u pick) scope rho e)

let rint (u:TR.uninterpreted) (pick:func_decl -> bool) (scope:list sort)
         (rho:V.environment (TR.carrier u) (S.signature PT.core_schema) scope) (e:expr) : GTot int =
  if D.scoped scope e && get_sort e = TR.int_s
  then TR.int_of PT.core_schema (V.evaluate (S.signature PT.core_schema) (model u pick) scope rho e)
  else 0

let ival (u:TR.uninterpreted) (n:int) : TR.tvalue u PT.core_schema TR.int_s =
  assert_norm (not (V.datatype_sort (S.signature PT.core_schema) TR.int_s));
  TR.lemma_carriers u;
  TR.make #u #(S.signature PT.core_schema) TR.int_s n

(* The environment of the A2 body scope [Int; Int] with x = Var 1 and
   y = Var 0. *)
let int_env (u:TR.uninterpreted) (x y:int)
  : V.environment (TR.carrier u) (S.signature PT.core_schema) ([QT.integer; QT.integer] @ []) =
  V.extend (S.signature PT.core_schema) [] [QT.integer; QT.integer] [ival u y; ival u x] (RD.empty_root u PT.core_schema)

let lemma_int_vars (u:TR.uninterpreted) (pick:func_decl -> bool) (x y:int)
  : Lemma (rint u pick ([QT.integer; QT.integer] @ []) (int_env u x y) QT.i1 == x /\
           rint u pick ([QT.integer; QT.integer] @ []) (int_env u x y) QT.i0 == y) =
  assert_norm ([QT.integer; QT.integer] @ [] == [QT.integer; QT.integer]);
  assert_norm (D.scoped [QT.integer; QT.integer] QT.i1 /\ D.scoped [QT.integer; QT.integer] QT.i0)

(* A canonical Int comparison and a canonical binary Int operation read the
   root values of their arguments (TR.lemma_operator, R2/R5). *)
let lemma_compare (u:TR.uninterpreted) (pick:func_decl -> bool) (scope:list sort)
                  (rho:V.environment (TR.carrier u) (S.signature PT.core_schema) scope)
                  (f:func_decl) (r:Z3LinearArithmeticAst.relation) (a b:expr)
  : Lemma (requires D.scoped scope (App f [a; b]) /\
                    TR.classify (S.signature PT.core_schema) f == TR.Compare TR.int_s r)
          (ensures rtruth u pick scope rho (App f [a; b]) ==
                   TR.icompare r (rint u pick scope rho a) (rint u pick scope rho b)) =
  let sigma = S.signature PT.core_schema in
  let i = model u pick in
  lemma_model u pick;
  TR.lemma_not_registered PT.core_schema f;
  TR.lemma_eval_application i scope rho f [a; b];
  let xs = V.evaluate_args sigma i scope rho [a; b] f.domain in
  TR.lemma_operator i f xs

let lemma_arith (u:TR.uninterpreted) (pick:func_decl -> bool) (scope:list sort)
                (rho:V.environment (TR.carrier u) (S.signature PT.core_schema) scope)
                (f:func_decl) (o:Z3LinearArithmeticAst.operation) (a b:expr)
  : Lemma (requires D.scoped scope (App f [a; b]) /\
                    TR.classify (S.signature PT.core_schema) f == TR.Arith TR.int_s o)
          (ensures rint u pick scope rho (App f [a; b]) ==
                   TR.icalculate o [rint u pick scope rho a; rint u pick scope rho b]) =
  let sigma = S.signature PT.core_schema in
  let i = model u pick in
  lemma_model u pick;
  TR.lemma_not_registered PT.core_schema f;
  TR.lemma_eval_application i scope rho f [a; b];
  let xs = V.evaluate_args sigma i scope rho [a; b] f.domain in
  TR.lemma_operator i f xs

let lemma_numeral (u:TR.uninterpreted) (pick:func_decl -> bool) (scope:list sort)
                  (rho:V.environment (TR.carrier u) (S.signature PT.core_schema) scope) (n:int)
  : Lemma (rint u pick scope rho (QT.num n) == n) =
  let i = model u pick in
  lemma_model u pick;
  RDT.schemas_supported ();
  TR.lemma_classify_numerals PT.core_schema n 1;
  TR.lemma_not_registered PT.core_schema (TR.int_numeral n);
  TR.lemma_eval_application i scope rho (TR.int_numeral n) [];
  TR.lemma_operator i (TR.int_numeral n) []

let int_classified ()
  : Lemma (TR.classify (S.signature PT.core_schema) (TR.gt_decl TR.int_s) == TR.Compare TR.int_s Z3LinearArithmeticAst.Gt /\
           TR.classify (S.signature PT.core_schema) (TR.le_decl TR.int_s) == TR.Compare TR.int_s Z3LinearArithmeticAst.Le /\
           TR.classify (S.signature PT.core_schema) (TR.plus_decl TR.int_s) == TR.Arith TR.int_s Z3LinearArithmeticAst.Add /\
           TR.classify (S.signature PT.core_schema) (TR.times_decl TR.int_s) == TR.Arith TR.int_s Z3LinearArithmeticAst.Mul) =
  RDT.schemas_supported ();
  TR.lemma_classify_gt PT.core_schema TR.int_s;
  TR.lemma_classify_le PT.core_schema TR.int_s;
  TR.lemma_classify_plus PT.core_schema TR.int_s;
  TR.lemma_classify_times PT.core_schema TR.int_s

(* D6 B2's corrupted leaf (x > y) = (not (y <= x)) at x = 1, y = 0: the
   left side is true, the right side false (every model, every u). The B2
   ROOT claim happens to be valid over the unbounded Int carrier, so B2 is
   another valid root whose proof reads a false open fact. *)
let d6_wrong_int_target (u:TR.uninterpreted)
  : Lemma (rtruth u none ([QT.integer; QT.integer] @ []) (int_env u 1 0) QT.gxy == true /\
           rtruth u none ([QT.integer; QT.integer] @ []) (int_env u 1 0) QT.lyx == true /\
           rtruth u none ([QT.integer; QT.integer] @ []) (int_env u 1 0) (QT.neg QT.lyx) == false) =
  let s = [QT.integer; QT.integer] @ [] in
  let rho = int_env u 1 0 in
  lemma_model u none; int_classified ();
  assert_norm ([QT.integer; QT.integer] @ [] == [QT.integer; QT.integer]);
  assert_norm (D.scoped [QT.integer; QT.integer] QT.gxy /\ D.scoped [QT.integer; QT.integer] (QT.neg QT.lyx));
  lemma_int_vars u none 1 0;
  lemma_compare u none s rho (TR.gt_decl TR.int_s) Z3LinearArithmeticAst.Gt QT.i1 QT.i0;
  lemma_compare u none s rho (TR.le_decl TR.int_s) Z3LinearArithmeticAst.Le QT.i0 QT.i1;
  Z3NnfReplayTests.lemma_not_value u (model u none) s rho QT.lyx

(* D7 B3's shifted leaf (x <= y) = (y + (-1)*y <= 0) at x = 1, y = 0: the
   left side is false, the right side true. *)
let d7_shift (u:TR.uninterpreted)
  : Lemma (rtruth u none ([QT.integer; QT.integer] @ []) (int_env u 1 0) QT.lxy == false /\
           rtruth u none ([QT.integer; QT.integer] @ []) (int_env u 1 0) QT.dyy == true) =
  let s = [QT.integer; QT.integer] @ [] in
  let rho = int_env u 1 0 in
  lemma_model u none; int_classified ();
  assert_norm ([QT.integer; QT.integer] @ [] == [QT.integer; QT.integer]);
  assert_norm (D.scoped [QT.integer; QT.integer] QT.lxy /\ D.scoped [QT.integer; QT.integer] QT.dyy);
  lemma_int_vars u none 1 0;
  lemma_compare u none s rho (TR.le_decl TR.int_s) Z3LinearArithmeticAst.Le QT.i1 QT.i0;
  lemma_numeral u none s rho (-1);
  lemma_numeral u none s rho 0;
  lemma_arith u none s rho (TR.times_decl TR.int_s) Z3LinearArithmeticAst.Mul (QT.num (-1)) QT.i0;
  lemma_arith u none s rho (TR.plus_decl TR.int_s) Z3LinearArithmeticAst.Add QT.i0 (QT.times (QT.num (-1)) QT.i0);
  lemma_compare u none s rho (TR.le_decl TR.int_s) Z3LinearArithmeticAst.Le
    (QT.plus QT.i0 (QT.times (QT.num (-1)) QT.i0)) (QT.num 0);
  assert_norm (TR.icalculate Z3LinearArithmeticAst.Mul [-1; 0] == 0);
  assert_norm (TR.icalculate Z3LinearArithmeticAst.Add [0; 0] == 0);
  assert_norm (TR.icompare Z3LinearArithmeticAst.Le 0 0 == true);
  assert_norm (QT.dyy == App (TR.le_decl TR.int_s) [QT.plus QT.i0 (QT.times (QT.num (-1)) QT.i0); QT.num 0])

(* ---------------------------------------------------------------------- *)
(* D8 B13 (iff/negation leaves of a wide disjunction, wrong sign)          *)
(* ---------------------------------------------------------------------- *)

let a4_facts ()
  : Lemma (QT.a4_o == App (BR.connective_decl BR.Disjunction QT.a4_lits) QT.a4_lits /\
           QT.a4_lits == QT.neg (QT.w_ "w1") :: L.tl QT.a4_lits /\
           T.classify (BR.connective_decl BR.Disjunction QT.a4_lits) == T.Nary B.Or /\
           TR.classify (S.signature PT.core_schema) (QT.wd "w1") == TR.Other /\
           D.scoped [QT.term] (QT.w_ "w1") /\ D.scoped [QT.term] (QT.neg (QT.w_ "w1")) /\
           D.scoped [QT.term] QT.a4_o /\ D.scoped [QT.term] (QT.neg QT.a4_o) /\
           D.scoped [QT.term] QT.a4_l /\ D.scoped [QT.term] QT.b13_r /\ D.scoped [QT.term] QT.b13_inner_r) =
  assert_norm (QT.a4_o == App (BR.connective_decl BR.Disjunction QT.a4_lits) QT.a4_lits);
  assert_norm (QT.a4_lits == QT.neg (QT.w_ "w1") :: L.tl QT.a4_lits);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction QT.a4_lits) == T.Nary B.Or);
  assert_norm (TR.classify (S.signature PT.core_schema) (QT.wd "w1") == TR.Other);
  assert_norm (D.scoped [QT.term] (QT.w_ "w1") /\ D.scoped [QT.term] (QT.neg (QT.w_ "w1")));
  assert_norm (D.scoped [QT.term] QT.a4_o /\ D.scoped [QT.term] (QT.neg QT.a4_o));
  assert_norm (D.scoped [QT.term] QT.a4_l /\ D.scoped [QT.term] QT.b13_r /\ D.scoped [QT.term] QT.b13_inner_r)

(* Both B13 leaves are the complement of the A4 leaf. At an environment of
   their scope [Term] with every free Boolean false (a false, every literal
   `not w` true, so o true) the A4 left side (= a (not o)) is true, while
   (= o a) and (= (not o) (not a)) are false: neither leaf equation holds
   there, so the two refused certificates would certify a false open fact. *)
let d8_iff_sign (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (model u none) /\
           st u none (L.rev [QT.term] @ [])
              (V.extend (S.signature PT.core_schema) [] (L.rev [QT.term]) (wterm u) (RD.empty_root u PT.core_schema))
              QT.a4_l == true /\
           st u none (L.rev [QT.term] @ [])
              (V.extend (S.signature PT.core_schema) [] (L.rev [QT.term]) (wterm u) (RD.empty_root u PT.core_schema))
              QT.b13_r == false /\
           st u none (L.rev [QT.term] @ [])
              (V.extend (S.signature PT.core_schema) [] (L.rev [QT.term]) (wterm u) (RD.empty_root u PT.core_schema))
              QT.b13_inner_r == false /\
           not (st u none (L.rev [QT.term] @ [])
                  (V.extend (S.signature PT.core_schema) [] (L.rev [QT.term]) (wterm u) (RD.empty_root u PT.core_schema))
                  (QT.eq QT.a4_l QT.b13_r)) /\
           not (st u none (L.rev [QT.term] @ [])
                  (V.extend (S.signature PT.core_schema) [] (L.rev [QT.term]) (wterm u) (RD.empty_root u PT.core_schema))
                  (QT.eq QT.a4_l QT.b13_inner_r))) =
  let sigma = S.signature PT.core_schema in
  let i = model u none in
  let sb = TR.booleans u in
  let sc = SR.root_scalars u in
  let s1 = L.rev [QT.term] @ [] in
  let r1 = V.extend sigma [] (L.rev [QT.term]) (wterm u) (RD.empty_root u PT.core_schema) in
  let t = T.truth_at PT.core_schema sb sc i s1 r1 in
  lemma_model u none; classified (); scopes (); a4_facts ();
  lemma_atom u none s1 r1 QT.pd [QT.t0];
  assert (t (QT.p_ QT.t0) == false);
  lemma_atom u none s1 r1 (QT.wd "w1") [QT.t0];
  NR.lemma_truth_not PT.core_schema sb sc i s1 r1 R.not_decl (QT.w_ "w1");
  assert (t (QT.neg (QT.w_ "w1")) == true);
  NR.lemma_truth_nary PT.core_schema sb sc i s1 r1 (BR.connective_decl BR.Disjunction QT.a4_lits) QT.a4_lits B.Or;
  assert (L.map B.Atom QT.a4_lits == B.Atom (QT.neg (QT.w_ "w1")) :: L.map B.Atom (L.tl QT.a4_lits));
  assert (B.geval_args t B.Or (L.map B.Atom QT.a4_lits) ==
          B.combine B.Or (t (QT.neg (QT.w_ "w1"))) (B.geval_args t B.Or (L.map B.Atom (L.tl QT.a4_lits))));
  assert (t QT.a4_o == true);
  NR.lemma_truth_not PT.core_schema sb sc i s1 r1 R.not_decl QT.a4_o;
  NR.lemma_truth_not PT.core_schema sb sc i s1 r1 R.not_decl (QT.p_ QT.t0);
  T.lemma_boolean_equality_at PT.core_schema sb sc i s1 r1 (QT.p_ QT.t0) (QT.neg QT.a4_o);
  assert (t QT.a4_l == true);
  T.lemma_boolean_equality_at PT.core_schema sb sc i s1 r1 QT.a4_o (QT.p_ QT.t0);
  assert (t QT.b13_r == false);
  T.lemma_boolean_equality_at PT.core_schema sb sc i s1 r1 (QT.neg QT.a4_o) (QT.neg (QT.p_ QT.t0));
  assert (t QT.b13_inner_r == false);
  T.lemma_boolean_equality_at PT.core_schema sb sc i s1 r1 QT.a4_l QT.b13_r;
  T.lemma_boolean_equality_at PT.core_schema sb sc i s1 r1 QT.a4_l QT.b13_inner_r

(* ---------------------------------------------------------------------- *)
(* D9 B14 (regrouping mutants) and the A6 regroupings in root models       *)
(* ---------------------------------------------------------------------- *)

(* The leaf scope [Term] of the A6/B14 certificates and one environment. *)
let leaf_scope : list sort = L.rev [QT.term] @ []

let leaf_env (u:TR.uninterpreted) : V.environment (TR.carrier u) (S.signature PT.core_schema) leaf_scope =
  V.extend (S.signature PT.core_schema) [] (L.rev [QT.term]) (wterm u) (RD.empty_root u PT.core_schema)

(* The free Boolean constants named in `names` are true, all others false. *)
let among (names:list string) (f:func_decl) : bool = L.mem f.decl_name names

let lemma_g (u:TR.uninterpreted) (pick:func_decl -> bool) (name:string)
  : Lemma (requires TR.classify (S.signature PT.core_schema) (QT.symbol name [] bool_sort) == TR.Other)
          (ensures T.truth_at PT.core_schema (TR.booleans u) (SR.root_scalars u) (model u pick) leaf_scope (leaf_env u)
                     (QT.g_ name) == pick (QT.symbol name [] bool_sort)) =
  assert (D.scoped leaf_scope (QT.g_ name));
  lemma_atom u pick leaf_scope (leaf_env u) (QT.symbol name [] bool_sort) []

(* A canonical n-ary node folds the truths of its arguments. *)
let lemma_node (u:TR.uninterpreted) (pick:func_decl -> bool) (f:func_decl) (args:list expr) (op:B.nary_op)
  : Lemma (requires D.scoped leaf_scope (App f args) /\ T.classify f == T.Nary op)
          (ensures T.truth_at PT.core_schema (TR.booleans u) (SR.root_scalars u) (model u pick) leaf_scope (leaf_env u)
                     (App f args) ==
                   NR.fold_truth (T.truth_at PT.core_schema (TR.booleans u) (SR.root_scalars u) (model u pick)
                                    leaf_scope (leaf_env u)) op args) =
  NR.lemma_truth_nary PT.core_schema (TR.booleans u) (SR.root_scalars u) (model u pick) leaf_scope (leaf_env u) f args op;
  NR.lemma_fold_atoms (T.truth_at PT.core_schema (TR.booleans u) (SR.root_scalars u) (model u pick)
                         leaf_scope (leaf_env u)) op args

let g_classified ()
  : Lemma (TR.classify (S.signature PT.core_schema) (QT.symbol "g1" [] bool_sort) == TR.Other /\
           TR.classify (S.signature PT.core_schema) (QT.symbol "g2" [] bool_sort) == TR.Other /\
           TR.classify (S.signature PT.core_schema) (QT.symbol "g3" [] bool_sort) == TR.Other /\
           TR.classify (S.signature PT.core_schema) (QT.symbol "g4" [] bool_sort) == TR.Other /\
           TR.classify (S.signature PT.core_schema) QT.fake_or == TR.Other /\
           T.classify QT.xor_d == T.Nary B.Xor /\
           leaf_scope == [QT.term]) =
  assert_norm (TR.classify (S.signature PT.core_schema) (QT.symbol "g1" [] bool_sort) == TR.Other);
  assert_norm (TR.classify (S.signature PT.core_schema) (QT.symbol "g2" [] bool_sort) == TR.Other);
  assert_norm (TR.classify (S.signature PT.core_schema) (QT.symbol "g3" [] bool_sort) == TR.Other);
  assert_norm (TR.classify (S.signature PT.core_schema) (QT.symbol "g4" [] bool_sort) == TR.Other);
  assert_norm (TR.classify (S.signature PT.core_schema) QT.fake_or == TR.Other);
  assert_norm (T.classify QT.xor_d == T.Nary B.Xor);
  assert_norm (leaf_scope == [QT.term])

(* The atoms g1..g4 read `among names` in the model `among names`. *)
let lemma_gs (u:TR.uninterpreted) (names:list string)
  : Lemma (T.truth_at PT.core_schema (TR.booleans u) (SR.root_scalars u) (model u (among names)) leaf_scope (leaf_env u)
             (QT.g_ "g1") == L.mem "g1" names /\
           T.truth_at PT.core_schema (TR.booleans u) (SR.root_scalars u) (model u (among names)) leaf_scope (leaf_env u)
             (QT.g_ "g2") == L.mem "g2" names /\
           T.truth_at PT.core_schema (TR.booleans u) (SR.root_scalars u) (model u (among names)) leaf_scope (leaf_env u)
             (QT.g_ "g3") == L.mem "g3" names /\
           T.truth_at PT.core_schema (TR.booleans u) (SR.root_scalars u) (model u (among names)) leaf_scope (leaf_env u)
             (QT.g_ "g4") == L.mem "g4" names) =
  g_classified ();
  lemma_g u (among names) "g1"; lemma_g u (among names) "g2";
  lemma_g u (among names) "g3"; lemma_g u (among names) "g4"

(* The leaf equation `l = r` is false at the environment when its sides
   have opposite values there. *)
let lemma_leaf_false (u:TR.uninterpreted) (pick:func_decl -> bool) (l r:expr)
  : Lemma (requires D.scoped leaf_scope l /\ D.scoped leaf_scope r /\ get_sort l == bool_sort /\ get_sort r == bool_sort /\
                    st u pick leaf_scope (leaf_env u) l <> st u pick leaf_scope (leaf_env u) r)
          (ensures TR.root_model u PT.core_schema (model u pick) /\
                   not (st u pick leaf_scope (leaf_env u) (QT.eq l r))) =
  lemma_model u pick;
  T.lemma_boolean_equality_at PT.core_schema (TR.booleans u) (SR.root_scalars u) (model u pick) leaf_scope (leaf_env u) l r

let g1 : expr = QT.g_ "g1"
let g2 : expr = QT.g_ "g2"
let g3 : expr = QT.g_ "g3"
let g4 : expr = QT.g_ "g4"

let b14_facts ()
  : Lemma (QT.b14_or3 == QT.mk_or [g1; g2; g3] /\
           QT.b14_dropped == (QT.b14_or3, QT.mk_or [QT.mk_or [g1; g2]]) /\
           QT.b14_extra == (QT.mk_or [g1; g2], QT.mk_or [QT.mk_or [g1; g2]; g3]) /\
           QT.b14_swapped == (QT.mk_or [g1; g2; g3; g4], QT.mk_or [QT.mk_and [g1; g2]; QT.mk_or [g3; g4]]) /\
           QT.b14_counterfeit == (QT.b14_or3, QT.mk_or [App QT.fake_or [g1; g2]; g3]) /\
           QT.b14_xor == (QT.b14_or3, QT.mk_or [App QT.xor_d [g1; g2]; g3]) /\
           QT.b14_polarity == (QT.b14_or3, QT.mk_or [QT.mk_or [g1; QT.neg g2]; g3]) /\
           QT.b14_wrong_atom == (QT.b14_or3, QT.mk_or [QT.mk_or [g1; g2]; g4]) /\
           QT.b14_empty == (QT.mk_or [], QT.mk_and []) /\
           T.classify (BR.connective_decl BR.Disjunction [g1; g2; g3]) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Disjunction [g1; g2; g3; g4]) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Disjunction [g1; g2]) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Disjunction [g3; g4]) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Conjunction [g1; g2]) == T.Nary B.And /\
           T.classify (BR.connective_decl BR.Disjunction [QT.mk_or [g1; g2]]) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Disjunction [QT.mk_or [g1; g2]; g3]) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Disjunction [QT.mk_or [g1; g2]; g4]) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Disjunction [QT.mk_and [g1; g2]; QT.mk_or [g3; g4]]) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Disjunction [App QT.fake_or [g1; g2]; g3]) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Disjunction [App QT.xor_d [g1; g2]; g3]) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Disjunction [g1; QT.neg g2]) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Disjunction [QT.mk_or [g1; QT.neg g2]; g3]) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Disjunction []) == T.Nary B.Or /\
           T.classify (BR.connective_decl BR.Conjunction []) == T.Nary B.And /\
           D.scoped leaf_scope (QT.mk_or [g1; g2; g3]) /\ D.scoped leaf_scope (QT.mk_or [g1; g2; g3; g4]) /\
           D.scoped leaf_scope (QT.mk_or [QT.mk_or [g1; g2]]) /\ D.scoped leaf_scope (QT.mk_or [QT.mk_or [g1; g2]; g3]) /\
           D.scoped leaf_scope (QT.mk_or [QT.mk_or [g1; g2]; g4]) /\
           D.scoped leaf_scope (QT.mk_or [QT.mk_and [g1; g2]; QT.mk_or [g3; g4]]) /\
           D.scoped leaf_scope (QT.mk_or [App QT.fake_or [g1; g2]; g3]) /\
           D.scoped leaf_scope (QT.mk_or [App QT.xor_d [g1; g2]; g3]) /\
           D.scoped leaf_scope (QT.mk_or [QT.mk_or [g1; QT.neg g2]; g3]) /\
           D.scoped leaf_scope (QT.mk_or []) /\ D.scoped leaf_scope (QT.mk_and []) /\
           D.scoped leaf_scope (QT.mk_or [g1; g2]) /\ D.scoped leaf_scope (QT.mk_or [g3; g4]) /\
           D.scoped leaf_scope (QT.mk_and [g1; g2]) /\ D.scoped leaf_scope (App QT.fake_or [g1; g2]) /\
           D.scoped leaf_scope (App QT.xor_d [g1; g2]) /\ D.scoped leaf_scope (QT.mk_or [g1; QT.neg g2]) /\
           D.scoped leaf_scope (QT.neg g2)) =
  assert_norm (QT.b14_or3 == QT.mk_or [g1; g2; g3]);
  assert_norm (QT.b14_dropped == (QT.b14_or3, QT.mk_or [QT.mk_or [g1; g2]]));
  assert_norm (QT.b14_extra == (QT.mk_or [g1; g2], QT.mk_or [QT.mk_or [g1; g2]; g3]));
  assert_norm (QT.b14_swapped == (QT.mk_or [g1; g2; g3; g4], QT.mk_or [QT.mk_and [g1; g2]; QT.mk_or [g3; g4]]));
  assert_norm (QT.b14_counterfeit == (QT.b14_or3, QT.mk_or [App QT.fake_or [g1; g2]; g3]));
  assert_norm (QT.b14_xor == (QT.b14_or3, QT.mk_or [App QT.xor_d [g1; g2]; g3]));
  assert_norm (QT.b14_polarity == (QT.b14_or3, QT.mk_or [QT.mk_or [g1; QT.neg g2]; g3]));
  assert_norm (QT.b14_wrong_atom == (QT.b14_or3, QT.mk_or [QT.mk_or [g1; g2]; g4]));
  assert_norm (QT.b14_empty == (QT.mk_or [], QT.mk_and []));
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [g1; g2; g3]) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [g1; g2; g3; g4]) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [g1; g2]) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [g3; g4]) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Conjunction [g1; g2]) == T.Nary B.And);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [QT.mk_or [g1; g2]]) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [QT.mk_or [g1; g2]; g3]) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [QT.mk_or [g1; g2]; g4]) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [QT.mk_and [g1; g2]; QT.mk_or [g3; g4]]) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [App QT.fake_or [g1; g2]; g3]) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [App QT.xor_d [g1; g2]; g3]) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [g1; QT.neg g2]) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [QT.mk_or [g1; QT.neg g2]; g3]) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction []) == T.Nary B.Or);
  assert_norm (T.classify (BR.connective_decl BR.Conjunction []) == T.Nary B.And);
  assert_norm (D.scoped leaf_scope (QT.mk_or [g1; g2; g3]) /\ D.scoped leaf_scope (QT.mk_or [g1; g2; g3; g4]));
  assert_norm (D.scoped leaf_scope (QT.mk_or [QT.mk_or [g1; g2]]) /\
               D.scoped leaf_scope (QT.mk_or [QT.mk_or [g1; g2]; g3]));
  assert_norm (D.scoped leaf_scope (QT.mk_or [QT.mk_or [g1; g2]; g4]) /\
               D.scoped leaf_scope (QT.mk_or [QT.mk_and [g1; g2]; QT.mk_or [g3; g4]]));
  assert_norm (D.scoped leaf_scope (QT.mk_or [App QT.fake_or [g1; g2]; g3]) /\
               D.scoped leaf_scope (QT.mk_or [App QT.xor_d [g1; g2]; g3]));
  assert_norm (D.scoped leaf_scope (QT.mk_or [QT.mk_or [g1; QT.neg g2]; g3]) /\
               D.scoped leaf_scope (QT.mk_or []) /\ D.scoped leaf_scope (QT.mk_and []));
  assert_norm (D.scoped leaf_scope (QT.mk_or [g1; g2]) /\ D.scoped leaf_scope (QT.mk_or [g3; g4]));
  assert_norm (D.scoped leaf_scope (QT.mk_and [g1; g2]) /\ D.scoped leaf_scope (App QT.fake_or [g1; g2]));
  assert_norm (D.scoped leaf_scope (App QT.xor_d [g1; g2]) /\ D.scoped leaf_scope (QT.mk_or [g1; QT.neg g2]));
  assert_norm (D.scoped leaf_scope (QT.neg g2))

(* Each B14 mutant leaf, in a standard root model of every u, at an
   environment of its scope [Term]: the two sides have OPPOSITE values, so
   the refused leaf equation is false there. *)
let st9 (u:TR.uninterpreted) (names:list string) (e:expr) : GTot bool =
  st u (among names) leaf_scope (leaf_env u) e

let d9_dropped_extra_wrong (u:TR.uninterpreted)
  : Lemma (st9 u ["g3"] (fst QT.b14_dropped) == true /\ st9 u ["g3"] (snd QT.b14_dropped) == false /\
           st9 u ["g3"] (fst QT.b14_extra) == false /\ st9 u ["g3"] (snd QT.b14_extra) == true /\
           st9 u ["g3"] (fst QT.b14_wrong_atom) == true /\ st9 u ["g3"] (snd QT.b14_wrong_atom) == false) =
  let n = ["g3"] in
  let p = among n in
  b14_facts (); lemma_gs u n;
  assert_norm (L.mem "g1" n == false /\ L.mem "g2" n == false /\ L.mem "g3" n == true /\ L.mem "g4" n == false);
  lemma_node u p (BR.connective_decl BR.Disjunction [g1; g2; g3]) [g1; g2; g3] B.Or;
  lemma_node u p (BR.connective_decl BR.Disjunction [g1; g2]) [g1; g2] B.Or;
  lemma_node u p (BR.connective_decl BR.Disjunction [QT.mk_or [g1; g2]]) [QT.mk_or [g1; g2]] B.Or;
  lemma_node u p (BR.connective_decl BR.Disjunction [QT.mk_or [g1; g2]; g3]) [QT.mk_or [g1; g2]; g3] B.Or;
  lemma_node u p (BR.connective_decl BR.Disjunction [QT.mk_or [g1; g2]; g4]) [QT.mk_or [g1; g2]; g4] B.Or

let d9_swapped_counterfeit (u:TR.uninterpreted)
  : Lemma (st9 u ["g1"] (fst QT.b14_swapped) == true /\ st9 u ["g1"] (snd QT.b14_swapped) == false /\
           st9 u ["g1"] (fst QT.b14_counterfeit) == true /\ st9 u ["g1"] (snd QT.b14_counterfeit) == false) =
  let n = ["g1"] in
  let p = among n in
  b14_facts (); lemma_gs u n; g_classified ();
  assert_norm (L.mem "g1" n == true /\ L.mem "g2" n == false /\ L.mem "g3" n == false /\ L.mem "g4" n == false);
  assert_norm (among n QT.fake_or == false);
  lemma_node u p (BR.connective_decl BR.Disjunction [g1; g2; g3; g4]) [g1; g2; g3; g4] B.Or;
  lemma_node u p (BR.connective_decl BR.Conjunction [g1; g2]) [g1; g2] B.And;
  lemma_node u p (BR.connective_decl BR.Disjunction [g3; g4]) [g3; g4] B.Or;
  lemma_node u p (BR.connective_decl BR.Disjunction [QT.mk_and [g1; g2]; QT.mk_or [g3; g4]])
    [QT.mk_and [g1; g2]; QT.mk_or [g3; g4]] B.Or;
  lemma_node u p (BR.connective_decl BR.Disjunction [g1; g2; g3]) [g1; g2; g3] B.Or;
  lemma_atom u p leaf_scope (leaf_env u) QT.fake_or [g1; g2];
  lemma_node u p (BR.connective_decl BR.Disjunction [App QT.fake_or [g1; g2]; g3]) [App QT.fake_or [g1; g2]; g3] B.Or

let d9_xor (u:TR.uninterpreted)
  : Lemma (st9 u ["g1"; "g2"] (fst QT.b14_xor) == true /\ st9 u ["g1"; "g2"] (snd QT.b14_xor) == false) =
  let n = ["g1"; "g2"] in
  let p = among n in
  b14_facts (); lemma_gs u n; g_classified ();
  assert_norm (L.mem "g1" n == true /\ L.mem "g2" n == true /\ L.mem "g3" n == false);
  lemma_node u p (BR.connective_decl BR.Disjunction [g1; g2; g3]) [g1; g2; g3] B.Or;
  lemma_node u p QT.xor_d [g1; g2] B.Xor;
  lemma_node u p (BR.connective_decl BR.Disjunction [App QT.xor_d [g1; g2]; g3]) [App QT.xor_d [g1; g2]; g3] B.Or

let d9_polarity (u:TR.uninterpreted)
  : Lemma (st9 u ["g2"] (fst QT.b14_polarity) == true /\ st9 u ["g2"] (snd QT.b14_polarity) == false) =
  let n = ["g2"] in
  let p = among n in
  b14_facts (); lemma_gs u n;
  assert_norm (L.mem "g1" n == false /\ L.mem "g2" n == true /\ L.mem "g3" n == false);
  NR.lemma_truth_not PT.core_schema (TR.booleans u) (SR.root_scalars u) (model u p) leaf_scope (leaf_env u) R.not_decl g2;
  lemma_node u p (BR.connective_decl BR.Disjunction [g1; g2; g3]) [g1; g2; g3] B.Or;
  lemma_node u p (BR.connective_decl BR.Disjunction [g1; QT.neg g2]) [g1; QT.neg g2] B.Or;
  lemma_node u p (BR.connective_decl BR.Disjunction [QT.mk_or [g1; QT.neg g2]; g3]) [QT.mk_or [g1; QT.neg g2]; g3] B.Or

let d9_empty (u:TR.uninterpreted)
  : Lemma (st9 u [] (fst QT.b14_empty) == false /\ st9 u [] (snd QT.b14_empty) == true) =
  b14_facts ();
  lemma_node u (among []) (BR.connective_decl BR.Disjunction []) [] B.Or;
  lemma_node u (among []) (BR.connective_decl BR.Conjunction []) [] B.And

(* Hence every refused B14 leaf equation is FALSE at that environment of
   its assigned scope. *)
let d9_regrouping_mutants (u:TR.uninterpreted)
  : Lemma (not (st9 u ["g3"] (QT.eq (fst QT.b14_dropped) (snd QT.b14_dropped))) /\
           not (st9 u ["g3"] (QT.eq (fst QT.b14_extra) (snd QT.b14_extra))) /\
           not (st9 u ["g1"] (QT.eq (fst QT.b14_swapped) (snd QT.b14_swapped))) /\
           not (st9 u ["g1"] (QT.eq (fst QT.b14_counterfeit) (snd QT.b14_counterfeit))) /\
           not (st9 u ["g1"; "g2"] (QT.eq (fst QT.b14_xor) (snd QT.b14_xor))) /\
           not (st9 u ["g2"] (QT.eq (fst QT.b14_polarity) (snd QT.b14_polarity))) /\
           not (st9 u ["g3"] (QT.eq (fst QT.b14_wrong_atom) (snd QT.b14_wrong_atom))) /\
           not (st9 u [] (QT.eq (fst QT.b14_empty) (snd QT.b14_empty)))) =
  b14_facts ();
  d9_dropped_extra_wrong u; d9_swapped_counterfeit u; d9_xor u; d9_polarity u; d9_empty u;
  lemma_leaf_false u (among ["g3"]) (fst QT.b14_dropped) (snd QT.b14_dropped);
  lemma_leaf_false u (among ["g3"]) (fst QT.b14_extra) (snd QT.b14_extra);
  lemma_leaf_false u (among ["g1"]) (fst QT.b14_swapped) (snd QT.b14_swapped);
  lemma_leaf_false u (among ["g1"]) (fst QT.b14_counterfeit) (snd QT.b14_counterfeit);
  lemma_leaf_false u (among ["g1"; "g2"]) (fst QT.b14_xor) (snd QT.b14_xor);
  lemma_leaf_false u (among ["g2"]) (fst QT.b14_polarity) (snd QT.b14_polarity);
  lemma_leaf_false u (among ["g3"]) (fst QT.b14_wrong_atom) (snd QT.b14_wrong_atom);
  lemma_leaf_false u (among []) (fst QT.b14_empty) (snd QT.b14_empty)

(* The A6 Base-1 shape in the root models: in EVERY root model, at EVERY
   typed environment of the leaf scope [Term], both sides have one ROOT
   truth value (the Sorted truth over the root scalars of the same
   interpretation, which A6's every-Sorted-model theorem equates, agrees
   with its root truth: Z3SortedRoot.lemma_truth_agreement). *)
let rtruth_in (u:TR.uninterpreted) (i:TR.interp u PT.core_schema) (scope:list sort)
              (rho:V.environment (TR.carrier u) (S.signature PT.core_schema) scope) (e:expr) : GTot bool =
  D.scoped scope e && get_sort e = bool_sort &&
  TR.truth PT.core_schema (V.evaluate (S.signature PT.core_schema) i scope rho e)

let d9_a6_root (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
               (rho:V.environment (TR.carrier u) (S.signature PT.core_schema) [QT.term])
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures rtruth_in u i [QT.term] rho QT.a6_l == rtruth_in u i [QT.term] rho QT.a6_r) =
  QT.a6_valid PT.core_schema (TR.booleans u) (SR.root_scalars u) i rho;
  assert_norm (D.scoped [QT.term] QT.a6_l /\ D.scoped [QT.term] QT.a6_r /\
               get_sort QT.a6_l == bool_sort /\ get_sort QT.a6_r == bool_sort);
  NR.lemma_same_at PT.core_schema (TR.booleans u) (SR.root_scalars u) i [QT.term] rho QT.a6_l QT.a6_r;
  SR.lemma_truth_agreement u PT.core_schema i [QT.term] rho QT.a6_l;
  SR.lemma_truth_agreement u PT.core_schema i [QT.term] rho QT.a6_r
