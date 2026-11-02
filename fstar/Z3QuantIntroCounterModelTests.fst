module Z3QuantIntroCounterModelTests

(* Counter-models for the false mutants of Z3QuantIntroReplayTests: each
   claim the scoped quant-intro replay refuses there is FALSE in an
   explicitly constructed standard root model (for every u), either as the
   closed root equation (B1 wrong leaf sign, B6 missing congruence premise,
   B7 swapped congruence premises) or, for a corrupted OPEN leaf, at a
   concrete typed environment of the scope the guard assigns it (B12 under
   a VALID closed root, B2 wrong Int target, B3 de Bruijn shift). So a
   replay that accepted any of them would be unsound; the refusals are the
   checker's own verdicts, proved by normalization in
   Z3QuantIntroReplayTests.

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
