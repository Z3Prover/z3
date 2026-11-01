module Z3SortedRootDocumentTests

(* G2 document slice tests (PROTOTYPE, not in the default route).

   The nine positive documents (B1-B9) are ACTUAL Z3ProofDocument.document
   values run through the ACTUAL checker (Z3SortedProof.check_document, by
   normalization), gated by the root-specific
   Z3SortedRootDocument.check_root_document, and then falsified in EVERY
   root model (Z3SortedRootDocument.lemma_root_certified, any u, any i with
   TR.root_model) and in the standard root model for EVERY u and uf
   (standard_joint_documents). Four further certified variants (the D8 and
   D10 minimal pairs, F1 and F2) are checked for their RootCertified verdict
   only; they are not run through the falsification lemmas.
   Negative controls report the actual verdict of the gate (Rejected,
   Pending, Uncovered); the false-input controls also come with a
   positively proved counter-model (the assertions hold in a standard root
   model), so certifying them would have been unsound. Fixtures of
   Z3SortedProofTests are reused (same schemas and documents). *)

open Z3AstTheory
open Z3ValueTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module D = Z3Definitions
module L = FStar.List.Tot
module TR = Z3TypedRoot
module SP = Z3SortedProof
module P = Z3ProofDocument
module U = Z3UnifiedProof
module R = Z3ResolutionProofTheory
module BR = Z3BooleanRewrite
module PT = Z3SortedProofTests
module RD = Z3SortedRootDocument

(* ---------------------------------------------------------------------- *)
(* Shared shapes                                                            *)
(* ---------------------------------------------------------------------- *)

let integer : sort = TR.int_s
let real : sort = TR.real_s
let three : expr = App (TR.int_numeral 3) []
let one : expr = App (TR.int_numeral 1) []

let const (name:string) (s:sort) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = [] } []

let unary (name:string) (d r:sort) : func_decl =
  { decl_name = name; domain = [d]; range = r; interp = None; int_params = [] }

let disjunction (es:list expr) : expr = App (BR.connective_decl BR.Disjunction es) es

let entry (r:U.rule) (f:expr) (ids:list int) : P.entry = { P.rule = r; formula = f; premise_ids = ids }

let doc (assertions:list expr) (entries:list P.entry) (root:int) : P.document = {
  P.declarations = []; P.expressions = []; P.assertions = assertions; P.entries = entries; P.root = root;
}

(* A two-assertion refutation shape: facts a and (not a) resolve to false. *)
let refute_pair (a:expr) : P.document =
  doc [a; R.mk_not_expr a]
      [entry U.Asserted a []; entry U.Asserted (R.mk_not_expr a) []; entry U.UnitResolution R.false_expr [0; 1]]
      2

(* An equality refutation: from x = y, the checker derives (by its
   equality/congruence kernel) the conclusion c, which the second
   assertion denies. *)
let refute_equality (x y c:expr) : P.document =
  doc [R.mk_eq_expr x y; R.mk_not_expr c]
      [entry U.Asserted (R.mk_eq_expr x y) [];
       entry U.Congruence c [0];
       entry U.Asserted (R.mk_not_expr c) [];
       entry U.UnitResolution R.false_expr [1; 2]]
      3

(* ---------------------------------------------------------------------- *)
(* A. The two fixture schemas are supported (root coverage)                *)
(* ---------------------------------------------------------------------- *)

let schemas_supported () : Lemma (TR.supported PT.schema /\ TR.supported PT.core_schema) =
  assert_norm (TR.supported PT.schema);
  assert_norm (TR.supported PT.core_schema)

(* ---------------------------------------------------------------------- *)
(* B. Positive controls, one per claimed family                             *)
(* ---------------------------------------------------------------------- *)

(* B1 datatype exhaustiveness (R5 through S.find_recognizer). *)
let b1_certified () : Lemma (RD.check_root_document PT.schema PT.exhaustive_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.schema PT.exhaustive_document == RD.RootCertified)

(* B2 equality transport of a recognizer fact. *)
let b2_certified () : Lemma (RD.check_root_document PT.schema PT.equality_exclusion_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.schema PT.equality_exclusion_document == RD.RootCertified)

(* B3 constructor/matched-selector conflict (R4, R6). *)
let b3_certified () : Lemma (RD.check_root_document PT.schema PT.constructor_conflict_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.schema PT.constructor_conflict_document == RD.RootCertified)

(* B4 propositional core. *)
let b4_certified () : Lemma (RD.check_root_document PT.core_schema PT.core_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema PT.core_document == RD.RootCertified)

(* B5 quantifier instantiation (Q.check, forall_elimination_model from R1):
   forall y:Int. pi(y) and not pi(3). *)
let pi_decl : func_decl = unary "pi" integer bool_sort
let all_pi : expr = Quantifier Forall_k [integer] bool_sort (App pi_decl [Var 0 integer])
let pi_at (t:expr) : expr = App pi_decl [t]
let qi_clause (inst:expr) : expr = disjunction [R.mk_not_expr all_pi; inst]

let qi_document (args:list expr) (inst:expr) : P.document =
  doc [all_pi; R.mk_not_expr inst]
      [entry (U.QuantifierInstantiation args) (qi_clause inst) [];
       entry U.Asserted all_pi [];
       entry U.Asserted (R.mk_not_expr inst) [];
       entry U.UnitResolution R.false_expr [0; 1; 2]]
      3

let b5_document : P.document = qi_document [three] (pi_at three)

let b5_certified () : Lemma (RD.check_root_document PT.core_schema b5_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema b5_document == RD.RootCertified)

(* B6 quantifier flattening (Q.check_flatten, forall_model from R1), with
   heterogeneous typed binders (Box, Bool, Int) of the fixture. *)
let b6_document : P.document =
  doc [PT.pull_nested; R.mk_not_expr PT.pull_flat]
      [entry U.Asserted PT.pull_nested [];
       entry U.PullQuantifier (R.mk_eq_expr PT.pull_nested PT.pull_flat) [];
       entry U.ModusPonens PT.pull_flat [0; 1];
       entry U.Asserted (R.mk_not_expr PT.pull_flat) [];
       entry U.UnitResolution R.false_expr [2; 3]]
      4

let b6_certified () : Lemma (RD.check_root_document PT.schema b6_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.schema b6_document == RD.RootCertified)

(* B7 congruence over REAL-valued array constants (infinite ghost function
   carriers), as opaque terms: a = b |- g(a) = g(b). No array law is used. *)
let arr_ir : sort = ArraySort [integer] real
let a_arr : expr = const "a" arr_ir
let b_arr : expr = const "b" arr_ir
let g_decl : func_decl = unary "g" arr_ir real

let b7_document : P.document =
  refute_equality a_arr b_arr (R.mk_eq_expr (App g_decl [a_arr]) (App g_decl [b_arr]))

let b7_certified () : Lemma (RD.check_root_document PT.core_schema b7_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema b7_document == RD.RootCertified)

(* B8 lambda TERMS as opaque congruence: (lambda y. f y) = (lambda y. h y)
   |- select(lambda y. f y, 3) = select(lambda y. h y, 3). *)
let f_decl : func_decl = unary "f" integer real
let h_decl : func_decl = unary "h" integer real
let lam (fd:func_decl) : expr = Quantifier Lambda_k [integer] arr_ir (App fd [Var 0 integer])
let sel (t:expr) : expr = App (TR.select_decl [integer] real) [t; three]

let b8_document : P.document =
  refute_equality (lam f_decl) (lam h_decl) (R.mk_eq_expr (sel (lam f_decl)) (sel (lam h_decl)))

let b8_certified () : Lemma (RD.check_root_document PT.core_schema b8_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema b8_document == RD.RootCertified)

(* B9 Int linear arithmetic (Z3SortedArithmetic.equivalent, the Int layer
   = R2 Int laws): not (x + 1 = 1 + x). *)
let x_int : expr = const "x" integer
let iplus (a b:expr) : expr = App (TR.plus_decl integer) [a; b]
let commuted : expr = R.mk_eq_expr (iplus x_int one) (iplus one x_int)

let b9_document : P.document =
  doc [R.mk_not_expr commuted]
      [entry U.RewriteRule commuted []; entry U.Asserted (R.mk_not_expr commuted) [];
       entry U.UnitResolution R.false_expr [0; 1]]
      2

let b9_certified () : Lemma (RD.check_root_document PT.core_schema b9_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema b9_document == RD.RootCertified)

(* ---------------------------------------------------------------------- *)
(* C. The certified theorem in EVERY root model and every standard model    *)
(* ---------------------------------------------------------------------- *)

let falsified (u:TR.uninterpreted) (sch:S.checked_schema) (d:P.document) (i:TR.interp u sch) : prop =
  RD.typed_assertions d.P.assertions /\ not (RD.root_truths u sch i d.P.assertions)

let box_documents_false (u:TR.uninterpreted) (i:TR.interp u PT.schema)
  : Lemma (requires TR.root_model u PT.schema i)
          (ensures falsified u PT.schema PT.exhaustive_document i /\
                   falsified u PT.schema PT.equality_exclusion_document i /\
                   falsified u PT.schema PT.constructor_conflict_document i /\
                   falsified u PT.schema b6_document i) =
  b1_certified (); RD.lemma_root_certified u PT.schema PT.exhaustive_document i;
  b2_certified (); RD.lemma_root_certified u PT.schema PT.equality_exclusion_document i;
  b3_certified (); RD.lemma_root_certified u PT.schema PT.constructor_conflict_document i;
  b6_certified (); RD.lemma_root_certified u PT.schema b6_document i

let core_documents_false (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema PT.core_document i /\
                   falsified u PT.core_schema b5_document i /\
                   falsified u PT.core_schema b7_document i /\
                   falsified u PT.core_schema b8_document i /\
                   falsified u PT.core_schema b9_document i) =
  b4_certified (); RD.lemma_root_certified u PT.core_schema PT.core_document i;
  b5_certified (); RD.lemma_root_certified u PT.core_schema b5_document i;
  b7_certified (); RD.lemma_root_certified u PT.core_schema b7_document i;
  b8_certified (); RD.lemma_root_certified u PT.core_schema b8_document i;
  b9_certified (); RD.lemma_root_certified u PT.core_schema b9_document i

(* Joint: for EVERY carrier choice u and EVERY free choices uf, uf', the
   standard root models (L1) are root models and falsify every positive
   document. No legacy model_sound and no assumed hypothesis. *)
let standard_joint_documents (u:TR.uninterpreted) (uf:TR.symbols u PT.schema) (uf':TR.symbols u PT.core_schema)
  : Lemma (TR.root_model u PT.schema (TR.standard u PT.schema uf) /\
           TR.root_model u PT.core_schema (TR.standard u PT.core_schema uf') /\
           falsified u PT.schema PT.exhaustive_document (TR.standard u PT.schema uf) /\
           falsified u PT.schema PT.equality_exclusion_document (TR.standard u PT.schema uf) /\
           falsified u PT.schema PT.constructor_conflict_document (TR.standard u PT.schema uf) /\
           falsified u PT.schema b6_document (TR.standard u PT.schema uf) /\
           falsified u PT.core_schema PT.core_document (TR.standard u PT.core_schema uf') /\
           falsified u PT.core_schema b5_document (TR.standard u PT.core_schema uf') /\
           falsified u PT.core_schema b7_document (TR.standard u PT.core_schema uf') /\
           falsified u PT.core_schema b8_document (TR.standard u PT.core_schema uf') /\
           falsified u PT.core_schema b9_document (TR.standard u PT.core_schema uf')) =
  TR.lemma_standard_root u PT.schema uf;
  TR.lemma_standard_root u PT.core_schema uf';
  box_documents_false u (TR.standard u PT.schema uf);
  core_documents_false u (TR.standard u PT.core_schema uf')

(* ---------------------------------------------------------------------- *)
(* D. Negative controls: actual verdicts of the gate                        *)
(* ---------------------------------------------------------------------- *)

(* D1 a removed original assertion: the Asserted entry is no longer an
   original input. *)
let d1_document : P.document = { PT.core_document with P.assertions = [PT.proposition] }

let d1_rejected () : Lemma (RD.check_root_document PT.core_schema d1_document == RD.RootRejected) =
  assert_norm (RD.check_root_document PT.core_schema d1_document == RD.RootRejected)

(* D2 an unjustified step: false from p alone is an open obligation. *)
let d2_document : P.document =
  doc [PT.proposition]
      [entry U.Asserted PT.proposition []; entry U.UnitResolution R.false_expr [0]]
      1

let d2_pending () : Lemma (RD.check_root_document PT.core_schema d2_document == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema d2_document == RD.RootPending 1)

(* D3 a wrong root (an asserted fact, not false). *)
let d3_rejected () : Lemma (RD.check_root_document PT.core_schema ({ PT.core_document with P.root = 0 }) ==
                            RD.RootRejected) =
  assert_norm (RD.check_root_document PT.core_schema ({ PT.core_document with P.root = 0 }) == RD.RootRejected)

(* D4 a forward premise (index 2 is not yet checked when entry 1 is). *)
let d4_document : P.document =
  doc [PT.proposition; R.mk_not_expr PT.proposition]
      [entry U.Asserted PT.proposition [];
       entry U.UnitResolution R.false_expr [0; 2];
       entry U.Asserted (R.mk_not_expr PT.proposition) []]
      1

let d4_rejected () : Lemma (RD.check_root_document PT.core_schema d4_document == RD.RootRejected) =
  assert_norm (RD.check_root_document PT.core_schema d4_document == RD.RootRejected)

(* D5 a missing premise id. *)
let d5_document : P.document =
  doc [PT.proposition; R.mk_not_expr PT.proposition]
      [entry U.Asserted PT.proposition [];
       entry U.Asserted (R.mk_not_expr PT.proposition) [];
       entry U.UnitResolution R.false_expr [0; 7]]
      2

let d5_rejected () : Lemma (RD.check_root_document PT.core_schema d5_document == RD.RootRejected) =
  assert_norm (RD.check_root_document PT.core_schema d5_document == RD.RootRejected)

(* D6 an ill-scoped original assertion (an unbound variable). *)
let d6_rejected () : Lemma (RD.check_root_document PT.core_schema (refute_pair (Var 0 bool_sort)) ==
                            RD.RootRejected) =
  assert_norm (RD.check_root_document PT.core_schema (refute_pair (Var 0 bool_sort)) == RD.RootRejected)

(* D7 an instantiation argument of the wrong sort (Real for an Int binder):
   the instantiation is not checked, one obligation stays open. *)
let d7_pending () : Lemma (RD.check_root_document PT.core_schema
                             (qi_document [App (TR.real_numeral 3 1) []] (pi_at three)) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema
                 (qi_document [App (TR.real_numeral 3 1) []] (pi_at three)) == RD.RootPending 1)

(* D8 a datatype-mentioning array sort hidden in an uninterpreted
   function's domain: the Sorted proof is fine (Some 0), the gate reports
   Uncovered; the minimal pair with Array Int Int is Certified. *)
let q_on (s:sort) : func_decl = unary "q" s bool_sort
let hidden (s:sort) : expr = App (q_on s) [const "c" s]

let d8_sorted_accepts () : Lemma (SP.check_document PT.schema (refute_pair (hidden (ArraySort [integer] PT.box))) == Some 0) =
  assert_norm (SP.check_document PT.schema (refute_pair (hidden (ArraySort [integer] PT.box))) == Some 0)

let d8_uncovered () : Lemma (RD.check_root_document PT.schema (refute_pair (hidden (ArraySort [integer] PT.box))) ==
                             RD.RootUncovered) =
  assert_norm (RD.check_root_document PT.schema (refute_pair (hidden (ArraySort [integer] PT.box))) == RD.RootUncovered)

let d8_pair_certified () : Lemma (RD.check_root_document PT.schema (refute_pair (hidden (ArraySort [integer] integer))) ==
                                  RD.RootCertified) =
  assert_norm (RD.check_root_document PT.schema (refute_pair (hidden (ArraySort [integer] integer))) == RD.RootCertified)

(* D9 a zero-index array sort in a quantifier binder. *)
let zero_index : sort = ArraySort [] integer
let all_r : expr = Quantifier Forall_k [zero_index] bool_sort (App (q_on zero_index) [Var 0 zero_index])

let d9_uncovered () : Lemma (RD.check_root_document PT.core_schema (refute_pair all_r) == RD.RootUncovered) =
  assert_norm (RD.check_root_document PT.core_schema (refute_pair all_r) == RD.RootUncovered)

(* D10 an unsupported term that occurs ONLY in an instantiation argument
   (the body ignores its variable): Uncovered; with a covered argument the
   same document is Certified. *)
let p0 : expr = const "p0" bool_sort
let vacuous : expr = Quantifier Forall_k [integer] bool_sort p0
let k_on (s:sort) : func_decl = unary "k" s integer

let vacuous_document (arg:expr) : P.document =
  doc [vacuous; R.mk_not_expr p0]
      [entry (U.QuantifierInstantiation [arg]) (disjunction [R.mk_not_expr vacuous; p0]) [];
       entry U.Asserted vacuous [];
       entry U.Asserted (R.mk_not_expr p0) [];
       entry U.UnitResolution R.false_expr [0; 1; 2]]
      3

let hidden_arg : expr = App (k_on (ArraySort [integer] PT.box)) [const "c" (ArraySort [integer] PT.box)]

(* Split per document (the combined lemma took 5.6 s). *)
let d10_sorted_accepts () : Lemma (SP.check_document PT.schema (vacuous_document hidden_arg) == Some 0) =
  assert_norm (SP.check_document PT.schema (vacuous_document hidden_arg) == Some 0)

let d10_uncovered () : Lemma (RD.check_root_document PT.schema (vacuous_document hidden_arg) == RD.RootUncovered) =
  assert_norm (RD.check_root_document PT.schema (vacuous_document hidden_arg) == RD.RootUncovered)

let d10_pair_certified () : Lemma (RD.check_root_document PT.schema (vacuous_document three) == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.schema (vacuous_document three) == RD.RootCertified)

(* ---------------------------------------------------------------------- *)
(* E. Counter-models of the false inputs (positively proved)               *)
(* ---------------------------------------------------------------------- *)

let p_decl : func_decl = { decl_name = "p"; domain = []; range = bool_sort; interp = None; int_params = [] }

let uf_bool (u:TR.uninterpreted) (b:bool) : TR.symbols u PT.core_schema = {
  TR.apply = (fun f _ ->
    if f.range = bool_sort then TR.boolean #u PT.core_schema b
    else S.value_inhabitant PT.core_schema (TR.default_value u) f.range);
  TR.lambda = (fun bound t _ -> S.value_inhabitant PT.core_schema (TR.default_value u) (ArraySort bound t));
}

(* The original assertions of D1 and D2 ([p]) hold in the standard root
   model that interprets p as true (for every u): neither may be certified. *)
let d1_d2_satisfiable (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (TR.standard u PT.core_schema (uf_bool u true)) /\
           d1_document.P.assertions == [PT.proposition] /\ d2_document.P.assertions == [PT.proposition] /\
           RD.root_truths u PT.core_schema (TR.standard u PT.core_schema (uf_bool u true)) [PT.proposition] == true) =
  TR.lemma_standard_root u PT.core_schema (uf_bool u true);
  assert_norm (PT.proposition == App p_decl []);
  assert_norm (TR.classify (S.signature PT.core_schema) p_decl == TR.Other);
  TR.lemma_eval_free_choice u PT.core_schema (uf_bool u true) [] (RD.empty_root u PT.core_schema) p_decl []

(* ---------------------------------------------------------------------- *)
(* F. Data the checker does not read cannot change a verdict               *)
(* ---------------------------------------------------------------------- *)

(* For ANY schema and document: replacing the native declarations and
   expressions tables, or any rule payload outside the five read shapes,
   leaves the gate's verdict unchanged (RD.lemma_root_read_view). *)
let same_reads (schema:S.schema) (d1 d2:P.document)
  : Lemma (requires d1.P.assertions == d2.P.assertions /\ d1.P.root == d2.P.root /\
                    L.map RD.shape_entry d1.P.entries == L.map RD.shape_entry d2.P.entries)
          (ensures RD.check_root_document schema d1 == RD.check_root_document schema d2) =
  RD.lemma_root_read_view schema d1;
  RD.lemma_root_read_view schema d2

let tables_never_read (schema:S.schema) (d:P.document) (ds:list func_decl) (es:list expr)
  : Lemma (RD.check_root_document schema ({ d with P.declarations = ds; P.expressions = es }) ==
           RD.check_root_document schema d) =
  same_reads schema d ({ d with P.declarations = ds; P.expressions = es })

(* Concrete instances: an UNSUPPORTED term (an array over the datatype Box)
   listed only in the expressions table, and an (empty, hence not
   replayable) Farkas certificate on a step the consequence kernel checks
   by itself, leave the certified verdicts unchanged. *)
let f1_hidden_table_term () : Lemma (RD.check_root_document PT.schema
                                       ({ b6_document with P.expressions = [hidden_arg] }) == RD.RootCertified) =
  b6_certified ();
  tables_never_read PT.schema b6_document [] [hidden_arg]

let f2_payload_rule () : Lemma (RD.check_root_document PT.core_schema
                                  (doc [R.mk_not_expr commuted]
                                       [entry (U.ArithmeticFarkas []) commuted [];
                                        entry U.Asserted (R.mk_not_expr commuted) [];
                                        entry U.UnitResolution R.false_expr [0; 1]] 2) == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema
                 (doc [R.mk_not_expr commuted]
                      [entry (U.ArithmeticFarkas []) commuted [];
                       entry U.Asserted (R.mk_not_expr commuted) [];
                       entry U.UnitResolution R.false_expr [0; 1]] 2) == RD.RootCertified)

(* ---------------------------------------------------------------------- *)
(* G. Typed Int Farkas: the coefficients are READ (kept by the read view)   *)
(* ---------------------------------------------------------------------- *)

(* x > 0 and x < 1 over Int: refuted only with the strict-bound rounding of
   the integer Farkas replay, by the certificate (1, 1). *)
let zero : expr = App (TR.int_numeral 0) []
let x_positive : expr = App (TR.gt_decl integer) [x_int; zero]
let x_below_one : expr = App (TR.lt_decl integer) [x_int; one]

let farkas_document (cs:list Z3LinearArithmeticAst.coefficient) : P.document =
  doc [x_positive; x_below_one]
      [entry U.Asserted x_positive []; entry U.Asserted x_below_one [];
       entry (U.ArithmeticFarkas cs) R.false_expr [0; 1]]
      2

let g1_farkas_certified () : Lemma (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (1, 1)]) ==
                                    RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (1, 1)]) == RD.RootCertified)

(* Mutant certificates on the same step: a zero weight, a missing and an
   extra coefficient. Each leaves the step as an open obligation (one
   document per lemma). *)
let g2_zero_weight_pending () : Lemma (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (0, 1)]) ==
                                       RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (0, 1)]) == RD.RootPending 1)

let g2_missing_coefficient_pending () : Lemma (RD.check_root_document PT.core_schema (farkas_document [(1, 1)]) ==
                                               RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_document [(1, 1)]) == RD.RootPending 1)

let g2_extra_coefficient_pending ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (1, 1); (1, 1)]) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (1, 1); (1, 1)]) == RD.RootPending 1)

(* The read view keeps the coefficient list: the certified and the mutant
   documents keep different read views, and each keeps its verdict there. *)
let g3_farkas_read_view ()
  : Lemma (RD.read_view (farkas_document [(1, 1); (1, 1)]) =!= RD.read_view (farkas_document [(1, 1); (0, 1)]) /\
           RD.check_root_document PT.core_schema (RD.read_view (farkas_document [(1, 1); (1, 1)])) ==
             RD.RootCertified /\
           RD.check_root_document PT.core_schema (RD.read_view (farkas_document [(1, 1); (0, 1)])) ==
             RD.RootPending 1) =
  assert_norm (L.map RD.shape_entry (farkas_document [(1, 1); (1, 1)]).P.entries =!=
               L.map RD.shape_entry (farkas_document [(1, 1); (0, 1)]).P.entries);
  g1_farkas_certified (); g2_zero_weight_pending ();
  RD.lemma_root_read_view PT.core_schema (farkas_document [(1, 1); (1, 1)]);
  RD.lemma_root_read_view PT.core_schema (farkas_document [(1, 1); (0, 1)])

(* The certified Farkas document is false in EVERY root model. *)
let g4_farkas_false (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema (farkas_document [(1, 1); (1, 1)]) i) =
  g1_farkas_certified ();
  RD.lemma_root_certified u PT.core_schema (farkas_document [(1, 1); (1, 1)]) i

(* ---------------------------------------------------------------------- *)
(* H. The Hilbert-epsilon route and its root gate                           *)
(* ---------------------------------------------------------------------- *)

(* exists y:Int. pi(y) is Skolemized to pi(sk) (an observational step with no
   premises); pi(sk) and forall y. not pi(y) then refute by instantiation. *)
let sk : expr = const "sk" integer
let some_pi : expr = Quantifier Exists_k [integer] bool_sort (App pi_decl [Var 0 integer])
let no_pi : expr = Quantifier Forall_k [integer] bool_sort (R.mk_not_expr (App pi_decl [Var 0 integer]))

let epsilon_document (assertions:list expr) (witness:expr) : P.document =
  doc assertions
      [entry U.Skolemization (Z3ObservationalEquality.mk_oeq_expr some_pi (pi_at witness)) [];
       entry U.Asserted some_pi [];
       entry U.ModusPonens (pi_at witness) [1; 0];
       entry (U.QuantifierInstantiation [witness])
             (disjunction [R.mk_not_expr no_pi; R.mk_not_expr (pi_at witness)]) [];
       entry U.Asserted no_pi [];
       entry U.UnitResolution R.false_expr [3; 4; 2]]
      5

let h_document : P.document = epsilon_document [some_pi; no_pi] sk

(* The plain route leaves exactly the Skolem step open; the epsilon route
   certifies it, and its root gate reports RootCertified (one normalized
   run of each route; the gate verdicts follow from them and coverage). *)
let h1_plain_pending () : Lemma (SP.check_document PT.core_schema h_document == Some 1) =
  assert_norm (SP.check_document PT.core_schema h_document == Some 1)

let h1_epsilon_accepts () : Lemma (SP.check_document_epsilon PT.core_schema h_document == Some 0) =
  assert_norm (SP.check_document_epsilon PT.core_schema h_document == Some 0)

let h1_covered () : Lemma (RD.root_covered PT.core_schema h_document) =
  assert_norm (RD.root_covered PT.core_schema h_document)

let h1_epsilon_certified ()
  : Lemma (SP.check_document PT.core_schema h_document == Some 1 /\
           SP.check_document_epsilon PT.core_schema h_document == Some 0 /\
           RD.check_root_document PT.core_schema h_document == RD.RootPending 1 /\
           RD.check_root_document_epsilon PT.core_schema h_document == RD.RootCertified) =
  h1_plain_pending (); h1_epsilon_accepts (); h1_covered ()

(* The certified epsilon document is false in EVERY root model, and in the
   standard root model for EVERY u and uf; the choice extension of any root
   model by its definitions is again a root model, keeps the original
   assertions' truth and satisfies the generated choice equation. *)
let h2_epsilon_false (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema h_document i /\
                   TR.root_model u PT.core_schema (RD.epsilon_extension u PT.core_schema i h_document) /\
                   RD.root_truths u PT.core_schema (RD.epsilon_extension u PT.core_schema i h_document)
                     h_document.P.assertions == RD.root_truths u PT.core_schema i h_document.P.assertions) =
  h1_epsilon_certified ();
  RD.lemma_root_certified_epsilon u PT.core_schema h_document i;
  RD.lemma_root_epsilon_extension u PT.core_schema i h_document

let h3_epsilon_standard (u:TR.uninterpreted) (uf:TR.symbols u PT.core_schema)
  : Lemma (TR.root_model u PT.core_schema (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema h_document (TR.standard u PT.core_schema uf)) =
  TR.lemma_standard_root u PT.core_schema uf;
  h2_epsilon_false u (TR.standard u PT.core_schema uf)

(* Negative controls. A witness that already occurs in an original
   assertion is not fresh: no choice equation is used and the Skolem step
   stays open. *)
let h4_reused_witness_pending ()
  : Lemma (RD.check_root_document_epsilon PT.core_schema
             (epsilon_document [some_pi; no_pi; R.mk_eq_expr sk sk] sk) == RD.RootPending 1) =
  assert_norm (RD.check_root_document_epsilon PT.core_schema
                 (epsilon_document [some_pi; no_pi; R.mk_eq_expr sk sk] sk) == RD.RootPending 1)

(* A wrong-polarity target, exists y. pi(y) ~ not pi(sk), on the satisfiable
   inputs (exists y. pi(y)) and (forall y. pi(y)) (every pi true): the step
   is no Skolem definition, so the would-be refutation stays open. *)
let h5_document : P.document =
  doc [some_pi; all_pi]
      [entry U.Skolemization (Z3ObservationalEquality.mk_oeq_expr some_pi (R.mk_not_expr (pi_at sk))) [];
       entry U.Asserted some_pi [];
       entry U.ModusPonens (R.mk_not_expr (pi_at sk)) [1; 0];
       entry (U.QuantifierInstantiation [sk]) (qi_clause (pi_at sk)) [];
       entry U.Asserted all_pi [];
       entry U.UnitResolution R.false_expr [3; 4; 2]]
      5

let h5_wrong_polarity_unused () : Lemma (SP.epsilon_context PT.core_schema h5_document == []) =
  assert_norm (SP.epsilon_context PT.core_schema h5_document == [])

let h5_wrong_polarity_pending ()
  : Lemma (RD.check_root_document_epsilon PT.core_schema h5_document == RD.RootPending 1) =
  assert_norm (RD.check_root_document_epsilon PT.core_schema h5_document == RD.RootPending 1)

(* The epsilon gate reads only the read view (Skolemization kept): the native
   tables never change its verdict. *)
let h6_epsilon_tables_never_read (ds:list func_decl) (es:list expr)
  : Lemma (RD.check_root_document_epsilon PT.core_schema
             ({ h_document with P.declarations = ds; P.expressions = es }) == RD.RootCertified) =
  h1_epsilon_certified ();
  RD.lemma_root_read_view_epsilon PT.core_schema h_document;
  RD.lemma_root_read_view_epsilon PT.core_schema ({ h_document with P.declarations = ds; P.expressions = es })

(* A later definition whose source mentions the witness of an earlier one
   (exists y. q2(sk, y) ~ q2(sk, sk2)) is ordered after it: both
   definitions are used, in either entry order. *)
let q2_decl : func_decl =
  { decl_name = "q2"; domain = [integer; integer]; range = bool_sort; interp = None; int_params = [] }
let sk2 : expr = const "sk2" integer
let skolem_pi : P.entry = entry U.Skolemization (Z3ObservationalEquality.mk_oeq_expr some_pi (pi_at sk)) []
let skolem_q : P.entry =
  entry U.Skolemization
    (Z3ObservationalEquality.mk_oeq_expr
       (Quantifier Exists_k [integer] bool_sort (App q2_decl [sk; Var 0 integer])) (App q2_decl [sk; sk2])) []

let h7_later_reference_forward ()
  : Lemma (L.length (SP.epsilon_context PT.core_schema (doc [some_pi] [skolem_pi; skolem_q] 0)) == 2) =
  assert_norm (L.length (SP.epsilon_context PT.core_schema (doc [some_pi] [skolem_pi; skolem_q] 0)) == 2)

let h7_later_reference_backward ()
  : Lemma (L.length (SP.epsilon_context PT.core_schema (doc [some_pi] [skolem_q; skolem_pi] 0)) == 2) =
  assert_norm (L.length (SP.epsilon_context PT.core_schema (doc [some_pi] [skolem_q; skolem_pi] 0)) == 2)
