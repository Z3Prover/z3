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
module Tac = FStar.Tactics.V2

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

let integer_product_document (strict:bool) (wrong_sign:bool) : P.document =
  let x = const "product_x" integer in
  let y = const "product_y" integer in
  let z = const "product_z" integer in
  let minimum = if strict then SP.int_one else SP.int_zero in
  let a = SP.int_ge x minimum in
  let b = if wrong_sign then SP.int_le y SP.int_zero else SP.int_ge y minimum in
  let c = if strict then SP.int_le z SP.int_zero else App (TR.lt_decl integer) [z; SP.int_zero] in
  let product = App (TR.times_decl integer) [x; y] in
  let negative = App (TR.times_decl integer) [App (TR.int_numeral (-1)) []; z] in
  let bound = SP.int_le (App (TR.plus_decl integer) [product; negative]) SP.int_zero in
  doc [a; b; c; bound]
    [entry U.Asserted a []; entry U.Asserted b []; entry U.Asserted c [];
     entry U.Asserted bound []; entry (U.Unverified "th-lemma") R.false_expr [0; 1; 2; 3]] 4

let nonnegative_integer_products ()
  : Lemma (SP.check_document_epsilon PT.core_schema (integer_product_document false false) == Some 0 /\
           RD.check_root_document_epsilon PT.core_schema (integer_product_document false false) == RD.RootCertified /\
           SP.check_document_epsilon PT.core_schema (RD.read_view (integer_product_document false false)) == Some 0 /\
           SP.check_document_epsilon PT.core_schema (integer_product_document false true) == Some 1) =
  assert_norm (SP.check_document_epsilon PT.core_schema (integer_product_document false false) == Some 0);
  assert_norm (RD.check_root_document_epsilon PT.core_schema (integer_product_document false false) == RD.RootCertified);
  assert_norm (SP.check_document_epsilon PT.core_schema (RD.read_view (integer_product_document false false)) == Some 0);
  assert_norm (SP.check_document_epsilon PT.core_schema (integer_product_document false true) == Some 1)

let positive_integer_products ()
  : Lemma (SP.check_document_epsilon PT.core_schema (integer_product_document true false) == Some 0 /\
           RD.check_root_document_epsilon PT.core_schema (integer_product_document true false) == RD.RootCertified /\
           SP.check_document_epsilon PT.core_schema (RD.read_view (integer_product_document true false)) == Some 0 /\
           SP.check_document_epsilon PT.core_schema (integer_product_document true true) == Some 1) =
  assert_norm (SP.check_document_epsilon PT.core_schema (integer_product_document true false) == Some 0);
  assert_norm (RD.check_root_document_epsilon PT.core_schema (integer_product_document true false) == RD.RootCertified);
  assert_norm (SP.check_document_epsilon PT.core_schema (RD.read_view (integer_product_document true false)) == Some 0);
  assert_norm (SP.check_document_epsilon PT.core_schema (integer_product_document true true) == Some 1)

let integer_signed_product_document (strict:bool) (opposite:bool) (wrong_sign:bool) : P.document =
  let x = const "sign_x" integer in
  let y = const "sign_y" integer in
  let z = const "sign_z" integer in
  let positive = if strict then SP.int_one else SP.int_zero in
  let negative = if strict then SP.int_minus_one else SP.int_zero in
  let a = SP.int_le x negative in
  let b = if opposite <> wrong_sign then SP.int_ge y positive else SP.int_le y negative in
  let c = if strict then (if opposite then SP.int_ge z SP.int_zero else SP.int_le z SP.int_zero)
    else App (if opposite then TR.gt_decl integer else TR.lt_decl integer) [z; SP.int_zero] in
  let product = App (TR.times_decl integer) [x; y] in
  let negative = App (TR.times_decl integer) [App (TR.int_numeral (-1)) []; z] in
  let difference = App (TR.plus_decl integer) [product; negative] in
  let bound = if opposite then SP.int_ge difference SP.int_zero else SP.int_le difference SP.int_zero in
  doc [a; b; c; bound]
    [entry U.Asserted a []; entry U.Asserted b []; entry U.Asserted c [];
     entry U.Asserted bound []; entry (U.Unverified "th-lemma") R.false_expr [0; 1; 2; 3]] 4

let nonpositive_integer_products ()
  : Lemma (SP.check_document_epsilon PT.core_schema (integer_signed_product_document false true false) == Some 0 /\
           RD.check_root_document_epsilon PT.core_schema (integer_signed_product_document false true false) == RD.RootCertified /\
           SP.check_document_epsilon PT.core_schema (RD.read_view (integer_signed_product_document false true false)) == Some 0 /\
           SP.check_document_epsilon PT.core_schema (integer_signed_product_document false true true) == Some 1) =
  assert_norm (SP.check_document_epsilon PT.core_schema (integer_signed_product_document false true false) == Some 0);
  assert_norm (RD.check_root_document_epsilon PT.core_schema (integer_signed_product_document false true false) == RD.RootCertified);
  assert_norm (SP.check_document_epsilon PT.core_schema (RD.read_view (integer_signed_product_document false true false)) == Some 0);
  assert_norm (SP.check_document_epsilon PT.core_schema (integer_signed_product_document false true true) == Some 1)

let both_nonpositive_integer_products ()
  : Lemma (SP.check_document_epsilon PT.core_schema (integer_signed_product_document false false false) == Some 0 /\
           RD.check_root_document_epsilon PT.core_schema (integer_signed_product_document false false false) == RD.RootCertified /\
           SP.check_document_epsilon PT.core_schema (RD.read_view (integer_signed_product_document false false false)) == Some 0 /\
           SP.check_document_epsilon PT.core_schema (integer_signed_product_document false false true) == Some 1) =
  assert_norm (SP.check_document_epsilon PT.core_schema (integer_signed_product_document false false false) == Some 0);
  assert_norm (RD.check_root_document_epsilon PT.core_schema (integer_signed_product_document false false false) == RD.RootCertified);
  assert_norm (SP.check_document_epsilon PT.core_schema (RD.read_view (integer_signed_product_document false false false)) == Some 0);
  assert_norm (SP.check_document_epsilon PT.core_schema (integer_signed_product_document false false true) == Some 1)

let negative_integer_products ()
  : Lemma (SP.check_document_epsilon PT.core_schema (integer_signed_product_document true true false) == Some 0 /\
           RD.check_root_document_epsilon PT.core_schema (integer_signed_product_document true true false) == RD.RootCertified /\
           SP.check_document_epsilon PT.core_schema (RD.read_view (integer_signed_product_document true true false)) == Some 0 /\
           SP.check_document_epsilon PT.core_schema (integer_signed_product_document true true true) == Some 1) =
  assert_norm (SP.check_document_epsilon PT.core_schema (integer_signed_product_document true true false) == Some 0);
  assert_norm (RD.check_root_document_epsilon PT.core_schema (integer_signed_product_document true true false) == RD.RootCertified);
  assert_norm (SP.check_document_epsilon PT.core_schema (RD.read_view (integer_signed_product_document true true false)) == Some 0);
  assert_norm (SP.check_document_epsilon PT.core_schema (integer_signed_product_document true true true) == Some 1)

let both_negative_integer_products ()
  : Lemma (SP.check_document_epsilon PT.core_schema (integer_signed_product_document true false false) == Some 0 /\
           RD.check_root_document_epsilon PT.core_schema (integer_signed_product_document true false false) == RD.RootCertified /\
           SP.check_document_epsilon PT.core_schema (RD.read_view (integer_signed_product_document true false false)) == Some 0 /\
           SP.check_document_epsilon PT.core_schema (integer_signed_product_document true false true) == Some 1) =
  assert_norm (SP.check_document_epsilon PT.core_schema (integer_signed_product_document true false false) == Some 0);
  assert_norm (RD.check_root_document_epsilon PT.core_schema (integer_signed_product_document true false false) == RD.RootCertified);
  assert_norm (SP.check_document_epsilon PT.core_schema (RD.read_view (integer_signed_product_document true false false)) == Some 0);
  assert_norm (SP.check_document_epsilon PT.core_schema (integer_signed_product_document true false true) == Some 1)

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

(* x > 0 and x < 1 over Int, with an unrelated Boolean fact p among the
   step's premises: refuted only with the strict-bound rounding of the
   integer Farkas replay, by the certificate (1, 1, 0) (p weighted 0). The
   checker's own recomputation of coefficients (SP.linear_consequence,
   section M) reads steps over Int comparisons only, so on this step the
   producer's coefficients decide; G5 is the same step without p. *)
let zero : expr = App (TR.int_numeral 0) []
let x_positive : expr = App (TR.gt_decl integer) [x_int; zero]
let x_below_one : expr = App (TR.lt_decl integer) [x_int; one]

let farkas_document (cs:list Z3LinearArithmeticAst.coefficient) : P.document =
  doc [x_positive; x_below_one; PT.proposition]
      [entry U.Asserted x_positive []; entry U.Asserted x_below_one []; entry U.Asserted PT.proposition [];
       entry (U.ArithmeticFarkas cs) R.false_expr [0; 1; 2]]
      3

let g1_farkas_certified ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (1, 1); (0, 1)]) == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (1, 1); (0, 1)]) == RD.RootCertified)

(* Mutant certificates on the same step: a zero weight, a missing and an
   extra coefficient. Each leaves the step as an open obligation (one
   document per lemma). *)
let g2_zero_weight_pending ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (0, 1); (0, 1)]) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (0, 1); (0, 1)]) == RD.RootPending 1)

let g2_missing_coefficient_pending ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (1, 1)]) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (1, 1)]) == RD.RootPending 1)

let g2_extra_coefficient_pending ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (1, 1); (0, 1); (1, 1)]) ==
           RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_document [(1, 1); (1, 1); (0, 1); (1, 1)]) ==
               RD.RootPending 1)

(* The read view keeps the coefficient list: the certified and the mutant
   documents keep different read views, and each keeps its verdict there. *)
let g3_farkas_read_view ()
  : Lemma (RD.read_view (farkas_document [(1, 1); (1, 1); (0, 1)]) =!=
             RD.read_view (farkas_document [(1, 1); (0, 1); (0, 1)]) /\
           RD.check_root_document PT.core_schema (RD.read_view (farkas_document [(1, 1); (1, 1); (0, 1)])) ==
             RD.RootCertified /\
           RD.check_root_document PT.core_schema (RD.read_view (farkas_document [(1, 1); (0, 1); (0, 1)])) ==
             RD.RootPending 1) =
  assert_norm (L.map RD.shape_entry (farkas_document [(1, 1); (1, 1); (0, 1)]).P.entries =!=
               L.map RD.shape_entry (farkas_document [(1, 1); (0, 1); (0, 1)]).P.entries);
  g1_farkas_certified (); g2_zero_weight_pending ();
  RD.lemma_root_read_view PT.core_schema (farkas_document [(1, 1); (1, 1); (0, 1)]);
  RD.lemma_root_read_view PT.core_schema (farkas_document [(1, 1); (0, 1); (0, 1)])

(* The certified Farkas document is false in EVERY root model. *)
let g4_farkas_false (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema (farkas_document [(1, 1); (1, 1); (0, 1)]) i) =
  g1_farkas_certified ();
  RD.lemma_root_certified u PT.core_schema (farkas_document [(1, 1); (1, 1); (0, 1)]) i

(* G5. The same step over the Int comparisons alone, with the zero-weight
   mutant certificate. The supplied coefficients stay invalid (G6: the
   coefficient validator refuses them); the step is rescued by a DIFFERENT
   certificate, the weights the checker recomputes from the formulas
   (SP.linear_consequence), which the same typed validator accepts. The
   document is certified and false in EVERY root model. *)
let farkas_pair_document (cs:list Z3LinearArithmeticAst.coefficient) : P.document =
  doc [x_positive; x_below_one]
      [entry U.Asserted x_positive []; entry U.Asserted x_below_one [];
       entry (U.ArithmeticFarkas cs) R.false_expr [0; 1]]
      2

let g5_recomputed_certified ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_pair_document [(1, 1); (0, 1)]) == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_pair_document [(1, 1); (0, 1)]) == RD.RootCertified)

let g5_recomputed_false (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema (farkas_pair_document [(1, 1); (0, 1)]) i) =
  g5_recomputed_certified ();
  RD.lemma_root_certified u PT.core_schema (farkas_pair_document [(1, 1); (0, 1)]) i

(* G6. Direct coefficient-validator discrimination on the ORIGINAL
   two-premise step: SP.arithmetic_farkas (AR.check_contradiction on the
   supplied weights) accepts (1, 1) and refuses the zero-weight, missing
   and extra coefficient mutants; the recomputed weights for the same
   literals are a validated certificate (the one G5 uses). *)
let pair_fact (e:expr) : U.checked_fact = { U.conclusion = U.Holds e; hypotheses = [] }

let pair_node (cs:list Z3LinearArithmeticAst.coefficient) : U.proof_node = {
  U.kind = U.ArithmeticFarkas cs; conclusion = U.Holds R.false_expr;
  premises = [pair_fact x_positive; pair_fact x_below_one];
}

let g6_validator_discriminates ()
  : Lemma (SP.arithmetic_farkas (pair_node [(1, 1); (1, 1)]) /\
           not (SP.arithmetic_farkas (pair_node [(1, 1); (0, 1)])) /\
           not (SP.arithmetic_farkas (pair_node [(1, 1)])) /\
           not (SP.arithmetic_farkas (pair_node [(1, 1); (1, 1); (1, 1)])) /\
           (match Z3LinearArithmeticAst.synthesize R.false_expr [x_positive; x_below_one] with
            | Some cs -> Z3SortedArithmetic.check_contradiction
                           (Z3LinearArithmeticAst.assumptions R.false_expr [x_positive; x_below_one]) cs
            | None -> False)) =
  assert_norm (SP.arithmetic_farkas (pair_node [(1, 1); (1, 1)]));
  assert_norm (not (SP.arithmetic_farkas (pair_node [(1, 1); (0, 1)])));
  assert_norm (not (SP.arithmetic_farkas (pair_node [(1, 1)])));
  assert_norm (not (SP.arithmetic_farkas (pair_node [(1, 1); (1, 1); (1, 1)])));
  assert_norm (match Z3LinearArithmeticAst.synthesize R.false_expr [x_positive; x_below_one] with
               | Some cs -> Z3SortedArithmetic.check_contradiction
                              (Z3LinearArithmeticAst.assumptions R.false_expr [x_positive; x_below_one]) cs
               | None -> False)

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

let h1_covered ()
  : Lemma (RD.root_covered PT.core_schema h_document /\ RD.dependent_closures PT.core_schema h_document == []) =
  assert_norm (RD.root_covered PT.core_schema h_document);
  assert_norm (RD.dependent_closures PT.core_schema h_document == [])

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

(* ---------------------------------------------------------------------- *)
(* I. Int equality/order laws: triangle clauses and implied equalities      *)
(* ---------------------------------------------------------------------- *)

(* The checks read the formulas only (never the rule label), over the
   fixtures of Z3SortedProofTests: opaque Int-valued applications ulevel(a),
   ulevel(b), the sum ulevel(a) + (-1) * ulevel(b) of Raise q5 and the
   nonconstant product ulevel(a) * ulevel(b), each read as one Int value. *)
let th_lemma : U.rule = U.Unverified "th-lemma"

(* A clause step refuted by the complements of its literals. *)
let refute2 (clause u1 u2:expr) : P.document =
  doc [u1; u2]
      [entry th_lemma clause []; entry U.Asserted u1 []; entry U.Asserted u2 [];
       entry U.UnitResolution R.false_expr [0; 1; 2]]
      3

let refute3 (clause u1 u2 u3:expr) : P.document =
  doc [u1; u2; u3]
      [entry th_lemma clause []; entry U.Asserted u1 []; entry U.Asserted u2 []; entry U.Asserted u3 [];
       entry U.UnitResolution R.false_expr [0; 1; 2; 3]]
      4

let i1_document : P.document =
  refute2 PT.raise_le (R.mk_eq_expr PT.ione PT.span) (R.mk_not_expr (PT.leq PT.span PT.ione))

let i2_document : P.document =
  refute2 PT.gap_le_reversed (R.mk_not_expr (PT.leq PT.gap PT.izero)) (R.mk_eq_expr PT.la PT.product)

let i3_document : P.document =
  refute3 PT.antisymmetry (PT.not_eq PT.product PT.la) (PT.leq PT.gap PT.izero) (PT.geq PT.gap PT.izero)

(* x = y from the two opposite bounds on x + (-1) * y, the premise ids given. *)
let implied_document (premises:list int) : P.document =
  doc [PT.geq PT.gap PT.izero; PT.leq PT.gap PT.izero; PT.not_eq PT.product PT.la]
      [entry U.Asserted (PT.geq PT.gap PT.izero) []; entry U.Asserted (PT.leq PT.gap PT.izero) [];
       entry th_lemma (R.mk_eq_expr PT.product PT.la) premises;
       entry U.Asserted (PT.not_eq PT.product PT.la) [];
       entry U.UnitResolution R.false_expr [2; 3]]
      4

let i4_document : P.document = implied_document [0; 1]

let i1_certified () : Lemma (RD.check_root_document PT.core_schema i1_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema i1_document == RD.RootCertified)

let i2_certified () : Lemma (RD.check_root_document PT.core_schema i2_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema i2_document == RD.RootCertified)

let i3_certified () : Lemma (RD.check_root_document PT.core_schema i3_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema i3_document == RD.RootCertified)

let i4_certified () : Lemma (RD.check_root_document PT.core_schema i4_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema i4_document == RD.RootCertified)

(* The certified documents are false in EVERY root model, and in the
   standard root model for every u and uf. *)
let int_order_documents_false (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema i1_document i /\ falsified u PT.core_schema i2_document i /\
                   falsified u PT.core_schema i3_document i /\ falsified u PT.core_schema i4_document i) =
  i1_certified (); RD.lemma_root_certified u PT.core_schema i1_document i;
  i2_certified (); RD.lemma_root_certified u PT.core_schema i2_document i;
  i3_certified (); RD.lemma_root_certified u PT.core_schema i3_document i;
  i4_certified (); RD.lemma_root_certified u PT.core_schema i4_document i

let int_order_documents_standard (u:TR.uninterpreted) (uf:TR.symbols u PT.core_schema)
  : Lemma (TR.root_model u PT.core_schema (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema i1_document (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema i2_document (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema i3_document (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema i4_document (TR.standard u PT.core_schema uf)) =
  TR.lemma_standard_root u PT.core_schema uf;
  int_order_documents_false u (TR.standard u PT.core_schema uf)

(* False variants on the same refutation shapes stay open obligations (their
   counter-models: Z3SortedProofTests.int_order_counter_models): a strict
   bound at x = y, a counterfeit `<=` without its interpretation tag, and an
   implied equality with one of its two bounds missing. *)
let i5_strict_pending ()
  : Lemma (RD.check_root_document PT.core_schema
             (refute2 PT.strict_mutant (R.mk_eq_expr PT.xi PT.yi)
                (R.mk_not_expr (App PT.ilt [PT.xi; PT.yi]))) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema
                 (refute2 PT.strict_mutant (R.mk_eq_expr PT.xi PT.yi)
                    (R.mk_not_expr (App PT.ilt [PT.xi; PT.yi]))) == RD.RootPending 1)

let i6_counterfeit_pending ()
  : Lemma (RD.check_root_document PT.core_schema
             (refute2 PT.counterfeit_le_mutant (R.mk_eq_expr PT.xi PT.yi)
                (R.mk_not_expr (App ({ PT.ile with interp = None }) [PT.xi; PT.yi]))) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema
                 (refute2 PT.counterfeit_le_mutant (R.mk_eq_expr PT.xi PT.yi)
                    (R.mk_not_expr (App ({ PT.ile with interp = None }) [PT.xi; PT.yi]))) == RD.RootPending 1)

let i7_missing_bound_pending ()
  : Lemma (RD.check_root_document PT.core_schema (implied_document [0]) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (implied_document [0]) == RD.RootPending 1)

let integer_unit_document (bound:int) (premises:list int) : P.document =
  let term = App (TR.times_decl integer) [one; x_int] in
  let strict = App (TR.lt_decl integer) [term; zero] in
  let tightened = SP.int_le term (App (TR.int_numeral bound) []) in
  let negative = R.mk_not_expr tightened in
  doc [R.true_expr; strict; negative]
    [entry U.Asserted R.true_expr []; entry U.Asserted strict [];
     entry (U.Unverified "arith/lp-integer-tighten") tightened premises;
     entry U.Asserted negative []; entry U.UnitResolution R.false_expr [2; 3]] 4

let integer_unit_certified ()
  : Lemma (SP.check_document_epsilon PT.core_schema (integer_unit_document (-1) [0; 1]) == Some 0 /\
           RD.check_root_document PT.core_schema (integer_unit_document (-1) [0; 1]) == RD.RootCertified /\
           RD.check_root_document PT.core_schema (RD.read_view (integer_unit_document (-1) [0; 1])) == RD.RootCertified) =
  assert_norm (SP.check_document_epsilon PT.core_schema (integer_unit_document (-1) [0; 1]) == Some 0);
  assert_norm (RD.check_root_document PT.core_schema (integer_unit_document (-1) [0; 1]) == RD.RootCertified);
  assert_norm (RD.check_root_document PT.core_schema (RD.read_view (integer_unit_document (-1) [0; 1])) == RD.RootCertified)

let integer_unit_mutants ()
  : Lemma (RD.check_root_document PT.core_schema (integer_unit_document (-1) [0]) == RD.RootPending 1 /\
           RD.check_root_document PT.core_schema (integer_unit_document (-2) [0; 1]) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (integer_unit_document (-1) [0]) == RD.RootPending 1);
  assert_norm (RD.check_root_document PT.core_schema (integer_unit_document (-2) [0; 1]) == RD.RootPending 1)

(* ---------------------------------------------------------------------- *)
(* J. Term if-then-else branch clauses (same-model theorem, no new symbol)  *)
(* ---------------------------------------------------------------------- *)

let def_axiom_refute (clause u1 u2:expr) : P.document =
  doc [u1; u2]
      [entry U.DefAxiom clause []; entry U.Asserted u1 []; entry U.Asserted u2 [];
       entry U.UnitResolution R.false_expr [0; 1; 2]]
      3

(* Raise q5 nodes 68 and 116 over Universe, and an Int choice with reversed
   equality operands and swapped literals. *)
let j1_document : P.document =
  def_axiom_refute PT.ite_then PT.raise_guard
    (PT.not_eq PT.ub (PT.universe_choice PT.raise_guard PT.ub PT.ua))

let j2_document : P.document =
  def_axiom_refute PT.ite_else (R.mk_not_expr PT.raise_guard)
    (PT.not_eq PT.ua (PT.universe_choice PT.raise_guard PT.ub PT.ua))

let j3_document : P.document =
  def_axiom_refute PT.ite_int_else_swapped (PT.not_eq (PT.int_choice PT.pb PT.ione PT.izero) PT.izero)
    (R.mk_not_expr PT.pb)

let j1_certified () : Lemma (RD.check_root_document PT.core_schema j1_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema j1_document == RD.RootCertified)

let j2_certified () : Lemma (RD.check_root_document PT.core_schema j2_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema j2_document == RD.RootCertified)

let j3_certified () : Lemma (RD.check_root_document PT.core_schema j3_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema j3_document == RD.RootCertified)

let choice_documents_false (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema j1_document i /\ falsified u PT.core_schema j2_document i /\
                   falsified u PT.core_schema j3_document i) =
  j1_certified (); RD.lemma_root_certified u PT.core_schema j1_document i;
  j2_certified (); RD.lemma_root_certified u PT.core_schema j2_document i;
  j3_certified (); RD.lemma_root_certified u PT.core_schema j3_document i

let choice_documents_standard (u:TR.uninterpreted) (uf:TR.symbols u PT.core_schema)
  : Lemma (TR.root_model u PT.core_schema (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema j1_document (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema j2_document (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema j3_document (TR.standard u PT.core_schema uf)) =
  TR.lemma_standard_root u PT.core_schema uf;
  choice_documents_false u (TR.standard u PT.core_schema uf)

(* False variants (counter-models: Z3SortedProofTests.choice_counter_models)
   stay open obligations: the guard flipped, the other branch, another
   condition. *)
let j4_flipped_guard_pending ()
  : Lemma (RD.check_root_document PT.core_schema
             (def_axiom_refute PT.flipped_guard_mutant (R.mk_not_expr PT.pb)
                (PT.not_eq PT.ione (PT.int_choice PT.pb PT.ione PT.izero))) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema
                 (def_axiom_refute PT.flipped_guard_mutant (R.mk_not_expr PT.pb)
                    (PT.not_eq PT.ione (PT.int_choice PT.pb PT.ione PT.izero))) == RD.RootPending 1)

let j5_wrong_branch_pending ()
  : Lemma (RD.check_root_document PT.core_schema
             (def_axiom_refute PT.wrong_branch_mutant PT.pb
                (PT.not_eq PT.izero (PT.int_choice PT.pb PT.ione PT.izero))) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema
                 (def_axiom_refute PT.wrong_branch_mutant PT.pb
                    (PT.not_eq PT.izero (PT.int_choice PT.pb PT.ione PT.izero))) == RD.RootPending 1)

let j6_other_condition_pending ()
  : Lemma (RD.check_root_document PT.core_schema
             (def_axiom_refute PT.other_condition_mutant PT.pb
                (PT.not_eq PT.ione (PT.int_choice PT.qb PT.ione PT.izero))) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema
                 (def_axiom_refute PT.other_condition_mutant PT.pb
                    (PT.not_eq PT.ione (PT.int_choice PT.qb PT.ione PT.izero))) == RD.RootPending 1)

(* ---------------------------------------------------------------------- *)
(* K. Int equality/order laws over the commuted difference (-1) * y + x    *)
(* ---------------------------------------------------------------------- *)

(* FStar.Math.Lemmas-2 q12 node 68: x = y from (-1) * y + x >= 0 and <= 0,
   x the nonconstant product and y the opaque application; the commuted
   triangle clause and antisymmetry clause. *)
let commuted_implied_document (premises:list int) : P.document =
  doc [PT.geq PT.cgap PT.izero; PT.leq PT.cgap PT.izero; PT.not_eq PT.product PT.la]
      [entry U.Asserted (PT.geq PT.cgap PT.izero) []; entry U.Asserted (PT.leq PT.cgap PT.izero) [];
       entry th_lemma (R.mk_eq_expr PT.product PT.la) premises;
       entry U.Asserted (PT.not_eq PT.product PT.la) [];
       entry U.UnitResolution R.false_expr [2; 3]]
      4

let k1_document : P.document = commuted_implied_document [0; 1]

let k2_document : P.document =
  refute2 PT.commuted_eq_upper (R.mk_eq_expr PT.product PT.la) (R.mk_not_expr (PT.leq PT.cgap PT.izero))

let k3_document : P.document =
  refute3 PT.commuted_antisymmetry (PT.not_eq PT.product PT.la) (PT.leq PT.cgap PT.izero) (PT.geq PT.cgap PT.izero)

let k1_certified () : Lemma (RD.check_root_document PT.core_schema k1_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema k1_document == RD.RootCertified)

let k2_certified () : Lemma (RD.check_root_document PT.core_schema k2_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema k2_document == RD.RootCertified)

let k3_certified () : Lemma (RD.check_root_document PT.core_schema k3_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema k3_document == RD.RootCertified)

let commuted_documents_false (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema k1_document i /\ falsified u PT.core_schema k2_document i /\
                   falsified u PT.core_schema k3_document i) =
  k1_certified (); RD.lemma_root_certified u PT.core_schema k1_document i;
  k2_certified (); RD.lemma_root_certified u PT.core_schema k2_document i;
  k3_certified (); RD.lemma_root_certified u PT.core_schema k3_document i

let commuted_documents_standard (u:TR.uninterpreted) (uf:TR.symbols u PT.core_schema)
  : Lemma (TR.root_model u PT.core_schema (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema k1_document (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema k2_document (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema k3_document (TR.standard u PT.core_schema uf)) =
  TR.lemma_standard_root u PT.core_schema uf;
  commuted_documents_false u (TR.standard u PT.core_schema uf)

(* False variants stay open obligations (counter-models:
   Z3SortedProofTests.commuted_counter_models): the coefficient +1, and the
   two bounds with x and y swapped in one of them. *)
let k4_plus_one_pending ()
  : Lemma (RD.check_root_document PT.core_schema
             (refute2 PT.commuted_plus_one_mutant (R.mk_eq_expr PT.xi PT.yi)
                (R.mk_not_expr (PT.leq (App PT.iadd [App PT.imul [PT.ione; PT.yi]; PT.xi]) PT.izero))) ==
           RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema
                 (refute2 PT.commuted_plus_one_mutant (R.mk_eq_expr PT.xi PT.yi)
                    (R.mk_not_expr (PT.leq (App PT.iadd [App PT.imul [PT.ione; PT.yi]; PT.xi]) PT.izero))) ==
               RD.RootPending 1)

let k5_swapped_bounds_document : P.document =
  doc [PT.geq (PT.commuted PT.xi PT.yi) PT.izero; PT.leq (PT.commuted PT.yi PT.xi) PT.izero; PT.not_eq PT.xi PT.yi]
      [entry U.Asserted (PT.geq (PT.commuted PT.xi PT.yi) PT.izero) [];
       entry U.Asserted (PT.leq (PT.commuted PT.yi PT.xi) PT.izero) [];
       entry th_lemma (R.mk_eq_expr PT.xi PT.yi) [0; 1];
       entry U.Asserted (PT.not_eq PT.xi PT.yi) [];
       entry U.UnitResolution R.false_expr [2; 3]]
      4

let k5_swapped_bounds_pending ()
  : Lemma (RD.check_root_document PT.core_schema k5_swapped_bounds_document == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema k5_swapped_bounds_document == RD.RootPending 1)

(* ---------------------------------------------------------------------- *)
(* L. Boolean or-gate definition axioms (same-model tautologies)           *)
(* ---------------------------------------------------------------------- *)

let def_axiom_refute3 (clause u1 u2 u3:expr) : P.document =
  doc [u1; u2; u3]
      [entry U.DefAxiom clause []; entry U.Asserted u1 []; entry U.Asserted u2 []; entry U.Asserted u3 [];
       entry U.UnitResolution R.false_expr [0; 1; 2; 3]]
      4

(* The nested or-intro of Tactics.BreakVC-1 q1 node 51 and an or-elim, each
   refuted by the complements of its literals. *)
let l1_document : P.document =
  def_axiom_refute PT.or_intro_nested (R.mk_not_expr PT.bvc_g) (R.mk_not_expr PT.bvc_h)

let l2_document : P.document =
  def_axiom_refute3 PT.or_elim_two (PT.disjunction [PT.atom_a; PT.atom_b])
    (R.mk_not_expr PT.atom_a) (R.mk_not_expr PT.atom_b)

let l1_certified () : Lemma (RD.check_root_document PT.core_schema l1_document == RD.RootCertified) =
  assert (RD.check_root_document PT.core_schema l1_document == RD.RootCertified) by
    (Tac.norm [nbe; delta; iota; zeta; primops]; Tac.trivial ())

let l2_certified () : Lemma (RD.check_root_document PT.core_schema l2_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema l2_document == RD.RootCertified)

let gate_documents_false (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema l1_document i /\ falsified u PT.core_schema l2_document i) =
  l1_certified (); RD.lemma_root_certified u PT.core_schema l1_document i;
  l2_certified (); RD.lemma_root_certified u PT.core_schema l2_document i

let gate_documents_standard (u:TR.uninterpreted) (uf:TR.symbols u PT.core_schema)
  : Lemma (TR.root_model u PT.core_schema (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema l1_document (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema l2_document (TR.standard u PT.core_schema uf)) =
  TR.lemma_standard_root u PT.core_schema uf;
  gate_documents_false u (TR.standard u PT.core_schema uf)

(* False variants stay open obligations (counter-models:
   Z3SortedProofTests.gate_counter_models): the or-elim with a disjunct
   dropped, and an or-intro literal complementing no disjunct. *)
let l3_dropped_pending ()
  : Lemma (RD.check_root_document PT.core_schema
             (def_axiom_refute3 PT.elim_dropped_mutant (PT.disjunction [PT.atom_a; PT.atom_b; PT.atom_c])
                (R.mk_not_expr PT.atom_a) (R.mk_not_expr PT.atom_b)) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema
                 (def_axiom_refute3 PT.elim_dropped_mutant (PT.disjunction [PT.atom_a; PT.atom_b; PT.atom_c])
                    (R.mk_not_expr PT.atom_a) (R.mk_not_expr PT.atom_b)) == RD.RootPending 1)

let l4_member_pending ()
  : Lemma (RD.check_root_document PT.core_schema
             (def_axiom_refute PT.intro_member_mutant (R.mk_not_expr (PT.disjunction [PT.atom_a; PT.atom_b]))
                PT.atom_c) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema
                 (def_axiom_refute PT.intro_member_mutant (R.mk_not_expr (PT.disjunction [PT.atom_a; PT.atom_b]))
                    PT.atom_c) == RD.RootPending 1)

(* ---------------------------------------------------------------------- *)
(* M. Coefficient-free linear Int consequences (recomputed weights)        *)
(* ---------------------------------------------------------------------- *)

(* The facts asserted (entries 0 .. n-1), the th-lemma step concluding the
   target from all of them (entry n, no coefficients), the negated target
   asserted, and false by unit resolution. Fixtures of Z3SortedProofTests:
   the equality chain x = z through y, FStar.Math.Euclid-2 q3 node 306
   (-1 = x from not (x <= -2) and not (x >= 0), strict-Int rounding), and
   false from not (x <= 0) and not (x >= 1) as the root step itself. *)
let rec asserted_entries (es:list expr) : Tot (list P.entry) (decreases es) =
  match es with [] -> [] | e :: rest -> entry U.Asserted e [] :: asserted_entries rest

let rec first_ids (n:nat) : Tot (list int) (decreases n) =
  if n = 0 then [] else L.append (first_ids (n - 1)) [n - 1]

let linear_refutation (facts:list expr) (target:expr) : P.document =
  let n = L.length facts in
  doc (L.append facts [R.mk_not_expr target])
      (L.append (asserted_entries facts)
        [entry th_lemma target (first_ids n); entry U.Asserted (R.mk_not_expr target) [];
         entry U.UnitResolution R.false_expr [n; n + 1]])
      (n + 2)

let linear_conflict (facts:list expr) : P.document =
  let n = L.length facts in
  doc facts (L.append (asserted_entries facts) [entry th_lemma R.false_expr (first_ids n)]) n

let m1_document : P.document = linear_refutation PT.lin_chain PT.lin_chain_target
let m2_document : P.document = linear_refutation PT.lin_tight PT.lin_tight_target
let m3_document : P.document = linear_conflict PT.lin_conflict

let m1_certified () : Lemma (RD.check_root_document PT.core_schema m1_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema m1_document == RD.RootCertified)

let m2_certified () : Lemma (RD.check_root_document PT.core_schema m2_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema m2_document == RD.RootCertified)

let m3_certified () : Lemma (RD.check_root_document PT.core_schema m3_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema m3_document == RD.RootCertified)

let linear_documents_false (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema m1_document i /\ falsified u PT.core_schema m2_document i /\
                   falsified u PT.core_schema m3_document i) =
  m1_certified (); RD.lemma_root_certified u PT.core_schema m1_document i;
  m2_certified (); RD.lemma_root_certified u PT.core_schema m2_document i;
  m3_certified (); RD.lemma_root_certified u PT.core_schema m3_document i

let linear_documents_standard (u:TR.uninterpreted) (uf:TR.symbols u PT.core_schema)
  : Lemma (TR.root_model u PT.core_schema (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema m1_document (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema m2_document (TR.standard u PT.core_schema uf) /\
           falsified u PT.core_schema m3_document (TR.standard u PT.core_schema uf)) =
  TR.lemma_standard_root u PT.core_schema uf;
  linear_documents_false u (TR.standard u PT.core_schema uf)

(* False variants stay open obligations (counter-models:
   Z3SortedProofTests.linear_counter_models): a dropped bound, one link of
   the chain at Real, and non-strict bounds in place of the strict ones (for
   the equation and for the conflict). *)
let m4_dropped_pending ()
  : Lemma (RD.check_root_document PT.core_schema (linear_refutation PT.lin_dropped PT.lin_chain_target) ==
           RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (linear_refutation PT.lin_dropped PT.lin_chain_target) ==
               RD.RootPending 1)

let m5_mixed_pending ()
  : Lemma (RD.check_root_document PT.core_schema (linear_refutation PT.lin_mixed PT.lin_chain_target) ==
           RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (linear_refutation PT.lin_mixed PT.lin_chain_target) ==
               RD.RootPending 1)

let m6_weak_bounds_pending ()
  : Lemma (RD.check_root_document PT.core_schema (linear_refutation PT.lin_weak_tight PT.lin_tight_target) ==
           RD.RootPending 1 /\
           RD.check_root_document PT.core_schema (linear_conflict PT.lin_weak_conflict) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (linear_refutation PT.lin_weak_tight PT.lin_tight_target) ==
               RD.RootPending 1);
  assert_norm (RD.check_root_document PT.core_schema (linear_conflict PT.lin_weak_conflict) == RD.RootPending 1)

(* M7. Genuinely false steps over the satisfiable bounds 0 < x < 2 (x = 1:
   Z3SortedProofTests.linear_counter_models) stay open whatever the rule
   label or the supplied coefficients: x = 0 as a th-lemma or as an
   arith/farkas step with weights, and false as a th-lemma or with the
   weights that refute 0 < x < 1. No certificate, supplied or recomputed,
   exists. *)
let between_equation (r:U.rule) : P.document =
  doc (L.append PT.lin_between [R.mk_not_expr PT.lin_between_target])
      (L.append (asserted_entries PT.lin_between)
        [entry r PT.lin_between_target [0; 1]; entry U.Asserted (R.mk_not_expr PT.lin_between_target) [];
         entry U.UnitResolution R.false_expr [2; 3]])
      4

let between_conflict (r:U.rule) : P.document =
  doc PT.lin_between (L.append (asserted_entries PT.lin_between) [entry r R.false_expr [0; 1]]) 2

let m7_false_steps_pending ()
  : Lemma (RD.check_root_document PT.core_schema (between_equation th_lemma) == RD.RootPending 1 /\
           RD.check_root_document PT.core_schema (between_equation (U.ArithmeticFarkas [(1, 1); (1, 1); (1, 1)])) ==
             RD.RootPending 1 /\
           RD.check_root_document PT.core_schema (between_conflict th_lemma) == RD.RootPending 1 /\
           RD.check_root_document PT.core_schema (between_conflict (U.ArithmeticFarkas [(1, 1); (1, 1)])) ==
             RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (between_equation th_lemma) == RD.RootPending 1);
  assert_norm (RD.check_root_document PT.core_schema (between_equation (U.ArithmeticFarkas [(1, 1); (1, 1); (1, 1)])) ==
               RD.RootPending 1);
  assert_norm (RD.check_root_document PT.core_schema (between_conflict th_lemma) == RD.RootPending 1);
  assert_norm (RD.check_root_document PT.core_schema (between_conflict (U.ArithmeticFarkas [(1, 1); (1, 1)])) ==
               RD.RootPending 1)
