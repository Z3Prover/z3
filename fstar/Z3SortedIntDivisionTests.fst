module Z3SortedIntDivisionTests

(* Tests of the Sorted Int division laws and the guarded Int div/mod clauses
   (run e78cd96c): Z3TypedRoot's IntDiv/IntMod classes, Z3SortedIntDivision's
   laws, their derivation from R2 of every root model
   (Z3SortedDivisionRoot), and the clause check Z3SortedProof.division_order
   with the five producer templates

     d = 0 \/ mod x d >= 0
     d <= 0 \/ (mod x d) + (-1)*d <= -1
     d >= 0 \/ (mod x d) + d <= -1
     d = 0 \/ x = d*(div x d) + mod x d    (and the equation's sides swapped)

   D1 the clause check (normalized): each template over opaque, compound and
      uninterpreted-function operands, in both literal orders, is checked by
      division_order and by no other kernel; its refusals: a missing guard (a
      unit clause), a guard of the wrong sign for its bound, a wrong bound
      constant, mod and div exchanged, a guard on x instead of d, a wrong
      coefficient or operand in the decomposition, lookalike declarations
      (counterfeit div/mod/=/0/-1, twin parameter, Real division tag, another
      name), the unguarded alias of a division with its div0, and VALID
      clauses in an unsupported shape (a weaker guard, a commuted product, 0 on
      the left, a third literal, a strict bound), which are SHAPE controls and
      not false mutants.
   D2 documents: refutations using a template are RootCertified on both
      routes and false in every root model; the same documents with a wrong
      clause stay RootPending.
   D3 the clause theorem in every root model, from Z3SortedProof.
      lemma_division_clause and the laws derived from R2 of that model.
   D4 counter-models: every FALSE mutant of D1 is false in the standard root
      model of a free choice that makes a division by zero answer -1 / 5 (and
      its div0 alias 0), at a concrete typed environment of two Int variables,
      so a check that accepted one would be unsound; and the guarded
      templates are TRUE at the same environments (the positive instances).

   Deep and large inputs, and the producer's own proofs, run natively
   (test_native_bridge.ml, Z3CherryTests.fst). *)

open Z3AstTheory
open Z3ValueTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3Definitions
module L = FStar.List.Tot
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module SP = Z3SortedProof
module DT = Z3SortedDatatype
module P = Z3ProofDocument
module U = Z3UnifiedProof
module R = Z3ResolutionProofTheory
module BR = Z3BooleanRewrite
module B = Z3BoundedBoolEquiv
module NR = Z3NnfReplay
module RD = Z3SortedRootDocument
module PT = Z3SortedProofTests
module RR = Z3SortedRealRoot
module DV = Z3SortedIntDivision
module DR = Z3SortedDivisionRoot
module AR = Z3SortedArithmetic
module SI = Z3SortedInteger
module LA = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed

(* ---------------------------------------------------------------------- *)
(* Shapes                                                                   *)
(* ---------------------------------------------------------------------- *)

let integer : sort = TR.int_s
let real : sort = TR.real_s

let constant (name:string) (s:sort) (params:list int) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = params } []

let x : expr = constant "x" integer []
let d : expr = constant "d" integer []
let i : expr = constant "i" integer []
let j : expr = constant "j" integer []

let inum (n:int) : expr = App (TR.int_numeral n) []
let zero : expr = inum 0
let m1 : expr = inum (-1)
let two : expr = inum 2

let eq (a b:expr) : expr = R.mk_eq_expr a b
let neg (a:expr) : expr = R.mk_not_expr a
let le (a b:expr) : expr = App (TR.le_decl integer) [a; b]
let lt (a b:expr) : expr = App (TR.lt_decl integer) [a; b]
let ge (a b:expr) : expr = App (TR.ge_decl integer) [a; b]
let plus (a b:expr) : expr = App (TR.plus_decl integer) [a; b]
let times (a b:expr) : expr = App (TR.times_decl integer) [a; b]
let or2 (a b:expr) : expr = App (BR.connective_decl BR.Disjunction [a; b]) [a; b]
let or3 (a b c':expr) : expr = App (BR.connective_decl BR.Disjunction [a; b; c']) [a; b; c']

(* An uninterpreted Int function, an opaque compound operand. *)
let fdecl : func_decl = { decl_name = "f"; domain = [integer]; range = integer; interp = None; int_params = [] }
let fapp (a:expr) : expr = App fdecl [a]

let quot (a b:expr) : expr = App DV.quotient_decl [a; b]
let rem (a b:expr) : expr = App DV.remainder_decl [a; b]

(* x - y as the producer writes it. *)
let diff (a b:expr) : expr = plus a (times m1 b)
let diff_swapped (a b:expr) : expr = plus (times m1 b) a

(* The five templates. *)
let t_lower (a b:expr) : expr = or2 (eq b zero) (ge (rem a b) zero)
let t_upper_pos (a b:expr) : expr = or2 (le b zero) (le (diff (rem a b) b) m1)
let t_upper_neg (a b:expr) : expr = or2 (ge b zero) (le (plus (rem a b) b) m1)
let decomposition (a b:expr) : expr = plus (times b (quot a b)) (rem a b)
let t_decomposition (a b:expr) : expr = or2 (eq b zero) (eq a (decomposition a b))
let t_decomposition_swapped (a b:expr) : expr = or2 (eq b zero) (eq (decomposition a b) a)

(* Counterfeits: the same spelling and signature, no or another tag. *)
let fake_rem_decl : func_decl = { DV.remainder_decl with interp = None }
let fake_quot_decl : func_decl = { DV.quotient_decl with interp = None }
let rem_with_quotient_tag : func_decl = { DV.remainder_decl with interp = Some Z3IntegerDivision.op_idiv }
let rem_twin : func_decl = { DV.remainder_decl with int_params = [1] }
let rem_renamed : func_decl = { DV.remainder_decl with decl_name = "remainder" }
let rem_real_tag : func_decl = { DV.remainder_decl with interp = Some op_arith_div }
let rem_over_real : func_decl =
  { decl_name = "mod"; domain = [real; real]; range = real; interp = Some Z3IntegerDivision.op_mod; int_params = [] }
let fake_eq_decl : func_decl = { R.eq_decl integer with interp = None }
let fake_zero : expr = constant "0" integer []
let fake_m1 : expr = constant "-1" integer []
let fake_le_decl : func_decl = { TR.le_decl integer with interp = None }

let th_node (clause:expr) : U.proof_node =
  { U.kind = U.Unverified "th-lemma"; conclusion = U.Holds clause; premises = [] }

let pending_of (sch:S.checked_schema) (n:U.proof_node) : option nat =
  match SP.check_node_cached sch [] n with
  | Some (_, p) -> Some p
  | None -> None

(* The disjuncts of check_node_cached that read a premise-free theory-lemma
   clause other than the division check. *)
let old_paths (clause:expr) : bool =
  SP.consequence PT.core_schema [] clause ||
  DT.consequence PT.core_schema [] (SP.scoped_proposition ({ U.conclusion = U.Holds clause; hypotheses = [] })) ||
  SP.linear_consequence [] clause ||
  SP.order_clause clause || SP.real_order PT.core_schema (th_node clause)

let checked_clause (clause:expr) : bool =
  SP.division_order (th_node clause) && not (old_paths clause) &&
  pending_of PT.core_schema (th_node clause) = Some 0

let refused_clause (clause:expr) : bool =
  not (SP.division_order (th_node clause)) && not (old_paths clause) &&
  pending_of PT.core_schema (th_node clause) = Some 1

(* ---------------------------------------------------------------------- *)
(* D1. The clause check                                                     *)
(* ---------------------------------------------------------------------- *)

(* The five templates over opaque constants, a datatype-free compound
   operand (x + 1, a product) and an uninterpreted function application, with
   the difference in both operand orders and in both literal orders. *)
let positives : list expr = [
  t_lower x d;
  t_lower i j;
  t_lower (plus i (inum 1)) (times i j);
  t_lower (fapp x) (fapp d);
  t_lower x (inum 3);
  t_lower (inum 7) d;
  or2 (ge (rem x d) zero) (eq d zero);
  t_upper_pos x d;
  t_upper_pos (fapp i) (times i j);
  or2 (le (diff (rem x d) d) m1) (le d zero);
  or2 (le d zero) (le (diff_swapped (rem x d) d) m1);
  t_upper_neg x d;
  t_upper_neg (plus i (inum 1)) (fapp j);
  or2 (le (plus (rem x d) d) m1) (ge d zero);
  t_decomposition x d;
  t_decomposition (plus i (inum 1)) (times i j);
  t_decomposition (fapp x) (fapp d);
  t_decomposition_swapped x d;
  t_decomposition_swapped (plus i (inum 1)) (times i j);
  or2 (eq x (decomposition x d)) (eq d zero);
  or2 (eq (decomposition x d) x) (eq d zero);
  (* the numeral instance x = 7, d = -2 (7 div -2 = -3, 7 mod -2 = 1) of every template *)
  t_lower (inum 7) (inum (-2));
  t_upper_pos (inum 7) (inum 2);
  t_upper_neg (inum 7) (inum (-2));
  t_decomposition (inum 7) (inum (-2));
  t_decomposition_swapped (inum 7) (inum (-2))
]

let d1_positives () : Lemma (L.for_all checked_clause positives) =
  assert_norm (L.for_all checked_clause positives)

(* FALSE clauses (each is false in some root model, see D4): refused. *)
let mutants : list expr = [
  (* a missing guard *)
  ge (rem x d) zero;
  le (diff (rem x d) d) m1;
  (* a guard of the wrong sign for the bound *)
  or2 (ge d zero) (le (diff (rem x d) d) m1);
  or2 (le d zero) (le (plus (rem x d) d) m1);
  (* a wrong bound constant *)
  or2 (le d zero) (le (diff (rem x d) d) (inum (-2)));
  or2 (ge d zero) (le (plus (rem x d) d) (inum (-2)));
  (* mod and div exchanged, the guard on x instead of d *)
  or2 (eq d zero) (ge (quot x d) zero);
  or2 (eq x zero) (ge (rem x d) zero);
  (* the decomposition with a wrong operand or coefficient, or no guard *)
  or2 (eq d zero) (eq x (plus (times d (quot d x)) (rem x d)));
  or2 (eq d zero) (eq x (plus (times d (quot x d)) (times two (rem x d))));
  or2 (eq d zero) (eq x (plus (times x (quot x d)) (rem x d)));
  or2 (eq d zero) (eq x (plus (times d (quot x d)) (rem d x)));
  eq x (decomposition x d);
  (* the zero-divisor controls at numerals: no guard, or a guard on the dividend instead of the divisor *)
  ge (rem (inum 7) zero) zero;
  or2 (eq (inum 7) zero) (ge (rem (inum 7) zero) zero);
  or2 (eq (inum 7) zero) (eq (inum 7) (plus (times zero (quot (inum 7) zero)) (rem (inum 7) zero)));
  (* a division is not its div0 alias without a guard *)
  eq (quot x d) (App ({ DV.quotient_decl with decl_name = "div0"; interp = None }) [x; d]);
  (* lookalike declarations: free symbols, hence not constrained *)
  or2 (eq d zero) (ge (App fake_rem_decl [x; d]) zero);
  or2 (eq d zero) (ge (App rem_with_quotient_tag [x; d]) zero);
  or2 (eq d zero) (ge (App rem_twin [x; d]) zero);
  or2 (eq d zero) (ge (App rem_renamed [x; d]) zero);
  or2 (eq d zero) (ge (App rem_real_tag [x; d]) zero);
  or2 (eq d zero) (eq x (plus (times d (App fake_quot_decl [x; d])) (rem x d)));
  or2 (App fake_eq_decl [d; zero]) (ge (rem x d) zero);
  or2 (eq d fake_zero) (ge (rem x d) zero);
  or2 (eq d zero) (ge (rem x d) fake_zero);
  or2 (le d zero) (le (diff (rem x d) d) fake_m1);
  or2 (App fake_le_decl [d; zero]) (le (diff (rem x d) d) m1)
]

let d1_mutants () : Lemma (L.for_all refused_clause mutants) =
  assert_norm (L.for_all refused_clause mutants)

(* VALID clauses in an unsupported shape: SHAPE-refusal controls, not false
   mutants (each statement holds in every root model). *)
let unsupported : list expr = [
  or2 (le d zero) (ge (rem x d) zero);                       (* a weaker guard *)
  or2 (ge d zero) (ge (rem x d) zero);
  or2 (eq zero d) (ge (rem x d) zero);                       (* 0 on the left *)
  or2 (eq d zero) (ge zero (inum 0));
  or2 (eq d zero) (eq x (plus (times (quot x d) d) (rem x d)));   (* a commuted product *)
  or2 (eq d zero) (eq x (plus (rem x d) (times d (quot x d))));   (* the summands exchanged *)
  or2 (le d zero) (lt (diff (rem x d) d) zero);              (* a strict bound *)
  or2 (le d zero) (le (rem x d) (diff d (inum 1)));          (* d - 1 written with Int - *)
  or3 (eq d zero) (ge (rem x d) zero) (le x zero)            (* a third literal *)
]

let d1_unsupported () : Lemma (L.for_all refused_clause unsupported) =
  assert_norm (L.for_all refused_clause unsupported)

(* Not an Int clause, a leaf, a lemma-rule node, and the equation conclusions. *)
let d1_node_guards ()
  : Lemma (not (SP.division_order ({ th_node (t_lower x d) with U.kind = U.Asserted })) /\
           not (SP.division_order ({ th_node (t_lower x d) with U.kind = U.Hypothesis })) /\
           not (SP.division_order ({ th_node (t_lower x d) with U.kind = U.LemmaRule })) /\
           not (SP.division_order ({ U.kind = U.RewriteRule; conclusion = U.Equal (t_lower x d) (t_lower x d);
                                     premises = [] })) /\
           SP.division_order ({ th_node (t_lower x d) with U.kind = U.RewriteRule })) =
  assert_norm (not (SP.division_order ({ th_node (t_lower x d) with U.kind = U.Asserted })));
  assert_norm (not (SP.division_order ({ th_node (t_lower x d) with U.kind = U.Hypothesis })));
  assert_norm (not (SP.division_order ({ th_node (t_lower x d) with U.kind = U.LemmaRule })));
  assert_norm (not (SP.division_order ({ U.kind = U.RewriteRule; conclusion = U.Equal (t_lower x d) (t_lower x d);
                                         premises = [] })));
  assert_norm (SP.division_order ({ th_node (t_lower x d) with U.kind = U.RewriteRule }))

(* ---------------------------------------------------------------------- *)
(* D2. Documents                                                            *)
(* ---------------------------------------------------------------------- *)

let entry (r:U.rule) (f:expr) (ids:list int) : P.entry = { P.rule = r; formula = f; premise_ids = ids }

let doc (assertions:list expr) (entries:list P.entry) (root:int) : P.document = {
  P.declarations = []; P.expressions = []; P.assertions = assertions; P.entries = entries; P.root = root;
}

(* The refutation of {d <> 0, mod x d < 0}: the guarded clause d = 0 \/ mod x d >= 0
   and unit resolution with the two assertions. *)
let lower_document (clause:expr) : P.document =
  doc [neg (eq d zero); neg (ge (rem x d) zero)]
      [entry U.Asserted (neg (eq d zero)) [];
       entry U.Asserted (neg (ge (rem x d) zero)) [];
       entry (U.Unverified "th-lemma") clause [];
       entry U.UnitResolution R.false_expr [2; 0; 1]]
      3

(* {d > 0, mod x d >= d}: d <= 0 \/ mod x d - d <= -1 *)
let upper_document (clause:expr) : P.document =
  doc [neg (le d zero); neg (le (diff (rem x d) d) m1)]
      [entry U.Asserted (neg (le d zero)) [];
       entry U.Asserted (neg (le (diff (rem x d) d) m1)) [];
       entry (U.Unverified "th-lemma") clause [];
       entry U.UnitResolution R.false_expr [2; 0; 1]]
      3

(* {d <> 0, x <> d*(div x d) + mod x d} *)
let decomposition_document (clause:expr) : P.document =
  doc [neg (eq d zero); neg (eq x (decomposition x d))]
      [entry U.Asserted (neg (eq d zero)) [];
       entry U.Asserted (neg (eq x (decomposition x d))) [];
       entry (U.Unverified "th-lemma") clause [];
       entry U.UnitResolution R.false_expr [2; 0; 1]]
      3

let falsified (u:TR.uninterpreted) (sch:S.checked_schema) (dc:P.document) (i:TR.interp u sch) : prop =
  RD.typed_assertions dc.P.assertions /\ not (RD.root_truths u sch i dc.P.assertions)

let d2_certified ()
  : Lemma (RD.check_root_document PT.core_schema (lower_document (t_lower x d)) == RD.RootCertified /\
           RD.check_root_document_epsilon PT.core_schema (lower_document (t_lower x d)) == RD.RootCertified /\
           RD.check_root_document PT.core_schema (upper_document (t_upper_pos x d)) == RD.RootCertified /\
           RD.check_root_document_epsilon PT.core_schema (upper_document (t_upper_pos x d)) == RD.RootCertified /\
           RD.check_root_document PT.core_schema (decomposition_document (t_decomposition x d)) == RD.RootCertified /\
           RD.check_root_document_epsilon PT.core_schema (decomposition_document (t_decomposition x d)) == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema (lower_document (t_lower x d)) == RD.RootCertified);
  assert_norm (RD.check_root_document_epsilon PT.core_schema (lower_document (t_lower x d)) == RD.RootCertified);
  assert_norm (RD.check_root_document PT.core_schema (upper_document (t_upper_pos x d)) == RD.RootCertified);
  assert_norm (RD.check_root_document_epsilon PT.core_schema (upper_document (t_upper_pos x d)) == RD.RootCertified);
  assert_norm (RD.check_root_document PT.core_schema (decomposition_document (t_decomposition x d)) == RD.RootCertified);
  assert_norm (RD.check_root_document_epsilon PT.core_schema (decomposition_document (t_decomposition x d)) == RD.RootCertified)

let d2_false_in_every_root (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema (lower_document (t_lower x d)) i /\
                   falsified u PT.core_schema (upper_document (t_upper_pos x d)) i /\
                   falsified u PT.core_schema (decomposition_document (t_decomposition x d)) i) =
  d2_certified ();
  RD.lemma_root_certified u PT.core_schema (lower_document (t_lower x d)) i;
  RD.lemma_root_certified u PT.core_schema (upper_document (t_upper_pos x d)) i;
  RD.lemma_root_certified u PT.core_schema (decomposition_document (t_decomposition x d)) i

let is_pending (v:RD.root_verdict) : bool = RD.RootPending? v

(* The same documents with a wrong clause stay open: the clause is checked by
   no kernel and the unit resolution that reads it is no consequence either. *)
let d2_mutant_documents ()
  : Lemma (is_pending (RD.check_root_document PT.core_schema (lower_document (or2 (eq x zero) (ge (rem x d) zero)))) /\
           is_pending (RD.check_root_document PT.core_schema (lower_document (ge (rem x d) zero))) /\
           is_pending (RD.check_root_document PT.core_schema (upper_document (or2 (ge d zero) (le (diff (rem x d) d) m1)))) /\
           is_pending (RD.check_root_document PT.core_schema
                         (decomposition_document (or2 (eq d zero) (eq x (plus (times d (quot d x)) (rem x d))))))) =
  assert_norm (is_pending (RD.check_root_document PT.core_schema (lower_document (or2 (eq x zero) (ge (rem x d) zero)))));
  assert_norm (is_pending (RD.check_root_document PT.core_schema (lower_document (ge (rem x d) zero))));
  assert_norm (is_pending (RD.check_root_document PT.core_schema (upper_document (or2 (ge d zero) (le (diff (rem x d) d) m1)))));
  assert_norm (is_pending (RD.check_root_document PT.core_schema
                             (decomposition_document (or2 (eq d zero) (eq x (plus (times d (quot d x)) (rem x d)))))))

(* ---------------------------------------------------------------------- *)
(* D3. The clause theorem in every root model                                *)
(* ---------------------------------------------------------------------- *)

(* An accepted guarded clause is true in EVERY root model of every checked
   schema: Z3SortedProof.lemma_division_clause with the division laws
   derived from R2 of that same model. *)
let lemma_clause_in_every_root (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (c:expr)
  : Lemma (requires TR.root_model u sch i /\ D.scoped [] c /\ get_sort c == bool_sort /\ SP.division_clause c)
          (ensures TR.truth sch (V.evaluate (S.signature sch) i [] (T.empty_environment (S.signature sch)) c)) =
  DR.lemma_root_division_laws u sch i;
  SP.lemma_division_clause sch (TR.booleans u) (SR.root_scalars u) i c;
  SR.lemma_truth_agreement u sch i [] (T.empty_environment (S.signature sch)) c

(* ---------------------------------------------------------------------- *)
(* D4. Counter-models and positive instances                                 *)
(* ---------------------------------------------------------------------- *)

(* The standard root model of an ADVERSARIAL free choice: every division by
   zero answers 5, every modulus zero -1, and the unclassified symbols the
   schema's inhabitant (0 at Int). The free choice is legal at a zero divisor
   only: at a nonzero divisor the root class fixes div and mod. *)
let esch : S.checked_schema = RR.empty_schema

unfold let iscope : list sort = [TR.int_s; TR.int_s]

let vd : expr = Var 0 integer
let vx : expr = Var 1 integer

let uf_adversary (u:TR.uninterpreted) : TR.symbols u esch = {
  TR.apply = (fun f _ ->
    match DV.classify f with
    | DV.Remainder -> (TR.make #u #(S.signature esch) integer (-1) <: TR.tvalue u esch f.range)
    | DV.Quotient -> (TR.make #u #(S.signature esch) integer 5 <: TR.tvalue u esch f.range)
    | DV.Other -> S.value_inhabitant esch (TR.default_value u) f.range);
  TR.lambda = (fun bound t _ -> S.value_inhabitant esch (TR.default_value u) (ArraySort bound t));
}

let cm (u:TR.uninterpreted) : TR.interp u esch = TR.standard u esch (uf_adversary u)

let env2 (u:TR.uninterpreted) (xv dv:int)
  : V.environment (TR.carrier u) (S.signature esch) iscope =
  fun (n:nat{n < 2}) -> V.Scalar integer ((if n = 1 then xv else dv) <: TR.carrier u integer)

let tv (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope) (e:expr) : GTot bool =
  T.truth_at esch (TR.booleans u) (SR.root_scalars u) (cm u) iscope rho e

let iv (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope) (e:expr) : GTot int =
  AR.integer esch (TR.booleans u) (SR.root_scalars u) (cm u) iscope rho e

let lemma_cm (u:TR.uninterpreted)
  : Lemma (TR.root_model u esch (cm u) /\ DV.division_laws esch (TR.booleans u) (SR.root_scalars u) (cm u)) =
  DR.lemma_standard_division_root u esch (uf_adversary u)

let lemma_vars (u:TR.uninterpreted) (xv dv:int)
  : Lemma (iv u (env2 u xv dv) vx == xv /\ iv u (env2 u xv dv) vd == dv) =
  assert_norm (D.scoped iscope vx /\ D.scoped iscope vd)

let lemma_num (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope) (n:int) (e:expr)
  : Lemma (requires D.scoped iscope e /\ AR.int_numeral n e) (ensures iv u rho e == n) =
  AR.lemma_int_numeral esch (TR.booleans u) (SR.root_scalars u) (cm u) iscope rho n e

let lemma_cmp (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope)
              (c':expr) (rel:LA.relation) (l r:expr)
  : Lemma (requires D.scoped iscope c' /\ LA.comparison c' == Some (rel, l, r) /\ get_sort l == integer)
          (ensures tv u rho c' <==> SI.compare rel (iv u rho l) (iv u rho r)) =
  AR.lemma_int_comparison esch (TR.booleans u) (SR.root_scalars u) (cm u) iscope rho c' rel l r

let lemma_bin (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope)
              (f:func_decl) (a b:expr) (o:LA.operation)
  : Lemma (requires D.scoped iscope (App f [a; b]) /\ SI.classify f == SI.Calculate o)
          (ensures (o == LA.Add ==> iv u rho (App f [a; b]) == iv u rho a + iv u rho b) /\
                   (o == LA.Mul ==> iv u rho (App f [a; b]) == iv u rho a * iv u rho b)) =
  AR.lemma_int_binary esch (TR.booleans u) (SR.root_scalars u) (cm u) iscope rho f a b o

(* mod and div at a nonzero divisor are the Euclidean remainder and quotient;
   at a zero divisor they are the adversary's answers. *)
let lemma_rem_nonzero (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope) (a b:expr)
  : Lemma (requires D.scoped iscope (rem a b) /\ ~(iv u rho b == 0))
          (ensures iv u rho (rem a b) == DV.remainder_of (iv u rho a) (iv u rho b)) =
  lemma_cm u;
  DV.lemma_classify_canonical ();
  DV.lemma_remainder_at esch (TR.booleans u) (SR.root_scalars u) (cm u) iscope rho DV.remainder_decl a b

let lemma_quot_nonzero (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope) (a b:expr)
  : Lemma (requires D.scoped iscope (quot a b) /\ ~(iv u rho b == 0))
          (ensures iv u rho (quot a b) == DV.quotient_of (iv u rho a) (iv u rho b)) =
  lemma_cm u;
  DV.lemma_classify_canonical ();
  DV.lemma_quotient_at esch (TR.booleans u) (SR.root_scalars u) (cm u) iscope rho DV.quotient_decl a b

let lemma_rem_zero (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope) (a b:expr)
  : Lemma (requires D.scoped iscope (rem a b) /\ iv u rho b == 0) (ensures iv u rho (rem a b) == (-1)) =
  lemma_cm u;
  DV.lemma_classify_canonical ();
  DV.lemma_evaluate_division_at esch (TR.booleans u) (SR.root_scalars u) (cm u) iscope rho DV.remainder_decl [a; b];
  let va = T.evaluate_at esch (TR.booleans u) (SR.root_scalars u) (cm u) iscope rho a in
  let vb = T.evaluate_at esch (TR.booleans u) (SR.root_scalars u) (cm u) iscope rho b in
  let xs = T.evaluate_arguments_at esch (TR.booleans u) (SR.root_scalars u) (cm u) iscope rho [a; b]
             DV.remainder_decl.domain in
  assert_norm (T.evaluate_arguments_at esch (TR.booleans u) (SR.root_scalars u) (cm u) iscope rho [a; b]
                 [integer; integer] == [va; vb]);
  SR.lemma_application_agreement u esch (cm u) DV.remainder_decl xs;
  DR.lemma_remainder_classify esch DV.remainder_decl;
  SR.lemma_number esch vb;
  TR.lemma_standard_int_divide_by_zero u esch (uf_adversary u) DV.remainder_decl va vb

(* A clause with two false literals is false. *)
let lemma_or2_false (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope) (a b:expr)
  : Lemma (requires D.scoped iscope (or2 a b) /\ not (tv u rho a) /\ not (tv u rho b))
          (ensures not (tv u rho (or2 a b))) =
  lemma_cm u;
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [a; b]) == T.Nary B.Or);
  NR.lemma_truth_or2 esch (TR.booleans u) (SR.root_scalars u) (cm u) iscope rho
    (BR.connective_decl BR.Disjunction [a; b]) a b B.Or

let lemma_plus (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope) (a b:expr)
  : Lemma (requires D.scoped iscope (plus a b))
          (ensures iv u rho (plus a b) == iv u rho a + iv u rho b) =
  assert_norm (SI.classify (TR.plus_decl integer) == SI.Calculate LA.Add);
  lemma_bin u rho (TR.plus_decl integer) a b LA.Add

let lemma_times (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope) (a b:expr)
  : Lemma (requires D.scoped iscope (times a b))
          (ensures iv u rho (times a b) == iv u rho a * iv u rho b) =
  assert_norm (SI.classify (TR.times_decl integer) == SI.Calculate LA.Mul);
  lemma_bin u rho (TR.times_decl integer) a b LA.Mul

(* a - b as the producer writes it. *)
let lemma_diff (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope) (a b:expr)
  : Lemma (requires D.scoped iscope (diff a b) /\ D.scoped iscope (times m1 b))
          (ensures iv u rho (diff a b) == iv u rho a - iv u rho b) =
  lemma_plus u rho a (times m1 b);
  lemma_times u rho m1 b;
  assert_norm (AR.int_numeral (-1) m1);
  lemma_num u rho (-1) m1

(* Every shape below is well sorted at the scope [d; x]. *)
let scoped_shapes () : Lemma (
    D.scoped iscope vx /\ D.scoped iscope vd /\ D.scoped iscope zero /\ D.scoped iscope m1 /\ D.scoped iscope two /\
    D.scoped iscope (rem vx vd) /\ D.scoped iscope (quot vx vd) /\ D.scoped iscope (diff (rem vx vd) vd) /\
    D.scoped iscope (times m1 vd) /\ D.scoped iscope (plus (rem vx vd) vd)) =
  assert_norm (
    D.scoped iscope vx /\ D.scoped iscope vd /\ D.scoped iscope zero /\ D.scoped iscope m1 /\ D.scoped iscope two /\
    D.scoped iscope (rem vx vd) /\ D.scoped iscope (quot vx vd) /\ D.scoped iscope (diff (rem vx vd) vd) /\
    D.scoped iscope (times m1 vd) /\ D.scoped iscope (plus (rem vx vd) vd))

(* The values of the shared pieces, at x = xv and d = dv, dv <> 0. *)
let lemma_pieces (u:TR.uninterpreted) (xv dv:int)
  : Lemma (requires dv <> 0)
          (ensures (let rho = env2 u xv dv in
                    iv u rho vx == xv /\ iv u rho vd == dv /\ iv u rho zero == 0 /\ iv u rho m1 == (-1) /\
                    iv u rho (rem vx vd) == DV.remainder_of xv dv /\
                    iv u rho (quot vx vd) == DV.quotient_of xv dv /\
                    iv u rho (diff (rem vx vd) vd) == DV.remainder_of xv dv - dv /\
                    iv u rho (plus (rem vx vd) vd) == DV.remainder_of xv dv + dv)) =
  let rho = env2 u xv dv in
  scoped_shapes ();
  lemma_vars u xv dv;
  assert_norm (AR.int_numeral 0 zero /\ AR.int_numeral (-1) m1);
  lemma_num u rho 0 zero;
  lemma_num u rho (-1) m1;
  lemma_rem_nonzero u rho vx vd;
  lemma_quot_nonzero u rho vx vd;
  lemma_diff u rho (rem vx vd) vd;
  lemma_plus u rho (rem vx vd) vd

(* A literal true or false, by the value of its operands. *)
let lit_ge (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope) (a b:expr)
  : Lemma (requires D.scoped iscope (ge a b) /\ get_sort a == integer)
          (ensures tv u rho (ge a b) <==> iv u rho b <= iv u rho a) =
  assert_norm (LA.comparison (ge a b) == Some (LA.Ge, a, b));
  lemma_cmp u rho (ge a b) LA.Ge a b

let lit_le (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope) (a b:expr)
  : Lemma (requires D.scoped iscope (le a b) /\ get_sort a == integer)
          (ensures tv u rho (le a b) <==> iv u rho a <= iv u rho b) =
  assert_norm (LA.comparison (le a b) == Some (LA.Le, a, b));
  lemma_cmp u rho (le a b) LA.Le a b

let lit_eq (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) iscope) (a b:expr)
  : Lemma (requires D.scoped iscope (eq a b) /\ get_sort a == integer)
          (ensures tv u rho (eq a b) <==> iv u rho a == iv u rho b) =
  assert_norm (LA.comparison (eq a b) == Some (LA.Eq, a, b));
  lemma_cmp u rho (eq a b) LA.Eq a b

(* --- the unguarded and the wrongly guarded mod ---------------------------- *)

(* No guard: mod x 0 answers -1 in the adversarial root model. *)
let o4_unguarded (u:TR.uninterpreted)
  : Lemma (not (tv u (env2 u 5 0) (ge (rem vx vd) zero))) =
  let rho = env2 u 5 0 in
  scoped_shapes ();
  lemma_vars u 5 0;
  assert_norm (AR.int_numeral 0 zero);
  lemma_num u rho 0 zero;
  lemma_rem_zero u rho vx vd;
  lit_ge u rho (rem vx vd) zero

(* The guard on x instead of d: x = 5 is not 0, d = 0, mod 5 0 = -1. *)
let o4_guard_on_x (u:TR.uninterpreted)
  : Lemma (not (tv u (env2 u 5 0) (or2 (eq vx zero) (ge (rem vx vd) zero)))) =
  let rho = env2 u 5 0 in
  scoped_shapes ();
  lemma_vars u 5 0;
  assert_norm (AR.int_numeral 0 zero);
  lemma_num u rho 0 zero;
  lemma_rem_zero u rho vx vd;
  assert_norm (D.scoped iscope (eq vx zero) /\ D.scoped iscope (ge (rem vx vd) zero) /\
               D.scoped iscope (or2 (eq vx zero) (ge (rem vx vd) zero)));
  lit_eq u rho vx zero;
  lit_ge u rho (rem vx vd) zero;
  lemma_or2_false u rho (eq vx zero) (ge (rem vx vd) zero)

(* The positive-divisor bound under the negative guard: d = -2, x = 0 (mod = 0,
   0 - (-2) = 2 > -1). *)
let o4_wrong_guard_positive_bound (u:TR.uninterpreted)
  : Lemma (not (tv u (env2 u 0 (-2)) (or2 (ge vd zero) (le (diff (rem vx vd) vd) m1)))) =
  let rho = env2 u 0 (-2) in
  lemma_pieces u 0 (-2);
  assert_norm (DV.remainder_of 0 (-2) == 0);
  assert_norm (D.scoped iscope (ge vd zero) /\ D.scoped iscope (le (diff (rem vx vd) vd) m1) /\
               D.scoped iscope (or2 (ge vd zero) (le (diff (rem vx vd) vd) m1)));
  lit_ge u rho vd zero;
  lit_le u rho (diff (rem vx vd) vd) m1;
  lemma_or2_false u rho (ge vd zero) (le (diff (rem vx vd) vd) m1)

(* The negative-divisor bound under the positive guard: d = 3, x = 0 (0 + 3 > -1). *)
let o4_wrong_guard_negative_bound (u:TR.uninterpreted)
  : Lemma (not (tv u (env2 u 0 3) (or2 (le vd zero) (le (plus (rem vx vd) vd) m1)))) =
  let rho = env2 u 0 3 in
  lemma_pieces u 0 3;
  assert_norm (DV.remainder_of 0 3 == 0);
  assert_norm (D.scoped iscope (le vd zero) /\ D.scoped iscope (le (plus (rem vx vd) vd) m1) /\
               D.scoped iscope (or2 (le vd zero) (le (plus (rem vx vd) vd) m1)));
  lit_le u rho vd zero;
  lit_le u rho (plus (rem vx vd) vd) m1;
  lemma_or2_false u rho (le vd zero) (le (plus (rem vx vd) vd) m1)

(* The bound -2 instead of -1: d = 1, x = 0 (0 - 1 = -1 > -2). *)
let o4_wrong_bound (u:TR.uninterpreted)
  : Lemma (not (tv u (env2 u 0 1) (or2 (le vd zero) (le (diff (rem vx vd) vd) (inum (-2)))))) =
  let rho = env2 u 0 1 in
  lemma_pieces u 0 1;
  assert_norm (DV.remainder_of 0 1 == 0);
  assert_norm (AR.int_numeral (-2) (inum (-2)));
  lemma_num u rho (-2) (inum (-2));
  assert_norm (D.scoped iscope (inum (-2)) /\ D.scoped iscope (le vd zero) /\
               D.scoped iscope (le (diff (rem vx vd) vd) (inum (-2))) /\
               D.scoped iscope (or2 (le vd zero) (le (diff (rem vx vd) vd) (inum (-2)))));
  lit_le u rho vd zero;
  lit_le u rho (diff (rem vx vd) vd) (inum (-2));
  lemma_or2_false u rho (le vd zero) (le (diff (rem vx vd) vd) (inum (-2)))

(* mod and div exchanged: x = -5, d = 1, div = -5 < 0. *)
let o4_div_for_mod (u:TR.uninterpreted)
  : Lemma (not (tv u (env2 u (-5) 1) (or2 (eq vd zero) (ge (quot vx vd) zero)))) =
  let rho = env2 u (-5) 1 in
  lemma_pieces u (-5) 1;
  assert_norm (DV.quotient_of (-5) 1 == (-5));
  assert_norm (D.scoped iscope (eq vd zero) /\ D.scoped iscope (ge (quot vx vd) zero) /\
               D.scoped iscope (or2 (eq vd zero) (ge (quot vx vd) zero)));
  lit_eq u rho vd zero;
  lit_ge u rho (quot vx vd) zero;
  lemma_or2_false u rho (eq vd zero) (ge (quot vx vd) zero)

(* The decomposition with the remainder doubled: x = 1, d = 2 (1 div 2 = 0, 1 mod 2 = 1,
   0 + 2*1 = 2 <> 1). *)
let o4_wrong_decomposition (u:TR.uninterpreted)
  : Lemma (not (tv u (env2 u 1 2)
                  (or2 (eq vd zero) (eq vx (plus (times vd (quot vx vd)) (times two (rem vx vd))))))) =
  let rho = env2 u 1 2 in
  lemma_pieces u 1 2;
  assert_norm (DV.quotient_of 1 2 == 0 /\ DV.remainder_of 1 2 == 1);
  let sum = plus (times vd (quot vx vd)) (times two (rem vx vd)) in
  assert_norm (D.scoped iscope (times vd (quot vx vd)) /\ D.scoped iscope (times two (rem vx vd)) /\
               D.scoped iscope sum /\ D.scoped iscope (eq vx sum) /\ D.scoped iscope (eq vd zero) /\
               D.scoped iscope (or2 (eq vd zero) (eq vx sum)));
  assert_norm (AR.int_numeral 2 two);
  lemma_num u rho 2 two;
  lemma_times u rho vd (quot vx vd);
  lemma_times u rho two (rem vx vd);
  lemma_plus u rho (times vd (quot vx vd)) (times two (rem vx vd));
  lit_eq u rho vd zero;
  lit_eq u rho vx sum;
  lemma_or2_false u rho (eq vd zero) (eq vx sum)

(* The decomposition over div d x: x = 3, d = 2 (2 div 3 = 0, 3 mod 2 = 1; 0 + 1 <> 3). *)
let o4_swapped_operands (u:TR.uninterpreted)
  : Lemma (not (tv u (env2 u 3 2)
                  (or2 (eq vd zero) (eq vx (plus (times vd (quot vd vx)) (rem vx vd)))))) =
  let rho = env2 u 3 2 in
  lemma_pieces u 3 2;
  assert_norm (DV.remainder_of 3 2 == 1);
  assert_norm (D.scoped iscope (quot vd vx));
  lemma_quot_nonzero u rho vd vx;
  assert_norm (DV.quotient_of 2 3 == 0);
  let sum = plus (times vd (quot vd vx)) (rem vx vd) in
  assert_norm (D.scoped iscope (times vd (quot vd vx)) /\ D.scoped iscope sum /\ D.scoped iscope (eq vx sum) /\
               D.scoped iscope (eq vd zero) /\ D.scoped iscope (or2 (eq vd zero) (eq vx sum)));
  lemma_times u rho vd (quot vd vx);
  lemma_plus u rho (times vd (quot vd vx)) (rem vx vd);
  lit_eq u rho vd zero;
  lit_eq u rho vx sum;
  lemma_or2_false u rho (eq vd zero) (eq vx sum)

(* The positive instance of a negative divisor, x = 7, d = -2 (7 mod -2 = 1): the
   guard d <= 0 holds, the lower bound mod >= 0 and the negative-divisor bound
   mod + d <= -1 hold, and the positive-divisor bound mod - d <= -1 does not (its
   guard is what makes it valid). *)
let o4_positive_instance (u:TR.uninterpreted)
  : Lemma (let rho = env2 u 7 (-2) in
           tv u rho (ge (rem vx vd) zero) /\
           tv u rho (le (plus (rem vx vd) vd) m1) /\
           not (tv u rho (le (diff (rem vx vd) vd) m1)) /\ tv u rho (le vd zero)) =
  let rho = env2 u 7 (-2) in
  lemma_pieces u 7 (-2);
  assert_norm (DV.remainder_of 7 (-2) == 1);
  assert_norm (D.scoped iscope (ge (rem vx vd) zero) /\ D.scoped iscope (le (plus (rem vx vd) vd) m1) /\
               D.scoped iscope (le (diff (rem vx vd) vd) m1) /\ D.scoped iscope (le vd zero));
  lit_ge u rho (rem vx vd) zero;
  lit_le u rho (plus (rem vx vd) vd) m1;
  lit_le u rho (diff (rem vx vd) vd) m1;
  lit_le u rho vd zero

(* The retained countermodel of the previous class (Z3SortedDivisionRoot.mod_minus_one: the
   standard root with mod answering -1) gives mod 0 1 the value -1, so d = 0 \/ mod x d >= 0
   was false there at x = 0, d = 1 (both literals false); every root model of the corrected
   class gives mod 0 1 the value 0 (the Euclidean remainder), whatever the free choices. *)
let lemma_old_mod_value (u:TR.uninterpreted) (uf:TR.symbols u esch) (a b:expr)
  : Lemma (requires D.scoped [] (rem a b))
          (ensures AR.integer esch (TR.booleans u) (SR.root_scalars u) (DR.mod_minus_one u esch uf) []
                     (T.empty_environment (S.signature esch)) (rem a b) == (-1)) =
  let rho = T.empty_environment (S.signature esch) in
  let other = DR.mod_minus_one u esch uf in
  DV.lemma_classify_canonical ();
  DV.lemma_evaluate_division_at esch (TR.booleans u) (SR.root_scalars u) other [] rho DV.remainder_decl [a; b];
  let va = T.evaluate_at esch (TR.booleans u) (SR.root_scalars u) other [] rho a in
  let vb = T.evaluate_at esch (TR.booleans u) (SR.root_scalars u) other [] rho b in
  let xs = T.evaluate_arguments_at esch (TR.booleans u) (SR.root_scalars u) other [] rho [a; b]
             DV.remainder_decl.domain in
  assert_norm (T.evaluate_arguments_at esch (TR.booleans u) (SR.root_scalars u) other [] rho [a; b]
                 [integer; integer] == [va; vb]);
  DV.lemma_division_application esch (TR.booleans u) (SR.root_scalars u) other DV.remainder_decl xs;
  DR.lemma_remainder_classify esch DV.remainder_decl

let o4_previous_class_value (u:TR.uninterpreted) (uf:TR.symbols u esch)
  : Lemma (AR.integer esch (TR.booleans u) (SR.root_scalars u) (DR.mod_minus_one u esch uf) []
             (T.empty_environment (S.signature esch)) (rem zero (inum 1)) == (-1)) =
  assert_norm (D.scoped [] (rem zero (inum 1)));
  lemma_old_mod_value u uf zero (inum 1)

let o4_corrected_class_value (u:TR.uninterpreted) (i:TR.interp u esch)
  : Lemma (requires TR.root_model u esch i)
          (ensures AR.integer esch (TR.booleans u) (SR.root_scalars u) i []
                     (T.empty_environment (S.signature esch)) (rem zero (inum 1)) == 0) =
  let rho = T.empty_environment (S.signature esch) in
  DR.lemma_root_division_laws u esch i;
  DV.lemma_classify_canonical ();
  assert_norm (D.scoped [] (rem zero (inum 1)) /\ D.scoped [] zero /\ D.scoped [] (inum 1));
  assert_norm (AR.int_numeral 0 zero /\ AR.int_numeral 1 (inum 1));
  AR.lemma_int_numeral esch (TR.booleans u) (SR.root_scalars u) i [] rho 0 zero;
  AR.lemma_int_numeral esch (TR.booleans u) (SR.root_scalars u) i [] rho 1 (inum 1);
  DV.lemma_remainder_at esch (TR.booleans u) (SR.root_scalars u) i [] rho DV.remainder_decl zero (inum 1);
  assert_norm (DV.remainder_of 0 1 == 0)
