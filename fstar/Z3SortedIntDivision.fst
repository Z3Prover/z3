module Z3SortedIntDivision

(* Sorted Int division laws (run e78cd96c, the guarded Int div/mod axioms of
   the Pulse arithmetic lemmas).

   The canonical Int `div` and `mod` (SMT-LIB Euclidean division: for a
   nonzero divisor y, x = y * (x div y) + (x mod y) and 0 <= x mod y < |y|)
   are classified here and nowhere else of the Sorted layers: Z3SortedInteger
   and Z3SortedSemantics pass them to `other` untouched, exactly like the
   Real operators of Z3SortedReal. The laws are a hypothesis about that
   `other` interpretation, stated over the SAME Sorted interpretation and the
   same Int carrier (`model.T.integers`) as every other Int law:

     division_model s bc model other
       = for every classified div/mod application with a nonzero divisor the
         value is the F* quotient (x / y) resp. remainder (x % y) of the
         arguments' Int values.

   A zero divisor has NO law: x div 0 and x mod 0 stay free, argument-
   dependent choices of `other`, as at Real. So nothing here proves an
   identity between a division and its `div0`/`mod0` alias, and a clause that
   is only valid by the guard (d = 0, d <= 0, d >= 0) is only provable under
   the corresponding nonzero divisor.

   Derivation: Z3SortedDivisionRoot derives `division_model` from R2 of ANY
   model of the typed root contract (TR.root_model; the root classes IntDiv
   and IntMod of Z3TypedRoot), and shows the standard root model satisfies
   it jointly with R1-R6 and the Real laws; no legacy division_model of
   Z3IntegerDivision is used. The model-contract change (the root class now
   fixes div/mod at a nonzero divisor) is documented in Z3TypedRoot. *)

open Z3AstTheory
open Z3ValueTheory
module A = Z3LinearArithmeticAst
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module I = Z3SortedInteger
module AR = Z3SortedArithmetic
module D = Z3Definitions
module IDV = Z3IntegerDivision
module R = Z3ResolutionProofTheory
module L = FStar.List.Tot

(* The canonical Int division declarations: exact name, kind tag, domain,
   range and parameters (what Z3NativeProof.marshal_declaration builds for
   Z3's `div` and `mod`). Everything else (another name or tag, a div over
   Real, a sort merely named Int, a parameter) is `Other`. *)
type operation =
  | Quotient
  | Remainder
  | Other

let operation_typed (f:func_decl) (op:operation) : bool =
  match op with
  | Quotient | Remainder -> f.domain = [A.int_s; A.int_s] && f.range = A.int_s
  | Other -> true

let canonical (f:func_decl) (remainder:bool) : bool =
  f.decl_name = (if remainder then "mod" else "div") &&
  f.interp = Some (if remainder then IDV.op_mod else IDV.op_idiv) &&
  f.domain = [A.int_s; A.int_s] && f.range = A.int_s && f.int_params = []

let classify (f:func_decl) : op:operation{operation_typed f op} =
  if canonical f false then Quotient
  else if canonical f true then Remainder
  else Other

(* The two canonical declarations, as the checkers write them. *)
let quotient_decl : func_decl = {
  decl_name = "div"; domain = [A.int_s; A.int_s]; range = A.int_s;
  interp = Some IDV.op_idiv; int_params = [];
}

let remainder_decl : func_decl = {
  decl_name = "mod"; domain = [A.int_s; A.int_s]; range = A.int_s;
  interp = Some IDV.op_mod; int_params = [];
}

let lemma_classify_canonical ()
  : Lemma (classify quotient_decl == Quotient /\ classify remainder_decl == Remainder) =
  assert_norm (classify quotient_decl == Quotient);
  assert_norm (classify remainder_decl == Remainder)

(* The meaning of a nonzero divisor: F*'s own Euclidean / and % on int (the
   SMT-LIB div and mod), as total functions (the zero divisor is never
   consulted: it carries no law). *)
let quotient_of (x y:int) : int = if y = 0 then 0 else x / y
let remainder_of (x y:int) : int = if y = 0 then 0 else x % y

(* The Euclidean facts the guarded clauses read. *)
let lemma_euclid (x d:int)
  : Lemma (requires d <> 0)
          (ensures x == d * quotient_of x d + remainder_of x d /\
                   0 <= remainder_of x d /\
                   (d > 0 ==> remainder_of x d <= d - 1) /\
                   (d < 0 ==> remainder_of x d <= (-d) - 1)) = ()

(* ---------------------------------------------------------------------- *)
(* The laws, over the Sorted interpretation                                 *)
(* ---------------------------------------------------------------------- *)

let division_meaning (#base:sort -> Type0) (s:S.checked_schema) (integers:I.carrier base)
                     (f:func_decl) (xs:V.arguments base (S.signature s) f.domain)
                     (v:V.value base (S.signature s) f.range) : prop =
  match classify f with
  | Quotient ->
    (match xs with
     | [x; y] -> ~(I.number s integers y == 0) ==>
                 I.number s integers v == quotient_of (I.number s integers x) (I.number s integers y)
     | _ -> True)
  | Remainder ->
    (match xs with
     | [x; y] -> ~(I.number s integers y == 0) ==>
                 I.number s integers v == remainder_of (I.number s integers x) (I.number s integers y)
     | _ -> True)
  | Other -> True

let division_laws (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (model:T.scalar_model base) (other:V.interpretation base (S.signature s)) : prop =
  forall (f:func_decl) (xs:V.arguments base (S.signature s) f.domain).
    division_meaning s model.T.integers f xs (T.application s bc model other f xs)

(* ---------------------------------------------------------------------- *)
(* Classified division operators are theory operators                        *)
(* ---------------------------------------------------------------------- *)

let theory_tag (f:func_decl) : bool =
  f.interp = Some IDV.op_idiv || f.interp = Some IDV.op_mod

let lemma_classified_tag (f:func_decl)
  : Lemma (requires ~(Other? (classify f))) (ensures theory_tag f) = ()

let lemma_classified_not_registered (s:S.checked_schema) (f:func_decl)
  : Lemma (requires ~(Other? (classify f))) (ensures not (L.mem f (S.signature s))) =
  lemma_classified_tag f;
  if L.mem f (S.signature s) then T.lemma_registered_constructor s f

let lemma_classified_not_core (f:func_decl)
  : Lemma (requires ~(Other? (classify f)))
          (ensures T.classify f == T.Other /\ I.classify f == I.Other) =
  lemma_classified_tag f

let rec lemma_no_recognizer (f:func_decl) (cs:list S.constructor_case)
  : Lemma (requires theory_tag f) (ensures None? (S.find_recognizer f cs)) (decreases cs) =
  match cs with [] -> () | _ :: rest -> lemma_no_recognizer f rest

let rec lemma_no_accessor (f:func_decl) (cs:list S.constructor_case)
  : Lemma (requires theory_tag f) (ensures None? (S.find_accessor f cs)) (decreases cs) =
  match cs with [] -> () | _ :: rest -> lemma_no_accessor f rest

(* The Sorted layers pass every classified division operator to `other`. *)
let lemma_division_application (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                               (f:func_decl) (xs:V.arguments base (S.signature s) f.domain)
  : Lemma (requires ~(Other? (classify f)))
          (ensures T.application s bc model other f xs == other.V.application f xs) =
  lemma_classified_not_core f;
  lemma_classified_not_registered s f;
  lemma_no_recognizer f s.S.cases;
  lemma_no_accessor f s.S.cases

(* An interpretation that agrees with `other` on every classified division
   operator inherits the division laws (the model overrides of the epsilon and
   dependent-Skolem routes only change uninterpreted witness symbols). *)
let division_agreement (#base:sort -> Type0) (s:S.checked_schema)
                       (other newer:V.interpretation base (S.signature s)) : prop =
  forall (f:func_decl) (xs:V.arguments base (S.signature s) f.domain).
    ~(Other? (classify f)) ==> newer.V.application f xs == other.V.application f xs

let lemma_division_laws_transfer (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                 (model:T.scalar_model base)
                                 (other newer:V.interpretation base (S.signature s))
  : Lemma (requires division_laws s bc model other /\ division_agreement s other newer)
          (ensures division_laws s bc model newer) =
  introduce forall (f:func_decl) (xs:V.arguments base (S.signature s) f.domain).
    division_meaning s model.T.integers f xs (T.application s bc model newer f xs)
  with (
    if Other? (classify f) then ()
    else (
      lemma_division_application s bc model other f xs;
      lemma_division_application s bc model newer f xs;
      assert (division_meaning s model.T.integers f xs (T.application s bc model other f xs))))

(* ---------------------------------------------------------------------- *)
(* The canonical operators at every scope and environment                    *)
(* ---------------------------------------------------------------------- *)

let lemma_evaluate_division_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                               (scope:list sort) (rho:V.environment base (S.signature s) scope)
                               (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped scope (App f args) /\ ~(Other? (classify f)))
          (ensures T.evaluate_at s bc model other scope rho (App f args) ==
                   T.application s bc model other f
                     (T.evaluate_arguments_at s bc model other scope rho args f.domain)) =
  lemma_classified_not_registered s f

(* The division law of one application div a b at an arbitrary scope and
   environment: its operands are Int terms of the scope, and a nonzero value
   of b gives the quotient of the operands' values. *)
let lemma_quotient_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (scope:list sort) (rho:V.environment base (S.signature s) scope)
                      (f:func_decl) (a b:expr)
  : Lemma (requires division_laws s bc model other /\ D.scoped scope (App f [a; b]) /\
                    classify f == Quotient)
          (ensures D.scoped scope a /\ D.scoped scope b /\ get_sort a == A.int_s /\ get_sort b == A.int_s /\
                   get_sort (App f [a; b]) == A.int_s /\
                   (~(AR.integer s bc model other scope rho b == 0) ==>
                    AR.integer s bc model other scope rho (App f [a; b]) ==
                    quotient_of (AR.integer s bc model other scope rho a)
                                (AR.integer s bc model other scope rho b))) =
  V.lemma_sort_eq (get_sort a) A.int_s;
  V.lemma_sort_eq (get_sort b) A.int_s;
  lemma_evaluate_division_at s bc model other scope rho f [a; b];
  let va = T.evaluate_at s bc model other scope rho a in
  let vb = T.evaluate_at s bc model other scope rho b in
  let xs = T.evaluate_arguments_at s bc model other scope rho [a; b] f.domain in
  assert_norm (T.evaluate_arguments_at s bc model other scope rho [a; b] [A.int_s; A.int_s] == [va; vb]);
  assert (xs == [va; vb]);
  assert (division_meaning s model.T.integers f xs (T.application s bc model other f xs))

let lemma_remainder_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (f:func_decl) (a b:expr)
  : Lemma (requires division_laws s bc model other /\ D.scoped scope (App f [a; b]) /\
                    classify f == Remainder)
          (ensures D.scoped scope a /\ D.scoped scope b /\ get_sort a == A.int_s /\ get_sort b == A.int_s /\
                   get_sort (App f [a; b]) == A.int_s /\
                   (~(AR.integer s bc model other scope rho b == 0) ==>
                    AR.integer s bc model other scope rho (App f [a; b]) ==
                    remainder_of (AR.integer s bc model other scope rho a)
                                 (AR.integer s bc model other scope rho b))) =
  V.lemma_sort_eq (get_sort a) A.int_s;
  V.lemma_sort_eq (get_sort b) A.int_s;
  lemma_evaluate_division_at s bc model other scope rho f [a; b];
  let va = T.evaluate_at s bc model other scope rho a in
  let vb = T.evaluate_at s bc model other scope rho b in
  let xs = T.evaluate_arguments_at s bc model other scope rho [a; b] f.domain in
  assert_norm (T.evaluate_arguments_at s bc model other scope rho [a; b] [A.int_s; A.int_s] == [va; vb]);
  assert (xs == [va; vb]);
  assert (division_meaning s model.T.integers f xs (T.application s bc model other f xs))

(* ---------------------------------------------------------------------- *)
(* Atoms of the guarded clauses                                              *)
(* ---------------------------------------------------------------------- *)

(* x and d of a canonical div x d / mod x d (by declaration identity only). *)
let quotient_arguments (e:expr) : option (expr & expr) =
  match e with
  | App f [x; d] -> if classify f = Quotient then Some (x, d) else None
  | _ -> None

let remainder_arguments (e:expr) : option (expr & expr) =
  match e with
  | App f [x; d] -> if classify f = Remainder then Some (x, d) else None
  | _ -> None

(* The guard literal d = 0: the canonical Int equality of d and the canonical
   Int numeral 0, in this orientation. *)
let zero_guard (d lit:expr) : bool =
  match lit with
  | App f [a; z] -> f = R.eq_decl A.int_s && a = d && AR.int_numeral 0 z
  | _ -> false

(* The guard literals d <= 0 (rel = Le) and d >= 0 (rel = Ge): a canonical
   Int comparison of d against the canonical Int numeral 0. *)
let sign_guard (rel:A.relation) (d lit:expr) : bool =
  match A.comparison lit with
  | Some (r, a, z) ->
    (rel = A.Le || rel = A.Ge) && r = rel && get_sort a = A.int_s && a = d && AR.int_numeral 0 z
  | None -> false

let lemma_zero_guard (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (d lit:expr)
  : Lemma (requires D.scoped scope lit /\ zero_guard d lit)
          (ensures D.scoped scope d /\ get_sort d == A.int_s /\
                   (T.truth_at s bc model other scope rho lit <==>
                    AR.integer s bc model other scope rho d == 0)) =
  match lit with
  | App f [a; z] ->
    V.lemma_sort_eq (get_sort a) A.int_s;
    V.lemma_sort_eq (get_sort z) A.int_s;
    AR.lemma_int_numeral s bc model other scope rho 0 z;
    T.lemma_equality_at s bc model other scope rho a z;
    AR.lemma_integer_equality s bc model other scope rho a z
  | _ -> ()

let lemma_sign_guard (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (rel:A.relation) (d lit:expr)
  : Lemma (requires D.scoped scope lit /\ sign_guard rel d lit)
          (ensures D.scoped scope d /\ get_sort d == A.int_s /\
                   (T.truth_at s bc model other scope rho lit <==>
                    I.compare rel (AR.integer s bc model other scope rho d) 0)) =
  match A.comparison lit with
  | Some (r, a, z) ->
    AR.lemma_int_comparison s bc model other scope rho lit r a z;
    AR.lemma_int_numeral s bc model other scope rho 0 z
  | None -> ()

(* The values of div x d and mod x d under the laws, whatever the scope. *)
let lemma_quotient_arguments (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (scope:list sort) (rho:V.environment base (S.signature s) scope)
                             (e x d:expr)
  : Lemma (requires division_laws s bc model other /\ D.scoped scope e /\ quotient_arguments e == Some (x, d))
          (ensures D.scoped scope x /\ D.scoped scope d /\ get_sort x == A.int_s /\ get_sort d == A.int_s /\
                   get_sort e == A.int_s /\
                   (~(AR.integer s bc model other scope rho d == 0) ==>
                    AR.integer s bc model other scope rho e ==
                    quotient_of (AR.integer s bc model other scope rho x) (AR.integer s bc model other scope rho d))) =
  match e with
  | App f [a; b] -> lemma_quotient_at s bc model other scope rho f a b
  | _ -> ()

let lemma_remainder_arguments (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (scope:list sort) (rho:V.environment base (S.signature s) scope)
                              (e x d:expr)
  : Lemma (requires division_laws s bc model other /\ D.scoped scope e /\ remainder_arguments e == Some (x, d))
          (ensures D.scoped scope x /\ D.scoped scope d /\ get_sort x == A.int_s /\ get_sort d == A.int_s /\
                   get_sort e == A.int_s /\
                   (~(AR.integer s bc model other scope rho d == 0) ==>
                    AR.integer s bc model other scope rho e ==
                    remainder_of (AR.integer s bc model other scope rho x) (AR.integer s bc model other scope rho d))) =
  match e with
  | App f [a; b] -> lemma_remainder_at s bc model other scope rho f a b
  | _ -> ()
