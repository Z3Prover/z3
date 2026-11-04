module Z3SortedRealRoot

open Z3AstTheory
open Z3ValueTheory
open FStar.Real
module A = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed
module P = Z3LinearArithmeticTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module I = Z3SortedInteger
module D = Z3Definitions
module L = FStar.List.Tot
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module RL = Z3SortedReal
module AR = Z3SortedArithmetic

(* ---------------------------------------------------------------------- *)
(* The root Real carrier: the identity on FStar.Real.real                   *)
(* ---------------------------------------------------------------------- *)

let root_reals (u:TR.uninterpreted) : RL.carrier (TR.carrier u) = {
  RL.real_of = (fun (x:TR.carrier u A.real_s) -> (x <: real));
  RL.real_injective = ();
}

(* ---------------------------------------------------------------------- *)
(* Classifier agreement with the root classification at Real               *)
(* ---------------------------------------------------------------------- *)

let real_op (op:RL.operation) : TR.theory_op =
  match op with
  | RL.Numeral n d -> TR.Numeral TR.real_s n d
  | RL.Calculate o -> TR.Arith TR.real_s o
  | RL.Divide -> TR.Divide
  | RL.ToReal -> TR.ToReal
  | RL.Compare r -> TR.Compare TR.real_s r
  | RL.Other -> TR.Other

let real_part (op:TR.theory_op) : TR.theory_op =
  match op with
  | TR.Numeral s _ _ | TR.Arith s _ | TR.Compare s _ -> if s = TR.real_s then op else TR.Other
  | TR.Divide | TR.ToReal -> op
  | _ -> TR.Other

let rec lemma_real_sorts (ss:list sort)
  : Lemma (TR.same_sorts TR.real_s ss == RL.real_sorts ss) (decreases ss) =
  match ss with [] -> () | _ :: rest -> lemma_real_sorts rest

let lemma_numeric_agreement (sch:S.checked_schema) (f:func_decl)
  : Lemma (requires RL.real_primitive sch)
          (ensures real_op (RL.classify f) == real_part (TR.numeric (S.signature sch) f)) =
  SR.lemma_int_primitive sch;
  lemma_real_sorts f.domain

let lemma_real_classify (sch:S.checked_schema) (f:func_decl)
  : Lemma (requires RL.real_primitive sch /\ ~(RL.Other? (RL.classify f)))
          (ensures TR.classify (S.signature sch) f == real_op (RL.classify f)) =
  RL.lemma_classified_not_core f;
  SR.lemma_core_agreement f;
  lemma_numeric_agreement sch f

(* ---------------------------------------------------------------------- *)
(* Value bridges                                                            *)
(* ---------------------------------------------------------------------- *)

let lemma_real_value (#u:TR.uninterpreted) (sch:S.checked_schema{RL.real_primitive sch})
                     (v:TR.tvalue u sch A.real_s)
  : Lemma (RL.real_value sch (root_reals u) v == TR.scalar #u #(S.signature sch) A.real_s v) =
  match v with
  | V.Scalar _ _ -> ()
  | V.Constructor f _ -> TR.lemma_registered (S.signature sch) f

let rec lemma_real_values (#u:TR.uninterpreted) (sch:S.checked_schema{RL.real_primitive sch})
                          (ss:list sort{RL.real_sorts ss /\ TR.same_sorts TR.real_s ss})
                          (xs:TR.targuments u sch ss)
  : Lemma (ensures RL.real_values sch (root_reals u) ss xs == TR.reals sch ss xs) (decreases ss) =
  match ss, xs with
  | [], [] -> ()
  | _ :: rest, x :: tail -> lemma_real_value sch x; lemma_real_values sch rest tail
  | _, _ -> ()

let rec lemma_numeric_sum (xs:list real) : Lemma (E.numeric_sum xs == TR.rsum xs) (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_numeric_sum rest

let rec lemma_numeric_product (xs:list real) : Lemma (E.numeric_product xs == TR.rproduct xs) (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_numeric_product rest

let lemma_calculate (o:A.operation) (xs:list real)
  : Lemma (RL.calculate o xs == TR.rcalculate o xs) =
  lemma_numeric_sum xs;
  lemma_numeric_product xs;
  match xs with _ :: rest -> lemma_numeric_sum rest | [] -> ()

let lemma_quotient (x y:real)
  : Lemma (requires ~(y == 0.0R)) (ensures (x /. y) *. y == x) = ()

(* ---------------------------------------------------------------------- *)
(* Derivation of the Sorted Real laws from R2 of ONE root model             *)
(* ---------------------------------------------------------------------- *)

let lemma_root_meaning (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                       (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires TR.root_model u sch i /\ RL.real_primitive sch)
          (ensures RL.real_meaning sch (TR.booleans u) (SR.root_integers u) (root_reals u) f xs
                     (T.application sch (TR.booleans u) (SR.root_scalars u) i f xs)) =
  SR.lemma_application_agreement u sch i f xs;
  match RL.classify f with
  | RL.Other -> ()
  | RL.Numeral n d ->
    lemma_real_classify sch f;
    TR.lemma_operator i f xs;
    lemma_real_value sch (i.V.application f xs)
  | RL.Calculate o ->
    lemma_real_classify sch f;
    lemma_real_sorts f.domain;
    TR.lemma_operator i f xs;
    lemma_real_value sch (i.V.application f xs);
    lemma_real_values sch f.domain xs;
    lemma_calculate o (TR.reals sch f.domain xs)
  | RL.Divide ->
    lemma_real_classify sch f;
    (match xs with
     | [x; y] ->
       lemma_real_value sch x;
       lemma_real_value sch y;
       lemma_real_value sch (i.V.application f [x; y]);
       let a = TR.scalar #u #(S.signature sch) A.real_s x in
       let b = TR.scalar #u #(S.signature sch) A.real_s y in
       if TR.decide (b == 0.0R) then ()
       else (TR.lemma_operator i f [x; y]; lemma_quotient a b)
     | _ -> ())
  | RL.ToReal ->
    lemma_real_classify sch f;
    (match xs with
     | [x] ->
       TR.lemma_operator i f [x];
       lemma_real_value sch (i.V.application f [x]);
       SR.lemma_number sch x
     | _ -> ())
  | RL.Compare r ->
    lemma_real_classify sch f;
    (match xs with
     | [x; y] ->
       TR.lemma_operator i f [x; y];
       lemma_real_value sch x;
       lemma_real_value sch y;
       SR.lemma_truth_value sch (i.V.application f [x; y])
     | _ -> ())

(* For EVERY root model i (R1-R6) over a checked schema that does not register
   Real as a datatype sort, the Sorted interpretation over the root scalars on
   top of i satisfies the Sorted Real laws with the identity Real carrier. *)
let lemma_root_real_laws (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
  : Lemma (requires TR.root_model u sch i /\ RL.real_primitive sch)
          (ensures RL.real_laws sch (TR.booleans u) (SR.root_scalars u) i (root_reals u)) =
  introduce forall (f:func_decl) (xs:TR.targuments u sch f.domain).
    RL.real_meaning sch (TR.booleans u) (SR.root_integers u) (root_reals u) f xs
      (T.application sch (TR.booleans u) (SR.root_scalars u) i f xs)
  with lemma_root_meaning u sch i f xs

(* The kernel-facing existential hypothesis, discharged by the identity
   carrier in every root model. *)
let lemma_root_real_model (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
  : Lemma (requires TR.root_model u sch i /\ RL.real_primitive sch)
          (ensures RL.real_model sch (TR.booleans u) (SR.root_scalars u) i) =
  lemma_root_real_laws u sch i

(* The Real-primitive premise is never assumed: it is part of the root's own
   support gate (TR.supported), and the typed check validates it at runtime. *)
let lemma_supported_primitive (sch:TR.supported_schema) : Lemma (RL.real_primitive sch) = ()

(* Joint realizability: the standard root model, for EVERY u and uf, satisfies
   R1-R6 and the Sorted Real laws at once. *)
let lemma_standard_real_root (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
  : Lemma (requires RL.real_primitive sch)
          (ensures TR.root_model u sch (TR.standard u sch uf) /\
                   RL.real_laws sch (TR.booleans u) (SR.root_scalars u) (TR.standard u sch uf) (root_reals u)) =
  TR.lemma_standard_root u sch uf;
  lemma_root_real_laws u sch (TR.standard u sch uf)

let lemma_real_root_inhabited (u:TR.uninterpreted) (sch:S.checked_schema)
  : Lemma (requires RL.real_primitive sch)
          (ensures exists (i:TR.interp u sch).
                     TR.root_model u sch i /\
                     RL.real_laws sch (TR.booleans u) (SR.root_scalars u) i (root_reals u)) =
  let uf : TR.symbols u sch = {
    TR.apply = (fun f _ -> S.value_inhabitant sch (TR.default_value u) f.range);
    TR.lambda = (fun bound t _ -> S.value_inhabitant sch (TR.default_value u) (ArraySort bound t));
  } in
  lemma_standard_real_root u sch uf

(* ---------------------------------------------------------------------- *)
(* A positive instance: a Real variable valued 1/2 in the standard root     *)
(* ---------------------------------------------------------------------- *)

let empty_schema : S.checked_schema =
  let s = { S.sorts = []; S.cases = [] } in
  assert_norm (S.valid s);
  s

let lemma_empty_primitive () : Lemma (RL.real_primitive empty_schema) =
  assert_norm (RL.real_primitive empty_schema)

let half : real = of_int 1 /. of_int 2

let half_environment (u:TR.uninterpreted)
  : V.environment (TR.carrier u) (S.signature empty_schema) [A.real_s] =
  lemma_empty_primitive ();
  fun (n:nat{n < 1}) -> V.Scalar A.real_s (half <: TR.carrier u A.real_s)

let x_real : expr = Var 0 A.real_s
let real_constant (n:int) (d:pos) : expr = App (RL.real_numeral_decl n d) []
let real_lt (a b:expr) : expr = App RL.real_lt_decl [a; b]
let real_le (a b:expr) : expr = App RL.real_le_decl [a; b]
let real_minus (a b:expr) : expr = App RL.real_minus_decl [a; b]

let standard_half (u:TR.uninterpreted) (uf:TR.symbols u empty_schema) : TR.interp u empty_schema =
  TR.standard u empty_schema uf

let lemma_half_value (u:TR.uninterpreted) (uf:TR.symbols u empty_schema)
  : Lemma (RL.real_at empty_schema (TR.booleans u) (SR.root_scalars u) (standard_half u uf) (root_reals u)
             [A.real_s] (half_environment u) x_real == half) =
  lemma_empty_primitive ()

let lemma_half_laws (u:TR.uninterpreted) (uf:TR.symbols u empty_schema)
  : Lemma (TR.root_model u empty_schema (standard_half u uf) /\
           RL.real_laws empty_schema (TR.booleans u) (SR.root_scalars u) (standard_half u uf) (root_reals u)) =
  lemma_empty_primitive ();
  lemma_standard_real_root u empty_schema uf

let half_truth (u:TR.uninterpreted) (uf:TR.symbols u empty_schema) (e:expr) : GTot bool =
  T.truth_at empty_schema (TR.booleans u) (SR.root_scalars u) (standard_half u uf) [A.real_s] (half_environment u) e

let half_value (u:TR.uninterpreted) (uf:TR.symbols u empty_schema) (e:expr) : GTot real =
  RL.real_at empty_schema (TR.booleans u) (SR.root_scalars u) (standard_half u uf) (root_reals u)
    [A.real_s] (half_environment u) e

let lemma_half_bounds ()
  : Lemma (of_int 0 /. of_int 1 <. half /\ half <. of_int 1 /. of_int 1 /\
           ~(half <=. (of_int 1 /. of_int 1) -. (of_int 1 /. of_int 1))) = ()

let lemma_half_constants (u:TR.uninterpreted) (uf:TR.symbols u empty_schema)
  : Lemma (half_value u uf x_real == half /\
           half_value u uf (real_constant 0 1) == of_int 0 /. of_int 1 /\
           half_value u uf (real_constant 1 1) == of_int 1 /. of_int 1) =
  lemma_half_laws u uf;
  lemma_half_value u uf;
  RL.lemma_classify_numeral 0 1;
  RL.lemma_classify_numeral 1 1;
  RL.lemma_real_numeral_at empty_schema (TR.booleans u) (SR.root_scalars u) (standard_half u uf) (root_reals u)
    [A.real_s] (half_environment u) (RL.real_numeral_decl 0 1) 0 1;
  RL.lemma_real_numeral_at empty_schema (TR.booleans u) (SR.root_scalars u) (standard_half u uf) (root_reals u)
    [A.real_s] (half_environment u) (RL.real_numeral_decl 1 1) 1 1

let lemma_half_comparison (u:TR.uninterpreted) (uf:TR.symbols u empty_schema)
                          (f:func_decl) (a b:expr) (r:A.relation)
  : Lemma (requires D.scoped [A.real_s] (App f [a; b]) /\ RL.classify f == RL.Compare r)
          (ensures half_truth u uf (App f [a; b]) <==> E.numeric_relation r (half_value u uf a) (half_value u uf b)) =
  lemma_half_laws u uf;
  RL.lemma_real_comparison_at empty_schema (TR.booleans u) (SR.root_scalars u) (standard_half u uf) (root_reals u)
    [A.real_s] (half_environment u) f a b r

(* 0 < x holds with x = 1/2. *)
let lemma_half_positive (u:TR.uninterpreted) (uf:TR.symbols u empty_schema)
  : Lemma (half_truth u uf (real_lt (real_constant 0 1) x_real) == true) =
  RL.lemma_classify_canonical ();
  assert_norm (D.scoped [A.real_s] (App RL.real_lt_decl [real_constant 0 1; x_real]));
  lemma_half_comparison u uf RL.real_lt_decl (real_constant 0 1) x_real A.Lt;
  lemma_half_constants u uf;
  lemma_half_bounds ()

(* x < 1 holds with x = 1/2. *)
let lemma_half_below_one (u:TR.uninterpreted) (uf:TR.symbols u empty_schema)
  : Lemma (half_truth u uf (real_lt x_real (real_constant 1 1)) == true) =
  RL.lemma_classify_canonical ();
  assert_norm (D.scoped [A.real_s] (App RL.real_lt_decl [x_real; real_constant 1 1]));
  lemma_half_comparison u uf RL.real_lt_decl x_real (real_constant 1 1) A.Lt;
  lemma_half_constants u uf;
  lemma_half_bounds ()

(* The Int rounding of x < 1, namely x <= 1 - 1, is false at x = 1/2. *)
let lemma_half_rounding_false (u:TR.uninterpreted) (uf:TR.symbols u empty_schema)
  : Lemma (half_truth u uf (real_le x_real (real_minus (real_constant 1 1) (real_constant 1 1))) == false) =
  RL.lemma_classify_canonical ();
  let one_minus_one = real_minus (real_constant 1 1) (real_constant 1 1) in
  assert_norm (D.scoped [A.real_s] (App RL.real_minus_decl [real_constant 1 1; real_constant 1 1]));
  assert_norm (D.scoped [A.real_s] (App RL.real_le_decl [x_real; one_minus_one]));
  lemma_half_laws u uf;
  RL.lemma_real_binary_at empty_schema (TR.booleans u) (SR.root_scalars u) (standard_half u uf) (root_reals u)
    [A.real_s] (half_environment u) RL.real_minus_decl (real_constant 1 1) (real_constant 1 1) A.Sub;
  lemma_half_comparison u uf RL.real_le_decl x_real one_minus_one A.Le;
  lemma_half_constants u uf;
  lemma_half_bounds ()

(* 0 < x and x < 1 both hold with x = 1/2, and the Int rounding of x < 1,
   x <= 1 - 1, is false there: the integer strict-bound adjustment is not a
   Real law. *)
let lemma_real_rounding_countermodel (u:TR.uninterpreted) (uf:TR.symbols u empty_schema)
  : Lemma (half_truth u uf (real_lt (real_constant 0 1) x_real) == true /\
           half_truth u uf (real_lt x_real (real_constant 1 1)) == true /\
           half_truth u uf (real_le x_real (real_minus (real_constant 1 1) (real_constant 1 1))) == false) =
  lemma_half_positive u uf;
  lemma_half_below_one u uf;
  lemma_half_rounding_false u uf

(* The same countermodel against the executable certificate arithmetic: with
   the Int strict-bound adjustment (integer = true) the two satisfiable strict
   bounds 0 < x, x < 1 are refuted by unit weights; with the Real orientation
   (integer = false, what A.prepare_literal uses for Real atoms) they are not,
   and A.prepare on the actual Real literals does not refute them either. *)
let zero_poly : A.poly = P.constant 0 1
let one_poly : A.poly = P.constant 1 1
let x_poly : A.poly = P.variable x_real

let lemma_integer_rounding_refutes_satisfiable ()
  : Lemma (P.accepts [A.weighted (1, 1) true A.Lt true zero_poly x_poly;
                      A.weighted (1, 1) true A.Lt true x_poly one_poly] == true /\
           P.accepts [A.weighted (1, 1) true A.Lt false zero_poly x_poly;
                      A.weighted (1, 1) true A.Lt false x_poly one_poly] == false /\
           A.prepare [(true, real_lt (real_constant 0 1) x_real); (true, real_lt x_real (real_constant 1 1))]
                     [(1, 1); (1, 1)] ==
             Some [A.weighted (1, 1) true A.Lt false zero_poly x_poly;
                   A.weighted (1, 1) true A.Lt false x_poly one_poly]) =
  assert_norm (P.accepts [A.weighted (1, 1) true A.Lt true zero_poly x_poly;
                          A.weighted (1, 1) true A.Lt true x_poly one_poly] == true);
  assert_norm (P.accepts [A.weighted (1, 1) true A.Lt false zero_poly x_poly;
                          A.weighted (1, 1) true A.Lt false x_poly one_poly] == false);
  assert_norm (A.prepare [(true, real_lt (real_constant 0 1) x_real); (true, real_lt x_real (real_constant 1 1))]
                         [(1, 1); (1, 1)] ==
                 Some [A.weighted (1, 1) true A.Lt false zero_poly x_poly;
                       A.weighted (1, 1) true A.Lt false x_poly one_poly])

(* A checked schema MAY register a datatype named Real (S.valid excludes only
   Bool and Int). There the root leaves Real heads free, so no Real law is
   derivable and the Real gate is closed: the primitive premise is validated,
   not assumed. *)
let real_box : func_decl = {
  decl_name = "real-box"; domain = []; range = A.real_s;
  interp = Some Z3DatatypeLemma.op_constructor; int_params = [0; 0; 0];
}

let is_real_box : func_decl = {
  decl_name = "is-real-box"; domain = [A.real_s]; range = bool_sort;
  interp = Some Z3DatatypeLemma.op_recognizer; int_params = [0; 0];
}

let real_datatype_schema : S.checked_schema =
  let s = { S.sorts = [A.real_s];
            S.cases = [{ S.constructor = real_box; S.recognizer = is_real_box; S.accessors = [] }] } in
  assert_norm (S.valid s);
  s

let lemma_real_datatype_refused ()
  : Lemma (not (RL.real_primitive real_datatype_schema) /\
           not (TR.supported real_datatype_schema)) =
  assert_norm (not (RL.real_primitive real_datatype_schema));
  assert_norm (not (TR.supported real_datatype_schema))
