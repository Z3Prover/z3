module Z3SortedDivisionRoot

(* Run e78cd96c. The Sorted Int division laws (Z3SortedIntDivision) from R2
   of ONE root model, and the joint positive construction.

   Z3TypedRoot gives the canonical Int div and mod the classes IntDiv and
   IntMod: the Euclidean quotient x / y and remainder x % y of F* for a NONZERO
   divisor, free (uf.apply) at a zero divisor. For EVERY model i of the typed
   root contract (TR.root_model u sch i, R1-R6) over EVERY checked schema, the
   Sorted interpretation over the root scalars on top of i satisfies
   DV.division_laws; the Int carrier is the identity of the root, so no
   carrier is existentially assumed (the Real laws need one). The standard
   root model satisfies R1-R6, the Real laws (when the schema gate holds) and
   the division laws at once, for every choice of uninterpreted carriers and
   free symbols, so the class is inhabited.

   Model-contract change (documented in Z3TypedRoot): before this module the
   root class left div and mod free at EVERY divisor, so the guarded clause
   (or (= d 0) (>= (mod x d) 0)) was false in some root models (mod the
   constant -1, d = 1). `mod_minus_one` keeps that model: the standard root
   with mod answering -1. It agrees with the standard root on the
   quantification and on every application of a declaration other than the
   canonical mod (`lemma_mod_minus_one_agrees`), and the root laws R1 and
   R3-R6, and R2 at every other operator, read only those (so the previous
   class, which left mod free, contained it); it is NOT a root model of the
   corrected class (`lemma_mod_minus_one_not_root`: R2 at mod 0 1 demands 0). The change fixes nothing
   at a zero divisor and nothing for a declaration that differs from the
   canonical div or mod in name, tag, sorts or parameters. *)

open Z3AstTheory
open Z3ValueTheory
module A = Z3LinearArithmeticAst
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module I = Z3SortedInteger
module D = Z3Definitions
module L = FStar.List.Tot
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module DV = Z3SortedIntDivision
module RL = Z3SortedReal
module RR = Z3SortedRealRoot

(* ---------------------------------------------------------------------- *)
(* Classifier agreement with the root classification                        *)
(* ---------------------------------------------------------------------- *)

(* A canonical declaration is THE canonical declaration: every field is fixed. *)
let lemma_canonical_quotient (f:func_decl)
  : Lemma (requires DV.canonical f false) (ensures f == DV.quotient_decl) = ()

let lemma_canonical_remainder (f:func_decl)
  : Lemma (requires DV.canonical f true) (ensures f == DV.remainder_decl) = ()

let lemma_root_declarations ()
  : Lemma (TR.idiv_decl == DV.quotient_decl /\ TR.imod_decl == DV.remainder_decl) =
  assert_norm (TR.idiv_decl == DV.quotient_decl);
  assert_norm (TR.imod_decl == DV.remainder_decl)

let lemma_quotient_classify (sch:S.checked_schema) (f:func_decl)
  : Lemma (requires DV.classify f == DV.Quotient)
          (ensures TR.classify (S.signature sch) f == TR.IntDiv) =
  lemma_canonical_quotient f;
  lemma_root_declarations ();
  TR.lemma_classify_idiv sch

let lemma_remainder_classify (sch:S.checked_schema) (f:func_decl)
  : Lemma (requires DV.classify f == DV.Remainder)
          (ensures TR.classify (S.signature sch) f == TR.IntMod) =
  lemma_canonical_remainder f;
  lemma_root_declarations ();
  TR.lemma_classify_imod sch

(* The two classifications cannot drift: the root class is IntDiv/IntMod
   exactly on the declarations the Sorted layer classifies (both directions
   are needed by the derivation only one way, but the other is pinned in the
   tests by the lookalike declarations). *)

(* ---------------------------------------------------------------------- *)
(* Derivation of the Sorted division laws from R2 of ONE root model         *)
(* ---------------------------------------------------------------------- *)

let lemma_root_meaning (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                       (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires TR.root_model u sch i)
          (ensures DV.division_meaning sch (SR.root_integers u) f xs
                     (T.application sch (TR.booleans u) (SR.root_scalars u) i f xs)) =
  SR.lemma_application_agreement u sch i f xs;
  match DV.classify f with
  | DV.Other -> ()
  | DV.Quotient ->
    lemma_quotient_classify sch f;
    (match xs with
     | [x; y] ->
       SR.lemma_number sch x;
       SR.lemma_number sch y;
       SR.lemma_number sch (i.V.application f [x; y]);
       if TR.int_of sch y = 0 then () else TR.law_int_div i f x y
     | _ -> ())
  | DV.Remainder ->
    lemma_remainder_classify sch f;
    (match xs with
     | [x; y] ->
       SR.lemma_number sch x;
       SR.lemma_number sch y;
       SR.lemma_number sch (i.V.application f [x; y]);
       if TR.int_of sch y = 0 then () else TR.law_int_mod i f x y
     | _ -> ())

(* For EVERY root model i (R1-R6) over a checked schema, the Sorted
   interpretation over the root scalars on top of i satisfies the Sorted
   division laws (the Int carrier is the root's identity). *)
let lemma_root_division_laws (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
  : Lemma (requires TR.root_model u sch i)
          (ensures DV.division_laws sch (TR.booleans u) (SR.root_scalars u) i) =
  introduce forall (f:func_decl) (xs:TR.targuments u sch f.domain).
    DV.division_meaning sch (SR.root_integers u) f xs
      (T.application sch (TR.booleans u) (SR.root_scalars u) i f xs)
  with lemma_root_meaning u sch i f xs

(* Joint realizability: the standard root model, for EVERY u and uf,
   satisfies R1-R6 and the Sorted division laws at once. *)
let lemma_standard_division_root (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
  : Lemma (ensures TR.root_model u sch (TR.standard u sch uf) /\
                   DV.division_laws sch (TR.booleans u) (SR.root_scalars u) (TR.standard u sch uf)) =
  TR.lemma_standard_root u sch uf;
  lemma_root_division_laws u sch (TR.standard u sch uf)

(* ... and the Real laws too when the Real gate holds: one model of the whole
   class used by the checker (R1-R6, Real laws, division laws). *)
let lemma_standard_joint_root (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
  : Lemma (requires RL.real_primitive sch)
          (ensures TR.root_model u sch (TR.standard u sch uf) /\
                   RL.real_laws sch (TR.booleans u) (SR.root_scalars u) (TR.standard u sch uf) (RR.root_reals u) /\
                   DV.division_laws sch (TR.booleans u) (SR.root_scalars u) (TR.standard u sch uf)) =
  RR.lemma_standard_real_root u sch uf;
  lemma_root_division_laws u sch (TR.standard u sch uf)

(* Non-vacuity: the class of root models with the division laws is inhabited
   for every checked schema and every choice of uninterpreted carriers. *)
let lemma_division_root_inhabited (u:TR.uninterpreted) (sch:S.checked_schema)
  : Lemma (exists (i:TR.interp u sch).
             TR.root_model u sch i /\ DV.division_laws sch (TR.booleans u) (SR.root_scalars u) i) =
  let uf : TR.symbols u sch = {
    TR.apply = (fun f _ -> S.value_inhabitant sch (TR.default_value u) f.range);
    TR.lambda = (fun bound t _ -> S.value_inhabitant sch (TR.default_value u) (ArraySort bound t));
  } in
  lemma_standard_division_root u sch uf

(* ---------------------------------------------------------------------- *)
(* A positive instance: x = 7 and d = -2 in the standard root                 *)
(* ---------------------------------------------------------------------- *)

let int_x : expr = Var 1 A.int_s
let int_d : expr = Var 0 A.int_s

let quotient_app (a b:expr) : expr = App DV.quotient_decl [a; b]
let remainder_app (a b:expr) : expr = App DV.remainder_decl [a; b]

(* The environment of the scope [d; x] (index 0 is d): x = 7, d = -2. *)
let seven_environment (u:TR.uninterpreted)
  : V.environment (TR.carrier u) (S.signature RR.empty_schema) [A.int_s; A.int_s] =
  fun (n:nat{n < 2}) -> if n = 1 then V.Scalar A.int_s (7 <: TR.carrier u A.int_s)
                        else V.Scalar A.int_s ((-2) <: TR.carrier u A.int_s)

let standard_seven (u:TR.uninterpreted) (uf:TR.symbols u RR.empty_schema) : TR.interp u RR.empty_schema =
  TR.standard u RR.empty_schema uf

let seven_value (u:TR.uninterpreted) (uf:TR.symbols u RR.empty_schema) (e:expr) : GTot int =
  Z3SortedArithmetic.integer RR.empty_schema (TR.booleans u) (SR.root_scalars u) (standard_seven u uf)
    [A.int_s; A.int_s] (seven_environment u) e

let lemma_seven_laws (u:TR.uninterpreted) (uf:TR.symbols u RR.empty_schema)
  : Lemma (TR.root_model u RR.empty_schema (standard_seven u uf) /\
           DV.division_laws RR.empty_schema (TR.booleans u) (SR.root_scalars u) (standard_seven u uf)) =
  lemma_standard_division_root u RR.empty_schema uf

let lemma_seven_variables (u:TR.uninterpreted) (uf:TR.symbols u RR.empty_schema)
  : Lemma (seven_value u uf int_x == 7 /\ seven_value u uf int_d == (-2)) =
  assert_norm (D.scoped [A.int_s; A.int_s] int_x);
  assert_norm (D.scoped [A.int_s; A.int_s] int_d)

(* 7 div (-2) = -3 and 7 mod (-2) = 1 in the standard root (7 = (-2)(-3) + 1,
   0 <= 1 < 2): the law of a negative divisor. *)
let lemma_seven_division (u:TR.uninterpreted) (uf:TR.symbols u RR.empty_schema)
  : Lemma (seven_value u uf (quotient_app int_x int_d) == (-3) /\
           seven_value u uf (remainder_app int_x int_d) == 1) =
  lemma_seven_laws u uf;
  lemma_seven_variables u uf;
  DV.lemma_classify_canonical ();
  assert_norm (D.scoped [A.int_s; A.int_s] (quotient_app int_x int_d));
  assert_norm (D.scoped [A.int_s; A.int_s] (remainder_app int_x int_d));
  DV.lemma_quotient_at RR.empty_schema (TR.booleans u) (SR.root_scalars u) (standard_seven u uf)
    [A.int_s; A.int_s] (seven_environment u) DV.quotient_decl int_x int_d;
  DV.lemma_remainder_at RR.empty_schema (TR.booleans u) (SR.root_scalars u) (standard_seven u uf)
    [A.int_s; A.int_s] (seven_environment u) DV.remainder_decl int_x int_d;
  assert_norm (DV.quotient_of 7 (-2) == (-3));
  assert_norm (DV.remainder_of 7 (-2) == 1)

(* ---------------------------------------------------------------------- *)
(* The retained countermodel of the previous class                            *)
(* ---------------------------------------------------------------------- *)

(* The standard root with mod answering -1 at every argument list (and at every
   divisor, zero or not). *)
let mod_minus_one (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
  : TR.interp u sch =
  let base = TR.standard u sch uf in
  { V.application = (fun (f:func_decl) (xs:TR.targuments u sch f.domain) ->
      match TR.classify (S.signature sch) f with
      | TR.IntMod -> (TR.make #u #(S.signature sch) A.int_s (-1) <: TR.tvalue u sch f.range)
      | _ -> base.V.application f xs);
    V.quantification = base.V.quantification }

(* It differs from the standard root exactly at the applications of the
   canonical mod (the quantification and every other declaration are the
   standard root's), so every root law that does not read the canonical mod
   holds in it as in the standard root. *)
let lemma_mod_minus_one_agrees (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
                               (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (((mod_minus_one u sch uf).V.quantification == (TR.standard u sch uf).V.quantification) /\
           (not (TR.IntMod? (TR.classify (S.signature sch) f)) ==>
            (mod_minus_one u sch uf).V.application f xs == (TR.standard u sch uf).V.application f xs)) = ()

(* It is no root model of the corrected class: R2 at mod 0 1 demands 0 % 1 = 0. *)
let lemma_mod_minus_one_not_root (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
  : Lemma (~(TR.operator_law u sch (mod_minus_one u sch uf))) =
  lemma_root_declarations ();
  TR.lemma_classify_imod sch;
  let xs : TR.targuments u sch TR.imod_decl.domain =
    [V.Scalar A.int_s (0 <: TR.carrier u A.int_s); V.Scalar A.int_s (1 <: TR.carrier u A.int_s)] in
  assert (TR.interpreted u sch TR.imod_decl xs ==
          Some (TR.make #u #(S.signature sch) A.int_s (0 % 1)));
  assert (not (TR.datatype_kind TR.imod_decl));
  assert ((mod_minus_one u sch uf).V.application TR.imod_decl xs ==
          TR.make #u #(S.signature sch) A.int_s (-1));
  assert (~((mod_minus_one u sch uf).V.application TR.imod_decl xs ==
            TR.make #u #(S.signature sch) A.int_s 0))
