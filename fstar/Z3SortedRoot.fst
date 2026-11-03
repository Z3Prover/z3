module Z3SortedRoot

(* G2 first slice (PROTOTYPE, branch fstar-typed-root-prototype-20261030; not
   in the checker manifest, no route, no executable change).

   The first two Sorted layers, Z3SortedInteger and Z3SortedSemantics (now
   ghost specifications; their executable classifiers stay Tot and
   unchanged), are instantiated over the ONE typed root carrier family
   `TR.carrier u` with the root Boolean carrier, the identity integer carrier
   and the GHOST scalar equality `TR.decide (x == y)`. For EVERY model `i` of
   the corrected root contract (TR.root_model, R1-R6) over EVERY checked
   schema, the Sorted application built on top of `i` is proved EQUAL to
   `i.application`, operator by operator, and hence the Sorted evaluation
   equals the root evaluation for every scoped expression.

   The proof only uses
   - classifier agreement, proved on the WHOLE classification domain:
     Z3SortedSemantics.classify is TR.connective (`lemma_core_agreement`),
     and on its Other branch Z3SortedInteger.classify is exactly the Int part
     of TR.classify (`lemma_integer_agreement`, both directions; this needs
     the nullary +/* policy of TR.numeric);
   - the NAMED root laws (law_constant ... law_int_nary, law_equality,
     law_ite), R4 (constructors), R5 (recognizers) and R6 (matched
     selectors); an unmatched selector is passed to `i` itself, so the
     selector freedom of the root class is kept, not dropped.
   Layer order: Sorted runs its classifiers first and the datatype layer
   (S.application) last; the root contract fixes datatypes through R4-R6.
   They agree because classified operators carry theory tags and datatype
   operations carry tags 200/201/202 (TR.lemma_classified_theory).

   Dependency DAG: Z3SortedRoot -> {Z3TypedRoot, Z3SortedSemantics,
   Z3SortedInteger}; Z3TypedRoot depends on no Sorted module. *)

open Z3AstTheory
open Z3ValueTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module A = Z3LinearArithmeticAst
module B = Z3BoundedBoolEquiv
module R = Z3ResolutionProofTheory
module D = Z3Definitions
module L = FStar.List.Tot
module FE = FStar.FunctionalExtensionality
module TR = Z3TypedRoot
module I = Z3SortedInteger
module T = Z3SortedSemantics

(* ---------------------------------------------------------------------- *)
(* 1. Classifier agreement (executable classifiers, every declaration)     *)
(* ---------------------------------------------------------------------- *)

let rec lemma_boolean_sorts (ss:list sort)
  : Lemma (TR.boolean_sorts ss == T.boolean_sorts ss) (decreases ss) =
  match ss with [] -> () | _ :: rest -> lemma_boolean_sorts rest

let rec lemma_integer_sorts (ss:list sort)
  : Lemma (TR.same_sorts TR.int_s ss == I.integer_sorts ss) (decreases ss) =
  match ss with [] -> () | _ :: rest -> lemma_integer_sorts rest

let core_op (op:T.operation) : TR.theory_op =
  match op with
  | T.Constant b -> TR.Constant b
  | T.Negation -> TR.Negation
  | T.Implication -> TR.Implication
  | T.Nary o -> TR.Nary o
  | T.Equality s -> TR.Equality s
  | T.Choice s -> TR.Choice s
  | T.Other -> TR.Other

(* The Sorted core classifier IS the root connective classifier. *)
let lemma_core_agreement (f:func_decl) : Lemma (TR.connective f == core_op (T.classify f)) =
  lemma_boolean_sorts f.domain

let lemma_core_classify (sch:S.checked_schema) (f:func_decl)
  : Lemma (requires ~(T.Other? (T.classify f)))
          (ensures TR.classify (S.signature sch) f == core_op (T.classify f)) =
  lemma_core_agreement f

let int_op (op:I.operation) : TR.theory_op =
  match op with
  | I.Numeral n -> TR.Numeral TR.int_s n 1
  | I.Calculate o -> TR.Arith TR.int_s o
  | I.Compare r -> TR.Compare TR.int_s r
  | I.Other -> TR.Other

(* The Int operations of the root classification. *)
let int_part (op:TR.theory_op) : TR.theory_op =
  match op with
  | TR.Numeral s _ _ | TR.Arith s _ | TR.Compare s _ -> if s = TR.int_s then op else TR.Other
  | _ -> TR.Other

(* Int is never a datatype of a checked schema (S.valid). *)
let lemma_int_primitive (sch:S.checked_schema)
  : Lemma (not (V.datatype_sort (S.signature sch) TR.int_s)) = ()

let lemma_numeric_agreement (sch:S.checked_schema) (f:func_decl)
  : Lemma (int_op (I.classify f) == int_part (TR.numeric (S.signature sch) f)) =
  lemma_int_primitive sch;
  lemma_integer_sorts f.domain

(* On the Sorted integer layer's domain (the core classifier says Other),
   the Sorted integer classifier is exactly the Int part of the root
   classifier, in BOTH directions, for every checked schema. *)
let lemma_integer_agreement (sch:S.checked_schema) (f:func_decl)
  : Lemma (requires T.Other? (T.classify f))
          (ensures int_op (I.classify f) == int_part (TR.classify (S.signature sch) f)) =
  lemma_core_agreement f;
  lemma_numeric_agreement sch f

let lemma_integer_classify (sch:S.checked_schema) (f:func_decl)
  : Lemma (requires T.Other? (T.classify f) /\ ~(I.Other? (I.classify f)))
          (ensures TR.classify (S.signature sch) f == int_op (I.classify f)) =
  lemma_integer_agreement sch f

(* ---------------------------------------------------------------------- *)
(* 2. The root scalar model of the Sorted layers (one carrier family)      *)
(* ---------------------------------------------------------------------- *)

let root_integers (u:TR.uninterpreted) : I.carrier (TR.carrier u) = {
  I.encode = (fun (n:int) -> (n <: TR.carrier u A.int_s));
  I.decode = (fun (v:TR.carrier u A.int_s) -> (v <: int));
  I.integer_isomorphism = ();
}

(* Ghost equality: no Tot decision of equality on reals, functions or
   uninterpreted carriers is assumed. *)
let root_equality (u:TR.uninterpreted) : T.scalar_equality (TR.carrier u) = {
  T.equal_scalar = (fun (s:sort) (x y:TR.carrier u s) -> TR.decide (x == y));
  T.scalar_equality_correct = ();
}

let root_scalars (u:TR.uninterpreted) : T.scalar_model (TR.carrier u) = {
  T.reflection = root_equality u;
  T.integers = root_integers u;
}

(* The Sorted interpretation on top of a root interpretation i. *)
let sorted (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) : TR.interp u sch =
  T.interpretation sch (TR.booleans u) (root_scalars u) i

(* ---------------------------------------------------------------------- *)
(* 3. Value-level bridges (pure, no model hypothesis)                      *)
(* ---------------------------------------------------------------------- *)

let lemma_truth_value (#u:TR.uninterpreted) (sch:S.checked_schema) (v:TR.tvalue u sch bool_sort)
  : Lemma (T.truth_value sch (TR.booleans u) v == TR.truth sch v) =
  match v with
  | V.Scalar _ _ -> ()
  | V.Constructor f _ -> TR.lemma_registered (S.signature sch) f

let lemma_boolean (#u:TR.uninterpreted) (sch:S.checked_schema) (b:bool)
  : Lemma (T.boolean sch (TR.booleans u) b == TR.boolean #u sch b) = ()

(* A Boolean value is determined by its truth. *)
let lemma_bool_ext (#u:TR.uninterpreted) (sch:S.checked_schema) (v:TR.tvalue u sch bool_sort) (b:bool)
  : Lemma (requires TR.truth sch v == b) (ensures v == TR.boolean #u sch b) =
  TR.lemma_make_scalar #u #(S.signature sch) bool_sort v

let lemma_number (#u:TR.uninterpreted) (sch:S.checked_schema) (v:TR.tvalue u sch A.int_s)
  : Lemma (I.number sch (root_integers u) v == TR.int_of sch v) =
  match v with
  | V.Scalar _ _ -> ()
  | V.Constructor f _ -> TR.lemma_registered (S.signature sch) f

(* An Int value is determined by its number. *)
let lemma_int_ext (#u:TR.uninterpreted) (sch:S.checked_schema) (v:TR.tvalue u sch A.int_s) (n:int)
  : Lemma (requires TR.int_of sch v == n) (ensures v == I.value sch (root_integers u) n) =
  TR.lemma_make_scalar #u #(S.signature sch) A.int_s v

let rec lemma_combine (op:B.nary_op) (bs:list bool)
  : Lemma (T.combine op bs == TR.combine op bs) (decreases bs) =
  match bs with [] -> () | _ :: rest -> lemma_combine op rest

let rec lemma_boolean_values (#u:TR.uninterpreted) (sch:S.checked_schema)
                             (ss:list sort{T.boolean_sorts ss /\ TR.boolean_sorts ss})
                             (xs:TR.targuments u sch ss)
  : Lemma (ensures T.boolean_values sch (TR.booleans u) ss xs == TR.truths sch ss xs) (decreases ss) =
  match ss, xs with
  | [], [] -> ()
  | _ :: rest, x :: tail -> lemma_truth_value sch x; lemma_boolean_values sch rest tail
  | _, _ -> ()

let rec lemma_numbers (#u:TR.uninterpreted) (sch:S.checked_schema)
                      (ss:list sort{I.integer_sorts ss /\ TR.same_sorts TR.int_s ss})
                      (xs:TR.targuments u sch ss)
  : Lemma (ensures I.numbers sch (root_integers u) ss xs == TR.ints sch ss xs) (decreases ss) =
  match ss, xs with
  | [], [] -> ()
  | _ :: rest, x :: tail -> lemma_number sch x; lemma_numbers sch rest tail
  | _, _ -> ()

let rec lemma_sum (xs:list int) : Lemma (I.sum xs == TR.isum xs) (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_sum rest

let rec lemma_product (xs:list int) : Lemma (I.product xs == TR.iproduct xs) (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_product rest

let lemma_calculate (o:A.operation{o = A.Add || o = A.Mul || o = A.Sub}) (xs:list int)
  : Lemma (I.calculate o xs ==
           (match o with A.Add -> TR.isum xs | A.Mul -> TR.iproduct xs | _ -> TR.isubtract xs)) =
  lemma_sum xs; lemma_product xs;
  match xs with _ :: rest -> lemma_sum rest | [] -> ()

(* ---------------------------------------------------------------------- *)
(* 4. Layer agreement for EVERY root model                                 *)
(* ---------------------------------------------------------------------- *)

(* Datatype layer (S.application, Sorted's last layer): R4, R5, R6; an
   unmatched selector goes to i itself (its free choice is kept). *)
let lemma_datatype_layer (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                         (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires TR.root_model u sch i)
          (ensures S.application sch (TR.booleans u) i f xs == i.V.application f xs) =
  let sigma = S.signature sch in
  if L.mem f sigma then assert (TR.constructor_law u sch i)
  else match S.find_recognizer f sch.S.cases with
  | Some c ->
    (match xs with
     | [v] ->
       assert (TR.recognizer_at u sch i f);
       assert (TR.recognizer_case u sch i f c v);
       lemma_bool_ext sch (i.V.application f [v]) (V.recognize c.S.constructor v)
     | _ -> ())
  | None ->
    (match S.find_accessor f sch.S.cases with
     | Some r ->
       (match xs with
        | [v] ->
          let c = r.S.matched_case in
          S.lemma_signature_member sch.S.cases c;
          if V.recognize c.S.constructor v then begin
            V.lemma_reconstruct sigma c.S.constructor v;
            let ys : TR.targuments u sch c.S.constructor.domain = V.fields v in
            assert (TR.accessor_at u sch i f);
            assert (TR.accessor_case u sch i f r ys);
            V.lemma_fields_index sigma c.S.constructor.domain ys r.S.field
          end
          else ()
        | _ -> ())
     | None -> ())

(* Integer layer (Z3SortedInteger.application) on the core's Other branch,
   one small lemma per operation class. *)
let sapp (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
         (f:func_decl) (xs:TR.targuments u sch f.domain) : GTot (TR.tvalue u sch f.range) =
  I.application sch (TR.booleans u) (root_integers u) i f xs

let lemma_numeral_layer (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (n:int)
                        (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires TR.root_model u sch i /\ T.Other? (T.classify f) /\ I.classify f == I.Numeral n)
          (ensures sapp u sch i f xs == i.V.application f xs) =
  lemma_integer_classify sch f;
  TR.law_int_numeral i f n 1 xs;
  lemma_int_ext sch (i.V.application f xs) n

let lemma_calculate_layer (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (o:A.operation)
                          (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires TR.root_model u sch i /\ T.Other? (T.classify f) /\ I.classify f == I.Calculate o)
          (ensures sapp u sch i f xs == i.V.application f xs) =
  lemma_integer_classify sch f;
  lemma_integer_sorts f.domain;
  TR.law_int_nary i f o xs;
  lemma_numbers sch f.domain xs;
  lemma_calculate o (TR.ints sch f.domain xs);
  lemma_int_ext sch (i.V.application f xs) (I.calculate o (I.numbers sch (root_integers u) f.domain xs))

let lemma_compare_layer (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (r:A.relation)
                        (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires TR.root_model u sch i /\ T.Other? (T.classify f) /\ I.classify f == I.Compare r)
          (ensures sapp u sch i f xs == i.V.application f xs) =
  lemma_integer_classify sch f;
  match xs with
  | [x; y] ->
    lemma_number sch x; lemma_number sch y;
    (match r with
     | A.Le -> TR.law_int_le i f x y
     | A.Lt -> TR.law_int_lt i f x y
     | A.Ge -> TR.law_int_ge i f x y
     | A.Gt -> TR.law_int_gt i f x y
     | A.Eq -> ());
    lemma_bool_ext sch (i.V.application f [x; y]) (I.compare r (TR.int_of sch x) (TR.int_of sch y))
  | _ -> ()

let lemma_integer_layer (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                        (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires TR.root_model u sch i /\ T.Other? (T.classify f))
          (ensures I.application sch (TR.booleans u) (root_integers u) i f xs == i.V.application f xs) =
  match I.classify f with
  | I.Numeral n -> lemma_numeral_layer u sch i n f xs
  | I.Calculate o -> lemma_calculate_layer u sch i o f xs
  | I.Compare r -> lemma_compare_layer u sch i r f xs
  | I.Other -> lemma_datatype_layer u sch i f xs

(* Core layer (Z3SortedSemantics.application), one lemma per operation class. *)
let tapp (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
         (f:func_decl) (xs:TR.targuments u sch f.domain) : GTot (TR.tvalue u sch f.range) =
  T.application sch (TR.booleans u) (root_scalars u) i f xs

let lemma_connective_layer (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                           (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires TR.root_model u sch i /\
                    (T.Constant? (T.classify f) \/ T.Negation? (T.classify f) \/ T.Implication? (T.classify f)))
          (ensures tapp u sch i f xs == i.V.application f xs) =
  lemma_core_classify sch f;
  match T.classify f with
  | T.Constant b ->
    TR.law_constant i f b xs;
    lemma_bool_ext sch (i.V.application f xs) b
  | T.Negation ->
    (match xs with
     | [x] ->
       TR.law_not i f x; lemma_truth_value sch x;
       lemma_bool_ext sch (i.V.application f [x]) (not (TR.truth sch x))
     | _ -> ())
  | T.Implication ->
    (match xs with
     | [x; y] ->
       TR.law_implies i f x y; lemma_truth_value sch x; lemma_truth_value sch y;
       lemma_bool_ext sch (i.V.application f [x; y]) (not (TR.truth sch x) || TR.truth sch y)
     | _ -> ())
  | _ -> ()

let lemma_nary_layer (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (op:B.nary_op)
                     (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires TR.root_model u sch i /\ T.classify f == T.Nary op)
          (ensures tapp u sch i f xs == i.V.application f xs) =
  lemma_core_classify sch f;
  lemma_boolean_sorts f.domain;
  TR.law_nary i f op xs;
  lemma_boolean_values sch f.domain xs;
  lemma_combine op (TR.truths sch f.domain xs);
  lemma_bool_ext sch (i.V.application f xs) (TR.combine op (TR.truths sch f.domain xs))

(* = at EVERY sort: the Sorted ghost equality (TR.decide) agrees with R2. *)
let lemma_equality_layer (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (s:sort)
                         (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires TR.root_model u sch i /\ T.classify f == T.Equality s)
          (ensures tapp u sch i f xs == i.V.application f xs) =
  lemma_core_classify sch f;
  match xs with
  | [x; y] ->
    TR.law_equality i f s x y;
    T.lemma_equal_tree (root_equality u) x y;
    lemma_bool_ext sch (i.V.application f [x; y]) (T.equal_tree (root_equality u) x y)
  | _ -> ()

let lemma_choice_layer (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (s:sort)
                       (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires TR.root_model u sch i /\ T.classify f == T.Choice s)
          (ensures tapp u sch i f xs == i.V.application f xs) =
  lemma_core_classify sch f;
  match xs with
  | [c; x; y] -> TR.law_ite i f s c x y; lemma_truth_value sch c
  | _ -> ()

(* THE same-model compatibility lemma: the Sorted application over a root
   model i IS i's application, for every declaration and argument list. *)
let lemma_application_agreement (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                                (f:func_decl) (xs:TR.targuments u sch f.domain)
  : Lemma (requires TR.root_model u sch i)
          (ensures T.application sch (TR.booleans u) (root_scalars u) i f xs == i.V.application f xs) =
  match T.classify f with
  | T.Constant _ | T.Negation | T.Implication -> lemma_connective_layer u sch i f xs
  | T.Nary op -> lemma_nary_layer u sch i op f xs
  | T.Equality s -> lemma_equality_layer u sch i s f xs
  | T.Choice s -> lemma_choice_layer u sch i s f xs
  | T.Other -> lemma_integer_layer u sch i f xs

(* ---------------------------------------------------------------------- *)
(* 5. Evaluation agreement for every scoped expression                     *)
(* ---------------------------------------------------------------------- *)

let rec lemma_evaluate_agreement (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                                 (scope:list sort) (rho:V.environment (TR.carrier u) (S.signature sch) scope)
                                 (e:expr{D.scoped scope e})
  : Lemma (requires TR.root_model u sch i)
          (ensures V.evaluate (S.signature sch) (sorted u sch i) scope rho e ==
                   V.evaluate (S.signature sch) i scope rho e)
          (decreases %[(V.expression_size e <: nat); (0 <: nat)]) =
  let sigma = S.signature sch in
  match e with
  | Var _ _ -> ()
  | App f args ->
    lemma_evaluate_args_agreement u sch i scope rho args f.domain;
    if not (L.mem f sigma) then
      lemma_application_agreement u sch i f (V.evaluate_args sigma i scope rho args f.domain)
  | Quantifier k bound _ body ->
    let left = V.evaluate_body sigma (sorted u sch i) scope rho bound body in
    let right = V.evaluate_body sigma i scope rho bound body in
    let pointwise (vs:TR.targuments u sch (L.rev bound)) : Lemma (left vs == right vs) =
      lemma_evaluate_agreement u sch i (L.rev bound @ scope) (V.extend sigma scope (L.rev bound) vs rho) body in
    FStar.Classical.forall_intro pointwise;
    assert (FE.feq_g left right);
    FE.extensionality_g (TR.targuments u sch (L.rev bound)) (fun _ -> V.tree (TR.carrier u)) left right;
    assert (left == right);
    (* Sorted's quantification IS i's (T.interpretation keeps other.quantification). *)
    assert ((sorted u sch i).V.quantification == i.V.quantification);
    assert (V.evaluate sigma (sorted u sch i) scope rho e ==
            i.V.quantification k bound (get_sort body) (V.typed_body sigma bound (get_sort body) left));
    assert (V.evaluate sigma i scope rho e ==
            i.V.quantification k bound (get_sort body) (V.typed_body sigma bound (get_sort body) right))

and lemma_evaluate_args_agreement (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                                  (scope:list sort) (rho:V.environment (TR.carrier u) (S.signature sch) scope)
                                  (es:list expr{D.scoped_args scope es}) (ss:list sort{sorts_match es ss})
  : Lemma (requires TR.root_model u sch i)
          (ensures V.evaluate_args (S.signature sch) (sorted u sch i) scope rho es ss ==
                   V.evaluate_args (S.signature sch) i scope rho es ss)
          (decreases %[(V.expressions_size es <: nat); (1 <: nat)]) =
  match es, ss with
  | e :: rest, s :: remaining ->
    V.lemma_sort_eq (get_sort e) s;
    lemma_evaluate_agreement u sch i scope rho e;
    lemma_evaluate_args_agreement u sch i scope rho rest remaining
  | _, _ -> ()

(* Sorted truth = root truth, at every scope and environment. *)
let lemma_truth_agreement (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                          (scope:list sort) (rho:V.environment (TR.carrier u) (S.signature sch) scope)
                          (e:expr)
  : Lemma (requires TR.root_model u sch i /\ D.scoped scope e /\ get_sort e == bool_sort)
          (ensures T.truth_at sch (TR.booleans u) (root_scalars u) i scope rho e ==
                   TR.truth sch (V.evaluate (S.signature sch) i scope rho e)) =
  lemma_evaluate_agreement u sch i scope rho e;
  lemma_truth_value sch (V.evaluate (S.signature sch) i scope rho e)
