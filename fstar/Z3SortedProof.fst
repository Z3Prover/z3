module Z3SortedProof

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module AR = Z3SortedArithmetic
module DT = Z3SortedDatatype
module U = Z3UnifiedProof
module P = Z3ProofDocument
module R = Z3ResolutionProofTheory
module D = Z3Definitions
module L = FStar.List.Tot
module I = Z3ProofIndex
module IT = Z3IdTable
module B = Z3BoundedBoolEquiv
module TN = Z3TheoryNormalize
module Q = Z3SortedQuantifier
module N = Z3BooleanNormalForm
module E = Z3SortedSkolem
module SK = Z3Skolemization
module NR = Z3NnfReplay
module DS = Z3SortedDependentSkolem
module LA = Z3LinearArithmeticAst
module RL = Z3SortedReal
module LIN = Z3SortedRealLinear
module RO = Z3SortedRealOrder
module RP = Z3SortedRealProduct
module SI = Z3SortedInteger
module DV = Z3SortedIntDivision
module RX = Z3SortedRealExtension
module DX = Z3SortedDivisionExtension

let rec equations (facts:list expr) : Tot (list U.judgment) (decreases facts) =
  match facts with
  | [] -> []
  | App f [a; b] :: rest ->
    if f = R.eq_decl (get_sort a) && get_sort a = get_sort b
    then U.Equal a b :: equations rest else equations rest
  | _ :: rest -> equations rest

let rec equations_hold (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (js:list U.judgment) : GTot bool (decreases js) =
  match js with
  | [] -> true
  | U.Equal a b :: rest -> T.same_value s bc eq other a b && equations_hold s bc eq other rest
  | _ -> false

let rec lemma_equations (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (facts:list expr)
  : Lemma (requires T.truths s bc eq other facts)
          (ensures equations_hold s bc eq other (equations facts))
          (decreases facts) =
  match facts with
  | [] -> ()
  | App f [a; b] :: rest ->
    if f = R.eq_decl (get_sort a) && get_sort a = get_sort b then (
      T.lemma_equality s bc eq other a b;
      T.lemma_same_value s bc eq other a b);
    lemma_equations s bc eq other rest
  | _ :: rest -> lemma_equations s bc eq other rest

let rec known_equal (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (origin:expr) (known:list expr) : GTot bool (decreases known) =
  match known with
  | [] -> true
  | e :: rest -> T.same_value s bc eq other origin e && known_equal s bc eq other origin rest

let rec lemma_known_member (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (origin:expr) (known:list expr) (e:expr)
  : Lemma (requires known_equal s bc eq other origin known /\ L.mem e known)
          (ensures T.same_value s bc eq other origin e)
          (decreases known) =
  match known with
  | [] -> ()
  | x :: rest -> if x <> e then lemma_known_member s bc eq other origin rest e

let lemma_same_transitive (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (a b c:expr)
  : Lemma (requires T.same_value s bc eq other a b /\ T.same_value s bc eq other b c)
          (ensures T.same_value s bc eq other a c) =
  T.lemma_same_value s bc eq other a b;
  T.lemma_same_value s bc eq other b c;
  T.lemma_same_value s bc eq other a c

let lemma_same_symmetric (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (a b:expr)
  : Lemma (requires T.same_value s bc eq other a b)
          (ensures T.same_value s bc eq other b a) =
  T.lemma_same_value s bc eq other a b;
  T.lemma_same_value s bc eq other b a

let rec lemma_extend_reachable (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                               (origin:expr) (js:list U.judgment) (known:list expr)
  : Lemma (requires equations_hold s bc eq other js /\ known_equal s bc eq other origin known)
          (ensures known_equal s bc eq other origin (U.extend_reachable U.Equality js known))
          (decreases js) =
  match js with
  | [] -> ()
  | U.Equal a b :: rest ->
    if L.mem a known then (
      lemma_known_member s bc eq other origin known a;
      lemma_same_transitive s bc eq other origin a b;
      lemma_extend_reachable s bc eq other origin rest (b :: known))
    else if L.mem b known then (
      lemma_known_member s bc eq other origin known b;
      lemma_same_symmetric s bc eq other a b;
      lemma_same_transitive s bc eq other origin b a;
      lemma_extend_reachable s bc eq other origin rest (a :: known))
    else lemma_extend_reachable s bc eq other origin rest known
  | _ -> ()

let rec lemma_reachable (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (fuel:nat) (origin:expr) (js:list U.judgment) (known:list expr)
  : Lemma (requires equations_hold s bc eq other js /\ known_equal s bc eq other origin known)
          (ensures known_equal s bc eq other origin (U.reachable fuel U.Equality js known))
          (decreases fuel) =
  if fuel > 0 then (
    lemma_extend_reachable s bc eq other origin js known;
    lemma_reachable s bc eq other (fuel - 1) origin js (U.extend_reachable U.Equality js known))

(* Set matching tries many pairs; cap the recursive work for each candidate. *)
let atom_fuel (fuel:nat) : n:nat{n <= fuel} = if fuel > 8 then 8 else fuel

let propositional (arithmetic:bool) (negated:bool) (a b:expr) : bool =
  (* Arithmetic matches must not unlock unbounded Boolean context specialization. *)
  if arithmetic then
    if not (Some? (expression_budget 256 a) && Some? (expression_budget 256 b)) then false
    else N.shape_equal 32 (N.normalize negated (T.cut 64 a)) (N.normalize false (T.cut 64 b))
  else DT.bounded_propositional (B.Eq (if negated then B.Not (T.cut 64 a) else T.cut 64 a) (T.cut 64 b))

let lemma_propositional (rho:expr -> bool) (arithmetic:bool) (negated:bool) (a b:expr)
  : Lemma (requires propositional arithmetic negated a b)
          (ensures B.eval rho
            (B.Eq (if negated then B.Not (T.cut 64 a) else T.cut 64 a) (T.cut 64 b))) =
  if arithmetic then (
    N.lemma_shape_equal_sound rho 32
      (N.normalize negated (T.cut 64 a)) (N.normalize false (T.cut 64 b));
    N.lemma_normalize_sound rho negated (T.cut 64 a);
    N.lemma_normalize_sound rho false (T.cut 64 b))
  else DT.lemma_bounded_propositional rho
    (B.Eq (if negated then B.Not (T.cut 64 a) else T.cut 64 a) (T.cut 64 b))

(* Typed-root G2: the Sorted truth is a GHOST valuation. The executable
   propositional checks are sound for it through an executable valuation
   frozen on the atoms of the checked formula (B.freeze / B.lemma_freeze),
   never by casting the ghost valuation to Tot. *)
let lemma_propositional_g (sigma:expr -> GTot bool) (arithmetic:bool) (negated:bool) (a b:expr)
  : Lemma (requires propositional arithmetic negated a b)
          (ensures B.geval sigma
            (B.Eq (if negated then B.Not (T.cut 64 a) else T.cut 64 a) (T.cut 64 b))) =
  let f = B.Eq (if negated then B.Not (T.cut 64 a) else T.cut 64 a) (T.cut 64 b) in
  lemma_propositional (B.freeze sigma (B.support f)) arithmetic negated a b;
  B.lemma_freeze sigma (B.support f) f

(* N.normalize preserves every ghost valuation (frozen on the atoms of both
   formulas). *)
let lemma_normalize_geval (sigma:expr -> GTot bool) (negative:bool) (f:B.skeleton)
  : Lemma (B.geval sigma (N.normalize negative f) ==
           (if negative then not (B.geval sigma f) else B.geval sigma f)) =
  B.lemma_freeze_pair sigma f (N.normalize negative f);
  N.lemma_normalize_sound (B.freeze sigma (L.append (B.support f) (B.support (N.normalize negative f))))
    negative f

(* Ghost twin of N.lemma_shape_equal_by_sound: its hypothesis relates the
   valuation on EVERY pair accepted by `same`, so it cannot go through a
   finite freeze; the same structural proof is repeated over B.geval. *)
let rec lemma_shape_equal_by_geval (rho:expr -> GTot bool) (same:expr -> expr -> Tot bool)
                                   (fuel:nat) (s t:B.skeleton)
  : Lemma (requires N.shape_equal_by same fuel s t /\
                    (forall (a b:expr). same a b ==> rho a == rho b))
          (ensures B.geval rho s == B.geval rho t)
          (decreases %[fuel; 0]) =
  if s = t || fuel = 0 then ()
  else match s, t with
  | B.Atom _, B.Atom _ -> ()
  | B.Not a, B.Not b -> lemma_shape_equal_by_geval rho same (fuel - 1) a b
  | B.Eq a b, B.Eq c d ->
    if N.shape_equal_by same (fuel - 1) a c && N.shape_equal_by same (fuel - 1) b d then (
      lemma_shape_equal_by_geval rho same (fuel - 1) a c;
      lemma_shape_equal_by_geval rho same (fuel - 1) b d)
    else (
      lemma_shape_equal_by_geval rho same (fuel - 1) a d;
      lemma_shape_equal_by_geval rho same (fuel - 1) b c)
  | B.Nary op xs, B.Nary other ys ->
    lemma_shape_included_by_geval rho same (fuel - 1) xs ys;
    lemma_shape_included_by_geval rho same (fuel - 1) ys xs;
    (match op with B.And | B.Or | B.Xor -> ())
  | _, _ -> ()

and lemma_shape_included_by_geval (rho:expr -> GTot bool) (same:expr -> expr -> Tot bool)
                                  (fuel:nat) (xs ys:list B.skeleton)
  : Lemma (requires N.shape_included_by same fuel xs ys /\
                    (forall (a b:expr). same a b ==> rho a == rho b))
          (ensures
            (B.geval_args rho B.And ys ==> B.geval_args rho B.And xs) /\
            (B.geval_args rho B.Or xs ==> B.geval_args rho B.Or ys))
          (decreases %[fuel; L.length xs + L.length ys + 1]) =
  match xs with
  | [] -> ()
  | x :: rest ->
    lemma_shape_member_by_geval rho same fuel x ys;
    lemma_shape_included_by_geval rho same fuel rest ys

and lemma_shape_member_by_geval (rho:expr -> GTot bool) (same:expr -> expr -> Tot bool)
                                (fuel:nat) (x:B.skeleton) (ys:list B.skeleton)
  : Lemma (requires N.shape_member_by same fuel x ys /\
                    (forall (a b:expr). same a b ==> rho a == rho b))
          (ensures
            (B.geval_args rho B.And ys ==> B.geval rho x) /\
            (B.geval rho x ==> B.geval_args rho B.Or ys))
          (decreases %[fuel; L.length ys]) =
  match ys with
  | [] -> ()
  | y :: rest ->
    if fuel > 0 && N.shape_equal_by same (fuel - 1) x y
    then lemma_shape_equal_by_geval rho same (fuel - 1) x y
    else lemma_shape_member_by_geval rho same fuel x rest

let rec congruent (arithmetic:bool) (search_atoms:bool) (scope:list sort) (fuel:nat) (a b:expr)
  : Tot bool (decreases %[fuel; 0]) =
  get_sort a = get_sort b &&
  (a = b || (arithmetic && AR.equivalent a b) ||
   (get_sort a = bool_sort && propositional arithmetic false a b) ||
   (fuel > 0 &&
    ((match a, b with
     | App f xs, App g ys -> f = g && congruent_application arithmetic search_atoms scope (fuel - 1) f xs ys
     | Quantifier k bs t body, Quantifier k' bs' t' body' ->
       k = k' && bs = bs' && t = t' && congruent arithmetic search_atoms (L.rev bs @ scope) (fuel - 1) body body'
     | _, _ -> false) ||
     (get_sort a = bool_sort && congruent_boolean arithmetic search_atoms scope (fuel - 1) a b))))

and congruent_arguments (arithmetic:bool) (search_atoms:bool) (scope:list sort) (fuel:nat) (xs ys:list expr)
  : Tot bool (decreases %[fuel; L.length xs + 1]) =
  match xs, ys with
  | [], [] -> true
  | x :: rest, y :: tail ->
    congruent arithmetic search_atoms scope fuel x y && congruent_arguments arithmetic search_atoms scope fuel rest tail
  | _, _ -> false

and congruent_application (arithmetic:bool) (search_atoms:bool) (scope:list sort) (fuel:nat) (f:func_decl) (xs ys:list expr)
  : Tot bool (decreases %[fuel; L.length xs + 2]) =
  congruent_arguments arithmetic search_atoms scope fuel xs ys ||
  (* Boolean equality and choices use reflection instead of branching over operand orders. *)
  (match xs, ys with
   | [x; y], [u; v] ->
     get_sort x <> bool_sort &&
     f = R.eq_decl (get_sort x) &&
     congruent arithmetic search_atoms scope fuel x v && congruent arithmetic search_atoms scope fuel y u
   | [c; x; y], [d; u; v] ->
     get_sort x <> bool_sort &&
     T.classify f = T.Choice (get_sort x) &&
     propositional arithmetic true c d &&
     congruent arithmetic search_atoms scope fuel x v && congruent arithmetic search_atoms scope fuel y u
   | _, _ -> false)

and congruent_boolean (arithmetic:bool) (search_atoms:bool) (scope:list sort) (fuel:nat) (a b:expr)
  : Tot bool (decreases %[fuel; 2]) =
  if not search_atoms || scope = [] then false else
  if not (Some? (expression_budget 256 a) && Some? (expression_budget 256 b)) then false else
  let left = T.cut 64 a in
  let right = T.cut 64 b in
  (* Keep this guard lazy during normalization; opaque atoms would re-enter the same pair. *)
  if left = B.Atom a && right = B.Atom b then false
  else N.shape_equal_by (congruent_atom arithmetic scope fuel)
    32 (N.normalize false left) (N.normalize false right)

and congruent_atom (arithmetic:bool) (scope:list sort) (fuel:nat) (a b:expr)
  : Tot bool (decreases %[fuel; 1]) =
  (* Candidate comparison must not recursively restart the pair search. *)
  if D.scoped scope a && D.scoped scope b
  then congruent arithmetic false scope (atom_fuel fuel) a b else false

let lemma_scoped_binary (scope:list sort) (f:func_decl) (x y:expr)
  : Lemma (requires D.scoped scope (App f [x; y]))
          (ensures D.scoped scope x /\ D.scoped scope y) =
  assert (D.scoped_args scope [x; y]);
  assert (D.scoped_args scope [y])

let lemma_scoped_ternary (scope:list sort) (f:func_decl) (c x y:expr)
  : Lemma (requires D.scoped scope (App f [c; x; y]))
          (ensures D.scoped scope c /\ D.scoped scope x /\ D.scoped scope y) =
  assert (D.scoped_args scope [c; x; y]);
  assert (D.scoped_args scope [x; y]);
  assert (D.scoped_args scope [y])

let lemma_congruent_boolean_shape (arithmetic:bool) (search_atoms:bool) (scope:list sort)
                                  (fuel:nat) (a b:expr)
  : Lemma (requires congruent_boolean arithmetic search_atoms scope fuel a b)
          (ensures N.shape_equal_by (congruent_atom arithmetic scope fuel)
                     32 (N.normalize false (T.cut 64 a)) (N.normalize false (T.cut 64 b))) =
  assert_norm (congruent_boolean arithmetic search_atoms scope fuel a b ==
    (if not search_atoms || scope = [] then false else
     if not (Some? (expression_budget 256 a) && Some? (expression_budget 256 b)) then false else
     if T.cut 64 a = B.Atom a && T.cut 64 b = B.Atom b then false
     else N.shape_equal_by (congruent_atom arithmetic scope fuel)
       32 (N.normalize false (T.cut 64 a)) (N.normalize false (T.cut 64 b))))

let rec lemma_congruent (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (scope:list sort) (rho:V.environment base (S.signature s) scope)
                        (arithmetic:bool) (search_atoms:bool) (fuel:nat) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ congruent arithmetic search_atoms scope fuel a b)
          (ensures T.evaluate_at s bc eq other scope rho a ==
                   T.evaluate_at s bc eq other scope rho b)
          (decreases %[fuel; 0]) =
  if a = b then ()
  else if arithmetic && AR.equivalent a b then AR.lemma_equivalent s bc eq other scope rho a b
  else if get_sort a = bool_sort && propositional arithmetic false a b then (
    T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 64 a;
    T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 64 b;
    lemma_propositional_g (T.truth_at s bc eq other scope rho) arithmetic false a b;
    T.lemma_boolean s bc (T.evaluate_at s bc eq other scope rho a);
    T.lemma_boolean s bc (T.evaluate_at s bc eq other scope rho b))
  else if fuel > 0 then (
    match a, b with
    | App f xs, App g ys ->
      if not (f = g && congruent_application arithmetic search_atoms scope (fuel - 1) f xs ys) then
        lemma_congruent_boolean s bc eq other scope rho arithmetic search_atoms (fuel - 1) a b
      else if congruent_arguments arithmetic search_atoms scope (fuel - 1) xs ys then
        lemma_congruent_arguments s bc eq other scope rho arithmetic search_atoms (fuel - 1) xs ys f.domain
      else (match xs, ys with
      | [x; y], [u; v] ->
        lemma_scoped_binary scope f x y;
        lemma_scoped_binary scope g u v;
        assert (f = R.eq_decl (get_sort x));
        V.lemma_sort_eq (get_sort y) (get_sort x);
        V.lemma_sort_eq (get_sort u) (get_sort x);
        V.lemma_sort_eq (get_sort v) (get_sort x);
        lemma_congruent s bc eq other scope rho arithmetic search_atoms (fuel - 1) x v;
        lemma_congruent s bc eq other scope rho arithmetic search_atoms (fuel - 1) y u;
        T.lemma_equality_at s bc eq other scope rho x y;
        T.lemma_equality_at s bc eq other scope rho u v;
        T.lemma_boolean s bc (T.evaluate_at s bc eq other scope rho a);
        T.lemma_boolean s bc (T.evaluate_at s bc eq other scope rho b)
      | [c; x; y], [d; u; v] ->
        lemma_scoped_ternary scope f c x y;
        lemma_scoped_ternary scope g d u v;
        assert (T.classify f = T.Choice (get_sort x));
        assert (f = T.ite_decl (get_sort x));
        V.lemma_sort_eq (get_sort c) bool_sort;
        V.lemma_sort_eq (get_sort d) bool_sort;
        V.lemma_sort_eq (get_sort y) (get_sort x);
        V.lemma_sort_eq (get_sort u) (get_sort x);
        V.lemma_sort_eq (get_sort v) (get_sort x);
        lemma_congruent s bc eq other scope rho arithmetic search_atoms (fuel - 1) x v;
        lemma_congruent s bc eq other scope rho arithmetic search_atoms (fuel - 1) y u;
        T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 64 c;
        T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 64 d;
        lemma_propositional_g (T.truth_at s bc eq other scope rho) arithmetic true c d;
        assert (T.truth_at s bc eq other scope rho c <>
                T.truth_at s bc eq other scope rho d);
        T.lemma_evaluate_core_at s bc eq other scope rho f xs;
        T.lemma_evaluate_core_at s bc eq other scope rho f ys;
        assert_norm (T.evaluate_arguments_at s bc eq other scope rho [c; x; y]
                [bool_sort; get_sort x; get_sort x] ==
                [T.evaluate_at s bc eq other scope rho c;
                 T.evaluate_at s bc eq other scope rho x;
                 T.evaluate_at s bc eq other scope rho y]);
        assert_norm (T.evaluate_arguments_at s bc eq other scope rho [d; u; v]
                [bool_sort; get_sort x; get_sort x] ==
                [T.evaluate_at s bc eq other scope rho d;
                 T.evaluate_at s bc eq other scope rho u;
                 T.evaluate_at s bc eq other scope rho v])
      | _, _ -> ())
    | Quantifier k bs t body, Quantifier k' bs' t' body' ->
      if not (k = k' && bs = bs' && t = t' &&
              congruent arithmetic search_atoms (L.rev bs @ scope) (fuel - 1) body body') then
        lemma_congruent_boolean s bc eq other scope rho arithmetic search_atoms (fuel - 1) a b
      else (
      let pointwise (vs:V.arguments base (S.signature s) (L.rev bs))
        : Lemma (
            T.evaluate_at s bc eq other (L.rev bs @ scope)
              (V.extend (S.signature s) scope (L.rev bs) vs rho) body ==
            T.evaluate_at s bc eq other (L.rev bs @ scope)
              (V.extend (S.signature s) scope (L.rev bs) vs rho) body') =
        lemma_congruent s bc eq other (L.rev bs @ scope)
          (V.extend (S.signature s) scope (L.rev bs) vs rho) arithmetic search_atoms (fuel - 1) body body' in
      FStar.Classical.forall_intro pointwise;
      V.lemma_quantifier_congruence (S.signature s) (T.interpretation s bc eq other)
        scope rho k bs (get_sort body) body body')
    | _, _ -> lemma_congruent_boolean s bc eq other scope rho arithmetic search_atoms (fuel - 1) a b)

and lemma_congruent_arguments (#base:sort -> Type0) (s:S.checked_schema)
                              (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                              (other:V.interpretation base (S.signature s))
                              (scope:list sort) (rho:V.environment base (S.signature s) scope)
                              (arithmetic:bool) (search_atoms:bool) (fuel:nat) (xs ys:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args scope xs /\ D.scoped_args scope ys /\
                    sorts_match xs ss /\ sorts_match ys ss /\ congruent_arguments arithmetic search_atoms scope fuel xs ys)
          (ensures V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho xs ss ==
                   V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho ys ss)
          (decreases %[fuel; L.length xs + 1]) =
  match xs, ys, ss with
  | x :: rest, y :: tail, t :: remaining ->
    V.lemma_sort_eq (get_sort x) t;
    V.lemma_sort_eq (get_sort y) t;
    lemma_congruent s bc eq other scope rho arithmetic search_atoms fuel x y;
    lemma_congruent_arguments s bc eq other scope rho arithmetic search_atoms fuel rest tail remaining
  | _, _, _ -> ()

and lemma_congruent_boolean (#base:sort -> Type0) (s:S.checked_schema)
                           (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                           (other:V.interpretation base (S.signature s))
                           (scope:list sort) (rho:V.environment base (S.signature s) scope)
                           (arithmetic:bool) (search_atoms:bool) (fuel:nat) (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort /\
                    congruent_boolean arithmetic search_atoms scope fuel a b)
          (ensures T.evaluate_at s bc eq other scope rho a ==
                   T.evaluate_at s bc eq other scope rho b)
          (decreases %[fuel; 2]) =
  lemma_congruent_boolean_shape arithmetic search_atoms scope fuel a b;
  assert (N.shape_equal_by
    (congruent_atom arithmetic scope fuel)
    32 (N.normalize false (T.cut 64 a)) (N.normalize false (T.cut 64 b)));
  let same = congruent_atom arithmetic scope fuel in
  let atoms (x y:expr)
    : Lemma (same x y ==>
             T.truth_at s bc eq other scope rho x == T.truth_at s bc eq other scope rho y) =
    if same x y then lemma_congruent s bc eq other scope rho arithmetic false (atom_fuel fuel) x y in
  FStar.Classical.forall_intro_2 atoms;
  lemma_shape_equal_by_geval (T.truth_at s bc eq other scope rho) same
    32 (N.normalize false (T.cut 64 a)) (N.normalize false (T.cut 64 b));
  lemma_normalize_geval (T.truth_at s bc eq other scope rho) false (T.cut 64 a);
  lemma_normalize_geval (T.truth_at s bc eq other scope rho) false (T.cut 64 b);
  T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 64 a;
  T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 64 b;
  T.lemma_boolean s bc (T.evaluate_at s bc eq other scope rho a);
  T.lemma_boolean s bc (T.evaluate_at s bc eq other scope rho b)

let rec equal_core (s:S.checked_schema) (fuel:nat) (facts:list expr) (a b:expr)
  : Tot bool (decreases %[fuel; 0]) =
  D.scoped [] a && D.scoped [] b && get_sort a = get_sort b &&
  (a = b || congruent false true [] 64 a b || L.mem b (U.reachable 8 U.Equality (equations facts) [a]) ||
   (fuel > 0 &&
    (match a, b with
     | App f xs, App g ys -> f = g && equal_arguments_core s (fuel - 1) facts xs ys
     | _, _ -> false)) ||
   (match DT.normalize s 64 a, DT.normalize s 64 b with
    | Some x, Some y -> x = y
    | _, _ -> false))

and equal_arguments_core (s:S.checked_schema) (fuel:nat) (facts:list expr) (xs ys:list expr)
  : Tot bool (decreases %[fuel; L.length xs + 1]) =
  match xs, ys with
  | [], [] -> true
  | x :: rest, y :: tail -> equal_core s fuel facts x y && equal_arguments_core s fuel facts rest tail
  | _, _ -> false

let rec lemma_equal_core (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (fuel:nat) (facts:list expr) (a b:expr)
  : Lemma (requires T.truths s bc eq other facts /\ equal_core s fuel facts a b)
          (ensures T.same_value s bc eq other a b)
          (decreases %[fuel; 0]) =
  T.lemma_same_value s bc eq other a b;
  if a = b then ()
  else if congruent false true [] 64 a b then
    lemma_congruent s bc eq other [] (T.empty_environment (S.signature s)) false true 64 a b
  else if L.mem b (U.reachable 8 U.Equality (equations facts) [a]) then (
    T.lemma_same_value s bc eq other a a;
    lemma_equations s bc eq other facts;
    lemma_reachable s bc eq other 8 a (equations facts) [a];
    lemma_known_member s bc eq other a (U.reachable 8 U.Equality (equations facts) [a]) b)
  else
    let congruent =
      fuel > 0 &&
      (match a, b with
       | App f xs, App g ys -> f = g && equal_arguments_core s (fuel - 1) facts xs ys
       | _, _ -> false) in
    if not congruent then (
      DT.lemma_normalize s bc eq other 64 a (Some?.v (DT.normalize s 64 a));
      DT.lemma_normalize s bc eq other 64 b (Some?.v (DT.normalize s 64 b)))
    else
      (match a, b with
       | App f xs, App _ ys ->
         lemma_equal_arguments_core s bc eq other (fuel - 1) facts xs ys f.domain
       | _, _ -> ())

and lemma_equal_arguments_core (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (fuel:nat) (facts:list expr) (xs ys:list expr) (ss:list sort)
  : Lemma (requires T.truths s bc eq other facts /\
                    D.scoped_args [] xs /\ D.scoped_args [] ys /\
                    sorts_match xs ss /\ sorts_match ys ss /\
                    equal_arguments_core s fuel facts xs ys)
          (ensures T.evaluate_arguments s bc eq other xs ss == T.evaluate_arguments s bc eq other ys ss)
          (decreases %[fuel; L.length xs + 1]) =
  match xs, ys, ss with
  | x :: rest, y :: tail, t :: remaining ->
    V.lemma_sort_eq (get_sort x) t;
    V.lemma_sort_eq (get_sort y) t;
    lemma_equal_core s bc eq other fuel facts x y;
    T.lemma_same_value s bc eq other x y;
    lemma_equal_arguments_core s bc eq other fuel facts rest tail remaining
  | _, _, _ -> ()

let equal (s:S.checked_schema) (fuel:nat) (facts:list expr) (a b:expr) : bool =
  (* Preserve the original search before trying a separately bounded extension. *)
  if equal_core s fuel facts a b then true
  else if not (Some? (expression_budget 4096 a) && Some? (expression_budget 4096 b)) then false
  else D.scoped [] a && D.scoped [] b && congruent true true [] 64 a b

let lemma_equal (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (fuel:nat) (facts:list expr) (a b:expr)
  : Lemma (requires T.truths s bc eq other facts /\ equal s fuel facts a b)
          (ensures T.same_value s bc eq other a b) =
  if equal_core s fuel facts a b then lemma_equal_core s bc eq other fuel facts a b
  else (
    T.lemma_same_value s bc eq other a b;
    lemma_congruent s bc eq other [] (T.empty_environment (S.signature s)) true true 64 a b)

let rec lemma_replace (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (source target e:expr)
  : Lemma (requires T.same_value s bc eq other source target /\
                    get_sort source == get_sort target /\ D.scoped [] e)
          (ensures D.scoped [] (TN.replace source target e) /\
                   get_sort (TN.replace source target e) == get_sort e /\
                   T.evaluate s bc eq other (TN.replace source target e) == T.evaluate s bc eq other e)
          (decreases e) =
  T.lemma_same_value s bc eq other source target;
  if e = source then ()
  else match e with
  | App f args -> lemma_replace_args s bc eq other source target args f.domain
  | _ -> ()

and lemma_replace_args (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (source target:expr) (args:list expr) (ss:list sort)
  : Lemma (requires T.same_value s bc eq other source target /\
                    get_sort source == get_sort target /\
                    D.scoped_args [] args /\ sorts_match args ss)
          (ensures D.scoped_args [] (TN.replace_args source target args) /\
                   sorts_match (TN.replace_args source target args) ss /\
                   T.evaluate_arguments s bc eq other (TN.replace_args source target args) ss ==
                     T.evaluate_arguments s bc eq other args ss)
          (decreases args) =
  match args, ss with
  | e :: rest, t :: tail ->
    V.lemma_sort_eq (get_sort e) t;
    lemma_replace s bc eq other source target e;
    V.lemma_sort_eq (get_sort (TN.replace source target e)) t;
    lemma_replace_args s bc eq other source target rest tail
  | _, _ -> ()

let rec lemma_replace_facts (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                            (source target:expr) (facts:list expr)
  : Lemma (requires T.same_value s bc eq other source target /\
                    get_sort source == get_sort target /\ T.truths s bc eq other facts)
          (ensures T.truths s bc eq other (TN.replace_args source target facts))
          (decreases facts) =
  match facts with
  | [] -> ()
  | f :: rest ->
    lemma_replace s bc eq other source target f;
    lemma_replace_facts s bc eq other source target rest

let rec lemma_constructor_premise (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                  (facts:list expr) (source target:expr)
  : Lemma (requires T.truths s bc eq other facts /\
                    TN.constructor_premise facts == Some (source, target))
          (ensures T.same_value s bc eq other source target /\ get_sort source == get_sort target)
          (decreases facts) =
  match facts with
  | [] -> ()
  | e :: rest ->
    (match TN.constructor_replacement e with
     | Some _ ->
       (match e with
        | App _ [a; b] ->
          T.lemma_equality s bc eq other a b;
          T.lemma_same_value s bc eq other source target
        | _ -> ())
     | None -> lemma_constructor_premise s bc eq other rest source target)

let rec negative_atoms (facts:list expr) : Tot (list expr) (decreases facts) =
  match facts with
  | [] -> []
  | App f [arg] :: rest ->
    if T.classify f = T.Negation then arg :: negative_atoms rest else negative_atoms rest
  | _ :: rest -> negative_atoms rest

let negative_exhaustion (s:S.checked_schema) (facts:list expr) : bool =
  let atoms = negative_atoms facts in
  let clause = App (Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Disjunction atoms) atoms in
  D.scoped [] clause && DT.exhaustive s clause

let rec lemma_negative_atoms (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (facts:list expr)
  : Lemma (requires T.truths s bc eq other facts)
          (ensures not (B.geval_args (T.truth s bc eq other) B.Or (L.map B.Atom (negative_atoms facts))))
          (decreases facts) =
  match facts with
  | [] -> ()
  | App f [arg] :: rest ->
    if T.classify f = T.Negation then T.lemma_negation s bc eq other f arg;
    lemma_negative_atoms s bc eq other rest
  | _ :: rest -> lemma_negative_atoms s bc eq other rest

let lemma_negative_exhaustion (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (facts:list expr)
  : Lemma (requires T.truths s bc eq other facts /\ negative_exhaustion s facts)
          (ensures False) =
  let atoms = negative_atoms facts in
  let disjunction = Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Disjunction atoms in
  lemma_negative_atoms s bc eq other facts;
  DT.lemma_exhaustive s bc eq other (App disjunction atoms);
  T.lemma_nary s bc eq other disjunction atoms B.Or

let rec reconstruction_conflict (s:S.checked_schema) (facts remaining:list expr)
  : Tot bool (decreases remaining) =
  match remaining with
  | [] -> false
  | App f [arg] :: rest ->
    (T.classify f = T.Negation && DT.reconstruction_from s facts arg) ||
    reconstruction_conflict s facts rest
  | _ :: rest -> reconstruction_conflict s facts rest

let rec lemma_truth_scopes (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (facts:list expr)
  : Lemma (requires T.truths s bc eq other facts)
          (ensures D.scoped_args [] facts)
          (decreases facts) =
  match facts with [] -> () | _ :: rest -> lemma_truth_scopes s bc eq other rest

let rec lemma_reconstruction_conflict (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                      (facts remaining:list expr)
  : Lemma (requires T.truths s bc eq other facts /\ T.truths s bc eq other remaining /\
                    reconstruction_conflict s facts remaining)
          (ensures False)
          (decreases remaining) =
  match remaining with
  | [] -> ()
  | App f [arg] :: rest ->
    if T.classify f = T.Negation && DT.reconstruction_from s facts arg then (
      lemma_truth_scopes s bc eq other facts;
      T.lemma_negation s bc eq other f arg;
      DT.lemma_reconstruction_from s bc eq other facts arg)
    else lemma_reconstruction_conflict s bc eq other facts rest
  | _ :: rest -> lemma_reconstruction_conflict s bc eq other facts rest

let rec field_position (child:expr) (args:list expr)
  : Tot (option nat) (decreases args) =
  match args with
  | [] -> None
  | a :: rest ->
    if a = child then Some 0
    else match field_position child rest with Some n -> Some (n + 1) | None -> None

let rec lemma_field_position (child:expr) (args:list expr) (n:nat)
  : Lemma (requires field_position child args == Some n)
          (ensures n < L.length args /\ L.index args n == child)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    if a <> child then
      match field_position child rest with
      | Some k -> lemma_field_position child rest k
      | None -> ()

let rec lemma_sorts_match_length (args:list expr) (ss:list sort)
  : Lemma (requires sorts_match args ss)
          (ensures L.length args == L.length ss)
          (decreases args) =
  match args, ss with
  | _ :: rest, _ :: tail -> lemma_sorts_match_length rest tail
  | _, _ -> ()

let immediate_field (s:S.checked_schema) (parent child:expr) : bool =
  match parent with
  | App c args -> L.mem c (S.signature s) && Some? (field_position child args)
  | _ -> false

let lemma_immediate_field (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (parent child:expr)
  : Lemma (requires D.scoped [] parent /\ D.scoped [] child /\ immediate_field s parent child)
          (ensures T.evaluate s bc eq other parent =!= T.evaluate s bc eq other child) =
  match parent with
  | App c args ->
    let n = Some?.v (field_position child args) in
    lemma_field_position child args n;
    lemma_sorts_match_length args c.domain;
    DT.lemma_arguments_index s bc eq other args c.domain n;
    let xs = T.evaluate_arguments s bc eq other args c.domain in
    assert (T.evaluate s bc eq other parent == V.Constructor c xs);
    V.lemma_acyclic c xs n
  | _ -> ()

let cyclic_equation (s:S.checked_schema) (e:expr) : bool =
  D.scoped [] e &&
  (match e with
   | App f [a; b] ->
     f = R.eq_decl (get_sort a) && get_sort a = get_sort b &&
     (immediate_field s a b || immediate_field s b a)
   | _ -> false)

let rec cyclic_conflict (s:S.checked_schema) (facts:list expr) : Tot bool (decreases facts) =
  match facts with
  | [] -> false
  | e :: rest -> cyclic_equation s e || cyclic_conflict s rest

let lemma_cyclic_equation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (e:expr)
  : Lemma (requires T.truth s bc eq other e /\ cyclic_equation s e)
          (ensures False) =
  match e with
  | App _ [a; b] ->
    T.lemma_equality s bc eq other a b;
    if immediate_field s a b then lemma_immediate_field s bc eq other a b
    else lemma_immediate_field s bc eq other b a
  | _ -> ()

let rec lemma_cyclic_conflict (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (facts:list expr)
  : Lemma (requires T.truths s bc eq other facts /\ cyclic_conflict s facts)
          (ensures False)
          (decreases facts) =
  match facts with
  | [] -> ()
  | e :: rest ->
    if cyclic_equation s e then lemma_cyclic_equation s bc eq other e
    else lemma_cyclic_conflict s bc eq other rest

let equality_consequence (s:S.checked_schema) (facts:list expr) (conclusion:expr) : bool =
  match conclusion with
   | App f [a; b] -> f = R.eq_decl (get_sort a) && equal s 8 facts a b
   | _ -> false

let quantifier_equality (conclusion:expr) : bool =
  match conclusion with
  | App f [Quantifier k bs t a; Quantifier k' bs' _ b] ->
    f = R.eq_decl t && k = k' && bs = bs' &&
    get_sort a = bool_sort && get_sort b = bool_sort &&
    DT.propositional (B.Eq (T.cut 64 a) (T.cut 64 b))
  | _ -> false

let lemma_scoped_quantifier_pair (f:func_decl) (k k':quantifier_kind) (bs bs':list sort) (t t':sort) (a b:expr)
  : Lemma (requires D.scoped [] (App f [Quantifier k bs t a; Quantifier k' bs' t' b]))
          (ensures D.scoped [] (Quantifier k bs t a) /\ D.scoped [] (Quantifier k' bs' t' b) /\
                   D.scoped (L.rev bs @ []) a /\ D.scoped (L.rev bs' @ []) b) =
  assert (D.scoped_args [] [Quantifier k bs t a; Quantifier k' bs' t' b]);
  assert (D.scoped_args [] [Quantifier k' bs' t' b])

let lemma_quantifier_equality (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (conclusion:expr)
  : Lemma (requires D.scoped [] conclusion /\ quantifier_equality conclusion)
          (ensures T.truth s bc eq other conclusion) =
  match conclusion with
  | App f [Quantifier k bs t a; Quantifier k' bs' t' b] ->
    lemma_scoped_quantifier_pair f k k' bs bs' t t' a b;
    let sigma = S.signature s in
    let scope = L.rev bs in
    let body_scope = L.append scope [] in
    let rho = T.empty_environment sigma in
    let left (vs:V.arguments base sigma scope) =
      T.evaluate_at s bc eq other body_scope (V.extend sigma [] scope vs rho) a in
    let right (vs:V.arguments base sigma scope) =
      T.evaluate_at s bc eq other body_scope (V.extend sigma [] scope vs rho) b in
    let pointwise (vs:V.arguments base sigma scope)
      : Lemma (left vs == right vs) =
      let bound = V.extend sigma [] scope vs rho in
      T.lemma_cut_with_boundaries_at s bc eq other body_scope bound [] 64 a;
      T.lemma_cut_with_boundaries_at s bc eq other body_scope bound [] 64 b;
      DT.lemma_propositional_g (T.truth_at s bc eq other body_scope bound)
        (B.Eq (T.cut 64 a) (T.cut 64 b));
      T.lemma_boolean s bc (left vs);
      T.lemma_boolean s bc (right vs)
    in
    FStar.Classical.forall_intro pointwise;
    V.lemma_quantifier_congruence sigma (T.interpretation s bc eq other)
      [] rho k bs bool_sort a b;
    T.lemma_equality s bc eq other (Quantifier k bs t a) (Quantifier k' bs' t' b)
  | _ -> ()

(* ---------------------------------------------------------------------- *)
(* Int equality/order laws: the producer's triangle clauses and implied    *)
(* equalities over two Int terms x and y (arith_eq_adapter: x = y gives    *)
(* x <= y and x >= y, directly or on x + (-1)*y or (-1)*y + x against 0,  *)
(* and the two bounds give x = y back). x and y are any Int terms, read    *)
(* only as their typed scalar values in the same Sorted interpretation: an *)
(* opaque application, a nonlinear product or a sum is one value, matched  *)
(* by expression identity and never linearized. Formula-based, so the rule *)
(* label is never read.                                                    *)
(* ---------------------------------------------------------------------- *)

(* The operands l and r of an Int comparison read against the pair (x, y):
   l - r is x - y (Some true) or y - x (Some false), either directly or as a
   difference (AR.difference, either addition operand order) compared with
   the numeral 0. *)
let offset (x y l r:expr) : option bool =
  if l = x && r = y then Some true
  else if l = y && r = x then Some false
  else if not (AR.int_numeral 0 r) then None
  else match AR.difference l with
  | Some (a, b) ->
    if a = x && b = y then Some true
    else if a = y && b = x then Some false
    else None
  | None -> None

(* An equation x = y at Int (the canonical equality). *)
let int_equation (e:expr) : option (expr & expr) =
  match e with
  | App f [x; y] -> if f = R.eq_decl LA.int_s then Some (x, y) else None
  | _ -> None

(* An Int comparison l <= r, l >= r or l = r with l - r = +-(x - y): every
   equal pair x, y satisfies it. *)
let implied_by_equation (x y c:expr) : bool =
  match LA.comparison c with
  | Some (rel, l, r) ->
    get_sort l = LA.int_s && (rel = LA.Le || rel = LA.Ge || rel = LA.Eq) && Some? (offset x y l r)
  | None -> false

(* An Int comparison read as a bound on x - y: Some true for x - y <= 0,
   Some false for x - y >= 0. *)
let bound (x y c:expr) : option bool =
  match LA.comparison c with
  | Some (rel, l, r) ->
    if get_sort l <> LA.int_s then None
    else (match offset x y l r with
          | Some sign -> if rel = LA.Le then Some sign else if rel = LA.Ge then Some (not sign) else None
          | None -> None)
  | None -> None

let negated (e:expr) : option expr =
  match e with App f [a] -> if T.classify f = T.Negation then Some a else None | _ -> None

(* not (x = y) \/ c, c implied by x = y. *)
let equation_order (ne c:expr) : bool =
  match negated ne with
  | Some e -> (match int_equation e with Some (x, y) -> implied_by_equation x y c | None -> false)
  | None -> false

(* (x = y) \/ not c1 \/ not c2, c1 and c2 opposite bounds on x - y. *)
let antisymmetric (e n1 n2:expr) : bool =
  match int_equation e, negated n1, negated n2 with
  | Some (x, y), Some c1, Some c2 ->
    (match bound x y c1, bound x y c2 with
     | Some u1, Some u2 -> u1 <> u2
     | _, _ -> false)
  | _, _, _ -> false

(* The two- and three-literal clauses, literals in any order. *)
let order_clause (conclusion:expr) : bool =
  match DT.literals conclusion with
  | [a; b] -> equation_order a b || equation_order b a
  | [a; b; c] -> antisymmetric a b c || antisymmetric b a c || antisymmetric c a b
  | _ -> false

let rec has_bound (x y:expr) (upper:bool) (facts:list expr) : Tot bool (decreases facts) =
  match facts with
  | [] -> false
  | e :: rest -> bound x y e = Some upper || has_bound x y upper rest

(* x = y from an upper and a lower bound on x - y among the facts. *)
let order_equation (facts:list expr) (conclusion:expr) : bool =
  match int_equation conclusion with
  | Some (x, y) -> has_bound x y true facts && has_bound x y false facts
  | None -> false

let integer_value (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (e:expr) : GTot int =
  AR.integer s bc eq other [] (T.empty_environment (S.signature s)) e

let lemma_offset (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                 (x y l r:expr) (sign:bool)
  : Lemma (requires D.scoped [] l /\ D.scoped [] r /\ offset x y l r == Some sign)
          (ensures integer_value s bc eq other l - integer_value s bc eq other r ==
                   (if sign then integer_value s bc eq other x - integer_value s bc eq other y
                    else integer_value s bc eq other y - integer_value s bc eq other x)) =
  if l = x && r = y then ()
  else if l = y && r = x then ()
  else (
    let rho = T.empty_environment (S.signature s) in
    AR.lemma_int_numeral s bc eq other [] rho 0 r;
    match AR.difference l with
    | Some (a, b) -> AR.lemma_difference s bc eq other [] rho l a b
    | None -> ())

let lemma_equation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (e x y:expr)
  : Lemma (requires D.scoped [] e /\ int_equation e == Some (x, y))
          (ensures D.scoped [] x /\ D.scoped [] y /\ get_sort x == LA.int_s /\ get_sort y == LA.int_s /\
                   (T.truth s bc eq other e <==>
                    integer_value s bc eq other x == integer_value s bc eq other y)) =
  match e with
  | App f [_; _] ->
    V.lemma_sort_eq (get_sort x) LA.int_s;
    V.lemma_sort_eq (get_sort y) LA.int_s;
    T.lemma_equality s bc eq other x y;
    AR.lemma_integer_equality s bc eq other [] (T.empty_environment (S.signature s)) x y
  | _ -> ()

let lemma_negated (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (e a:expr)
  : Lemma (requires D.scoped [] e /\ negated e == Some a)
          (ensures D.scoped [] a /\ T.truth s bc eq other e == not (T.truth s bc eq other a)) =
  match e with
  | App f [_] -> T.lemma_negation s bc eq other f a
  | _ -> ()

let lemma_implied_by_equation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (x y c:expr)
  : Lemma (requires D.scoped [] c /\ implied_by_equation x y c /\
                    integer_value s bc eq other x == integer_value s bc eq other y)
          (ensures T.truth s bc eq other c) =
  match LA.comparison c with
  | Some (rel, l, r) ->
    AR.lemma_int_comparison s bc eq other [] (T.empty_environment (S.signature s)) c rel l r;
    lemma_offset s bc eq other x y l r (Some?.v (offset x y l r))
  | None -> ()

let lemma_bound (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (x y c:expr) (upper:bool)
  : Lemma (requires D.scoped [] c /\ bound x y c == Some upper /\ T.truth s bc eq other c)
          (ensures (if upper then integer_value s bc eq other x <= integer_value s bc eq other y
                    else integer_value s bc eq other y <= integer_value s bc eq other x)) =
  match LA.comparison c with
  | Some (rel, l, r) ->
    AR.lemma_int_comparison s bc eq other [] (T.empty_environment (S.signature s)) c rel l r;
    lemma_offset s bc eq other x y l r (Some?.v (offset x y l r))
  | None -> ()

(* A true literal of a clause makes the clause true. *)
let lemma_clause_member (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (conclusion lit:expr)
  : Lemma (requires D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    L.mem lit (DT.literals conclusion) /\ T.truth s bc eq other lit)
          (ensures T.truth s bc eq other conclusion) =
  DT.lemma_literal_member (T.truth s bc eq other) (DT.literals conclusion) lit;
  DT.lemma_literals s bc eq other conclusion

let rec lemma_literals_scoped (es:list expr) (e:expr)
  : Lemma (requires D.scoped_args [] es /\ L.mem e es) (ensures D.scoped [] e) (decreases es) =
  match es with [] -> () | d :: rest -> if d <> e then lemma_literals_scoped rest e

let lemma_literals_of (conclusion:expr)
  : Lemma (requires D.scoped [] conclusion)
          (ensures D.scoped_args [] (DT.literals conclusion)) =
  match conclusion with
  | App f es -> ()
  | _ -> ()

let lemma_equation_order (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (conclusion ne c:expr)
  : Lemma (requires D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    L.mem ne (DT.literals conclusion) /\ L.mem c (DT.literals conclusion) /\
                    equation_order ne c)
          (ensures T.truth s bc eq other conclusion) =
  lemma_literals_of conclusion;
  lemma_literals_scoped (DT.literals conclusion) ne;
  lemma_literals_scoped (DT.literals conclusion) c;
  let e = Some?.v (negated ne) in
  lemma_negated s bc eq other ne e;
  let x, y = Some?.v (int_equation e) in
  lemma_equation s bc eq other e x y;
  if T.truth s bc eq other ne then lemma_clause_member s bc eq other conclusion ne
  else (
    lemma_implied_by_equation s bc eq other x y c;
    lemma_clause_member s bc eq other conclusion c)

let lemma_antisymmetric (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (conclusion e n1 n2:expr)
  : Lemma (requires D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    L.mem e (DT.literals conclusion) /\ L.mem n1 (DT.literals conclusion) /\
                    L.mem n2 (DT.literals conclusion) /\ antisymmetric e n1 n2)
          (ensures T.truth s bc eq other conclusion) =
  lemma_literals_of conclusion;
  lemma_literals_scoped (DT.literals conclusion) e;
  lemma_literals_scoped (DT.literals conclusion) n1;
  lemma_literals_scoped (DT.literals conclusion) n2;
  let x, y = Some?.v (int_equation e) in
  let c1 = Some?.v (negated n1) in
  let c2 = Some?.v (negated n2) in
  lemma_equation s bc eq other e x y;
  lemma_negated s bc eq other n1 c1;
  lemma_negated s bc eq other n2 c2;
  if T.truth s bc eq other n1 then lemma_clause_member s bc eq other conclusion n1
  else if T.truth s bc eq other n2 then lemma_clause_member s bc eq other conclusion n2
  else (
    lemma_bound s bc eq other x y c1 (Some?.v (bound x y c1));
    lemma_bound s bc eq other x y c2 (Some?.v (bound x y c2));
    lemma_clause_member s bc eq other conclusion e)

let lemma_order_clause (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (conclusion:expr)
  : Lemma (requires D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\ order_clause conclusion)
          (ensures T.truth s bc eq other conclusion) =
  match DT.literals conclusion with
  | [a; b] ->
    if equation_order a b then lemma_equation_order s bc eq other conclusion a b
    else lemma_equation_order s bc eq other conclusion b a
  | [a; b; c] ->
    if antisymmetric a b c then lemma_antisymmetric s bc eq other conclusion a b c
    else if antisymmetric b a c then lemma_antisymmetric s bc eq other conclusion b a c
    else lemma_antisymmetric s bc eq other conclusion c a b
  | _ -> ()

let rec lemma_has_bound (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (x y:expr) (upper:bool) (facts:list expr)
  : Lemma (requires T.truths s bc eq other facts /\ has_bound x y upper facts)
          (ensures (if upper then integer_value s bc eq other x <= integer_value s bc eq other y
                    else integer_value s bc eq other y <= integer_value s bc eq other x))
          (decreases facts) =
  match facts with
  | [] -> ()
  | e :: rest ->
    if bound x y e = Some upper then lemma_bound s bc eq other x y e upper
    else lemma_has_bound s bc eq other x y upper rest

let lemma_order_equation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc eq other facts /\ D.scoped [] conclusion /\ order_equation facts conclusion)
          (ensures T.truth s bc eq other conclusion) =
  let x, y = Some?.v (int_equation conclusion) in
  lemma_equation s bc eq other conclusion x y;
  lemma_has_bound s bc eq other x y true facts;
  lemma_has_bound s bc eq other x y false facts

(* ---------------------------------------------------------------------- *)
(* Real equality/order laws: the Real mirror of the Int clauses above       *)
(* ---------------------------------------------------------------------- *)

(* The same producer clauses over two Real terms x and y (arith_eq_adapter:
   not (x = y) \/ c with c = x <= y, x >= y, x = y, or any of them on
   x + (-1)*y or (-1)*y + x against 0, and (x = y) \/ not c1 \/ not c2 with
   c1 and c2 opposite bounds on x - y). The equation is the canonical Real
   equality and the comparisons and operands are the canonical Real ones
   (Z3SortedRealLinear.real_equation, real_offset, real_bound: exact
   declaration identity, never a name). x and y are read only as their typed
   Real values in the same Sorted interpretation and matched by expression
   identity: an opaque application, a nonlinear product, a quotient or a
   to_real is one value, and nothing is linearized or searched. Strict
   comparisons are not implied by an equation and are no bound. The literals
   are at most three and the clause must be shallow (Z3NnfReplay.shallow)
   before any comparison. Formula-based like the Int check, so the rule label
   is never read; the laws it reads are the Sorted Real laws. *)

(* not (x = y) \/ c, c implied by x = y. *)
let real_equation_order (ne c:expr) : bool =
  match negated ne with
  | Some e ->
    (match LIN.real_equation e with
     | Some (x, y) -> RO.real_implied_by_equation x y c
     | None -> false)
  | None -> false

(* (x = y) \/ not c1 \/ not c2, c1 and c2 opposite bounds on x - y. *)
let real_antisymmetric (e n1 n2:expr) : bool =
  match LIN.real_equation e, negated n1, negated n2 with
  | Some (x, y), Some c1, Some c2 ->
    (match RO.real_bound x y c1, RO.real_bound x y c2 with
     | Some u1, Some u2 -> u1 <> u2
     | _, _ -> false)
  | _, _, _ -> false

(* The two- and three-literal clauses, literals in any order. *)
let real_order_clause (conclusion:expr) : bool =
  match DT.literals conclusion with
  | [a; b] -> NR.shallow conclusion && (real_equation_order a b || real_equation_order b a)
  | [a; b; c] ->
    NR.shallow conclusion &&
    (real_antisymmetric a b c || real_antisymmetric b a c || real_antisymmetric c a b)
  | _ -> false

(* A closed Real equation, read at the Real values of its sides. *)
let lemma_real_equation_sides (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (reals:RL.carrier base) (e x y:expr)
  : Lemma (requires RL.real_laws s bc eq other reals /\ D.scoped [] e /\ LIN.real_equation e == Some (x, y))
          (ensures D.scoped [] x /\ D.scoped [] y /\ get_sort x == LA.real_s /\
                   (T.truth s bc eq other e <==>
                    RL.real_at s bc eq other reals [] (T.empty_environment (S.signature s)) x ==
                    RL.real_at s bc eq other reals [] (T.empty_environment (S.signature s)) y)) =
  let rho = T.empty_environment (S.signature s) in
  LIN.lemma_comparison s bc eq other reals [] rho e x y LA.Eq;
  RO.lemma_numeric_at_real s bc eq other reals [] rho x;
  RO.lemma_numeric_at_real s bc eq other reals [] rho y

let lemma_real_equation_order (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (reals:RL.carrier base) (conclusion ne c:expr)
  : Lemma (requires RL.real_laws s bc eq other reals /\ D.scoped [] conclusion /\
                    get_sort conclusion == bool_sort /\
                    L.mem ne (DT.literals conclusion) /\ L.mem c (DT.literals conclusion) /\
                    real_equation_order ne c)
          (ensures T.truth s bc eq other conclusion) =
  lemma_literals_of conclusion;
  lemma_literals_scoped (DT.literals conclusion) ne;
  lemma_literals_scoped (DT.literals conclusion) c;
  let e = Some?.v (negated ne) in
  lemma_negated s bc eq other ne e;
  let x, y = Some?.v (LIN.real_equation e) in
  lemma_real_equation_sides s bc eq other reals e x y;
  if T.truth s bc eq other ne then lemma_clause_member s bc eq other conclusion ne
  else (
    RO.lemma_real_implied_by_equation s bc eq other reals [] (T.empty_environment (S.signature s)) x y c;
    lemma_clause_member s bc eq other conclusion c)

let lemma_real_antisymmetric (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (reals:RL.carrier base) (conclusion e n1 n2:expr)
  : Lemma (requires RL.real_laws s bc eq other reals /\ D.scoped [] conclusion /\
                    get_sort conclusion == bool_sort /\
                    L.mem e (DT.literals conclusion) /\ L.mem n1 (DT.literals conclusion) /\
                    L.mem n2 (DT.literals conclusion) /\ real_antisymmetric e n1 n2)
          (ensures T.truth s bc eq other conclusion) =
  lemma_literals_of conclusion;
  lemma_literals_scoped (DT.literals conclusion) e;
  lemma_literals_scoped (DT.literals conclusion) n1;
  lemma_literals_scoped (DT.literals conclusion) n2;
  let x, y = Some?.v (LIN.real_equation e) in
  let c1 = Some?.v (negated n1) in
  let c2 = Some?.v (negated n2) in
  lemma_real_equation_sides s bc eq other reals e x y;
  lemma_negated s bc eq other n1 c1;
  lemma_negated s bc eq other n2 c2;
  if T.truth s bc eq other n1 then lemma_clause_member s bc eq other conclusion n1
  else if T.truth s bc eq other n2 then lemma_clause_member s bc eq other conclusion n2
  else (
    let rho = T.empty_environment (S.signature s) in
    RO.lemma_real_bound s bc eq other reals [] rho x y c1 (Some?.v (RO.real_bound x y c1));
    RO.lemma_real_bound s bc eq other reals [] rho x y c2 (Some?.v (RO.real_bound x y c2));
    lemma_clause_member s bc eq other conclusion e)

let lemma_real_order_clause (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                            (reals:RL.carrier base) (conclusion:expr)
  : Lemma (requires RL.real_laws s bc eq other reals /\ D.scoped [] conclusion /\
                    get_sort conclusion == bool_sort /\ real_order_clause conclusion)
          (ensures T.truth s bc eq other conclusion) =
  match DT.literals conclusion with
  | [a; b] ->
    if real_equation_order a b then lemma_real_equation_order s bc eq other reals conclusion a b
    else lemma_real_equation_order s bc eq other reals conclusion b a
  | [a; b; c] ->
    if real_antisymmetric a b c then lemma_real_antisymmetric s bc eq other reals conclusion a b c
    else if real_antisymmetric b a c then lemma_real_antisymmetric s bc eq other reals conclusion b a c
    else lemma_real_antisymmetric s bc eq other reals conclusion c a b
  | _ -> ()

(* ---------------------------------------------------------------------- *)
(* Guarded Int div/mod clauses                                              *)
(* ---------------------------------------------------------------------- *)

(* z3's arithmetic div/mod axioms for a non-numeral divisor d, as the
   producer states them (premise-free th-lemma clauses), over any two Int
   terms x and d, with q = div x d and m = mod x d the CANONICAL declarations
   (Z3SortedIntDivision.classify: exact name, kind tag, domain, range and
   parameters, never a name alone):

     d = 0   \/ m >= 0
     d <= 0  \/ m + (-1)*d <= -1        (AR.difference: either operand order)
     d >= 0  \/ m + d <= -1
     d = 0   \/ x = d*q + m             (and the sides of the equation swapped)

   with the guard against the canonical Int numeral 0, the bound against the
   canonical Int numeral -1, + and * the canonical Int operators (two
   operands) and the guard's d the very d of the division. x and d are read
   only as their typed Int values in the same Sorted interpretation, matched
   by expression identity: an opaque application, a datatype accessor or a
   product is one value. Each clause is a theorem of every Sorted model
   satisfying the division laws (Z3SortedIntDivision.division_laws: the
   Euclidean quotient and remainder at a NONZERO divisor, nothing at zero),
   because the guard is false exactly where the divisor is nonzero (and of the
   sign the bound needs); a clause with another guard, bound, operand order
   or declaration is not recognized. The unguarded identity of a division
   with its div0/mod0 alias is not a clause of this shape and is not proved.
   The clause is two literals and must be shallow (Z3NnfReplay.shallow)
   before any comparison. Formula-based like the Int and Real order clauses,
   so the rule label is never read. *)

(* d = 0 \/ mod x d >= 0 *)
let remainder_lower (guard body:expr) : bool =
  match LA.comparison body with
  | Some (LA.Ge, m, z) ->
    get_sort m = LA.int_s && AR.int_numeral 0 z &&
    (match DV.remainder_arguments m with
     | Some (_, d) -> DV.zero_guard d guard
     | None -> false)
  | _ -> false

(* d <= 0 \/ (mod x d) + (-1)*d <= -1 *)
let remainder_upper_positive (guard body:expr) : bool =
  match LA.comparison body with
  | Some (LA.Le, l, r) ->
    get_sort l = LA.int_s && AR.int_numeral (-1) r &&
    (match AR.difference l with
     | Some (m, d) ->
       (match DV.remainder_arguments m with
        | Some (_, d') -> d' = d && DV.sign_guard LA.Le d guard
        | None -> false)
     | None -> false)
  | _ -> false

(* d >= 0 \/ (mod x d) + d <= -1 *)
let remainder_upper_negative (guard body:expr) : bool =
  match LA.comparison body with
  | Some (LA.Le, l, r) ->
    get_sort l = LA.int_s && AR.int_numeral (-1) r &&
    (match l with
     | App f [m; d] ->
       SI.classify f = SI.Calculate LA.Add &&
       (match DV.remainder_arguments m with
        | Some (_, d') -> d' = d && DV.sign_guard LA.Ge d guard
        | None -> false)
     | _ -> false)
  | _ -> false

(* x = d*(div x d) + mod x d, read from the sum side `sum` and the plain side `x`. *)
let decomposed (x sum guard:expr) : bool =
  match sum with
  | App f [p; m] ->
    SI.classify f = SI.Calculate LA.Add &&
    (match p with
     | App g [d; q] ->
       SI.classify g = SI.Calculate LA.Mul && DV.quotient_arguments q = Some (x, d) &&
       DV.remainder_arguments m = Some (x, d) && DV.zero_guard d guard
     | _ -> false)
  | _ -> false

(* d = 0 \/ x = d*q + m, the equation in either orientation. *)
let remainder_decomposition (guard body:expr) : bool =
  match int_equation body with
  | Some (a, b) -> decomposed a b guard || decomposed b a guard
  | None -> false

let division_literals (guard body:expr) : bool =
  remainder_lower guard body || remainder_upper_positive guard body ||
  remainder_upper_negative guard body || remainder_decomposition guard body

(* The two-literal clause, literals in either order. *)
let division_clause (conclusion:expr) : bool =
  match DT.literals conclusion with
  | [a; b] -> NR.shallow conclusion && (division_literals a b || division_literals b a)
  | _ -> false

let lemma_remainder_lower (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (conclusion guard body:expr)
  : Lemma (requires DV.division_laws s bc eq other /\ D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    L.mem guard (DT.literals conclusion) /\ L.mem body (DT.literals conclusion) /\
                    remainder_lower guard body)
          (ensures T.truth s bc eq other conclusion) =
  lemma_literals_of conclusion;
  lemma_literals_scoped (DT.literals conclusion) guard;
  lemma_literals_scoped (DT.literals conclusion) body;
  let rho = T.empty_environment (S.signature s) in
  match LA.comparison body with
  | Some (LA.Ge, m, z) ->
    AR.lemma_int_comparison s bc eq other [] rho body LA.Ge m z;
    AR.lemma_int_numeral s bc eq other [] rho 0 z;
    let x, d = Some?.v (DV.remainder_arguments m) in
    DV.lemma_zero_guard s bc eq other [] rho d guard;
    DV.lemma_remainder_arguments s bc eq other [] rho m x d;
    if T.truth s bc eq other guard then lemma_clause_member s bc eq other conclusion guard
    else (
      DV.lemma_euclid (integer_value s bc eq other x) (integer_value s bc eq other d);
      lemma_clause_member s bc eq other conclusion body)
  | _ -> ()

let lemma_remainder_upper_positive (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                   (conclusion guard body:expr)
  : Lemma (requires DV.division_laws s bc eq other /\ D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    L.mem guard (DT.literals conclusion) /\ L.mem body (DT.literals conclusion) /\
                    remainder_upper_positive guard body)
          (ensures T.truth s bc eq other conclusion) =
  lemma_literals_of conclusion;
  lemma_literals_scoped (DT.literals conclusion) guard;
  lemma_literals_scoped (DT.literals conclusion) body;
  let rho = T.empty_environment (S.signature s) in
  match LA.comparison body with
  | Some (LA.Le, l, r) ->
    AR.lemma_int_comparison s bc eq other [] rho body LA.Le l r;
    AR.lemma_int_numeral s bc eq other [] rho (-1) r;
    let m, d = Some?.v (AR.difference l) in
    AR.lemma_difference s bc eq other [] rho l m d;
    let x, _ = Some?.v (DV.remainder_arguments m) in
    DV.lemma_sign_guard s bc eq other [] rho LA.Le d guard;
    DV.lemma_remainder_arguments s bc eq other [] rho m x d;
    if T.truth s bc eq other guard then lemma_clause_member s bc eq other conclusion guard
    else (
      DV.lemma_euclid (integer_value s bc eq other x) (integer_value s bc eq other d);
      lemma_clause_member s bc eq other conclusion body)
  | _ -> ()

let lemma_remainder_upper_negative (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                   (conclusion guard body:expr)
  : Lemma (requires DV.division_laws s bc eq other /\ D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    L.mem guard (DT.literals conclusion) /\ L.mem body (DT.literals conclusion) /\
                    remainder_upper_negative guard body)
          (ensures T.truth s bc eq other conclusion) =
  lemma_literals_of conclusion;
  lemma_literals_scoped (DT.literals conclusion) guard;
  lemma_literals_scoped (DT.literals conclusion) body;
  let rho = T.empty_environment (S.signature s) in
  match LA.comparison body with
  | Some (LA.Le, l, r) ->
    AR.lemma_int_comparison s bc eq other [] rho body LA.Le l r;
    AR.lemma_int_numeral s bc eq other [] rho (-1) r;
    (match l with
     | App f [m; d] ->
       AR.lemma_int_binary s bc eq other [] rho f m d LA.Add;
       let x, _ = Some?.v (DV.remainder_arguments m) in
       DV.lemma_sign_guard s bc eq other [] rho LA.Ge d guard;
       DV.lemma_remainder_arguments s bc eq other [] rho m x d;
       if T.truth s bc eq other guard then lemma_clause_member s bc eq other conclusion guard
       else (
         DV.lemma_euclid (integer_value s bc eq other x) (integer_value s bc eq other d);
         lemma_clause_member s bc eq other conclusion body)
     | _ -> ())
  | _ -> ()

let lemma_decomposed (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (x sum guard:expr)
  : Lemma (requires DV.division_laws s bc eq other /\ D.scoped [] sum /\ D.scoped [] guard /\
                    decomposed x sum guard /\ D.scoped [] x /\
                    ~(T.truth s bc eq other guard))
          (ensures integer_value s bc eq other x == integer_value s bc eq other sum) =
  let rho = T.empty_environment (S.signature s) in
  match sum with
  | App f [p; m] ->
    AR.lemma_int_binary s bc eq other [] rho f p m LA.Add;
    (match p with
     | App g [d; q] ->
       AR.lemma_int_binary s bc eq other [] rho g d q LA.Mul;
       DV.lemma_zero_guard s bc eq other [] rho d guard;
       DV.lemma_quotient_arguments s bc eq other [] rho q x d;
       DV.lemma_remainder_arguments s bc eq other [] rho m x d;
       DV.lemma_euclid (integer_value s bc eq other x) (integer_value s bc eq other d)
     | _ -> ())
  | _ -> ()

let lemma_remainder_decomposition (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                  (conclusion guard body:expr)
  : Lemma (requires DV.division_laws s bc eq other /\ D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    L.mem guard (DT.literals conclusion) /\ L.mem body (DT.literals conclusion) /\
                    remainder_decomposition guard body)
          (ensures T.truth s bc eq other conclusion) =
  lemma_literals_of conclusion;
  lemma_literals_scoped (DT.literals conclusion) guard;
  lemma_literals_scoped (DT.literals conclusion) body;
  match int_equation body with
  | Some (a, b) ->
    lemma_equation s bc eq other body a b;
    if T.truth s bc eq other guard then lemma_clause_member s bc eq other conclusion guard
    else (
      if decomposed a b guard then lemma_decomposed s bc eq other a b guard
      else lemma_decomposed s bc eq other b a guard;
      lemma_clause_member s bc eq other conclusion body)
  | None -> ()

let lemma_division_literals (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                            (conclusion guard body:expr)
  : Lemma (requires DV.division_laws s bc eq other /\ D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    L.mem guard (DT.literals conclusion) /\ L.mem body (DT.literals conclusion) /\
                    division_literals guard body)
          (ensures T.truth s bc eq other conclusion) =
  if remainder_lower guard body then lemma_remainder_lower s bc eq other conclusion guard body
  else if remainder_upper_positive guard body then lemma_remainder_upper_positive s bc eq other conclusion guard body
  else if remainder_upper_negative guard body then lemma_remainder_upper_negative s bc eq other conclusion guard body
  else lemma_remainder_decomposition s bc eq other conclusion guard body

let lemma_division_clause (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (conclusion:expr)
  : Lemma (requires DV.division_laws s bc eq other /\ D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    division_clause conclusion)
          (ensures T.truth s bc eq other conclusion) =
  match DT.literals conclusion with
  | [a; b] ->
    if division_literals a b then lemma_division_literals s bc eq other conclusion a b
    else lemma_division_literals s bc eq other conclusion b a
  | _ -> ()

(* ---------------------------------------------------------------------- *)
(* Term if-then-else branch clauses                                         *)
(* ---------------------------------------------------------------------- *)

(* The producer's two clauses of a term choice (smt_internalizer,
   internalize_ite_term): (not c) \/ t = (ite c t u) and c \/ u = (ite c t u).
   A theorem of the same Sorted interpretation: the canonical choice
   evaluates to the branch its condition selects and the canonical equality
   reflects that value. No symbol is introduced and the interpretation is not
   extended. Any branch sort, either equality orientation, either literal
   order. *)

(* lit holds exactly when c does not: lit is (not c), or c is (not lit). *)
let complement (lit c:expr) : bool =
  (match negated lit with Some a -> a = c | None -> false) ||
  (match negated c with Some a -> a = lit | None -> false)

(* lit \/ v = ch, ch the canonical choice (ite c t u) at the sort of its
   branches and v the branch the condition selects whenever lit is false:
   t when lit is the complement of c, u when lit is c itself. *)
let branch_equation (lit v ch:expr) : bool =
  match ch with
  | App g [c; t; u] ->
    T.classify g = T.Choice (get_sort t) &&
    ((v = t && complement lit c) || (v = u && lit = c))
  | _ -> false

(* The canonical equality of a branch and its choice, in either order. *)
let branch_literal (lit e:expr) : bool =
  match e with
  | App f [a; b] -> f = R.eq_decl (get_sort a) && (branch_equation lit a b || branch_equation lit b a)
  | _ -> false

let choice_clause (conclusion:expr) : bool =
  match DT.literals conclusion with
  | [a; b] -> branch_literal a b || branch_literal b a
  | _ -> false

let lemma_branch_equation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (lit v ch:expr)
  : Lemma (requires D.scoped [] lit /\ D.scoped [] ch /\ branch_equation lit v ch /\
                    not (T.truth s bc eq other lit))
          (ensures D.scoped [] v /\ get_sort ch == get_sort v /\
                   T.evaluate s bc eq other ch == T.evaluate s bc eq other v) =
  match ch with
  | App g [c; t; u] ->
    assert (g == T.ite_decl (get_sort t));
    V.lemma_sort_eq (get_sort c) bool_sort;
    V.lemma_sort_eq (get_sort u) (get_sort t);
    let rho = T.empty_environment (S.signature s) in
    T.lemma_evaluate_core_at s bc eq other [] rho g [c; t; u];
    assert_norm (T.evaluate_arguments_at s bc eq other [] rho [c; t; u] [bool_sort; get_sort t; get_sort t] ==
                 [T.evaluate_at s bc eq other [] rho c; T.evaluate_at s bc eq other [] rho t;
                  T.evaluate_at s bc eq other [] rho u]);
    (match negated lit with
     | Some a -> if a = c then lemma_negated s bc eq other lit a
     | None -> ());
    (match negated c with
     | Some a -> if a = lit then lemma_negated s bc eq other c a
     | None -> ())
  | _ -> ()

let lemma_branch_literal (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (lit e:expr)
  : Lemma (requires D.scoped [] lit /\ D.scoped [] e /\ branch_literal lit e /\
                    not (T.truth s bc eq other lit))
          (ensures T.truth s bc eq other e) =
  match e with
  | App f [a; b] ->
    V.lemma_sort_eq (get_sort b) (get_sort a);
    T.lemma_equality s bc eq other a b;
    if branch_equation lit a b then lemma_branch_equation s bc eq other lit a b
    else lemma_branch_equation s bc eq other lit b a
  | _ -> ()

let lemma_choice_clause (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (conclusion:expr)
  : Lemma (requires D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\ choice_clause conclusion)
          (ensures T.truth s bc eq other conclusion) =
  lemma_literals_of conclusion;
  match DT.literals conclusion with
  | [a; b] ->
    lemma_literals_scoped (DT.literals conclusion) a;
    lemma_literals_scoped (DT.literals conclusion) b;
    if T.truth s bc eq other a then lemma_clause_member s bc eq other conclusion a
    else if T.truth s bc eq other b then lemma_clause_member s bc eq other conclusion b
    else if branch_literal a b then lemma_branch_literal s bc eq other a b
    else lemma_branch_literal s bc eq other b a
  | _ -> ()

(* ---------------------------------------------------------------------- *)
(* Boolean or-gate definition clauses                                       *)
(* ---------------------------------------------------------------------- *)

(* The producer's clauses for a Boolean gate g = (or x1 ... xn), the
   def-axiom of an `or` subterm: or-intro (or g l), l the complement of a
   disjunct x_i, and or-elim (or (not g) x1 ... xn), the literals after
   (not g) exactly the disjuncts of g, in order. Tautologies of the same
   Sorted interpretation, checked structurally on the canonical or/not
   declarations (T.classify fixes their Boolean argument and result sorts)
   and exact expression identity. No cut, truth table or boundary search, so
   a gate whose shared disjunct the bounded propositional cut would read at
   two depths is still decided, linearly in the clause size. *)

(* The disjuncts of a canonical `or`. *)
let disjuncts (g:expr) : option (list expr) =
  match g with
  | App f xs -> if T.classify f = T.Nary B.Or then Some xs else None
  | _ -> None

let rec has_complement (l:expr) (xs:list expr) : Tot bool (decreases xs) =
  match xs with [] -> false | x :: rest -> complement l x || has_complement l rest

(* g \/ l, l the complement of some disjunct of g. *)
let or_intro (g l:expr) : bool =
  match disjuncts g with Some xs -> has_complement l xs | None -> false

(* (not g) \/ x1 \/ ... \/ xn, the literals after (not g) exactly the
   disjuncts of g. *)
let or_elim (lits:list expr) : bool =
  match lits with
  | n :: ys ->
    (match negated n with
     | Some g -> (match disjuncts g with Some xs -> xs = ys | None -> false)
     | None -> false)
  | [] -> false

let gate_clause (conclusion:expr) : bool =
  match DT.literals conclusion with
  | [a; b] -> or_intro a b || or_intro b a || or_elim [a; b]
  | lits -> or_elim lits

(* When l is false, the disjunct it complements is true, so the disjunction is. *)
let rec lemma_has_complement (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (l:expr) (xs:list expr)
  : Lemma (requires D.scoped [] l /\ D.scoped_args [] xs /\ has_complement l xs /\
                    not (T.truth s bc eq other l))
          (ensures B.geval_args (T.truth s bc eq other) B.Or (L.map B.Atom xs))
          (decreases xs) =
  match xs with
  | x :: rest ->
    if complement l x then (
      (match negated l with Some a -> if a = x then lemma_negated s bc eq other l a | None -> ());
      (match negated x with Some a -> if a = l then lemma_negated s bc eq other x a | None -> ());
      DT.lemma_literal_member (T.truth s bc eq other) xs x)
    else lemma_has_complement s bc eq other l rest
  | [] -> ()

let lemma_or_intro (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (conclusion g l:expr)
  : Lemma (requires D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    L.mem g (DT.literals conclusion) /\ L.mem l (DT.literals conclusion) /\ or_intro g l)
          (ensures T.truth s bc eq other conclusion) =
  lemma_literals_of conclusion;
  lemma_literals_scoped (DT.literals conclusion) g;
  lemma_literals_scoped (DT.literals conclusion) l;
  if T.truth s bc eq other l then lemma_clause_member s bc eq other conclusion l
  else match g with
  | App f xs ->
    lemma_has_complement s bc eq other l xs;
    T.lemma_nary s bc eq other f xs B.Or;
    lemma_clause_member s bc eq other conclusion g
  | _ -> ()

let lemma_or_elim (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (conclusion:expr)
  : Lemma (requires D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    or_elim (DT.literals conclusion))
          (ensures T.truth s bc eq other conclusion) =
  lemma_literals_of conclusion;
  DT.lemma_literals s bc eq other conclusion;
  match DT.literals conclusion with
  | n :: ys ->
    lemma_literals_scoped (DT.literals conclusion) n;
    let g = Some?.v (negated n) in
    lemma_negated s bc eq other n g;
    (match g with
     | App f xs -> T.lemma_nary s bc eq other f xs B.Or
     | _ -> ())
  | [] -> ()

let lemma_gate_clause (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (conclusion:expr)
  : Lemma (requires D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\ gate_clause conclusion)
          (ensures T.truth s bc eq other conclusion) =
  match DT.literals conclusion with
  | [a; b] ->
    if or_intro a b then lemma_or_intro s bc eq other conclusion a b
    else if or_intro b a then lemma_or_intro s bc eq other conclusion b a
    else lemma_or_elim s bc eq other conclusion
  | _ -> lemma_or_elim s bc eq other conclusion

let direct_consequence (s:S.checked_schema) (facts:list expr) (conclusion:expr) : bool =
  (D.scoped [] conclusion && get_sort conclusion = bool_sort && DT.simple_consequence facts conclusion) ||
  equality_consequence s facts conclusion ||
  (D.scoped [] conclusion && quantifier_equality conclusion) ||
  negative_exhaustion s facts || cyclic_conflict s facts || reconstruction_conflict s facts facts ||
  DT.consequence s facts conclusion ||
  (D.scoped [] conclusion && get_sort conclusion = bool_sort &&
   (order_clause conclusion || order_equation facts conclusion || choice_clause conclusion ||
    gate_clause conclusion))

let lemma_direct_consequence (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc eq other facts /\ direct_consequence s facts conclusion)
          (ensures T.truth s bc eq other conclusion) =
  if D.scoped [] conclusion && get_sort conclusion = bool_sort && DT.simple_consequence facts conclusion then
    DT.lemma_simple_consequence s bc eq other facts conclusion
  else if equality_consequence s facts conclusion then (
    match conclusion with
    | App _ [a; b] ->
      lemma_equal s bc eq other 8 facts a b;
      T.lemma_same_value s bc eq other a b;
      T.lemma_equality s bc eq other a b
    | _ -> ())
  else if D.scoped [] conclusion && quantifier_equality conclusion then
    lemma_quantifier_equality s bc eq other conclusion
  else if negative_exhaustion s facts then lemma_negative_exhaustion s bc eq other facts
  else if cyclic_conflict s facts then lemma_cyclic_conflict s bc eq other facts
  else if reconstruction_conflict s facts facts then lemma_reconstruction_conflict s bc eq other facts facts
  else if DT.consequence s facts conclusion then DT.lemma_consequence s bc eq other facts conclusion
  else if order_clause conclusion then lemma_order_clause s bc eq other conclusion
  else if order_equation facts conclusion then lemma_order_equation s bc eq other facts conclusion
  else if choice_clause conclusion then lemma_choice_clause s bc eq other conclusion
  else lemma_gate_clause s bc eq other conclusion

let rec propagate (s:S.checked_schema) (fuel:nat) (facts:list expr) (conclusion:expr)
  : Tot bool (decreases fuel) =
  if direct_consequence s facts conclusion then true
  else if fuel = 0 then false
  else let _ = assert (fuel > 0) in
  let next:nat = fuel - 1 in
  match TN.constructor_premise facts with
  | Some (source, target) ->
    propagate s next (TN.replace_args source target facts) (TN.replace source target conclusion)
  | None -> false

let rec lemma_propagate (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (fuel:nat) (facts:list expr) (conclusion:expr)
  : Lemma (requires D.scoped [] conclusion /\ T.truths s bc eq other facts /\
                    propagate s fuel facts conclusion)
          (ensures T.truth s bc eq other conclusion)
          (decreases fuel) =
  if direct_consequence s facts conclusion then lemma_direct_consequence s bc eq other facts conclusion
  else if fuel > 0 then
    match TN.constructor_premise facts with
    | Some (source, target) ->
      lemma_constructor_premise s bc eq other facts source target;
      lemma_replace_facts s bc eq other source target facts;
      lemma_replace s bc eq other source target conclusion;
      lemma_propagate s bc eq other (fuel - 1)
        (TN.replace_args source target facts) (TN.replace source target conclusion)
    | None -> ()

let consequence (s:S.checked_schema) (facts:list expr) (conclusion:expr) : bool =
  D.scoped_args [] facts && D.scoped [] conclusion && get_sort conclusion = bool_sort &&
  propagate s 8 facts conclusion

let lemma_consequence (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc eq other facts /\ consequence s facts conclusion)
          (ensures T.truth s bc eq other conclusion) =
  lemma_propagate s bc eq other 8 facts conclusion

let proposition (j:U.judgment) : expr =
  match j with
  | U.Holds e -> e
  | U.Equal a b | U.Observational a b -> R.mk_eq_expr a b

let declaration_in_context (s:S.checked_schema) (f:func_decl) : bool =
  if f.interp = Some Z3DatatypeLemma.op_constructor then Some? (S.case_of s.cases f)
  else if f.interp = Some Z3DatatypeLemma.op_recognizer then Some? (S.find_recognizer f s.cases)
  else if f.interp = Some Z3DatatypeLemma.op_accessor then Some? (S.find_accessor f s.cases)
  else true

let rec in_context (s:S.checked_schema) (e:expr) : Tot bool (decreases e) =
  match e with
  | App f es -> declaration_in_context s f && args_in_context s es
  | Quantifier _ _ _ body -> in_context s body
  | Var _ _ -> true

and args_in_context (s:S.checked_schema) (es:list expr) : Tot bool (decreases es) =
  match es with [] -> true | e :: rest -> in_context s e && args_in_context s rest

let boolean_expression (s:S.checked_schema) (e:expr) : bool =
  D.scoped [] e && get_sort e = bool_sort && in_context s e

let rec boolean_expressions (s:S.checked_schema) (es:list expr) : Tot bool (decreases es) =
  match es with [] -> true | e :: rest -> boolean_expression s e && boolean_expressions s rest

let fact_valid (s:S.checked_schema) (p:U.checked_fact) : bool =
  boolean_expression s (proposition p.conclusion) && boolean_expressions s p.hypotheses

let rec facts_valid (s:S.checked_schema) (ps:list U.checked_fact) : Tot bool (decreases ps) =
  match ps with [] -> true | p :: rest -> fact_valid s p && facts_valid s rest

let rec propositions (ps:list U.checked_fact) : Tot (list expr) (decreases ps) =
  match ps with [] -> [] | p :: rest -> proposition p.conclusion :: propositions rest

let implies_decl : func_decl = {
  decl_name = "=>"; domain = [bool_sort; bool_sort]; range = bool_sort;
  interp = Some Z3ValueTheory.op_implies; int_params = [];
}

let scoped_proposition (p:U.checked_fact) : expr =
  App implies_decl [
    App (Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Conjunction p.hypotheses) p.hypotheses;
    proposition p.conclusion]

let rec scoped_propositions (ps:list U.checked_fact) : Tot (list expr) (decreases ps) =
  match ps with [] -> [] | p :: rest -> scoped_proposition p :: scoped_propositions rest

let fact_holds (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
               (p:U.checked_fact) : GTot bool =
  not (T.truths s bc eq other p.hypotheses) || T.truth s bc eq other (proposition p.conclusion)

let rec facts_hold (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (ps:list U.checked_fact) : GTot bool (decreases ps) =
  match ps with [] -> true | p :: rest -> fact_holds s bc eq other p && facts_hold s bc eq other rest

let rec lemma_boolean_expressions (s:S.checked_schema) (es:list expr)
  : Lemma (requires boolean_expressions s es)
          (ensures D.scoped_args [] es /\
                   (forall (e:expr). L.mem e es ==> get_sort e == bool_sort))
          (decreases es) =
  match es with [] -> () | _ :: rest -> lemma_boolean_expressions s rest

let lemma_scoped_proposition (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (p:U.checked_fact)
  : Lemma (requires fact_valid s p)
          (ensures D.scoped [] (scoped_proposition p) /\
                   T.truth s bc eq other (scoped_proposition p) == fact_holds s bc eq other p) =
  lemma_boolean_expressions s p.hypotheses;
  DT.lemma_boolean_domain p.hypotheses;
  DT.lemma_conjunction s bc eq other p.hypotheses;
  T.lemma_truths s bc eq other p.hypotheses;
  T.lemma_evaluate_core s bc eq other implies_decl [
    App (Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Conjunction p.hypotheses) p.hypotheses;
    proposition p.conclusion]

let rec lemma_scoped_propositions (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                  (ps:list U.checked_fact)
  : Lemma (requires facts_valid s ps /\ facts_hold s bc eq other ps)
          (ensures T.truths s bc eq other (scoped_propositions ps))
          (decreases ps) =
  match ps with
  | [] -> ()
  | p :: rest ->
    lemma_scoped_proposition s bc eq other p;
    lemma_scoped_propositions s bc eq other rest

let rec lemma_truth_member (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (es:list expr) (e:expr)
  : Lemma (requires T.truths s bc eq other es /\ L.mem e es)
          (ensures T.truth s bc eq other e)
          (decreases es) =
  match es with [] -> () | x :: rest -> if x <> e then lemma_truth_member s bc eq other rest e

let rec lemma_hypothesis_union (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                               (xs ys:list expr)
  : Lemma (requires T.truths s bc eq other (U.add_hypotheses xs ys))
          (ensures T.truths s bc eq other xs /\ T.truths s bc eq other ys)
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest ->
    if L.mem x ys then (
      lemma_hypothesis_union s bc eq other rest ys;
      lemma_truth_member s bc eq other ys x)
    else lemma_hypothesis_union s bc eq other rest (x :: ys)

let rec lemma_premise_hypotheses (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                 (ps:list U.checked_fact)
  : Lemma (requires facts_hold s bc eq other ps /\
                    T.truths s bc eq other (U.premise_hypotheses ps))
          (ensures T.truths s bc eq other (propositions ps))
          (decreases ps) =
  match ps with
  | [] -> ()
  | p :: rest ->
    lemma_hypothesis_union s bc eq other p.hypotheses (U.premise_hypotheses rest);
    lemma_premise_hypotheses s bc eq other rest

let rec remaining_hypotheses (hyps:list expr) (conclusion:expr)
  : Tot (list expr) (decreases hyps) =
  match hyps with
  | [] -> []
  | h :: rest ->
    if DT.eliminated (conclusion :: DT.literals conclusion) h then remaining_hypotheses rest conclusion
    else h :: remaining_hypotheses rest conclusion

let lemma_discharged (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (h conclusion:expr)
  : Lemma (requires boolean_expression s h /\ boolean_expression s conclusion /\
                    not (T.truth s bc eq other conclusion) /\
                    DT.eliminated (conclusion :: DT.literals conclusion) h)
          (ensures T.truth s bc eq other h) =
  DT.lemma_literals s bc eq other conclusion;
  let clause = conclusion :: DT.literals conclusion in
  if L.mem (R.mk_not_expr h) clause then (
    if T.truth s bc eq other (R.mk_not_expr h) then
      DT.lemma_literal_member (T.truth s bc eq other) clause (R.mk_not_expr h);
    T.lemma_negation s bc eq other R.not_decl h)
  else match h with
  | App f [a] ->
    if T.truth s bc eq other a then DT.lemma_literal_member (T.truth s bc eq other) clause a;
    T.lemma_negation s bc eq other f a
  | _ -> ()

let rec lemma_remaining_hypotheses (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                   (hyps:list expr) (conclusion:expr)
  : Lemma (requires boolean_expressions s hyps /\ boolean_expression s conclusion /\
                    not (T.truth s bc eq other conclusion) /\
                    T.truths s bc eq other (remaining_hypotheses hyps conclusion))
          (ensures T.truths s bc eq other hyps)
          (decreases hyps) =
  match hyps with
  | [] -> ()
  | h :: rest ->
    if DT.eliminated (conclusion :: DT.literals conclusion) h then lemma_discharged s bc eq other h conclusion;
    lemma_remaining_hypotheses s bc eq other rest conclusion

let lemma_step (node:U.proof_node) : bool =
  node.kind = U.LemmaRule &&
  (match node.premises with [p] -> p.conclusion = U.Holds R.false_expr | _ -> false)

let rec lemma_context_union (s:S.checked_schema) (xs ys:list expr)
  : Lemma (requires boolean_expressions s xs /\ boolean_expressions s ys)
          (ensures boolean_expressions s (U.add_hypotheses xs ys))
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest ->
    lemma_context_union s rest (if L.mem x ys then ys else x :: ys)

let rec lemma_premise_context (s:S.checked_schema) (ps:list U.checked_fact)
  : Lemma (requires facts_valid s ps)
          (ensures boolean_expressions s (U.premise_hypotheses ps))
          (decreases ps) =
  match ps with
  | [] -> ()
  | p :: rest ->
    lemma_premise_context s rest;
    lemma_context_union s p.hypotheses (U.premise_hypotheses rest)

let rec lemma_remaining_context (s:S.checked_schema) (hyps:list expr) (conclusion:expr)
  : Lemma (requires boolean_expressions s hyps)
          (ensures boolean_expressions s (remaining_hypotheses hyps conclusion) /\
                   boolean_expressions s (U.remaining_hypotheses hyps conclusion))
          (decreases hyps) =
  match hyps with
  | [] -> ()
  | _ :: rest -> lemma_remaining_context s rest conclusion

let quantifier_instantiation (node:U.proof_node) : bool =
  match node.kind, node.conclusion with
  | U.QuantifierInstantiation args, U.Holds formula ->
    node.premises = [] && Q.check args formula
  | _, _ -> false

let quantifier_flattening (node:U.proof_node) : bool =
  node.kind = U.PullQuantifier && node.premises = [] &&
  Q.check_flatten (proposition node.conclusion)

let arithmetic_assumptions (node:U.proof_node) : list (bool & expr) =
  L.map Z3LinearArithmeticAst.positive_literal (propositions node.premises) @
  L.map Z3LinearArithmeticAst.negative_literal (DT.literals (proposition node.conclusion))

let arithmetic_farkas (node:U.proof_node) : bool =
  match node.kind with
  | U.ArithmeticFarkas cs -> AR.check_contradiction (arithmetic_assumptions node) cs
  | _ -> false

(* The SAME supplied weights against the SAME literals, replayed by the typed
   Int/Real check (Z3SortedRealLinear.check_numeric_contradiction): enabled
   only when the executed schema check RL.real_primitive s holds (Real is not
   a datatype sort of the schema), Int literals rounded as on the Int path,
   Real strict literals kept strict. Tried after the unchanged Int path. *)
let real_farkas (s:S.checked_schema) (node:U.proof_node) : bool =
  match node.kind with
  | U.ArithmeticFarkas cs -> LIN.check_numeric_contradiction s (arithmetic_assumptions node) cs
  | _ -> false

(* A premise-free rewrite step whose closed equation the Real normal forms
   (Z3SortedRealLinear.real_equivalent: Real and Int-with-to_real linear
   renormalization, comparison orientation and strictness, binary Real
   product commutation) prove, enabled by the same schema gate. *)
let real_rewrite (s:S.checked_schema) (node:U.proof_node) : bool =
  RL.real_primitive s && node.kind = U.RewriteRule && Nil? node.premises &&
  (match node.conclusion with
   | U.Equal a b | U.Observational a b -> D.scoped [] a && D.scoped [] b && LIN.real_equivalent a b
   | U.Holds _ -> false)

(* A premise-free rewrite step whose closed equation is one of the ITE laws
   of Z3NnfReplay.ite_rewritten (negated-condition swap, then-branch merge by
   `or`, else-branch merge by `and`, one canonical ite declaration at any
   result sort): the same check as on the quant-intro rewrite leaves, read
   at the scope []. No schema gate: the laws hold in every Sorted model. *)
let ite_rewrite (node:U.proof_node) : bool =
  node.kind = U.RewriteRule && Nil? node.premises &&
  (match node.conclusion with
   | U.Equal a b | U.Observational a b -> D.scoped [] a && D.scoped [] b && NR.ite_rewritten a b
   | U.Holds _ -> false)

(* A premise-free rewrite step whose closed Int equation permutes and
   regroups the factors of canonical Int products
   (Z3NnfReplay.product_permuted, the check of the quant-intro rewrite
   leaves, read at the scope []). No schema gate: the Int product is the
   one the Sorted semantics gives `*` in every Sorted model. *)
let product_rewrite (node:U.proof_node) : bool =
  node.kind = U.RewriteRule && Nil? node.premises &&
  (match node.conclusion with
   | U.Equal a b | U.Observational a b -> D.scoped [] a && D.scoped [] b && NR.product_permuted a b
   | U.Holds _ -> false)

(* A premise-free closed ElimUnused step (q = e, exported as iff(q, e)):
   the check of the quant-intro elim-unused entries
   (Z3NnfReplay.unused_eliminated, z3's elim_unused_vars recomputed from q),
   read at the scope []. It reads the universal and existential laws, and
   the removed binders' carriers are inhabited by the interpretation. *)
let unused_elimination (node:U.proof_node) : bool =
  node.kind = U.ElimUnused && Nil? node.premises &&
  (match node.conclusion with
   | U.Equal a b | U.Observational a b -> D.scoped [] a && D.scoped [] b && NR.unused_eliminated a b
   | U.Holds _ -> false)

(* A premise-free closed der step (q = e, exported as iff(q, e)): the check
   of the quant-intro der entries (Z3NnfReplay.der_step: one eliminated
   binder of a universal over a disjunction, the binder list kept), read at
   the scope []. *)
let der_rewrite (node:U.proof_node) : bool =
  node.kind = U.DestructiveEquality && Nil? node.premises &&
  (match node.conclusion with
   | U.Equal a b | U.Observational a b -> D.scoped [] a && D.scoped [] b && NR.der_step a b
   | U.Holds _ -> false)

(* The rules whose checks read the universal and existential laws: a binder
   certificate (the NNF and quant-intro replay), an ElimUnused step and a
   der step. *)
let binder_rule (r:U.rule) : bool =
  U.QuantifierIntroduction? r || r = U.ElimUnused || r = U.DestructiveEquality

(* The rules whose entries may be closed Real order clauses: every rule but
   the two leaves and the lemma rule (the Int clauses are read by the same
   rule-independent consequence kernel). *)
let order_rule (r:U.rule) : bool = not (r = U.Asserted || r = U.Hypothesis || r = U.LemmaRule)

(* A closed Real equality/order clause (real_order_clause above), judged from
   the entry formula alone: no premise, rule label or payload is read. It is a
   theorem of every Sorted model satisfying the Real laws, enabled by the same
   executed schema gate RL.real_primitive as the other Real kernels. *)
let real_order (s:S.checked_schema) (node:U.proof_node) : bool =
  order_rule node.kind &&
  (match node.conclusion with
   | U.Holds c -> real_order_clause c && D.scoped [] c && get_sort c = bool_sort
   | U.Equal _ _ | U.Observational _ _ -> false) &&
  RL.real_primitive s

(* The node kernels that read the Sorted Real laws. *)
let real_equality (s:S.checked_schema) (node:U.proof_node) : bool =
  (node.kind = U.RewriteRule || node.kind = U.Unverified "th-lemma") &&
  (match node.conclusion with
   | U.Equal a b | U.Observational a b -> LIN.implied_equality s (propositions node.premises) a b
   | _ -> false)

let real_product (s:S.checked_schema) (node:U.proof_node) : bool =
  node.kind = U.Unverified "th-lemma" && node.conclusion = U.Holds R.false_expr &&
  RP.check s (propositions node.premises)

let real_node (s:S.checked_schema) (node:U.proof_node) : bool =
  real_farkas s node || real_rewrite s node || real_order s node || real_equality s node || real_product s node

(* A closed guarded Int div/mod clause (division_clause above), judged from the
   entry formula alone: no premise, rule label or payload is read. It is a
   theorem of every Sorted model satisfying the Sorted Int division laws
   (Z3SortedIntDivision.division_laws). No schema gate: Int is never a
   datatype sort of a checked schema, and the laws are derived from R2 of the
   same root model whatever the schema. *)
let division_order (node:U.proof_node) : bool =
  order_rule node.kind &&
  (match node.conclusion with
   | U.Holds c -> division_clause c && D.scoped [] c && get_sort c = bool_sort
   | U.Equal _ _ | U.Observational _ _ -> false)

(* The node kernels that read the Sorted division laws. *)
let division_node (node:U.proof_node) : bool = division_order node

let rec lemma_arithmetic_assumptions (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                    (facts lits:list expr)
  : Lemma (requires T.truths s bc eq other facts /\
                    not (B.geval_args (T.truth s bc eq other) B.Or (L.map B.Atom lits)))
          (ensures AR.assumptions_hold s bc eq other
            (L.map Z3LinearArithmeticAst.positive_literal facts @
             L.map Z3LinearArithmeticAst.negative_literal lits))
          (decreases %[facts; lits]) =
  match facts with
  | _ :: rest -> lemma_arithmetic_assumptions s bc eq other rest lits
  | [] ->
    (match lits with
     | [] -> ()
     | _ :: rest -> lemma_arithmetic_assumptions s bc eq other [] rest)

(* ---------------------------------------------------------------------- *)
(* Coefficient-free linear Int consequences                                 *)
(* ---------------------------------------------------------------------- *)

(* The producer's implied Int equalities and bound conflicts carry no Farkas
   coefficients (only its arith farkas/bound steps do). The checker
   recomputes them from the step's own formulas: the existing bounded search
   LA.synthesize (unchanged and untrusted: at most 32 literals, 16
   elimination rounds and 128 rows) proposes weights for the premises with
   one target negated, and the existing typed check AR.check_contradiction
   validates them against exactly those literals (one weight per literal,
   signs and orientation, the strict-Int rounding, atoms by expression
   identity, closed scope, Int comparisons only, every contribution). A
   failed or wrong search leaves the step open. Only the entry formula and
   the premise propositions are read, never the rule label or a payload;
   the two bounds below are internal checker terms. *)

(* Every literal an Int comparison or its negation (AR.integer_formula):
   Real, mixed and non-arithmetic literals are refused before any search. *)
let rec integer_literals (lits:list (bool & expr)) : Tot bool (decreases lits) =
  match lits with
  | [] -> true
  | (_, e) :: rest -> AR.integer_formula 16 e && integer_literals rest

(* The existing input bounds, enforced before the search: synthesize's
   literal cap, check_contradiction's expression budget, Int-only literals. *)
let linear_inputs (lits:list (bool & expr)) : bool =
  L.length lits <= 32 && Some? (arguments_budget 4096 (L.map snd lits)) && integer_literals lits

(* The facts and the negation of c are contradictory: the search's weights
   for the literals it refutes (LA.assumptions c facts), validated. *)
let refutes (facts:list expr) (c:expr) : bool =
  let lits = LA.assumptions c facts in
  linear_inputs lits &&
  (match LA.synthesize c facts with
   | Some cs -> AR.check_contradiction lits cs
   | None -> false)

let int_le (x y:expr) : expr =
  App { decl_name = "<="; domain = [LA.int_s; LA.int_s]; range = bool_sort;
        interp = Some Z3ValueTheory.op_arith_le; int_params = [] } [x; y]

let int_ge (x y:expr) : expr =
  App { decl_name = ">="; domain = [LA.int_s; LA.int_s]; range = bool_sort;
        interp = Some Z3ValueTheory.op_arith_ge; int_params = [] } [x; y]

(* An Int equation x = y: x <= y and x >= y each refuted on its own (its own
   search and check), then antisymmetry (order_equation over the two
   bounds). The conclusion false: one refutation of the facts. *)
let linear_consequence (facts:list expr) (conclusion:expr) : bool =
  match int_equation conclusion with
  | Some (x, y) -> refutes facts (int_le x y) && refutes facts (int_ge x y)
  | None -> conclusion = R.false_expr && refutes facts R.false_expr

(* A refuted c is not false where the facts hold: the facts and the negated
   literals of c would satisfy every literal of the validated certificate
   (lemma_arithmetic_assumptions), contradicting AR.lemma_check_contradiction.
   The search itself is not trusted. *)
let lemma_refutes (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (facts:list expr) (c:expr)
  : Lemma (requires T.truths s bc eq other facts /\ refutes facts c /\
                    not (B.geval_args (T.truth s bc eq other) B.Or (L.map B.Atom (R.formula_clause c))))
          (ensures False) =
  lemma_arithmetic_assumptions s bc eq other facts (R.formula_clause c);
  AR.lemma_check_contradiction s bc eq other (LA.assumptions c facts) (Some?.v (LA.synthesize c facts))

(* A refuted unit clause is true. *)
let lemma_unit_refuted (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (facts:list expr) (c:expr)
  : Lemma (requires T.truths s bc eq other facts /\ refutes facts c /\ R.formula_clause c == [c])
          (ensures T.truth s bc eq other c) =
  if not (T.truth s bc eq other c) then (
    assert_norm (B.geval_args (T.truth s bc eq other) B.Or (L.map B.Atom [c]) ==
                 B.combine B.Or (T.truth s bc eq other c) (B.neutral B.Or));
    lemma_refutes s bc eq other facts c)

let lemma_linear_consequence (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc eq other facts /\ D.scoped [] conclusion /\
                    linear_consequence facts conclusion)
          (ensures T.truth s bc eq other conclusion) =
  match int_equation conclusion with
  | Some (x, y) ->
    let le = int_le x y in
    let ge = int_ge x y in
    lemma_equation s bc eq other conclusion x y;
    assert (R.formula_clause le == [le] /\ R.formula_clause ge == [ge]);
    lemma_unit_refuted s bc eq other facts le;
    lemma_unit_refuted s bc eq other facts ge;
    assert (LA.comparison le == Some (LA.Le, x, y) /\ LA.comparison ge == Some (LA.Ge, x, y));
    assert (has_bound x y true [le; ge] /\ has_bound x y false [le; ge]);
    lemma_order_equation s bc eq other [le; ge] conclusion
  | None ->
    assert_norm (R.formula_clause R.false_expr == []);
    lemma_refutes s bc eq other facts R.false_expr

let int_zero : expr =
  App { decl_name = "0"; domain = []; range = LA.int_s;
        interp = Some Z3ValueTheory.op_num_rational; int_params = [0; 1] } []

let int_one : expr =
  App { decl_name = "1"; domain = []; range = LA.int_s;
        interp = Some Z3ValueTheory.op_num_rational; int_params = [1; 1] } []

let int_bound (lower:bool) (e:expr) : expr =
  if lower then int_ge e int_zero else int_le e int_zero

let nonnegative_int_product (facts:list expr) (p:expr) : bool =
  match p with
  | App f [x; y] ->
    SI.classify f = SI.Calculate LA.Mul && D.scoped [] p &&
    ((refutes facts (int_bound true x) && refutes facts (int_bound true y)) ||
     (refutes facts (int_bound false x) && refutes facts (int_bound false y))) &&
    refutes (int_ge p int_zero :: facts) R.false_expr
  | _ -> false

let nonpositive_int_product (facts:list expr) (p:expr) : bool =
  match p with
  | App f [x; y] ->
    SI.classify f = SI.Calculate LA.Mul && D.scoped [] p &&
    ((refutes facts (int_bound true x) && refutes facts (int_bound false y)) ||
     (refutes facts (int_bound false x) && refutes facts (int_bound true y))) &&
    refutes (int_le p int_zero :: facts) R.false_expr
  | _ -> false

let positive_int_product (facts:list expr) (p:expr) : bool =
  match p with
  | App f [x; y] ->
    SI.classify f = SI.Calculate LA.Mul && D.scoped [] p &&
    refutes facts (int_ge x int_one) && refutes facts (int_ge y int_one) &&
    refutes (int_ge p int_one :: facts) R.false_expr
  | _ -> false

let rec integer_products (fuel:nat) (e:expr) : Tot (list expr) (decreases fuel) =
  if fuel = 0 then []
  else match e with
  | App f args ->
    (if SI.classify f = SI.Calculate LA.Mul && L.length args = 2 then [e] else []) @
    L.concatMap (integer_products (fuel - 1)) args
  | _ -> []

let rec integer_product_candidate (facts:list expr) (fuel:nat) (rest:list expr)
  : Tot (p:option expr{Some? p ==> (nonnegative_int_product facts (Some?.v p) ||
                                   positive_int_product facts (Some?.v p) ||
                                   nonpositive_int_product facts (Some?.v p))}) (decreases fuel) =
  if fuel = 0 then None
  else match rest with
  | [] -> None
  | p :: tail ->
    let next : nat = fuel - 1 in
    if nonnegative_int_product facts p || positive_int_product facts p || nonpositive_int_product facts p then Some p
    else integer_product_candidate facts next tail

let integer_product_witness (facts:list expr) : option expr =
  integer_product_candidate facts 32 (L.concatMap (integer_products 16) facts)

let integer_product_check (facts:list expr) : bool =
  if L.length facts > 30 then false
  else if None? (arguments_budget 4096 facts) then false
  else integer_literals (L.map LA.positive_literal facts) && Some? (integer_product_witness facts)

let integer_product (node:U.proof_node) : bool =
  node.kind = U.Unverified "th-lemma" && node.conclusion = U.Holds R.false_expr &&
  integer_product_check (propositions node.premises)

let lemma_int_bound_shape (lower:bool) (e:expr)
  : Lemma (requires D.scoped [] e /\ get_sort e == LA.int_s)
          (ensures AR.int_numeral 0 int_zero /\ D.scoped [] (int_bound lower e) /\
                   LA.comparison (int_bound lower e) == Some ((if lower then LA.Ge else LA.Le), e, int_zero) /\
                   R.formula_clause (int_bound lower e) == [int_bound lower e]) =
  assert_norm (get_sort int_zero == LA.int_s);
  assert_norm (AR.int_numeral 0 int_zero);
  if lower then assert (LA.application
    { decl_name = ">="; domain = [LA.int_s; LA.int_s]; range = bool_sort;
      interp = Some Z3ValueTheory.op_arith_ge; int_params = [] }
    [e; int_zero] bool_sort ">=" Z3ValueTheory.op_arith_ge)
  else assert (LA.application
    { decl_name = "<="; domain = [LA.int_s; LA.int_s]; range = bool_sort;
      interp = Some Z3ValueTheory.op_arith_le; int_params = [] }
    [e; int_zero] bool_sort "<=" Z3ValueTheory.op_arith_le)

let lemma_int_bound (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (facts:list expr) (lower:bool) (e:expr)
  : Lemma (requires T.truths s bc eq other facts /\ D.scoped [] e /\ get_sort e == LA.int_s /\
                    refutes facts (int_bound lower e))
          (ensures (if lower then integer_value s bc eq other e >= 0 else integer_value s bc eq other e <= 0)) =
  let rho = T.empty_environment (S.signature s) in
  lemma_int_bound_shape lower e;
  lemma_unit_refuted s bc eq other facts (int_bound lower e);
  AR.lemma_int_comparison s bc eq other [] rho (int_bound lower e) (if lower then LA.Ge else LA.Le) e int_zero;
  AR.lemma_int_numeral s bc eq other [] rho 0 int_zero

let lemma_int_positive_shape (e:expr)
  : Lemma (requires D.scoped [] e /\ get_sort e == LA.int_s)
          (ensures AR.int_numeral 1 int_one /\ D.scoped [] (int_ge e int_one) /\
                   LA.comparison (int_ge e int_one) == Some (LA.Ge, e, int_one) /\
                   R.formula_clause (int_ge e int_one) == [int_ge e int_one]) =
  assert_norm (get_sort int_one == LA.int_s);
  assert_norm (AR.int_numeral 1 int_one);
  assert (LA.application
    { decl_name = ">="; domain = [LA.int_s; LA.int_s]; range = bool_sort;
      interp = Some Z3ValueTheory.op_arith_ge; int_params = [] }
    [e; int_one] bool_sort ">=" Z3ValueTheory.op_arith_ge)

let lemma_int_positive (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (facts:list expr) (e:expr)
  : Lemma (requires T.truths s bc eq other facts /\ D.scoped [] e /\ get_sort e == LA.int_s /\
                    refutes facts (int_ge e int_one))
          (ensures integer_value s bc eq other e >= 1) =
  let rho = T.empty_environment (S.signature s) in
  lemma_int_positive_shape e;
  lemma_unit_refuted s bc eq other facts (int_ge e int_one);
  AR.lemma_int_comparison s bc eq other [] rho (int_ge e int_one) LA.Ge e int_one;
  AR.lemma_int_numeral s bc eq other [] rho 1 int_one

#push-options "--smtencoding.nl_arith_repr native --using_facts_from 'Prims' --fuel 0 --ifuel 0"
let lemma_int_multiply_nonnegative (x y:int)
  : Lemma (requires (x >= 0 /\ y >= 0) \/ (x <= 0 /\ y <= 0)) (ensures x * y >= 0) = ()

let lemma_int_multiply_nonpositive (x y:int)
  : Lemma (requires (x >= 0 /\ y <= 0) \/ (x <= 0 /\ y >= 0)) (ensures x * y <= 0) = ()

let lemma_int_multiply_positive (x y:int)
  : Lemma (requires x >= 1 /\ y >= 1) (ensures x * y >= 1) = ()
#pop-options

let lemma_nonnegative_int_product (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                  (facts:list expr) (p:expr)
  : Lemma (requires T.truths s bc eq other facts /\ nonnegative_int_product facts p)
          (ensures False) =
  match p with
  | App f [x; y] ->
    let rho = T.empty_environment (S.signature s) in
    AR.lemma_int_binary s bc eq other [] rho f x y LA.Mul;
    if refutes facts (int_bound true x) && refutes facts (int_bound true y) then (
      lemma_int_bound s bc eq other facts true x;
      lemma_int_bound s bc eq other facts true y)
    else (
      lemma_int_bound s bc eq other facts false x;
      lemma_int_bound s bc eq other facts false y);
    lemma_int_multiply_nonnegative (integer_value s bc eq other x) (integer_value s bc eq other y);
    lemma_int_bound_shape true p;
    AR.lemma_int_comparison s bc eq other [] rho (int_ge p int_zero) LA.Ge p int_zero;
    AR.lemma_int_numeral s bc eq other [] rho 0 int_zero;
    assert (T.truth s bc eq other (int_ge p int_zero));
    assert_norm (R.formula_clause R.false_expr == []);
    lemma_refutes s bc eq other (int_ge p int_zero :: facts) R.false_expr
  | _ -> ()

let lemma_nonpositive_int_product (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                  (facts:list expr) (p:expr)
  : Lemma (requires T.truths s bc eq other facts /\ nonpositive_int_product facts p)
          (ensures False) =
  match p with
  | App f [x; y] ->
    let rho = T.empty_environment (S.signature s) in
    AR.lemma_int_binary s bc eq other [] rho f x y LA.Mul;
    if refutes facts (int_bound true x) && refutes facts (int_bound false y) then (
      lemma_int_bound s bc eq other facts true x;
      lemma_int_bound s bc eq other facts false y)
    else (
      lemma_int_bound s bc eq other facts false x;
      lemma_int_bound s bc eq other facts true y);
    lemma_int_multiply_nonpositive (integer_value s bc eq other x) (integer_value s bc eq other y);
    lemma_int_bound_shape false p;
    AR.lemma_int_comparison s bc eq other [] rho (int_le p int_zero) LA.Le p int_zero;
    AR.lemma_int_numeral s bc eq other [] rho 0 int_zero;
    assert (T.truth s bc eq other (int_le p int_zero));
    assert_norm (R.formula_clause R.false_expr == []);
    lemma_refutes s bc eq other (int_le p int_zero :: facts) R.false_expr
  | _ -> ()

let lemma_positive_int_product (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                               (facts:list expr) (p:expr)
  : Lemma (requires T.truths s bc eq other facts /\ positive_int_product facts p)
          (ensures False) =
  match p with
  | App f [x; y] ->
    let rho = T.empty_environment (S.signature s) in
    AR.lemma_int_binary s bc eq other [] rho f x y LA.Mul;
    lemma_int_positive s bc eq other facts x;
    lemma_int_positive s bc eq other facts y;
    lemma_int_multiply_positive (integer_value s bc eq other x) (integer_value s bc eq other y);
    lemma_int_positive_shape p;
    AR.lemma_int_comparison s bc eq other [] rho (int_ge p int_one) LA.Ge p int_one;
    AR.lemma_int_numeral s bc eq other [] rho 1 int_one;
    assert (T.truth s bc eq other (int_ge p int_one));
    assert_norm (R.formula_clause R.false_expr == []);
    lemma_refutes s bc eq other (int_ge p int_one :: facts) R.false_expr
  | _ -> ()

let lemma_integer_product_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                (facts:list expr)
  : Lemma (requires T.truths s bc eq other facts /\ integer_product_check facts)
          (ensures False) =
  let p = Some?.v (integer_product_witness facts) in
  if nonnegative_int_product facts p then lemma_nonnegative_int_product s bc eq other facts p
  else if positive_int_product facts p then lemma_positive_int_product s bc eq other facts p
  else lemma_nonpositive_int_product s bc eq other facts p

(* The NNF certificate replay (Z3NnfReplay) of a premise-free
   QuantifierIntroduction node whose certificate root is nnf-neg or nnf-pos.
   Every other node, and every other certificate, is Unreplayed here and
   keeps the previous treatment. *)
let nnf_verdict (s:S.checked_schema) (assertions:list expr) (node:U.proof_node) : NR.verdict =
  match node.U.kind with
  | U.QuantifierIntroduction c ->
    if Nil? node.U.premises then NR.replay_with (RL.real_primitive s) assertions c node.U.conclusion
    else NR.Unreplayed
  | _ -> NR.Unreplayed

let check_node_cached (s:S.checked_schema) (assertions:list expr) (node:U.proof_node)
  : option (U.checked_fact & nat) =
  let conclusion = proposition node.conclusion in
  if not (boolean_expression s conclusion) then None
  else match node.kind with
  | U.Asserted ->
    if node.premises = [] && L.mem conclusion assertions
    then Some ({ U.conclusion = node.conclusion; hypotheses = [] }, 0)
    else None
  | U.Hypothesis ->
    if node.premises = []
    then Some ({ U.conclusion = node.conclusion; hypotheses = [conclusion] }, 0)
    else None
  | _ ->
    let nnf = nnf_verdict s assertions node in
    (* A certificate whose premise ids are not earlier entries is a malformed
       proof entry, reported as a rejection rather than as a pending step. *)
    if nnf = NR.Malformed then None else
    let inherited = U.premise_hypotheses node.premises in
    let hypotheses =
      if lemma_step node then
        match node.premises with [p] -> remaining_hypotheses p.hypotheses conclusion | _ -> inherited
      else if node.kind = U.LemmaRule then U.remaining_hypotheses inherited conclusion
      else inherited in
    let fact = { U.conclusion = node.conclusion; hypotheses = hypotheses } in
    let checked =
      arithmetic_farkas node || real_farkas s node || quantifier_instantiation node || quantifier_flattening node ||
      lemma_step node || real_rewrite s node || real_order s node || real_equality s node || real_product s node ||
      integer_product node || division_order node ||
      nnf = NR.Replayed ||
      (node.kind <> U.LemmaRule && consequence s (propositions node.premises) conclusion) ||
      DT.consequence s (scoped_propositions node.premises) (scoped_proposition fact) ||
      (node.kind <> U.LemmaRule && linear_consequence (propositions node.premises) conclusion) ||
      ite_rewrite node || product_rewrite node || unused_elimination node || der_rewrite node in
    Some (fact, (if checked then 0 else 1))

let check_node (s:S.checked_schema) (assertions:list expr) (node:U.proof_node)
  : option (U.checked_fact & nat) =
  if facts_valid s node.premises then check_node_cached s assertions node else None

let lemma_check_node_context (s:S.checked_schema) (assertions:list expr)
                             (node:U.proof_node) (fact:U.checked_fact) (pending:nat)
  : Lemma (requires facts_valid s node.premises /\
                    check_node_cached s assertions node == Some (fact, pending))
          (ensures fact_valid s fact) =
  match node.kind with
  | U.Asserted | U.Hypothesis -> ()
  | _ ->
    lemma_premise_context s node.premises;
    if lemma_step node then (
      match node.premises with
      | [p] -> lemma_remaining_context s p.hypotheses (proposition node.conclusion)
      | _ -> ())
    else if node.kind = U.LemmaRule then
      lemma_remaining_context s (U.premise_hypotheses node.premises) (proposition node.conclusion)

(* A replayed NNF node: its conclusion, a closed equation of two values, is
   true (Z3NnfReplay.lemma_replay at the scope [] and the empty environment). *)
let lemma_nnf_node (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (assertions:list expr) (node:U.proof_node)
  : Lemma (requires T.truths s bc eq other assertions /\
                    Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (RL.real_primitive s ==> RL.real_model s bc eq other) /\
                    boolean_expression s (proposition node.conclusion) /\
                    nnf_verdict s assertions node == NR.Replayed)
          (ensures T.truth s bc eq other (proposition node.conclusion)) =
  match node.kind with
  | U.QuantifierIntroduction c ->
    NR.lemma_replay_with s bc eq other (RL.real_primitive s) assertions c node.conclusion;
    (match node.conclusion with
     | U.Equal a b | U.Observational a b ->
       V.lemma_sort_eq (get_sort b) (get_sort a);
       T.lemma_same_value s bc eq other a b;
       T.lemma_equality s bc eq other a b
     | U.Holds _ -> ())
  | _ -> ()

(* An accepted typed Int/Real certificate refutes its literals in every
   Sorted model satisfying the Real laws (RL.real_model: SOME Real carrier). *)
let lemma_real_contradiction (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (xs:list (bool & expr)) (cs:list LA.coefficient)
  : Lemma (requires RL.real_model s bc eq other /\ LIN.check_numeric_contradiction s xs cs /\
                    AR.assumptions_hold s bc eq other xs)
          (ensures False) =
  FStar.Classical.exists_elim False #(RL.carrier base) #(fun reals -> RL.real_laws s bc eq other reals) ()
    (fun reals -> LIN.lemma_check_numeric_contradiction s bc eq other reals xs cs)

(* An accepted Real rewrite equation is true in every Sorted model
   satisfying the Real laws. *)
let lemma_real_rewrite (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (node:U.proof_node)
  : Lemma (requires RL.real_model s bc eq other /\ boolean_expression s (proposition node.conclusion) /\
                    real_rewrite s node)
          (ensures T.truth s bc eq other (proposition node.conclusion)) =
  match node.conclusion with
  | U.Equal a b | U.Observational a b ->
    FStar.Classical.exists_elim (T.evaluate s bc eq other a == T.evaluate s bc eq other b)
      #(RL.carrier base) #(fun reals -> RL.real_laws s bc eq other reals) ()
      (fun reals -> LIN.lemma_real_equivalent s bc eq other reals [] (T.empty_environment (S.signature s)) a b);
    V.lemma_sort_eq (get_sort b) (get_sort a);
    T.lemma_equality s bc eq other a b
  | U.Holds _ -> ()

(* An accepted Real equality/order clause is true in every Sorted model
   satisfying the Real laws. *)
let lemma_real_order (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (node:U.proof_node)
  : Lemma (requires RL.real_model s bc eq other /\ boolean_expression s (proposition node.conclusion) /\
                    real_order s node)
          (ensures T.truth s bc eq other (proposition node.conclusion)) =
  match node.conclusion with
  | U.Holds c ->
    FStar.Classical.exists_elim (T.truth s bc eq other c)
      #(RL.carrier base) #(fun reals -> RL.real_laws s bc eq other reals) ()
      (fun reals -> lemma_real_order_clause s bc eq other reals c)
  | _ -> ()

(* An accepted guarded Int div/mod clause is true in every Sorted model
   satisfying the division laws. *)
let lemma_division_order (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (node:U.proof_node)
  : Lemma (requires DV.division_laws s bc eq other /\ boolean_expression s (proposition node.conclusion) /\
                    division_order node)
          (ensures T.truth s bc eq other (proposition node.conclusion)) =
  match node.conclusion with
  | U.Holds c -> lemma_division_clause s bc eq other c
  | _ -> ()

(* An accepted ITE rewrite equation is true in every Sorted model: the ITE
   laws at the scope [] and the empty environment. *)
let lemma_ite_rewrite (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (node:U.proof_node)
  : Lemma (requires boolean_expression s (proposition node.conclusion) /\ ite_rewrite node)
          (ensures T.truth s bc eq other (proposition node.conclusion)) =
  match node.conclusion with
  | U.Equal a b | U.Observational a b ->
    let rho = T.empty_environment (S.signature s) in
    NR.lemma_ite_rewritten_at s bc eq other [] rho a b;
    NR.lemma_same_at s bc eq other [] rho a b;
    assert (T.evaluate s bc eq other a == T.evaluate s bc eq other b);
    V.lemma_sort_eq (get_sort b) (get_sort a);
    T.lemma_equality s bc eq other a b
  | U.Holds _ -> ()

(* An accepted Int factor permutation equation is true in every Sorted
   model: the law at the scope [] and the empty environment. *)
let lemma_product_rewrite (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (node:U.proof_node)
  : Lemma (requires boolean_expression s (proposition node.conclusion) /\ product_rewrite node)
          (ensures T.truth s bc eq other (proposition node.conclusion)) =
  match node.conclusion with
  | U.Equal a b | U.Observational a b ->
    let rho = T.empty_environment (S.signature s) in
    NR.lemma_product_permuted_at s bc eq other [] rho a b;
    NR.lemma_same_at s bc eq other [] rho a b;
    assert (T.evaluate s bc eq other a == T.evaluate s bc eq other b);
    V.lemma_sort_eq (get_sort b) (get_sort a);
    T.lemma_equality s bc eq other a b
  | U.Holds _ -> ()

(* An accepted ElimUnused equation is true in every Sorted model satisfying
   the universal and existential laws: the law at the scope [] and the empty
   environment. *)
let lemma_unused_elimination (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (node:U.proof_node)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    boolean_expression s (proposition node.conclusion) /\ unused_elimination node)
          (ensures T.truth s bc eq other (proposition node.conclusion)) =
  match node.conclusion with
  | U.Equal a b | U.Observational a b ->
    let rho = T.empty_environment (S.signature s) in
    NR.lemma_unused_eliminated_at s bc eq other [] rho a b;
    NR.lemma_same_at s bc eq other [] rho a b;
    assert (T.evaluate s bc eq other a == T.evaluate s bc eq other b);
    V.lemma_sort_eq (get_sort b) (get_sort a);
    T.lemma_equality s bc eq other a b
  | U.Holds _ -> ()

(* An accepted der equation is true in every Sorted model satisfying the
   universal law: the law at the scope [] and the empty environment. *)
let lemma_der_rewrite (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (node:U.proof_node)
  : Lemma (requires Q.forall_model s bc other /\
                    boolean_expression s (proposition node.conclusion) /\ der_rewrite node)
          (ensures T.truth s bc eq other (proposition node.conclusion)) =
  match node.conclusion with
  | U.Equal a b | U.Observational a b ->
    let rho = T.empty_environment (S.signature s) in
    NR.lemma_der_at s bc eq other [] rho a b;
    NR.lemma_same_at s bc eq other [] rho a b;
    assert (T.evaluate s bc eq other a == T.evaluate s bc eq other b);
    V.lemma_sort_eq (get_sort b) (get_sort a);
    T.lemma_equality s bc eq other a b
  | U.Holds _ -> ()

let lemma_check_node_cached (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (assertions:list expr) (node:U.proof_node) (fact:U.checked_fact)
  : Lemma (requires T.truths s bc eq other assertions /\ facts_hold s bc eq other node.premises /\
                    facts_valid s node.premises /\
                    (quantifier_instantiation node ==> Q.forall_elimination_model s bc other) /\
                    (quantifier_flattening node ==> Q.forall_model s bc other) /\
                    (binder_rule node.kind ==>
                       Q.forall_model s bc other /\ E.exists_model s bc other /\
                       (RL.real_primitive s ==> RL.real_model s bc eq other)) /\
                    (real_node s node ==> RL.real_model s bc eq other) /\
                    (division_node node ==> DV.division_laws s bc eq other) /\
                    check_node_cached s assertions node == Some (fact, 0))
          (ensures fact_holds s bc eq other fact) =
  lemma_check_node_context s assertions node fact 0;
  match node.kind with
  | U.Asserted -> lemma_truth_member s bc eq other assertions (proposition node.conclusion)
  | U.Hypothesis -> ()
  | _ ->
    let conclusion = proposition node.conclusion in
    if arithmetic_farkas node then (
      if T.truths s bc eq other fact.hypotheses && not (T.truth s bc eq other conclusion) then (
        lemma_premise_hypotheses s bc eq other node.premises;
        DT.lemma_literals s bc eq other conclusion;
        lemma_arithmetic_assumptions s bc eq other (propositions node.premises) (DT.literals conclusion);
        match node.kind with
        | U.ArithmeticFarkas cs ->
          AR.lemma_check_contradiction s bc eq other (arithmetic_assumptions node) cs
        | _ -> ()))
    else if real_farkas s node then (
      if T.truths s bc eq other fact.hypotheses && not (T.truth s bc eq other conclusion) then (
        lemma_premise_hypotheses s bc eq other node.premises;
        DT.lemma_literals s bc eq other conclusion;
        lemma_arithmetic_assumptions s bc eq other (propositions node.premises) (DT.literals conclusion);
        match node.kind with
        | U.ArithmeticFarkas cs -> lemma_real_contradiction s bc eq other (arithmetic_assumptions node) cs
        | _ -> ()))
    else if real_rewrite s node then lemma_real_rewrite s bc eq other node
    else if real_order s node then lemma_real_order s bc eq other node
    else if real_equality s node then (
      if T.truths s bc eq other fact.hypotheses then (
        lemma_premise_hypotheses s bc eq other node.premises;
        match node.conclusion with
        | U.Equal a b | U.Observational a b ->
          FStar.Classical.exists_elim (T.truth s bc eq other (proposition node.conclusion))
            #(RL.carrier base) #(fun reals -> RL.real_laws s bc eq other reals) ()
            (fun reals -> LIN.lemma_implied_equality s bc eq other reals (propositions node.premises) a b)
        | _ -> ()))
    else if real_product s node then (
      if T.truths s bc eq other fact.hypotheses then (
        lemma_premise_hypotheses s bc eq other node.premises;
        FStar.Classical.exists_elim False
          #(RL.carrier base) #(fun reals -> RL.real_laws s bc eq other reals) ()
          (fun reals -> RP.lemma_check s bc eq other reals (propositions node.premises))))
    else if integer_product node then (
      if T.truths s bc eq other fact.hypotheses then (
        lemma_premise_hypotheses s bc eq other node.premises;
        lemma_integer_product_check s bc eq other (propositions node.premises)))
    else if division_order node then lemma_division_order s bc eq other node
    else if quantifier_instantiation node then (
      match node.kind, node.conclusion with
      | U.QuantifierInstantiation args, U.Holds formula ->
        Q.lemma_check s bc eq other args formula
      | _, _ -> ())
    else if quantifier_flattening node then
      Q.lemma_check_flatten s bc eq other conclusion
    else if lemma_step node then (
      match node.premises with
      | [p] ->
        if T.truths s bc eq other fact.hypotheses && not (T.truth s bc eq other conclusion) then (
          lemma_remaining_hypotheses s bc eq other p.hypotheses conclusion;
          assert_norm (T.cut 1 R.false_expr == B.Bool false);
          T.lemma_cut s bc eq other 1 R.false_expr)
      | _ -> ())
    else if nnf_verdict s assertions node = NR.Replayed then
      lemma_nnf_node s bc eq other assertions node
    else if node.kind <> U.LemmaRule && consequence s (propositions node.premises) conclusion then (
      if T.truths s bc eq other fact.hypotheses then (
        lemma_premise_hypotheses s bc eq other node.premises;
        lemma_consequence s bc eq other (propositions node.premises) conclusion))
    else if DT.consequence s (scoped_propositions node.premises) (scoped_proposition fact) then (
      lemma_scoped_propositions s bc eq other node.premises;
      DT.lemma_consequence s bc eq other (scoped_propositions node.premises) (scoped_proposition fact);
      lemma_scoped_proposition s bc eq other fact)
    else if node.kind <> U.LemmaRule && linear_consequence (propositions node.premises) conclusion then (
      if T.truths s bc eq other fact.hypotheses then (
        lemma_premise_hypotheses s bc eq other node.premises;
        lemma_linear_consequence s bc eq other (propositions node.premises) conclusion))
    else if ite_rewrite node then lemma_ite_rewrite s bc eq other node
    else if product_rewrite node then lemma_product_rewrite s bc eq other node
    else if unused_elimination node then lemma_unused_elimination s bc eq other node
    else lemma_der_rewrite s bc eq other node

let prepare_entry_from (s:S.checked_schema) (premises:option (list U.checked_fact)) (e:P.entry)
  : option U.proof_node =
  if not (D.scoped [] e.formula && in_context s e.formula) then None
  else match U.classify_fact e.formula, premises with
  | Some conclusion, Some premises ->
    Some { U.kind = e.rule; conclusion = conclusion; premises = premises }
  | _, _ -> None

let prepare_entry (s:S.checked_schema) (cache:I.index_tree U.checked_fact) (e:P.entry)
  : option U.proof_node =
  prepare_entry_from s (I.opt_map_tail (I.index_find cache) e.premise_ids) e

let prepare_entry_table (s:S.checked_schema) (cache:IT.t U.checked_fact) (e:P.entry)
  : option U.proof_node =
  prepare_entry_from s (I.opt_map_tail (IT.find cache) e.premise_ids) e

let rec check_entries (s:S.checked_schema) (assertions:list expr)
                      (cache:I.index_tree U.checked_fact) (next pending:nat) (entries:list P.entry)
  : Tot (option (I.index_tree U.checked_fact & nat)) (decreases entries) =
  match entries with
  | [] -> Some (cache, pending)
  | e :: rest ->
    (match prepare_entry s cache e with
     | None -> None
     | Some node ->
       (match check_node_cached s assertions node with
        | None -> None
        | Some (fact, local) ->
          check_entries s assertions (I.index_put cache next fact) (next + 1) (pending + local) rest))

let check_document (schema:S.schema) (doc:P.document) : option nat =
  if not (S.valid schema) then None
  else if not (boolean_expressions schema doc.assertions && U.ordinary_facts doc.assertions) then None
  else match check_entries schema doc.assertions I.Empty 0 0 doc.entries with
  | None -> None
  | Some (cache, pending) ->
    (match I.index_find cache doc.root with
     | Some fact ->
       if fact.conclusion = U.Holds R.false_expr && fact.hypotheses = [] then Some pending else None
     | None -> None)

let rec lemma_pending (s:S.checked_schema) (assertions:list expr)
                      (cache:I.index_tree U.checked_fact) (next pending:nat) (entries:list P.entry)
                      (result:I.index_tree U.checked_fact) (count:nat)
  : Lemma (requires check_entries s assertions cache next pending entries == Some (result, count))
          (ensures pending <= count)
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    let node = Some?.v (prepare_entry s cache e) in
    let fact, local = Some?.v (check_node_cached s assertions node) in
    lemma_pending s assertions (I.index_put cache next fact) (next + 1) (pending + local) rest result count

let cache_sound (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (cache:I.index_tree U.checked_fact) : prop =
  forall (key:nat) (p:U.checked_fact).
    I.index_get cache key == Some p ==> fact_valid s p /\ fact_holds s bc eq other p

let lemma_cache_insert (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (cache:I.index_tree U.checked_fact) (key:nat) (fact:U.checked_fact)
  : Lemma (requires cache_sound s bc eq other cache /\ fact_valid s fact /\ fact_holds s bc eq other fact)
          (ensures cache_sound s bc eq other (I.index_put cache key fact)) =
  let at (query:nat)
    : Lemma (forall (p:U.checked_fact).
        I.index_get (I.index_put cache key fact) query == Some p ==>
        fact_valid s p /\ fact_holds s bc eq other p) =
    I.lemma_index_put cache key fact query in
  FStar.Classical.forall_intro at

let rec lemma_premise_lookup (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (cache:I.index_tree U.checked_fact) (ids:list int) (ps:list U.checked_fact)
  : Lemma (requires cache_sound s bc eq other cache /\
                    I.opt_map (I.index_find cache) ids == Some ps)
          (ensures facts_valid s ps /\ facts_hold s bc eq other ps)
          (decreases ids) =
  match ids, ps with
  | id :: rest, p :: tail ->
    assert (id >= 0);
    assert (I.index_get cache id == Some p);
    assert (fact_valid s p /\ fact_holds s bc eq other p);
    lemma_premise_lookup s bc eq other cache rest tail
  | _, _ -> ()

let rec needs_forall_semantics (entries:list P.entry) : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | e :: rest ->
    (match e.P.rule with U.QuantifierInstantiation _ -> true | _ -> needs_forall_semantics rest)

let rec needs_forall_truth (entries:list P.entry) : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | e :: rest ->
    e.P.rule = U.PullQuantifier || needs_forall_truth rest

(* An entry with a binder certificate (the NNF replay reads the universal and
   existential laws, Z3NnfReplay.lemma_replay) or an ElimUnused step. *)
let rec needs_binder_semantics (entries:list P.entry) : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | e :: rest -> binder_rule e.P.rule || needs_binder_semantics rest

(* A Farkas or rewrite entry over a Real-primitive schema: the typed Int/Real
   replay (real_farkas) and the Real rewrite check (real_rewrite) read the
   Real laws. *)
let real_rule (r:U.rule) : bool = U.ArithmeticFarkas? r || r = U.RewriteRule

(* An entry whose formula is a closed Real order clause (real_order reads the
   Real laws for exactly those). *)
let real_order_entry (e:P.entry) : bool = order_rule e.P.rule && real_order_clause e.P.formula

let real_product_entry (e:P.entry) : bool =
  e.P.rule = U.Unverified "th-lemma" && e.P.formula = R.false_expr

let real_equality_entry (e:P.entry) : bool =
  e.P.rule = U.Unverified "th-lemma" &&
  (match U.classify_fact e.P.formula with
   | Some (U.Equal a b) | Some (U.Observational a b) -> get_sort a = LA.real_s && get_sort b = LA.real_s
   | _ -> false)

let rec needs_real_semantics (s:S.checked_schema) (entries:list P.entry) : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | e :: rest ->
    (RL.real_primitive s && (real_rule e.P.rule || real_order_entry e || real_product_entry e || real_equality_entry e)) ||
    needs_real_semantics s rest

(* An entry whose formula is a guarded Int div/mod clause (division_order reads
   the division laws for exactly those). *)
let division_order_entry (e:P.entry) : bool = order_rule e.P.rule && division_clause e.P.formula

let rec needs_division_semantics (entries:list P.entry) : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | e :: rest -> division_order_entry e || needs_division_semantics rest

let lemma_division_node_entry (s:S.checked_schema) (cache:I.index_tree U.checked_fact) (e:P.entry)
                              (node:U.proof_node)
  : Lemma (requires prepare_entry s cache e == Some node /\ division_node node)
          (ensures division_order_entry e) = ()

let rec lemma_needs_real_primitive (s:S.checked_schema) (entries:list P.entry)
  : Lemma (requires needs_real_semantics s entries) (ensures RL.real_primitive s) (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    if not (RL.real_primitive s && (real_rule e.P.rule || real_order_entry e || real_product_entry e || real_equality_entry e))
    then lemma_needs_real_primitive s rest

let lemma_real_node_entry (s:S.checked_schema) (cache:I.index_tree U.checked_fact) (e:P.entry)
                          (node:U.proof_node)
  : Lemma (requires prepare_entry s cache e == Some node /\ real_node s node)
          (ensures RL.real_primitive s /\
                   (real_rule e.P.rule \/ real_order_entry e \/ real_product_entry e \/ real_equality_entry e)) = ()

let rec lemma_entries (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (assertions:list expr) (cache:I.index_tree U.checked_fact)
                      (next pending:nat) (entries:list P.entry) (result:I.index_tree U.checked_fact)
  : Lemma (requires T.truths s bc eq other assertions /\ cache_sound s bc eq other cache /\
                    (needs_forall_semantics entries ==> Q.forall_elimination_model s bc other) /\
                    (needs_forall_truth entries ==> Q.forall_model s bc other) /\
                    (needs_binder_semantics entries ==>
                       Q.forall_model s bc other /\ E.exists_model s bc other /\
                       (RL.real_primitive s ==> RL.real_model s bc eq other)) /\
                    (needs_real_semantics s entries ==> RL.real_model s bc eq other) /\
                    (needs_division_semantics entries ==> DV.division_laws s bc eq other) /\
                    check_entries s assertions cache next pending entries == Some (result, 0))
          (ensures cache_sound s bc eq other result)
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    let node = Some?.v (prepare_entry s cache e) in
    let fact, local = Some?.v (check_node_cached s assertions node) in
    lemma_pending s assertions (I.index_put cache next fact) (next + 1) (pending + local) rest result 0;
    lemma_premise_lookup s bc eq other cache e.premise_ids node.premises;
    lemma_check_node_context s assertions node fact local;
    if real_node s node then lemma_real_node_entry s cache e node;
    if division_node node then lemma_division_node_entry s cache e node;
    lemma_check_node_cached s bc eq other assertions node fact;
    lemma_cache_insert s bc eq other cache next fact;
    lemma_entries s bc eq other assertions (I.index_put cache next fact) (next + 1)
      (pending + local) rest result

let lemma_check_document (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (doc:P.document)
  : Lemma (requires check_document s doc == Some 0 /\
                    (needs_forall_semantics doc.entries ==> Q.forall_elimination_model s bc other) /\
                    (needs_forall_truth doc.entries ==> Q.forall_model s bc other) /\
                    (needs_binder_semantics doc.entries ==>
                       Q.forall_model s bc other /\ E.exists_model s bc other /\
                       (RL.real_primitive s ==> RL.real_model s bc eq other)) /\
                    (needs_real_semantics s doc.entries ==> RL.real_model s bc eq other) /\
                    (needs_division_semantics doc.entries ==> DV.division_laws s bc eq other))
          (ensures not (T.truths s bc eq other doc.assertions)) =
  if T.truths s bc eq other doc.assertions then (
    let cache, _ = Some?.v (check_entries s doc.assertions I.Empty 0 0 doc.entries) in
    lemma_entries s bc eq other doc.assertions I.Empty 0 0 doc.entries cache;
    assert (doc.root >= 0);
    let root = Some?.v (I.index_find cache doc.root) in
    assert (I.index_get cache doc.root == Some root);
    assert (fact_valid s root /\ fact_holds s bc eq other root);
    assert (T.truth s bc eq other R.false_expr);
    assert_norm (T.cut 1 R.false_expr == B.Bool false);
    T.lemma_cut s bc eq other 1 R.false_expr)

let rec diagnose_entries (s:S.checked_schema) (assertions:list expr)
                         (cache:IT.t U.checked_fact) (next pending:nat)
                         (unmet:list P.unmet_obligation) (entries:list P.entry)
  : Tot P.entries_diagnostic (decreases entries) =
  match entries with
  | [] -> P.EntriesChecked cache pending (L.rev unmet)
  | e :: rest ->
    let reject = P.EntriesRejected (P.DocumentRejected P.ProofEntry (Some next) (Some e.formula)) in
    match prepare_entry_table s cache e with
    | None -> reject
    | Some node ->
      (match check_node_cached s assertions node with
       | None -> reject
       | Some (fact, local) ->
         let cache = IT.put cache next fact in
         let unmet =
           if local = 0 then unmet
           else {
             P.obligation_index = next; obligation_rule = e.rule;
             obligation_conclusion = fact.conclusion;
             obligation_premises = U.premise_judgments node.premises;
             obligation_source = e.formula; obligation_count = local;
           } :: unmet in
         diagnose_entries s assertions cache (next + 1) (pending + local) unmet rest)

let diagnostic_entries_result (d:P.entries_diagnostic) : option (IT.t U.checked_fact & nat) =
  match d with P.EntriesChecked cache pending _ -> Some (cache, pending) | P.EntriesRejected _ -> None

let rec lemma_diagnose_entries (s:S.checked_schema) (assertions:list expr)
                               (cache:IT.t U.checked_fact) (tree:I.index_tree U.checked_fact) (next pending:nat)
                               (unmet:list P.unmet_obligation) (entries:list P.entry)
  : Lemma (requires P.agrees cache tree)
          (ensures P.entries_agree (diagnostic_entries_result (diagnose_entries s assertions cache next pending unmet entries))
                                   (check_entries s assertions tree next pending entries))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    P.lemma_agrees_opt_map cache tree e.premise_ids;
    (match prepare_entry_table s cache e with
     | None -> ()
     | Some node ->
       (match check_node_cached s assertions node with
        | None -> ()
        | Some (fact, local) ->
          let unmet =
            if local = 0 then unmet
            else {
              P.obligation_index = next; obligation_rule = e.rule;
              obligation_conclusion = fact.conclusion;
              obligation_premises = U.premise_judgments node.premises;
              obligation_source = e.formula; obligation_count = local;
            } :: unmet in
          P.lemma_agrees_put cache tree next fact;
          lemma_diagnose_entries s assertions (IT.put cache next fact) (I.index_put tree next fact)
            (next + 1) (pending + local) unmet rest))

let diagnose_document (schema:S.schema) (doc:P.document) : P.document_diagnostic =
  if not (S.valid schema) then P.DocumentRejected P.LogicalDeclarations None None
  else if not (boolean_expressions schema doc.assertions && U.ordinary_facts doc.assertions)
  then P.DocumentRejected P.OriginalAssertions None None
  else match diagnose_entries schema doc.assertions IT.empty 0 0 [] doc.entries with
  | P.EntriesRejected reason ->
    (match reason with
     | P.DocumentRejected _ _ _ -> reason
     | P.DocumentChecked _ _ -> P.DocumentRejected P.ProofEntry None None)
  | P.EntriesChecked cache pending unmet ->
    (match IT.find cache doc.root with
     | None -> P.DocumentRejected P.MissingRoot None None
     | Some fact ->
       if fact.conclusion = U.Holds R.false_expr && fact.hypotheses = []
       then P.DocumentChecked pending unmet else P.DocumentRejected P.OpenRoot None None)

let diagnostic_result (d:P.document_diagnostic) : option nat =
  match d with P.DocumentChecked n _ -> Some n | P.DocumentRejected _ _ _ -> None

let lemma_diagnose_document (schema:S.schema) (doc:P.document)
  : Lemma (diagnostic_result (diagnose_document schema doc) == check_document schema doc) =
  if S.valid schema && boolean_expressions schema doc.assertions && U.ordinary_facts doc.assertions
  then (
    lemma_diagnose_entries schema doc.assertions IT.empty I.Empty 0 0 [] doc.entries;
    match diagnose_entries schema doc.assertions IT.empty 0 0 [] doc.entries with
    | P.EntriesRejected reason ->
      (match reason with P.DocumentRejected _ _ _ | P.DocumentChecked _ _ -> ())
    | P.EntriesChecked cache _ _ ->
      (match IT.find cache doc.root with None -> () | Some _ -> ()))

let check_document_diagnosed (schema:S.schema) (doc:P.document)
  : result:(option nat & P.document_diagnostic){
     fst result == check_document schema doc /\
     diagnostic_result (snd result) == fst result} =
  lemma_diagnose_document schema doc;
  let diagnostic = diagnose_document schema doc in
  diagnostic_result diagnostic, diagnostic

let epsilon_definition (s:S.checked_schema) (e:P.entry) : option (E.definition s) =
  if e.rule <> U.Skolemization || e.premise_ids <> [] ||
     not (Some? (expression_budget 4096 e.formula)) then None
  else match U.classify_fact e.formula with
  | Some (U.Observational a b) -> E.definition_of s a b
  | _ -> None

let rec collect_epsilon (s:S.checked_schema) (defs:list SK.definition) (entries:list P.entry)
  : Tot (option (list SK.definition)) (decreases entries) =
  match entries with
  | [] -> Some defs
  | e :: rest ->
    (match epsilon_definition s e with
     | None -> collect_epsilon s defs rest
     | Some d ->
       (match SK.add_definition defs d with
        | None -> None
        | Some more -> collect_epsilon s more rest))

let rec certify_epsilon (s:S.checked_schema) (defs:list SK.definition)
  : Tot (option (list (E.definition s))) (decreases defs) =
  match defs with
  | [] -> Some []
  | d :: rest ->
    if not (E.eligible s d) then None
    else match certify_epsilon s rest with None -> None | Some more -> Some (d :: more)

(* The collections list definitions in document order, oldest first, while an
   ordered context lists the newest first (each definition's witnesses fresh in
   every later body). Ordering the reversed list makes the common case a single
   `SK.ordered_context` pass instead of `order_context`'s repeated selection,
   which is cubic in the number of definitions (243 merged definitions: 17 s
   instead of 0.2 s). The selection still runs when the reversed list is not
   ordered, and every result passes the same gates below. *)
let certified_context (s:S.checked_schema) (doc:P.document) (collected:option (list SK.definition))
  : ds:list (E.definition s){SK.ordered_context (E.erase s ds) /\ SK.fresh_inputs (E.erase s ds) doc.assertions} =
  match collected with
  | None -> []
  | Some defs ->
    (match SK.order_context (L.length defs) (L.rev defs) with
     | None -> []
     | Some ordered ->
       (match certify_epsilon s ordered with
        | None -> []
        | Some ds ->
          if SK.ordered_context (E.erase s ds) && SK.fresh_inputs (E.erase s ds) doc.assertions
          then ds else []))

(* A closed Skolem step inside an NNF certificate (Z3NnfReplay): the shape of
   a top-level step (premise-free, no binder sorts, a closed eligible
   definition of Skolem CONSTANTS: E.definition_of, so dependent Skolem
   functions and open steps are never collected), and a formula in the
   schema context, which the elaborated assertions require. *)
let inner_definition (s:S.checked_schema) (b:U.binder_entry) : option (E.definition s) =
  if b.U.binder_name <> "sk" || b.U.binder_premises <> [] || Some? b.U.binder_sorts ||
     not (Some? (expression_budget 4096 b.U.binder_formula)) ||
     not (D.scoped [] b.U.binder_formula && in_context s b.U.binder_formula) then None
  else match U.classify_fact b.U.binder_formula with
  | Some (U.Observational x y) -> E.definition_of s x y
  | _ -> None

let rec collect_inner (s:S.checked_schema) (defs:list SK.definition) (bs:list U.binder_entry)
  : Tot (option (list SK.definition)) (decreases bs) =
  match bs with
  | [] -> Some defs
  | b :: rest ->
    (match inner_definition s b with
     | None -> collect_inner s defs rest
     | Some d ->
       (match SK.add_definition defs d with
        | None -> None
        | Some more -> collect_inner s more rest))

(* The certificate of an entry, when the NNF replay consumes it. *)
let nnf_certificate (e:P.entry) : option U.binder_certificate =
  match e.P.rule with
  | U.QuantifierIntroduction c -> if NR.nnf_root c then Some c else None
  | _ -> None

(* The top-level Skolem steps and the inner Skolem steps of NNF certificates,
   in document order. *)
let rec collect_merged (s:S.checked_schema) (defs:list SK.definition) (entries:list P.entry)
  : Tot (option (list SK.definition)) (decreases entries) =
  match entries with
  | [] -> Some defs
  | e :: rest ->
    let here =
      match epsilon_definition s e with
      | None -> Some defs
      | Some d -> SK.add_definition defs d in
    (match here with
     | None -> None
     | Some defs' ->
       (match nnf_certificate e with
        | None -> collect_merged s defs' rest
        | Some c ->
          (match collect_inner s defs' c.U.binder_entries with
           | None -> None
           | Some more -> collect_merged s more rest)))

(* The epsilon context: the definitions of the top-level Skolem steps and of
   the closed inner Skolem steps of NNF certificates, through the unchanged
   gates (E.eligible, disjoint witnesses, an acyclic order, witnesses fresh in
   every original assertion). When the merged collection fails a gate, the
   top-level context alone is used, exactly as before; the inner Skolem steps
   then stay pending. *)
let epsilon_context (s:S.checked_schema) (doc:P.document)
  : ds:list (E.definition s){SK.ordered_context (E.erase s ds) /\ SK.fresh_inputs (E.erase s ds) doc.assertions} =
  match certified_context s doc (collect_merged s [] doc.entries) with
  | [] -> certified_context s doc (collect_epsilon s [] doc.entries)
  | ds -> ds

(* An OPEN Skolem step inside an NNF certificate: a dependent Skolem
   function of outer binders (Z3SortedDependentSkolem). The shape of a
   closed inner step (premise-free, no binder sorts, the 4096-node
   expression budget), a formula that is NOT closed (closed steps are
   inner_definition's), an eligible dependent definition (complete typed
   argument tuples, safe witness functions, typed dependency scope), and a
   closure the kernel accepts as an assertion (closed, Boolean, in the
   schema context). *)
let dependent_definition (s:S.checked_schema) (b:U.binder_entry) : option (DS.definition s) =
  if b.U.binder_name <> "sk" || b.U.binder_premises <> [] || Some? b.U.binder_sorts ||
     not (Some? (expression_budget 4096 b.U.binder_formula)) || D.scoped [] b.U.binder_formula then None
  else match U.classify_fact b.U.binder_formula with
  | Some (U.Observational x y) ->
    (match DS.definition_of s x y with
     | Some d -> if boolean_expression s (DS.closure d) then Some d else None
     | None -> None)
  | _ -> None

let rec collect_dependent (s:S.checked_schema) (defs:list SK.definition) (bs:list U.binder_entry)
  : Tot (option (list SK.definition)) (decreases bs) =
  match bs with
  | [] -> Some defs
  | b :: rest ->
    (match dependent_definition s b with
     | None -> collect_dependent s defs rest
     | Some d ->
       (match SK.add_definition defs d with
        | None -> None
        | Some more -> collect_dependent s more rest))

(* The dependent Skolem steps of every consumed NNF certificate, in document
   order; a duplicate is collected once, a conflicting redefinition of a
   witness fails the collection (SK.add_definition). *)
let rec collect_dependents (s:S.checked_schema) (defs:list SK.definition) (entries:list P.entry)
  : Tot (option (list SK.definition)) (decreases entries) =
  match entries with
  | [] -> Some defs
  | e :: rest ->
    (match nnf_certificate e with
     | None -> collect_dependents s defs rest
     | Some c ->
       (match collect_dependent s defs c.U.binder_entries with
        | None -> None
        | Some more -> collect_dependents s more rest))

let rec certify_dependent (s:S.checked_schema) (defs:list SK.definition)
  : Tot (option (list (DS.definition s))) (decreases defs) =
  match defs with
  | [] -> Some []
  | d :: rest ->
    if not (DS.eligible s d) then None
    else if not (boolean_expression s (DS.closure #s d)) then None
    else match certify_dependent s rest with None -> None | Some more -> Some (d :: more)

(* The dependent context, on top of the closed epsilon context `closed`: the
   collected definitions in an acyclic order (from the reversed collection,
   as certified_context), each eligible, the dependent definitions followed
   by the closed ones an ordered context (every dependent witness fresh in
   every later body, closed bodies included), and every dependent witness
   fresh in every ORIGINAL assertion. Otherwise no dependent definition is
   used and the dependent steps stay pending. *)
let dependent_context (s:S.checked_schema) (doc:P.document)
                      (closed:list (E.definition s){SK.ordered_context (E.erase s closed)})
  : dds:list (DS.definition s){SK.ordered_context (DS.erase s dds @ E.erase s closed) /\
                               SK.fresh_inputs (DS.erase s dds) doc.assertions} =
  match collect_dependents s [] doc.entries with
  | None -> []
  | Some defs ->
    (match SK.order_context (L.length defs) (L.rev defs) with
     | None -> []
     | Some ordered ->
       (match certify_dependent s ordered with
        | None -> []
        | Some dds ->
          if SK.ordered_context (DS.erase s dds @ E.erase s closed) &&
             SK.fresh_inputs (DS.erase s dds) doc.assertions
          then dds else []))

let epsilon_entry (s:S.checked_schema) (ds:list (E.definition s)) (e:P.entry) : bool =
  match epsilon_definition s e with None -> false | Some d -> L.mem d ds

let inner_entry (s:S.checked_schema) (ds:list (E.definition s)) (b:U.binder_entry) : bool =
  match inner_definition s b with None -> false | Some d -> L.mem d ds

(* The choice equations of the used inner definitions, prepended to acc (a
   loop over the certificate). *)
let rec inner_equations (s:S.checked_schema) (ds:list (E.definition s)) (bs:list U.binder_entry)
                        (acc:list expr)
  : Tot (list expr) (decreases bs) =
  match bs with
  | [] -> acc
  | b :: rest ->
    if inner_entry s ds b then
      (match U.classify_fact b.U.binder_formula with
       | Some j -> inner_equations s ds rest (proposition j :: acc)
       | None -> inner_equations s ds rest acc)
    else inner_equations s ds rest acc

let rec epsilon_equations (s:S.checked_schema) (ds:list (E.definition s)) (entries:list P.entry)
  : Tot (list expr) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    let tail =
      match nnf_certificate e with
      | Some c -> inner_equations s ds c.U.binder_entries (epsilon_equations s ds rest)
      | None -> epsilon_equations s ds rest in
    if epsilon_entry s ds e then
      match U.classify_fact e.formula with
      | Some j -> proposition j :: tail
      | None -> tail
    else tail

let rec epsilon_entries (s:S.checked_schema) (ds:list (E.definition s)) (entries:list P.entry)
  : Tot (list P.entry) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    (if epsilon_entry s ds e then { e with P.rule = U.Asserted } else e) :: epsilon_entries s ds rest

(* Only choice equations proved in a fresh, typed model extension become
   assumptions of the unchanged kernel; they are not original inputs. *)
let elaborate_epsilon (s:S.checked_schema) (ds:list (E.definition s)) (doc:P.document) : P.document =
  if ds = [] then doc
  else { doc with P.assertions = doc.assertions @ epsilon_equations s ds doc.entries;
                  P.entries = epsilon_entries s ds doc.entries }

(* Source-node alignment, which both native frontends' readable reports rely
   on (they render the elaborated diagnostic against the ORIGINAL entries):
   elaboration keeps one entry per original entry, at the same index, with
   the same formula and premise ids; only the rule of a used Skolem step
   becomes Asserted. Choice equations are appended to the assertions, and a
   rejected assertion list is reported without an index. *)
let rec lemma_epsilon_entries_aligned (s:S.checked_schema) (ds:list (E.definition s))
                                      (entries:list P.entry) (n:nat)
  : Lemma (requires n < L.length entries)
          (ensures L.length (epsilon_entries s ds entries) == L.length entries /\
                   (let e = L.index entries n in
                    let e' = L.index (epsilon_entries s ds entries) n in
                    e'.P.formula == e.P.formula /\ e'.P.premise_ids == e.P.premise_ids /\
                    (e'.P.rule == e.P.rule \/ (epsilon_entry s ds e /\ e'.P.rule == U.Asserted))))
          (decreases entries) =
  match entries with
  | _ :: rest ->
    if n > 0 then lemma_epsilon_entries_aligned s ds rest (n - 1)
    else if Cons? rest then lemma_epsilon_entries_aligned s ds rest 0

(* The closures of the used dependent definitions (closed universal
   equations, proved in the dependent choice extension; not original
   inputs) are appended to the assertions. The replay accepts an open `sk`
   step only when its closure is one of them. *)
let elaborate_dependent (s:S.checked_schema) (dds:list (DS.definition s)) (doc:P.document) : P.document =
  if dds = [] then doc
  else { doc with P.assertions = doc.assertions @ DS.closures s dds }

(* The whole elaboration of the epsilon route: the closed choice equations
   of the epsilon context, then the closures of the dependent context. *)
let elaborate_full (s:S.checked_schema) (doc:P.document) : P.document =
  let ds = epsilon_context s doc in
  elaborate_dependent s (dependent_context s doc ds) (elaborate_epsilon s ds doc)

let check_document_epsilon (schema:S.schema) (doc:P.document) : option nat =
  if not (S.valid schema) then None
  else check_document schema (elaborate_full schema doc)

let diagnose_document_epsilon (schema:S.schema) (doc:P.document) : P.document_diagnostic =
  if not (S.valid schema) then P.DocumentRejected P.LogicalDeclarations None None
  else diagnose_document schema (elaborate_full schema doc)

let lemma_diagnose_document_epsilon (schema:S.schema) (doc:P.document)
  : Lemma (diagnostic_result (diagnose_document_epsilon schema doc) == check_document_epsilon schema doc) =
  if S.valid schema then
    lemma_diagnose_document schema (elaborate_full schema doc)

let check_document_epsilon_diagnosed (schema:S.schema) (doc:P.document)
  : result:(option nat & P.document_diagnostic){
      fst result == check_document_epsilon schema doc /\ diagnostic_result (snd result) == fst result} =
  lemma_diagnose_document_epsilon schema doc;
  let diagnostic = diagnose_document_epsilon schema doc in
  diagnostic_result diagnostic, diagnostic

(* The choice equations of the used inner definitions hold in every model of
   the epsilon context (in the proof below: the choice extension of the
   original model, never the original model itself). *)
let rec lemma_inner_equations (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (ds:list (E.definition s)) (bs:list U.binder_entry) (acc:list expr)
  : Lemma (requires E.context_model s bc eq other ds /\ T.truths s bc eq other acc)
          (ensures T.truths s bc eq other (inner_equations s ds bs acc))
          (decreases bs) =
  match bs with
  | [] -> ()
  | b :: rest ->
    if inner_entry s ds b then (
      let d = Some?.v (inner_definition s b) in
      E.lemma_context_member s bc eq other ds d;
      match U.classify_fact b.U.binder_formula with
      | Some (U.Observational x y) ->
        E.lemma_definition_parts s x y d;
        T.lemma_boolean_equality s bc eq other x y;
        lemma_inner_equations s bc eq other ds rest (proposition (U.Observational x y) :: acc)
      | _ -> ())
    else lemma_inner_equations s bc eq other ds rest acc

let rec lemma_epsilon_equations (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                               (ds:list (E.definition s)) (entries:list P.entry)
  : Lemma (requires E.context_model s bc eq other ds)
          (ensures T.truths s bc eq other (epsilon_equations s ds entries))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    lemma_epsilon_equations s bc eq other ds rest;
    (match nnf_certificate e with
     | Some c -> lemma_inner_equations s bc eq other ds c.U.binder_entries (epsilon_equations s ds rest)
     | None -> ());
    if epsilon_entry s ds e then (
      let d = Some?.v (epsilon_definition s e) in
      E.lemma_context_member s bc eq other ds d;
      match U.classify_fact e.formula with
      | Some (U.Observational a b) ->
        E.lemma_definition_parts s a b d;
        T.lemma_boolean_equality s bc eq other a b
      | _ -> ())

let rec lemma_truths_append (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (xs ys:list expr)
  : Lemma (T.truths s bc eq other (xs @ ys) ==
           (T.truths s bc eq other xs && T.truths s bc eq other ys))
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_truths_append s bc eq other rest ys

(* The elimination law over GHOST bodies (Q.elimination_case), read off the
   universal law case by case. *)
let lemma_full_forall_elimination (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                 (other:V.interpretation base (S.signature s))
  : Lemma (requires Q.forall_model s bc other)
          (ensures Q.forall_elimination_model s bc other) =
  introduce forall (bound:list sort) (body:Q.ghost_body base s bound)
                   (vs:V.arguments base (S.signature s) (L.rev bound)).
    Q.elimination_case s bc other bound body vs
  with assert (Q.forall_case s bc other bound body)

(* ONE consistent extension per document, built from the ORIGINAL model:
   the closed choice context first (Z3SortedSkolem.build), then the
   dependent context on top of it (Z3SortedDependentSkolem.build). *)
let full_extension (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                   (doc:P.document) (other:V.interpretation base (S.signature s))
  : GTot (V.interpretation base (S.signature s)) =
  let ds = epsilon_context s doc in
  DS.build s bc eq choice (dependent_context s doc ds) (E.build s bc eq choice ds other)

(* The extension keeps the quantifiers (hence both quantifier laws) and the
   truth of every ORIGINAL assertion, and makes every generated assertion
   (closed choice equation, dependent closure) true: the elaborated
   assertions hold in it exactly when the original ones hold in `other`. *)
let lemma_full_extension (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                         (doc:P.document) (other:V.interpretation base (S.signature s))
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other)
          (ensures (let j = full_extension s bc eq choice doc other in
                    j.V.quantification == other.V.quantification /\
                    Q.forall_model s bc j /\ E.exists_model s bc j /\
                    T.truths s bc eq j doc.assertions == T.truths s bc eq other doc.assertions /\
                    T.truths s bc eq j (epsilon_equations s (epsilon_context s doc) doc.entries) /\
                    T.truths s bc eq j (DS.closures s (dependent_context s doc (epsilon_context s doc))) /\
                    T.truths s bc eq j (elaborate_full s doc).P.assertions ==
                      T.truths s bc eq other doc.assertions)) =
  let ds = epsilon_context s doc in
  let dds = dependent_context s doc ds in
  let e1 = E.build s bc eq choice ds other in
  let j = DS.build s bc eq choice dds e1 in
  E.lemma_build_context s bc eq choice ds other;
  E.lemma_build_inputs s bc eq choice ds other doc.assertions;
  E.lemma_build_quantification s bc eq choice ds other;
  E.lemma_quantification_models s bc other e1;
  DS.lemma_ordered_append (DS.erase s dds) (E.erase s ds);
  DS.lemma_build_context s bc eq choice dds e1;
  DS.lemma_build_inputs s bc eq choice dds e1 doc.assertions;
  DS.lemma_build_closed s bc eq choice dds e1 ds;
  DS.lemma_build_quantification s bc eq choice dds e1;
  E.lemma_quantification_models s bc e1 j;
  lemma_epsilon_equations s bc eq j ds doc.entries;
  DS.lemma_context_truths s bc eq j dds;
  lemma_truths_append s bc eq j doc.assertions (epsilon_equations s ds doc.entries);
  lemma_truths_append s bc eq j (elaborate_epsilon s ds doc).P.assertions (DS.closures s dds)

(* The same extension keeps the Real laws of `other` (a witness is never a
   classified Real operator), so the Real hypothesis transfers from the
   original model to the elaborated one. *)
let lemma_full_extension_real (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                              (doc:P.document) (other:V.interpretation base (S.signature s))
                              (reals:RL.carrier base)
  : Lemma (requires RL.real_laws s bc eq other reals)
          (ensures RL.real_laws s bc eq (full_extension s bc eq choice doc other) reals) =
  let ds = epsilon_context s doc in
  RX.lemma_build_real s bc eq choice ds other reals;
  RX.lemma_dbuild_real s bc eq choice (dependent_context s doc ds) (E.build s bc eq choice ds other) reals

let lemma_full_extension_real_model (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                    (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                                    (doc:P.document) (other:V.interpretation base (S.signature s))
  : Lemma (requires RL.real_model s bc eq other)
          (ensures RL.real_model s bc eq (full_extension s bc eq choice doc other)) =
  FStar.Classical.exists_elim (RL.real_model s bc eq (full_extension s bc eq choice doc other))
    #(RL.carrier base) #(fun reals -> RL.real_laws s bc eq other reals) ()
    (fun reals -> lemma_full_extension_real s bc eq choice doc other reals)

(* The same extension keeps the Sorted Int division laws of `other` (a witness
   is never a classified division operator). *)
let lemma_full_extension_division (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                  (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                                  (doc:P.document) (other:V.interpretation base (S.signature s))
  : Lemma (requires DV.division_laws s bc eq other)
          (ensures DV.division_laws s bc eq (full_extension s bc eq choice doc other)) =
  let ds = epsilon_context s doc in
  DX.lemma_build_division s bc eq choice ds other;
  DX.lemma_dbuild_division s bc eq choice (dependent_context s doc ds) (E.build s bc eq choice ds other)

let lemma_check_document_epsilon (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                 (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                                 (other:V.interpretation base (S.signature s)) (doc:P.document)
  : Lemma (requires check_document_epsilon s doc == Some 0 /\
                    Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (RL.real_primitive s ==> RL.real_model s bc eq other) /\
                    DV.division_laws s bc eq other)
          (ensures not (T.truths s bc eq other doc.assertions)) =
  if T.truths s bc eq other doc.assertions then (
    let j = full_extension s bc eq choice doc other in
    lemma_full_extension s bc eq choice doc other;
    lemma_full_forall_elimination s bc j;
    if RL.real_primitive s then lemma_full_extension_real_model s bc eq choice doc other;
    lemma_full_extension_division s bc eq choice doc other;
    if needs_real_semantics s (elaborate_full s doc).P.entries then
      lemma_needs_real_primitive s (elaborate_full s doc).P.entries;
    lemma_check_document s bc eq j (elaborate_full s doc))
