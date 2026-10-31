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

let rec equations (facts:list expr) : Tot (list U.judgment) (decreases facts) =
  match facts with
  | [] -> []
  | App f [a; b] :: rest ->
    if f = R.eq_decl (get_sort a) && get_sort a = get_sort b
    then U.Equal a b :: equations rest else equations rest
  | _ :: rest -> equations rest

let rec equations_hold (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (js:list U.judgment) : Tot bool (decreases js) =
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
                    (origin:expr) (known:list expr) : Tot bool (decreases known) =
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
    lemma_propositional (T.truth_at s bc eq other scope rho) arithmetic false a b;
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
        lemma_propositional (T.truth_at s bc eq other scope rho) arithmetic true c d;
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
  assert_norm (congruent_boolean arithmetic search_atoms scope fuel a b ==
    (search_atoms && scope <> [] && Some? (expression_budget 256 a) && Some? (expression_budget 256 b) &&
     (T.cut 64 a <> B.Atom a || T.cut 64 b <> B.Atom b) &&
     N.shape_equal_by
       (congruent_atom arithmetic scope fuel)
       32 (N.normalize false (T.cut 64 a)) (N.normalize false (T.cut 64 b))));
  assert (N.shape_equal_by
    (congruent_atom arithmetic scope fuel)
    32 (N.normalize false (T.cut 64 a)) (N.normalize false (T.cut 64 b)));
  let same = congruent_atom arithmetic scope fuel in
  let atoms (x y:expr)
    : Lemma (same x y ==>
             T.truth_at s bc eq other scope rho x == T.truth_at s bc eq other scope rho y) =
    if same x y then lemma_congruent s bc eq other scope rho arithmetic false (atom_fuel fuel) x y in
  FStar.Classical.forall_intro_2 atoms;
  N.lemma_shape_equal_by_sound (T.truth_at s bc eq other scope rho) same
    32 (N.normalize false (T.cut 64 a)) (N.normalize false (T.cut 64 b));
  N.lemma_normalize_sound (T.truth_at s bc eq other scope rho) false (T.cut 64 a);
  N.lemma_normalize_sound (T.truth_at s bc eq other scope rho) false (T.cut 64 b);
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
          (ensures not (B.eval_args (T.truth s bc eq other) B.Or (L.map B.Atom (negative_atoms facts))))
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

let lemma_quantifier_equality (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (conclusion:expr)
  : Lemma (requires D.scoped [] conclusion /\ quantifier_equality conclusion)
          (ensures T.truth s bc eq other conclusion) =
  match conclusion with
  | App _ [Quantifier k bs t a; Quantifier k' bs' t' b] ->
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
      DT.lemma_propositional (T.truth_at s bc eq other body_scope bound)
        (B.Eq (T.cut 64 a) (T.cut 64 b));
      T.lemma_boolean s bc (left vs);
      T.lemma_boolean s bc (right vs)
    in
    FStar.Classical.forall_intro pointwise;
    V.lemma_quantifier_congruence sigma (T.interpretation s bc eq other)
      [] rho k bs bool_sort a b;
    T.lemma_equality s bc eq other (Quantifier k bs t a) (Quantifier k' bs' t' b)
  | _ -> ()

let direct_consequence (s:S.checked_schema) (facts:list expr) (conclusion:expr) : bool =
  (D.scoped [] conclusion && get_sort conclusion = bool_sort && DT.simple_consequence facts conclusion) ||
  equality_consequence s facts conclusion ||
  (D.scoped [] conclusion && quantifier_equality conclusion) ||
  negative_exhaustion s facts || cyclic_conflict s facts || reconstruction_conflict s facts facts ||
  DT.consequence s facts conclusion

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
  else DT.lemma_consequence s bc eq other facts conclusion

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
               (p:U.checked_fact) : bool =
  not (T.truths s bc eq other p.hypotheses) || T.truth s bc eq other (proposition p.conclusion)

let rec facts_hold (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (ps:list U.checked_fact) : Tot bool (decreases ps) =
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

let rec lemma_arithmetic_assumptions (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                    (facts lits:list expr)
  : Lemma (requires T.truths s bc eq other facts /\
                    not (B.eval_args (T.truth s bc eq other) B.Or (L.map B.Atom lits)))
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
    let inherited = U.premise_hypotheses node.premises in
    let hypotheses =
      if lemma_step node then
        match node.premises with [p] -> remaining_hypotheses p.hypotheses conclusion | _ -> inherited
      else if node.kind = U.LemmaRule then U.remaining_hypotheses inherited conclusion
      else inherited in
    let fact = { U.conclusion = node.conclusion; hypotheses = hypotheses } in
    let checked =
      arithmetic_farkas node || quantifier_instantiation node || quantifier_flattening node || lemma_step node ||
      (node.kind <> U.LemmaRule && consequence s (propositions node.premises) conclusion) ||
      DT.consequence s (scoped_propositions node.premises) (scoped_proposition fact) in
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

let lemma_check_node_cached (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (assertions:list expr) (node:U.proof_node) (fact:U.checked_fact)
  : Lemma (requires T.truths s bc eq other assertions /\ facts_hold s bc eq other node.premises /\
                    facts_valid s node.premises /\
                    (quantifier_instantiation node ==> Q.forall_elimination_model s bc other) /\
                    (quantifier_flattening node ==> Q.forall_model s bc other) /\
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
    else if node.kind <> U.LemmaRule && consequence s (propositions node.premises) conclusion then (
      if T.truths s bc eq other fact.hypotheses then (
        lemma_premise_hypotheses s bc eq other node.premises;
        lemma_consequence s bc eq other (propositions node.premises) conclusion))
    else (
      lemma_scoped_propositions s bc eq other node.premises;
      DT.lemma_consequence s bc eq other (scoped_propositions node.premises) (scoped_proposition fact);
      lemma_scoped_proposition s bc eq other fact)

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

let rec lemma_entries (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (assertions:list expr) (cache:I.index_tree U.checked_fact)
                      (next pending:nat) (entries:list P.entry) (result:I.index_tree U.checked_fact)
  : Lemma (requires T.truths s bc eq other assertions /\ cache_sound s bc eq other cache /\
                    (needs_forall_semantics entries ==> Q.forall_elimination_model s bc other) /\
                    (needs_forall_truth entries ==> Q.forall_model s bc other) /\
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
    lemma_check_node_cached s bc eq other assertions node fact;
    lemma_cache_insert s bc eq other cache next fact;
    lemma_entries s bc eq other assertions (I.index_put cache next fact) (next + 1)
      (pending + local) rest result

let lemma_check_document (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (doc:P.document)
  : Lemma (requires check_document s doc == Some 0 /\
                    (needs_forall_semantics doc.entries ==> Q.forall_elimination_model s bc other) /\
                    (needs_forall_truth doc.entries ==> Q.forall_model s bc other))
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

let epsilon_context (s:S.checked_schema) (doc:P.document)
  : ds:list (E.definition s){SK.ordered_context (E.erase s ds) /\ SK.fresh_inputs (E.erase s ds) doc.assertions} =
  match collect_epsilon s [] doc.entries with
  | None -> []
  | Some defs ->
    (match SK.order_context (L.length defs) defs with
     | None -> []
     | Some ordered ->
       (match certify_epsilon s ordered with
        | None -> []
        | Some ds ->
          if SK.ordered_context (E.erase s ds) && SK.fresh_inputs (E.erase s ds) doc.assertions
          then ds else []))

let epsilon_entry (s:S.checked_schema) (ds:list (E.definition s)) (e:P.entry) : bool =
  match epsilon_definition s e with None -> false | Some d -> L.mem d ds

let rec epsilon_equations (s:S.checked_schema) (ds:list (E.definition s)) (entries:list P.entry)
  : Tot (list expr) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    if epsilon_entry s ds e then
      match U.classify_fact e.formula with
      | Some j -> proposition j :: epsilon_equations s ds rest
      | None -> epsilon_equations s ds rest
    else epsilon_equations s ds rest

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

let check_document_epsilon (schema:S.schema) (doc:P.document) : option nat =
  if not (S.valid schema) then None
  else check_document schema (elaborate_epsilon schema (epsilon_context schema doc) doc)

let diagnose_document_epsilon (schema:S.schema) (doc:P.document) : P.document_diagnostic =
  if not (S.valid schema) then P.DocumentRejected P.LogicalDeclarations None None
  else diagnose_document schema (elaborate_epsilon schema (epsilon_context schema doc) doc)

let lemma_diagnose_document_epsilon (schema:S.schema) (doc:P.document)
  : Lemma (diagnostic_result (diagnose_document_epsilon schema doc) == check_document_epsilon schema doc) =
  if S.valid schema then
    lemma_diagnose_document schema (elaborate_epsilon schema (epsilon_context schema doc) doc)

let check_document_epsilon_diagnosed (schema:S.schema) (doc:P.document)
  : result:(option nat & P.document_diagnostic){
      fst result == check_document_epsilon schema doc /\ diagnostic_result (snd result) == fst result} =
  lemma_diagnose_document_epsilon schema doc;
  let diagnostic = diagnose_document_epsilon schema doc in
  diagnostic_result diagnostic, diagnostic

let rec lemma_epsilon_equations (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                               (ds:list (E.definition s)) (entries:list P.entry)
  : Lemma (requires E.context_model s bc eq other ds)
          (ensures T.truths s bc eq other (epsilon_equations s ds entries))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    if epsilon_entry s ds e then (
      let d = Some?.v (epsilon_definition s e) in
      E.lemma_context_member s bc eq other ds d;
      match U.classify_fact e.formula with
      | Some (U.Observational a b) ->
        E.lemma_definition_parts s a b d;
        T.lemma_boolean_equality s bc eq other a b
      | _ -> ());
    lemma_epsilon_equations s bc eq other ds rest

let rec lemma_truths_append (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (xs ys:list expr)
  : Lemma (T.truths s bc eq other (xs @ ys) ==
           (T.truths s bc eq other xs && T.truths s bc eq other ys))
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_truths_append s bc eq other rest ys

let lemma_full_forall_elimination (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                 (other:V.interpretation base (S.signature s))
  : Lemma (requires Q.forall_model s bc other)
          (ensures Q.forall_elimination_model s bc other) =
  let at (bound:list sort)
    : Lemma (forall (body:V.arguments base (S.signature s) (L.rev bound) ->
                         V.value base (S.signature s) bool_sort)
                   (vs:V.arguments base (S.signature s) (L.rev bound)).
        T.truth_value s bc (other.quantification Forall_k bound bool_sort body) ==>
        T.truth_value s bc (body vs)) =
    let body_at (body:V.arguments base (S.signature s) (L.rev bound) ->
                     V.value base (S.signature s) bool_sort)
      : Lemma (forall (vs:V.arguments base (S.signature s) (L.rev bound)).
          T.truth_value s bc (other.quantification Forall_k bound bool_sort body) ==>
          T.truth_value s bc (body vs)) =
      assert (T.truth_value s bc (other.quantification Forall_k bound bool_sort body) <==>
        (forall (vs:V.arguments base (S.signature s) (L.rev bound)). T.truth_value s bc (body vs))) in
    FStar.Classical.forall_intro body_at in
  FStar.Classical.forall_intro at

let lemma_check_document_epsilon (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                 (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                                 (other:V.interpretation base (S.signature s)) (doc:P.document)
  : Lemma (requires check_document_epsilon s doc == Some 0 /\
                    Q.forall_model s bc other /\ E.exists_model s bc other)
          (ensures not (T.truths s bc eq other doc.assertions)) =
  if T.truths s bc eq other doc.assertions then (
    let ds = epsilon_context s doc in
    let extended = E.build s bc eq choice ds other in
    E.lemma_build_context s bc eq choice ds other;
    E.lemma_build_inputs s bc eq choice ds other doc.assertions;
    E.lemma_build_quantification s bc eq choice ds other;
    E.lemma_quantification_models s bc other extended;
    lemma_full_forall_elimination s bc extended;
    lemma_epsilon_equations s bc eq extended ds doc.entries;
    lemma_truths_append s bc eq extended doc.assertions (epsilon_equations s ds doc.entries);
    lemma_check_document s bc eq extended (elaborate_epsilon s ds doc))
