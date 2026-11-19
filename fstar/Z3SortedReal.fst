module Z3SortedReal

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open FStar.Real
module A = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module I = Z3SortedInteger
module AR = Z3SortedArithmetic
module R = Z3ResolutionProofTheory
module D = Z3Definitions
module L = FStar.List.Tot

noeq
type carrier (base:sort -> Type0) = {
  real_of: base A.real_s -> real;
  real_injective: u:unit{forall (x y:base A.real_s). real_of x == real_of y ==> x == y};
}

let rec real_sorts (ss:list sort) : Tot bool (decreases ss) =
  match ss with [] -> true | s :: rest -> s = A.real_s && real_sorts rest

type operation =
  | Numeral : int -> pos -> operation
  | Calculate : A.operation -> operation
  | Divide
  | ToReal
  | Compare : A.relation -> operation
  | Other

let operation_typed (f:func_decl) (op:operation) : bool =
  match op with
  | Numeral _ _ -> f.domain = [] && f.range = A.real_s
  | Calculate o -> f.range = A.real_s && real_sorts f.domain && (o = A.Add || o = A.Mul || o = A.Sub)
  | Divide -> f.domain = [A.real_s; A.real_s] && f.range = A.real_s
  | ToReal -> f.domain = [A.int_s] && f.range = A.real_s
  | Compare r -> f.domain = [A.real_s; A.real_s] && f.range = bool_sort && r <> A.Eq
  | Other -> true

let classify (f:func_decl) : op:operation{operation_typed f op} =
  if f.range = A.real_s && f.domain = [] && Some? (A.numeral (App f [])) then
    (match A.numeral (App f []) with
     | Some (n, d) -> Numeral n d
     | None -> Other)
  else if f.range = A.real_s && real_sorts f.domain then
    (match A.operation_of f (S.dummy_fields f.domain) with
     | Some A.Add -> Calculate A.Add
     | Some A.Mul -> Calculate A.Mul
     | Some A.Sub -> Calculate A.Sub
     | Some A.Div -> if f.domain = [A.real_s; A.real_s] then Divide else Other
     | _ -> Other)
  else if f.range = A.real_s && f.domain = [A.int_s] then
    (match A.operation_of f (S.dummy_fields f.domain) with Some A.ToReal -> ToReal | _ -> Other)
  else match f.domain with
  | [a; b] ->
    if a = A.real_s && b = A.real_s && f.range = bool_sort then
      (match A.comparison (App f [Var 0 a; Var 0 a]) with
       | Some (r, _, _) -> if r <> A.Eq then Compare r else Other
       | None -> Other)
    else Other
  | _ -> Other

let real_primitive (s:S.checked_schema) : bool = not (V.datatype_sort (S.signature s) A.real_s)

let real_value (#base:sort -> Type0) (s:S.checked_schema) (reals:carrier base)
               (v:V.value base (S.signature s) A.real_s) : real =
  match v with
  | V.Scalar _ x -> reals.real_of x
  | V.Constructor _ _ -> 0.0R

let rec real_values (#base:sort -> Type0) (s:S.checked_schema) (reals:carrier base)
                    (ss:list sort{real_sorts ss}) (xs:V.arguments base (S.signature s) ss)
  : Tot (list real) (decreases ss) =
  match ss, xs with
  | [], [] -> []
  | _ :: rest, x :: tail -> real_value s reals x :: real_values s reals rest tail
  | _, _ -> FStar.Pervasives.false_elim ()

let calculate (o:A.operation) (xs:list real) : real =
  match o with
  | A.Add -> E.numeric_sum xs
  | A.Mul -> E.numeric_product xs
  | _ -> E.numeric_subtract xs

let real_meaning (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (integers:I.carrier base) (reals:carrier base)
                 (f:func_decl) (xs:V.arguments base (S.signature s) f.domain)
                 (v:V.value base (S.signature s) f.range) : prop =
  match classify f with
  | Numeral n d -> real_value s reals v == of_int n /. of_int d
  | Calculate o -> real_value s reals v == calculate o (real_values s reals f.domain xs)
  | Divide ->
    (match xs with
     | [x; y] -> ~(real_value s reals y == 0.0R) ==>
                 real_value s reals v *. real_value s reals y == real_value s reals x
     | _ -> True)
  | ToReal ->
    (match xs with
     | [x] -> real_value s reals v == of_int (I.number s integers x)
     | _ -> True)
  | Compare r ->
    (match xs with
     | [x; y] -> (T.truth_value s bc v == true <==>
                  E.numeric_relation r (real_value s reals x) (real_value s reals y))
     | _ -> True)
  | Other -> True

let real_laws (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
              (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
              (reals:carrier base) : prop =
  real_primitive s /\
  (forall (f:func_decl) (xs:V.arguments base (S.signature s) f.domain).
     real_meaning s bc model.T.integers reals f xs (T.application s bc model other f xs))

(* The kernel-facing hypothesis: SOME Real carrier makes the laws hold for
   this Sorted interpretation (kernel theorems need no new parameter). *)
let real_model (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
               (model:T.scalar_model base) (other:V.interpretation base (S.signature s)) : prop =
  exists (reals:carrier base). real_laws s bc model other reals

let real_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
            (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
            (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
            (e:expr) : GTot real =
  if D.scoped scope e && get_sort e = A.real_s
  then real_value s reals (T.evaluate_at s bc model other scope rho e)
  else 0.0R

let valuation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
              (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
              (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
  : expr -> real =
  fun e -> real_at s bc model other reals scope rho e

let numeric_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
               (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
               (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
               (e:expr) : GTot real =
  if get_sort e = A.int_s then of_int (AR.integer s bc model other scope rho e)
  else real_at s bc model other reals scope rho e

let numeric_valuation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
  : expr -> real =
  fun e -> numeric_at s bc model other reals scope rho e

(* ---------------------------------------------------------------------- *)
(* Canonical declarations                                                   *)
(* ---------------------------------------------------------------------- *)

let real_numeral_decl (n:int) (d:pos) : func_decl = {
  decl_name = "real"; domain = []; range = A.real_s; interp = Some op_num_rational; int_params = [n; d];
}

let real_binary_decl (name:string) (tag:decl_kind) (range:sort) : func_decl = {
  decl_name = name; domain = [A.real_s; A.real_s]; range = range; interp = Some tag; int_params = [];
}

let real_plus_decl : func_decl = real_binary_decl "+" op_arith_add A.real_s
let real_minus_decl : func_decl = real_binary_decl "-" op_arith_sub A.real_s
let real_times_decl : func_decl = real_binary_decl "*" op_arith_mul A.real_s
let real_divide_decl : func_decl = real_binary_decl "/" op_arith_div A.real_s
let real_le_decl : func_decl = real_binary_decl "<=" op_arith_le bool_sort
let real_lt_decl : func_decl = real_binary_decl "<" op_arith_lt bool_sort
let real_ge_decl : func_decl = real_binary_decl ">=" op_arith_ge bool_sort
let real_gt_decl : func_decl = real_binary_decl ">" op_arith_gt bool_sort

let to_real_decl : func_decl = {
  decl_name = "to_real"; domain = [A.int_s]; range = A.real_s; interp = Some op_to_real; int_params = [];
}

let lemma_classify_numeral (n:int) (d:pos)
  : Lemma (classify (real_numeral_decl n d) == Numeral n d) = ()

let lemma_classify_canonical ()
  : Lemma (classify real_plus_decl == Calculate A.Add /\
           classify real_minus_decl == Calculate A.Sub /\
           classify real_times_decl == Calculate A.Mul /\
           classify real_divide_decl == Divide /\
           classify to_real_decl == ToReal /\
           classify real_le_decl == Compare A.Le /\
           classify real_lt_decl == Compare A.Lt /\
           classify real_ge_decl == Compare A.Ge /\
           classify real_gt_decl == Compare A.Gt /\
           classify (R.eq_decl A.real_s) == Other) =
  assert_norm (classify real_plus_decl == Calculate A.Add);
  assert_norm (classify real_minus_decl == Calculate A.Sub);
  assert_norm (classify real_times_decl == Calculate A.Mul);
  assert_norm (classify real_divide_decl == Divide);
  assert_norm (classify to_real_decl == ToReal);
  assert_norm (classify real_le_decl == Compare A.Le);
  assert_norm (classify real_lt_decl == Compare A.Lt);
  assert_norm (classify real_ge_decl == Compare A.Ge);
  assert_norm (classify real_gt_decl == Compare A.Gt);
  assert_norm (classify (R.eq_decl A.real_s) == Other)

(* ---------------------------------------------------------------------- *)
(* Classified Real operators are theory operators                          *)
(* ---------------------------------------------------------------------- *)

let theory_tag (f:func_decl) : bool =
  f.interp = Some op_num_rational || f.interp = Some op_arith_add || f.interp = Some op_arith_mul ||
  f.interp = Some op_arith_sub || f.interp = Some op_arith_div || f.interp = Some op_to_real ||
  f.interp = Some op_arith_le || f.interp = Some op_arith_lt || f.interp = Some op_arith_ge ||
  f.interp = Some op_arith_gt

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

(* The Sorted layers pass every classified Real operator to `other`. *)
let lemma_real_application (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (f:func_decl) (xs:V.arguments base (S.signature s) f.domain)
  : Lemma (requires ~(Other? (classify f)))
          (ensures T.application s bc model other f xs == other.V.application f xs) =
  lemma_classified_not_core f;
  lemma_classified_not_registered s f;
  lemma_no_recognizer f s.S.cases;
  lemma_no_accessor f s.S.cases

(* An interpretation that agrees with `other` on every classified Real
   operator inherits the Real laws (the model overrides of the epsilon and
   dependent-Skolem routes only change uninterpreted witness symbols). *)
let real_agreement (#base:sort -> Type0) (s:S.checked_schema)
                   (other newer:V.interpretation base (S.signature s)) : prop =
  forall (f:func_decl) (xs:V.arguments base (S.signature s) f.domain).
    ~(Other? (classify f)) ==> newer.V.application f xs == other.V.application f xs

let lemma_real_laws_transfer (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (model:T.scalar_model base) (other newer:V.interpretation base (S.signature s))
                             (reals:carrier base)
  : Lemma (requires real_laws s bc model other reals /\ real_agreement s other newer)
          (ensures real_laws s bc model newer reals) =
  introduce forall (f:func_decl) (xs:V.arguments base (S.signature s) f.domain).
    real_meaning s bc model.T.integers reals f xs (T.application s bc model newer f xs)
  with (
    if Other? (classify f) then ()
    else (
      lemma_real_application s bc model other f xs;
      lemma_real_application s bc model newer f xs;
      assert (real_meaning s bc model.T.integers reals f xs (T.application s bc model other f xs))))

(* ---------------------------------------------------------------------- *)
(* Values                                                                   *)
(* ---------------------------------------------------------------------- *)

let rec lemma_registered_sort (sigma:V.signature) (f:func_decl)
  : Lemma (requires L.mem f sigma) (ensures V.datatype_sort sigma f.range) (decreases sigma) =
  match sigma with [] -> () | g :: rest -> if f <> g then lemma_registered_sort rest f

let lemma_real_injective (#base:sort -> Type0) (s:S.checked_schema) (reals:carrier base)
                         (x y:V.value base (S.signature s) A.real_s)
  : Lemma (requires real_primitive s)
          (ensures real_value s reals x == real_value s reals y <==> x == y) =
  let _ : unit = reals.real_injective in
  match x, y with
  | V.Constructor f _, _ -> lemma_registered_sort (S.signature s) f
  | _, V.Constructor g _ -> lemma_registered_sort (S.signature s) g
  | V.Scalar _ _, V.Scalar _ _ -> ()

let lemma_evaluate_real_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (scope:list sort) (rho:V.environment base (S.signature s) scope)
                           (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped scope (App f args) /\ ~(Other? (classify f)))
          (ensures T.evaluate_at s bc model other scope rho (App f args) ==
                   T.application s bc model other f
                     (T.evaluate_arguments_at s bc model other scope rho args f.domain)) =
  lemma_classified_not_registered s f

(* ---------------------------------------------------------------------- *)
(* Canonical Real operators at every scope and environment                  *)
(* ---------------------------------------------------------------------- *)

let lemma_real_numeral_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
                          (f:func_decl) (n:int) (d:pos)
  : Lemma (requires real_laws s bc model other reals /\ classify f == Numeral n d)
          (ensures D.scoped scope (App f []) /\ get_sort (App f []) == A.real_s /\
                   real_at s bc model other reals scope rho (App f []) == of_int n /. of_int d) =
  lemma_evaluate_real_at s bc model other scope rho f [];
  let xs : V.arguments base (S.signature s) f.domain = [] in
  assert (real_meaning s bc model.T.integers reals f xs (T.application s bc model other f xs))

let lemma_real_binary_value_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                               (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
                               (f:func_decl) (a b:expr) (o:A.operation)
  : Lemma (requires real_laws s bc model other reals /\ D.scoped scope (App f [a; b]) /\
                    classify f == Calculate o)
          (ensures D.scoped scope a /\ D.scoped scope b /\ get_sort a == A.real_s /\ get_sort b == A.real_s /\
                   get_sort (App f [a; b]) == A.real_s /\
                   real_at s bc model other reals scope rho (App f [a; b]) ==
                   calculate o [real_at s bc model other reals scope rho a; real_at s bc model other reals scope rho b]) =
  match f.domain with
  | [ta; tb] ->
    V.lemma_sort_eq (get_sort a) ta;
    V.lemma_sort_eq (get_sort b) tb;
    lemma_evaluate_real_at s bc model other scope rho f [a; b];
    let va = T.evaluate_at s bc model other scope rho a in
    let vb = T.evaluate_at s bc model other scope rho b in
    let xs = T.evaluate_arguments_at s bc model other scope rho [a; b] f.domain in
    assert_norm (T.evaluate_arguments_at s bc model other scope rho [a; b] [A.real_s; A.real_s] == [va; vb]);
    assert (xs == [va; vb]);
    assert (real_meaning s bc model.T.integers reals f xs (T.application s bc model other f xs));
    assert_norm (real_values s reals [A.real_s; A.real_s] [va; vb] ==
                 [real_value s reals va; real_value s reals vb])
  | _ -> ()

let lemma_calculate_pair (o:A.operation) (x y:real)
  : Lemma ((o == A.Add ==> calculate o [x; y] == x +. y) /\
           (o == A.Sub ==> calculate o [x; y] == x -. y) /\
           (o == A.Mul ==> calculate o [x; y] == x *. y)) = ()

let lemma_real_binary_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
                         (f:func_decl) (a b:expr) (o:A.operation)
  : Lemma (requires real_laws s bc model other reals /\ D.scoped scope (App f [a; b]) /\
                    classify f == Calculate o)
          (ensures D.scoped scope a /\ D.scoped scope b /\ get_sort a == A.real_s /\ get_sort b == A.real_s /\
                   get_sort (App f [a; b]) == A.real_s /\
                   (let x = real_at s bc model other reals scope rho a in
                    let y = real_at s bc model other reals scope rho b in
                    let z = real_at s bc model other reals scope rho (App f [a; b]) in
                    (o == A.Add ==> z == x +. y) /\
                    (o == A.Sub ==> z == x -. y) /\
                    (o == A.Mul ==> z == x *. y))) =
  lemma_real_binary_value_at s bc model other reals scope rho f a b o;
  lemma_calculate_pair o (real_at s bc model other reals scope rho a) (real_at s bc model other reals scope rho b)

let lemma_real_comparison_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
                             (f:func_decl) (a b:expr) (r:A.relation)
  : Lemma (requires real_laws s bc model other reals /\ D.scoped scope (App f [a; b]) /\
                    classify f == Compare r)
          (ensures D.scoped scope a /\ D.scoped scope b /\ get_sort a == A.real_s /\ get_sort b == A.real_s /\
                   (T.truth_at s bc model other scope rho (App f [a; b]) <==>
                    E.numeric_relation r (real_at s bc model other reals scope rho a)
                                         (real_at s bc model other reals scope rho b))) =
  V.lemma_sort_eq (get_sort a) A.real_s;
  V.lemma_sort_eq (get_sort b) A.real_s;
  lemma_evaluate_real_at s bc model other scope rho f [a; b];
  let va = T.evaluate_at s bc model other scope rho a in
  let vb = T.evaluate_at s bc model other scope rho b in
  let xs = T.evaluate_arguments_at s bc model other scope rho [a; b] f.domain in
  assert_norm (T.evaluate_arguments_at s bc model other scope rho [a; b] [A.real_s; A.real_s] == [va; vb]);
  assert (xs == [va; vb]);
  assert (real_meaning s bc model.T.integers reals f xs (T.application s bc model other f xs))

let lemma_real_equality_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
                           (a b:expr)
  : Lemma (requires real_primitive s /\ D.scoped scope a /\ D.scoped scope b /\
                    get_sort a == A.real_s /\ get_sort b == A.real_s)
          (ensures T.truth_at s bc model other scope rho (R.mk_eq_expr a b) <==>
                   real_at s bc model other reals scope rho a == real_at s bc model other reals scope rho b) =
  T.lemma_equality_at s bc model other scope rho a b;
  lemma_real_injective s reals (T.evaluate_at s bc model other scope rho a)
                               (T.evaluate_at s bc model other scope rho b)

(* Division by a nonzero divisor; x/0 has no law (a free model choice). *)
let lemma_real_divide_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
                         (f:func_decl) (a b:expr)
  : Lemma (requires real_laws s bc model other reals /\ D.scoped scope (App f [a; b]) /\ classify f == Divide)
          (ensures D.scoped scope a /\ D.scoped scope b /\ get_sort a == A.real_s /\ get_sort b == A.real_s /\
                   (~(real_at s bc model other reals scope rho b == 0.0R) ==>
                    real_at s bc model other reals scope rho (App f [a; b]) *. real_at s bc model other reals scope rho b ==
                    real_at s bc model other reals scope rho a)) =
  V.lemma_sort_eq (get_sort a) A.real_s;
  V.lemma_sort_eq (get_sort b) A.real_s;
  lemma_evaluate_real_at s bc model other scope rho f [a; b];
  let va = T.evaluate_at s bc model other scope rho a in
  let vb = T.evaluate_at s bc model other scope rho b in
  let xs = T.evaluate_arguments_at s bc model other scope rho [a; b] f.domain in
  assert_norm (T.evaluate_arguments_at s bc model other scope rho [a; b] [A.real_s; A.real_s] == [va; vb]);
  assert (xs == [va; vb]);
  assert (real_meaning s bc model.T.integers reals f xs (T.application s bc model other f xs))

let lemma_to_real_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (f:func_decl) (a:expr)
  : Lemma (requires real_laws s bc model other reals /\ D.scoped scope (App f [a]) /\ classify f == ToReal)
          (ensures D.scoped scope a /\ get_sort a == A.int_s /\
                   real_at s bc model other reals scope rho (App f [a]) ==
                   of_int (AR.integer s bc model other scope rho a)) =
  V.lemma_sort_eq (get_sort a) A.int_s;
  lemma_evaluate_real_at s bc model other scope rho f [a];
  let va = T.evaluate_at s bc model other scope rho a in
  let xs = T.evaluate_arguments_at s bc model other scope rho [a] f.domain in
  assert_norm (T.evaluate_arguments_at s bc model other scope rho [a] [A.int_s] == [va]);
  assert (xs == [va]);
  assert (real_meaning s bc model.T.integers reals f xs (T.application s bc model other f xs))

(* One coherent numeric valuation: on Int terms the mixed valuation IS the
   existing Int valuation of Z3SortedArithmetic (same model, same integer
   carrier), and to_real reads exactly that value into the one Real carrier. *)
let lemma_numeric_int_agreement (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                                (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
                                (e:expr)
  : Lemma (requires get_sort e == A.int_s)
          (ensures numeric_valuation s bc model other reals scope rho e == AR.valuation s bc model other scope rho e) = ()

let lemma_to_real_coherent (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
                           (f:func_decl) (a:expr)
  : Lemma (requires real_laws s bc model other reals /\ D.scoped scope (App f [a]) /\ classify f == ToReal)
          (ensures numeric_valuation s bc model other reals scope rho (App f [a]) ==
                   AR.valuation s bc model other scope rho a /\
                   numeric_valuation s bc model other reals scope rho (App f [a]) ==
                   numeric_valuation s bc model other reals scope rho a) =
  lemma_to_real_at s bc model other reals scope rho f a

let lemma_to_real_numeral_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (reals:carrier base) (scope:list sort) (rho:V.environment base (S.signature s) scope)
                             (f:func_decl) (k:expr) (n:int)
  : Lemma (requires real_laws s bc model other reals /\ D.scoped scope (App f [k]) /\
                    classify f == ToReal /\ AR.int_numeral n k)
          (ensures real_at s bc model other reals scope rho (App f [k]) == of_int n) =
  V.lemma_sort_eq (get_sort k) A.int_s;
  lemma_evaluate_real_at s bc model other scope rho f [k];
  AR.lemma_int_numeral s bc model other scope rho n k;
  let vk = T.evaluate_at s bc model other scope rho k in
  let xs = T.evaluate_arguments_at s bc model other scope rho [k] f.domain in
  assert_norm (T.evaluate_arguments_at s bc model other scope rho [k] [A.int_s] == [vk]);
  assert (xs == [vk]);
  assert (real_meaning s bc model.T.integers reals f xs (T.application s bc model other f xs))
