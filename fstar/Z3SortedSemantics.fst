module Z3SortedSemantics

open Z3AstTheory
open Z3ValueTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module R = Z3ResolutionProofTheory
module B = Z3BoundedBoolEquiv
module D = Z3Definitions
module L = FStar.List.Tot
module I = Z3SortedInteger

noeq
type scalar_equality (base:sort -> Type0) = {
  equal_scalar: s:sort -> base s -> base s -> bool;
  scalar_equality_correct: u:unit{
    forall (s:sort) (x y:base s). equal_scalar s x y <==> x == y};
}

noeq
type scalar_model (base:sort -> Type0) = {
  reflection: scalar_equality base;
  integers: I.carrier base;
}

let rec equal_tree (#base:sort -> Type0) (equality:scalar_equality base)
                   (x y:V.tree base)
  : Tot bool (decreases x) =
  match x, y with
  | V.Scalar s a, V.Scalar t b ->
    if s = t then equality.equal_scalar s a b else false
  | V.Constructor f xs, V.Constructor g ys ->
    f = g && equal_fields equality xs ys
  | _, _ -> false

and equal_fields (#base:sort -> Type0) (equality:scalar_equality base)
                 (xs ys:list (V.tree base))
  : Tot bool (decreases xs) =
  match xs, ys with
  | [], [] -> true
  | x :: rest, y :: tail -> equal_tree equality x y && equal_fields equality rest tail
  | _, _ -> false

let rec lemma_equal_tree (#base:sort -> Type0) (equality:scalar_equality base)
                         (x y:V.tree base)
  : Lemma (equal_tree equality x y <==> x == y) (decreases x) =
  match x, y with
  | V.Scalar _ _, V.Scalar _ _ -> ()
  | V.Constructor _ xs, V.Constructor _ ys -> lemma_equal_fields equality xs ys
  | _, _ -> ()

and lemma_equal_fields (#base:sort -> Type0) (equality:scalar_equality base)
                       (xs ys:list (V.tree base))
  : Lemma (equal_fields equality xs ys <==> xs == ys) (decreases xs) =
  match xs, ys with
  | x :: rest, y :: tail ->
    lemma_equal_tree equality x y;
    lemma_equal_fields equality rest tail
  | _, _ -> ()

let boolean (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base) (b:bool)
  : V.value base (S.signature s) bool_sort =
  V.Scalar bool_sort (bc.encode_bool b)

let rec lemma_registered_sort (sigma:V.signature) (f:func_decl)
  : Lemma (requires L.mem f sigma)
          (ensures V.datatype_sort sigma f.range)
          (decreases sigma) =
  match sigma with
  | [] -> ()
  | g :: rest -> if f <> g then lemma_registered_sort rest f

let truth_value (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (v:V.value base (S.signature s) bool_sort)
  : bool =
  match v with
  | V.Scalar _ x -> bc.decode_bool x
  | V.Constructor f _ ->
    lemma_registered_sort (S.signature s) f;
    FStar.Pervasives.false_elim ()

let lemma_boolean (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (v:V.value base (S.signature s) bool_sort)
  : Lemma (boolean s bc (truth_value s bc v) == v) =
  match v with
  | V.Scalar _ _ -> ()
  | V.Constructor f _ -> lemma_registered_sort (S.signature s) f

let rec boolean_sorts (ss:list sort) : Tot bool (decreases ss) =
  match ss with [] -> true | s :: rest -> s = bool_sort && boolean_sorts rest

let rec boolean_values (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (ss:list sort{boolean_sorts ss})
                       (xs:V.arguments base (S.signature s) ss)
  : Tot (list bool) (decreases ss) =
  match ss, xs with
  | [], [] -> []
  | _ :: rest, x :: tail -> truth_value s bc x :: boolean_values s bc rest tail
  | _, _ -> FStar.Pervasives.false_elim ()

let rec combine (op:B.nary_op) (xs:list bool) : Tot bool (decreases xs) =
  match xs with [] -> B.neutral op | x :: rest -> B.combine op x (combine op rest)

let ite_decl (s:sort) : func_decl = {
  decl_name = "if"; domain = [bool_sort; s; s]; range = s;
  interp = Some op_ite; int_params = [];
}

type operation =
  | Constant : bool -> operation
  | Negation
  | Implication
  | Nary : B.nary_op -> operation
  | Equality : sort -> operation
  | Choice : sort -> operation
  | Other

let operation_typed (f:func_decl) (op:operation) : bool =
  match op with
  | Constant b -> f = (match (if b then R.true_expr else R.false_expr) with App g _ -> g | _ -> f)
  | Negation -> f.domain = [bool_sort] && f.range = bool_sort
  | Implication -> f.domain = [bool_sort; bool_sort] && f.range = bool_sort
  | Nary _ -> boolean_sorts f.domain && f.range = bool_sort
  | Equality s -> f = R.eq_decl s
  | Choice s -> f = ite_decl s
  | Other -> true

let classify (f:func_decl) : op:operation{operation_typed f op} =
  if f = { decl_name = "true"; domain = []; range = bool_sort;
           interp = Some op_true; int_params = [] } then Constant true
  else if f = { decl_name = "false"; domain = []; range = bool_sort;
                interp = Some op_false; int_params = [] } then Constant false
  else if f = { decl_name = "not"; domain = [bool_sort]; range = bool_sort;
                interp = Some op_not; int_params = [] } then Negation
  else if (f.decl_name = "=>" || f.decl_name = "implies") &&
          f.domain = [bool_sort; bool_sort] && f.range = bool_sort &&
          f.interp = Some op_implies && f.int_params = [] then Implication
  else if f.range = bool_sort && boolean_sorts f.domain && f.int_params = [] &&
          (f.decl_name = "and" && f.interp = Some op_and ||
           f.decl_name = "or" && f.interp = Some op_or ||
           f.decl_name = "xor" && f.interp = Some op_xor) then
    Nary (if f.interp = Some op_and then B.And
          else if f.interp = Some op_or then B.Or else B.Xor)
  else match f.domain with
  | [s; _] -> if f = R.eq_decl s then Equality s else Other
  | [_; s; _] -> if f = ite_decl s then Choice s else Other
  | _ -> Other

let application (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                (f:func_decl) (xs:V.arguments base (S.signature s) f.domain)
  : V.value base (S.signature s) f.range =
  match classify f with
  | Constant b -> boolean s bc b
  | Negation ->
    (match xs with
     | [x] -> boolean s bc (not (truth_value s bc x))
     | _ -> FStar.Pervasives.false_elim ())
  | Implication ->
    (match xs with
     | [x; y] -> boolean s bc (not (truth_value s bc x) || truth_value s bc y)
     | _ -> FStar.Pervasives.false_elim ())
  | Nary op -> boolean s bc (combine op (boolean_values s bc f.domain xs))
  | Equality _ ->
    (match xs with
     | [x; y] -> boolean s bc (equal_tree equality.reflection x y)
     | _ -> FStar.Pervasives.false_elim ())
  | Choice _ ->
    (match xs with
     | [c; x; y] -> if truth_value s bc c then x else y
     | _ -> FStar.Pervasives.false_elim ())
  | Other -> I.application s bc equality.integers other f xs

let interpretation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (equality:scalar_model base) (other:V.interpretation base (S.signature s))
  : V.interpretation base (S.signature s) = {
  application = application s bc equality other;
  quantification = other.quantification;
}

let empty_environment (#base:sort -> Type0) (sigma:V.signature)
  : V.environment base sigma [] = fun _ -> FStar.Pervasives.false_elim ()

let evaluate_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
             (equality:scalar_model base) (other:V.interpretation base (S.signature s))
             (scope:list sort) (rho:V.environment base (S.signature s) scope)
             (e:expr{D.scoped scope e})
  : V.value base (S.signature s) (get_sort e) =
  V.evaluate (S.signature s) (interpretation s bc equality other) scope rho e

let evaluate (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
             (equality:scalar_model base) (other:V.interpretation base (S.signature s))
             (e:expr{D.scoped [] e})
  : V.value base (S.signature s) (get_sort e) =
  evaluate_at s bc equality other [] (empty_environment (S.signature s)) e

let truth_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
          (equality:scalar_model base) (other:V.interpretation base (S.signature s))
          (scope:list sort) (rho:V.environment base (S.signature s) scope)
          (e:expr) : bool =
  D.scoped scope e && get_sort e = bool_sort &&
  truth_value s bc (evaluate_at s bc equality other scope rho e)

unfold let truth (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
          (equality:scalar_model base) (other:V.interpretation base (S.signature s))
  : expr -> Tot bool =
  truth_at s bc equality other [] (empty_environment (S.signature s))

let evaluate_arguments_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (es:list expr{D.scoped_args scope es})
                       (ss:list sort{sorts_match es ss})
  : V.arguments base (S.signature s) ss =
  V.evaluate_args (S.signature s) (interpretation s bc equality other) scope rho es ss

let evaluate_arguments (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                       (es:list expr{D.scoped_args [] es})
                       (ss:list sort{sorts_match es ss})
  : V.arguments base (S.signature s) ss =
  evaluate_arguments_at s bc equality other [] (empty_environment (S.signature s)) es ss

let lemma_registered_constructor (s:S.checked_schema) (f:func_decl)
  : Lemma (requires L.mem f (S.signature s))
          (ensures f.interp == Some Z3DatatypeLemma.op_constructor) =
  S.lemma_case_of s.cases f;
  let c = Some?.v (S.case_of s.cases f) in
  S.lemma_case_member (S.signature s) s.sorts s.cases c

let lemma_core_not_constructor (s:S.checked_schema) (f:func_decl)
  : Lemma (requires classify f <> Other)
          (ensures not (L.mem f (S.signature s))) =
  if L.mem f (S.signature s) then lemma_registered_constructor s f

let lemma_evaluate_core_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                        (scope:list sort) (rho:V.environment base (S.signature s) scope)
                        (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped scope (App f args) /\ classify f <> Other)
          (ensures evaluate_at s bc equality other scope rho (App f args) ==
                   application s bc equality other f
                     (evaluate_arguments_at s bc equality other scope rho args f.domain)) =
  lemma_core_not_constructor s f

let lemma_evaluate_core (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                        (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped [] (App f args) /\ classify f <> Other)
          (ensures evaluate s bc equality other (App f args) ==
                   application s bc equality other f
                     (evaluate_arguments s bc equality other args f.domain)) =
  lemma_evaluate_core_at s bc equality other [] (empty_environment (S.signature s)) f args

let lemma_equality_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                   (scope:list sort) (rho:V.environment base (S.signature s) scope)
                   (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ get_sort a == get_sort b)
          (ensures truth_at s bc equality other scope rho (R.mk_eq_expr a b) <==>
                   evaluate_at s bc equality other scope rho a ==
                   evaluate_at s bc equality other scope rho b) =
  V.lemma_sort_eq (get_sort a) (get_sort b);
  lemma_evaluate_core_at s bc equality other scope rho (R.eq_decl (get_sort a)) [a; b];
  lemma_equal_tree equality.reflection (evaluate_at s bc equality other scope rho a)
                            (evaluate_at s bc equality other scope rho b)

let lemma_equality (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                   (a b:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\ get_sort a == get_sort b)
          (ensures truth s bc equality other (R.mk_eq_expr a b) <==>
                   evaluate s bc equality other a == evaluate s bc equality other b) =
  lemma_equality_at s bc equality other [] (empty_environment (S.signature s)) a b

let lemma_boolean_equality_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                           (scope:list sort) (rho:V.environment base (S.signature s) scope)
                           (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort)
          (ensures truth_at s bc equality other scope rho (R.mk_eq_expr a b) ==
                   (truth_at s bc equality other scope rho a = truth_at s bc equality other scope rho b)) =
  lemma_equality_at s bc equality other scope rho a b;
  lemma_boolean s bc (evaluate_at s bc equality other scope rho a);
  lemma_boolean s bc (evaluate_at s bc equality other scope rho b)

let lemma_boolean_equality (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                           (a b:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort)
          (ensures truth s bc equality other (R.mk_eq_expr a b) ==
                   (truth s bc equality other a = truth s bc equality other b)) =
  lemma_boolean_equality_at s bc equality other [] (empty_environment (S.signature s)) a b

let rec cut_with_boundaries (boundaries:list expr) (fuel:nat) (e:expr) : Tot B.skeleton (decreases e) =
  if fuel = 0 || L.mem e boundaries then B.Atom e
  else match e with
  | App f args ->
    (match classify f, args with
     | Constant b, _ -> B.Bool b
     | Negation, [a] -> B.Not (cut_with_boundaries boundaries (fuel - 1) a)
     | Implication, [a; b] ->
       B.Implies (cut_with_boundaries boundaries (fuel - 1) a)
                 (cut_with_boundaries boundaries (fuel - 1) b)
     | Nary op, _ -> B.Nary op (cut_args_with_boundaries boundaries (fuel - 1) args)
     | Equality t, [a; b] ->
       if a = b then B.Bool true
       else if t = bool_sort then
         B.Eq (cut_with_boundaries boundaries (fuel - 1) a)
              (cut_with_boundaries boundaries (fuel - 1) b)
       else B.Atom e
     | Choice t, [c; a; b] ->
       if t = bool_sort then
         B.boolean_ite (cut_with_boundaries boundaries (fuel - 1) c)
                       (cut_with_boundaries boundaries (fuel - 1) a)
                       (cut_with_boundaries boundaries (fuel - 1) b)
       else B.Atom e
     | _, _ -> B.Atom e)
  | _ -> B.Atom e

and cut_args_with_boundaries (boundaries:list expr) (fuel:nat) (args:list expr)
  : Tot (list B.skeleton) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> cut_with_boundaries boundaries fuel a :: cut_args_with_boundaries boundaries fuel rest

let cut (fuel:nat) (e:expr) : B.skeleton = cut_with_boundaries [] fuel e

let cut_args (fuel:nat) (args:list expr) : list B.skeleton =
  cut_args_with_boundaries [] fuel args

let rec lemma_boolean_arguments_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                                (scope:list sort) (rho:V.environment base (S.signature s) scope)
                                (args:list expr) (ss:list sort) (op:B.nary_op)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss /\ boolean_sorts ss)
          (ensures combine op (boolean_values s bc ss
                     (evaluate_arguments_at s bc equality other scope rho args ss)) ==
                   B.eval_args (truth_at s bc equality other scope rho) op (L.map B.Atom args))
          (decreases args) =
  match args, ss with
  | a :: rest, t :: tail ->
    V.lemma_sort_eq (get_sort a) t;
    lemma_boolean_arguments_at s bc equality other scope rho rest tail op
  | _, _ -> ()

let lemma_boolean_arguments (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                            (args:list expr) (ss:list sort) (op:B.nary_op)
  : Lemma (requires D.scoped_args [] args /\ sorts_match args ss /\ boolean_sorts ss)
          (ensures combine op (boolean_values s bc ss (evaluate_arguments s bc equality other args ss)) ==
                   B.eval_args (truth s bc equality other) op (L.map B.Atom args)) =
  lemma_boolean_arguments_at s bc equality other [] (empty_environment (S.signature s)) args ss op

let rec lemma_cut_with_boundaries_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                  (scope:list sort) (rho:V.environment base (S.signature s) scope)
                  (boundaries:list expr) (fuel:nat) (e:expr)
  : Lemma (requires D.scoped scope e /\ get_sort e == bool_sort)
          (ensures B.eval (truth_at s bc equality other scope rho) (cut_with_boundaries boundaries fuel e) ==
                   truth_at s bc equality other scope rho e)
          (decreases e) =
  if fuel = 0 || L.mem e boundaries then ()
  else match e with
  | App f args ->
    (if classify f <> Other then lemma_evaluate_core_at s bc equality other scope rho f args);
    (match classify f, args with
     | Constant _, _ -> ()
     | Negation, [a] -> lemma_cut_with_boundaries_at s bc equality other scope rho boundaries (fuel - 1) a
     | Implication, [a; b] ->
       lemma_cut_with_boundaries_at s bc equality other scope rho boundaries (fuel - 1) a;
       lemma_cut_with_boundaries_at s bc equality other scope rho boundaries (fuel - 1) b
     | Nary op, _ ->
       lemma_boolean_arguments_at s bc equality other scope rho args f.domain op;
       lemma_cut_args_with_boundaries_at s bc equality other scope rho boundaries (fuel - 1) args f.domain op
     | Equality t, [a; b] ->
       V.lemma_sort_eq (get_sort a) t;
       V.lemma_sort_eq (get_sort b) t;
       if a = b then lemma_equality_at s bc equality other scope rho a b
       else if t = bool_sort then (
         lemma_cut_with_boundaries_at s bc equality other scope rho boundaries (fuel - 1) a;
         lemma_cut_with_boundaries_at s bc equality other scope rho boundaries (fuel - 1) b;
         lemma_boolean_equality_at s bc equality other scope rho a b)
     | Choice t, [c; a; b] ->
       if t = bool_sort then (
         V.lemma_sort_eq (get_sort c) bool_sort;
         V.lemma_sort_eq (get_sort a) t;
         V.lemma_sort_eq (get_sort b) t;
         lemma_cut_with_boundaries_at s bc equality other scope rho boundaries (fuel - 1) c;
         lemma_cut_with_boundaries_at s bc equality other scope rho boundaries (fuel - 1) a;
         lemma_cut_with_boundaries_at s bc equality other scope rho boundaries (fuel - 1) b;
         B.lemma_boolean_ite_eval (truth_at s bc equality other scope rho)
           (cut_with_boundaries boundaries (fuel - 1) c)
           (cut_with_boundaries boundaries (fuel - 1) a)
           (cut_with_boundaries boundaries (fuel - 1) b))
     | _, _ -> ())
  | _ -> ()

and lemma_cut_args_with_boundaries_at (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                   (scope:list sort) (rho:V.environment base (S.signature s) scope)
                   (boundaries:list expr) (fuel:nat) (args:list expr) (ss:list sort) (op:B.nary_op)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss /\ boolean_sorts ss)
          (ensures B.eval_args (truth_at s bc equality other scope rho) op
                     (cut_args_with_boundaries boundaries fuel args) ==
                   B.eval_args (truth_at s bc equality other scope rho) op (L.map B.Atom args))
          (decreases args) =
  match args, ss with
  | a :: rest, t :: tail ->
    V.lemma_sort_eq (get_sort a) t;
    lemma_cut_with_boundaries_at s bc equality other scope rho boundaries fuel a;
    lemma_cut_args_with_boundaries_at s bc equality other scope rho boundaries fuel rest tail op
  | _, _ -> ()

let lemma_cut_with_boundaries (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (equality:scalar_model base) (other:V.interpretation base (S.signature s))
                  (boundaries:list expr) (fuel:nat) (e:expr)
  : Lemma (requires D.scoped [] e /\ get_sort e == bool_sort)
          (ensures B.eval (truth s bc equality other) (cut_with_boundaries boundaries fuel e) ==
                   truth s bc equality other e) =
  lemma_cut_with_boundaries_at s bc equality other [] (empty_environment (S.signature s)) boundaries fuel e

let lemma_cut (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
              (equality:scalar_model base) (other:V.interpretation base (S.signature s))
              (fuel:nat) (e:expr)
  : Lemma (requires D.scoped [] e /\ get_sort e == bool_sort)
          (ensures B.eval (truth s bc equality other) (cut fuel e) == truth s bc equality other e) =
  lemma_cut_with_boundaries s bc equality other [] fuel e

let lemma_nary (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
               (eq:scalar_model base) (other:V.interpretation base (S.signature s))
               (f:func_decl) (args:list expr) (op:B.nary_op)
  : Lemma (requires D.scoped [] (App f args) /\ classify f == Nary op)
          (ensures truth s bc eq other (App f args) ==
                   B.eval_args (truth s bc eq other) op (L.map B.Atom args)) =
  lemma_evaluate_core s bc eq other f args;
  lemma_boolean_arguments s bc eq other args f.domain op

let lemma_negation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:scalar_model base) (other:V.interpretation base (S.signature s))
                   (f:func_decl) (arg:expr)
  : Lemma (requires D.scoped [] (App f [arg]) /\ classify f == Negation)
          (ensures truth s bc eq other (App f [arg]) == not (truth s bc eq other arg)) =
  lemma_evaluate_core s bc eq other f [arg];
  V.lemma_sort_eq (get_sort arg) bool_sort

let rec truths (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
               (eq:scalar_model base) (other:V.interpretation base (S.signature s))
               (es:list expr) : Tot bool (decreases es) =
  match es with [] -> true | e :: rest -> truth s bc eq other e && truths s bc eq other rest

let rec lemma_truths (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:scalar_model base) (other:V.interpretation base (S.signature s))
                     (es:list expr)
  : Lemma (B.eval_args (truth s bc eq other) B.And (L.map B.Atom es) ==
           truths s bc eq other es) (decreases es) =
  match es with [] -> () | _ :: rest -> lemma_truths s bc eq other rest

let same_value (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
               (eq:scalar_model base) (other:V.interpretation base (S.signature s))
               (a b:expr) : bool =
  D.scoped [] a && D.scoped [] b &&
  equal_tree eq.reflection (evaluate s bc eq other a) (evaluate s bc eq other b)

let lemma_same_value (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:scalar_model base) (other:V.interpretation base (S.signature s))
                     (a b:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b)
          (ensures same_value s bc eq other a b <==>
                   evaluate s bc eq other a == evaluate s bc eq other b) =
  lemma_equal_tree eq.reflection (evaluate s bc eq other a) (evaluate s bc eq other b)
