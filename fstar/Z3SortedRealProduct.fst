module Z3SortedRealProduct

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open FStar.Real
open FStar.List.Tot
module A = Z3LinearArithmeticAst
module B = Z3BoundedBoolEquiv
module D = Z3Definitions
module L = FStar.List.Tot
module LIN = Z3SortedRealLinear
module R = Z3ResolutionProofTheory
module RL = Z3SortedReal
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue

let zero : expr = App (RL.real_numeral_decl 0 1) []
let positive (e:expr) : expr = App RL.real_gt_decl [e; zero]
let bound (lower:bool) (e:expr) : expr =
  App (if lower then RL.real_ge_decl else RL.real_le_decl) [e; zero]

let lemma_positive_shape (e:expr)
  : Lemma (requires D.scoped [] e /\ get_sort e == A.real_s)
          (ensures D.scoped [] (positive e) /\
                   A.comparison (positive e) == Some (A.Gt, e, zero) /\
                   R.formula_clause (positive e) == [positive e]) =
  assert_norm (get_sort zero == A.real_s);
  assert (A.application RL.real_gt_decl [e; zero] bool_sort ">" op_arith_gt)

let positive_product (s:S.checked_schema) (facts:list expr) (p:expr) : bool =
  match p with
  | App f [x; y] ->
    RL.classify f = RL.Calculate A.Mul &&
    D.scoped [] p &&
    LIN.refutes s facts (positive x) && LIN.refutes s facts (positive y) &&
    LIN.refutes s (positive p :: facts) R.false_expr
  | _ -> false

let nonpositive_product (s:S.checked_schema) (facts:list expr) (p:expr) : bool =
  match p with
  | App f [x; y] ->
    RL.classify f = RL.Calculate A.Mul && D.scoped [] p &&
    ((LIN.refutes s facts (bound true x) && LIN.refutes s facts (bound false y)) ||
     (LIN.refutes s facts (bound false x) && LIN.refutes s facts (bound true y))) &&
    LIN.refutes s (bound false p :: facts) R.false_expr
  | _ -> false

let product (e:expr) : bool =
  match e with App f [_; _] -> RL.classify f = RL.Calculate A.Mul | _ -> false

let product_literal (e:expr) : option expr =
  match A.literal 16 true e with
  | Some (_, _, x, y) -> if product x then Some x else if product y then Some y else None
  | None -> None

let rec candidate (s:S.checked_schema) (facts rest:list expr)
  : Tot (p:option expr{Some? p ==> positive_product s facts (Some?.v p)}) (decreases rest) =
  match rest with
  | [] -> None
  | e :: tail ->
    (match product_literal e with
     | Some p -> if positive_product s facts p then Some p else candidate s facts tail
     | None -> candidate s facts tail)

let rec products (fuel:nat) (e:expr) : Tot (list expr) (decreases fuel) =
  if fuel = 0 then []
  else match e with
  | App f args ->
    (if RL.classify f = RL.Calculate A.Mul && L.length args = 2 then [e] else []) @
    L.concatMap (products (fuel - 1)) args
  | _ -> []

let rec nonpositive_candidate (s:S.checked_schema) (facts:list expr) (fuel:nat) (rest:list expr)
  : Tot (p:option expr{Some? p ==> nonpositive_product s facts (Some?.v p)}) (decreases fuel) =
  if fuel = 0 then None
  else match rest with
  | [] -> None
  | p :: tail ->
    if nonpositive_product s facts p then Some p
    else nonpositive_candidate s facts (fuel - 1) tail

let nested_candidate (s:S.checked_schema) (facts:list expr) : option expr =
  nonpositive_candidate s facts 32 (L.concatMap (products 16) facts)

let substituted_product (f:func_decl) (x y k:expr) (left:bool) : expr =
  App f [k; if left then y else x]

let constant_product (s:S.checked_schema) (facts:list expr) (p k:expr) (left:bool) : bool =
  match p with
  | App f [x; y] ->
    RL.classify f = RL.Calculate A.Mul && D.scoped [] p &&
    LIN.implied_equality s facts (if left then x else y) k &&
    LIN.refutes s (R.mk_eq_expr p (substituted_product f x y k left) :: facts) R.false_expr
  | _ -> false

type constant_witness (s:S.checked_schema) (facts:list expr) =
  w:(expr & expr & bool){let p, k, left = w in constant_product s facts p k left}

let rec constant_factor_candidate (s:S.checked_schema) (facts:list expr) (p:expr) (ns:list int)
  : Tot (option (constant_witness s facts)) (decreases ns) =
  match ns with
  | [] -> None
  | n :: rest ->
    let k = App (RL.real_numeral_decl n 1) [] in
    if constant_product s facts p k true then Some (p, k, true)
    else if constant_product s facts p k false then Some (p, k, false)
    else constant_factor_candidate s facts p rest

let rec constant_candidate (s:S.checked_schema) (facts:list expr) (fuel:nat) (rest:list expr)
  : Tot (option (constant_witness s facts)) (decreases fuel) =
  if fuel = 0 then None
  else match rest with
  | [] -> None
  | p :: tail ->
    (match constant_factor_candidate s facts p [0; 1; 2; -1] with
     | Some w -> Some w
     | None -> constant_candidate s facts (fuel - 1) tail)

let constant_product_witness (s:S.checked_schema) (facts:list expr) : option (constant_witness s facts) =
  constant_candidate s facts 32 (L.concatMap (products 16) facts)

let check (s:S.checked_schema) (facts:list expr) : bool =
  if not (RL.real_primitive s) || L.length facts > 30 then false
  else if None? (arguments_budget 4096 facts) then false
  else Some? (candidate s facts facts) || Some? (nested_candidate s facts) ||
       Some? (constant_product_witness s facts)

let lemma_positive_meaning (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (reals:RL.carrier base) (e:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped [] e /\ get_sort e == A.real_s)
          (ensures T.truth s bc model other (positive e) <==>
                   RL.real_at s bc model other reals [] (T.empty_environment (S.signature s)) e >. 0.0R) =
  let rho = T.empty_environment (S.signature s) in
  lemma_positive_shape e;
  LIN.lemma_comparison s bc model other reals [] rho (positive e) e zero A.Gt;
  RL.lemma_real_numeral_at s bc model other reals [] rho (RL.real_numeral_decl 0 1) 0 1

let lemma_positive (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (reals:RL.carrier base) (facts:list expr) (e:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    D.scoped [] e /\ get_sort e == A.real_s /\ LIN.refutes s facts (positive e))
          (ensures RL.real_at s bc model other reals [] (T.empty_environment (S.signature s)) e >. 0.0R) =
  let c = positive e in
  lemma_positive_shape e;
  if not (T.truth s bc model other c) then (
    assert (R.formula_clause c == [c]);
    LIN.lemma_refutes s bc model other reals facts c);
  lemma_positive_meaning s bc model other reals e

let lemma_bound_shape (lower:bool) (e:expr)
  : Lemma (requires D.scoped [] e /\ get_sort e == A.real_s)
          (ensures D.scoped [] (bound lower e) /\
                   A.comparison (bound lower e) == Some ((if lower then A.Ge else A.Le), e, zero) /\
                   R.formula_clause (bound lower e) == [bound lower e]) =
  assert_norm (get_sort zero == A.real_s);
  if lower then assert (A.application RL.real_ge_decl [e; zero] bool_sort ">=" op_arith_ge)
  else assert (A.application RL.real_le_decl [e; zero] bool_sort "<=" op_arith_le)

let lemma_bound_meaning (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (reals:RL.carrier base) (lower:bool) (e:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped [] e /\ get_sort e == A.real_s)
          (ensures T.truth s bc model other (bound lower e) <==>
                   (if lower then RL.real_at s bc model other reals [] (T.empty_environment (S.signature s)) e >=. 0.0R
                    else RL.real_at s bc model other reals [] (T.empty_environment (S.signature s)) e <=. 0.0R)) =
  let rho = T.empty_environment (S.signature s) in
  lemma_bound_shape lower e;
  LIN.lemma_comparison s bc model other reals [] rho (bound lower e) e zero (if lower then A.Ge else A.Le);
  RL.lemma_real_numeral_at s bc model other reals [] rho (RL.real_numeral_decl 0 1) 0 1

let lemma_bound (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (reals:RL.carrier base) (facts:list expr) (lower:bool) (e:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    D.scoped [] e /\ get_sort e == A.real_s /\ LIN.refutes s facts (bound lower e))
          (ensures (if lower then RL.real_at s bc model other reals [] (T.empty_environment (S.signature s)) e >=. 0.0R
                    else RL.real_at s bc model other reals [] (T.empty_environment (S.signature s)) e <=. 0.0R)) =
  lemma_bound_shape lower e;
  if not (T.truth s bc model other (bound lower e)) then
    LIN.lemma_refutes s bc model other reals facts (bound lower e);
  lemma_bound_meaning s bc model other reals lower e

#push-options "--using_facts_from 'Prims FStar.Real' --fuel 0 --ifuel 0"
let lemma_multiply_positive (x y:real)
  : Lemma (requires x >. 0.0R /\ y >. 0.0R) (ensures x *. y >. 0.0R) = ()

let lemma_multiply_nonpositive (x y:real)
  : Lemma (requires (x >=. 0.0R /\ y <=. 0.0R) \/ (x <=. 0.0R /\ y >=. 0.0R))
          (ensures x *. y <=. 0.0R) = ()

let lemma_substituted_values (x y k original replacement:real) (left:bool)
  : Lemma (requires original == x *. y /\ replacement == k *. (if left then y else x) /\
                    (if left then x else y) == k)
          (ensures original == replacement) = ()
#pop-options

let lemma_positive_product (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (reals:RL.carrier base) (facts:list expr) (p:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    positive_product s facts p)
          (ensures False) =
  match p with
  | App f [x; y] ->
    let rho = T.empty_environment (S.signature s) in
    RL.lemma_real_binary_at s bc model other reals [] rho f x y A.Mul;
    lemma_positive s bc model other reals facts x;
    lemma_positive s bc model other reals facts y;
    lemma_multiply_positive (RL.real_at s bc model other reals [] rho x)
                            (RL.real_at s bc model other reals [] rho y);
    let c = positive p in
    lemma_positive_meaning s bc model other reals p;
    assert (T.truth s bc model other c);
    assert_norm (R.formula_clause R.false_expr == []);
    assert_norm (not (B.geval_args (T.truth s bc model other) B.Or []));
    LIN.lemma_refutes s bc model other reals (c :: facts) R.false_expr
  | _ -> ()

let lemma_nonpositive_product (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (reals:RL.carrier base) (facts:list expr) (p:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    nonpositive_product s facts p)
          (ensures False) =
  match p with
  | App f [x; y] ->
    let rho = T.empty_environment (S.signature s) in
    RL.lemma_real_binary_at s bc model other reals [] rho f x y A.Mul;
    if LIN.refutes s facts (bound true x) && LIN.refutes s facts (bound false y) then (
      lemma_bound s bc model other reals facts true x;
      lemma_bound s bc model other reals facts false y)
    else (
      lemma_bound s bc model other reals facts false x;
      lemma_bound s bc model other reals facts true y);
    lemma_multiply_nonpositive (RL.real_at s bc model other reals [] rho x)
                               (RL.real_at s bc model other reals [] rho y);
    let c = bound false p in
    lemma_bound_meaning s bc model other reals false p;
    assert (T.truth s bc model other c);
    assert_norm (R.formula_clause R.false_expr == []);
    assert_norm (not (B.geval_args (T.truth s bc model other) B.Or []));
    LIN.lemma_refutes s bc model other reals (c :: facts) R.false_expr
  | _ -> ()

let lemma_substituted_product_shape (f:func_decl) (x y k:expr) (left:bool)
  : Lemma (requires D.scoped [] (App f [x; y]) /\ D.scoped [] k /\
                    get_sort x == A.real_s /\ get_sort y == A.real_s /\ get_sort k == A.real_s)
          (ensures D.scoped [] (substituted_product f x y k left)) =
  assert (sorts_match [x; y] f.domain);
  LIN.lemma_real_argument_sorts [x; y] f.domain;
  assert (f.domain == [A.real_s; A.real_s]);
  assert (D.scoped_args [] [x; y]);
  assert (D.scoped_args [] [y]);
  assert_norm (sort_eq A.real_s A.real_s);
  let other = if left then y else x in
  assert (sorts_match [k; other] f.domain);
  assert (D.scoped_args [] [k; other])

let lemma_constant_product_shape (s:S.checked_schema) (facts:list expr) (p k:expr) (left:bool)
  : Lemma (requires constant_product s facts p k left)
          (ensures (match p with
                   | App f [x; y] ->
                     RL.classify f == RL.Calculate A.Mul /\ D.scoped [] p /\
                     LIN.implied_equality s facts (if left then x else y) k /\
                     LIN.refutes s (R.mk_eq_expr p (substituted_product f x y k left) :: facts) R.false_expr
                   | _ -> False)) = ()

let lemma_fixed_factor (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (reals:RL.carrier base) (facts:list expr) (factor k:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    LIN.implied_equality s facts factor k)
          (ensures RL.real_primitive s /\ D.scoped [] k /\ get_sort k == A.real_s /\
                   RL.real_at s bc model other reals [] (T.empty_environment (S.signature s)) factor ==
                   RL.real_at s bc model other reals [] (T.empty_environment (S.signature s)) k) =
  LIN.lemma_implied_equality s bc model other reals facts factor k;
  RL.lemma_real_equality_at s bc model other reals [] (T.empty_environment (S.signature s)) factor k

let lemma_product_equation (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (reals:RL.carrier base) (p value:expr)
  : Lemma (requires RL.real_primitive s /\ D.scoped [] p /\ D.scoped [] value /\
                    get_sort p == A.real_s /\ get_sort value == A.real_s /\
                    RL.real_at s bc model other reals [] (T.empty_environment (S.signature s)) p ==
                    RL.real_at s bc model other reals [] (T.empty_environment (S.signature s)) value)
          (ensures T.truth s bc model other (R.mk_eq_expr p value)) =
  RL.lemma_real_equality_at s bc model other reals [] (T.empty_environment (S.signature s)) p value

let lemma_refutes_added (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (reals:RL.carrier base) (facts:list expr) (equation:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    T.truth s bc model other equation /\
                    LIN.refutes s (equation :: facts) R.false_expr)
          (ensures False) =
  assert_norm (R.formula_clause R.false_expr == []);
  LIN.lemma_refutes s bc model other reals (equation :: facts) R.false_expr

#push-options "--using_facts_from 'Prims FStar.Real Z3AstTheory' --fuel 0 --ifuel 0"
let lemma_constant_product (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (reals:RL.carrier base) (facts:list expr) (p k:expr) (left:bool)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    constant_product s facts p k left)
          (ensures False) =
  lemma_constant_product_shape s facts p k left;
  match p with
  | App f [x; y] ->
    let p = App f [x; y] in
    let rho = T.empty_environment (S.signature s) in
    RL.lemma_real_binary_at s bc model other reals [] rho f x y A.Mul;
    let factor = if left then x else y in
    let other_factor = if left then y else x in
    lemma_fixed_factor s bc model other reals facts factor k;
    lemma_substituted_product_shape f x y k left;
    let value = substituted_product f x y k left in
    assert_norm (substituted_product f x y k left == App f [k; if left then y else x]);
    assert (value == App f [k; other_factor]);
    RL.lemma_real_binary_at s bc model other reals [] rho f k other_factor A.Mul;
    if left then (
      assert (other_factor == y);
      lemma_substituted_values (RL.real_at s bc model other reals [] rho x)
        (RL.real_at s bc model other reals [] rho y) (RL.real_at s bc model other reals [] rho k)
        (RL.real_at s bc model other reals [] rho p)
        (RL.real_at s bc model other reals [] rho (App f [k; other_factor])) true)
    else (
      assert (other_factor == x);
      lemma_substituted_values (RL.real_at s bc model other reals [] rho x)
        (RL.real_at s bc model other reals [] rho y) (RL.real_at s bc model other reals [] rho k)
        (RL.real_at s bc model other reals [] rho p)
        (RL.real_at s bc model other reals [] rho (App f [k; other_factor])) false);
    lemma_product_equation s bc model other reals p value;
    let equation = R.mk_eq_expr p value in
    assert (T.truth s bc model other equation);
    lemma_refutes_added s bc model other reals facts equation
  | _ -> ()
#pop-options

let lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (reals:RL.carrier base) (facts:list expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\ check s facts)
          (ensures False) =
  if Some? (candidate s facts facts) then
    lemma_positive_product s bc model other reals facts (Some?.v (candidate s facts facts))
  else if Some? (nested_candidate s facts) then
    lemma_nonpositive_product s bc model other reals facts (Some?.v (nested_candidate s facts))
  else
    let p, k, left = Some?.v (constant_product_witness s facts) in
    lemma_constant_product s bc model other reals facts p k left
