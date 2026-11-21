module Z3ArithmeticRewrite

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open FStar.Real
open FStar.List.Tot
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module B = Z3BooleanRewrite
module A = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed
module P = Z3LinearArithmeticTheory
module L = FStar.List.Tot
module Syntax = Z3ArithmeticSyntax

let zero_polynomial = Syntax.zero_polynomial
let same_polynomial = Syntax.same_polynomial
let first_nonzero = Syntax.first_nonzero
let coefficient = Syntax.coefficient
let proportional_polynomial = Syntax.proportional_polynomial
let constant_truth = Syntax.constant_truth
let same_constraint = Syntax.same_constraint
let not_decl = Syntax.not_decl
let constraint_of = Syntax.constraint_of
let boolean_equivalent = Syntax.boolean_equivalent
let integer_equivalent = Syntax.integer_equivalent
let numeric_equivalent = Syntax.numeric_equivalent
let equation_of = Syntax.equation_of
let equation_equivalent = Syntax.equation_equivalent
let constant_equation = Syntax.constant_equation
let split_equation = Syntax.split_equation
let triangle_equality = Syntax.triangle_equality
let binary_product = Syntax.binary_product
let expanded_product = Syntax.expanded_product
let distributed_product = Syntax.distributed_product
let commuted_product = Syntax.commuted_product
let product_factors = Syntax.product_factors
let product_factor_args = Syntax.product_factor_args
let remove_factor = Syntax.remove_factor
let factor_permutation = Syntax.factor_permutation
let product_equivalent = Syntax.product_equivalent
let nonnegative_expr = Syntax.nonnegative_expr
let product_sign_formula = Syntax.product_sign_formula
let zero_factor_equality = Syntax.zero_factor_equality
let product_sign_rewrite = Syntax.product_sign_rewrite
let equivalent = Syntax.equivalent
let lemma_zero_polynomial = Syntax.lemma_zero_polynomial
let lemma_same_polynomial = Syntax.lemma_same_polynomial
let lemma_denotes_zero = Syntax.lemma_denotes_zero
let lemma_scaled_signs = Syntax.lemma_scaled_signs
let lemma_proportional_polynomial = Syntax.lemma_proportional_polynomial
let lemma_equation_polynomials = Syntax.lemma_equation_polynomials
let lemma_constant_truth = Syntax.lemma_constant_truth
let lemma_same_constraint = Syntax.lemma_same_constraint

(* These are local value-typing premises, not the global all-environments
   typing contract used by the older embedding. *)
let rec boolean_values (i:interpretation value) (rho:env value) (e:expr)
  : Tot prop (decreases e) =
  VBool? (eval i e rho) /\
  (match e with
   | App f [a] -> if f = not_decl then boolean_values i rho a else True
   | _ -> True)

let lemma_scaled_relation = Syntax.lemma_scaled_relation

#push-options "--fuel 4"

let rec lemma_constraint_of (fuel:nat) (positive:bool) (e:expr)
                            (p:A.contribution)
                            (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ not_sound i /\ true_sound i /\ false_sound i /\
                    boolean_values i rho e /\ constraint_of fuel positive e == Some p)
          (ensures P.holds p (E.valuation i nu rho) <==>
                   (if positive then lit_true i rho e else ~(lit_true i rho e)))
          (decreases fuel) =
  if e = true_expr || e = false_expr then ()
  else match e with
  | App f [a] ->
    lemma_constraint_of (fuel - 1) (not positive) a p i nu rho;
    (match eval i a rho with VBool _ -> () | _ -> ())
  | _ ->
    (match A.comparison e with
     | Some (r, a, b) ->
       assert (r <> A.Eq);
       let pa = Some?.v (A.linearize 64 a) in
       let pb = Some?.v (A.linearize 64 b) in
       assert (p.poly == fst (A.oriented positive r pa pb) /\
               p.strict == snd (A.oriented positive r pa pb));
       E.lemma_linearize 64 a pa i nu rho;
       E.lemma_linearize 64 b pb i nu rho;
       E.lemma_oriented positive r pa pb (nu (eval i a rho)) (nu (eval i b rho))
                         (E.valuation i nu rho);
       lemma_scaled_relation positive r p.poly.denom
         (P.value p.poly (E.valuation i nu rho)) (nu (eval i a rho)) (nu (eval i b rho));
       assert (lit_true i rho e <==>
               E.numeric_relation r (nu (eval i a rho)) (nu (eval i b rho)))
     | None -> ())

#pop-options

let lemma_boolean_equivalent (a b:expr) (i:interpretation value)
                             (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ not_sound i /\ true_sound i /\ false_sound i /\
                    boolean_values i rho a /\ boolean_values i rho b /\ boolean_equivalent a b)
          (ensures eval i a rho == eval i b rho) =
  let p = Some?.v (constraint_of 16 true a) in
  let q = Some?.v (constraint_of 16 true b) in
  lemma_constraint_of 16 true a p i nu rho;
  lemma_constraint_of 16 true b q i nu rho;
  lemma_same_constraint p q (E.valuation i nu rho);
  match eval i a rho, eval i b rho with
  | VBool _, VBool _ -> ()
  | _, _ -> ()

let lemma_integer_equivalent (a b:expr) (i:interpretation value)
                             (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ VInt? (eval i a rho) /\
                    VInt? (eval i b rho) /\ integer_equivalent a b)
          (ensures eval i a rho == eval i b rho) =
  let p = Some?.v (A.linearize 64 a) in
  let q = Some?.v (A.linearize 64 b) in
  E.lemma_linearize 64 a p i nu rho;
  E.lemma_linearize 64 b q i nu rho;
  lemma_same_polynomial p q (nu (eval i a rho)) (nu (eval i b rho)) (E.valuation i nu rho);
  match eval i a rho, eval i b rho with
  | VInt _, VInt _ -> ()
  | _, _ -> ()

let rec lemma_boolean_values (fuel:nat) (positive:bool)
                             (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires Z3ObservationalEquality.boolean_model i /\ get_sort e == bool_sort /\
                    Some? (constraint_of fuel positive e))
          (ensures boolean_values i rho e)
          (decreases fuel) =
  if e = true_expr || e = false_expr then ()
  else match e with
  | App f [a] -> lemma_boolean_values (fuel - 1) (not positive) i rho a
  | _ -> ()

let lemma_numeric_values_equal (a b:expr) (i:interpretation value)
                               (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ A.numeric_sort (get_sort a) /\
                    get_sort a == get_sort b /\ nu (eval i a rho) == nu (eval i b rho))
          (ensures eval i a rho == eval i b rho) =
  if get_sort a = A.real_s then ()
  else match eval i a rho, eval i b rho with
  | VInt _, VInt _ -> ()
  | _, _ -> ()

let lemma_numeric_equivalent (a b:expr) (i:interpretation value)
                             (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ numeric_equivalent a b)
          (ensures eval i a rho == eval i b rho) =
  let p = Some?.v (A.linearize 64 a) in
  let q = Some?.v (A.linearize 64 b) in
  E.lemma_linearize 64 a p i nu rho;
  E.lemma_linearize 64 b q i nu rho;
  lemma_same_polynomial p q (nu (eval i a rho)) (nu (eval i b rho)) (E.valuation i nu rho);
  lemma_numeric_values_equal a b i nu rho

#push-options "--fuel 4 --ifuel 1"
let lemma_commuted_product (a b:expr) (i:interpretation value)
                          (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ commuted_product a == Some b)
          (ensures eval i a rho == eval i b rho) =
  match a with
  | App f [x; y] ->
    E.lemma_mul_application f [x; y] i nu rho;
    E.lemma_mul_application f [y; x] i nu rho;
    assert_norm (E.numeric_product (FStar.List.Tot.map nu (eval_args i [x; y] rho)) ==
                 nu (eval i x rho) *. nu (eval i y rho));
    assert_norm (E.numeric_product (FStar.List.Tot.map nu (eval_args i [y; x] rho)) ==
                 nu (eval i y rho) *. nu (eval i x rho));
    lemma_numeric_values_equal a b i nu rho
  | _ -> ()
#pop-options

#push-options "--using_facts_from 'Prims FStar.Real FStar.List.Tot FStar.Pervasives Z3AstTheory Z3LinearArithmeticEmbed.numeric_product Z3PolynomialSemantics.numeric_product Z3ArithmeticRewrite.remove_factor Z3ArithmeticSyntax.remove_factor Z3ArithmeticRewrite.factor_permutation Z3ArithmeticSyntax.factor_permutation'"
let rec lemma_product_append (xs ys:list expr) (r:expr -> real)
  : Lemma (E.numeric_product (L.map r (xs @ ys)) ==
           E.numeric_product (L.map r xs) *. E.numeric_product (L.map r ys))
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_product_append rest ys r

let rec lemma_remove_factor (x:expr) (xs ys:list expr) (r:expr -> real)
  : Lemma (requires remove_factor x xs == Some ys)
          (ensures E.numeric_product (L.map r xs) ==
                   r x *. E.numeric_product (L.map r ys))
          (decreases xs) =
  match xs with
  | [] -> ()
  | y :: rest ->
    if x <> y then lemma_remove_factor x rest (Some?.v (remove_factor x rest)) r

let rec lemma_factor_permutation (xs ys:list expr) (r:expr -> real)
  : Lemma (requires factor_permutation xs ys)
          (ensures E.numeric_product (L.map r xs) == E.numeric_product (L.map r ys))
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest ->
    let tail = Some?.v (remove_factor x ys) in
    lemma_remove_factor x ys tail r;
    lemma_factor_permutation rest tail r
#pop-options

let rec lemma_product_factors (fuel:nat) (e:expr) (xs:list expr)
                              (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ product_factors fuel e == Some xs)
          (ensures nu (eval i e rho) == E.numeric_product (L.map (E.valuation i nu rho) xs))
          (decreases %[fuel; 0]) =
  if fuel = 0 then ()
  else match e with
  | App f args ->
    if A.operation_of f args = Some A.Mul then (
      E.lemma_mul_application f args i nu rho;
      lemma_product_factor_args (fuel - 1) args xs i nu rho)
  | _ -> ()

and lemma_product_factor_args (fuel:nat) (args xs:list expr)
                             (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ product_factor_args fuel args == Some xs)
          (ensures E.numeric_product (L.map nu (eval_args i args rho)) ==
                   E.numeric_product (L.map (E.valuation i nu rho) xs))
          (decreases %[fuel; 1; args]) =
  match args with
  | [] -> ()
  | x :: rest ->
    let fs = Some?.v (product_factors fuel x) in
    let tail = Some?.v (product_factor_args fuel rest) in
    lemma_product_factors fuel x fs i nu rho;
    lemma_product_factor_args fuel rest tail i nu rho;
    assert (xs == fs @ tail);
    assert_norm (E.numeric_product (L.map nu (eval_args i (x :: rest) rho)) ==
      nu (eval i x rho) *. E.numeric_product (L.map nu (eval_args i rest rho)));
    lemma_product_append fs tail (E.valuation i nu rho)

let lemma_product_equivalent (a b:expr) (i:interpretation value)
                             (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ product_equivalent a b)
          (ensures eval i a rho == eval i b rho) =
  let xs = Some?.v (product_factors 32 a) in
  let ys = Some?.v (product_factors 32 b) in
  lemma_product_factors 32 a xs i nu rho;
  lemma_product_factors 32 b ys i nu rho;
  lemma_factor_permutation xs ys (E.valuation i nu rho);
  lemma_numeric_values_equal a b i nu rho

let lemma_numeric_zero (zero:expr) (i:interpretation value)
                       (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ A.linearize 4 zero == Some (P.constant 0 1))
          (ensures nu (eval i zero rho) == 0.0R) =
  E.lemma_linearize 4 zero (P.constant 0 1) i nu rho;
  lemma_denotes_zero (P.constant 0 1) (nu (eval i zero rho)) (E.valuation i nu rho)

let lemma_numeric_comparison (e a b:expr) (r:A.relation)
                             (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ A.comparison e == Some (r, a, b) /\ r <> A.Eq)
          (ensures lit_true i rho e <==> E.numeric_relation r (nu (eval i a rho)) (nu (eval i b rho))) = ()

let lemma_numeric_zero_equality (x zero:expr)
                                (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ Z3ObservationalEquality.boolean_model i /\ eq_sound i /\
                    A.numeric_sort (get_sort zero) /\ get_sort x == get_sort zero /\
                    nu (eval i zero rho) == 0.0R)
          (ensures lit_true i rho (mk_eq_expr x zero) <==> nu (eval i x rho) == 0.0R) =
  if nu (eval i x rho) >=. 0.0R && nu (eval i x rho) <=. 0.0R then
    lemma_numeric_values_equal x zero i nu rho

let lemma_zero_product_disjunction (args:list expr) (zero:expr)
                                  (i:interpretation value) (rho:env value)
  : Lemma (requires or_sound i)
          (ensures (let eqs = L.map (zero_factor_equality zero) args in
                    lit_true i rho (App (B.connective_decl B.Disjunction eqs) eqs) <==>
                    clause_holds i rho eqs)) = ()

let rec lemma_zero_product_args (args:list expr) (zero:expr)
                               (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ Z3ObservationalEquality.boolean_model i /\ eq_sound i /\
                    A.numeric_sort (get_sort zero) /\ A.same_sort (get_sort zero) args /\
                    nu (eval i zero rho) == 0.0R)
          (ensures (E.numeric_product (L.map nu (eval_args i args rho)) == 0.0R) <==>
                   clause_holds i rho (L.map (zero_factor_equality zero) args))
          (decreases args) =
  match args with
  | [] -> ()
  | x :: rest ->
    lemma_zero_product_args rest zero i nu rho;
    if nu (eval i x rho) >=. 0.0R && nu (eval i x rho) <=. 0.0R then
      lemma_numeric_values_equal x zero i nu rho;
    assert ((nu (eval i x rho) == 0.0R) <==> eval i x rho == eval i zero rho)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10 --using_facts_from 'Prims FStar.Real'"
let lemma_product_sign_numbers (x y:real)
  : Lemma (((x *. y <=. 0.0R) <==>
            (~((x >=. 0.0R) <==> (y >=. 0.0R)) \/ x == 0.0R \/ y == 0.0R)) /\
           ((x *. y >=. 0.0R) <==>
            (((x >=. 0.0R) <==> (y >=. 0.0R)) \/ x == 0.0R \/ y == 0.0R))) =
  if x >. 0.0R then () else if x <. 0.0R then () else ()

let lemma_fourth_power_zero (x:real)
  : Lemma (x *. (x *. (x *. (x *. 1.0R))) <=. 0.0R <==> x == 0.0R) =
  assert (x *. x >=. 0.0R);
  assert (x *. (x *. (x *. (x *. 1.0R))) == (x *. x) *. (x *. x))
#pop-options

#push-options "--fuel 4 --ifuel 2"
let lemma_nonnegative_expr (x zero:expr) (i:interpretation value)
                           (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ A.numeric_sort (get_sort x) /\
                    get_sort x == get_sort zero /\ nu (eval i zero rho) == 0.0R)
          (ensures get_sort (nonnegative_expr x zero) == bool_sort /\
                   (lit_true i rho (nonnegative_expr x zero) <==> nu (eval i x rho) >=. 0.0R)) =
  assert_norm (get_sort (nonnegative_expr x zero) == bool_sort);
  assert (A.comparison (nonnegative_expr x zero) == Some (A.Ge, x, zero));
  assert (lit_true i rho (nonnegative_expr x zero) <==>
    E.numeric_relation A.Ge (nu (eval i x rho)) (nu (eval i zero rho)))

(* The canonical equality of two Boolean terms, and its canonical negation. *)
let lemma_same_sign (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires Z3ObservationalEquality.boolean_model i /\ eq_sound i /\ not_sound i /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort)
          (ensures (lit_true i rho (mk_eq_expr a b) <==> (lit_true i rho a <==> lit_true i rho b)) /\
                   (lit_true i rho (mk_not_expr (mk_eq_expr a b)) <==> ~(lit_true i rho (mk_eq_expr a b)))) =
  lemma_eq_decl_canonical bool_sort;
  lemma_not_decl_canonical (mk_eq_expr a b);
  assert (get_sort (mk_eq_expr a b) == bool_sort)

let lemma_product_sign_formula (r:A.relation) (x y zero:expr)
                              (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ Z3ObservationalEquality.boolean_model i /\
                    eq_sound i /\ not_sound i /\ and_sound i /\ or_sound i /\
                    (r = A.Le \/ r = A.Ge) /\ A.numeric_sort (get_sort zero) /\
                    get_sort x == get_sort zero /\ get_sort y == get_sort zero /\
                    nu (eval i zero rho) == 0.0R)
          (ensures get_sort (product_sign_formula r x y zero) == bool_sort /\
                   (lit_true i rho (product_sign_formula r x y zero) <==>
                    E.numeric_relation r (nu (eval i x rho) *. nu (eval i y rho)) 0.0R)) =
  lemma_nonnegative_expr x zero i nu rho;
  lemma_nonnegative_expr y zero i nu rho;
  lemma_zero_product_args [x] zero i nu rho;
  lemma_zero_product_args [y] zero i nu rho;
  lemma_product_sign_numbers (nu (eval i x rho)) (nu (eval i y rho));
  let gx, gy = nonnegative_expr x zero, nonnegative_expr y zero in
  let same = mk_eq_expr gx gy in
  let eqs = [mk_eq_expr x zero; mk_eq_expr y zero] in
  let zeros = App (B.connective_decl B.Disjunction eqs) eqs in
  let terms = [(if r = A.Le then mk_not_expr same else same); zeros] in
  B.lemma_connective_holds B.Disjunction i rho eqs;
  B.lemma_connective_holds B.Disjunction i rho terms;
  lemma_same_sign i rho gx gy;
  assert (product_sign_formula r x y zero == App (B.connective_decl B.Disjunction terms) terms);
  assert_norm (get_sort (product_sign_formula r x y zero) == bool_sort);
  assert (lit_true i rho zeros <==>
    nu (eval i x rho) == 0.0R \/ nu (eval i y rho) == 0.0R)

(* The equation branch of `product_sign_rewrite`, from the facts it needs only. *)
let lemma_product_zero_rewrite (e result product zero:expr) (args:list expr)
                               (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ Z3ObservationalEquality.boolean_model i /\ eq_sound i /\
                    and_sound i /\ or_sound i /\
                    A.numeric_sort (get_sort zero) /\ A.same_sort (get_sort zero) args /\
                    get_sort product == get_sort zero /\ nu (eval i zero rho) == 0.0R /\
                    nu (eval i product rho) == E.numeric_product (L.map nu (eval_args i args rho)) /\
                    e == mk_eq_expr product zero /\ get_sort e == bool_sort /\ get_sort result == bool_sort /\
                    result == App (B.connective_decl B.Disjunction (L.map (zero_factor_equality zero) args))
                                  (L.map (zero_factor_equality zero) args))
          (ensures eval i e rho == eval i result rho) =
  let eqs = L.map (zero_factor_equality zero) args in
  lemma_zero_product_args args zero i nu rho;
  lemma_numeric_zero_equality product zero i nu rho;
  B.lemma_connective_holds B.Disjunction i rho eqs;
  Z3ObservationalEquality.lemma_observations_values i rho e result

(* The two-factor sign branch. *)
let lemma_product_sign_pair (r:A.relation) (e result product x y zero:expr)
                            (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ B.boolean_rewrite_model i /\
                    (r = A.Le \/ r = A.Ge) /\ A.numeric_sort (get_sort zero) /\
                    get_sort x == get_sort zero /\ get_sort y == get_sort zero /\
                    nu (eval i zero rho) == 0.0R /\ A.comparison e == Some (r, product, zero) /\
                    nu (eval i product rho) == nu (eval i x rho) *. nu (eval i y rho) /\
                    result == product_sign_formula r x y zero /\ get_sort e == bool_sort)
          (ensures eval i e rho == eval i result rho) =
  lemma_product_sign_formula r x y zero i nu rho;
  lemma_numeric_comparison e product zero r i nu rho;
  Z3ObservationalEquality.lemma_observations_values i rho e result

(* The fourth-power branch: x*x*x*x <= 0 iff x = 0. *)
let lemma_product_fourth_power (e result product x zero:expr)
                               (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ Z3ObservationalEquality.boolean_model i /\ eq_sound i /\
                    A.numeric_sort (get_sort zero) /\ get_sort x == get_sort zero /\
                    nu (eval i zero rho) == 0.0R /\ A.comparison e == Some (A.Le, product, zero) /\
                    nu (eval i product rho) ==
                      nu (eval i x rho) *. (nu (eval i x rho) *. (nu (eval i x rho) *. (nu (eval i x rho) *. 1.0R))) /\
                    result == mk_eq_expr x zero /\ get_sort e == bool_sort)
          (ensures eval i e rho == eval i result rho) =
  lemma_fourth_power_zero (nu (eval i x rho));
  lemma_numeric_zero_equality x zero i nu rho;
  lemma_numeric_comparison e product zero A.Le i nu rho;
  Z3ObservationalEquality.lemma_observations_values i rho e result

#push-options "--z3rlimit 20"
let lemma_product_sign_rewrite (e result:expr) (i:interpretation value)
                               (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ B.boolean_rewrite_model i /\
                    product_sign_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho) =
  match e with
  | App cmp [App f args; zero] ->
    let r, _, _ = Some?.v (A.comparison e) in
    let product = App f args in
    assert (A.comparison e == Some (r, product, zero));
    assert (A.operation_of f args == Some A.Mul);
    assert (2 <= L.length args /\ L.length args <= 64);
    assert (A.numeric_sort (get_sort zero));
    assert (A.same_sort (get_sort zero) args);
    assert (A.linearize 4 zero == Some (P.constant 0 1));
    lemma_numeric_zero zero i nu rho;
    E.lemma_mul_application f args i nu rho;
    assert (get_sort e == bool_sort /\ get_sort result == bool_sort);
    if r = A.Eq then (
      assert (cmp == eq_decl (get_sort product));
      assert (get_sort product == get_sort zero);
      assert_norm (zero_factor_equality == Syntax.zero_factor_equality);
      assert (B.connective_decl B.Disjunction (L.map (zero_factor_equality zero) args) ==
              Z3ClauseSyntax.or_decl (L.map (zero_factor_equality zero) args));
      lemma_product_zero_rewrite e result product zero args i nu rho)
    else (match args with
      | [x; y] ->
        assert (r = A.Le \/ r = A.Ge);
        assert (result == product_sign_formula r x y zero);
        assert_norm (E.numeric_product (L.map nu (eval_args i [x; y] rho)) ==
          nu (eval i x rho) *. nu (eval i y rho));
        lemma_product_sign_pair r e result product x y zero i nu rho
      | [x; _; _; _] ->
        assert (r == A.Le /\ result == mk_eq_expr x zero);
        assert_norm (E.numeric_product (L.map nu (eval_args i [x; x; x; x] rho)) ==
          nu (eval i x rho) *. (nu (eval i x rho) *. (nu (eval i x rho) *. (nu (eval i x rho) *. 1.0R))));
        lemma_product_fourth_power e result product x zero i nu rho
      | _ -> ())
  | _ -> ()
#pop-options
#pop-options

let lemma_equation_sort (e:expr) (p:A.poly)
  : Lemma (requires equation_of e == Some p)
          (ensures get_sort e == bool_sort) =
  match e with App _ [_; _] -> () | _ -> ()

let lemma_equation_of (e:expr) (p:A.poly) (i:interpretation value)
                      (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\ equation_of e == Some p)
          (ensures lit_true i rho e <==> P.value p (E.valuation i nu rho) == 0.0R) =
  match A.comparison e with
  | Some (A.Eq, a, b) ->
    let pa = Some?.v (A.linearize 64 a) in
    let pb = Some?.v (A.linearize 64 b) in
    let x = nu (eval i a rho) in
    let y = nu (eval i b rho) in
    let rv = E.valuation i nu rho in
    E.lemma_linearize 64 a pa i nu rho;
    E.lemma_linearize 64 b pb i nu rho;
    E.lemma_denotes_negative pb y rv;
    E.lemma_denotes_add pa (P.scale (-1) 1 pb) x (0.0R -. y) rv;
    lemma_denotes_zero (P.add pa (P.scale (-1) 1 pb)) (x +. (0.0R -. y)) rv;
    FStar.Classical.impl_intro #(x == y) #(eval i a rho == eval i b rho)
      (fun _ -> lemma_numeric_values_equal a b i nu rho);
    (match e with App _ [_; _] -> () | _ -> ())
  | _ -> ()

let lemma_equation_equivalent (a b:expr) (i:interpretation value)
                              (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\
                    Z3ObservationalEquality.boolean_model i /\ equation_equivalent a b)
          (ensures eval i a rho == eval i b rho) =
  let p = Some?.v (equation_of a) in
  let q = Some?.v (equation_of b) in
  let rv = E.valuation i nu rho in
  lemma_equation_of a p i nu rho;
  lemma_equation_of b q i nu rho;
  lemma_equation_polynomials p q rv;
  assert (lit_true i rho a <==> lit_true i rho b);
  match eval i a rho, eval i b rho with
  | VBool _, VBool _ -> ()
  | _, _ -> ()

let lemma_constant_equation (e result:expr) (i:interpretation value)
                            (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\
                    Z3ObservationalEquality.boolean_model i /\
                    true_sound i /\ false_sound i /\ constant_equation e result)
          (ensures eval i e rho == eval i result rho) =
  let p = Some?.v (equation_of e) in
  let rv = E.valuation i nu rho in
  lemma_equation_of e p i nu rho;
  P.lemma_collect p.mono [] rv;
  P.lemma_all_zero (P.collect p.mono []) rv;
  match eval i e rho with
  | VBool _ -> ()
  | _ -> ()

#push-options "--fuel 4 --ifuel 2"
let lemma_split_equation (e bounds:expr) (i:interpretation value)
                         (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\ and_sound i /\
                    not_sound i /\ true_sound i /\ false_sound i /\
                    Z3ObservationalEquality.boolean_model i /\ split_equation e bounds)
          (ensures eval i e rho == eval i bounds rho) =
  match equation_of e, bounds with
  | Some p, App f [lower; upper] ->
    (match constraint_of 16 true lower, constraint_of 16 true upper with
     | Some l, Some u ->
       let rv = E.valuation i nu rho in
       lemma_equation_sort e p;
       lemma_equation_of e p i nu rho;
       lemma_boolean_values 16 true i rho lower;
       lemma_boolean_values 16 true i rho upper;
       lemma_constraint_of 16 true lower l i nu rho;
       lemma_constraint_of 16 true upper u i nu rho;
       lemma_same_constraint l { P.poly = p; strict = false } rv;
       lemma_same_constraint u { P.poly = P.scale (-1) 1 p; strict = false } rv;
       P.lemma_scale (-1) 1 p rv;
       assert (P.value (P.scale (-1) 1 p) rv == 0.0R -. P.value p rv);
       assert (lit_true i rho lower <==> P.value p rv <=. 0.0R);
       assert (lit_true i rho upper <==> 0.0R <=. P.value p rv);
       assert (lit_true i rho e <==> (lit_true i rho lower /\ lit_true i rho upper));
       assert (lit_true i rho bounds <==> conj_holds i rho [lower; upper]);
       assert (lit_true i rho e <==> lit_true i rho bounds);
       assert (get_sort e == bool_sort);
       assert (get_sort bounds == bool_sort);
       Z3ObservationalEquality.lemma_observations_values i rho e bounds
     | _, _ -> ())
  | _, _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 2"
let lemma_triangle_equality (e:expr) (i:interpretation value)
                            (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\ and_sound i /\ or_sound i /\
                    not_sound i /\ true_sound i /\ false_sound i /\
                    Z3ObservationalEquality.boolean_model i /\ triangle_equality e)
          (ensures lit_true i rho e) =
  match e with
  | App f [App nf [eq]; bound] ->
    (match equation_of eq, constraint_of 16 true bound with
     | Some p, Some q ->
       let rv = E.valuation i nu rho in
       lemma_equation_sort eq p;
       lemma_equation_of eq p i nu rho;
       lemma_boolean_values 16 true i rho bound;
       lemma_constraint_of 16 true bound q i nu rho;
       if same_constraint q { P.poly = p; strict = false }
       then lemma_same_constraint q { P.poly = p; strict = false } rv
       else (
         lemma_same_constraint q { P.poly = P.scale (-1) 1 p; strict = false } rv;
         P.lemma_scale (-1) 1 p rv);
       assert (lit_true i rho eq ==> lit_true i rho bound);
       (match eval i eq rho with VBool _ -> () | _ -> ())
     | _, _ -> ())
  | App f [eq; App lf [l]; App uf [u]] ->
    let forward = App (B.connective_decl B.Conjunction [l; u]) [l; u] in
    let bounds = if split_equation eq forward then forward
                 else App (B.connective_decl B.Conjunction [u; l]) [u; l] in
    lemma_split_equation eq bounds i nu rho;
    B.lemma_connective_holds B.Disjunction i rho [eq; App lf [l]; App uf [u]];
    B.lemma_connective_holds B.Conjunction i rho [l; u];
    B.lemma_connective_holds B.Conjunction i rho [u; l];
    lemma_not_decl_canonical l;
    (match eval i l rho, eval i u rho with
     | VBool _, VBool _ -> ()
     | _, _ -> ())
  | _ -> ()
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10 --using_facts_from 'Prims FStar.Real'"
let lemma_distribute_four (a b c d:real)
  : Lemma ((a +. b) *. (c +. d) ==
           a *. c +. (b *. c +. (a *. d +. (b *. d +. 0.0R)))) =
  assert ((a +. b) *. (c +. d) == (a +. b) *. c +. (a +. b) *. d);
  assert ((a +. b) *. c == a *. c +. b *. c);
  assert ((a +. b) *. d == a *. d +. b *. d)
#pop-options

#push-options "--fuel 4 --ifuel 1 --z3rlimit 20"
let lemma_binary_product (s:sort) (a b:expr) (i:interpretation value)
                         (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ A.numeric_sort s /\
                    get_sort a == s /\ get_sort b == s)
          (ensures nu (eval i (binary_product s a b) rho) ==
                   nu (eval i a rho) *. nu (eval i b rho)) =
  let f = { decl_name = "*"; domain = [s; s]; range = s;
            interp = Some (if s = A.int_s then op_mul else op_arith_mul);
            int_params = [] } in
  E.lemma_mul_application f [a; b] i nu rho;
  assert_norm (E.numeric_product (FStar.List.Tot.map nu (eval_args i [a; b] rho)) ==
               nu (eval i a rho) *. nu (eval i b rho))

let lemma_expanded_product (a b:expr) (i:interpretation value)
                           (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ expanded_product a == Some b)
          (ensures eval i a rho == eval i b rho) =
  match a with
  | App mul [App left [x; y]; App right [z; w]] ->
    let s = mul.range in
    E.lemma_add_application left [x; y] i nu rho;
    E.lemma_add_application right [z; w] i nu rho;
    E.lemma_mul_application mul [App left [x; y]; App right [z; w]] i nu rho;
    assert_norm (E.numeric_sum (FStar.List.Tot.map nu (eval_args i [x; y] rho)) ==
                 nu (eval i x rho) +. nu (eval i y rho));
    assert_norm (E.numeric_sum (FStar.List.Tot.map nu (eval_args i [z; w] rho)) ==
                 nu (eval i z rho) +. nu (eval i w rho));
    assert_norm (E.numeric_product (FStar.List.Tot.map nu
      (eval_args i [App left [x; y]; App right [z; w]] rho)) ==
      nu (eval i (App left [x; y]) rho) *. nu (eval i (App right [z; w]) rho));
    lemma_binary_product s x z i nu rho;
    lemma_binary_product s y z i nu rho;
    lemma_binary_product s x w i nu rho;
    lemma_binary_product s y w i nu rho;
    (match b with
     | App add terms ->
       E.lemma_add_application add terms i nu rho;
       assert_norm (E.numeric_sum (FStar.List.Tot.map nu
         (eval_args i [binary_product s x z; binary_product s y z;
                       binary_product s x w; binary_product s y w] rho)) ==
         nu (eval i (binary_product s x z) rho) +.
         (nu (eval i (binary_product s y z) rho) +.
         (nu (eval i (binary_product s x w) rho) +.
         (nu (eval i (binary_product s y w) rho) +. 0.0R))));
       lemma_distribute_four (nu (eval i x rho)) (nu (eval i y rho))
                             (nu (eval i z rho)) (nu (eval i w rho));
       lemma_numeric_values_equal a b i nu rho
     | _ -> ())
  | _ -> ()
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10 --using_facts_from 'Prims FStar.Real'"
let lemma_distribute_two (x y z:real)
  : Lemma (x *. (y +. z) == x *. y +. x *. z /\
           (y +. z) *. x == y *. x +. z *. x) =
  assert (x *. (y +. z) == x *. y +. x *. z);
  assert ((y +. z) *. x == y *. x +. z *. x)
#pop-options

#push-options "--fuel 4 --ifuel 1 --z3rlimit 20"
let lemma_binary_addition (f:func_decl) (a b:expr) (i:interpretation value)
                          (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ A.operation_of f [a; b] == Some A.Add)
          (ensures nu (eval i (App f [a; b]) rho) ==
                   nu (eval i a rho) +. nu (eval i b rho)) =
  E.lemma_add_application f [a; b] i nu rho;
  assert_norm (E.numeric_sum (L.map nu (eval_args i [a; b] rho)) ==
               nu (eval i a rho) +. nu (eval i b rho))

let lemma_binary_multiplication (f:func_decl) (a b:expr) (i:interpretation value)
                                (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ A.operation_of f [a; b] == Some A.Mul)
          (ensures nu (eval i (App f [a; b]) rho) ==
                   nu (eval i a rho) *. nu (eval i b rho)) =
  E.lemma_mul_application f [a; b] i nu rho;
  assert_norm (E.numeric_product (L.map nu (eval_args i [a; b] rho)) ==
               nu (eval i a rho) *. nu (eval i b rho))

let lemma_distributed_sum (left:bool) (s:sort) (factor z w:expr)
                          (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ A.numeric_sort s /\
                    get_sort factor == s /\ get_sort z == s /\ get_sort w == s)
          (ensures (
            let first, second =
              if left then binary_product s z factor, binary_product s w factor
              else binary_product s factor z, binary_product s factor w in
            nu (eval i first rho) +. nu (eval i second rho) ==
              (if left
               then (nu (eval i z rho) +. nu (eval i w rho)) *. nu (eval i factor rho)
               else nu (eval i factor rho) *. (nu (eval i z rho) +. nu (eval i w rho))))) =
  if left then (
    lemma_binary_product s z factor i nu rho;
    lemma_binary_product s w factor i nu rho)
  else (
    lemma_binary_product s factor z i nu rho;
    lemma_binary_product s factor w i nu rho);
  lemma_distribute_two (nu (eval i factor rho))
                       (nu (eval i z rho)) (nu (eval i w rho))

let lemma_distributed_product_shape (left:bool) (mul add:func_decl)
                                    (x y z w b:expr)
  : Lemma (requires distributed_product left (App mul [x; y]) == Some b /\
                    (if left then x else y) == App add [z; w])
          (ensures (
            let s = mul.range in
            let factor = if left then y else x in
            let first, second =
              if left then binary_product s z factor, binary_product s w factor
              else binary_product s factor z, binary_product s factor w in
            let result = { decl_name = "+"; domain = [s; s]; range = s;
                           interp = Some (if s = A.int_s then op_plus else op_arith_add);
                           int_params = [] } in
            A.operation_of mul [x; y] == Some A.Mul /\
            A.operation_of add [z; w] == Some A.Add /\
            A.numeric_sort s /\ get_sort factor == s /\ get_sort z == s /\ get_sort w == s /\
            b == App result [first; second] /\
            A.operation_of result [first; second] == Some A.Add)) =
  if left then () else ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20 --using_facts_from 'Prims FStar.Pervasives Z3AstTheory Z3LinearArithmeticEmbed.numeric_model Z3ArithmeticRewrite.distributed_product Z3ArithmeticSyntax.distributed_product'"
let lemma_distributed_product (left:bool) (a b:expr) (i:interpretation value)
                              (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ distributed_product left a == Some b)
          (ensures eval i a rho == eval i b rho) =
  match a with
  | App mul [x; y] ->
    let s = mul.range in
    let factor, sum = if left then y, x else x, y in
    (match sum with
     | App add [z; w] ->
       lemma_distributed_product_shape left mul add x y z w b;
       lemma_binary_addition add z w i nu rho;
       lemma_binary_multiplication mul x y i nu rho;
       lemma_distributed_sum left s factor z w i nu rho;
       let first, second =
         if left then binary_product s z factor, binary_product s w factor
         else binary_product s factor z, binary_product s factor w in
       (match b with
        | App result terms ->
          assert (terms == [first; second]);
          lemma_binary_addition result first second i nu rho;
          assert (nu (eval i a rho) == nu (eval i b rho));
          lemma_numeric_values_equal a b i nu rho
        | _ -> ())
     | _ -> ())
  | _ -> ()
#pop-options

let lemma_equivalent_with_numeric_model (a b:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    Z3ObservationalEquality.boolean_model i /\
                    not_sound i /\ true_sound i /\ false_sound i /\ eq_sound i /\
                    and_sound i /\ equivalent a b)
          (ensures eval i a rho == eval i b rho) =
  let aux (nu:value -> real) : Lemma
      (requires E.numeric_model i nu) (ensures eval i a rho == eval i b rho) =
    if boolean_equivalent a b then (
      lemma_boolean_values 16 true i rho a;
      lemma_boolean_values 16 true i rho b;
      lemma_boolean_equivalent a b i nu rho)
    else if numeric_equivalent a b then lemma_numeric_equivalent a b i nu rho
    else if equation_equivalent a b then lemma_equation_equivalent a b i nu rho
    else if constant_equation a b then lemma_constant_equation a b i nu rho
    else if constant_equation b a then lemma_constant_equation b a i nu rho
    else if split_equation a b then lemma_split_equation a b i nu rho
    else if split_equation b a then lemma_split_equation b a i nu rho
    else if commuted_product a = Some b then lemma_commuted_product a b i nu rho
    else if product_equivalent a b then lemma_product_equivalent a b i nu rho
    else if expanded_product a = Some b then lemma_expanded_product a b i nu rho
    else if expanded_product b = Some a then lemma_expanded_product b a i nu rho
    else if distributed_product false a = Some b then lemma_distributed_product false a b i nu rho
    else if distributed_product false b = Some a then lemma_distributed_product false b a i nu rho
    else if distributed_product true a = Some b then lemma_distributed_product true a b i nu rho
    else lemma_distributed_product true b a i nu rho
  in
  FStar.Classical.exists_elim (eval i a rho == eval i b rho)
    #(value -> real) #(fun nu -> E.numeric_model i nu) () (fun nu -> aux nu)

let lemma_product_sign_with_numeric_model (e result:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    B.boolean_rewrite_model i /\ product_sign_rewrite e == Some result)
          (ensures eval i e rho == eval i result rho) =
  let aux (nu:value -> real) : Lemma
      (requires E.numeric_model i nu) (ensures eval i e rho == eval i result rho) =
    lemma_product_sign_rewrite e result i nu rho in
  FStar.Classical.exists_elim (eval i e rho == eval i result rho)
    #(value -> real) #(fun nu -> E.numeric_model i nu) () (fun nu -> aux nu)

let lemma_triangle_with_numeric_model (e:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    Z3ObservationalEquality.boolean_model i /\ eq_sound i /\
                    and_sound i /\ or_sound i /\ not_sound i /\
                    true_sound i /\ false_sound i /\ triangle_equality e)
          (ensures lit_true i rho e) =
  let aux (nu:value -> real) : Lemma
      (requires E.numeric_model i nu) (ensures lit_true i rho e) =
    lemma_triangle_equality e i nu rho
  in
  FStar.Classical.exists_elim (lit_true i rho e)
    #(value -> real) #(fun nu -> E.numeric_model i nu) () (fun nu -> aux nu)
