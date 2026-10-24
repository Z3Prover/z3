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

let zero_polynomial (p:A.poly) : bool =
  p.cst = 0 && P.all_zero (P.collect p.mono [])

let same_polynomial (p q:A.poly) : bool =
  zero_polynomial (P.add p (P.scale (-1) 1 q))

let rec first_nonzero (ms:list (int & expr))
  : Tot (option (int & expr)) (decreases ms) =
  match ms with
  | [] -> None
  | (n, e) :: rest -> if n = 0 then first_nonzero rest else Some (n, e)

let rec coefficient (e:expr) (ms:list (int & expr)) : Tot int (decreases ms) =
  match ms with
  | [] -> 0
  | (n, v) :: rest -> if v = e then n else coefficient e rest

let proportional_polynomial (positive:bool) (p q:A.poly) : bool =
  match first_nonzero (P.collect p.mono []) with
  | Some (a, e) ->
    let b = coefficient e (P.collect q.mono []) in
    a <> 0 && b <> 0 && (not positive || (a > 0) = (b > 0)) &&
    same_polynomial (P.scale b 1 { p with denom = 1 })
                    (P.scale a 1 { q with denom = 1 })
  | None -> false

let constant_truth (p:A.contribution) : option bool =
  if P.all_zero (P.collect p.poly.mono [])
  then Some (if p.strict then p.poly.cst < 0 else p.poly.cst <= 0)
  else None

let same_constraint (p q:A.contribution) : bool =
  match constant_truth p, constant_truth q with
  | Some x, Some y -> x = y
  | _, _ ->
    p.strict = q.strict &&
    (same_polynomial p.poly q.poly || proportional_polynomial true p.poly q.poly)

let not_decl : func_decl =
  { decl_name = "not"; domain = [bool_sort]; range = bool_sort;
    interp = Some op_not; int_params = [] }

let rec constraint_of (fuel:nat) (positive:bool) (e:expr)
  : Tot (option A.contribution) (decreases fuel) =
  if fuel = 0 then None
  else if e = true_expr || e = false_expr then
    Some { P.poly = P.constant (if (e = true_expr) = positive then 0 else 1) 1;
           strict = false }
  else match e with
  | App f [a] ->
    if f = not_decl && get_sort a = bool_sort
    then constraint_of (fuel - 1) (not positive) a else None
  | _ ->
    (match A.comparison e with
     | Some (r, a, b) ->
       if r = A.Eq then None
       else (match A.linearize 64 a, A.linearize 64 b with
       | Some pa, Some pb ->
         let p, strict = A.oriented positive r pa pb in
         Some { P.poly = p; strict = strict }
       | _, _ -> None)
     | None -> None)

let boolean_equivalent (a b:expr) : bool =
  get_sort a = bool_sort && get_sort b = bool_sort &&
  (match constraint_of 16 true a, constraint_of 16 true b with
   | Some p, Some q -> same_constraint p q
   | _, _ -> false)

let integer_equivalent (a b:expr) : bool =
  get_sort a = A.int_s && get_sort b = A.int_s &&
  (match A.linearize 64 a, A.linearize 64 b with
   | Some p, Some q -> same_polynomial p q
   | _, _ -> false)

let numeric_equivalent (a b:expr) : bool =
  A.numeric_sort (get_sort a) && get_sort a = get_sort b &&
  (match A.linearize 64 a, A.linearize 64 b with
   | Some p, Some q -> same_polynomial p q
   | _, _ -> false)

let equation_of (e:expr) : option A.poly =
  match A.comparison e with
  | Some (A.Eq, a, b) ->
    (match A.linearize 64 a, A.linearize 64 b with
     | Some p, Some q -> Some (P.add p (P.scale (-1) 1 q))
     | _, _ -> None)
  | _ -> None

let equation_equivalent (a b:expr) : bool =
  match equation_of a, equation_of b with
  | Some p, Some q ->
    same_polynomial p q || same_polynomial p (P.scale (-1) 1 q) ||
    proportional_polynomial false p q
  | _, _ -> false

let constant_equation (e result:expr) : bool =
  match equation_of e with
  | Some p ->
    P.all_zero (P.collect p.mono []) &&
    result = (if p.cst = 0 then true_expr else false_expr)
  | None -> false

let split_equation (e bounds:expr) : bool =
  match equation_of e, bounds with
  | Some p, App f [lower; upper] ->
    B.connective_app B.Conjunction f [lower; upper] &&
    (match constraint_of 16 true lower, constraint_of 16 true upper with
     | Some l, Some u ->
       same_constraint l { P.poly = p; strict = false } &&
       same_constraint u { P.poly = P.scale (-1) 1 p; strict = false }
     | _, _ -> false)
  | _, _ -> false

let triangle_equality (e:expr) : bool =
  match e with
  | App f [App nf [eq]; bound] ->
    B.connective_app B.Disjunction f [App nf [eq]; bound] && nf = not_decl &&
    (match equation_of eq, constraint_of 16 true bound with
     | Some p, Some q ->
       same_constraint q { P.poly = p; strict = false } ||
       same_constraint q { P.poly = P.scale (-1) 1 p; strict = false }
     | _, _ -> false)
  | App f [eq; App lf [l]; App uf [u]] ->
    B.connective_app B.Disjunction f [eq; App lf [l]; App uf [u]] &&
    lf = not_decl && uf = not_decl &&
    (split_equation eq (App (B.connective_decl B.Conjunction [l; u]) [l; u]) ||
     split_equation eq (App (B.connective_decl B.Conjunction [u; l]) [u; l]))
  | _ -> false

let binary_product (s:sort) (a b:expr) : expr =
  App { decl_name = "*"; domain = [s; s]; range = s;
        interp = Some (if s = A.int_s then op_mul else op_arith_mul);
        int_params = [] } [a; b]

let expanded_product (e:expr) : option expr =
  match e with
  | App mul [App left [a; b]; App right [c; d]] ->
    let s = mul.range in
    if A.operation_of mul [App left [a; b]; App right [c; d]] = Some A.Mul &&
       A.operation_of left [a; b] = Some A.Add &&
       A.operation_of right [c; d] = Some A.Add then
      let terms = [binary_product s a c; binary_product s b c;
                   binary_product s a d; binary_product s b d] in
      Some (App { decl_name = "+"; domain = [s; s; s; s]; range = s;
                  interp = Some op_arith_add; int_params = [] } terms)
    else None
  | _ -> None

let commuted_product (e:expr) : option expr =
  match e with
  | App f [x; y] ->
    if A.operation_of f [x; y] = Some A.Mul then Some (App f [y; x])
    else None
  | _ -> None

let rec product_factors (fuel:nat) (e:expr)
  : Tot (option (list expr)) (decreases %[fuel; 0]) =
  if fuel = 0 then None
  else match e with
  | App f args ->
    if A.operation_of f args = Some A.Mul
    then product_factor_args (fuel - 1) args
    else Some [e]
  | _ -> Some [e]

and product_factor_args (fuel:nat) (args:list expr)
  : Tot (option (list expr)) (decreases %[fuel; 1; args]) =
  match args with
  | [] -> Some []
  | x :: rest ->
    (match product_factors fuel x with
     | None -> None
     | Some xs ->
       (match product_factor_args fuel rest with
        | Some ys -> if L.length xs + L.length ys <= 64 then Some (xs @ ys) else None
        | None -> None))

let rec remove_factor (x:expr) (xs:list expr)
  : Tot (option (list expr)) (decreases xs) =
  match xs with
  | [] -> None
  | y :: rest ->
    if x = y then Some rest
    else (match remove_factor x rest with Some ys -> Some (y :: ys) | None -> None)

let rec factor_permutation (xs ys:list expr) : Tot bool (decreases xs) =
  match xs with
  | [] -> ys = []
  | x :: rest ->
    (match remove_factor x ys with
     | Some tail -> factor_permutation rest tail
     | None -> false)

let product_equivalent (a b:expr) : bool =
  A.numeric_sort (get_sort a) && get_sort a = get_sort b &&
  (match product_factors 32 a, product_factors 32 b with
   | Some xs, Some ys -> factor_permutation xs ys
   | _, _ -> false)

let nonnegative_expr (x zero:expr) : expr =
  App { decl_name = ">="; domain = [get_sort x; get_sort zero]; range = bool_sort;
        interp = Some op_arith_ge; int_params = [] } [x; zero]

let product_sign_formula (r:A.relation) (x y zero:expr) : expr =
  let same_sign = mk_eq_expr (nonnegative_expr x zero) (nonnegative_expr y zero) in
  let zeros = [mk_eq_expr x zero; mk_eq_expr y zero] in
  let terms = [(if r = A.Le then mk_not_expr same_sign else same_sign);
               App (B.connective_decl B.Disjunction zeros) zeros] in
  App (B.connective_decl B.Disjunction terms) terms

let zero_factor_equality (zero x:expr) : expr = mk_eq_expr x zero

let product_sign_rewrite (e:expr) : option expr =
  match A.comparison e with
  | Some (r, App f args, zero) ->
    if A.linearize 4 zero <> Some (P.constant 0 1) || A.operation_of f args <> Some A.Mul ||
       L.length args < 2 || L.length args > 64 then None
    else if r = A.Eq then
      let eqs = L.map (zero_factor_equality zero) args in
      Some (App (B.connective_decl B.Disjunction eqs) eqs)
    else (match args with
      | [x; y] ->
        if r = A.Le || r = A.Ge then Some (product_sign_formula r x y zero) else None
      | [x; y; z; w] ->
        if r = A.Le && x = y && x = z && x = w then Some (mk_eq_expr x zero) else None
      | _ -> None)
  | _ -> None

let equivalent (a b:expr) : bool =
  boolean_equivalent a b || numeric_equivalent a b ||
  equation_equivalent a b || constant_equation a b || constant_equation b a ||
  split_equation a b || split_equation b a ||
  expanded_product a = Some b || expanded_product b = Some a ||
  commuted_product a = Some b || product_equivalent a b

let lemma_zero_polynomial (p:A.poly) (rho:expr -> real)
  : Lemma (requires zero_polynomial p) (ensures P.value p rho == 0.0R) =
  P.lemma_collect p.mono [] rho;
  P.lemma_all_zero (P.collect p.mono []) rho

let lemma_same_polynomial (p q:A.poly) (x y:real) (rho:expr -> real)
  : Lemma (requires same_polynomial p q /\ E.denotes p x rho /\ E.denotes q y rho)
          (ensures x == y) =
  E.lemma_denotes_negative q y rho;
  E.lemma_denotes_add p (P.scale (-1) 1 q) x (0.0R -. y) rho;
  lemma_zero_polynomial (P.add p (P.scale (-1) 1 q)) rho;
  assert (of_int (P.add p (P.scale (-1) 1 q)).denom >. 0.0R)

let lemma_denotes_zero (p:A.poly) (x:real) (rho:expr -> real)
  : Lemma (requires E.denotes p x rho)
          (ensures P.value p rho == 0.0R <==> x == 0.0R) =
  assert (of_int p.denom >. 0.0R);
  assert (P.value p rho == of_int p.denom *. x)

let lemma_scaled_signs (a b x y:real)
  : Lemma (requires ~(a == 0.0R) /\ ~(b == 0.0R) /\ b *. x == a *. y)
          (ensures (x == 0.0R <==> y == 0.0R) /\
                   ((a >. 0.0R <==> b >. 0.0R) ==>
                    (x <. 0.0R <==> y <. 0.0R) /\
                    (x <=. 0.0R <==> y <=. 0.0R))) =
  if a >. 0.0R then () else ()

let lemma_proportional_polynomial (positive:bool) (p q:A.poly) (rho:expr -> real)
  : Lemma (requires proportional_polynomial positive p q)
          (ensures (P.value p rho == 0.0R <==> P.value q rho == 0.0R) /\
                   (positive ==>
                    (P.value p rho <. 0.0R <==> P.value q rho <. 0.0R) /\
                    (P.value p rho <=. 0.0R <==> P.value q rho <=. 0.0R))) =
  let a, e = Some?.v (first_nonzero (P.collect p.mono [])) in
  let b = coefficient e (P.collect q.mono []) in
  let raw_p = { p with denom = 1 } in
  let raw_q = { q with denom = 1 } in
  let x = P.value p rho in
  let y = P.value q rho in
  P.lemma_scale b 1 raw_p rho;
  P.lemma_scale a 1 raw_q rho;
  lemma_same_polynomial (P.scale b 1 raw_p) (P.scale a 1 raw_q)
                        (of_int b *. x) (of_int a *. y) rho;
  lemma_scaled_signs (of_int a) (of_int b) x y

let lemma_equation_polynomials (p q:A.poly) (rho:expr -> real)
  : Lemma (requires same_polynomial p q || same_polynomial p (P.scale (-1) 1 q) ||
                    proportional_polynomial false p q)
          (ensures P.value p rho == 0.0R <==> P.value q rho == 0.0R) =
  if proportional_polynomial false p q then lemma_proportional_polynomial false p q rho
  else (
    let x = P.value p rho /. of_int p.denom in
    let y = P.value q rho /. of_int q.denom in
    assert (of_int p.denom >. 0.0R /\ of_int q.denom >. 0.0R);
    assert (E.denotes p x rho /\ E.denotes q y rho);
    if same_polynomial p q then lemma_same_polynomial p q x y rho
    else (
      E.lemma_denotes_negative q y rho;
      lemma_same_polynomial p (P.scale (-1) 1 q) x (0.0R -. y) rho);
    assert (x == 0.0R <==> y == 0.0R);
    lemma_denotes_zero p x rho;
    lemma_denotes_zero q y rho)

let lemma_constant_truth (p:A.contribution) (rho:expr -> real) (b:bool)
  : Lemma (requires constant_truth p == Some b)
          (ensures P.holds p rho <==> b) =
  P.lemma_collect p.poly.mono [] rho;
  P.lemma_all_zero (P.collect p.poly.mono []) rho

let lemma_same_constraint (p q:A.contribution) (rho:expr -> real)
  : Lemma (requires same_constraint p q)
          (ensures P.holds p rho <==> P.holds q rho) =
  match constant_truth p, constant_truth q with
  | Some x, Some y ->
    lemma_constant_truth p rho x;
    lemma_constant_truth q rho y
  | _, _ ->
    if proportional_polynomial true p.poly q.poly then
      lemma_proportional_polynomial true p.poly q.poly rho
    else (
      let x = P.value p.poly rho /. of_int p.poly.denom in
      let y = P.value q.poly rho /. of_int q.poly.denom in
      assert (E.denotes p.poly x rho /\ E.denotes q.poly y rho);
      lemma_same_polynomial p.poly q.poly x y rho;
      assert (of_int p.poly.denom >. 0.0R /\ of_int q.poly.denom >. 0.0R))

(* These are local value-typing premises, not the global all-environments
   typing contract used by the older embedding. *)
let rec boolean_values (i:interpretation value) (rho:env value) (e:expr)
  : Tot prop (decreases e) =
  VBool? (eval i e rho) /\
  (match e with
   | App f [a] -> if f = not_decl then boolean_values i rho a else True
   | _ -> True)

let lemma_scaled_relation (positive:bool) (rel:A.relation) (d:pos) (v x y:real)
  : Lemma (requires rel <> A.Eq /\ v == of_int d *. E.difference positive rel x y)
          (ensures
            (if (if positive then rel = A.Lt || rel = A.Gt else rel = A.Le || rel = A.Ge)
             then v <. 0.0R else v <=. 0.0R) <==>
            (if positive then E.numeric_relation rel x y else ~(E.numeric_relation rel x y))) =
  assert (of_int d >. 0.0R);
  match rel with
  | A.Le | A.Lt | A.Ge | A.Gt | A.Eq -> if positive then () else ()

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

#push-options "--using_facts_from 'Prims FStar.Real FStar.List.Tot FStar.Pervasives Z3AstTheory Z3LinearArithmeticEmbed.numeric_product Z3ArithmeticRewrite.remove_factor Z3ArithmeticRewrite.factor_permutation'"
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

let lemma_product_sign_formula (r:A.relation) (x y zero:expr)
                              (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ B.boolean_rewrite_model i /\
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
  assert_norm (get_sort (product_sign_formula r x y zero) == bool_sort);
  assert (lit_true i rho zeros <==>
    nu (eval i x rho) == 0.0R \/ nu (eval i y rho) == 0.0R);
  (match eval i gx rho, eval i gy rho with
   | VBool _, VBool _ ->
     assert (lit_true i rho same <==>
       ((nu (eval i x rho) >=. 0.0R) <==> (nu (eval i y rho) >=. 0.0R)))
   | _, _ -> ());
  assert (lit_true i rho (mk_not_expr same) <==> ~(lit_true i rho same))

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
      lemma_zero_product_args args zero i nu rho;
      lemma_numeric_zero_equality product zero i nu rho;
      assert (cmp == eq_decl (get_sort product));
      assert (lit_true i rho e <==> nu (eval i product rho) == 0.0R);
      let eqs = L.map (zero_factor_equality zero) args in
      assert (result == App (B.connective_decl B.Disjunction eqs) eqs);
      lemma_zero_product_disjunction args zero i rho;
      assert (lit_true i rho result <==>
        clause_holds i rho eqs);
      Z3ObservationalEquality.lemma_observations_values i rho e result)
    else (match args with
      | [x; y] ->
        assert (r = A.Le \/ r = A.Ge);
        assert (result == product_sign_formula r x y zero);
        assert_norm (E.numeric_product (L.map nu (eval_args i [x; y] rho)) ==
          nu (eval i x rho) *. nu (eval i y rho));
        lemma_product_sign_formula r x y zero i nu rho;
        lemma_numeric_comparison e product zero r i nu rho;
        assert (lit_true i rho e <==> E.numeric_relation r (nu (eval i product rho)) 0.0R);
        Z3ObservationalEquality.lemma_observations_values i rho e result
      | [x; _; _; _] ->
        assert (r == A.Le /\ result == mk_eq_expr x zero);
        assert_norm (E.numeric_product (L.map nu (eval_args i [x; x; x; x] rho)) ==
          nu (eval i x rho) *. (nu (eval i x rho) *. (nu (eval i x rho) *. (nu (eval i x rho) *. 1.0R))));
        lemma_fourth_power_zero (nu (eval i x rho));
        lemma_numeric_zero_equality x zero i nu rho;
        lemma_numeric_comparison e product zero r i nu rho;
        assert (lit_true i rho e <==> nu (eval i product rho) <=. 0.0R);
        assert (lit_true i rho result <==> nu (eval i x rho) == 0.0R);
        Z3ObservationalEquality.lemma_observations_values i rho e result
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
    else lemma_expanded_product b a i nu rho
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
