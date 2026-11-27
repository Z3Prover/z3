module Z3ArithmeticSyntax

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open FStar.Real
open FStar.List.Tot
open Z3AstTheory
open Z3OperatorTags
open Z3ClauseSyntax
module S = Z3ClauseSyntax
module BS = Z3BooleanSyntax
module A = Z3LinearArithmeticAst
module E = Z3PolynomialSemantics
module P = Z3LinearArithmeticTheory
module L = FStar.List.Tot

let conjunction_app (f:func_decl) (args:list expr) : bool =
  f = S.and_decl args && BS.boolean_args args

let disjunction_app (f:func_decl) (args:list expr) : bool =
  f = S.or_decl args && BS.boolean_args args

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
    conjunction_app f [lower; upper] &&
    (match constraint_of 16 true lower, constraint_of 16 true upper with
     | Some l, Some u ->
       same_constraint l { P.poly = p; strict = false } &&
       same_constraint u { P.poly = P.scale (-1) 1 p; strict = false }
     | _, _ -> false)
  | _, _ -> false

let triangle_equality (e:expr) : bool =
  match e with
  | App f [App nf [eq]; bound] ->
    disjunction_app f [App nf [eq]; bound] && nf = not_decl &&
    (match equation_of eq, constraint_of 16 true bound with
     | Some p, Some q ->
       same_constraint q { P.poly = p; strict = false } ||
       same_constraint q { P.poly = P.scale (-1) 1 p; strict = false }
     | _, _ -> false)
  | App f [eq; App lf [l]; App uf [u]] ->
    disjunction_app f [eq; App lf [l]; App uf [u]] &&
    lf = not_decl && uf = not_decl &&
    (split_equation eq (App (S.and_decl [l; u]) [l; u]) ||
     split_equation eq (App (S.and_decl [u; l]) [u; l]))
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

let distributed_product (left:bool) (e:expr) : option expr =
  match e with
  | App mul [x; y] ->
    let s = mul.range in
    let factor, sum = if left then y, x else x, y in
    (match sum with
     | App add [a; b] ->
       if A.operation_of mul [x; y] = Some A.Mul &&
          A.operation_of add [a; b] = Some A.Add then
         let first, second =
           if left then binary_product s a factor, binary_product s b factor
           else binary_product s factor a, binary_product s factor b in
         Some (App { decl_name = "+"; domain = [s; s]; range = s;
                     interp = Some (if s = A.int_s then op_plus else op_arith_add);
                     int_params = [] } [first; second])
       else None
     | _ -> None)
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
               App (S.or_decl zeros) zeros] in
  App (S.or_decl terms) terms

let zero_factor_equality (zero x:expr) : expr = mk_eq_expr x zero

let product_sign_rewrite (e:expr) : option expr =
  match A.comparison e with
  | Some (r, App f args, zero) ->
    if A.linearize 4 zero <> Some (P.constant 0 1) || A.operation_of f args <> Some A.Mul ||
       L.length args < 2 || L.length args > 64 then None
    else if r = A.Eq then
      let eqs = L.map (zero_factor_equality zero) args in
      Some (App (S.or_decl eqs) eqs)
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
  distributed_product false a = Some b || distributed_product false b = Some a ||
  distributed_product true a = Some b || distributed_product true b = Some a ||
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

let lemma_scaled_relation (positive:bool) (rel:A.relation) (d:pos) (v x y:real)
  : Lemma (requires rel <> A.Eq /\ v == of_int d *. E.difference positive rel x y)
          (ensures
            (if (if positive then rel = A.Lt || rel = A.Gt else rel = A.Le || rel = A.Ge)
             then v <. 0.0R else v <=. 0.0R) <==>
            (if positive then E.numeric_relation rel x y else ~(E.numeric_relation rel x y))) =
  assert (of_int d >. 0.0R);
  match rel with
  | A.Le | A.Lt | A.Ge | A.Gt | A.Eq -> if positive then () else ()

