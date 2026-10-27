module Z3IntegerDivision

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open FStar.Real
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module A = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed
module R = Z3ArithmeticRewrite

let op_idiv : decl_kind = 33
let op_mod : decl_kind = 34

let division (f:func_decl) (args:list expr) (remainder:bool) : bool =
  A.same_sort A.int_s args && FStar.List.Tot.length args = 2 &&
  A.application f args A.int_s (if remainder then "mod" else "div")
    (if remainder then op_mod else op_idiv)

let parts (e:expr) (remainder:bool) : option (expr & expr) =
  match e with
  | App f [a; b] -> if division f [a; b] remainder then Some (a, b) else None
  | _ -> None

(* These are operator semantics, not assumptions about proof conclusions.
   Division by zero remains deliberately unspecified. *)
let division_model (i:interpretation value) : prop =
  forall (f:func_decl) (a b:expr) (rho:env value) (remainder:bool) (x y:int).
    division f [a; b] remainder /\ eval i a rho == VInt x /\
    eval i b rho == VInt y /\ y <> 0 ==>
    eval i (App f [a; b]) rho == VInt (if remainder then x % y else x / y)

let numeral (e:expr) (n:int) : bool = A.numeral e = Some (n, 1)

let nonzero_guard (guard b:expr) : bool =
  (guard = false_expr &&
   (match A.numeral b with Some (n, d) -> d = 1 && n <> 0 | None -> false)) ||
  (match A.comparison guard with
   | Some (A.Eq, x, z) -> x = b && numeral z 0
   | _ -> false)

let positive_guard (guard b:expr) : bool =
  (guard = false_expr &&
   (match A.numeral b with Some (n, d) -> d = 1 && n > 0 | None -> false)) ||
  (match A.comparison guard with
   | Some (A.Le, x, z) -> x = b && numeral z 0
   | _ -> false)

let decomposition (guard body:expr) : bool =
  match A.comparison body with
  | Some (A.Eq, a, App add [App mul [b; q]; r]) ->
    A.operation_of add [App mul [b; q]; r] = Some A.Add &&
    A.operation_of mul [b; q] = Some A.Mul &&
    parts q false = Some (a, b) && parts r true = Some (a, b) &&
    nonzero_guard guard b
  | _ -> false

let lower_bound (guard body:expr) : bool =
  match A.comparison body with
  | Some (A.Ge, r, z) ->
    numeral z 0 &&
    (match parts r true with Some (_, b) -> nonzero_guard guard b | None -> false)
  | _ -> false

let upper_bound (guard body:expr) : bool =
  match A.comparison body with
  | Some (A.Le, r, z) ->
    (match parts r true, A.numeral z with
     | Some (_, b), Some (n, d) ->
       d = 1 && A.numeral b = Some (n + 1, 1) && positive_guard guard b
     | _, _ ->
       match r with
       | App add [m; App mul [minus; b]] ->
         A.operation_of add [m; App mul [minus; b]] = Some A.Add &&
         A.operation_of mul [minus; b] = Some A.Mul &&
         numeral minus (-1) && numeral z (-1) &&
         (match parts m true with Some (_, divisor) -> divisor = b && positive_guard guard b
          | None -> false)
       | _ -> false)
  | _ -> false

let residual_bound (guard body:expr) : bool =
  match A.comparison body with
  | Some (A.Ge, App add [a; App mul [minus; App product [b; q]]], z) ->
    A.operation_of add [a; App mul [minus; App product [b; q]]] = Some A.Add &&
    A.operation_of mul [minus; App product [b; q]] = Some A.Mul &&
    A.operation_of product [b; q] = Some A.Mul &&
    numeral minus (-1) && numeral z 0 &&
    parts q false = Some (a, b) && nonzero_guard guard b
  | Some (A.Ge, App add [a; App mul [minus; b; q]], z) ->
    A.operation_of add [a; App mul [minus; b; q]] = Some A.Add &&
    A.operation_of mul [minus; b; q] = Some A.Mul &&
    numeral minus (-1) && numeral z 0 &&
    parts q false = Some (a, b) && nonzero_guard guard b
  | _ -> false

let check (e:expr) : bool =
  match e with
  | App f [guard; body] ->
    f.decl_name = "or" && f.interp = Some op_or &&
    f.domain = [bool_sort; bool_sort] && f.range = bool_sort &&
    (decomposition guard body || lower_bound guard body ||
     upper_bound guard body || residual_bound guard body)
  | _ -> false

let scalar (e:expr) : option (int & expr) =
  match e with
  | App f [a; b] ->
    if A.operation_of f [a; b] <> Some A.Mul || f.range <> A.int_s then None
    else (match A.numeral a, A.numeral b with
    | Some (n, d), _ -> if d = 1 then Some (n, b) else None
    | _, Some (n, d) -> if d = 1 then Some (n, a) else None
    | _, _ -> None)
  | _ -> None

let scaled_division (e:expr) : option (int & expr & pos) =
  match parts e false with
  | Some (a, b) ->
    (match scalar a, A.numeral b with
     | Some (n, x), Some (d, den) ->
       if den = 1 && d > 0 then Some (n, x, d) else None
     | _, _ -> None)
  | None -> None

let cancellation (a b:expr) : bool =
  match scaled_division a, scaled_division b with
  | Some (n, x, d), Some (m, y, e) ->
    x = y && d % e = 0 && n = (d / e) * m
  | _, _ -> false

let folded_target (e:expr) : expr =
  match Z3ArrayRewrite.ite_parts e with
  | Some (guard, _, other) -> if R.constant_equation guard false_expr then other else e
  | None -> e

let equivalent (a b:expr) : bool = cancellation a (folded_target b)

let lemma_numeral (e:expr) (n:int) (i:interpretation value)
                  (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ numeral e n)
          (ensures eval i e rho == VInt n \/ get_sort e == A.real_s) =
  E.lemma_linearize 1 e (Z3LinearArithmeticTheory.constant n 1) i nu rho;
  match e with
  | App f [] -> (match eval i e rho with VInt _ -> () | _ -> ())
  | _ -> ()

let lemma_parts (e:expr) (remainder:bool) (a b:expr)
                (i:interpretation value) (rho:env value)
  : Lemma (requires division_model i /\ parts e remainder == Some (a, b))
          (ensures forall (x y:int). eval i a rho == VInt x /\
                     eval i b rho == VInt y /\ y <> 0 ==>
                     eval i e rho == VInt (if remainder then x % y else x / y)) =
  match e with App f [a; b] -> () | _ -> ()

let lemma_nonzero_guard (guard b:expr) (i:interpretation value)
                         (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\ false_sound i /\
                    get_sort b == A.int_s /\ nonzero_guard guard b /\ ~(lit_true i rho guard))
          (ensures E.integer_value (eval i b rho) <> 0) =
  if guard = false_expr then (
    let n, _ = Some?.v (A.numeral b) in
    lemma_numeral b n i nu rho)
  else match A.comparison guard with
  | Some (A.Eq, x, z) ->
    lemma_numeral z 0 i nu rho;
    (match guard with
     | App f [_; _] -> (match eval i b rho with VInt _ -> () | _ -> ())
     | _ -> ())
  | _ -> ()

let lemma_positive_guard (guard b:expr) (i:interpretation value)
                          (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ false_sound i /\
                    get_sort b == A.int_s /\ positive_guard guard b /\ ~(lit_true i rho guard))
          (ensures E.integer_value (eval i b rho) > 0) =
  if guard = false_expr then (
    let n, _ = Some?.v (A.numeral b) in
    lemma_numeral b n i nu rho)
  else match A.comparison guard with
  | Some (A.Le, x, z) ->
    lemma_numeral z 0 i nu rho;
    Z3LpGomory.lemma_inequality i nu rho guard x z A.Le;
    (match guard with
     | App f [_; _] -> (match eval i b rho with VInt _ -> () | _ -> ())
     | _ -> ())
  | _ -> ()

#push-options "--fuel 4 --ifuel 1 --z3rlimit 20"
let lemma_int_binary (f:func_decl) (a b:expr) (x y:int) (multiply:bool)
                     (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ f.range == A.int_s /\
                    A.operation_of f [a; b] == Some (if multiply then A.Mul else A.Add) /\
                    eval i a rho == VInt x /\ eval i b rho == VInt y)
          (ensures eval i (App f [a; b]) rho == VInt (if multiply then x * y else x + y)) =
  assert (nu (VInt x) == of_int x /\ nu (VInt y) == of_int y);
  if multiply then (
    E.lemma_mul_application f [a; b] i nu rho;
    Z3LinearArithmeticTheory.lemma_of_int_product x y;
    assert_norm (E.numeric_product (FStar.List.Tot.map nu (eval_args i [a; b] rho)) ==
                 nu (eval i a rho) *. nu (eval i b rho)))
  else (
    E.lemma_add_application f [a; b] i nu rho;
    Z3LinearArithmeticTheory.lemma_of_int_sum x y;
    assert_norm (E.numeric_sum (FStar.List.Tot.map nu (eval_args i [a; b] rho)) ==
                 nu (eval i a rho) +. nu (eval i b rho)));
  match eval i (App f [a; b]) rho with VInt _ -> () | _ -> ()

let lemma_int_product3 (f:func_decl) (a b c:expr) (x y z:int)
                       (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ f.range == A.int_s /\
                    A.operation_of f [a; b; c] == Some A.Mul /\
                    eval i a rho == VInt x /\ eval i b rho == VInt y /\ eval i c rho == VInt z)
          (ensures eval i (App f [a; b; c]) rho == VInt (x * (y * z))) =
  assert (nu (VInt x) == of_int x /\ nu (VInt y) == of_int y /\ nu (VInt z) == of_int z);
  E.lemma_mul_application f [a; b; c] i nu rho;
  Z3LinearArithmeticTheory.lemma_of_int_product y z;
  Z3LinearArithmeticTheory.lemma_of_int_product x (y * z);
  assert_norm (E.numeric_product (FStar.List.Tot.map nu (eval_args i [a; b; c] rho)) ==
               nu (eval i a rho) *. (nu (eval i b rho) *. nu (eval i c rho)));
  match eval i (App f [a; b; c]) rho with VInt _ -> () | _ -> ()

let lemma_scalar (e:expr) (n:int) (x:expr)
                 (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ scalar e == Some (n, x))
          (ensures get_sort x == A.int_s /\
                   eval i e rho == VInt (n * E.integer_value (eval i x rho))) =
  match e with
  | App f [a; b] ->
    (match A.numeral a, A.numeral b with
     | Some (k, d), _ ->
       lemma_numeral a n i nu rho;
       lemma_int_binary f a b n (E.integer_value (eval i x rho)) true i nu rho
     | _, Some (k, d) ->
       lemma_numeral b n i nu rho;
       lemma_int_binary f a b (E.integer_value (eval i x rho)) n true i nu rho
     | _, _ -> ())
  | _ -> ()

let lemma_scaled_division (e:expr) (n:int) (x:expr) (d:pos)
                          (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ division_model i /\
                    scaled_division e == Some (n, x, d))
          (ensures eval i e rho == VInt ((n * E.integer_value (eval i x rho)) / d)) =
  let a, b = Some?.v (parts e false) in
  lemma_scalar a n x i nu rho;
  lemma_numeral b d i nu rho;
  lemma_parts e false a b i rho

let lemma_cancel_scale (a:int) (k d:pos)
  : Lemma ((k * a) / (k * d) == a / d) =
  FStar.Math.Lemmas.division_multiplication_lemma (a * k) k d;
  FStar.Math.Lemmas.cancel_mul_div a k

let lemma_cancel_coefficients (n m z:int) (d e:pos)
  : Lemma (requires d % e = 0 /\ n = (d / e) * m)
          (ensures (n * z) / d == (m * z) / e) =
  FStar.Math.Lemmas.lemma_div_mod d e;
  let k = d / e in
  assert (k > 0 /\ d == k * e /\ n * z == k * (m * z));
  lemma_cancel_scale (m * z) k e

let lemma_cancellation (a b:expr) (i:interpretation value)
                       (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ division_model i /\ cancellation a b)
          (ensures eval i a rho == eval i b rho) =
  match scaled_division a, scaled_division b with
  | Some (n, x, d), Some (m, y, e) ->
    lemma_scaled_division a n x d i nu rho;
    lemma_scaled_division b m y e i nu rho;
    assert (x == y /\ d % e = 0 /\ n = (d / e) * m);
    lemma_cancel_coefficients n m (E.integer_value (eval i x rho)) d e
  | _, _ -> ()

let lemma_equivalent (a b:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    division_model i /\ Z3ObservationalEquality.boolean_model i /\
                    eq_sound i /\ true_sound i /\ false_sound i /\
                    Z3ArrayRewrite.term_ite_sound i /\ equivalent a b)
          (ensures eval i a rho == eval i b rho) =
  let aux (nu:value -> real)
    : Lemma (requires E.numeric_model i nu) (ensures eval i a rho == eval i b rho) =
    lemma_cancellation a (folded_target b) i nu rho;
    match Z3ArrayRewrite.ite_parts b with
    | Some (guard, then_, other) ->
      if R.constant_equation guard false_expr then (
        R.lemma_constant_equation guard false_expr i nu rho;
        Z3ArrayRewrite.lemma_ite_parts i rho b guard then_ other)
    | None -> () in
  FStar.Classical.exists_elim (eval i a rho == eval i b rho)
    #(value -> real) #(fun nu -> E.numeric_model i nu) () (fun nu -> aux nu)

let lemma_decomposition (guard body:expr) (i:interpretation value)
                        (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ division_model i /\ eq_sound i /\ false_sound i /\
                    decomposition guard body /\ ~(lit_true i rho guard))
          (ensures lit_true i rho body) =
  match A.comparison body with
  | Some (A.Eq, a, App add [App mul [b; q]; r]) ->
    lemma_nonzero_guard guard b i nu rho;
    lemma_parts q false a b i rho;
    lemma_parts r true a b i rho;
    let x = E.integer_value (eval i a rho) in
    let y = E.integer_value (eval i b rho) in
    assert (eval i a rho == VInt x /\ eval i b rho == VInt y);
    assert (eval i q rho == VInt (x / y) /\ eval i r rho == VInt (x % y));
    FStar.Math.Lemmas.lemma_div_mod x y;
    lemma_int_binary mul b q y (x / y) true i nu rho;
    lemma_int_binary add (App mul [b; q]) r (y * (x / y)) (x % y) false i nu rho;
    (match body with App f [_; _] -> () | _ -> ())
  | _ -> ()

let lemma_lower_bound (guard body:expr) (i:interpretation value)
                      (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ division_model i /\ eq_sound i /\ false_sound i /\
                    lower_bound guard body /\ ~(lit_true i rho guard))
          (ensures lit_true i rho body) =
  match A.comparison body with
  | Some (A.Ge, r, z) ->
    let a, b = Some?.v (parts r true) in
    lemma_nonzero_guard guard b i nu rho;
    lemma_parts r true a b i rho;
    lemma_numeral z 0 i nu rho;
    Z3LpGomory.lemma_inequality i nu rho body r z A.Ge;
    (match eval i a rho, eval i b rho with VInt x, VInt y -> () | _, _ -> ())
  | _ -> ()

(* Finish comparisons only after evaluating their integer operands.  Keeping
   this bridge separate avoids mixing real-order reasoning with decoding the
   division checker and evaluating nested arithmetic applications. *)
let lemma_int_inequality (body a b:expr) (r:A.relation) (x y:int)
                         (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ A.comparison body == Some (r, a, b) /\
                    eval i a rho == VInt x /\ eval i b rho == VInt y /\
                    ((r == A.Le /\ x <= y) \/ (r == A.Ge /\ y <= x)))
          (ensures lit_true i rho body) =
  assert (nu (VInt x) == of_int x /\ nu (VInt y) == of_int y);
  if r = A.Le then assert (of_int x <=. of_int y)
  else assert (of_int y <=. of_int x);
  Z3LpGomory.lemma_inequality i nu rho body a b r

#push-options "--fuel 2"
let lemma_upper_bound (guard body:expr) (i:interpretation value)
                      (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ division_model i /\ false_sound i /\
                    upper_bound guard body /\ ~(lit_true i rho guard))
          (ensures lit_true i rho body) =
  match A.comparison body with
  | Some (A.Le, r, z) ->
    (match parts r true, A.numeral z with
     | Some (a, b), Some (n, d) ->
       assert (d == 1 /\ A.numeral b == Some (n + 1, 1) /\ positive_guard guard b);
       lemma_positive_guard guard b i nu rho;
       lemma_parts r true a b i rho;
       lemma_numeral z n i nu rho;
       lemma_numeral b (n + 1) i nu rho;
       (match eval i a rho with
        | VInt x ->
          assert (eval i b rho == VInt (n + 1));
          assert (eval i r rho == VInt (x % (n + 1)));
          assert (x % (n + 1) <= n);
          lemma_int_inequality body r z A.Le (x % (n + 1)) n i nu rho
        | _ -> ())
     | _, _ ->
       match r with
       | App add [m; App mul [minus; b]] ->
         let a, _ = Some?.v (parts m true) in
         assert (parts m true == Some (a, b) /\ positive_guard guard b);
         lemma_positive_guard guard b i nu rho;
         lemma_parts m true a b i rho;
         lemma_numeral minus (-1) i nu rho;
         lemma_numeral z (-1) i nu rho;
         let x = E.integer_value (eval i a rho) in
         let y = E.integer_value (eval i b rho) in
         assert (eval i a rho == VInt x /\ eval i b rho == VInt y);
         assert (eval i m rho == VInt (x % y));
         assert (x % y < y /\ x % y - y <= -1);
         assert (eval i minus rho == VInt (-1));
         lemma_int_binary mul minus b (-1) y true i nu rho;
         lemma_int_binary add m (App mul [minus; b]) (x % y) (-y) false i nu rho;
         assert (eval i r rho == VInt (x % y - y));
         lemma_int_inequality body r z A.Le (x % y - y) (-1) i nu rho
       | _ -> ())
  | _ -> ()

let lemma_residual_bound (guard body:expr) (i:interpretation value)
                         (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ division_model i /\ eq_sound i /\ false_sound i /\
                    residual_bound guard body /\ ~(lit_true i rho guard))
          (ensures lit_true i rho body) =
  match A.comparison body with
  | Some (A.Ge, App add [a; App mul [minus; App product [b; q]]], z) ->
    lemma_nonzero_guard guard b i nu rho;
    lemma_parts q false a b i rho;
    lemma_numeral minus (-1) i nu rho;
    lemma_numeral z 0 i nu rho;
    let x = E.integer_value (eval i a rho) in
    let y = E.integer_value (eval i b rho) in
    assert (eval i a rho == VInt x /\ eval i b rho == VInt y);
    assert (eval i q rho == VInt (x / y));
    FStar.Math.Lemmas.lemma_div_mod x y;
    assert (eval i minus rho == VInt (-1));
    lemma_int_binary product b q y (x / y) true i nu rho;
    lemma_int_binary mul minus (App product [b; q]) (-1) (y * (x / y)) true i nu rho;
    lemma_int_binary add a (App mul [minus; App product [b; q]])
      x (-1 * (y * (x / y))) false i nu rho;
    assert (x - y * (x / y) == x % y /\ 0 <= x % y);
    assert (eval i (App add [a; App mul [minus; App product [b; q]]]) rho == VInt (x % y));
    lemma_int_inequality body (App add [a; App mul [minus; App product [b; q]]])
      z A.Ge (x % y) 0 i nu rho
  | Some (A.Ge, App add [a; App mul [minus; b; q]], z) ->
    lemma_nonzero_guard guard b i nu rho;
    lemma_parts q false a b i rho;
    lemma_numeral minus (-1) i nu rho;
    lemma_numeral z 0 i nu rho;
    let x = E.integer_value (eval i a rho) in
    let y = E.integer_value (eval i b rho) in
    assert (eval i a rho == VInt x /\ eval i b rho == VInt y);
    assert (eval i q rho == VInt (x / y));
    FStar.Math.Lemmas.lemma_div_mod x y;
    assert (eval i minus rho == VInt (-1));
    lemma_int_product3 mul minus b q (-1) y (x / y) i nu rho;
    lemma_int_binary add a (App mul [minus; b; q]) x (-1 * (y * (x / y))) false i nu rho;
    assert (x - y * (x / y) == x % y /\ 0 <= x % y);
    assert (eval i (App add [a; App mul [minus; b; q]]) rho == VInt (x % y));
    lemma_int_inequality body (App add [a; App mul [minus; b; q]])
      z A.Ge (x % y) 0 i nu rho
  | _ -> ()
#pop-options

let lemma_check (e:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    division_model i /\ eq_sound i /\ false_sound i /\ or_sound i /\ check e)
          (ensures lit_true i rho e) =
  let aux (nu:value -> real)
    : Lemma (requires E.numeric_model i nu) (ensures lit_true i rho e) =
    match e with
    | App f [guard; body] ->
      FStar.Classical.excluded_middle (lit_true i rho guard);
      FStar.Classical.or_elim #(lit_true i rho guard) #(~(lit_true i rho guard))
        #(fun () -> lit_true i rho e)
        (fun _ -> ())
        (fun _ ->
          if decomposition guard body then lemma_decomposition guard body i nu rho
          else if lower_bound guard body then lemma_lower_bound guard body i nu rho
          else if upper_bound guard body then lemma_upper_bound guard body i nu rho
          else lemma_residual_bound guard body i nu rho)
    | _ -> () in
  FStar.Classical.exists_elim (lit_true i rho e)
    #(value -> real) #(fun nu -> E.numeric_model i nu) () (fun nu -> aux nu)
#pop-options
