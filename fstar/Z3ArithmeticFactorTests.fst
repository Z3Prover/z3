module Z3ArithmeticFactorTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module A = Z3LinearArithmeticAst
module B = Z3BooleanRewrite
module F = Z3ArithmeticFactor

(* Closed instances of the factored sign rewrite, decided by normalization. *)

let constant (s:sort) (name:string) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = [] } []

let num (s:sort) (n:int) : expr =
  App { decl_name = "numeral"; domain = []; range = s; interp = Some op_num_rational;
        int_params = [n; 1] } []

let arith (name:string) (tag:decl_kind) (s:sort) (args:list expr) : expr =
  App { decl_name = name; domain = FStar.List.Tot.map get_sort args; range = s;
        interp = Some tag; int_params = [] } args

let add (s:sort) (args:list expr) : expr = arith "+" op_arith_add s args
let mul (s:sort) (args:list expr) : expr = arith "*" op_arith_mul s args

let compare (name:string) (tag:decl_kind) (a b:expr) : expr =
  App { decl_name = name; domain = [get_sort a; get_sort b]; range = bool_sort;
        interp = Some tag; int_params = [] } [a; b]

let ge (a b:expr) : expr = compare ">=" op_arith_ge a b
let le (a b:expr) : expr = compare "<=" op_arith_le a b
let either (a b:expr) : expr = App (B.connective_decl B.Disjunction [a; b]) [a; b]

let int_s = A.int_s
let real_s = A.real_s
let x (s:sort) = constant s "x"
let y (s:sort) = constant s "y"
let z (s:sort) = constant s "z"

let zeros_at (z0 f g:expr) : expr = either (mk_eq_expr f z0) (mk_eq_expr g z0)
let signs_at (z0 f g:expr) : expr = mk_eq_expr (ge f z0) (ge g z0)
let zeros (s:sort) (f g:expr) : expr = zeros_at (num s 0) f g
let signs (s:sort) (f g:expr) : expr = signs_at (num s 0) f g

(* x*z + z <= 0  ~>  not ((z >= 0) = (1 + x >= 0)) \/ (z = 0 \/ 1 + x = 0) *)
let le_source (s:sort) : expr = le (add s [mul s [x s; z s]; z s]) (num s 0)
let le_target (s:sort) (g:expr) : expr =
  either (mk_not_expr (signs s (z s) g)) (zeros s (z s) g)
let one_plus_x (s:sort) : expr = add s [num s 1; x s]

(* y*x - (z*x) = 0  ~>  x = 0 \/ z*(-1) + y = 0 *)
let eq_source (s:sort) : expr =
  mk_eq_expr (add s [mul s [y s; x s]; mul s [num s (-1); mul s [z s; x s]]]) (num s 0)
let eq_cofactor (s:sort) : expr = add s [mul s [z s; num s (-1)]; y s]

(* x - x*x >= 0  ~>  ((x >= 0) = (x*(-1) + 1 >= 0)) \/ (x = 0 \/ x*(-1) + 1 = 0) *)
let ge_source (s:sort) : expr =
  ge (add s [x s; mul s [num s (-1); mul s [x s; x s]]]) (num s 0)
let ge_cofactor (s:sort) : expr = add s [mul s [x s; num s (-1)]; num s 1]
let ge_target (s:sort) : expr = either (signs s (x s) (ge_cofactor s)) (zeros s (x s) (ge_cofactor s))

(* The Real instance above with a malformed zero on the right-hand side. *)
let ge_target_at (z0:expr) : expr =
  either (signs_at z0 (x real_s) (ge_cofactor real_s)) (zeros_at z0 (x real_s) (ge_cofactor real_s))
let int_zero : expr = num int_s 0
let opaque_zero : expr = constant real_s "0"
let scaled_zero : expr =
  App { decl_name = "numeral"; domain = []; range = real_s; interp = Some op_num_rational;
        int_params = [0; 2] } []

let accepted ()
  : Lemma (F.check (le_source int_s) (le_target int_s (one_plus_x int_s)) /\
           F.check (le_source real_s) (le_target real_s (one_plus_x real_s)) /\
           F.check (eq_source int_s) (zeros int_s (x int_s) (eq_cofactor int_s)) /\
           F.check (eq_source real_s) (zeros real_s (x real_s) (eq_cofactor real_s)) /\
           F.check (ge_source real_s) (ge_target real_s) /\
           F.check (ge_source int_s) (ge_target int_s)) =
  assert_norm (F.check (le_source int_s) (le_target int_s (one_plus_x int_s)));
  assert_norm (F.check (le_source real_s) (le_target real_s (one_plus_x real_s)));
  assert_norm (F.check (eq_source int_s) (zeros int_s (x int_s) (eq_cofactor int_s)));
  assert_norm (F.check (eq_source real_s) (zeros real_s (x real_s) (eq_cofactor real_s)));
  assert_norm (F.check (ge_source real_s) (ge_target real_s));
  assert_norm (F.check (ge_source int_s) (ge_target int_s))

let rejected ()
  : Lemma (not (F.check (ge (add int_s [mul int_s [x int_s; z int_s]; z int_s]) (num int_s 0))
                        (le_target int_s (one_plus_x int_s))) /\
           not (F.check (le_source int_s) (either (signs int_s (z int_s) (one_plus_x int_s))
                                                  (zeros int_s (z int_s) (one_plus_x int_s)))) /\
           not (F.check (le_source int_s) (le_target int_s (add int_s [num int_s 2; x int_s]))) /\
           not (F.check (eq_source int_s) (zeros int_s (z int_s) (eq_cofactor int_s))) /\
           not (F.check (mk_eq_expr (add int_s [mul int_s [num int_s 2; x int_s];
                                                mul int_s [num int_s 2; y int_s]]) (num int_s 0))
                        (zeros int_s (num int_s 2) (add int_s [x int_s; y int_s]))) /\
           not (F.check (le (add int_s [mul int_s [x int_s; z int_s]; z int_s]) (num int_s 1))
                        (le_target int_s (one_plus_x int_s))) /\
           not (F.check (ge_source real_s) (ge_target_at int_zero)) /\
           not (F.check (ge_source real_s) (ge_target_at opaque_zero)) /\
           not (F.check (ge_source real_s) (ge_target_at scaled_zero))) =
  assert_norm (not (F.check (ge (add int_s [mul int_s [x int_s; z int_s]; z int_s]) (num int_s 0))
                            (le_target int_s (one_plus_x int_s))));
  assert_norm (not (F.check (le_source int_s)
                            (either (signs int_s (z int_s) (one_plus_x int_s))
                                    (zeros int_s (z int_s) (one_plus_x int_s)))));
  assert_norm (not (F.check (le_source int_s)
                            (le_target int_s (add int_s [num int_s 2; x int_s]))));
  assert_norm (not (F.check (eq_source int_s) (zeros int_s (z int_s) (eq_cofactor int_s))));
  assert_norm (not (F.check (mk_eq_expr (add int_s [mul int_s [num int_s 2; x int_s];
                                                    mul int_s [num int_s 2; y int_s]])
                                        (num int_s 0))
                            (zeros int_s (num int_s 2) (add int_s [x int_s; y int_s]))));
  assert_norm (not (F.check (le (add int_s [mul int_s [x int_s; z int_s]; z int_s]) (num int_s 1))
                            (le_target int_s (one_plus_x int_s))));
  assert_norm (not (F.check (ge_source real_s) (ge_target_at int_zero)));
  assert_norm (not (F.check (ge_source real_s) (ge_target_at opaque_zero)));
  assert_norm (not (F.check (ge_source real_s) (ge_target_at scaled_zero)))
