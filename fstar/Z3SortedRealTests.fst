module Z3SortedRealTests

(* Executable controls of the typed Real checks (Z3SortedRealLinear), decided
   by normalization of the checker functions themselves. *)

open Z3AstTheory
open Z3ValueTheory
module A = Z3LinearArithmeticAst
module P = Z3LinearArithmeticTheory
module R = Z3ResolutionProofTheory
module RL = Z3SortedReal
module LIN = Z3SortedRealLinear

(* ---------------------------------------------------------------------- *)
(* Executable controls on Real atoms x, y (no Int rounding at Real)         *)
(* ---------------------------------------------------------------------- *)

let x_real : expr = Var 0 A.real_s
let y_real : expr = Var 1 A.real_s
let zero_real : expr = App (RL.real_numeral_decl 0 1) []
let rle (a b:expr) : expr = App RL.real_le_decl [a; b]
let rlt (a b:expr) : expr = App RL.real_lt_decl [a; b]
let rgt (a b:expr) : expr = App RL.real_gt_decl [a; b]

let accepts (xs:list (bool & expr)) (cs:list A.coefficient) : bool =
  match A.prepare xs cs with Some ps -> P.accepts ps | None -> false

let lemma_real_controls ()
  : Lemma (accepts [(true, rle x_real y_real); (true, rle y_real x_real)] [(1, 1); (1, 1)] == false /\
           accepts [(true, rlt x_real y_real); (true, rle y_real x_real)] [(1, 1); (1, 1)] == true /\
           accepts [(true, rlt x_real y_real); (true, rle y_real x_real)] [(0, 1); (1, 1)] == false /\
           accepts [(true, rgt x_real zero_real); (true, rle x_real zero_real)] [(1, 1); (1, 1)] == true /\
           accepts [(true, rlt x_real y_real); (true, rle y_real x_real)] [(1, 2); (2, 4)] == true /\
           accepts [(true, rlt x_real y_real); (true, rle y_real x_real)] [(1, 2); (3, 7)] == false /\
           accepts [(true, rlt x_real y_real); (true, rle y_real x_real)] [(-1, 1); (1, 1)] == true /\
           accepts [(true, rlt x_real y_real); (false, rlt x_real y_real)] [(1, 1); (1, 1)] == true) =
  assert_norm (accepts [(true, rle x_real y_real); (true, rle y_real x_real)] [(1, 1); (1, 1)] == false);
  assert_norm (accepts [(true, rlt x_real y_real); (true, rle y_real x_real)] [(1, 1); (1, 1)] == true);
  assert_norm (accepts [(true, rlt x_real y_real); (true, rle y_real x_real)] [(0, 1); (1, 1)] == false);
  assert_norm (accepts [(true, rgt x_real zero_real); (true, rle x_real zero_real)] [(1, 1); (1, 1)] == true);
  assert_norm (accepts [(true, rlt x_real y_real); (true, rle y_real x_real)] [(1, 2); (2, 4)] == true);
  assert_norm (accepts [(true, rlt x_real y_real); (true, rle y_real x_real)] [(1, 2); (3, 7)] == false);
  assert_norm (accepts [(true, rlt x_real y_real); (true, rle y_real x_real)] [(-1, 1); (1, 1)] == true);
  assert_norm (accepts [(true, rlt x_real y_real); (false, rlt x_real y_real)] [(1, 1); (1, 1)] == true)

(* Captured Real leaf shapes (REPORT section 4 Real) and opposite mutants,
   decided by the executable real_equivalent. *)
let real_minus_one : expr = App (RL.real_numeral_decl (-1) 1) []
let real_plus (a b:expr) : expr = App RL.real_plus_decl [a; b]
let real_times (a b:expr) : expr = App RL.real_times_decl [a; b]
let rge (a b:expr) : expr = App RL.real_ge_decl [a; b]
let rnot (a:expr) : expr = App R.not_decl [a]
let int_zero : expr =
  App { decl_name = "0"; domain = []; range = A.int_s; interp = Some op_num_rational; int_params = [0; 1] } []

let lemma_real_rewrite_controls ()
  : Lemma (LIN.real_equivalent (rgt x_real y_real) (rnot (rle x_real y_real)) == true /\
           LIN.real_equivalent (rle x_real y_real)
             (rge (real_plus y_real (real_times real_minus_one x_real)) zero_real) == true /\
           LIN.real_equivalent (real_plus x_real y_real) (real_plus y_real x_real) == true /\
           LIN.real_equivalent (App RL.to_real_decl [int_zero]) zero_real == true /\
           LIN.real_equivalent (real_times x_real y_real) (real_times y_real x_real) == true /\
           LIN.real_equivalent (rgt x_real y_real) (rnot (rlt x_real y_real)) == false /\
           LIN.real_equivalent (real_plus x_real y_real) (real_plus x_real x_real) == false /\
           LIN.real_equivalent (rle x_real y_real)
             (rge (real_plus x_real (real_times real_minus_one y_real)) zero_real) == false) =
  assert_norm (LIN.real_equivalent (rgt x_real y_real) (rnot (rle x_real y_real)) == true);
  assert_norm (LIN.real_equivalent (rle x_real y_real)
                 (rge (real_plus y_real (real_times real_minus_one x_real)) zero_real) == true);
  assert_norm (LIN.real_equivalent (real_plus x_real y_real) (real_plus y_real x_real) == true);
  assert_norm (LIN.real_equivalent (App RL.to_real_decl [int_zero]) zero_real == true);
  assert_norm (LIN.real_equivalent (real_times x_real y_real) (real_times y_real x_real) == true);
  assert_norm (LIN.real_equivalent (rgt x_real y_real) (rnot (rlt x_real y_real)) == false);
  assert_norm (LIN.real_equivalent (real_plus x_real y_real) (real_plus x_real x_real) == false);
  assert_norm (LIN.real_equivalent (rle x_real y_real)
                 (rge (real_plus x_real (real_times real_minus_one y_real)) zero_real) == false)
