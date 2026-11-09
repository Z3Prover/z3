module Z3SortedRealProductTests

open Z3AstTheory
open Z3ValueTheory
module A = Z3LinearArithmeticAst
module L = FStar.List.Tot
module P = Z3SortedRealProduct
module R = Z3ResolutionProofTheory
module RL = Z3SortedReal
module S = Z3DatatypeSignature

let schema : S.checked_schema = { S.sorts = []; S.cases = [] }
let constant (name:string) : expr =
  App { decl_name = name; domain = []; range = A.real_s; interp = None; int_params = [] } []
let x = constant "x"
let y = constant "y"
let z = constant "z"
let mul (a b:expr) : expr = App RL.real_times_decl [a; b]
let le (a b:expr) : expr = App RL.real_le_decl [a; b]
let ge (a b:expr) : expr = App RL.real_ge_decl [a; b]
let neg (a:expr) : expr = R.mk_not_expr a

let direct : list expr = [P.positive x; P.positive y; le (mul x y) P.zero]
let indirect : list expr = [
  ge z P.zero;
  neg (ge (App RL.real_plus_decl [z; mul (App (RL.real_numeral_decl (-1) 1) []) x]) P.zero);
  neg (le y P.zero);
  le (mul x y) P.zero
]

let positive_products () : Lemma (P.check schema direct /\ P.check schema indirect) =
  assert_norm (P.check schema direct);
  assert_norm (P.check schema indirect)

let mutations : list (list expr) = [
  [ge x P.zero; P.positive y; le (mul x y) P.zero];
  [P.positive x; ge y P.zero; le (mul x y) P.zero];
  [P.positive x; P.positive y; ge (mul x y) P.zero];
  [P.positive x; P.positive y; le (mul x z) P.zero];
  [P.positive x; P.positive y;
   le (App ({ RL.real_times_decl with interp = None }) [x; y]) P.zero]
]

let feasible_mutants () : Lemma (L.for_all (fun facts -> not (P.check schema facts)) mutations) =
  assert_norm (L.for_all (fun facts -> not (P.check schema facts)) mutations)

let rec repeat (n:nat) (e:expr) : Tot (list expr) (decreases n) =
  if n = 0 then [] else e :: repeat (n - 1) e

let literal_budget () : Lemma (not (P.check schema (repeat 31 (P.positive x)))) =
  assert_norm (not (P.check schema (repeat 31 (P.positive x))))
