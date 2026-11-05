module Z3LpIntegerCutTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module A = Z3LinearArithmeticAst
module C = Z3LpIntegerCut
module G = Z3LpGomory

(* Closed instances of the integer rounding certificate, decided by normalization.
   Facts: 256 * a >= 1 and 256 * a <= 255. They hold over the reals (a = 1/2)
   but not over the integers: rounding gives a >= 1 and a <= 0. *)

let constant (s:sort) (name:string) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = [] } []

let num (s:sort) (n:int) : expr =
  App { decl_name = "numeral"; domain = []; range = s; interp = Some op_num_rational;
        int_params = [n; 1] } []

let arith (name:string) (tag:decl_kind) (s:sort) (args:list expr) : expr =
  App { decl_name = name; domain = FStar.List.Tot.map get_sort args; range = s;
        interp = Some tag; int_params = [] } args

let mul (s:sort) (args:list expr) : expr = arith "*" op_arith_mul s args

let compare (name:string) (tag:decl_kind) (a b:expr) : expr =
  App { decl_name = name; domain = [get_sort a; get_sort b]; range = bool_sort;
        interp = Some tag; int_params = [] } [a; b]

let ge (a b:expr) : expr = compare ">=" op_arith_ge a b
let le (a b:expr) : expr = compare "<=" op_arith_le a b

let int_s = A.int_s
let real_s = A.real_s
let a (s:sort) : expr = constant s "a"
let b (s:sort) : expr = constant s "b"

let scaled (s:sort) (n:int) : expr = mul s [num s n; a s]

let lower (s:sort) : expr = ge (scaled s 256) (num s 1)
let upper (s:sort) : expr = le (scaled s 256) (num s 255)
let facts (s:sort) : list expr = [lower s; upper s]

let w (n:int) (d:pos) : A.coefficient = (n, d)
let one : A.coefficient = w 1 1
let zero : A.coefficient = w 0 1

(* -a <= -1 is the rounded form of 256 * (-a) <= -1; a <= 0 of 256 * a <= 255. *)
let below (s:sort) (k:int) : expr = le (mul s [num s (-1); a s]) (num s k)
let above (s:sort) (k:int) : expr = le (a s) (num s k)

let certificate (s:sort) (k1 k2:int) : C.certificate = {
  C.steps = [ { C.bound = below s k1; C.weights = [one; zero; w 256 1] };
              { C.bound = above s k2; C.weights = [zero; one; zero; w 256 1] } ];
  C.refutation = [zero; zero; one; one] }

let accepted ()
  : Lemma (C.check (certificate int_s (-1) 0) false_expr (facts int_s) /\
           (* weights may be scaled by any positive rational *)
           C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [w 1 2; zero; w 128 1] };
                                 { C.bound = above int_s 0; C.weights = [zero; w 1 3; zero; w 256 3] } ];
                     C.refutation = [zero; zero; w 5 1; w 5 1] } false_expr (facts int_s)) =
  assert_norm (C.check (certificate int_s (-1) 0) false_expr (facts int_s));
  assert_norm (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [w 1 2; zero; w 128 1] };
                                     { C.bound = above int_s 0; C.weights = [zero; w 1 3; zero; w 256 3] } ];
                         C.refutation = [zero; zero; w 5 1; w 5 1] } false_expr (facts int_s))

(* A bound that rounds too far (-a <= -2, a <= -1) does not follow; a bound that is too weak
   (-a <= 0, a <= 1) is a consequence but leaves the system satisfiable. *)
let wrong_rounding ()
  : Lemma (not (C.check (certificate int_s (-2) 0) false_expr (facts int_s)) /\
           not (C.check (certificate int_s (-1) (-1)) false_expr (facts int_s)) /\
           not (C.check (certificate int_s (-1) 1) false_expr (facts int_s)) /\
           not (C.check (certificate int_s 0 0) false_expr (facts int_s))) =
  assert_norm (not (C.check (certificate int_s (-2) 0) false_expr (facts int_s)));
  assert_norm (not (C.check (certificate int_s (-1) (-1)) false_expr (facts int_s)));
  assert_norm (not (C.check (certificate int_s (-1) 1) false_expr (facts int_s)));
  assert_norm (not (C.check (certificate int_s 0 0) false_expr (facts int_s)))

(* The negated divisor, a zero divisor, a wrong direction, and weights that do not cancel. *)
let divisor_and_weights ()
  : Lemma (not (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [one; zero; zero] };
                                      { C.bound = above int_s 0; C.weights = [zero; one; zero; w 256 1] } ];
                          C.refutation = [zero; zero; one; one] } false_expr (facts int_s)) /\
           not (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [one; zero; w (-1) 1] };
                                      { C.bound = above int_s (-1); C.weights = [zero; one; zero; w (-256) 1] } ];
                          C.refutation = [zero; zero; one; one] } false_expr (facts int_s)) /\
           (* a bound with the wrong direction cannot be rescued by a negative divisor *)
           not (C.check { C.steps = [ { C.bound = above int_s (-1); C.weights = [one; zero; w (-256) 1] } ];
                          C.refutation = [one; zero; one] } false_expr (facts int_s)) /\
           (* non-integral weights that do not cancel the variable *)
           not (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [w 1 2; zero; w 127 1] };
                                      { C.bound = above int_s 0; C.weights = [zero; one; zero; w 256 1] } ];
                          C.refutation = [zero; zero; one; one] } false_expr (facts int_s))) =
  assert_norm (not (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [one; zero; zero] };
                                          { C.bound = above int_s 0; C.weights = [zero; one; zero; w 256 1] } ];
                              C.refutation = [zero; zero; one; one] } false_expr (facts int_s)));
  assert_norm (not (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [one; zero; w (-1) 1] };
                                          { C.bound = above int_s (-1); C.weights = [zero; one; zero; w (-256) 1] } ];
                              C.refutation = [zero; zero; one; one] } false_expr (facts int_s)));
  assert_norm (not (C.check { C.steps = [ { C.bound = above int_s (-1); C.weights = [one; zero; w (-256) 1] } ];
                              C.refutation = [one; zero; one] } false_expr (facts int_s)));
  assert_norm (not (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [w 1 2; zero; w 127 1] };
                                          { C.bound = above int_s 0; C.weights = [zero; one; zero; w 256 1] } ];
                              C.refutation = [zero; zero; one; one] } false_expr (facts int_s)))

(* Weights are bound to the exact accumulated list: a missing weight, an extra weight for the step itself or a
   later step, a dropped or swapped premise, and a conclusion other than false are all rejected. *)
let dependency_binding ()
  : Lemma (not (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [one; zero] };
                                      { C.bound = above int_s 0; C.weights = [zero; one; zero; w 256 1] } ];
                          C.refutation = [zero; zero; one; one] } false_expr (facts int_s)) /\
           not (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [one; zero; w 256 1; zero] };
                                      { C.bound = above int_s 0; C.weights = [zero; one; zero; w 256 1] } ];
                          C.refutation = [zero; zero; one; one] } false_expr (facts int_s)) /\
           not (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [one; zero; w 256 1] };
                                      { C.bound = above int_s 0; C.weights = [zero; one; zero; w 256 1] } ];
                          C.refutation = [zero; zero; one] } false_expr (facts int_s)) /\
           not (C.check (certificate int_s (-1) 0) false_expr [upper int_s; lower int_s]) /\
           not (C.check (certificate int_s (-1) 0) false_expr [lower int_s]) /\
           not (C.check (certificate int_s (-1) 0) (le (a int_s) (num int_s 5)) (facts int_s)) /\
           (* a refutation using the second step before it exists *)
           not (C.check { C.steps = [ { C.bound = above int_s 0; C.weights = [zero; one; zero; w 256 1] };
                                      { C.bound = below int_s (-1); C.weights = [one; zero; w 256 1] } ];
                          C.refutation = [zero; zero; one; one] } false_expr (facts int_s))) =
  assert_norm (not (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [one; zero] };
                                          { C.bound = above int_s 0; C.weights = [zero; one; zero; w 256 1] } ];
                              C.refutation = [zero; zero; one; one] } false_expr (facts int_s)));
  assert_norm (not (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [one; zero; w 256 1; zero] };
                                          { C.bound = above int_s 0; C.weights = [zero; one; zero; w 256 1] } ];
                              C.refutation = [zero; zero; one; one] } false_expr (facts int_s)));
  assert_norm (not (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [one; zero; w 256 1] };
                                          { C.bound = above int_s 0; C.weights = [zero; one; zero; w 256 1] } ];
                              C.refutation = [zero; zero; one] } false_expr (facts int_s)));
  assert_norm (not (C.check (certificate int_s (-1) 0) false_expr [upper int_s; lower int_s]));
  assert_norm (not (C.check (certificate int_s (-1) 0) false_expr [lower int_s]));
  assert_norm (not (C.check (certificate int_s (-1) 0) (le (a int_s) (num int_s 5)) (facts int_s)));
  assert_norm (not (C.check { C.steps = [ { C.bound = above int_s 0; C.weights = [zero; one; zero; w 256 1] };
                                          { C.bound = below int_s (-1); C.weights = [one; zero; w 256 1] } ];
                              C.refutation = [zero; zero; one; one] } false_expr (facts int_s)))

(* Rounding needs integer terms: the same certificate over Real constants is rejected, as is a satisfiable
   integer system (a >= 0 and a <= 255 / 256 have the model a = 0). *)
let sorts_and_models ()
  : Lemma (not (C.check (certificate real_s (-1) 0) false_expr (facts real_s)) /\
           not (C.check (certificate int_s (-1) 0) false_expr
                  [ge (scaled int_s 256) (num int_s 0); upper int_s]) /\
           not (C.check (certificate int_s (-1) 0) false_expr
                  [lower int_s; le (scaled int_s 256) (num int_s 256)])) =
  assert_norm (not (C.check (certificate real_s (-1) 0) false_expr (facts real_s)));
  assert_norm (not (C.check (certificate int_s (-1) 0) false_expr
                      [ge (scaled int_s 256) (num int_s 0); upper int_s]));
  assert_norm (not (C.check (certificate int_s (-1) 0) false_expr
                      [lower int_s; le (scaled int_s 256) (num int_s 256)]))

(* The empty certificate is a plain Farkas refutation: it holds when the rational relaxation is empty and
   fails when it is not. Real-sorted refutations are unaffected by the integer rounding restrictions. *)
let plain_farkas ()
  : Lemma (C.check { C.steps = []; C.refutation = [one; one] } false_expr
             [ge (a int_s) (num int_s 1); le (a int_s) (num int_s 0)] /\
           C.check { C.steps = []; C.refutation = [one; one] } false_expr
             [ge (a real_s) (num real_s 1); le (a real_s) (num real_s 0)] /\
           C.check { C.steps = []; C.refutation = [w 3 2; w 3 2] } false_expr
             [ge (a real_s) (num real_s 1); le (a real_s) (num real_s 0)] /\
           not (C.check { C.steps = []; C.refutation = [one; one] } false_expr (facts int_s)) /\
           not (C.check { C.steps = []; C.refutation = [one; one] } false_expr (facts real_s))) =
  assert_norm (C.check { C.steps = []; C.refutation = [one; one] } false_expr
                 [ge (a int_s) (num int_s 1); le (a int_s) (num int_s 0)]);
  assert_norm (C.check { C.steps = []; C.refutation = [one; one] } false_expr
                 [ge (a real_s) (num real_s 1); le (a real_s) (num real_s 0)]);
  assert_norm (C.check { C.steps = []; C.refutation = [w 3 2; w 3 2] } false_expr
                 [ge (a real_s) (num real_s 1); le (a real_s) (num real_s 0)]);
  assert_norm (not (C.check { C.steps = []; C.refutation = [one; one] } false_expr (facts int_s)));
  assert_norm (not (C.check { C.steps = []; C.refutation = [one; one] } false_expr (facts real_s)))

(* A valid permutation of the premises, with the weights permuted accordingly, and a valid reordering of
   the independent steps remain accepted. *)
let permutations ()
  : Lemma (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [zero; one; w 256 1] };
                                 { C.bound = above int_s 0; C.weights = [one; zero; zero; w 256 1] } ];
                     C.refutation = [zero; zero; one; one] } false_expr [upper int_s; lower int_s] /\
           C.check { C.steps = [ { C.bound = above int_s 0; C.weights = [zero; one; w 256 1] };
                                 { C.bound = below int_s (-1); C.weights = [one; zero; zero; w 256 1] } ];
                     C.refutation = [zero; zero; one; one] } false_expr (facts int_s)) =
  assert_norm (C.check { C.steps = [ { C.bound = below int_s (-1); C.weights = [zero; one; w 256 1] };
                                     { C.bound = above int_s 0; C.weights = [one; zero; zero; w 256 1] } ];
                         C.refutation = [zero; zero; one; one] } false_expr [upper int_s; lower int_s]);
  assert_norm (C.check { C.steps = [ { C.bound = above int_s 0; C.weights = [zero; one; w 256 1] };
                                     { C.bound = below int_s (-1); C.weights = [one; zero; zero; w 256 1] } ];
                         C.refutation = [zero; zero; one; one] } false_expr (facts int_s))
