(* Regression tests for replaying recorded finite-field ideal certificates
   (`Z3FiniteFieldPac`). The positive certificates are the producer's own
   `ff-pac` parameters, flattened as the native bridge does, for the
   refutation `x*y = 1, x*(1+y) = 2+x` over the 31-bit prime 2^31-1 (where
   exhaustive evaluation is out of reach), over 2^127-1, and over Z/4Z (the
   checker uses only ring laws). The negative cases mutate one field each:
   a coefficient, the conclusion, the modulus, the premises, the support,
   an input index, a node reference, or the root; and a certificate using
   the inverse witness of a disequality, which needs primality, stays
   unchecked. *)
module Z3FiniteFieldPacTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module FF = Z3FiniteFieldLemma
module FP = Z3FiniteFieldPac
module U = Z3UnifiedProof

let num (p n:int) : expr =
  App { decl_name = "ff"; domain = []; range = FF.ff_sort p;
        interp = Some FF.op_ff_num; int_params = [p; n] } []

let const (p:int) (name:string) : expr =
  App { decl_name = name; domain = []; range = FF.ff_sort p;
        interp = None; int_params = [] } []

let field (p:int) (name:string) (k:decl_kind) (args:list expr) : expr =
  App { decl_name = name; domain = FF.ff_domain p args; range = FF.ff_sort p;
        interp = Some k; int_params = [p] } args

let add (p:int) (args:list expr) : expr = field p "ff.add" FF.op_ff_add args
let mul (p:int) (args:list expr) : expr = field p "ff.mul" FF.op_ff_mul args
let eq (a b:expr) : expr = mk_eq_expr a b

let disj (args:list expr) : expr =
  App (Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Disjunction args) args

(* `(= (ff.mul x y) 1)` and `(= (ff.mul x (ff.add 1 y)) (ff.add 2 x))`. *)
let premise0 (p:int) : expr = eq (mul p [const p "x"; const p "y"]) (num p 1)
let premise1 (p:int) : expr =
  eq (mul p [const p "x"; add p [num p 1; const p "y"]]) (add p [num p 2; const p "x"])

let clause (p:int) : expr = disj [mk_not_expr (premise0 p); mk_not_expr (premise1 p)]

(* The producer's table: y = v0, x = v1, v2 = x*y (eq 0), v2 - 1 (eq 1),
   v3 = 1+y (eq 2), v4 = x*v3 (eq 3), v5 = 2+x (eq 4), v4 - v5 (eq 5). The
   certificate is -(eq4 + eq5 - eq3 - x*eq2 - eq1 + eq0) = 1. *)
let later_nodes (m:expr) : list FP.pac_node = [
  FP.PacInput 5; FP.PacInput 3; FP.PacMul 2 m [];
  FP.PacAdd 1 3; FP.PacAdd 0 4; FP.PacInput 2; FP.PacMul 6 m [1];
  FP.PacAdd 5 7; FP.PacInput 1; FP.PacInput 0; FP.PacMul 10 m [];
  FP.PacAdd 9 11; FP.PacMul 12 m []; FP.PacAdd 8 13; FP.PacMul 14 m []]

let nodes (p:int) (m:expr) : list FP.pac_node = FP.PacInput 4 :: later_nodes m

let certificate (p:int) : FP.certificate = {
  FP.pac_premises = [premise0 p; premise1 p];
  FP.pac_nodes = nodes p (num p (p - 1));
  FP.pac_root = 15;
  FP.pac_support = [0; 1];
}

let p31 : int = 2147483647
let p127 : int = 170141183460469231731687303715884105727

let test_unit_ideal_certificates () : Lemma (
  FP.check (certificate p31) (clause p31) /\
  FP.check (certificate p127) (clause p127) /\
  FP.check (certificate 4) (clause 4)) =
  assert_norm (
    FP.check (certificate p31) (clause p31) /\
    FP.check (certificate p127) (clause p127) /\
    FP.check (certificate 4) (clause 4))

(* The kernel dispatch: the exhaustive check is out of budget (p^2
   assignments), the replay succeeds. Rejections through the kernel's other
   theory-lemma checks are exercised natively by the bridge tests. *)
let test_unit_ideal_is_checked_by_the_kernel () : Lemma (
  not (FF.exhaustive_clause (clause p31)) /\
  U.pac_lemma (U.FiniteFieldPac (certificate p31)) (clause p31) /\
  not (U.pac_lemma (U.Unverified "th-lemma") (clause p31))) =
  assert_norm (
    not (FF.exhaustive_clause (clause p31)) /\
    U.pac_lemma (U.FiniteFieldPac (certificate p31)) (clause p31) /\
    not (U.pac_lemma (U.Unverified "th-lemma") (clause p31)))

let with_nodes (c:FP.certificate) (ns:list FP.pac_node) : FP.certificate = { c with FP.pac_nodes = ns }

(* A changed coefficient, or a coefficient of another field. *)
let test_corrupted_coefficients () : Lemma (
  not (FP.check (with_nodes (certificate p31) (nodes p31 (num p31 2))) (clause p31)) /\
  not (FP.check (with_nodes (certificate p31) (nodes p31 (num 2147483659 2147483646))) (clause p31)) /\
  not (FP.check (with_nodes (certificate p31) (nodes p31 (const p31 "x"))) (clause p31))) =
  assert_norm (
    not (FP.check (with_nodes (certificate p31) (nodes p31 (num p31 2))) (clause p31)) /\
    not (FP.check (with_nodes (certificate p31) (nodes p31 (num 2147483659 2147483646))) (clause p31)) /\
    not (FP.check (with_nodes (certificate p31) (nodes p31 (const p31 "x"))) (clause p31)))

(* The conclusion must contain the negation of every used premise. *)
let test_false_conclusions () : Lemma (
  not (FP.check (certificate p31) (disj [mk_not_expr (premise0 p31)])) /\
  not (FP.check (certificate p31) (disj [premise0 p31; mk_not_expr (premise1 p31)])) /\
  not (FP.check (certificate p31) (mk_not_expr (premise1 p31))) /\
  not (FP.check (certificate p31) false_expr)) =
  assert_norm (
    not (FP.check (certificate p31) (disj [mk_not_expr (premise0 p31)])) /\
    not (FP.check (certificate p31) (disj [premise0 p31; mk_not_expr (premise1 p31)])) /\
    not (FP.check (certificate p31) (mk_not_expr (premise1 p31))) /\
    not (FP.check (certificate p31) false_expr))

let with_premises (c:FP.certificate) (ps:list expr) : FP.certificate = { c with FP.pac_premises = ps }
let with_support (c:FP.certificate) (s:list int) : FP.certificate = { c with FP.pac_support = s }

(* Premises are re-encoded, never trusted: a missing, reordered, extra
   leading, or negated premise changes the input table. *)
let test_premise_table () : Lemma (
  not (FP.check (with_premises (certificate p31) [premise0 p31]) (clause p31)) /\
  not (FP.check (with_premises (certificate p31) [premise1 p31; premise0 p31]) (clause p31)) /\
  not (FP.check (with_premises (certificate p31) [eq (const p31 "z") (num p31 0); premise0 p31; premise1 p31])
                (clause p31)) /\
  not (FP.check (with_premises (certificate p31) [premise0 p31; mk_not_expr (premise1 p31)])
                (disj [mk_not_expr (premise0 p31); premise1 p31])) /\
  not (FP.check (with_premises (certificate p31) []) (clause p31))) =
  assert_norm (
    not (FP.check (with_premises (certificate p31) [premise0 p31]) (clause p31)) /\
    not (FP.check (with_premises (certificate p31) [premise1 p31; premise0 p31]) (clause p31)) /\
    not (FP.check (with_premises (certificate p31) [eq (const p31 "z") (num p31 0); premise0 p31; premise1 p31])
                  (clause p31)) /\
    not (FP.check (with_premises (certificate p31) [premise0 p31; mk_not_expr (premise1 p31)])
                  (disj [mk_not_expr (premise0 p31); premise1 p31])) /\
    not (FP.check (with_premises (certificate p31) []) (clause p31)))

(* The support must be strictly increasing, in range and exactly the used premises. *)
let test_support () : Lemma (
  FP.check (with_premises (certificate p31) [premise0 p31; premise1 p31; eq (const p31 "z") (num p31 0)])
           (clause p31) /\
  not (FP.check (with_support (certificate p31) [0]) (clause p31)) /\
  not (FP.check (with_support (certificate p31) [1; 0]) (clause p31)) /\
  not (FP.check (with_support (certificate p31) [0; 0; 1]) (clause p31)) /\
  not (FP.check (with_support (certificate p31) [0; 1; 2]) (clause p31)) /\
  not (FP.check (with_support (certificate p31) [-1; 0; 1]) (clause p31)) /\
  not (FP.check (with_support (with_premises (certificate p31)
                  [premise0 p31; premise1 p31; eq (const p31 "z") (num p31 0)]) [0; 1; 2])
                (disj [mk_not_expr (premise0 p31); mk_not_expr (premise1 p31);
                       mk_not_expr (eq (const p31 "z") (num p31 0))]))) =
  assert_norm (
    FP.check (with_premises (certificate p31) [premise0 p31; premise1 p31; eq (const p31 "z") (num p31 0)])
             (clause p31) /\
    not (FP.check (with_support (certificate p31) [0]) (clause p31)) /\
    not (FP.check (with_support (certificate p31) [1; 0]) (clause p31)) /\
    not (FP.check (with_support (certificate p31) [0; 0; 1]) (clause p31)) /\
    not (FP.check (with_support (certificate p31) [0; 1; 2]) (clause p31)) /\
    not (FP.check (with_support (certificate p31) [-1; 0; 1]) (clause p31)) /\
    not (FP.check (with_support (with_premises (certificate p31)
                    [premise0 p31; premise1 p31; eq (const p31 "z") (num p31 0)]) [0; 1; 2])
                  (disj [mk_not_expr (premise0 p31); mk_not_expr (premise1 p31);
                         mk_not_expr (eq (const p31 "z") (num p31 0))])))

let m31 : expr = num p31 (p31 - 1)

(* Input indices name the table only (there are no Fermat equations), node
   references must be strictly earlier, factors sorted variables, and the
   root the constant 1. *)
let test_references () : Lemma (
  not (FP.check (with_nodes (certificate p31) (FP.PacInput 6 :: later_nodes m31)) (clause p31)) /\
  not (FP.check (with_nodes (certificate p31) (FP.PacInput (-1) :: later_nodes m31)) (clause p31)) /\
  not (FP.check (with_nodes (certificate p31) [FP.PacInput 4; FP.PacAdd 0 2; FP.PacInput 5]) (clause p31)) /\
  not (FP.check (with_nodes (certificate p31) [FP.PacInput 4; FP.PacAdd 1 1]) (clause p31)) /\
  not (FP.check (with_nodes (certificate p31) [FP.PacInput 4; FP.PacMul 1 m31 []]) (clause p31)) /\
  not (FP.check (with_nodes (certificate p31) [FP.PacInput 4; FP.PacAdd (-1) 0]) (clause p31)) /\
  not (FP.check (with_nodes (certificate p31) [FP.PacInput 2; FP.PacMul 0 m31 [6]]) (clause p31)) /\
  not (FP.check (with_nodes (certificate p31) [FP.PacInput 2; FP.PacMul 0 m31 [1; 0]]) (clause p31)) /\
  not (FP.check ({ certificate p31 with FP.pac_root = 14 }) (clause p31)) /\
  not (FP.check ({ certificate p31 with FP.pac_root = 16 }) (clause p31)) /\
  not (FP.check ({ certificate p31 with FP.pac_root = -1 }) (clause p31))) =
  assert_norm (
    not (FP.check (with_nodes (certificate p31) (FP.PacInput 6 :: later_nodes m31)) (clause p31)) /\
    not (FP.check (with_nodes (certificate p31) (FP.PacInput (-1) :: later_nodes m31)) (clause p31)) /\
    not (FP.check (with_nodes (certificate p31) [FP.PacInput 4; FP.PacAdd 0 2; FP.PacInput 5]) (clause p31)) /\
    not (FP.check (with_nodes (certificate p31) [FP.PacInput 4; FP.PacAdd 1 1]) (clause p31)) /\
    not (FP.check (with_nodes (certificate p31) [FP.PacInput 4; FP.PacMul 1 m31 []]) (clause p31)) /\
    not (FP.check (with_nodes (certificate p31) [FP.PacInput 4; FP.PacAdd (-1) 0]) (clause p31)) /\
    not (FP.check (with_nodes (certificate p31) [FP.PacInput 2; FP.PacMul 0 m31 [6]]) (clause p31)) /\
    not (FP.check (with_nodes (certificate p31) [FP.PacInput 2; FP.PacMul 0 m31 [1; 0]]) (clause p31)) /\
    not (FP.check ({ certificate p31 with FP.pac_root = 14 }) (clause p31)) /\
    not (FP.check ({ certificate p31 with FP.pac_root = 16 }) (clause p31)) /\
    not (FP.check ({ certificate p31 with FP.pac_root = -1 }) (clause p31)))

(* `x*x = 0` and `x != 0`: the producer's certificate uses the inverse
   witness w*x - 1 (input 2) of the disequality. That needs a field; modulo 4
   the premises hold for x = 2. Both stay unchecked. *)
let square (p:int) : expr = eq (num p 0) (mul p [const p "x"; const p "x"])
let nonzero (p:int) : expr = mk_not_expr (eq (const p "x") (num p 0))

let rabinowitsch (p:int) : FP.certificate = {
  FP.pac_premises = [square p; nonzero p];
  FP.pac_nodes = [
    FP.PacInput 0; FP.PacInput 1; FP.PacAdd 0 1; FP.PacMul 2 (num p (p - 1)) [];
    FP.PacMul 3 (num p 1) [2]; FP.PacInput 2; FP.PacMul 5 (num p 1) [0];
    FP.PacMul 6 (num p (p - 1)) []; FP.PacAdd 4 7; FP.PacMul 8 (num p 1) [2];
    FP.PacInput 2; FP.PacMul 10 (num p (p - 1)) []; FP.PacAdd 9 11];
  FP.pac_root = 12;
  FP.pac_support = [0; 1];
}

let rabinowitsch_clause (p:int) : expr = disj [mk_not_expr (square p); eq (const p "x") (num p 0)]

let test_inverse_witness_is_not_used () : Lemma (
  not (FP.check (rabinowitsch p31) (rabinowitsch_clause p31)) /\
  not (FP.check (rabinowitsch 4) (rabinowitsch_clause 4))) =
  assert_norm (
    not (FP.check (rabinowitsch p31) (rabinowitsch_clause p31)) /\
    not (FP.check (rabinowitsch 4) (rabinowitsch_clause 4)))

(* The replay bounds; exceeding them is exercised natively by the bridge tests. *)
let test_bounds () : Lemma (
  FP.max_nodes == 100000 /\ FP.max_poly_size == 16384 /\ FP.max_work == 4000000) =
  assert_norm (FP.max_nodes == 100000 /\ FP.max_poly_size == 16384 /\ FP.max_work == 4000000)
