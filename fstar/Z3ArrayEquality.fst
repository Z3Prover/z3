module Z3ArrayEquality

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open FStar.Real
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module A = Z3ArrayLemma
module T = Z3ArrayTheory
module LR = Z3LambdaRewrite
module D = Z3Definitions
module QP = Z3QuantifierPull
module LA = Z3LinearArithmeticAst
module LE = Z3LinearArithmeticEmbed
module AR = Z3ArithmeticRewrite

let int_array : sort = ArraySort [LA.int_s] LA.int_s

(* Only genuine, one-dimensional Int arrays have the infinite domain used
   below. In particular, do not generalize this test to scalar_sort. *)
let rec default_term (fuel:nat) (e:expr)
  : Tot (option expr) (decreases fuel) =
  if fuel = 0 || get_sort e <> int_array then None
  else match e with
  | App f [v] -> if LR.const_array f v then Some v else None
  | App f [a; k; v] ->
    if A.store_app f a k v then default_term (fuel - 1) a else None
  | _ -> None

let unequal_defaults (e:expr) : bool =
  match A.equality_parts e with
  | Some (a, b) ->
    (match default_term 64 a, default_term 64 b with
     | Some x, Some y -> AR.equivalent (mk_eq_expr x y) false_expr
     | _, _ -> false)
  | None -> false

let rec lemma_default_sort (fuel:nat) (e d:expr)
  : Lemma (requires default_term fuel e == Some d)
          (ensures get_sort d == LA.int_s)
          (decreases fuel) =
  if fuel = 0 then ()
  else match e with
  | App _ [_] -> ()
  | App _ [a; _; _] -> lemma_default_sort (fuel - 1) a d
  | _ -> ()

let model (i:interpretation value) : prop =
  A.array_model i /\ LR.lambda_model i /\ quant_extensional i /\
  Z3BooleanRewrite.boolean_rewrite_model i /\
  (exists (nu:value -> FStar.Real.real). LE.numeric_model i nu)

(* These expressions are proof witnesses, not new trusted operators. *)
let integer (n:int) : expr =
  App { decl_name = "array-index"; domain = []; range = LA.int_s;
        interp = Some op_num_rational; int_params = [n; 1] } []

let read_decl : func_decl =
  { decl_name = "select"; domain = [int_array; LA.int_s]; range = LA.int_s;
    interp = Some op_select; int_params = [] }

let lemma_integer (i:interpretation value) (nu:value -> FStar.Real.real)
                  (rho:env value) (n:int)
  : Lemma (requires LE.numeric_model i nu)
          (ensures eval i (integer n) rho == VInt n) =
  assert (LE.numeric_operators i nu);
  assert (LA.numeral (integer n) == Some (n, 1));
  LE.lemma_linearize 1 (integer n) (Z3LinearArithmeticTheory.constant n 1) i nu rho;
  assert (nu (eval i (integer n) rho) == of_int n);
  match eval i (integer n) rho with
  | VInt _ -> ()
  | _ -> ()

(* Derive constant-array reads from the existing lambda/select contracts.
   No assumption about array equality or this rewrite is introduced. *)
let lemma_const_read (i:interpretation value) (nu:value -> FStar.Real.real)
                     (rho:env value) (f:func_decl) (v:expr) (k:int)
  : Lemma (requires A.array_model i /\ LR.lambda_model i /\ quant_extensional i /\
                    LE.numeric_model i nu /\ LR.const_array f v /\ f.range == int_array)
          (ensures (match eval i (App f [v]) rho, eval i v rho with
                    | VArr av, VInt x -> T.select av k == x
                    | _, _ -> False)) =
  let c = App f [v] in
  let body = D.lift 1 0 v in
  let lam = Quantifier Lambda_k [LA.int_s] int_array body in
  let index = integer k in
  LR.lemma_lambda_view i rho c [LA.int_s] body;
  lemma_integer i nu rho k;
  assert (LR.select_decl read_decl lam [index]);
  assert (eval i (App read_decl [lam; index]) rho ==
          eval i body (shift [VInt k] rho));
  QP.lemma_lift_under i v rho [VInt k];
  assert (A.select_parts (App read_decl [c; index]) == Some (c, index));
  A.lemma_select_parts i rho (App read_decl [c; index]) c index;
  match eval i c rho, eval i v rho with
  | VArr _, VInt _ -> ()
  | _, _ -> ()

(* A semantic bound is used only in the proof. Every finite chain has an
   untouched integer above it, even with symbolic or repeated indices. *)
let rec upper_bound (i:interpretation value) (rho:env value) (e:expr)
  : GTot int (decreases e) =
  match e with
  | App _ [a; k; _] ->
    let b = upper_bound i rho a in
    (match eval i k rho with VInt n -> if n >= b then n + 1 else b | _ -> b)
  | _ -> 0

let rec lemma_default_read (fuel:nat) (i:interpretation value)
                           (nu:value -> FStar.Real.real) (rho:env value)
                           (e d:expr) (k:int)
  : Lemma (requires A.array_model i /\ LR.lambda_model i /\ quant_extensional i /\
                    LE.numeric_model i nu /\ default_term fuel e == Some d /\
                    k >= upper_bound i rho e)
          (ensures (match eval i e rho, eval i d rho with
                    | VArr av, VInt x -> T.select av k == x
                    | _, _ -> False))
          (decreases fuel) =
  if fuel = 0 then ()
  else match e with
  | App f [v] -> lemma_const_read i nu rho f v k
  | App f [a; index; v] ->
    A.lemma_store_parts i rho e a index v;
    lemma_default_read (fuel - 1) i nu rho a d k;
    (match eval i a rho, eval i index rho, eval i v rho with
     | VArr av, VInt n, VInt x -> T.lemma_select_store_diff av n k x
     | _, _, _ -> ())
  | _ -> ()

let lemma_unequal_defaults_numeric (i:interpretation value)
                                  (nu:value -> FStar.Real.real)
                                  (rho:env value) (e:expr)
  : Lemma (requires model i /\ LE.numeric_model i nu /\ unequal_defaults e)
          (ensures eval i e rho == eval i false_expr rho) =
  match A.equality_parts e with
  | Some (a, b) ->
    let x = Some?.v (default_term 64 a) in
    let y = Some?.v (default_term 64 b) in
    lemma_default_sort 64 a x;
    lemma_default_sort 64 b y;
    let ab = upper_bound i rho a in
    let bb = upper_bound i rho b in
    let k = if ab >= bb then ab else bb in
    lemma_default_read 64 i nu rho a x k;
    lemma_default_read 64 i nu rho b y k;
    AR.lemma_equivalent_with_numeric_model (mk_eq_expr x y) false_expr i rho;
    A.lemma_equality_parts i rho (mk_eq_expr x y) x y;
    A.lemma_equality_parts i rho e a b;
    (match eval i a rho, eval i b rho, eval i e rho with
    | VArr _, VArr _, VBool _ -> ()
    | _, _, _ -> ())
  | None -> ()

let lemma_unequal_defaults (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires model i /\ unequal_defaults e)
          (ensures eval i e rho == eval i false_expr rho) =
  let aux (nu:value -> FStar.Real.real)
    : Lemma (requires LE.numeric_model i nu)
            (ensures eval i e rho == eval i false_expr rho)
    = lemma_unequal_defaults_numeric i nu rho e in
  FStar.Classical.exists_elim (eval i e rho == eval i false_expr rho)
    #(value -> FStar.Real.real) #(fun nu -> LE.numeric_model i nu) ()
    (fun nu -> aux nu)
