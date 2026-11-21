module Z3LinearArithmeticEmbed

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open FStar.Real
open FStar.List.Tot
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
module A = Z3LinearArithmeticAst
module P = Z3LinearArithmeticTheory
module Numeric = Z3PolynomialSemantics

let numeric_sum = Numeric.numeric_sum
let numeric_product = Numeric.numeric_product
let numeric_subtract = Numeric.numeric_subtract
let numeric_relation = Numeric.numeric_relation

(* Only the standard interpretation of typed arithmetic operators is assumed;
   no certificate, polynomial, or linearization occurs in this contract. *)
let numeric_operators (i:interpretation value) (nu:value -> real) : prop =
  (forall (n:int). nu (VInt n) == of_int n) /\
  (forall (e:expr) (rho:env value) (n:int) (d:pos).
    A.numeral e == Some (n, d) ==>
    of_int d *. nu (eval i e rho) == of_int n) /\
  (forall (f:func_decl) (args:list expr) (rho:env value) (op:A.operation).
    A.operation_of f args == Some op ==>
    (let xs = map nu (eval_args i args rho) in
     let v = nu (eval i (App f args) rho) in
     match op with
     | A.Add -> v == numeric_sum xs
     | A.Mul -> v == numeric_product xs
     | A.Sub -> v == numeric_subtract xs
     | A.ToReal -> (match xs with [x] -> v == x | _ -> False)
     | A.Div -> (match xs with [x; y] -> ~(y == 0.0R) ==> v *. y == x | _ -> False))) /\
  (forall (e a b:expr) (rho:env value) (r:A.relation).
    A.comparison e == Some (r, a, b) /\ r <> A.Eq ==>
    (lit_true i rho e <==> numeric_relation r (nu (eval i a rho)) (nu (eval i b rho))))

(* The value type has no real constructor. Real term equality additionally
   needs reflection from the numeric projection, not just operator laws. *)
let numeric_model (i:interpretation value) (nu:value -> real) : prop =
  numeric_operators i nu /\
  (forall (e:expr) (rho:env value).
    get_sort e == A.int_s ==> VInt? (eval i e rho)) /\
  (forall (a b:expr) (rho:env value).
    get_sort a == A.real_s /\ get_sort b == A.real_s /\
    nu (eval i a rho) == nu (eval i b rho) ==>
    eval i a rho == eval i b rho)

let lemma_add_application (f:func_decl) (args:list expr)
                          (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires numeric_operators i nu /\ A.operation_of f args == Some A.Add)
          (ensures nu (eval i (App f args) rho) ==
                   numeric_sum (map nu (eval_args i args rho))) = ()

let lemma_mul_application (f:func_decl) (args:list expr)
                          (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires numeric_operators i nu /\ A.operation_of f args == Some A.Mul)
          (ensures nu (eval i (App f args) rho) ==
                   numeric_product (map nu (eval_args i args rho))) = ()

let valuation (i:interpretation value) (nu:value -> real) (rho:env value) : expr -> real =
  fun e -> nu (eval i e rho)

let denotes = Numeric.denotes
let denotations = Numeric.denotations
let lemma_scaled_sum = Numeric.lemma_scaled_sum
let lemma_scaled_product = Numeric.lemma_scaled_product
let lemma_product_value = Numeric.lemma_product_value
let lemma_scaled_quotient = Numeric.lemma_scaled_quotient
let lemma_negative_quotient = Numeric.lemma_negative_quotient
let lemma_scaled_value = Numeric.lemma_scaled_value
let lemma_denotes_intro = Numeric.lemma_denotes_intro
let lemma_denotes_add = Numeric.lemma_denotes_add
let lemma_sum = Numeric.lemma_sum
let lemma_denotes_multiply = Numeric.lemma_denotes_multiply
let lemma_product = Numeric.lemma_product
let lemma_denotes_negative = Numeric.lemma_denotes_negative
let lemma_subtract = Numeric.lemma_subtract
let lemma_denotes_scale = Numeric.lemma_denotes_scale
let lemma_divide = Numeric.lemma_divide

private let lemma_div_application (f:func_decl) (args:list expr) (x y:real)
                                  (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires numeric_operators i nu /\ A.operation_of f args == Some A.Div /\
                    map nu (eval_args i args rho) == [x; y])
          (ensures ~(y == 0.0R) ==> nu (eval i (App f args) rho) *. y == x) = ()

private let lemma_linearize_divide (f:func_decl) (args:list expr) (e:expr)
                                   (a b q p:A.poly) (x y:real)
                                   (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires numeric_operators i nu /\ e == App f args /\
                    A.operation_of f args == Some A.Div /\
                    map nu (eval_args i args rho) == [x; y] /\
                    denotations [a; b] [x; y] (valuation i nu rho) /\
                    A.divide a b == Some q /\ A.combine A.Div [a; b] e == Some p)
          (ensures denotes p (nu (eval i e rho)) (valuation i nu rho)) =
  lemma_div_application f args x y i nu rho;
  lemma_divide a b q x y (nu (eval i e rho)) (valuation i nu rho)

#push-options "--fuel 4"

let rec lemma_linearize (fuel:nat) (e:expr) (p:A.poly)
                         (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires numeric_operators i nu /\ A.linearize fuel e == Some p)
          (ensures denotes p (nu (eval i e rho)) (valuation i nu rho))
          (decreases %[fuel; 0]) =
  assert (fuel > 0);
  match A.numeral e with
  | Some _ -> ()
  | None ->
    (match e with
     | App f args ->
       (match A.operation_of f args with
        | None -> ()
        | Some op ->
          A.lemma_linearize_application fuel f args op;
          lemma_linearize_args (fuel - 1) args i nu rho;
          let ps = Some?.v (A.linearize_args (fuel - 1) args) in
          let xs = map nu (eval_args i args rho) in
          let r = valuation i nu rho in
          assert (A.combine op ps e == Some p);
          (match op, ps with
           | A.Add, _ -> lemma_sum ps xs r
           | A.Mul, _ ->
             (match P.product ps with
              | Some q -> lemma_product ps xs q r
              | None -> ())
           | A.Sub, _ -> lemma_subtract ps xs p r
           | A.Div, [a; b] ->
             (match A.divide a b with
              | Some q ->
                (match xs with
                 | [x; y] -> lemma_linearize_divide f args e a b q p x y i nu rho
                 | _ -> ())
              | None -> ())
           | A.ToReal, [_] -> ()
           | _, _ -> ()))
     | _ -> ())

and lemma_linearize_args (fuel:nat) (args:list expr)
                         (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires numeric_operators i nu /\ Some? (A.linearize_args fuel args))
          (ensures denotations (Some?.v (A.linearize_args fuel args))
                               (map nu (eval_args i args rho)) (valuation i nu rho))
          (decreases %[fuel; 1; args]) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_linearize fuel a (Some?.v (A.linearize fuel a)) i nu rho;
    lemma_linearize_args fuel rest i nu rho

#pop-options

let embedding_model (i:interpretation value) (nu:value -> real) : prop =
  numeric_model i nu /\ boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i

let satisfied (i:interpretation value) (rho:env value) (positive:bool) (e:expr) : prop =
  if positive then lit_true i rho e else ~(lit_true i rho e)

let parsed_holds = Numeric.parsed_holds

let lemma_comparison (i:interpretation value) (nu:value -> real) (rho:env value)
                     (positive:bool) (e a b:expr) (r:A.relation)
  : Lemma (requires embedding_model i nu /\ A.comparison e == Some (r, a, b) /\
                    satisfied i rho positive e)
          (ensures parsed_holds positive r (nu (eval i a rho)) (nu (eval i b rho)) /\
                   get_sort e == bool_sort /\ get_sort a == get_sort b) =
  match e with
  | App _ [_; _] ->
    assert (numeric_operators i nu);
    if r = A.Eq then
      assert (positive ==> eval i a rho == eval i b rho)
    else
      assert (lit_true i rho e <==>
              numeric_relation r (nu (eval i a rho)) (nu (eval i b rho)))
  | _ -> ()

let rec lemma_literal (fuel:nat) (positive:bool) (e:expr) (p:bool)
                      (r:A.relation) (a b:expr)
                      (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires embedding_model i nu /\ A.literal fuel positive e == Some (p, r, a, b) /\
                    satisfied i rho positive e)
          (ensures parsed_holds p r (nu (eval i a rho)) (nu (eval i b rho)) /\
                   get_sort e == bool_sort /\ get_sort a == get_sort b)
          (decreases fuel) =
  match e with
  | App f [q] ->
    lemma_literal (fuel - 1) (not positive) q p r a b i nu rho
  | _ -> lemma_comparison i nu rho positive e a b r

let reversed = Numeric.reversed
let difference = Numeric.difference
let lemma_oriented = Numeric.lemma_oriented
let lemma_integer_step = Numeric.lemma_integer_step
let lemma_weighted = Numeric.lemma_weighted

let integer_value (v:value) : int = match v with VInt n -> n | _ -> 0

#push-options "--fuel 4"

let lemma_prepare_literal (c:A.coefficient) (positive:bool) (e:expr) (out:A.contribution)
                          (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires embedding_model i nu /\ A.prepare_literal c positive e == Some out /\
                    satisfied i rho positive e)
          (ensures P.holds out (valuation i nu rho)) =
  if fst c = 0 then ()
  else
    let p, rel, a, b = Some?.v (A.literal 16 positive e) in
    lemma_literal 16 positive e p rel a b i nu rho;
    let pa = Some?.v (A.linearize 256 a) in
    let pb = Some?.v (A.linearize 256 b) in
    lemma_linearize 256 a pa i nu rho;
    lemma_linearize 256 b pb i nu rho;
    let va = eval i a rho in
    let vb = eval i b rho in
    lemma_weighted c p rel (get_sort a = A.int_s) pa pb (nu va) (nu vb)
                   (integer_value va) (integer_value vb) (valuation i nu rho)

#pop-options

let rec assumptions_hold (i:interpretation value) (rho:env value) (xs:list (bool & expr))
  : Tot prop (decreases xs) =
  match xs with
  | [] -> True
  | (positive, e) :: rest -> satisfied i rho positive e /\ assumptions_hold i rho rest

let rec lemma_prepare (xs:list (bool & expr)) (cs:list A.coefficient)
                      (ps:list A.contribution)
                      (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires embedding_model i nu /\ A.prepare xs cs == Some ps /\ assumptions_hold i rho xs)
          (ensures P.all_hold ps (valuation i nu rho))
          (decreases xs) =
  match xs, cs with
  | (positive, e) :: rest, c :: tail ->
    lemma_prepare_literal c positive e (Some?.v (A.prepare_literal c positive e)) i nu rho;
    lemma_prepare rest tail (Some?.v (A.prepare rest tail)) i nu rho
  | _, _ -> ()

let rec lemma_assumptions (facts:list expr) (lits:list expr)
                          (i:interpretation value) (rho:env value)
  : Lemma (requires conj_holds i rho facts /\ ~(clause_holds i rho lits))
          (ensures assumptions_hold i rho
                    (map A.positive_literal facts @ map A.negative_literal lits))
          (decreases %[facts; lits]) =
  match facts with
  | _ :: rest -> lemma_assumptions rest lits i rho
  | [] ->
    (match lits with [] -> () | _ :: rest -> lemma_assumptions [] rest i rho)

let lemma_check_sound (cs:list A.coefficient) (conclusion:expr) (facts:list expr)
                      (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires embedding_model i nu /\ A.check cs conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  let aux (_:squash (~(lit_true i rho conclusion))) : Lemma False =
    assert (~(clause_holds i rho (formula_clause conclusion)));
    lemma_assumptions facts (formula_clause conclusion) i rho;
    let ps = Some?.v (A.prepare (A.assumptions conclusion facts) cs) in
    lemma_prepare (A.assumptions conclusion facts) cs ps i nu rho;
    P.lemma_accepts_sound ps (valuation i nu rho)
  in
  FStar.Classical.excluded_middle (lit_true i rho conclusion);
  FStar.Classical.or_elim #(lit_true i rho conclusion) #(~(lit_true i rho conclusion))
    #(fun () -> lit_true i rho conclusion) (fun _ -> ()) (fun h -> aux h)

let lemma_check_with_numeric_model (cs:list A.coefficient) (conclusion:expr) (facts:list expr)
                                  (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    A.check cs conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  FStar.Classical.exists_elim (lit_true i rho conclusion)
    #(value -> real) #(fun nu -> numeric_model i nu) ()
    (fun nu -> lemma_check_sound cs conclusion facts i nu rho)
