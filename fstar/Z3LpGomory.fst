module Z3LpGomory

open FStar.Real
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3ProofIndex
open FStar.List.Tot
module A = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed
module P = Z3LinearArithmeticTheory
module C = Z3LpCertificate
module I = Z3IntegerRewrite
module L = FStar.List.Tot

include Z3LpGomorySyntax

let rec lemma_conj_branch (i:interpretation value) (rho:env value) (facts:list expr) (e:expr)
  : Lemma (requires conj_holds i rho facts /\ lit_true i rho e)
          (ensures conj_holds i rho (facts @ [e]))
          (decreases facts) =
  match facts with
  | [] -> ()
  | _ :: rest -> lemma_conj_branch i rho rest e

let lemma_integer (i:interpretation value) (nu:value -> real) (rho:env value) (n:int)
  : Lemma (requires E.numeric_operators i nu)
          (ensures nu (eval i (integer n) rho) == of_int n) =
  E.lemma_linearize 1 (integer n) (P.constant n 1) i nu rho

let lemma_inequality (i:interpretation value) (nu:value -> real) (rho:env value)
                     (e a b:expr) (r:A.relation)
  : Lemma (requires E.numeric_operators i nu /\ A.comparison e == Some (r,a,b) /\ r <> A.Eq)
          (ensures lit_true i rho e <==>
             E.numeric_relation r (nu (eval i a rho)) (nu (eval i b rho))) =
  match e with App _ [_;_] -> () | _ -> ()

let lemma_split (c:certificate) (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ get_sort c.split = A.int_s)
          (ensures lit_true i rho (branch false c) \/ lit_true i rho (branch true c)) =
  assert (E.numeric_operators i nu);
  assert (VInt? (eval i c.split rho));
  let n = E.integer_value (eval i c.split rho) in
  assert (nu (eval i c.split rho) == of_int n);
  lemma_integer i nu rho c.threshold;
  lemma_integer i nu rho (c.threshold + 1);
  assert (A.comparison (branch false c) == Some (A.Le, c.split, integer c.threshold));
  assert (A.comparison (branch true c) == Some (A.Ge, c.split, integer (c.threshold + 1)));
  lemma_inequality i nu rho (branch false c) c.split (integer c.threshold) A.Le;
  lemma_inequality i nu rho (branch true c) c.split (integer (c.threshold + 1)) A.Ge;
  if n <= c.threshold then (
    assert (of_int n <=. of_int c.threshold);
    assert (lit_true i rho (branch false c)))
  else (
    assert (of_int (c.threshold + 1) <=. of_int n);
    assert (lit_true i rho (branch true c)))

let lemma_check_sound (c:certificate) (conclusion:expr) (facts:list expr)
                      (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    check c conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  let split (nu:value -> real)
    : Lemma (requires E.numeric_model i nu)
            (ensures lit_true i rho (branch false c) \/ lit_true i rho (branch true c))
    = lemma_split c i nu rho in
  FStar.Classical.exists_elim
    (lit_true i rho (branch false c) \/ lit_true i rho (branch true c))
    #(value -> real) #(fun nu -> E.numeric_model i nu) () (fun nu -> split nu);
  FStar.Classical.or_elim #(lit_true i rho (branch false c)) #(lit_true i rho (branch true c))
    #(fun () -> lit_true i rho conclusion)
    (fun _ ->
      lemma_conj_branch i rho facts (branch false c);
      E.lemma_check_with_numeric_model c.below conclusion (facts @ [branch false c]) i rho)
    (fun _ ->
      lemma_conj_branch i rho facts (branch true c);
      E.lemma_check_with_numeric_model c.above conclusion (facts @ [branch true c]) i rho)

let lemma_inferred_split_sound (conclusion:expr) (facts:list expr)
                               (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    inferred_split conclusion facts /\ conj_holds i rho facts)
          (ensures lit_true i rho conclusion) =
  match synthesize_split conclusion facts with
  | Some c -> lemma_check_sound c conclusion facts i rho
  | None -> ()
