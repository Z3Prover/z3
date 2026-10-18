module Z3TheoryNormalize

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
module A = Z3ArrayRewrite
module B = Z3BooleanRewrite
module D = Z3Definitions
module AR = Z3ArithmeticRewrite
module LE = Z3LinearArithmeticEmbed
module LA = Z3LinearArithmeticAst
module QR = Z3QuantifierReduce
module QN = Z3QuantifierNnf
module LR = Z3LambdaRewrite
module BV = Z3BvLemma
module DT = Z3DatatypeLemma
module L = FStar.List.Tot

type datatype_view = (value -> (int & int)) & (value -> list value)

let normalization_model (i:interpretation value) : prop =
  D.definition_model i /\ A.rewrite_model i /\ Z3ArrayLemma.array_model i /\
  quant_extensional i /\ QN.quantifier_model i /\ LR.lambda_model i /\
  (exists (nu:value -> FStar.Real.real). LE.numeric_model i nu) /\
  (exists (project:pos -> value -> int). BV.bv_model i project) /\
  (exists (view:datatype_view). DT.datatype_model i (fst view) (snd view))

let root (e:expr) : option expr =
  if D.tautology 128 e || AR.equivalent e true_expr then Some true_expr
  else if AR.equivalent e false_expr then Some false_expr
  else match DT.rewrite e, BV.rewrite e, LR.beta e, LR.extensional e with
  | Some result, _, _, _ | _, Some result, _, _ |
    _, _, Some result, _ | _, _, _, Some result -> Some result
  | _, _, _, _ ->
    (match A.contract e with
     | Some result -> Some result
     | None ->
       (match A.expand_read e with
        | Some result -> Some result
        | None ->
          (match QR.normalize_root e with
           | Some result -> if result <> e then Some result else None
           | None -> None)))

let lemma_bv (i:interpretation value) (rho:env value) (e result:expr)
  : Lemma (requires (exists (project:pos -> value -> int). BV.bv_model i project) /\
                    B.boolean_rewrite_model i /\
                    BV.rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = let aux (project:pos -> value -> int)
      : Lemma (requires BV.bv_model i project) (ensures eval i e rho == eval i result rho)
      = BV.lemma_rewrite i rho project e result in
    FStar.Classical.exists_elim (eval i e rho == eval i result rho)
      #(pos -> value -> int) #(fun project -> BV.bv_model i project) () (fun project -> aux project)

let lemma_datatype (i:interpretation value) (rho:env value) (e result:expr)
  : Lemma (requires (exists (view:datatype_view). DT.datatype_model i (fst view) (snd view)) /\
                    B.boolean_rewrite_model i /\ DT.rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = let aux (view:datatype_view)
      : Lemma (requires DT.datatype_model i (fst view) (snd view))
              (ensures eval i e rho == eval i result rho)
      = DT.lemma_rewrite i rho (fst view) (snd view) e result in
    FStar.Classical.exists_elim (eval i e rho == eval i result rho)
      #datatype_view #(fun view -> DT.datatype_model i (fst view) (snd view)) () (fun view -> aux view)

let lemma_root (i:interpretation value) (rho:env value) (e result:expr)
  : Lemma (requires normalization_model i /\ root e == Some result)
          (ensures eval i e rho == eval i result rho)
  = if D.tautology 128 e then D.lemma_tautology_sound 128 i rho e
    else if AR.equivalent e true_expr then AR.lemma_equivalent_with_numeric_model e true_expr i rho
    else if AR.equivalent e false_expr then AR.lemma_equivalent_with_numeric_model e false_expr i rho
    else match DT.rewrite e, BV.rewrite e, LR.beta e, LR.extensional e with
    | Some result, _, _, _ -> lemma_datatype i rho e result
    | _, Some result, _, _ -> lemma_bv i rho e result
    | _, _, Some result, _ -> LR.lemma_beta i rho e result
    | _, _, _, Some result -> LR.lemma_extensional i rho e result
    | _, _, _, _ ->
      (match A.contract e with
       | Some result -> A.lemma_contract i rho e result
       | None ->
         if A.expand_read e = Some result then A.lemma_expand_read i rho e result
         else QR.lemma_normalize_root i rho e result)

let finish (e:expr) : expr =
  match root e with Some result -> result | None -> e

let lemma_finish (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires normalization_model i)
          (ensures eval i e rho == eval i (finish e) rho)
  = match root e with Some result -> lemma_root i rho e result | None -> ()

let rec normalize (fuel:nat) (e:expr) : Tot (option expr) (decreases %[fuel; e]) =
  if fuel = 0 then None
  else let next:nat = fuel - 1 in
  let rebuilt =
    match e with
    | App f args ->
      (match normalize_args next args with Some xs -> Some (App f xs) | None -> None)
    | Quantifier k bs s body ->
      (match normalize next body with Some b -> Some (Quantifier k bs s b) | None -> None)
    | _ -> Some e in
  match rebuilt with
  | Some source -> Some (finish source)
  | None -> None

and normalize_args (fuel:nat) (args:list expr)
  : Tot (option (list expr)) (decreases %[fuel; args]) =
  match args with
  | [] -> Some []
  | a :: rest ->
    (match normalize fuel a, normalize_args fuel rest with
     | Some b, Some bs -> Some (b :: bs)
     | _, _ -> None)

let rec lemma_normalize (fuel:nat) (i:interpretation value) (rho:env value) (e result:expr)
  : Lemma (requires normalization_model i /\ normalize fuel e == Some result)
          (ensures eval i e rho == eval i result rho)
          (decreases %[fuel; e])
  = if fuel = 0 then ()
    else let next:nat = fuel - 1 in
    let source =
      match e with
      | App f args ->
        let xs = Some?.v (normalize_args next args) in
        lemma_normalize_args next i rho args xs;
        App f xs
      | Quantifier k bs s body ->
        let b = Some?.v (normalize next body) in
        let bodies (vs:list value{L.length vs = L.length bs})
          : Lemma (eval i body (shift vs rho) == eval i b (shift vs rho))
          = lemma_normalize next i (shift vs rho) body b in
        FStar.Classical.forall_intro bodies;
        assert (eval i e rho == eval i (Quantifier k bs s b) rho);
        Quantifier k bs s b
      | _ -> e in
    assert (eval i e rho == eval i source rho);
    assert (normalize fuel e == Some (finish source));
    lemma_finish i rho source

and lemma_normalize_args (fuel:nat) (i:interpretation value) (rho:env value)
                         (xs ys:list expr)
  : Lemma (requires normalization_model i /\ normalize_args fuel xs == Some ys)
          (ensures eval_args i xs rho == eval_args i ys rho)
          (decreases %[fuel; xs])
  = match xs, ys with
    | x :: rest, y :: rest' ->
      lemma_normalize fuel i rho x y;
      lemma_normalize_args fuel i rho rest rest'
    | _, _ -> ()

let equivalent (a b:expr) : bool =
  match normalize 64 a, normalize 64 b with
  | Some x, Some y -> QR.equivalent 64 x y || AR.equivalent x y || A.equivalent 64 x y
  | _, _ -> false

let lemma_equivalent (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires normalization_model i /\ equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = let x, y = Some?.v (normalize 64 a), Some?.v (normalize 64 b) in
    lemma_normalize 64 i rho a x;
    lemma_normalize 64 i rho b y;
    if QR.equivalent 64 x y then QR.lemma_equivalent 64 i rho x y
    else if AR.equivalent x y then AR.lemma_equivalent_with_numeric_model x y i rho
    else A.lemma_equivalent_sound 64 i rho x y

let unit_coefficients (conclusion:expr) (facts:list expr) : list LA.coefficient =
  let one:LA.coefficient = 1, 1 in
  L.map (fun _ -> one) (LA.assumptions conclusion facts)

let tautology (e:expr) : bool =
  match normalize 64 e with
  | Some result ->
    D.tautology 128 result || Z3ArrayLemma.array_lemma result || AR.triangle_equality result ||
    LA.check (unit_coefficients result []) result []
  | None -> false

let lemma_tautology (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires normalization_model i /\ tautology e)
          (ensures lit_true i rho e)
  = let result = Some?.v (normalize 64 e) in
    lemma_normalize 64 i rho e result;
    if D.tautology 128 result then D.lemma_tautology_sound 128 i rho result
    else if Z3ArrayLemma.array_lemma result then Z3ArrayLemma.lemma_array_lemma_sound i rho result
    else if AR.triangle_equality result then AR.lemma_triangle_with_numeric_model result i rho
    else LE.lemma_check_with_numeric_model (unit_coefficients result []) result [] i rho

let sequent (facts:list expr) (conclusion:expr) : expr =
  let conjunction = App (B.connective_decl B.Conjunction facts) facts in
  let disjuncts = [mk_not_expr conjunction; conclusion] in
  App (B.connective_decl B.Disjunction disjuncts) disjuncts

let consequence (facts:list expr) (conclusion:expr) : bool =
  Z3QuantifierPull.boolean_args facts && get_sort conclusion = bool_sort &&
  (LA.check (unit_coefficients conclusion facts) conclusion facts ||
   tautology (sequent facts conclusion))

let lemma_consequence (i:interpretation value) (rho:env value)
                      (facts:list expr) (conclusion:expr)
  : Lemma (requires normalization_model i /\ conj_holds i rho facts /\ consequence facts conclusion)
          (ensures lit_true i rho conclusion)
  = if LA.check (unit_coefficients conclusion facts) conclusion facts
    then LE.lemma_check_with_numeric_model (unit_coefficients conclusion facts) conclusion facts i rho
    else (
      lemma_tautology i rho (sequent facts conclusion);
      match eval i (App (B.connective_decl B.Conjunction facts) facts) rho with
      | VBool _ -> ()
      | _ -> ())
