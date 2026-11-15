module Z3Definitions

open Z3AstTheory
open Z3ValueTheory
open Z3ProofTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3BooleanRewrite
open Z3ArrayLemma
module A = Z3ArrayRewrite
module E = Z3DistinctEmbed
module Distinct = Z3DistinctAst
module L = FStar.List.Tot
module Scope = Z3ExprScope
module Binding = Z3ExprBinding
module Substitution = Z3Substitution
open FStar.List.Tot

include Z3DefinitionRecognition

let forall_sound (i:interpretation value) : prop =
  forall (bs:list sort) (b:expr) (rho:env value).
    {:pattern (eval i (Quantifier Forall_k bs bool_sort b) rho)}
    (forall (vs:list value). L.length vs == L.length bs ==>
       lit_true i (shift vs rho) b) ==>
    lit_true i rho (Quantifier Forall_k bs bool_sort b)

let definition_model (i:interpretation value) : prop =
  boolean_rewrite_model i /\ A.term_ite_sound i /\ forall_sound i /\ E.distinct_sound i

#push-options "--fuel 4 --ifuel 2"

let lemma_binary (i:interpretation value) (rho:env value)
                 (op:connective) (e a b:expr)
  : Lemma (requires and_sound i /\ or_sound i /\ binary op e == Some (a, b))
          (ensures lit_true i rho e <==> connective_holds op i rho [a; b])
  = match e with
    | App _ [_; _] -> (match op with Conjunction | Disjunction -> ())
    | _ -> ()

let lemma_branch_equation (i:interpretation value) (rho:env value)
                          (c a b:expr) (positive:bool)
  : Lemma (requires definition_model i /\ branch_equation c a b positive)
          (ensures get_sort c == bool_sort /\
                   ((lit_true i rho c <==> positive) ==> eval i a rho == eval i b rho))
  = match A.ite_parts a with
    | Some (guard, t, u) ->
      A.lemma_ite_parts i rho a guard t u;
      (match eval i c rho with VBool _ -> () | _ -> ())
    | None -> ()

let lemma_branch_axiom (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires definition_model i /\ branch_axiom e)
          (ensures lit_true i rho e)
  = match binary Disjunction e with
    | Some (guard, equation) ->
      lemma_binary i rho Disjunction e guard equation;
      let c, positive =
        match negation guard with Some c -> c, true | None -> guard, false in
      (match equality_parts equation with
       | Some (a, b) ->
         lemma_equality_parts i rho equation a b;
         (if branch_equation c a b positive then lemma_branch_equation i rho c a b positive
          else lemma_branch_equation i rho c b a positive);
         (match negation guard with
          | Some c' ->
            (match guard with App f [_] -> lemma_not_relates i rho f c' | _ -> ())
          | None -> ());
         (match eval i c rho with VBool _ -> () | _ -> ())
       | None -> ())
    | None -> ()

#pop-options

let lemma_propositional_tautology_sound (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires definition_model i /\ propositional_tautology e)
          (ensures lit_true i rho e) =
  let s = boolean_cut (boolean_frontier 3 e) 4 e in
  Z3BoundedBoolEquiv.lemma_freeze (valuation i rho) (Z3BoundedBoolEquiv.support s) s;
  Z3BooleanNormalForm.lemma_clause_tautology_sound
    (Z3BoundedBoolEquiv.freeze (valuation i rho) (Z3BoundedBoolEquiv.support s)) s;
  lemma_boolean_cut_sound (boolean_frontier 3 e) 4 i rho e;
  match eval i e rho with VBool _ -> () | _ -> ()

let rec lemma_tautology_sound (fuel:nat) (i:interpretation value)
                             (rho:env value) (e:expr)
  : Lemma (requires definition_model i /\ tautology fuel e)
          (ensures lit_true i rho e)
          (decreases %[fuel; 0]) =
  if fuel = 0 then ()
  else match e with
  | Quantifier Forall_k bs s b ->
    let aux (vs:list value)
      : Lemma (lit_true i (shift vs rho) b)
      = lemma_tautology_sound (fuel - 1) i (shift vs rho) b
    in FStar.Classical.forall_intro aux
  | App f args ->
    if E.distinct_axiom e then E.lemma_distinct_axiom_sound i rho e
    else if branch_axiom e then lemma_branch_axiom i rho e
    else if propositional_tautology e then lemma_propositional_tautology_sound i rho e
    else if connective_app Conjunction f args then lemma_tautologies_sound (fuel - 1) i rho args
    else lemma_boolean_equiv_sound 8 10 i rho e true_expr
  | _ -> lemma_boolean_equiv_sound 8 10 i rho e true_expr

and lemma_tautologies_sound (fuel:nat) (i:interpretation value)
                            (rho:env value) (args:list expr)
  : Lemma (requires definition_model i /\ tautologies fuel args)
          (ensures conj_holds i rho args)
          (decreases %[fuel; L.length args + 1]) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_tautology_sound fuel i rho a;
    lemma_tautologies_sound fuel i rho rest
