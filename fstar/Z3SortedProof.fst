module Z3SortedProof

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module DT = Z3SortedDatatype
module U = Z3UnifiedProof
module P = Z3ProofDocument
module R = Z3ResolutionProofTheory
module D = Z3Definitions
module L = FStar.List.Tot
module I = Z3ProofIndex
module B = Z3BoundedBoolEquiv
module TN = Z3TheoryNormalize

let rec equations (facts:list expr) : Tot (list U.judgment) (decreases facts) =
  match facts with
  | [] -> []
  | App f [a; b] :: rest ->
    if f = R.eq_decl (get_sort a) && get_sort a = get_sort b
    then U.Equal a b :: equations rest else equations rest
  | _ :: rest -> equations rest

let rec equations_hold (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                       (js:list U.judgment) : Tot bool (decreases js) =
  match js with
  | [] -> true
  | U.Equal a b :: rest -> T.same_value s bc eq other a b && equations_hold s bc eq other rest
  | _ -> false

let rec lemma_equations (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                        (facts:list expr)
  : Lemma (requires T.truths s bc eq other facts)
          (ensures equations_hold s bc eq other (equations facts))
          (decreases facts) =
  match facts with
  | [] -> ()
  | App f [a; b] :: rest ->
    if f = R.eq_decl (get_sort a) && get_sort a = get_sort b then (
      T.lemma_equality s bc eq other a b;
      T.lemma_same_value s bc eq other a b);
    lemma_equations s bc eq other rest
  | _ :: rest -> lemma_equations s bc eq other rest

let rec known_equal (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                    (origin:expr) (known:list expr) : Tot bool (decreases known) =
  match known with
  | [] -> true
  | e :: rest -> T.same_value s bc eq other origin e && known_equal s bc eq other origin rest

let rec lemma_known_member (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                           (origin:expr) (known:list expr) (e:expr)
  : Lemma (requires known_equal s bc eq other origin known /\ L.mem e known)
          (ensures T.same_value s bc eq other origin e)
          (decreases known) =
  match known with
  | [] -> ()
  | x :: rest -> if x <> e then lemma_known_member s bc eq other origin rest e

let lemma_same_transitive (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                          (a b c:expr)
  : Lemma (requires T.same_value s bc eq other a b /\ T.same_value s bc eq other b c)
          (ensures T.same_value s bc eq other a c) =
  T.lemma_same_value s bc eq other a b;
  T.lemma_same_value s bc eq other b c;
  T.lemma_same_value s bc eq other a c

let lemma_same_symmetric (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                         (a b:expr)
  : Lemma (requires T.same_value s bc eq other a b)
          (ensures T.same_value s bc eq other b a) =
  T.lemma_same_value s bc eq other a b;
  T.lemma_same_value s bc eq other b a

let rec lemma_extend_reachable (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                               (origin:expr) (js:list U.judgment) (known:list expr)
  : Lemma (requires equations_hold s bc eq other js /\ known_equal s bc eq other origin known)
          (ensures known_equal s bc eq other origin (U.extend_reachable U.Equality js known))
          (decreases js) =
  match js with
  | [] -> ()
  | U.Equal a b :: rest ->
    if L.mem a known then (
      lemma_known_member s bc eq other origin known a;
      lemma_same_transitive s bc eq other origin a b;
      lemma_extend_reachable s bc eq other origin rest (b :: known))
    else if L.mem b known then (
      lemma_known_member s bc eq other origin known b;
      lemma_same_symmetric s bc eq other a b;
      lemma_same_transitive s bc eq other origin b a;
      lemma_extend_reachable s bc eq other origin rest (a :: known))
    else lemma_extend_reachable s bc eq other origin rest known
  | _ -> ()

let rec lemma_reachable (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                        (fuel:nat) (origin:expr) (js:list U.judgment) (known:list expr)
  : Lemma (requires equations_hold s bc eq other js /\ known_equal s bc eq other origin known)
          (ensures known_equal s bc eq other origin (U.reachable fuel U.Equality js known))
          (decreases fuel) =
  if fuel > 0 then (
    lemma_extend_reachable s bc eq other origin js known;
    lemma_reachable s bc eq other (fuel - 1) origin js (U.extend_reachable U.Equality js known))

let rec equal (s:S.checked_schema) (fuel:nat) (facts:list expr) (a b:expr)
  : Tot bool (decreases %[fuel; 0]) =
  D.scoped [] a && D.scoped [] b && get_sort a = get_sort b &&
  (a = b || L.mem b (U.reachable 8 U.Equality (equations facts) [a]) ||
   (fuel > 0 &&
    (match a, b with
     | App f xs, App g ys -> f = g && equal_arguments s (fuel - 1) facts xs ys
     | _, _ -> false)) ||
   (match DT.normalize s 64 a, DT.normalize s 64 b with
    | Some x, Some y -> x = y
    | _, _ -> false))

and equal_arguments (s:S.checked_schema) (fuel:nat) (facts:list expr) (xs ys:list expr)
  : Tot bool (decreases %[fuel; L.length xs + 1]) =
  match xs, ys with
  | [], [] -> true
  | x :: rest, y :: tail -> equal s fuel facts x y && equal_arguments s fuel facts rest tail
  | _, _ -> false

let rec lemma_equal (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                    (fuel:nat) (facts:list expr) (a b:expr)
  : Lemma (requires T.truths s bc eq other facts /\ equal s fuel facts a b)
          (ensures T.same_value s bc eq other a b)
          (decreases %[fuel; 0]) =
  T.lemma_same_value s bc eq other a b;
  if a = b then ()
  else if L.mem b (U.reachable 8 U.Equality (equations facts) [a]) then (
    T.lemma_same_value s bc eq other a a;
    lemma_equations s bc eq other facts;
    lemma_reachable s bc eq other 8 a (equations facts) [a];
    lemma_known_member s bc eq other a (U.reachable 8 U.Equality (equations facts) [a]) b)
  else
    let congruent =
      fuel > 0 &&
      (match a, b with
       | App f xs, App g ys -> f = g && equal_arguments s (fuel - 1) facts xs ys
       | _, _ -> false) in
    if not congruent then (
      DT.lemma_normalize s bc eq other 64 a (Some?.v (DT.normalize s 64 a));
      DT.lemma_normalize s bc eq other 64 b (Some?.v (DT.normalize s 64 b)))
    else
      (match a, b with
       | App f xs, App _ ys ->
         lemma_equal_arguments s bc eq other (fuel - 1) facts xs ys f.domain
       | _, _ -> ())

and lemma_equal_arguments (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                          (fuel:nat) (facts:list expr) (xs ys:list expr) (ss:list sort)
  : Lemma (requires T.truths s bc eq other facts /\
                    D.scoped_args [] xs /\ D.scoped_args [] ys /\
                    sorts_match xs ss /\ sorts_match ys ss /\
                    equal_arguments s fuel facts xs ys)
          (ensures T.evaluate_arguments s bc eq other xs ss == T.evaluate_arguments s bc eq other ys ss)
          (decreases %[fuel; L.length xs + 1]) =
  match xs, ys, ss with
  | x :: rest, y :: tail, t :: remaining ->
    V.lemma_sort_eq (get_sort x) t;
    V.lemma_sort_eq (get_sort y) t;
    lemma_equal s bc eq other fuel facts x y;
    T.lemma_same_value s bc eq other x y;
    lemma_equal_arguments s bc eq other fuel facts rest tail remaining
  | _, _, _ -> ()

let rec lemma_replace (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                      (source target e:expr)
  : Lemma (requires T.same_value s bc eq other source target /\
                    get_sort source == get_sort target /\ D.scoped [] e)
          (ensures D.scoped [] (TN.replace source target e) /\
                   get_sort (TN.replace source target e) == get_sort e /\
                   T.evaluate s bc eq other (TN.replace source target e) == T.evaluate s bc eq other e)
          (decreases e) =
  T.lemma_same_value s bc eq other source target;
  if e = source then ()
  else match e with
  | App f args -> lemma_replace_args s bc eq other source target args f.domain
  | _ -> ()

and lemma_replace_args (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                       (source target:expr) (args:list expr) (ss:list sort)
  : Lemma (requires T.same_value s bc eq other source target /\
                    get_sort source == get_sort target /\
                    D.scoped_args [] args /\ sorts_match args ss)
          (ensures D.scoped_args [] (TN.replace_args source target args) /\
                   sorts_match (TN.replace_args source target args) ss /\
                   T.evaluate_arguments s bc eq other (TN.replace_args source target args) ss ==
                     T.evaluate_arguments s bc eq other args ss)
          (decreases args) =
  match args, ss with
  | e :: rest, t :: tail ->
    V.lemma_sort_eq (get_sort e) t;
    lemma_replace s bc eq other source target e;
    V.lemma_sort_eq (get_sort (TN.replace source target e)) t;
    lemma_replace_args s bc eq other source target rest tail
  | _, _ -> ()

let rec lemma_replace_facts (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                            (source target:expr) (facts:list expr)
  : Lemma (requires T.same_value s bc eq other source target /\
                    get_sort source == get_sort target /\ T.truths s bc eq other facts)
          (ensures T.truths s bc eq other (TN.replace_args source target facts))
          (decreases facts) =
  match facts with
  | [] -> ()
  | f :: rest ->
    lemma_replace s bc eq other source target f;
    lemma_replace_facts s bc eq other source target rest

let rec lemma_constructor_premise (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                  (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                                  (facts:list expr) (source target:expr)
  : Lemma (requires T.truths s bc eq other facts /\
                    TN.constructor_premise facts == Some (source, target))
          (ensures T.same_value s bc eq other source target /\ get_sort source == get_sort target)
          (decreases facts) =
  match facts with
  | [] -> ()
  | e :: rest ->
    (match TN.constructor_replacement e with
     | Some _ ->
       (match e with
        | App _ [a; b] ->
          T.lemma_equality s bc eq other a b;
          T.lemma_same_value s bc eq other source target
        | _ -> ())
     | None -> lemma_constructor_premise s bc eq other rest source target)

let rec negative_atoms (facts:list expr) : Tot (list expr) (decreases facts) =
  match facts with
  | [] -> []
  | App f [arg] :: rest ->
    if T.classify f = T.Negation then arg :: negative_atoms rest else negative_atoms rest
  | _ :: rest -> negative_atoms rest

let negative_exhaustion (s:S.checked_schema) (facts:list expr) : bool =
  let atoms = negative_atoms facts in
  let clause = App (Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Disjunction atoms) atoms in
  D.scoped [] clause && DT.exhaustive s clause

let rec lemma_negative_atoms (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                              (facts:list expr)
  : Lemma (requires T.truths s bc eq other facts)
          (ensures not (B.eval_args (T.truth s bc eq other) B.Or (L.map B.Atom (negative_atoms facts))))
          (decreases facts) =
  match facts with
  | [] -> ()
  | App f [arg] :: rest ->
    if T.classify f = T.Negation then T.lemma_negation s bc eq other f arg;
    lemma_negative_atoms s bc eq other rest
  | _ :: rest -> lemma_negative_atoms s bc eq other rest

let lemma_negative_exhaustion (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                              (facts:list expr)
  : Lemma (requires T.truths s bc eq other facts /\ negative_exhaustion s facts)
          (ensures False) =
  let atoms = negative_atoms facts in
  let disjunction = Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Disjunction atoms in
  lemma_negative_atoms s bc eq other facts;
  DT.lemma_exhaustive s bc eq other (App disjunction atoms);
  T.lemma_nary s bc eq other disjunction atoms B.Or

let rec reconstruction_conflict (s:S.checked_schema) (facts remaining:list expr)
  : Tot bool (decreases remaining) =
  match remaining with
  | [] -> false
  | App f [arg] :: rest ->
    (T.classify f = T.Negation && DT.reconstruction_from s facts arg) ||
    reconstruction_conflict s facts rest
  | _ :: rest -> reconstruction_conflict s facts rest

let rec lemma_truth_scopes (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                          (facts:list expr)
  : Lemma (requires T.truths s bc eq other facts)
          (ensures D.scoped_args [] facts)
          (decreases facts) =
  match facts with [] -> () | _ :: rest -> lemma_truth_scopes s bc eq other rest

let rec lemma_reconstruction_conflict (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                      (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                                      (facts remaining:list expr)
  : Lemma (requires T.truths s bc eq other facts /\ T.truths s bc eq other remaining /\
                    reconstruction_conflict s facts remaining)
          (ensures False)
          (decreases remaining) =
  match remaining with
  | [] -> ()
  | App f [arg] :: rest ->
    if T.classify f = T.Negation && DT.reconstruction_from s facts arg then (
      lemma_truth_scopes s bc eq other facts;
      T.lemma_negation s bc eq other f arg;
      DT.lemma_reconstruction_from s bc eq other facts arg)
    else lemma_reconstruction_conflict s bc eq other facts rest
  | _ :: rest -> lemma_reconstruction_conflict s bc eq other facts rest

let equality_consequence (s:S.checked_schema) (facts:list expr) (conclusion:expr) : bool =
  match conclusion with
   | App f [a; b] -> f = R.eq_decl (get_sort a) && equal s 8 facts a b
   | _ -> false

let direct_consequence (s:S.checked_schema) (facts:list expr) (conclusion:expr) : bool =
  (D.scoped [] conclusion && get_sort conclusion = bool_sort && DT.simple_consequence facts conclusion) ||
  equality_consequence s facts conclusion ||
  negative_exhaustion s facts || reconstruction_conflict s facts facts ||
  DT.consequence s facts conclusion

let lemma_direct_consequence (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                             (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc eq other facts /\ direct_consequence s facts conclusion)
          (ensures T.truth s bc eq other conclusion) =
  if D.scoped [] conclusion && get_sort conclusion = bool_sort && DT.simple_consequence facts conclusion then
    DT.lemma_simple_consequence s bc eq other facts conclusion
  else if equality_consequence s facts conclusion then (
    match conclusion with
    | App _ [a; b] ->
      lemma_equal s bc eq other 8 facts a b;
      T.lemma_same_value s bc eq other a b;
      T.lemma_equality s bc eq other a b
    | _ -> ())
  else if negative_exhaustion s facts then lemma_negative_exhaustion s bc eq other facts
  else if reconstruction_conflict s facts facts then lemma_reconstruction_conflict s bc eq other facts facts
  else DT.lemma_consequence s bc eq other facts conclusion

let rec propagate (s:S.checked_schema) (fuel:nat) (facts:list expr) (conclusion:expr)
  : Tot bool (decreases fuel) =
  if direct_consequence s facts conclusion then true
  else if fuel = 0 then false
  else let _ = assert (fuel > 0) in
  let next:nat = fuel - 1 in
  match TN.constructor_premise facts with
  | Some (source, target) ->
    propagate s next (TN.replace_args source target facts) (TN.replace source target conclusion)
  | None -> false

let rec lemma_propagate (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                        (fuel:nat) (facts:list expr) (conclusion:expr)
  : Lemma (requires D.scoped [] conclusion /\ T.truths s bc eq other facts /\
                    propagate s fuel facts conclusion)
          (ensures T.truth s bc eq other conclusion)
          (decreases fuel) =
  if direct_consequence s facts conclusion then lemma_direct_consequence s bc eq other facts conclusion
  else if fuel > 0 then
    match TN.constructor_premise facts with
    | Some (source, target) ->
      lemma_constructor_premise s bc eq other facts source target;
      lemma_replace_facts s bc eq other source target facts;
      lemma_replace s bc eq other source target conclusion;
      lemma_propagate s bc eq other (fuel - 1)
        (TN.replace_args source target facts) (TN.replace source target conclusion)
    | None -> ()

let consequence (s:S.checked_schema) (facts:list expr) (conclusion:expr) : bool =
  D.scoped_args [] facts && D.scoped [] conclusion && get_sort conclusion = bool_sort &&
  propagate s 8 facts conclusion

let lemma_consequence (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                      (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc eq other facts /\ consequence s facts conclusion)
          (ensures T.truth s bc eq other conclusion) =
  lemma_propagate s bc eq other 8 facts conclusion

let proposition (j:U.judgment) : expr =
  match j with
  | U.Holds e -> e
  | U.Equal a b | U.Observational a b -> R.mk_eq_expr a b

let declaration_in_context (s:S.checked_schema) (f:func_decl) : bool =
  if f.interp = Some Z3DatatypeLemma.op_constructor then Some? (S.case_of s.cases f)
  else if f.interp = Some Z3DatatypeLemma.op_recognizer then Some? (S.find_recognizer f s.cases)
  else if f.interp = Some Z3DatatypeLemma.op_accessor then Some? (S.find_accessor f s.cases)
  else true

let rec in_context (s:S.checked_schema) (e:expr) : Tot bool (decreases e) =
  match e with
  | App f es -> declaration_in_context s f && args_in_context s es
  | Quantifier _ _ _ body -> in_context s body
  | Var _ _ -> true

and args_in_context (s:S.checked_schema) (es:list expr) : Tot bool (decreases es) =
  match es with [] -> true | e :: rest -> in_context s e && args_in_context s rest

let boolean_expression (s:S.checked_schema) (e:expr) : bool =
  D.scoped [] e && get_sort e = bool_sort && in_context s e

let rec boolean_expressions (s:S.checked_schema) (es:list expr) : Tot bool (decreases es) =
  match es with [] -> true | e :: rest -> boolean_expression s e && boolean_expressions s rest

let fact_valid (s:S.checked_schema) (p:U.checked_fact) : bool =
  boolean_expression s (proposition p.conclusion) && boolean_expressions s p.hypotheses

let rec facts_valid (s:S.checked_schema) (ps:list U.checked_fact) : Tot bool (decreases ps) =
  match ps with [] -> true | p :: rest -> fact_valid s p && facts_valid s rest

let rec propositions (ps:list U.checked_fact) : Tot (list expr) (decreases ps) =
  match ps with [] -> [] | p :: rest -> proposition p.conclusion :: propositions rest

let implies_decl : func_decl = {
  decl_name = "=>"; domain = [bool_sort; bool_sort]; range = bool_sort;
  interp = Some Z3ValueTheory.op_implies; int_params = [];
}

let scoped_proposition (p:U.checked_fact) : expr =
  App implies_decl [
    App (Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Conjunction p.hypotheses) p.hypotheses;
    proposition p.conclusion]

let rec scoped_propositions (ps:list U.checked_fact) : Tot (list expr) (decreases ps) =
  match ps with [] -> [] | p :: rest -> scoped_proposition p :: scoped_propositions rest

let fact_holds (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
               (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
               (p:U.checked_fact) : bool =
  not (T.truths s bc eq other p.hypotheses) || T.truth s bc eq other (proposition p.conclusion)

let rec facts_hold (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                   (ps:list U.checked_fact) : Tot bool (decreases ps) =
  match ps with [] -> true | p :: rest -> fact_holds s bc eq other p && facts_hold s bc eq other rest

let rec lemma_boolean_expressions (s:S.checked_schema) (es:list expr)
  : Lemma (requires boolean_expressions s es)
          (ensures D.scoped_args [] es /\
                   (forall (e:expr). L.mem e es ==> get_sort e == bool_sort))
          (decreases es) =
  match es with [] -> () | _ :: rest -> lemma_boolean_expressions s rest

let lemma_scoped_proposition (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                             (p:U.checked_fact)
  : Lemma (requires fact_valid s p)
          (ensures D.scoped [] (scoped_proposition p) /\
                   T.truth s bc eq other (scoped_proposition p) == fact_holds s bc eq other p) =
  lemma_boolean_expressions s p.hypotheses;
  DT.lemma_boolean_domain p.hypotheses;
  DT.lemma_conjunction s bc eq other p.hypotheses;
  T.lemma_truths s bc eq other p.hypotheses;
  T.lemma_evaluate_core s bc eq other implies_decl [
    App (Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Conjunction p.hypotheses) p.hypotheses;
    proposition p.conclusion]

let rec lemma_scoped_propositions (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                  (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                                  (ps:list U.checked_fact)
  : Lemma (requires facts_valid s ps /\ facts_hold s bc eq other ps)
          (ensures T.truths s bc eq other (scoped_propositions ps))
          (decreases ps) =
  match ps with
  | [] -> ()
  | p :: rest ->
    lemma_scoped_proposition s bc eq other p;
    lemma_scoped_propositions s bc eq other rest

let rec lemma_truth_member (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                           (es:list expr) (e:expr)
  : Lemma (requires T.truths s bc eq other es /\ L.mem e es)
          (ensures T.truth s bc eq other e)
          (decreases es) =
  match es with [] -> () | x :: rest -> if x <> e then lemma_truth_member s bc eq other rest e

let rec lemma_hypothesis_union (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                               (xs ys:list expr)
  : Lemma (requires T.truths s bc eq other (U.add_hypotheses xs ys))
          (ensures T.truths s bc eq other xs /\ T.truths s bc eq other ys)
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest ->
    if L.mem x ys then (
      lemma_hypothesis_union s bc eq other rest ys;
      lemma_truth_member s bc eq other ys x)
    else lemma_hypothesis_union s bc eq other rest (x :: ys)

let rec lemma_premise_hypotheses (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                 (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                                 (ps:list U.checked_fact)
  : Lemma (requires facts_hold s bc eq other ps /\
                    T.truths s bc eq other (U.premise_hypotheses ps))
          (ensures T.truths s bc eq other (propositions ps))
          (decreases ps) =
  match ps with
  | [] -> ()
  | p :: rest ->
    lemma_hypothesis_union s bc eq other p.hypotheses (U.premise_hypotheses rest);
    lemma_premise_hypotheses s bc eq other rest

let rec remaining_hypotheses (hyps:list expr) (conclusion:expr)
  : Tot (list expr) (decreases hyps) =
  match hyps with
  | [] -> []
  | h :: rest ->
    if DT.eliminated (conclusion :: DT.literals conclusion) h then remaining_hypotheses rest conclusion
    else h :: remaining_hypotheses rest conclusion

let lemma_discharged (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                     (h conclusion:expr)
  : Lemma (requires boolean_expression s h /\ boolean_expression s conclusion /\
                    not (T.truth s bc eq other conclusion) /\
                    DT.eliminated (conclusion :: DT.literals conclusion) h)
          (ensures T.truth s bc eq other h) =
  DT.lemma_literals s bc eq other conclusion;
  let clause = conclusion :: DT.literals conclusion in
  if L.mem (R.mk_not_expr h) clause then (
    if T.truth s bc eq other (R.mk_not_expr h) then
      DT.lemma_literal_member (T.truth s bc eq other) clause (R.mk_not_expr h);
    T.lemma_negation s bc eq other R.not_decl h)
  else match h with
  | App f [a] ->
    if T.truth s bc eq other a then DT.lemma_literal_member (T.truth s bc eq other) clause a;
    T.lemma_negation s bc eq other f a
  | _ -> ()

let rec lemma_remaining_hypotheses (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                   (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                                   (hyps:list expr) (conclusion:expr)
  : Lemma (requires boolean_expressions s hyps /\ boolean_expression s conclusion /\
                    not (T.truth s bc eq other conclusion) /\
                    T.truths s bc eq other (remaining_hypotheses hyps conclusion))
          (ensures T.truths s bc eq other hyps)
          (decreases hyps) =
  match hyps with
  | [] -> ()
  | h :: rest ->
    if DT.eliminated (conclusion :: DT.literals conclusion) h then lemma_discharged s bc eq other h conclusion;
    lemma_remaining_hypotheses s bc eq other rest conclusion

let lemma_step (node:U.proof_node) : bool =
  node.kind = U.LemmaRule &&
  (match node.premises with [p] -> p.conclusion = U.Holds R.false_expr | _ -> false)

let rec lemma_context_union (s:S.checked_schema) (xs ys:list expr)
  : Lemma (requires boolean_expressions s xs /\ boolean_expressions s ys)
          (ensures boolean_expressions s (U.add_hypotheses xs ys))
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest ->
    lemma_context_union s rest (if L.mem x ys then ys else x :: ys)

let rec lemma_premise_context (s:S.checked_schema) (ps:list U.checked_fact)
  : Lemma (requires facts_valid s ps)
          (ensures boolean_expressions s (U.premise_hypotheses ps))
          (decreases ps) =
  match ps with
  | [] -> ()
  | p :: rest ->
    lemma_premise_context s rest;
    lemma_context_union s p.hypotheses (U.premise_hypotheses rest)

let rec lemma_remaining_context (s:S.checked_schema) (hyps:list expr) (conclusion:expr)
  : Lemma (requires boolean_expressions s hyps)
          (ensures boolean_expressions s (remaining_hypotheses hyps conclusion) /\
                   boolean_expressions s (U.remaining_hypotheses hyps conclusion))
          (decreases hyps) =
  match hyps with
  | [] -> ()
  | _ :: rest -> lemma_remaining_context s rest conclusion

let check_node_cached (s:S.checked_schema) (assertions:list expr) (node:U.proof_node)
  : option (U.checked_fact & nat) =
  let conclusion = proposition node.conclusion in
  if not (boolean_expression s conclusion) then None
  else match node.kind with
  | U.Asserted ->
    if node.premises = [] && L.mem conclusion assertions
    then Some ({ U.conclusion = node.conclusion; hypotheses = [] }, 0)
    else None
  | U.Hypothesis ->
    if node.premises = []
    then Some ({ U.conclusion = node.conclusion; hypotheses = [conclusion] }, 0)
    else None
  | _ ->
    let inherited = U.premise_hypotheses node.premises in
    let hypotheses =
      if lemma_step node then
        match node.premises with [p] -> remaining_hypotheses p.hypotheses conclusion | _ -> inherited
      else if node.kind = U.LemmaRule then U.remaining_hypotheses inherited conclusion
      else inherited in
    let fact = { U.conclusion = node.conclusion; hypotheses = hypotheses } in
    let checked =
      lemma_step node ||
      (node.kind <> U.LemmaRule && consequence s (propositions node.premises) conclusion) ||
      DT.consequence s (scoped_propositions node.premises) (scoped_proposition fact) in
    Some (fact, (if checked then 0 else 1))

let check_node (s:S.checked_schema) (assertions:list expr) (node:U.proof_node)
  : option (U.checked_fact & nat) =
  if facts_valid s node.premises then check_node_cached s assertions node else None

let lemma_check_node_context (s:S.checked_schema) (assertions:list expr)
                             (node:U.proof_node) (fact:U.checked_fact) (pending:nat)
  : Lemma (requires facts_valid s node.premises /\
                    check_node_cached s assertions node == Some (fact, pending))
          (ensures fact_valid s fact) =
  match node.kind with
  | U.Asserted | U.Hypothesis -> ()
  | _ ->
    lemma_premise_context s node.premises;
    if lemma_step node then (
      match node.premises with
      | [p] -> lemma_remaining_context s p.hypotheses (proposition node.conclusion)
      | _ -> ())
    else if node.kind = U.LemmaRule then
      lemma_remaining_context s (U.premise_hypotheses node.premises) (proposition node.conclusion)

let lemma_check_node_cached (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                     (assertions:list expr) (node:U.proof_node) (fact:U.checked_fact)
  : Lemma (requires T.truths s bc eq other assertions /\ facts_hold s bc eq other node.premises /\
                    facts_valid s node.premises /\
                    check_node_cached s assertions node == Some (fact, 0))
          (ensures fact_holds s bc eq other fact) =
  lemma_check_node_context s assertions node fact 0;
  match node.kind with
  | U.Asserted -> lemma_truth_member s bc eq other assertions (proposition node.conclusion)
  | U.Hypothesis -> ()
  | _ ->
    let conclusion = proposition node.conclusion in
    if lemma_step node then (
      match node.premises with
      | [p] ->
        if T.truths s bc eq other fact.hypotheses && not (T.truth s bc eq other conclusion) then (
          lemma_remaining_hypotheses s bc eq other p.hypotheses conclusion;
          T.lemma_cut s bc eq other 1 R.false_expr)
      | _ -> ())
    else if node.kind <> U.LemmaRule && consequence s (propositions node.premises) conclusion then (
      if T.truths s bc eq other fact.hypotheses then (
        lemma_premise_hypotheses s bc eq other node.premises;
        lemma_consequence s bc eq other (propositions node.premises) conclusion))
    else (
      lemma_scoped_propositions s bc eq other node.premises;
      DT.lemma_consequence s bc eq other (scoped_propositions node.premises) (scoped_proposition fact);
      lemma_scoped_proposition s bc eq other fact)

let prepare_entry (s:S.checked_schema) (cache:I.index_tree U.checked_fact) (e:P.entry)
  : option U.proof_node =
  if not (D.scoped [] e.formula && in_context s e.formula) then None
  else match U.classify_fact e.formula, I.opt_map (I.index_find cache) e.premise_ids with
  | Some conclusion, Some premises ->
    Some { U.kind = e.rule; conclusion = conclusion; premises = premises }
  | _, _ -> None

let rec check_entries (s:S.checked_schema) (assertions:list expr)
                      (cache:I.index_tree U.checked_fact) (next pending:nat) (entries:list P.entry)
  : Tot (option (I.index_tree U.checked_fact & nat)) (decreases entries) =
  match entries with
  | [] -> Some (cache, pending)
  | e :: rest ->
    (match prepare_entry s cache e with
     | None -> None
     | Some node ->
       (match check_node_cached s assertions node with
        | None -> None
        | Some (fact, local) ->
          check_entries s assertions (I.index_put cache next fact) (next + 1) (pending + local) rest))

let check_document (schema:S.schema) (doc:P.document) : option nat =
  if not (S.valid schema) then None
  else if not (boolean_expressions schema doc.assertions && U.ordinary_facts doc.assertions) then None
  else match check_entries schema doc.assertions I.Empty 0 0 doc.entries with
  | None -> None
  | Some (cache, pending) ->
    (match I.index_find cache doc.root with
     | Some fact ->
       if fact.conclusion = U.Holds R.false_expr && fact.hypotheses = [] then Some pending else None
     | None -> None)

let rec lemma_pending (s:S.checked_schema) (assertions:list expr)
                      (cache:I.index_tree U.checked_fact) (next pending:nat) (entries:list P.entry)
                      (result:I.index_tree U.checked_fact) (count:nat)
  : Lemma (requires check_entries s assertions cache next pending entries == Some (result, count))
          (ensures pending <= count)
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    let node = Some?.v (prepare_entry s cache e) in
    let fact, local = Some?.v (check_node_cached s assertions node) in
    lemma_pending s assertions (I.index_put cache next fact) (next + 1) (pending + local) rest result count

let cache_sound (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                (cache:I.index_tree U.checked_fact) : prop =
  forall (key:nat) (p:U.checked_fact).
    I.index_get cache key == Some p ==> fact_valid s p /\ fact_holds s bc eq other p

let lemma_cache_insert (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                       (cache:I.index_tree U.checked_fact) (key:nat) (fact:U.checked_fact)
  : Lemma (requires cache_sound s bc eq other cache /\ fact_valid s fact /\ fact_holds s bc eq other fact)
          (ensures cache_sound s bc eq other (I.index_put cache key fact)) =
  let at (query:nat)
    : Lemma (forall (p:U.checked_fact).
        I.index_get (I.index_put cache key fact) query == Some p ==>
        fact_valid s p /\ fact_holds s bc eq other p) =
    I.lemma_index_put cache key fact query in
  FStar.Classical.forall_intro at

let rec lemma_premise_lookup (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                             (cache:I.index_tree U.checked_fact) (ids:list int) (ps:list U.checked_fact)
  : Lemma (requires cache_sound s bc eq other cache /\
                    I.opt_map (I.index_find cache) ids == Some ps)
          (ensures facts_valid s ps /\ facts_hold s bc eq other ps)
          (decreases ids) =
  match ids, ps with
  | id :: rest, p :: tail ->
    assert (id >= 0);
    assert (I.index_get cache id == Some p);
    assert (fact_valid s p /\ fact_holds s bc eq other p);
    lemma_premise_lookup s bc eq other cache rest tail
  | _, _ -> ()

let rec lemma_entries (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                      (assertions:list expr) (cache:I.index_tree U.checked_fact)
                      (next pending:nat) (entries:list P.entry) (result:I.index_tree U.checked_fact)
  : Lemma (requires T.truths s bc eq other assertions /\ cache_sound s bc eq other cache /\
                    check_entries s assertions cache next pending entries == Some (result, 0))
          (ensures cache_sound s bc eq other result)
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    let node = Some?.v (prepare_entry s cache e) in
    let fact, local = Some?.v (check_node_cached s assertions node) in
    lemma_pending s assertions (I.index_put cache next fact) (next + 1) (pending + local) rest result 0;
    lemma_premise_lookup s bc eq other cache e.premise_ids node.premises;
    lemma_check_node_context s assertions node fact local;
    lemma_check_node_cached s bc eq other assertions node fact;
    lemma_cache_insert s bc eq other cache next fact;
    lemma_entries s bc eq other assertions (I.index_put cache next fact) (next + 1)
      (pending + local) rest result

let lemma_check_document (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                         (doc:P.document)
  : Lemma (requires check_document s doc == Some 0)
          (ensures not (T.truths s bc eq other doc.assertions)) =
  if T.truths s bc eq other doc.assertions then (
    let cache, _ = Some?.v (check_entries s doc.assertions I.Empty 0 0 doc.entries) in
    lemma_entries s bc eq other doc.assertions I.Empty 0 0 doc.entries cache;
    assert (doc.root >= 0);
    let root = Some?.v (I.index_find cache doc.root) in
    assert (I.index_get cache doc.root == Some root);
    assert (fact_valid s root /\ fact_holds s bc eq other root);
    assert (T.truth s bc eq other R.false_expr);
    assert_norm (T.cut 1 R.false_expr == B.Bool false);
    T.lemma_cut s bc eq other 1 R.false_expr)

let rec diagnose_entries (s:S.checked_schema) (assertions:list expr)
                         (cache:I.index_tree U.checked_fact) (next pending:nat)
                         (unmet:list P.unmet_obligation) (entries:list P.entry)
  : Tot P.entries_diagnostic (decreases entries) =
  match entries with
  | [] -> P.EntriesChecked cache pending (L.rev unmet)
  | e :: rest ->
    let reject = P.EntriesRejected (P.DocumentRejected P.ProofEntry (Some next) (Some e.formula)) in
    match prepare_entry s cache e with
    | None -> reject
    | Some node ->
      (match check_node_cached s assertions node with
       | None -> reject
       | Some (fact, local) ->
         let cache = I.index_put cache next fact in
         let unmet =
           if local = 0 then unmet
           else {
             P.obligation_index = next; obligation_rule = e.rule;
             obligation_conclusion = fact.conclusion;
             obligation_premises = U.premise_judgments node.premises;
             obligation_source = e.formula; obligation_count = local;
           } :: unmet in
         diagnose_entries s assertions cache (next + 1) (pending + local) unmet rest)

let diagnostic_entries_result (d:P.entries_diagnostic) : option (I.index_tree U.checked_fact & nat) =
  match d with P.EntriesChecked cache pending _ -> Some (cache, pending) | P.EntriesRejected _ -> None

let rec lemma_diagnose_entries (s:S.checked_schema) (assertions:list expr)
                               (cache:I.index_tree U.checked_fact) (next pending:nat)
                               (unmet:list P.unmet_obligation) (entries:list P.entry)
  : Lemma (diagnostic_entries_result (diagnose_entries s assertions cache next pending unmet entries) ==
           check_entries s assertions cache next pending entries)
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    (match prepare_entry s cache e with
     | None -> ()
     | Some node ->
       (match check_node_cached s assertions node with
        | None -> ()
        | Some (fact, local) ->
          let unmet =
            if local = 0 then unmet
            else {
              P.obligation_index = next; obligation_rule = e.rule;
              obligation_conclusion = fact.conclusion;
              obligation_premises = U.premise_judgments node.premises;
              obligation_source = e.formula; obligation_count = local;
            } :: unmet in
          lemma_diagnose_entries s assertions (I.index_put cache next fact)
            (next + 1) (pending + local) unmet rest))

let diagnose_document (schema:S.schema) (doc:P.document) : P.document_diagnostic =
  if not (S.valid schema) then P.DocumentRejected P.LogicalDeclarations None None
  else if not (boolean_expressions schema doc.assertions && U.ordinary_facts doc.assertions)
  then P.DocumentRejected P.OriginalAssertions None None
  else match diagnose_entries schema doc.assertions I.Empty 0 0 [] doc.entries with
  | P.EntriesRejected reason ->
    (match reason with
     | P.DocumentRejected _ _ _ -> reason
     | P.DocumentChecked _ _ -> P.DocumentRejected P.ProofEntry None None)
  | P.EntriesChecked cache pending unmet ->
    (match I.index_find cache doc.root with
     | None -> P.DocumentRejected P.MissingRoot None None
     | Some fact ->
       if fact.conclusion = U.Holds R.false_expr && fact.hypotheses = []
       then P.DocumentChecked pending unmet else P.DocumentRejected P.OpenRoot None None)

let diagnostic_result (d:P.document_diagnostic) : option nat =
  match d with P.DocumentChecked n _ -> Some n | P.DocumentRejected _ _ _ -> None

let lemma_diagnose_document (schema:S.schema) (doc:P.document)
  : Lemma (diagnostic_result (diagnose_document schema doc) == check_document schema doc) =
  if S.valid schema && boolean_expressions schema doc.assertions && U.ordinary_facts doc.assertions
  then (
    lemma_diagnose_entries schema doc.assertions I.Empty 0 0 [] doc.entries;
    match diagnose_entries schema doc.assertions I.Empty 0 0 [] doc.entries with
    | P.EntriesRejected reason ->
      (match reason with P.DocumentRejected _ _ _ | P.DocumentChecked _ _ -> ())
    | P.EntriesChecked cache _ _ ->
      (match I.index_find cache doc.root with None -> () | Some _ -> ()))
