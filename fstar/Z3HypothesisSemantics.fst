module Z3HypothesisSemantics

open Z3AstTheory
open Z3UnifiedProofSyntax
module C = Z3ClausalSemantics
module R = Z3ClauseSyntax
module L = FStar.List.Tot

let rec lemma_union (rho:C.valuation) (xs ys:list expr)
  : Lemma (requires C.conj_holds rho (add_hypotheses xs ys))
          (ensures C.conj_holds rho xs /\ C.conj_holds rho ys)
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest ->
    if L.mem x ys then (
      lemma_union rho rest ys;
      FStar.List.Tot.Properties.mem_memP x ys;
      C.lemma_conj_member rho ys x)
    else lemma_union rho rest (x :: ys)

let fact_holds (rho:C.valuation) (holds:judgment -> prop) (p:checked_fact) : prop =
  C.conj_holds rho p.hypotheses ==> holds p.conclusion

let rec facts_hold (rho:C.valuation) (holds:judgment -> prop) (ps:list checked_fact)
  : Tot prop (decreases ps) =
  match ps with
  | [] -> True
  | p :: rest -> fact_holds rho holds p /\ facts_hold rho holds rest

let rec judgments_hold (holds:judgment -> prop) (js:list judgment)
  : Tot prop (decreases js) =
  match js with
  | [] -> True
  | j :: rest -> holds j /\ judgments_hold holds rest

let rec lemma_premises (rho:C.valuation) (holds:judgment -> prop) (ps:list checked_fact)
  : Lemma (requires facts_hold rho holds ps /\ C.conj_holds rho (premise_hypotheses ps))
          (ensures judgments_hold holds (premise_judgments ps))
          (decreases ps) =
  match ps with
  | [] -> ()
  | p :: rest ->
    lemma_union rho p.hypotheses (premise_hypotheses rest);
    lemma_premises rho holds rest

let rec valid_list (valid:expr -> Tot bool) (es:list expr) : GTot bool (decreases es) =
  match es with
  | [] -> true
  | e :: rest -> valid e && valid_list valid rest

let rec lemma_valid_union (valid:expr -> Tot bool) (xs ys:list expr)
  : Lemma (requires valid_list valid xs /\ valid_list valid ys)
          (ensures valid_list valid (add_hypotheses xs ys))
          (decreases xs) =
  match xs with
  | [] -> ()
  | x :: rest ->
    if L.mem x ys then lemma_valid_union valid rest ys
    else lemma_valid_union valid rest (x :: ys)

let rec lemma_valid_premises (valid:expr -> Tot bool) (ps:list checked_fact)
  : Lemma (requires (forall (p:checked_fact). L.mem p ps ==> valid_list valid p.hypotheses))
          (ensures valid_list valid (premise_hypotheses ps))
          (decreases ps) =
  match ps with
  | [] -> ()
  | p :: rest ->
    lemma_valid_premises valid rest;
    lemma_valid_union valid p.hypotheses (premise_hypotheses rest)

let rec lemma_valid_remaining (valid:expr -> Tot bool) (hyps:list expr) (concl:expr)
  : Lemma (requires valid_list valid hyps)
          (ensures valid_list valid (remaining_hypotheses hyps concl))
          (decreases hyps) =
  match hyps with
  | [] -> ()
  | _ :: rest -> lemma_valid_remaining valid rest concl

let complements_from_false (rho:C.valuation) (valid:expr -> Tot bool) : prop =
  forall (a b:expr). valid a /\ valid b /\ C.complementary a b /\ not (rho b) ==> rho a

let clause_from_formula (rho:C.valuation) (valid:expr -> Tot bool) : prop =
  forall (e:expr). valid e /\ not (rho e) ==> not (C.clause_holds rho (R.formula_clause e))

let rec lemma_discharged (rho:C.valuation) (valid:expr -> Tot bool)
                         (h:expr) (es:list expr)
  : Lemma (requires complements_from_false rho valid /\ valid h /\ valid_list valid es /\
                    discharged h es /\ not (C.clause_holds rho es))
          (ensures rho h)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    if C.complementary h e then ()
    else lemma_discharged rho valid h rest

let rec lemma_remaining (rho:C.valuation) (valid:expr -> Tot bool) (hyps:list expr) (concl:expr)
  : Lemma (requires complements_from_false rho valid /\ clause_from_formula rho valid /\
                    valid_list valid hyps /\ valid concl /\ valid_list valid (R.formula_clause concl) /\
                    C.conj_holds rho (remaining_hypotheses hyps concl) /\ not (rho concl))
          (ensures C.conj_holds rho hyps)
          (decreases hyps) =
  match hyps with
  | [] -> ()
  | h :: rest ->
    if C.complementary h concl then ()
    else if discharged h (R.formula_clause concl) then
      lemma_discharged rho valid h (R.formula_clause concl);
    lemma_remaining rho valid rest concl
