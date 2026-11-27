module Z3IndependentFiniteFieldBudget

module FF = Z3SortedFiniteField
module Polynomial = Z3IndependentFiniteFieldPolynomial
module Monomial = Z3IndependentFiniteFieldMonomial
module L = FStar.List.Tot

let compact_weight (q:Polynomial.compact) : Tot nat =
  Polynomial.compact_weight q

let rec expanded_weight (q:Polynomial.compact) : Tot nat (decreases q) =
  match q with
  | [] -> 0
  | (m, _) :: rest -> 1 + Monomial.degree m + expanded_weight rest

let degrees_bounded (limit:nat) (q:Polynomial.compact) : Tot bool =
  Polynomial.degrees_bounded limit q

let coefficients_bounded (limit:nat) (q:Polynomial.compact) : Tot bool =
  Polynomial.coefficients_bounded limit q

let rec consume_monomial (m:Monomial.compact) (weight degree:nat)
  : Tot (r:option nat{match r with
      | None -> True
      | Some left -> left + L.length m == weight /\ Monomial.degree m <= degree})
        (decreases m) =
  match m with
  | [] -> Monomial.lemma_degree_empty (); Some weight
  | (x, n) :: rest ->
    Monomial.lemma_degree_cons x n rest;
    if weight = 0 || n > degree then None
    else consume_monomial rest (weight - 1) (degree - n)

let rec consume (q:Polynomial.compact) (weight degree:nat)
  : Tot (r:option nat{match r with
      | None -> True
      | Some left -> left + compact_weight q == weight /\ degrees_bounded degree q})
        (decreases q) =
  match q with
  | [] -> Some weight
  | (m, _) :: rest ->
    if weight = 0 then None
    else
      (match consume_monomial m (weight - 1) degree with
       | None -> None
       | Some left -> consume rest left degree)

let check (weight_limit degree_limit:nat) (q:Polynomial.compact)
  : Tot (ok:bool{ok ==> compact_weight q <= weight_limit /\ degrees_bounded degree_limit q}) =
  Some? (consume q weight_limit degree_limit)

let rec consume_coefficients (q:Polynomial.compact) (fuel limit:nat)
  : Tot (r:option nat{match r with
      | None -> True
      | Some left -> left + L.length q == fuel /\ coefficients_bounded limit q})
        (decreases q) =
  match q with
  | [] -> Some fuel
  | (_, c) :: rest ->
    if fuel = 0 || c < -limit || c > limit then None
    else consume_coefficients rest (fuel - 1) limit

let check_resources (weight_limit degree_limit coefficient_limit:nat) (q:Polynomial.compact)
  : Tot (ok:bool{ok ==> compact_weight q <= weight_limit /\ degrees_bounded degree_limit q /\
                        coefficients_bounded coefficient_limit q}) =
  check weight_limit degree_limit q &&
  Some? (consume_coefficients q weight_limit coefficient_limit)

let rec lemma_consume_monomial_complete (m:Monomial.compact) (weight degree:nat)
  : Lemma (requires L.length m <= weight /\ Monomial.degree m <= degree)
          (ensures Some? (consume_monomial m weight degree))
          (decreases m) =
  match m with
  | [] -> ()
  | (x, n) :: rest ->
    Monomial.lemma_degree_cons x n rest;
    lemma_consume_monomial_complete rest (weight - 1) (degree - n)

let rec lemma_consume_complete (q:Polynomial.compact) (weight degree:nat)
  : Lemma (requires compact_weight q <= weight /\ degrees_bounded degree q)
          (ensures Some? (consume q weight degree))
          (decreases q) =
  match q with
  | [] -> ()
  | (m, _) :: rest ->
    lemma_consume_monomial_complete m (weight - 1) degree;
    (match consume_monomial m (weight - 1) degree with
     | None -> ()
     | Some left -> lemma_consume_complete rest left degree)

let lemma_check_complete (weight_limit degree_limit:nat) (q:Polynomial.compact)
  : Lemma (requires compact_weight q <= weight_limit /\ degrees_bounded degree_limit q)
          (ensures check weight_limit degree_limit q) =
  lemma_consume_complete q weight_limit degree_limit

let rec lemma_weight_covers_terms (q:Polynomial.compact)
  : Lemma (L.length q <= compact_weight q) (decreases q) =
  match q with
  | [] -> ()
  | _ :: rest -> lemma_weight_covers_terms rest

let rec lemma_consume_coefficients_complete (q:Polynomial.compact) (fuel limit:nat)
  : Lemma (requires L.length q <= fuel /\ coefficients_bounded limit q)
          (ensures Some? (consume_coefficients q fuel limit))
          (decreases q) =
  match q with
  | [] -> ()
  | _ :: rest -> lemma_consume_coefficients_complete rest (fuel - 1) limit

let lemma_check_resources_complete (weight_limit degree_limit coefficient_limit:nat)
  (q:Polynomial.compact)
  : Lemma (requires compact_weight q <= weight_limit /\ degrees_bounded degree_limit q /\
                    coefficients_bounded coefficient_limit q)
          (ensures check_resources weight_limit degree_limit coefficient_limit q) =
  lemma_check_complete weight_limit degree_limit q;
  lemma_weight_covers_terms q;
  lemma_consume_coefficients_complete q weight_limit coefficient_limit

let rec lemma_expanded_weight (q:Polynomial.compact)
  : Lemma (expanded_weight q == FF.poly_size (Polynomial.expand q) /\
           compact_weight q <= expanded_weight q)
          (decreases q) =
  match q with
  | [] -> Polynomial.lemma_expand_empty ()
  | (m, c) :: rest ->
    Polynomial.lemma_expand_cons m c rest;
    Monomial.lemma_degree m;
    lemma_expanded_weight rest
