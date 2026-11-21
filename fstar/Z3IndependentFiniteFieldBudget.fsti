module Z3IndependentFiniteFieldBudget

module FF = Z3SortedFiniteField
module Polynomial = Z3IndependentFiniteFieldPolynomial

val compact_weight (q:Polynomial.compact) : Tot nat
val expanded_weight (q:Polynomial.compact) : Tot nat
val degrees_bounded (limit:nat) (q:Polynomial.compact) : Tot bool
val coefficients_bounded (limit:nat) (q:Polynomial.compact) : Tot bool
val check (weight_limit degree_limit:nat) (q:Polynomial.compact)
  : Tot (ok:bool{ok ==> compact_weight q <= weight_limit /\ degrees_bounded degree_limit q})
val check_resources (weight_limit degree_limit coefficient_limit:nat) (q:Polynomial.compact)
  : Tot (ok:bool{ok ==> compact_weight q <= weight_limit /\ degrees_bounded degree_limit q /\
                        coefficients_bounded coefficient_limit q})

val lemma_check_complete (weight_limit degree_limit:nat) (q:Polynomial.compact)
  : Lemma (requires compact_weight q <= weight_limit /\ degrees_bounded degree_limit q)
          (ensures check weight_limit degree_limit q)
val lemma_check_resources_complete (weight_limit degree_limit coefficient_limit:nat)
  (q:Polynomial.compact)
  : Lemma (requires compact_weight q <= weight_limit /\ degrees_bounded degree_limit q /\
                    coefficients_bounded coefficient_limit q)
          (ensures check_resources weight_limit degree_limit coefficient_limit q)
val lemma_expanded_weight (q:Polynomial.compact)
  : Lemma (expanded_weight q == FF.poly_size (Polynomial.expand q) /\
           compact_weight q <= expanded_weight q)
