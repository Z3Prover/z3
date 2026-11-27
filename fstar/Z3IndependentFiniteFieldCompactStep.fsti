module Z3IndependentFiniteFieldCompactStep

module FF = Z3SortedFiniteField
module Monomial = Z3IndependentFiniteFieldMonomial
module Polynomial = Z3IndependentFiniteFieldPolynomial

val lemma_input (v:nat -> int) (p:pos) (q:FF.poly)
  : Lemma (requires Polynomial.sorted_monomials q /\ FF.peval v q % p == 0)
          (ensures Polynomial.canonical_monomials (Polynomial.normalize p (Polynomial.compress q)) /\
                   Polynomial.evaluate v (Polynomial.normalize p (Polynomial.compress q)) % p == 0)

val lemma_add (v:nat -> int) (p:pos) (a b:Polynomial.compact)
  : Lemma (requires Polynomial.canonical_monomials a /\ Polynomial.canonical_monomials b /\
                    Polynomial.evaluate v a % p == 0 /\ Polynomial.evaluate v b % p == 0)
          (ensures Polynomial.canonical_monomials (Polynomial.normalize p (Polynomial.add a b)) /\
                   Polynomial.evaluate v (Polynomial.normalize p (Polynomial.add a b)) % p == 0)

val lemma_scale (v:nat -> int) (p:pos) (m:Monomial.compact) (c:int) (q:Polynomial.compact)
  : Lemma (requires Monomial.ordered m /\ Polynomial.canonical_monomials q /\
                    Polynomial.evaluate v q % p == 0)
          (ensures Polynomial.canonical_monomials (Polynomial.normalize p (Polynomial.scale_mono m c q)) /\
                   Polynomial.evaluate v (Polynomial.normalize p (Polynomial.scale_mono m c q)) % p == 0)
