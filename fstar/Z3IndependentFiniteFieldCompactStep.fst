module Z3IndependentFiniteFieldCompactStep

module FF = Z3SortedFiniteField
module Monomial = Z3IndependentFiniteFieldMonomial
module Polynomial = Z3IndependentFiniteFieldPolynomial

let lemma_input (v:nat -> int) (p:pos) (q:FF.poly)
  : Lemma (requires Polynomial.sorted_monomials q /\ FF.peval v q % p == 0)
          (ensures Polynomial.canonical_monomials (Polynomial.normalize p (Polynomial.compress q)) /\
                   Polynomial.evaluate v (Polynomial.normalize p (Polynomial.compress q)) % p == 0) =
  let x = Polynomial.compress q in
  Polynomial.lemma_compress_canonical q;
  Polynomial.lemma_expand_compress q;
  Polynomial.lemma_evaluate v x;
  Polynomial.lemma_normalize_canonical p x;
  Polynomial.lemma_normalize_evaluate v p x

let lemma_add (v:nat -> int) (p:pos) (a b:Polynomial.compact)
  : Lemma (requires Polynomial.canonical_monomials a /\ Polynomial.canonical_monomials b /\
                    Polynomial.evaluate v a % p == 0 /\ Polynomial.evaluate v b % p == 0)
          (ensures Polynomial.canonical_monomials (Polynomial.normalize p (Polynomial.add a b)) /\
                   Polynomial.evaluate v (Polynomial.normalize p (Polynomial.add a b)) % p == 0) =
  let q = Polynomial.add a b in
  Polynomial.lemma_add_canonical a b;
  Polynomial.lemma_add_evaluate v a b;
  FF.lemma_zero_sum p (Polynomial.evaluate v a) (Polynomial.evaluate v b);
  Polynomial.lemma_normalize_canonical p q;
  Polynomial.lemma_normalize_evaluate v p q

let lemma_scale (v:nat -> int) (p:pos) (m:Monomial.compact) (c:int) (q:Polynomial.compact)
  : Lemma (requires Monomial.ordered m /\ Polynomial.canonical_monomials q /\
                    Polynomial.evaluate v q % p == 0)
          (ensures Polynomial.canonical_monomials (Polynomial.normalize p (Polynomial.scale_mono m c q)) /\
                   Polynomial.evaluate v (Polynomial.normalize p (Polynomial.scale_mono m c q)) % p == 0) =
  let x = Polynomial.scale_mono m c q in
  Polynomial.lemma_scale_canonical m c q;
  Polynomial.lemma_scale_evaluate v m c q;
  FF.lemma_zero_product p (c * Monomial.evaluate v m) (Polynomial.evaluate v q);
  Polynomial.lemma_normalize_canonical p x;
  Polynomial.lemma_normalize_evaluate v p x
