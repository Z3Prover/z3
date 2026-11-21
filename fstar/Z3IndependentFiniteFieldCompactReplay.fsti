module Z3IndependentFiniteFieldCompactReplay

module FF = Z3SortedFiniteField
module IX = Z3ProofIndex
module Monomial = Z3IndependentFiniteFieldMonomial
module Polynomial = Z3IndependentFiniteFieldPolynomial

noeq
type state = {
  values: IX.index_tree Polynomial.compact;
  next: nat;
}

val initial : state
val earlier (s:state) (j:int) : Tot (option Polynomial.compact)
val input (p:pos) (s:state) (q:FF.poly) : Tot (option state)
val add (p:pos) (s:state) (a b:int) : Tot (option state)
val scale (p:pos) (s:state) (source:int) (m:Monomial.compact) (c:int) : Tot (option state)
val unit_root (s:state) (root:int) : Tot bool

val values_ok (v:nat -> int) (p:pos) (s:state) : GTot prop
val lemma_initial (v:nat -> int) (p:pos) : Lemma (values_ok v p initial)
val lemma_input (v:nat -> int) (p:pos) (s s':state) (q:FF.poly)
  : Lemma (requires values_ok v p s /\ FF.peval v q % p == 0 /\ input p s q == Some s')
          (ensures values_ok v p s')
val lemma_add (v:nat -> int) (p:pos) (s s':state) (a b:int)
  : Lemma (requires values_ok v p s /\ add p s a b == Some s')
          (ensures values_ok v p s')
val lemma_scale (v:nat -> int) (p:pos) (s s':state)
  (source:int) (m:Monomial.compact) (c:int)
  : Lemma (requires values_ok v p s /\ scale p s source m c == Some s')
          (ensures values_ok v p s')
val lemma_unit_root (v:nat -> int) (p:int{p > 1}) (s:state) (root:int)
  : Lemma (requires values_ok v p s) (ensures not (unit_root s root))
val lemma_earlier (s:state) (j:int)
  : Lemma (earlier s j ==
           (if 0 <= j && j < s.next then IX.index_get s.values j else None))
val lemma_index_record_values_ok (v:nat -> int) (p:pos) (s s':state) (q:Polynomial.compact)
  : Lemma (requires values_ok v p s /\ Polynomial.canonical_monomials q /\
                    Polynomial.evaluate v q % p == 0 /\
                    s'.values == IX.index_put s.values s.next q)
          (ensures values_ok v p s')
val lemma_input_description (p:pos) (s:state) (q:FF.poly)
  : Lemma (input p s q ==
           (if Polynomial.sorted_monomials q
            then Some { values = IX.index_put s.values s.next
                                   (Polynomial.normalize p (Polynomial.compress q));
                        next = s.next + 1 }
            else None))
val lemma_add_description (p:pos) (s:state) (a b:int)
  : Lemma (add p s a b ==
           (match earlier s a, earlier s b with
            | Some qa, Some qb ->
              Some { values = IX.index_put s.values s.next
                                     (Polynomial.normalize p (Polynomial.add qa qb));
                     next = s.next + 1 }
            | _, _ -> None))
val lemma_scale_description (p:pos) (s:state) (source:int) (m:Monomial.compact) (c:int)
  : Lemma (scale p s source m c ==
           (if not (Monomial.ordered m) then None
            else match earlier s source with
                 | None -> None
                 | Some q ->
                   Some { values = IX.index_put s.values s.next
                                          (Polynomial.normalize p (Polynomial.scale_mono m c q));
                          next = s.next + 1 }))
val lemma_unit_root_description (s:state) (root:int)
  : Lemma (unit_root s root ==
           (0 <= root && root < s.next && IX.index_get s.values root = Some [([], 1)]))
