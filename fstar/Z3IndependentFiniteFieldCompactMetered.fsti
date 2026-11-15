module Z3IndependentFiniteFieldCompactMetered

module Index = Z3IndependentProofIndex
module Polynomial = Z3IndependentFiniteFieldPolynomial
module Replay = Z3IndependentFiniteFieldCompactReplay
module IX = Z3ProofIndex
module FF = Z3SortedFiniteField
module Monomial = Z3IndependentFiniteFieldMonomial

val earlier_bound (s:Replay.state) (j:int) : Tot pos
val earlier_metered (fuel:nat) (s:Replay.state) (j:int)
  : Tot (option (option Polynomial.compact & nat))
val lemma_earlier_metered (fuel:nat) (s:Replay.state) (j:int)
  : Lemma (match earlier_metered fuel s j with
           | None -> fuel < earlier_bound s j
           | Some (result, work) ->
             result == Replay.earlier s j /\ 0 < work /\
             work <= fuel /\ work <= earlier_bound s j)
val record_metered (fuel:nat) (s:Replay.state) (q:Polynomial.compact)
  : Tot (option (Replay.state & nat))
val lemma_record_metered (fuel:nat) (s:Replay.state) (q:Polynomial.compact)
  : Lemma (match record_metered fuel s q with
           | None -> fuel < Index.depth s.next
           | Some (result, work) ->
             result.values == IX.index_put s.values s.next q /\
             result.next == s.next + 1 /\
             work == Index.depth s.next /\ work <= fuel)
val lemma_record_values_ok (v:nat -> int) (p:pos) (fuel:nat)
  (s s':Replay.state) (q:Polynomial.compact) (work:nat)
  : Lemma (requires Replay.values_ok v p s /\ Polynomial.canonical_monomials q /\
                    Polynomial.evaluate v q % p == 0 /\
                    record_metered fuel s q == Some (s', work))
          (ensures Replay.values_ok v p s')
val input_bound (s:Replay.state) (q:FF.poly) : Tot nat
val input_metered (fuel:nat) (p:pos) (s:Replay.state) (q:FF.poly)
  : Tot (option (option Replay.state & nat))
val lemma_input_metered (fuel:nat) (p:pos) (s:Replay.state) (q:FF.poly)
  : Lemma (match input_metered fuel p s q with
           | None -> fuel < input_bound s q
           | Some (result, work) ->
             result == Replay.input p s q /\ 0 < work /\
             work <= fuel /\ work <= input_bound s q)
val lemma_input_values_ok (v:nat -> int) (p:pos) (fuel:nat)
  (s s':Replay.state) (q:FF.poly) (work:nat)
  : Lemma (requires Replay.values_ok v p s /\ FF.peval v q % p == 0 /\
                    input_metered fuel p s q == Some (Some s', work))
          (ensures Replay.values_ok v p s')
val add_bound (s:Replay.state) (a b:int) : GTot nat
val add_metered (fuel:nat) (p:pos) (s:Replay.state) (a b:int)
  : Tot (option (option Replay.state & nat))
val lemma_add_metered (fuel:nat) (p:pos) (s:Replay.state) (a b:int)
  : Lemma (match add_metered fuel p s a b with
           | None -> fuel < add_bound s a b
           | Some (result, work) ->
             result == Replay.add p s a b /\ 0 < work /\
             work <= fuel /\ work <= add_bound s a b)
val lemma_add_values_ok (v:nat -> int) (p:pos) (fuel:nat)
  (s s':Replay.state) (a b:int) (work:nat)
  : Lemma (requires Replay.values_ok v p s /\
                    add_metered fuel p s a b == Some (Some s', work))
          (ensures Replay.values_ok v p s')
val scale_bound (s:Replay.state) (source:int) (m:Monomial.compact) : GTot nat
val scale_metered (fuel:nat) (p:pos) (s:Replay.state) (source:int) (m:Monomial.compact) (c:int)
  : Tot (option (option Replay.state & nat))
val lemma_scale_metered (fuel:nat) (p:pos) (s:Replay.state) (source:int)
  (m:Monomial.compact) (c:int)
  : Lemma (match scale_metered fuel p s source m c with
           | None -> fuel < scale_bound s source m
           | Some (result, work) ->
             result == Replay.scale p s source m c /\ 0 < work /\
             work <= fuel /\ work <= scale_bound s source m)
val lemma_scale_values_ok (v:nat -> int) (p:pos) (fuel:nat)
  (s s':Replay.state) (source:int) (m:Monomial.compact) (c:int) (work:nat)
  : Lemma (requires Replay.values_ok v p s /\
                    scale_metered fuel p s source m c == Some (Some s', work))
          (ensures Replay.values_ok v p s')
