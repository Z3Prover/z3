module Z3IndependentFiniteFieldCompactReplay

module FF = Z3SortedFiniteField
module IX = Z3ProofIndex
module Monomial = Z3IndependentFiniteFieldMonomial
module Polynomial = Z3IndependentFiniteFieldPolynomial
module Step = Z3IndependentFiniteFieldCompactStep

let initial : state = { values = IX.Empty; next = 0 }

let earlier (s:state) (j:int) : Tot (option Polynomial.compact) =
  if 0 <= j && j < s.next then IX.index_get s.values j else None

let record (s:state) (q:Polynomial.compact) : Tot state =
  { values = IX.index_put s.values s.next q; next = s.next + 1 }

let input (p:pos) (s:state) (q:FF.poly) : Tot (option state) =
  if Polynomial.sorted_monomials q
  then Some (record s (Polynomial.normalize p (Polynomial.compress q)))
  else None

let add (p:pos) (s:state) (a b:int) : Tot (option state) =
  match earlier s a, earlier s b with
  | Some qa, Some qb -> Some (record s (Polynomial.normalize p (Polynomial.add qa qb)))
  | _, _ -> None

let scale (p:pos) (s:state) (source:int) (m:Monomial.compact) (c:int) : Tot (option state) =
  if not (Monomial.ordered m) then None
  else match earlier s source with
  | Some q -> Some (record s (Polynomial.normalize p (Polynomial.scale_mono m c q)))
  | None -> None

let unit_root (s:state) (root:int) : Tot bool =
  0 <= root && root < s.next && IX.index_get s.values root = Some [([], 1)]

let values_ok (v:nat -> int) (p:pos) (s:state) : GTot prop =
  forall (j:nat).
    match IX.index_get s.values j with
    | Some q -> Polynomial.canonical_monomials q /\ Polynomial.evaluate v q % p == 0
    | None -> True

let lemma_initial (v:nat -> int) (p:pos) : Lemma (values_ok v p initial) = ()

let lemma_record (v:nat -> int) (p:pos) (s:state) (q:Polynomial.compact)
  : Lemma (requires values_ok v p s /\ Polynomial.canonical_monomials q /\
                    Polynomial.evaluate v q % p == 0)
          (ensures values_ok v p (record s q)) =
  let aux (j:nat) : Lemma
    (match IX.index_get (record s q).values j with
     | Some x -> Polynomial.canonical_monomials x /\ Polynomial.evaluate v x % p == 0
     | None -> True) =
    IX.lemma_index_put s.values s.next q j
  in FStar.Classical.forall_intro aux

let lemma_input (v:nat -> int) (p:pos) (s s':state) (q:FF.poly)
  : Lemma (requires values_ok v p s /\ FF.peval v q % p == 0 /\ input p s q == Some s')
          (ensures values_ok v p s') =
  Step.lemma_input v p q;
  lemma_record v p s (Polynomial.normalize p (Polynomial.compress q))

let lemma_add (v:nat -> int) (p:pos) (s s':state) (a b:int)
  : Lemma (requires values_ok v p s /\ add p s a b == Some s')
          (ensures values_ok v p s') =
  let qa = Some?.v (earlier s a) in
  let qb = Some?.v (earlier s b) in
  assert (IX.index_get s.values a == Some qa);
  assert (IX.index_get s.values b == Some qb);
  Step.lemma_add v p qa qb;
  lemma_record v p s (Polynomial.normalize p (Polynomial.add qa qb))

let lemma_scale (v:nat -> int) (p:pos) (s s':state)
  (source:int) (m:Monomial.compact) (c:int)
  : Lemma (requires values_ok v p s /\ scale p s source m c == Some s')
          (ensures values_ok v p s') =
  let q = Some?.v (earlier s source) in
  assert (IX.index_get s.values source == Some q);
  Step.lemma_scale v p m c q;
  lemma_record v p s (Polynomial.normalize p (Polynomial.scale_mono m c q))

let lemma_unit_root (v:nat -> int) (p:int{p > 1}) (s:state) (root:int)
  : Lemma (requires values_ok v p s) (ensures not (unit_root s root)) =
  Polynomial.lemma_expand_empty ();
  Polynomial.lemma_expand_cons [] 1 [];
  Monomial.lemma_degree_empty ();
  Monomial.lemma_degree [];
  Polynomial.lemma_evaluate v [([], 1)];
  FF.lemma_peval_constant v 1

let lemma_earlier (s:state) (j:int)
  : Lemma (earlier s j ==
           (if 0 <= j && j < s.next then IX.index_get s.values j else None)) = ()

let lemma_index_record_values_ok (v:nat -> int) (p:pos) (s s':state) (q:Polynomial.compact)
  : Lemma (requires values_ok v p s /\ Polynomial.canonical_monomials q /\
                    Polynomial.evaluate v q % p == 0 /\
                    s'.values == IX.index_put s.values s.next q)
          (ensures values_ok v p s') =
  lemma_record v p s q

let lemma_input_description (p:pos) (s:state) (q:FF.poly)
  : Lemma (input p s q ==
           (if Polynomial.sorted_monomials q
            then Some { values = IX.index_put s.values s.next
                                   (Polynomial.normalize p (Polynomial.compress q));
                        next = s.next + 1 }
            else None)) = ()

let lemma_add_description (p:pos) (s:state) (a b:int)
  : Lemma (add p s a b ==
           (match earlier s a, earlier s b with
            | Some qa, Some qb ->
              Some { values = IX.index_put s.values s.next
                                     (Polynomial.normalize p (Polynomial.add qa qb));
                     next = s.next + 1 }
            | _, _ -> None)) = ()

let lemma_scale_description (p:pos) (s:state) (source:int) (m:Monomial.compact) (c:int)
  : Lemma (scale p s source m c ==
           (if not (Monomial.ordered m) then None
            else match earlier s source with
                 | None -> None
                 | Some q ->
                   Some { values = IX.index_put s.values s.next
                                          (Polynomial.normalize p (Polynomial.scale_mono m c q));
                          next = s.next + 1 })) = ()

let lemma_unit_root_description (s:state) (root:int)
  : Lemma (unit_root s root ==
           (0 <= root && root < s.next && IX.index_get s.values root = Some [([], 1)])) = ()
