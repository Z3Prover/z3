module Z3IndependentFiniteFieldCompactMetered

module Index = Z3IndependentProofIndex
module Polynomial = Z3IndependentFiniteFieldPolynomial
module Replay = Z3IndependentFiniteFieldCompactReplay
module IX = Z3ProofIndex
module FF = Z3SortedFiniteField
module Monomial = Z3IndependentFiniteFieldMonomial
module L = FStar.List.Tot

let earlier_bound (s:Replay.state) (j:int) : Tot pos =
  if 0 <= j && j < s.next then 1 + Index.depth j else 1

let earlier_metered (fuel:nat) (s:Replay.state) (j:int)
  : Tot (option (option Polynomial.compact & nat)) =
  if fuel = 0 then None
  else if j < 0 || j >= s.next then Some (None, 1)
  else
    match Index.get_metered (fuel - 1) s.values j with
    | None -> None
    | Some (result, work) -> Some (result, work + 1)

let lemma_earlier_metered (fuel:nat) (s:Replay.state) (j:int)
  : Lemma (match earlier_metered fuel s j with
           | None -> fuel < earlier_bound s j
           | Some (result, work) ->
             result == Replay.earlier s j /\ 0 < work /\
             work <= fuel /\ work <= earlier_bound s j) =
  Replay.lemma_earlier s j;
  if fuel > 0 && 0 <= j && j < s.next then
    Index.lemma_get_metered (fuel - 1) s.values j

let record_metered (fuel:nat) (s:Replay.state) (q:Polynomial.compact)
  : Tot (option (Replay.state & nat)) =
  match Index.put_metered fuel s.values s.next q with
  | None -> None
  | Some (values, work) ->
    Some ({ Replay.values = values; Replay.next = s.next + 1 }, work)

let lemma_record_metered (fuel:nat) (s:Replay.state) (q:Polynomial.compact)
  : Lemma (match record_metered fuel s q with
           | None -> fuel < Index.depth s.next
           | Some (result, work) ->
             result.values == IX.index_put s.values s.next q /\
             result.next == s.next + 1 /\
             work == Index.depth s.next /\ work <= fuel) =
  Index.lemma_put_metered fuel s.values s.next q

let lemma_record_values_ok (v:nat -> int) (p:pos) (fuel:nat)
  (s s':Replay.state) (q:Polynomial.compact) (work:nat)
  : Lemma (requires Replay.values_ok v p s /\ Polynomial.canonical_monomials q /\
                    Polynomial.evaluate v q % p == 0 /\
                    record_metered fuel s q == Some (s', work))
          (ensures Replay.values_ok v p s') =
  lemma_record_metered fuel s q;
  Replay.lemma_index_record_values_ok v p s s' q

let input_bound (s:Replay.state) (q:FF.poly) : Tot nat =
  Polynomial.input_prepare_guarded_bound q + Index.depth s.next

let input_metered (fuel:nat) (p:pos) (s:Replay.state) (q:FF.poly)
  : Tot (option (option Replay.state & nat)) =
  Polynomial.lemma_input_prepare_guarded_metered fuel p q;
  match Polynomial.input_prepare_guarded_metered fuel p q with
  | None -> None
  | Some (None, work) -> Some (None, work)
  | Some (Some prepared, work) ->
    match record_metered (fuel - work) s prepared with
    | None -> None
    | Some (result, record_work) -> Some (Some result, work + record_work)

let lemma_input_metered (fuel:nat) (p:pos) (s:Replay.state) (q:FF.poly)
  : Lemma (match input_metered fuel p s q with
           | None -> fuel < input_bound s q
           | Some (result, work) ->
             result == Replay.input p s q /\ 0 < work /\
             work <= fuel /\ work <= input_bound s q) =
  Polynomial.lemma_input_prepare_guarded_metered fuel p q;
  Replay.lemma_input_description p s q;
  match Polynomial.input_prepare_guarded_metered fuel p q with
  | Some (Some prepared, work) ->
    lemma_record_metered (fuel - work) s prepared
  | _ -> ()

let lemma_input_values_ok (v:nat -> int) (p:pos) (fuel:nat)
  (s s':Replay.state) (q:FF.poly) (work:nat)
  : Lemma (requires Replay.values_ok v p s /\ FF.peval v q % p == 0 /\
                    input_metered fuel p s q == Some (Some s', work))
          (ensures Replay.values_ok v p s') =
  lemma_input_metered fuel p s q;
  Replay.lemma_input v p s s' q

let add_bound (s:Replay.state) (a b:int) : GTot nat =
  earlier_bound s a + earlier_bound s b + Index.depth s.next +
  (match Replay.earlier s a, Replay.earlier s b with
   | Some qa, Some qb -> Polynomial.add_guarded_normalize_bound qa qb
   | _, _ -> 0)

let add_metered (fuel:nat) (p:pos) (s:Replay.state) (a b:int)
  : Tot (option (option Replay.state & nat)) =
  lemma_earlier_metered fuel s a;
  match earlier_metered fuel s a with
  | None -> None
  | Some (None, wa) -> Some (None, wa)
  | Some (Some qa, wa) ->
    let f1 = fuel - wa in
    lemma_earlier_metered f1 s b;
    match earlier_metered f1 s b with
    | None -> None
    | Some (None, wb) -> Some (None, wa + wb)
    | Some (Some qb, wb) ->
      let f2 = f1 - wb in
      Polynomial.lemma_add_guarded_normalize_metered f2 p qa qb;
      match Polynomial.add_guarded_normalize_metered f2 p qa qb with
      | None -> None
      | Some (result, wp) ->
        match record_metered (f2 - wp) s result with
        | None -> None
        | Some (s', wr) -> Some (Some s', wa + wb + wp + wr)

let lemma_add_metered (fuel:nat) (p:pos) (s:Replay.state) (a b:int)
  : Lemma (match add_metered fuel p s a b with
           | None -> fuel < add_bound s a b
           | Some (result, work) ->
             result == Replay.add p s a b /\ 0 < work /\
             work <= fuel /\ work <= add_bound s a b) =
  Replay.lemma_add_description p s a b;
  lemma_earlier_metered fuel s a;
  match earlier_metered fuel s a with
  | Some (Some qa, wa) ->
    let f1 = fuel - wa in
    lemma_earlier_metered f1 s b;
    (match earlier_metered f1 s b with
     | Some (Some qb, wb) ->
       let f2 = f1 - wb in
       Polynomial.lemma_add_guarded_normalize_metered f2 p qa qb;
       (match Polynomial.add_guarded_normalize_metered f2 p qa qb with
        | Some (result, wp) -> lemma_record_metered (f2 - wp) s result
        | None -> ())
     | _ -> ())
  | _ -> ()

let lemma_add_values_ok (v:nat -> int) (p:pos) (fuel:nat)
  (s s':Replay.state) (a b:int) (work:nat)
  : Lemma (requires Replay.values_ok v p s /\
                    add_metered fuel p s a b == Some (Some s', work))
          (ensures Replay.values_ok v p s') =
  lemma_add_metered fuel p s a b;
  Replay.lemma_add v p s s' a b

let scale_bound (s:Replay.state) (source:int) (m:Monomial.compact) : GTot nat =
  L.length m + 1 + earlier_bound s source + Index.depth s.next +
  (if Monomial.ordered m then
     match Replay.earlier s source with
     | None -> 0
     | Some q -> Polynomial.scale_guarded_normalize_bound m q
   else 0)

let scale_metered (fuel:nat) (p:pos) (s:Replay.state) (source:int)
  (m:Monomial.compact) (c:int) : Tot (option (option Replay.state & nat)) =
  Monomial.lemma_ordered_metered fuel m;
  match Monomial.ordered_metered fuel m with
  | None -> None
  | Some (false, wm) -> Some (None, wm)
  | Some (true, wm) ->
    let f1 = fuel - wm in
    lemma_earlier_metered f1 s source;
    match earlier_metered f1 s source with
    | None -> None
    | Some (None, wq) -> Some (None, wm + wq)
    | Some (Some q, wq) ->
      let f2 = f1 - wq in
      Polynomial.lemma_scale_guarded_normalize_metered f2 p m c q;
      match Polynomial.scale_guarded_normalize_metered f2 p m c q with
      | None -> None
      | Some (result, wp) ->
        match record_metered (f2 - wp) s result with
        | None -> None
        | Some (s', wr) -> Some (Some s', wm + wq + wp + wr)

let lemma_scale_metered (fuel:nat) (p:pos) (s:Replay.state) (source:int)
  (m:Monomial.compact) (c:int)
  : Lemma (match scale_metered fuel p s source m c with
           | None -> fuel < scale_bound s source m
           | Some (result, work) ->
             result == Replay.scale p s source m c /\ 0 < work /\
             work <= fuel /\ work <= scale_bound s source m) =
  Replay.lemma_scale_description p s source m c;
  Monomial.lemma_ordered_metered fuel m;
  match Monomial.ordered_metered fuel m with
  | Some (true, wm) ->
    let f1 = fuel - wm in
    lemma_earlier_metered f1 s source;
    (match earlier_metered f1 s source with
     | Some (Some q, wq) ->
       let f2 = f1 - wq in
       Polynomial.lemma_scale_guarded_normalize_metered f2 p m c q;
       (match Polynomial.scale_guarded_normalize_metered f2 p m c q with
        | Some (result, wp) -> lemma_record_metered (f2 - wp) s result
        | None -> ())
     | _ -> ())
  | _ -> ()

let lemma_scale_values_ok (v:nat -> int) (p:pos) (fuel:nat)
  (s s':Replay.state) (source:int) (m:Monomial.compact) (c:int) (work:nat)
  : Lemma (requires Replay.values_ok v p s /\
                    scale_metered fuel p s source m c == Some (Some s', work))
          (ensures Replay.values_ok v p s') =
  lemma_scale_metered fuel p s source m c;
  Replay.lemma_scale v p s s' source m c
