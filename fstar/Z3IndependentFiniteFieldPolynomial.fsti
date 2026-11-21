module Z3IndependentFiniteFieldPolynomial

module FF = Z3SortedFiniteField
module Monomial = Z3IndependentFiniteFieldMonomial
module L = FStar.List.Tot

type compact = list (Monomial.compact & int)

let rec compact_weight (q:compact) : Tot nat (decreases q) =
  match q with
  | [] -> 0
  | (m, _) :: rest -> 1 + L.length m + compact_weight rest

let rec degrees_bounded (limit:nat) (q:compact) : Tot bool (decreases q) =
  match q with
  | [] -> true
  | (m, _) :: rest -> Monomial.degree m <= limit && degrees_bounded limit rest

let rec coefficients_bounded (limit:nat) (q:compact) : Tot bool (decreases q) =
  match q with
  | [] -> true
  | (_, c) :: rest -> -limit <= c && c <= limit && coefficients_bounded limit rest

val compress (q:FF.poly) : Tot compact
val expand (q:compact) : Tot FF.poly
val canonical_monomials (q:compact) : Tot bool
val sorted_monomials (q:FF.poly) : Tot bool
val evaluate (v:nat -> int) (q:compact) : Tot int
val add (a b:compact) : Tot compact
val scale_mono (m:Monomial.compact) (c:int) (q:compact) : Tot compact
val split (q:compact)
  : Tot (r:(compact & compact){L.length (fst r) + L.length (snd r) == L.length q /\
                                  (L.length q >= 2 ==>
                                   L.length (fst r) < L.length q /\
                                   L.length (snd r) < L.length q)})
val canon (q:compact) : Tot compact
val reduce (p:pos) (q:compact) : Tot compact
val normalize (p:pos) (q:compact) : Tot compact

val lemma_expand_empty () : Lemma (expand [] == [])
val lemma_expand_cons (m:Monomial.compact) (c:int) (rest:compact)
  : Lemma (expand ((m, c) :: rest) == (Monomial.expand m, c) :: expand rest)
val lemma_expand_compress (q:FF.poly) : Lemma (expand (compress q) == q)
val lemma_compress_canonical (q:FF.poly)
  : Lemma (requires sorted_monomials q) (ensures canonical_monomials (compress q))
val lemma_evaluate (v:nat -> int) (q:compact)
  : Lemma (evaluate v q == FF.peval v (expand q))
val lemma_add_canonical (a b:compact)
  : Lemma (requires canonical_monomials a /\ canonical_monomials b)
          (ensures canonical_monomials (add a b))
val lemma_add_structure (a b:compact)
  : Lemma (requires canonical_monomials a /\ canonical_monomials b)
          (ensures expand (add a b) == FF.padd (expand a) (expand b))
val lemma_add_evaluate (v:nat -> int) (a b:compact)
  : Lemma (requires canonical_monomials a /\ canonical_monomials b)
          (ensures evaluate v (add a b) == evaluate v a + evaluate v b)
val lemma_add_coefficients (a b:compact) (a_limit b_limit:nat)
  : Lemma (requires coefficients_bounded a_limit a /\ coefficients_bounded b_limit b)
          (ensures coefficients_bounded (a_limit + b_limit) (add a b))
val lemma_add_size (a b:compact)
  : Lemma (compact_weight (add a b) <= compact_weight a + compact_weight b /\
           L.length (add a b) <= L.length a + L.length b)
val lemma_add_degrees (a b:compact) (limit:nat)
  : Lemma (requires degrees_bounded limit a /\ degrees_bounded limit b)
          (ensures degrees_bounded limit (add a b))
val lemma_scale_canonical (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (requires Monomial.ordered m /\ canonical_monomials q)
          (ensures canonical_monomials (scale_mono m c q))
val lemma_scale_structure (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (requires Monomial.ordered m /\ canonical_monomials q)
          (ensures expand (scale_mono m c q) == FF.scale_mono (Monomial.expand m) c (expand q))
val lemma_scale_evaluate (v:nat -> int) (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (requires Monomial.ordered m /\ canonical_monomials q)
          (ensures evaluate v (scale_mono m c q) == (c * Monomial.evaluate v m) * evaluate v q)
val lemma_scale_coefficients (m:Monomial.compact) (c:int) (q:compact)
  (factor_limit coefficient_limit:nat)
  : Lemma (requires -factor_limit <= c /\ c <= factor_limit /\
                    coefficients_bounded coefficient_limit q)
          (ensures coefficients_bounded (factor_limit * coefficient_limit) (scale_mono m c q))
val lemma_scale_size (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (compact_weight (scale_mono m c q) <= compact_weight q + L.length q * L.length m /\
           L.length (scale_mono m c q) == L.length q)
val lemma_scale_degrees (m:Monomial.compact) (c:int) (q:compact) (limit:nat)
  : Lemma (requires degrees_bounded limit q)
          (ensures degrees_bounded (Monomial.degree m + limit) (scale_mono m c q))
val lemma_canon_size (q:compact)
  : Lemma (compact_weight (canon q) <= compact_weight q /\ L.length (canon q) <= L.length q)
val lemma_canon_degrees (q:compact) (limit:nat)
  : Lemma (requires degrees_bounded limit q) (ensures degrees_bounded limit (canon q))
val lemma_normalize_size (p:pos) (q:compact)
  : Lemma (compact_weight (normalize p q) <= compact_weight q /\
           L.length (normalize p q) <= L.length q)
val lemma_normalize_degrees (p:pos) (q:compact) (limit:nat)
  : Lemma (requires degrees_bounded limit q) (ensures degrees_bounded limit (normalize p q))
val lemma_canon_coefficients (q:compact) (limit:nat)
  : Lemma (requires coefficients_bounded limit q)
          (ensures coefficients_bounded (FStar.List.Tot.length q * limit) (canon q))
val lemma_normalize_coefficients (p:pos) (q:compact)
  : Lemma (coefficients_bounded (p - 1) (normalize p q))
val lemma_normalize_canonical (p:pos) (q:compact)
  : Lemma (requires canonical_monomials q)
          (ensures canonical_monomials (normalize p q))
val lemma_normalize_structure (p:pos) (q:compact)
  : Lemma (requires canonical_monomials q)
          (ensures expand (normalize p q) == FF.normalize p (expand q))
val lemma_normalize_evaluate (v:nat -> int) (p:pos) (q:compact)
  : Lemma (requires canonical_monomials q)
          (ensures evaluate v (normalize p q) % p == evaluate v q % p)
val add_metered (fuel:nat) (a b:compact) : Tot (option (compact & nat))
val lemma_add_metered (fuel:nat) (a b:compact)
  : Lemma (match add_metered fuel a b with
           | None -> True
           | Some (result, work) -> result == add a b /\ 0 < work /\ work <= fuel)
val lemma_add_metered_sufficient (fuel:nat) (a b:compact)
  : Lemma (requires fuel >= 1 + (L.length a + L.length b) *
                                  (3 + 2 * (compact_weight a + compact_weight b)))
          (ensures (match add_metered fuel a b with
                   | None -> False
                   | Some _ -> True))
val split_metered (fuel:nat) (q:compact) : Tot (option (compact & compact & nat))
val lemma_split_metered (fuel:nat) (q:compact)
  : Lemma (match split_metered fuel q with
           | None -> fuel < L.length q + 1
           | Some (a, b, work) ->
             (a, b) == split q /\ 0 < work /\ work <= fuel /\ work <= L.length q + 1)
val canon_metered (fuel:nat) (q:compact) : Tot (option (compact & nat))
val lemma_canon_metered (fuel:nat) (q:compact)
  : Lemma (match canon_metered fuel q with
           | None -> True
           | Some (result, work) -> result == canon q /\ 0 < work /\ work <= fuel)
val lemma_add_metered_work (fuel:nat) (a b:compact)
  : Lemma (match add_metered fuel a b with
           | None -> True
           | Some (_, work) ->
             work <= 1 + (L.length a + L.length b) *
                           (3 + 2 * (compact_weight a + compact_weight b)))
val canon_work_bound (terms width:nat) : Tot nat
val lemma_canon_metered_bound (fuel:nat) (q:compact)
  : Lemma (match canon_metered fuel q with
           | None -> fuel < canon_work_bound (L.length q) (compact_weight q)
           | Some (_, work) -> work <= canon_work_bound (L.length q) (compact_weight q))
val reduce_metered (fuel:nat) (p:pos) (q:compact) : Tot (option (compact & nat))
val lemma_reduce_metered (fuel:nat) (p:pos) (q:compact)
  : Lemma (match reduce_metered fuel p q with
           | None -> fuel < L.length q + 1
           | Some (result, work) ->
             result == reduce p q /\ work == L.length q + 1 /\ work <= fuel)
val normalize_metered (fuel:nat) (p:pos) (q:compact) : Tot (option (compact & nat))
val lemma_normalize_metered (fuel:nat) (p:pos) (q:compact)
  : Lemma (match normalize_metered fuel p q with
           | None -> fuel < canon_work_bound (L.length q) (compact_weight q) + L.length q + 1
           | Some (result, work) ->
             result == normalize p q /\ 0 < work /\ work <= fuel /\
             work <= canon_work_bound (L.length q) (compact_weight q) + L.length q + 1)
val scale_metered (fuel:nat) (m:Monomial.compact) (c:int) (q:compact)
  : Tot (option (compact & nat))
val lemma_scale_metered (fuel:nat) (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (match scale_metered fuel m c q with
           | None -> fuel < 1 + compact_weight q + L.length q * (1 + L.length m)
           | Some (result, work) ->
             result == scale_mono m c q /\ 0 < work /\ work <= fuel /\
             work <= 1 + compact_weight q + L.length q * (1 + L.length m))
val scale_normalize_bound (m:Monomial.compact) (q:compact) : Tot nat
val scale_normalize_metered (fuel:nat) (p:pos) (m:Monomial.compact) (c:int) (q:compact)
  : Tot (option (compact & nat))
val lemma_scale_normalize_metered
  (fuel:nat) (p:pos) (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (match scale_normalize_metered fuel p m c q with
           | None -> fuel < scale_normalize_bound m q
           | Some (result, work) ->
             result == normalize p (scale_mono m c q) /\ 0 < work /\ work <= fuel /\
             work <= scale_normalize_bound m q)
val add_normalize_bound (a b:compact) : Tot nat
val add_normalize_metered (fuel:nat) (p:pos) (a b:compact)
  : Tot (option (compact & nat))
val lemma_add_normalize_metered (fuel:nat) (p:pos) (a b:compact)
  : Lemma (match add_normalize_metered fuel p a b with
           | None -> fuel < add_normalize_bound a b
           | Some (result, work) ->
             result == normalize p (add a b) /\ 0 < work /\ work <= fuel /\
             work <= add_normalize_bound a b)
val compress_metered (fuel:nat) (q:FF.poly) : Tot (option (compact & nat))
val lemma_compress_metered (fuel:nat) (q:FF.poly)
  : Lemma (match compress_metered fuel q with
           | None -> fuel < 1 + FF.poly_size q + L.length q
           | Some (result, work) ->
             result == compress q /\ work == 1 + FF.poly_size q + L.length q /\ work <= fuel)
val sorted_monomials_metered (fuel:nat) (q:FF.poly) : Tot (option (bool & nat))
val lemma_sorted_monomials_metered (fuel:nat) (q:FF.poly)
  : Lemma (match sorted_monomials_metered fuel q with
           | None -> fuel < 1 + FF.poly_size q + L.length q
           | Some (result, work) ->
             result == sorted_monomials q /\ 0 < work /\ work <= fuel /\
             work <= 1 + FF.poly_size q + L.length q)
val input_prepare_bound (q:FF.poly) : Tot nat
val input_prepare_metered (fuel:nat) (p:pos) (q:FF.poly)
  : Tot (option (option compact & nat))
val lemma_input_prepare_metered (fuel:nat) (p:pos) (q:FF.poly)
  : Lemma (match input_prepare_metered fuel p q with
           | None -> fuel < input_prepare_bound q
           | Some (result, work) ->
             result == (if sorted_monomials q then Some (normalize p (compress q)) else None) /\
             0 < work /\ work <= fuel /\ work <= input_prepare_bound q)

let rec terms_after (m:Monomial.compact) (q:compact) : Tot bool (decreases q) =
  match q with
  | [] -> true
  | (n, _) :: rest -> Monomial.less m n && terms_after m rest

let rec terms_ordered (q:compact) : Tot bool (decreases q) =
  match q with
  | [] -> true
  | (m, _) :: rest ->
    (match rest with [] -> true | (n, _) :: _ -> Monomial.less m n) &&
    terms_ordered rest

val lemma_terms_head (m:Monomial.compact) (c:int) (rest:compact)
  : Lemma (requires terms_ordered ((m, c) :: rest))
          (ensures terms_after m rest)
val lemma_add_terms_ordered (a b:compact)
  : Lemma (requires canonical_monomials a /\ canonical_monomials b /\
                    terms_ordered a /\ terms_ordered b)
          (ensures terms_ordered (add a b))
val lemma_reduce_terms_ordered (p:pos) (q:compact)
  : Lemma (requires terms_ordered q) (ensures terms_ordered (reduce p q))
val lemma_canon_terms_ordered (q:compact)
  : Lemma (requires canonical_monomials q) (ensures terms_ordered (canon q))
val lemma_normalize_terms_ordered (p:pos) (q:compact)
  : Lemma (requires canonical_monomials q) (ensures terms_ordered (normalize p q))
val lemma_canon_ordered_identity (q:compact)
  : Lemma (requires terms_ordered q) (ensures canon q == q)

val terms_order_bound (q:compact) : Tot nat
val terms_ordered_metered (fuel:nat) (q:compact) : Tot (option (bool & nat))
val lemma_terms_ordered_metered (fuel:nat) (q:compact)
  : Lemma (match terms_ordered_metered fuel q with
           | None -> fuel < terms_order_bound q
           | Some (result, work) ->
             result == terms_ordered q /\ 0 < work /\ work <= fuel /\
             work <= terms_order_bound q)
val guarded_normalize_bound (q:compact) : Tot nat
val guarded_normalize_metered (fuel:nat) (p:pos) (q:compact)
  : Tot (option (compact & nat))
val lemma_guarded_normalize_metered (fuel:nat) (p:pos) (q:compact)
  : Lemma (match guarded_normalize_metered fuel p q with
           | None -> fuel < guarded_normalize_bound q
           | Some (result, work) ->
             result == normalize p q /\ 0 < work /\ work <= fuel /\
             work <= guarded_normalize_bound q /\
             (terms_ordered q ==> work <= terms_order_bound q + L.length q + 1))

val add_guarded_normalize_bound (a b:compact) : Tot nat
val add_guarded_normalize_metered (fuel:nat) (p:pos) (a b:compact)
  : Tot (option (compact & nat))
val lemma_add_guarded_normalize_metered (fuel:nat) (p:pos) (a b:compact)
  : Lemma (match add_guarded_normalize_metered fuel p a b with
           | None -> fuel < add_guarded_normalize_bound a b
           | Some (result, work) ->
             result == normalize p (add a b) /\ 0 < work /\ work <= fuel /\
             work <= add_guarded_normalize_bound a b)
val scale_guarded_normalize_bound (m:Monomial.compact) (q:compact) : Tot nat
val scale_guarded_normalize_metered (fuel:nat) (p:pos)
  (m:Monomial.compact) (c:int) (q:compact) : Tot (option (compact & nat))
val lemma_scale_guarded_normalize_metered (fuel:nat) (p:pos)
  (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (match scale_guarded_normalize_metered fuel p m c q with
           | None -> fuel < scale_guarded_normalize_bound m q
           | Some (result, work) ->
             result == normalize p (scale_mono m c q) /\ 0 < work /\ work <= fuel /\
             work <= scale_guarded_normalize_bound m q)
val input_prepare_guarded_bound (q:FF.poly) : Tot nat
val input_prepare_guarded_metered (fuel:nat) (p:pos) (q:FF.poly)
  : Tot (option (option compact & nat))
val lemma_input_prepare_guarded_metered (fuel:nat) (p:pos) (q:FF.poly)
  : Lemma (match input_prepare_guarded_metered fuel p q with
           | None -> fuel < input_prepare_guarded_bound q
           | Some (result, work) ->
             result == (if sorted_monomials q then Some (normalize p (compress q)) else None) /\
             0 < work /\ work <= fuel /\ work <= input_prepare_guarded_bound q)
