module Z3IndependentFiniteFieldPolynomial

module FF = Z3SortedFiniteField
module Monomial = Z3IndependentFiniteFieldMonomial
module L = FStar.List.Tot
module Math = FStar.Math.Lemmas

let rec compress (q:FF.poly) : Tot compact (decreases q) =
  match q with
  | [] -> []
  | (m, c) :: rest -> (Monomial.compress m, c) :: compress rest

let rec expand (q:compact) : Tot FF.poly (decreases q) =
  match q with
  | [] -> []
  | (m, c) :: rest -> (Monomial.expand m, c) :: expand rest

let rec canonical_monomials (q:compact) : Tot bool (decreases q) =
  match q with
  | [] -> true
  | (m, _) :: rest -> Monomial.ordered m && canonical_monomials rest

let rec sorted_monomials (q:FF.poly) : Tot bool (decreases q) =
  match q with
  | [] -> true
  | (m, _) :: rest -> Monomial.sorted m && sorted_monomials rest

let rec evaluate (v:nat -> int) (q:compact) : Tot int (decreases q) =
  match q with
  | [] -> 0
  | (m, c) :: rest -> c * Monomial.evaluate v m + evaluate v rest

let rec add (a b:compact) : Tot compact (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> b
  | _, [] -> a
  | (m1, c1) :: ar, (m2, c2) :: br ->
    if m1 = m2 then (m1, c1 + c2) :: add ar br
    else if Monomial.less m1 m2 then (m1, c1) :: add ar b
    else (m2, c2) :: add a br

let rec scale_mono (m:Monomial.compact) (c:int) (q:compact)
  : Tot compact (decreases q) =
  match q with
  | [] -> []
  | (m2, c2) :: rest -> (Monomial.multiply m m2, c * c2) :: scale_mono m c rest

#push-options "--fuel 2"
let rec split (q:compact)
  : Tot (r:(compact & compact){L.length (fst r) + L.length (snd r) == L.length q /\
                                  (L.length q >= 2 ==>
                                   L.length (fst r) < L.length q /\
                                   L.length (snd r) < L.length q)})
        (decreases q) =
  match q with
  | x :: y :: rest -> let (a, b) = split rest in (x :: a, y :: b)
  | _ -> (q, [])
#pop-options

let rec canon (q:compact) : Tot compact (decreases (L.length q)) =
  if L.length q < 2 then q
  else let (a, b) = split q in add (canon a) (canon b)

let rec reduce (p:pos) (q:compact) : Tot compact (decreases q) =
  match q with
  | [] -> []
  | (m, c) :: rest ->
    if c % p = 0 then reduce p rest else (m, c % p) :: reduce p rest

let normalize (p:pos) (q:compact) : Tot compact = reduce p (canon q)

let lemma_expand_empty () : Lemma (expand [] == []) = ()

let lemma_expand_cons (m:Monomial.compact) (c:int) (rest:compact)
  : Lemma (expand ((m, c) :: rest) == (Monomial.expand m, c) :: expand rest) = ()

let rec lemma_expand_compress (q:FF.poly)
  : Lemma (expand (compress q) == q) (decreases q) =
  match q with
  | [] -> ()
  | (m, _) :: rest ->
    Monomial.lemma_expand_compress m;
    lemma_expand_compress rest

let rec lemma_compress_canonical (q:FF.poly)
  : Lemma (requires sorted_monomials q) (ensures canonical_monomials (compress q))
          (decreases q) =
  match q with
  | [] -> ()
  | (m, _) :: rest ->
    Monomial.lemma_compress_ordered m;
    lemma_compress_canonical rest

let rec lemma_evaluate (v:nat -> int) (q:compact)
  : Lemma (evaluate v q == FF.peval v (expand q)) (decreases q) =
  match q with
  | [] -> ()
  | (m, _) :: rest ->
    Monomial.lemma_evaluate v m;
    lemma_evaluate v rest

let rec lemma_add_canonical (a b:compact)
  : Lemma (requires canonical_monomials a /\ canonical_monomials b)
          (ensures canonical_monomials (add a b))
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> ()
  | _, [] -> ()
  | (m1, _) :: ar, (m2, _) :: br ->
    if m1 = m2 then lemma_add_canonical ar br
    else if Monomial.less m1 m2 then lemma_add_canonical ar b
    else lemma_add_canonical a br

let rec lemma_add_structure (a b:compact)
  : Lemma (requires canonical_monomials a /\ canonical_monomials b)
          (ensures expand (add a b) == FF.padd (expand a) (expand b))
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> ()
  | _, [] -> ()
  | (m1, _) :: ar, (m2, _) :: br ->
    if m1 = m2 then lemma_add_structure ar br
    else (
      if Monomial.expand m1 = Monomial.expand m2 then
        Monomial.lemma_ordered_injective m1 m2;
      Monomial.lemma_less m1 m2;
      if Monomial.less m1 m2 then lemma_add_structure ar b
      else lemma_add_structure a br)

let lemma_add_evaluate (v:nat -> int) (a b:compact)
  : Lemma (requires canonical_monomials a /\ canonical_monomials b)
          (ensures evaluate v (add a b) == evaluate v a + evaluate v b) =
  lemma_add_structure a b;
  lemma_evaluate v a;
  lemma_evaluate v b;
  lemma_evaluate v (add a b);
  FF.lemma_padd v (expand a) (expand b)

let rec lemma_coefficients_weaken (q:compact) (small big:nat)
  : Lemma (requires small <= big /\ coefficients_bounded small q)
          (ensures coefficients_bounded big q)
          (decreases q) =
  match q with [] -> () | _ :: rest -> lemma_coefficients_weaken rest small big

let rec lemma_add_coefficients (a b:compact) (a_limit b_limit:nat)
  : Lemma (requires coefficients_bounded a_limit a /\ coefficients_bounded b_limit b)
          (ensures coefficients_bounded (a_limit + b_limit) (add a b))
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> lemma_coefficients_weaken b b_limit (a_limit + b_limit)
  | _, [] -> lemma_coefficients_weaken a a_limit (a_limit + b_limit)
  | (m1, _) :: ar, (m2, _) :: br ->
    if m1 = m2 then lemma_add_coefficients ar br a_limit b_limit
    else if Monomial.less m1 m2 then lemma_add_coefficients ar b a_limit b_limit
    else lemma_add_coefficients a br a_limit b_limit

let rec lemma_add_size (a b:compact)
  : Lemma (compact_weight (add a b) <= compact_weight a + compact_weight b /\
           L.length (add a b) <= L.length a + L.length b)
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> ()
  | _, [] -> ()
  | (m1, _) :: ar, (m2, _) :: br ->
    if m1 = m2 then lemma_add_size ar br
    else if Monomial.less m1 m2 then lemma_add_size ar b
    else lemma_add_size a br

let rec lemma_add_degrees (a b:compact) (limit:nat)
  : Lemma (requires degrees_bounded limit a /\ degrees_bounded limit b)
          (ensures degrees_bounded limit (add a b))
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> ()
  | _, [] -> ()
  | (m1, _) :: ar, (m2, _) :: br ->
    if m1 = m2 then lemma_add_degrees ar br limit
    else if Monomial.less m1 m2 then lemma_add_degrees ar b limit
    else lemma_add_degrees a br limit

let rec lemma_scale_canonical (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (requires Monomial.ordered m /\ canonical_monomials q)
          (ensures canonical_monomials (scale_mono m c q))
          (decreases q) =
  match q with
  | [] -> ()
  | (m2, _) :: rest ->
    Monomial.lemma_multiply_ordered m m2;
    lemma_scale_canonical m c rest

let rec lemma_scale_structure (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (requires Monomial.ordered m /\ canonical_monomials q)
          (ensures expand (scale_mono m c q) == FF.scale_mono (Monomial.expand m) c (expand q))
          (decreases q) =
  match q with
  | [] -> ()
  | (m2, _) :: rest ->
    Monomial.lemma_multiply_structure m m2;
    lemma_scale_structure m c rest

let lemma_scale_evaluate (v:nat -> int) (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (requires Monomial.ordered m /\ canonical_monomials q)
          (ensures evaluate v (scale_mono m c q) == (c * Monomial.evaluate v m) * evaluate v q) =
  lemma_scale_structure m c q;
  lemma_evaluate v (scale_mono m c q);
  lemma_evaluate v q;
  Monomial.lemma_evaluate v m;
  FF.lemma_scale_mono v (Monomial.expand m) c (expand q)

let rec lemma_scale_coefficients (m:Monomial.compact) (c:int) (q:compact)
  (factor_limit coefficient_limit:nat)
  : Lemma (requires -factor_limit <= c /\ c <= factor_limit /\
                    coefficients_bounded coefficient_limit q)
          (ensures coefficients_bounded (factor_limit * coefficient_limit) (scale_mono m c q))
          (decreases q) =
  match q with
  | [] -> ()
  | _ :: rest -> lemma_scale_coefficients m c rest factor_limit coefficient_limit

let rec lemma_scale_size (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (compact_weight (scale_mono m c q) <= compact_weight q + L.length q * L.length m /\
           L.length (scale_mono m c q) == L.length q)
          (decreases q) =
  match q with
  | [] -> ()
  | (m2, _) :: rest ->
    Monomial.lemma_multiply_size m m2;
    lemma_scale_size m c rest

let rec lemma_scale_degrees (m:Monomial.compact) (c:int) (q:compact) (limit:nat)
  : Lemma (requires degrees_bounded limit q)
          (ensures degrees_bounded (Monomial.degree m + limit) (scale_mono m c q))
          (decreases q) =
  match q with
  | [] -> ()
  | (m2, _) :: rest ->
    Monomial.lemma_multiply_size m m2;
    lemma_scale_degrees m c rest limit

let rec lemma_split_size (q:compact)
  : Lemma (compact_weight (fst (split q)) + compact_weight (snd (split q)) == compact_weight q)
          (decreases q) =
  match q with
  | _ :: _ :: rest -> lemma_split_size rest
  | _ -> ()

let rec lemma_split_degrees (q:compact) (limit:nat)
  : Lemma (requires degrees_bounded limit q)
          (ensures degrees_bounded limit (fst (split q)) /\
                   degrees_bounded limit (snd (split q)))
          (decreases q) =
  match q with
  | _ :: _ :: rest -> lemma_split_degrees rest limit
  | _ -> ()

let rec lemma_canon_size (q:compact)
  : Lemma (compact_weight (canon q) <= compact_weight q /\ L.length (canon q) <= L.length q)
          (decreases (L.length q)) =
  if L.length q < 2 then ()
  else (
    let (a, b) = split q in
    lemma_split_size q;
    lemma_canon_size a;
    lemma_canon_size b;
    lemma_add_size (canon a) (canon b))

let rec lemma_canon_degrees (q:compact) (limit:nat)
  : Lemma (requires degrees_bounded limit q) (ensures degrees_bounded limit (canon q))
          (decreases (L.length q)) =
  if L.length q < 2 then ()
  else (
    let (a, b) = split q in
    lemma_split_degrees q limit;
    lemma_canon_degrees a limit;
    lemma_canon_degrees b limit;
    lemma_add_degrees (canon a) (canon b) limit)

let rec lemma_reduce_size (p:pos) (q:compact)
  : Lemma (compact_weight (reduce p q) <= compact_weight q /\
           L.length (reduce p q) <= L.length q) (decreases q) =
  match q with [] -> () | _ :: rest -> lemma_reduce_size p rest

let rec lemma_reduce_degrees (p:pos) (q:compact) (limit:nat)
  : Lemma (requires degrees_bounded limit q) (ensures degrees_bounded limit (reduce p q))
          (decreases q) =
  match q with [] -> () | _ :: rest -> lemma_reduce_degrees p rest limit

let lemma_normalize_size (p:pos) (q:compact)
  : Lemma (compact_weight (normalize p q) <= compact_weight q /\
           L.length (normalize p q) <= L.length q) =
  lemma_canon_size q;
  lemma_reduce_size p (canon q)

let lemma_normalize_degrees (p:pos) (q:compact) (limit:nat)
  : Lemma (requires degrees_bounded limit q) (ensures degrees_bounded limit (normalize p q)) =
  lemma_canon_degrees q limit;
  lemma_reduce_degrees p (canon q) limit

let rec lemma_split_coefficients (q:compact) (limit:nat)
  : Lemma (requires coefficients_bounded limit q)
          (ensures coefficients_bounded limit (fst (split q)) /\
                   coefficients_bounded limit (snd (split q)))
          (decreases q) =
  match q with
  | _ :: _ :: rest -> lemma_split_coefficients rest limit
  | _ -> ()

let rec lemma_canon_coefficients (q:compact) (limit:nat)
  : Lemma (requires coefficients_bounded limit q)
          (ensures coefficients_bounded (L.length q * limit) (canon q))
          (decreases (L.length q)) =
  if L.length q < 2 then ()
  else (
    let (a, b) = split q in
    lemma_split_coefficients q limit;
    lemma_canon_coefficients a limit;
    lemma_canon_coefficients b limit;
    lemma_add_coefficients (canon a) (canon b) (L.length a * limit) (L.length b * limit);
    Math.distributivity_add_left (L.length a) (L.length b) limit)

let rec lemma_reduce_coefficients (p:pos) (q:compact)
  : Lemma (coefficients_bounded (p - 1) (reduce p q))
          (decreases q) =
  match q with [] -> () | _ :: rest -> lemma_reduce_coefficients p rest

let lemma_normalize_coefficients (p:pos) (q:compact)
  : Lemma (coefficients_bounded (p - 1) (normalize p q)) =
  lemma_reduce_coefficients p (canon q)

let rec lemma_expand_length (q:compact)
  : Lemma (L.length (expand q) == L.length q) (decreases q) =
  match q with [] -> () | _ :: rest -> lemma_expand_length rest

let rec lemma_split_structure (q:compact)
  : Lemma (expand (fst (split q)) == fst (FF.split (expand q)) /\
           expand (snd (split q)) == snd (FF.split (expand q)))
          (decreases q) =
  match q with
  | _ :: _ :: rest -> lemma_split_structure rest
  | _ -> ()

let rec lemma_split_canonical (q:compact)
  : Lemma (requires canonical_monomials q)
          (ensures canonical_monomials (fst (split q)) /\
                   canonical_monomials (snd (split q)))
          (decreases q) =
  match q with
  | _ :: _ :: rest -> lemma_split_canonical rest
  | _ -> ()

let rec lemma_canon (q:compact)
  : Lemma (requires canonical_monomials q)
          (ensures canonical_monomials (canon q) /\
                   expand (canon q) == FF.canon (expand q))
          (decreases (L.length q)) =
  if L.length q < 2 then ()
  else (
    let (a, b) = split q in
    lemma_expand_length q;
    lemma_split_structure q;
    lemma_split_canonical q;
    lemma_canon a;
    lemma_canon b;
    lemma_add_canonical (canon a) (canon b);
    lemma_add_structure (canon a) (canon b))

let rec lemma_reduce (p:pos) (q:compact)
  : Lemma (requires canonical_monomials q)
          (ensures canonical_monomials (reduce p q) /\
                   expand (reduce p q) == FF.reduce p (expand q))
          (decreases q) =
  match q with [] -> () | _ :: rest -> lemma_reduce p rest

let lemma_normalize_canonical (p:pos) (q:compact)
  : Lemma (requires canonical_monomials q)
          (ensures canonical_monomials (normalize p q)) =
  lemma_canon q;
  lemma_reduce p (canon q)

let lemma_normalize_structure (p:pos) (q:compact)
  : Lemma (requires canonical_monomials q)
          (ensures expand (normalize p q) == FF.normalize p (expand q)) =
  lemma_canon q;
  lemma_reduce p (canon q)

let lemma_normalize_evaluate (v:nat -> int) (p:pos) (q:compact)
  : Lemma (requires canonical_monomials q)
          (ensures evaluate v (normalize p q) % p == evaluate v q % p) =
  lemma_normalize_structure p q;
  lemma_evaluate v q;
  lemma_evaluate v (normalize p q);
  FF.lemma_normalize v p (expand q)

let choose_metered (fuel:nat) (a b:compact)
  : Tot (option ((Monomial.compact & int) & compact & compact & nat)) =
  match a, b with
  | (m1, c1) :: ar, (m2, c2) :: br ->
    (match Monomial.equal_metered fuel m1 m2 with
     | None -> None
     | Some (equal, ew) ->
       if ew > fuel then None
       else if equal then Some ((m1, c1 + c2), ar, br, ew)
       else
         match Monomial.less_metered (fuel - ew) m1 m2 with
         | None -> None
         | Some (less, lw) ->
           if lw > fuel - ew then None
           else if less then Some ((m1, c1), ar, b, ew + lw)
           else Some ((m2, c2), a, br, ew + lw))
  | _, _ -> None

let lemma_choose_metered (fuel:nat) (a b:compact)
  : Lemma (match choose_metered fuel a b with
           | None -> True
           | Some (term, ar, br, work) ->
             work <= fuel /\ add a b == term :: add ar br) =
  match a, b with
  | (m1, _) :: _, (m2, _) :: _ ->
    Monomial.lemma_equal_metered fuel m1 m2;
    (match Monomial.equal_metered fuel m1 m2 with
     | Some (false, ew) ->
       if ew <= fuel then Monomial.lemma_less_metered (fuel - ew) m1 m2
     | _ -> ())
  | _, _ -> ()

let rec add_metered (fuel:nat) (a b:compact)
  : Tot (option (compact & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match a, b with
    | [], _ -> Some (b, 1)
    | _, [] -> Some (a, 1)
    | _, _ ->
      match choose_metered (fuel - 1) a b with
      | None -> None
      | Some (term, ar, br, work) ->
        if work > fuel - 1 then None
        else
          match add_metered (fuel - 1 - work) ar br with
          | None -> None
          | Some (result, tail_work) ->
            Some (term :: result, 1 + work + tail_work)

let rec lemma_add_metered (fuel:nat) (a b:compact)
  : Lemma (match add_metered fuel a b with
           | None -> True
           | Some (result, work) -> result == add a b /\ 0 < work /\ work <= fuel)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match a, b with
    | [], _ | _, [] -> ()
    | _, _ ->
      lemma_choose_metered (fuel - 1) a b;
      (match choose_metered (fuel - 1) a b with
       | Some (_, ar, br, work) ->
         if work <= fuel - 1 then lemma_add_metered (fuel - 1 - work) ar br
       | _ -> ())

let lemma_choose_sufficient (fuel:nat) (a b:compact)
  : Lemma (requires L.length a > 0 /\ L.length b > 0 /\
                    fuel >= 2 * (compact_weight a + compact_weight b + 1))
          (ensures (match choose_metered fuel a b with
                   | None -> False
                   | Some (_, ar, br, work) ->
                     work <= 2 * (compact_weight a + compact_weight b + 1) /\
                     work <= fuel /\
                     L.length ar + L.length br < L.length a + L.length b /\
                     compact_weight ar + compact_weight br <=
                       compact_weight a + compact_weight b)) =
  match a, b with
  | (m1, _) :: _, (m2, _) :: _ ->
    Monomial.lemma_equal_metered fuel m1 m2;
    (match Monomial.equal_metered fuel m1 m2 with
     | Some (false, ew) ->
       if ew <= fuel then Monomial.lemma_less_metered (fuel - ew) m1 m2
     | _ -> ())
  | _, _ -> ()

let rec lemma_add_sufficient_aux (fuel steps width:nat) (a b:compact)
  : Lemma (requires L.length a + L.length b <= steps /\
                    compact_weight a + compact_weight b <= width /\
                    fuel >= 1 + steps * (3 + 2 * width))
          (ensures (match add_metered fuel a b with
                   | None -> False
                   | Some _ -> True))
          (decreases steps) =
  match a, b with
  | [], _ | _, [] -> ()
  | _, _ ->
    lemma_choose_sufficient (fuel - 1) a b;
    (match choose_metered (fuel - 1) a b with
     | None -> ()
     | Some (_, ar, br, work) ->
       lemma_add_sufficient_aux (fuel - 1 - work) (steps - 1) width ar br)

let lemma_add_metered_sufficient (fuel:nat) (a b:compact)
  : Lemma (requires fuel >= 1 + (L.length a + L.length b) *
                                  (3 + 2 * (compact_weight a + compact_weight b)))
          (ensures (match add_metered fuel a b with
                   | None -> False
                   | Some _ -> True)) =
  lemma_add_sufficient_aux fuel (L.length a + L.length b)
    (compact_weight a + compact_weight b) a b

let rec split_metered (fuel:nat) (q:compact)
  : Tot (option (compact & compact & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match q with
    | x :: y :: rest ->
      (match split_metered (fuel - 1) rest with
       | None -> None
       | Some (a, b, work) -> Some (x :: a, y :: b, work + 1))
    | _ -> Some (q, [], 1)

let rec lemma_split_metered (fuel:nat) (q:compact)
  : Lemma (match split_metered fuel q with
           | None -> fuel < L.length q + 1
           | Some (a, b, work) ->
             (a, b) == split q /\ 0 < work /\ work <= fuel /\ work <= L.length q + 1)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match q with
    | _ :: _ :: rest -> lemma_split_metered (fuel - 1) rest
    | _ -> ()

let rec canon_metered (fuel:nat) (q:compact)
  : Tot (option (compact & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match q with
    | [] | [_] -> Some (q, 1)
    | _ ->
      match split_metered (fuel - 1) q with
      | None -> None
      | Some (a, b, sw) ->
        if sw > fuel - 1 then None
        else
          let f1 = fuel - 1 - sw in
          match canon_metered f1 a with
          | None -> None
          | Some (ca, aw) ->
            if aw > f1 then None
            else
              let f2 = f1 - aw in
              match canon_metered f2 b with
              | None -> None
              | Some (cb, bw) ->
                if bw > f2 then None
                else
                  match add_metered (f2 - bw) ca cb with
                  | None -> None
                  | Some (result, mw) -> Some (result, 1 + sw + aw + bw + mw)

let rec lemma_canon_metered (fuel:nat) (q:compact)
  : Lemma (match canon_metered fuel q with
           | None -> True
           | Some (result, work) -> result == canon q /\ 0 < work /\ work <= fuel)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match q with
    | [] | [_] -> ()
    | _ ->
      lemma_split_metered (fuel - 1) q;
      (match split_metered (fuel - 1) q with
       | None -> ()
       | Some (a, b, sw) ->
         if sw <= fuel - 1 then (
           let f1 = fuel - 1 - sw in
           lemma_canon_metered f1 a;
           match canon_metered f1 a with
           | None -> ()
           | Some (ca, aw) ->
             if aw <= f1 then (
               let f2 = f1 - aw in
               lemma_canon_metered f2 b;
               match canon_metered f2 b with
               | None -> ()
               | Some (cb, bw) ->
                 if bw <= f2 then lemma_add_metered (f2 - bw) ca cb)))

let lemma_choose_work (fuel:nat) (a b:compact)
  : Lemma (match choose_metered fuel a b with
           | None -> True
           | Some (_, ar, br, work) ->
             work <= 2 * (compact_weight a + compact_weight b + 1) /\
             L.length ar + L.length br < L.length a + L.length b /\
             compact_weight ar + compact_weight br <=
               compact_weight a + compact_weight b) =
  match a, b with
  | (m1, _) :: _, (m2, _) :: _ ->
    Monomial.lemma_equal_metered fuel m1 m2;
    (match Monomial.equal_metered fuel m1 m2 with
     | Some (false, ew) ->
       if ew <= fuel then Monomial.lemma_less_metered (fuel - ew) m1 m2
     | _ -> ())
  | _, _ -> ()

let rec lemma_add_work_aux (fuel steps width:nat) (a b:compact)
  : Lemma (requires L.length a + L.length b <= steps /\
                    compact_weight a + compact_weight b <= width)
          (ensures (match add_metered fuel a b with
                    | None -> True
                    | Some (_, work) -> work <= 1 + steps * (3 + 2 * width)))
          (decreases steps) =
  if fuel = 0 then ()
  else
    match a, b with
    | [], _ | _, [] -> ()
    | _, _ ->
      lemma_choose_work (fuel - 1) a b;
      (match choose_metered (fuel - 1) a b with
       | None -> ()
       | Some (_, ar, br, work) ->
         if work <= fuel - 1 then
           lemma_add_work_aux (fuel - 1 - work) (steps - 1) width ar br)

let lemma_add_metered_work (fuel:nat) (a b:compact)
  : Lemma (match add_metered fuel a b with
           | None -> True
           | Some (_, work) ->
             work <= 1 + (L.length a + L.length b) *
                           (3 + 2 * (compact_weight a + compact_weight b))) =
  lemma_add_work_aux fuel (L.length a + L.length b)
    (compact_weight a + compact_weight b) a b

let canon_work_bound (terms width:nat) : Tot nat =
  1 + terms * terms * (16 + 8 * width)

let lemma_canon_bound_split (a b width:nat)
  : Lemma (requires a > 0 /\ b > 0)
          (ensures 1 + (a + b + 1) + canon_work_bound a width +
                   canon_work_bound b width + (1 + (a + b) * (3 + 2 * width)) <=
                   canon_work_bound (a + b) width) =
  ()

let lemma_split_nonempty (q:compact)
  : Lemma (requires L.length q >= 2)
          (ensures L.length (fst (split q)) > 0 /\ L.length (snd (split q)) > 0) =
  match q with
  | _ :: _ :: rest -> (match split rest with | _, _ -> ())
  | _ -> ()

let rec lemma_canon_metered_bound_aux (fuel width:nat) (q:compact)
  : Lemma (requires compact_weight q <= width)
          (ensures (match canon_metered fuel q with
                    | None -> fuel < canon_work_bound (L.length q) width
                    | Some (_, work) -> work <= canon_work_bound (L.length q) width))
          (decreases (L.length q)) =
  if fuel = 0 then ()
  else
    match q with
    | [] | [_] -> ()
    | _ ->
      lemma_split_size q;
      lemma_split_nonempty q;
      let (left, right) = split q in
      lemma_canon_bound_split (L.length left) (L.length right) width;
      lemma_split_metered (fuel - 1) q;
      (match split_metered (fuel - 1) q with
       | None -> ()
       | Some (a, b, sw) ->
         if sw <= fuel - 1 then (
           let f1 = fuel - 1 - sw in
           lemma_canon_metered_bound_aux f1 width a;
           lemma_canon_metered f1 a;
           match canon_metered f1 a with
           | None -> ()
           | Some (ca, aw) ->
             if aw <= f1 then (
               let f2 = f1 - aw in
               lemma_canon_metered_bound_aux f2 width b;
               lemma_canon_metered f2 b;
               match canon_metered f2 b with
               | None -> ()
               | Some (cb, bw) ->
                 if bw <= f2 then (
                   let f3 = f2 - bw in
                   lemma_canon_size a;
                   lemma_canon_size b;
                   lemma_add_work_aux f3 (L.length q) width ca cb;
                   if f3 >= 1 + L.length q * (3 + 2 * width) then
                     lemma_add_sufficient_aux f3 (L.length q) width ca cb))))

let lemma_canon_metered_bound (fuel:nat) (q:compact)
  : Lemma (match canon_metered fuel q with
           | None -> fuel < canon_work_bound (L.length q) (compact_weight q)
           | Some (_, work) -> work <= canon_work_bound (L.length q) (compact_weight q)) =
  lemma_canon_metered_bound_aux fuel (compact_weight q) q

let rec reduce_metered (fuel:nat) (p:pos) (q:compact)
  : Tot (option (compact & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match q with
    | [] -> Some ([], 1)
    | (m, c) :: rest ->
      match reduce_metered (fuel - 1) p rest with
      | None -> None
      | Some (tail, work) ->
        let residue = c % p in
        let result = if residue = 0 then tail else (m, residue) :: tail in
        Some (result, work + 1)

let rec lemma_reduce_metered (fuel:nat) (p:pos) (q:compact)
  : Lemma (match reduce_metered fuel p q with
           | None -> fuel < L.length q + 1
           | Some (result, work) ->
             result == reduce p q /\ work == L.length q + 1 /\ work <= fuel)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match q with
    | [] -> ()
    | _ :: rest -> lemma_reduce_metered (fuel - 1) p rest

let normalize_metered (fuel:nat) (p:pos) (q:compact)
  : Tot (option (compact & nat)) =
  match canon_metered fuel q with
  | None -> None
  | Some (canonical, cw) ->
    if cw > fuel then None
    else
      match reduce_metered (fuel - cw) p canonical with
      | None -> None
      | Some (result, rw) -> Some (result, cw + rw)

let lemma_normalize_metered (fuel:nat) (p:pos) (q:compact)
  : Lemma (match normalize_metered fuel p q with
           | None -> fuel < canon_work_bound (L.length q) (compact_weight q) + L.length q + 1
           | Some (result, work) ->
             result == normalize p q /\ 0 < work /\ work <= fuel /\
             work <= canon_work_bound (L.length q) (compact_weight q) + L.length q + 1) =
  lemma_canon_metered fuel q;
  lemma_canon_metered_bound fuel q;
  lemma_canon_size q;
  match canon_metered fuel q with
  | None -> ()
  | Some (canonical, cw) ->
    if cw <= fuel then lemma_reduce_metered (fuel - cw) p canonical

let rec scale_metered (fuel:nat) (m:Monomial.compact) (c:int) (q:compact)
  : Tot (option (compact & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match q with
    | [] -> Some ([], 1)
    | (m2, c2) :: rest ->
      match Monomial.multiply_metered (fuel - 1) m m2 with
      | None -> None
      | Some (product, mw) ->
        if mw > fuel - 1 then None
        else
          match scale_metered (fuel - 1 - mw) m c rest with
          | None -> None
          | Some (tail, work) -> Some ((product, c * c2) :: tail, 1 + mw + work)

let rec lemma_scale_metered (fuel:nat) (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (match scale_metered fuel m c q with
           | None -> fuel < 1 + compact_weight q + L.length q * (1 + L.length m)
           | Some (result, work) ->
             result == scale_mono m c q /\ 0 < work /\ work <= fuel /\
             work <= 1 + compact_weight q + L.length q * (1 + L.length m))
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match q with
    | [] -> ()
    | (m2, _) :: rest ->
      Monomial.lemma_multiply_metered (fuel - 1) m m2;
      (match Monomial.multiply_metered (fuel - 1) m m2 with
       | None -> ()
       | Some (_, mw) ->
         if mw <= fuel - 1 then lemma_scale_metered (fuel - 1 - mw) m c rest)

let scale_normalize_bound (m:Monomial.compact) (q:compact) : Tot nat =
  let terms = L.length q in
  let weight = compact_weight q in
  let factor_runs = L.length m in
  let raw_weight = weight + terms * factor_runs in
  1 + weight + terms * (1 + factor_runs) +
    canon_work_bound terms raw_weight + terms + 1

let scale_normalize_metered (fuel:nat) (p:pos) (m:Monomial.compact) (c:int) (q:compact)
  : Tot (option (compact & nat)) =
  match scale_metered fuel m c q with
  | None -> None
  | Some (raw, sw) ->
    if sw > fuel then None
    else
      match normalize_metered (fuel - sw) p raw with
      | None -> None
      | Some (result, nw) -> Some (result, sw + nw)

let lemma_canon_bound_width (terms small big:nat)
  : Lemma (requires small <= big)
          (ensures canon_work_bound terms small <= canon_work_bound terms big) =
  ()

let lemma_scale_normalize_metered
  (fuel:nat) (p:pos) (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (match scale_normalize_metered fuel p m c q with
           | None -> fuel < scale_normalize_bound m q
           | Some (result, work) ->
             result == normalize p (scale_mono m c q) /\ 0 < work /\ work <= fuel /\
             work <= scale_normalize_bound m q) =
  lemma_scale_metered fuel m c q;
  lemma_scale_size m c q;
  match scale_metered fuel m c q with
  | None -> ()
  | Some (raw, sw) ->
    if sw <= fuel then (
      lemma_canon_bound_width (L.length q) (compact_weight raw)
        (compact_weight q + L.length q * L.length m);
      lemma_normalize_metered (fuel - sw) p raw)

let add_normalize_bound (a b:compact) : Tot nat =
  let terms = L.length a + L.length b in
  let weight = compact_weight a + compact_weight b in
  1 + terms * (3 + 2 * weight) + canon_work_bound terms weight + terms + 1

let add_normalize_metered (fuel:nat) (p:pos) (a b:compact)
  : Tot (option (compact & nat)) =
  match add_metered fuel a b with
  | None -> None
  | Some (raw, aw) ->
    if aw > fuel then None
    else
      match normalize_metered (fuel - aw) p raw with
      | None -> None
      | Some (result, nw) -> Some (result, aw + nw)

let lemma_canon_bound_terms (small big width:nat)
  : Lemma (requires small <= big)
          (ensures canon_work_bound small width <= canon_work_bound big width) =
  ()

let lemma_add_normalize_metered (fuel:nat) (p:pos) (a b:compact)
  : Lemma (match add_normalize_metered fuel p a b with
           | None -> fuel < add_normalize_bound a b
           | Some (result, work) ->
             result == normalize p (add a b) /\ 0 < work /\ work <= fuel /\
             work <= add_normalize_bound a b) =
  let terms = L.length a + L.length b in
  let weight = compact_weight a + compact_weight b in
  lemma_add_metered fuel a b;
  lemma_add_metered_work fuel a b;
  lemma_add_size a b;
  if fuel >= 1 + terms * (3 + 2 * weight) then lemma_add_metered_sufficient fuel a b;
  match add_metered fuel a b with
  | None -> ()
  | Some (raw, aw) ->
    if aw <= fuel then (
      lemma_canon_bound_width (L.length raw) (compact_weight raw) weight;
      lemma_canon_bound_terms (L.length raw) terms weight;
      lemma_normalize_metered (fuel - aw) p raw)

let rec compress_metered (fuel:nat) (q:FF.poly)
  : Tot (option (compact & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match q with
    | [] -> Some ([], 1)
    | (m, c) :: rest ->
      match Monomial.compress_metered (fuel - 1) m with
      | None -> None
      | Some (head, mw) ->
        if mw > fuel - 1 then None
        else
          match compress_metered (fuel - 1 - mw) rest with
          | None -> None
          | Some (tail, work) -> Some ((head, c) :: tail, 1 + mw + work)

let rec lemma_compress_metered (fuel:nat) (q:FF.poly)
  : Lemma (match compress_metered fuel q with
           | None -> fuel < 1 + FF.poly_size q + L.length q
           | Some (result, work) ->
             result == compress q /\ work == 1 + FF.poly_size q + L.length q /\ work <= fuel)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match q with
    | [] -> ()
    | (m, _) :: rest ->
      Monomial.lemma_compress_metered (fuel - 1) m;
      (match Monomial.compress_metered (fuel - 1) m with
       | None -> ()
       | Some (_, mw) ->
         if mw <= fuel - 1 then lemma_compress_metered (fuel - 1 - mw) rest)

let rec sorted_monomials_metered (fuel:nat) (q:FF.poly)
  : Tot (option (bool & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match q with
    | [] -> Some (true, 1)
    | (m, _) :: rest ->
      match Monomial.sorted_metered (fuel - 1) m with
      | None -> None
      | Some (ordered, mw) ->
        if mw > fuel - 1 then None
        else if not ordered then Some (false, 1 + mw)
        else
          match sorted_monomials_metered (fuel - 1 - mw) rest with
          | None -> None
          | Some (result, work) -> Some (result, 1 + mw + work)

let rec lemma_sorted_monomials_metered (fuel:nat) (q:FF.poly)
  : Lemma (match sorted_monomials_metered fuel q with
           | None -> fuel < 1 + FF.poly_size q + L.length q
           | Some (result, work) ->
             result == sorted_monomials q /\ 0 < work /\ work <= fuel /\
             work <= 1 + FF.poly_size q + L.length q)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match q with
    | [] -> ()
    | (m, _) :: rest ->
      Monomial.lemma_sorted_metered (fuel - 1) m;
      (match Monomial.sorted_metered (fuel - 1) m with
       | None -> ()
       | Some (ordered, mw) ->
         if mw <= fuel - 1 && ordered then
           lemma_sorted_monomials_metered (fuel - 1 - mw) rest)

let rec lemma_compress_size (q:FF.poly)
  : Lemma (compact_weight (compress q) <= FF.poly_size q /\
           L.length (compress q) == L.length q) (decreases q) =
  match q with
  | [] -> ()
  | (m, _) :: rest ->
    Monomial.lemma_expand_compress m;
    Monomial.lemma_degree (Monomial.compress m);
    lemma_compress_size rest

let rec input_weight (q:FF.poly) : Tot nat (decreases q) =
  match q with
  | [] -> 0
  | (m, _) :: rest -> 1 + L.length m + input_weight rest

let rec lemma_input_weight (q:FF.poly)
  : Lemma (input_weight q == FF.poly_size q) (decreases q) =
  match q with [] -> () | _ :: rest -> lemma_input_weight rest

let input_prepare_bound (q:FF.poly) : Tot nat =
  2 * (1 + input_weight q + L.length q) +
    canon_work_bound (L.length q) (input_weight q) + L.length q + 1

let input_prepare_metered (fuel:nat) (p:pos) (q:FF.poly)
  : Tot (option (option compact & nat)) =
  match sorted_monomials_metered fuel q with
  | None -> None
  | Some (ordered, sw) ->
    if sw > fuel then None
    else if not ordered then Some (None, sw)
    else
      let f1 = fuel - sw in
      match compress_metered f1 q with
      | None -> None
      | Some (raw, cw) ->
        if cw > f1 then None
        else
          match normalize_metered (f1 - cw) p raw with
          | None -> None
          | Some (result, nw) -> Some (Some result, sw + cw + nw)

let lemma_input_prepare_metered (fuel:nat) (p:pos) (q:FF.poly)
  : Lemma (match input_prepare_metered fuel p q with
           | None -> fuel < input_prepare_bound q
           | Some (result, work) ->
             result == (if sorted_monomials q then Some (normalize p (compress q)) else None) /\
             0 < work /\ work <= fuel /\ work <= input_prepare_bound q) =
  lemma_input_weight q;
  lemma_sorted_monomials_metered fuel q;
  lemma_compress_size q;
  match sorted_monomials_metered fuel q with
  | None -> ()
  | Some (ordered, sw) ->
    if sw <= fuel && ordered then (
      let f1 = fuel - sw in
      lemma_compress_metered f1 q;
      match compress_metered f1 q with
      | None -> ()
      | Some (raw, cw) ->
        if cw <= f1 then (
          lemma_canon_bound_width (L.length q) (compact_weight raw) (FF.poly_size q);
          lemma_normalize_metered (f1 - cw) p raw))

let rec lemma_terms_after_transitive (a b:Monomial.compact) (q:compact)
  : Lemma (requires Monomial.less a b /\ terms_after b q)
          (ensures terms_after a q) (decreases q) =
  match q with
  | [] -> ()
  | (m, _) :: rest ->
    Monomial.lemma_less_transitive a b m;
    lemma_terms_after_transitive a b rest

let rec lemma_terms_head (m:Monomial.compact) (c:int) (rest:compact)
  : Lemma (requires terms_ordered ((m, c) :: rest))
          (ensures terms_after m rest) (decreases rest) =
  match rest with
  | [] -> ()
  | (n, d) :: tail ->
    lemma_terms_head n d tail;
    lemma_terms_after_transitive m n tail

let rec lemma_add_terms_after (m:Monomial.compact) (a b:compact)
  : Lemma (requires terms_after m a /\ terms_after m b)
          (ensures terms_after m (add a b))
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> ()
  | _, [] -> ()
  | (m1, _) :: ar, (m2, _) :: br ->
    if m1 = m2 then lemma_add_terms_after m ar br
    else if Monomial.less m1 m2 then lemma_add_terms_after m ar b
    else lemma_add_terms_after m a br

let rec lemma_add_terms_ordered (a b:compact)
  : Lemma (requires canonical_monomials a /\ canonical_monomials b /\
                    terms_ordered a /\ terms_ordered b)
          (ensures terms_ordered (add a b))
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> ()
  | _, [] -> ()
  | (m1, c1) :: ar, (m2, c2) :: br ->
    lemma_terms_head m1 c1 ar;
    lemma_terms_head m2 c2 br;
    if m1 = m2 then (
      lemma_add_terms_ordered ar br;
      lemma_add_terms_after m1 ar br)
    else if Monomial.less m1 m2 then (
      lemma_add_terms_ordered ar b;
      lemma_terms_after_transitive m1 m2 br;
      lemma_add_terms_after m1 ar b)
    else (
      Monomial.lemma_less_total m1 m2;
      lemma_add_terms_ordered a br;
      lemma_terms_after_transitive m2 m1 ar;
      lemma_add_terms_after m2 a br)

let rec lemma_reduce_terms_after (p:pos) (m:Monomial.compact) (q:compact)
  : Lemma (requires terms_after m q) (ensures terms_after m (reduce p q))
          (decreases q) =
  match q with [] -> () | _ :: rest -> lemma_reduce_terms_after p m rest

let rec lemma_reduce_terms_ordered (p:pos) (q:compact)
  : Lemma (requires terms_ordered q) (ensures terms_ordered (reduce p q))
          (decreases q) =
  match q with
  | [] -> ()
  | (m, c) :: rest ->
    lemma_reduce_terms_ordered p rest;
    lemma_terms_head m c rest;
    lemma_reduce_terms_after p m rest

let rec lemma_canon_terms_ordered (q:compact)
  : Lemma (requires canonical_monomials q) (ensures terms_ordered (canon q))
          (decreases (L.length q)) =
  if L.length q < 2 then ()
  else (
    let (a, b) = split q in
    lemma_split_canonical q;
    lemma_canon_terms_ordered a;
    lemma_canon_terms_ordered b;
    lemma_canon a;
    lemma_canon b;
    lemma_add_terms_ordered (canon a) (canon b))

let lemma_normalize_terms_ordered (p:pos) (q:compact)
  : Lemma (requires canonical_monomials q) (ensures terms_ordered (normalize p q)) =
  lemma_canon_terms_ordered q;
  lemma_reduce_terms_ordered p (canon q)

let rec lemma_split_terms_after (m:Monomial.compact) (q:compact)
  : Lemma (requires terms_after m q)
          (ensures terms_after m (fst (split q)) /\ terms_after m (snd (split q)))
          (decreases q) =
  match q with
  | _ :: _ :: rest -> lemma_split_terms_after m rest
  | _ -> ()

let rec lemma_split_terms_ordered (q:compact)
  : Lemma (requires terms_ordered q)
          (ensures terms_ordered (fst (split q)) /\ terms_ordered (snd (split q)))
          (decreases q) =
  match q with
  | (m, c) :: (n, d) :: rest ->
    lemma_terms_head m c ((n, d) :: rest);
    lemma_terms_head n d rest;
    lemma_split_terms_after m rest;
    lemma_split_terms_after n rest;
    lemma_split_terms_ordered rest
  | _ -> ()

let rec lemma_add_split_identity (q:compact)
  : Lemma (requires terms_ordered q)
          (ensures add (fst (split q)) (snd (split q)) == q)
          (decreases q) =
  match q with
  | (m, _) :: (n, d) :: rest ->
    lemma_terms_head n d rest;
    lemma_split_terms_after n rest;
    lemma_add_split_identity rest;
    Monomial.lemma_less_irreflexive m;
    Monomial.lemma_less_irreflexive n;
    (match fst (split rest) with
     | [] -> ()
     | (h, _) :: _ ->
       if Monomial.less h n then Monomial.lemma_less_transitive n h n)
  | _ -> ()

let rec lemma_canon_ordered_identity (q:compact)
  : Lemma (requires terms_ordered q) (ensures canon q == q)
          (decreases (L.length q)) =
  if L.length q < 2 then ()
  else (
    let (a, b) = split q in
    lemma_split_terms_ordered q;
    lemma_canon_ordered_identity a;
    lemma_canon_ordered_identity b;
    lemma_add_split_identity q)

let terms_order_bound (q:compact) : Tot nat =
  1 + L.length q * (2 + 2 * compact_weight q)

let rec terms_ordered_metered (fuel:nat) (q:compact)
  : Tot (option (bool & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match q with
    | [] -> Some (true, 1)
    | (m, _) :: rest ->
      (match rest with
       | [] -> Some (true, 1)
       | (n, _) :: _ ->
         match Monomial.less_metered (fuel - 1) m n with
         | None -> None
         | Some (ordered, cw) ->
           if cw > fuel - 1 then None
           else if not ordered then Some (false, cw + 1)
           else
             match terms_ordered_metered (fuel - 1 - cw) rest with
             | None -> None
             | Some (result, rw) -> Some (result, 1 + cw + rw))

let rec lemma_terms_ordered_metered_aux (fuel width:nat) (q:compact)
  : Lemma (requires compact_weight q <= width)
          (ensures (match terms_ordered_metered fuel q with
                    | None -> fuel < 1 + L.length q * (2 + 2 * width)
                    | Some (result, work) ->
                      result == terms_ordered q /\ 0 < work /\ work <= fuel /\
                      work <= 1 + L.length q * (2 + 2 * width)))
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match q with
    | (m, _) :: (n, d) :: tail ->
      let rest = (n, d) :: tail in
      Monomial.lemma_less_metered (fuel - 1) m n;
      (match Monomial.less_metered (fuel - 1) m n with
       | None -> ()
       | Some (ordered, cw) ->
         if cw <= fuel - 1 && ordered then
           lemma_terms_ordered_metered_aux (fuel - 1 - cw) width rest)
    | _ -> ()

let lemma_terms_ordered_metered (fuel:nat) (q:compact)
  : Lemma (match terms_ordered_metered fuel q with
           | None -> fuel < terms_order_bound q
           | Some (result, work) ->
             result == terms_ordered q /\ 0 < work /\ work <= fuel /\
             work <= terms_order_bound q) =
  lemma_terms_ordered_metered_aux fuel (compact_weight q) q

let guarded_normalize_bound (q:compact) : Tot nat =
  terms_order_bound q +
  canon_work_bound (L.length q) (compact_weight q) + L.length q + 1

let guarded_normalize_metered (fuel:nat) (p:pos) (q:compact)
  : Tot (option (compact & nat)) =
  match terms_ordered_metered fuel q with
  | None -> None
  | Some (ordered, gw) ->
    if gw > fuel then None
    else
      let next =
        if ordered then reduce_metered (fuel - gw) p q
        else normalize_metered (fuel - gw) p q in
      match next with
      | None -> None
      | Some (result, nw) -> Some (result, gw + nw)

let lemma_guarded_normalize_metered (fuel:nat) (p:pos) (q:compact)
  : Lemma (match guarded_normalize_metered fuel p q with
           | None -> fuel < guarded_normalize_bound q
           | Some (result, work) ->
             result == normalize p q /\ 0 < work /\ work <= fuel /\
             work <= guarded_normalize_bound q /\
             (terms_ordered q ==> work <= terms_order_bound q + L.length q + 1)) =
  lemma_terms_ordered_metered fuel q;
  match terms_ordered_metered fuel q with
  | None -> ()
  | Some (ordered, gw) ->
    if gw <= fuel then
      if ordered then (
        lemma_canon_ordered_identity q;
        lemma_reduce_metered (fuel - gw) p q)
      else lemma_normalize_metered (fuel - gw) p q

let lemma_guarded_normalize_bound_size (q:compact) (terms weight:nat)
  : Lemma (requires L.length q <= terms /\ compact_weight q <= weight)
          (ensures guarded_normalize_bound q <=
                   1 + terms * (2 + 2 * weight) +
                   canon_work_bound terms weight + terms + 1) =
  lemma_canon_bound_width (L.length q) (compact_weight q) weight;
  lemma_canon_bound_terms (L.length q) terms weight

let add_guarded_normalize_bound (a b:compact) : Tot nat =
  let terms = L.length a + L.length b in
  let weight = compact_weight a + compact_weight b in
  add_normalize_bound a b + 1 + terms * (2 + 2 * weight)

let add_guarded_normalize_metered (fuel:nat) (p:pos) (a b:compact)
  : Tot (option (compact & nat)) =
  match add_metered fuel a b with
  | None -> None
  | Some (raw, aw) ->
    if aw > fuel then None
    else
      match guarded_normalize_metered (fuel - aw) p raw with
      | None -> None
      | Some (result, nw) -> Some (result, aw + nw)

let lemma_add_guarded_normalize_metered (fuel:nat) (p:pos) (a b:compact)
  : Lemma (match add_guarded_normalize_metered fuel p a b with
           | None -> fuel < add_guarded_normalize_bound a b
           | Some (result, work) ->
             result == normalize p (add a b) /\ 0 < work /\ work <= fuel /\
             work <= add_guarded_normalize_bound a b) =
  let terms = L.length a + L.length b in
  let weight = compact_weight a + compact_weight b in
  lemma_add_metered fuel a b;
  lemma_add_metered_work fuel a b;
  lemma_add_size a b;
  if fuel >= 1 + terms * (3 + 2 * weight) then lemma_add_metered_sufficient fuel a b;
  match add_metered fuel a b with
  | None -> ()
  | Some (raw, aw) ->
    if aw <= fuel then (
      lemma_guarded_normalize_bound_size raw terms weight;
      lemma_guarded_normalize_metered (fuel - aw) p raw)

let scale_guarded_normalize_bound (m:Monomial.compact) (q:compact) : Tot nat =
  let terms = L.length q in
  let raw_weight = compact_weight q + terms * L.length m in
  scale_normalize_bound m q + 1 + terms * (2 + 2 * raw_weight)

let scale_guarded_normalize_metered (fuel:nat) (p:pos)
  (m:Monomial.compact) (c:int) (q:compact) : Tot (option (compact & nat)) =
  match scale_metered fuel m c q with
  | None -> None
  | Some (raw, sw) ->
    if sw > fuel then None
    else
      match guarded_normalize_metered (fuel - sw) p raw with
      | None -> None
      | Some (result, nw) -> Some (result, sw + nw)

let lemma_scale_guarded_normalize_metered (fuel:nat) (p:pos)
  (m:Monomial.compact) (c:int) (q:compact)
  : Lemma (match scale_guarded_normalize_metered fuel p m c q with
           | None -> fuel < scale_guarded_normalize_bound m q
           | Some (result, work) ->
             result == normalize p (scale_mono m c q) /\ 0 < work /\ work <= fuel /\
             work <= scale_guarded_normalize_bound m q) =
  lemma_scale_metered fuel m c q;
  lemma_scale_size m c q;
  match scale_metered fuel m c q with
  | None -> ()
  | Some (raw, sw) ->
    if sw <= fuel then (
      lemma_guarded_normalize_bound_size raw (L.length q)
        (compact_weight q + L.length q * L.length m);
      lemma_guarded_normalize_metered (fuel - sw) p raw)

let input_prepare_guarded_bound (q:FF.poly) : Tot nat =
  input_prepare_bound q + 1 + L.length q * (2 + 2 * input_weight q)

let input_prepare_guarded_metered (fuel:nat) (p:pos) (q:FF.poly)
  : Tot (option (option compact & nat)) =
  match sorted_monomials_metered fuel q with
  | None -> None
  | Some (ordered, sw) ->
    if sw > fuel then None
    else if not ordered then Some (None, sw)
    else
      let f1 = fuel - sw in
      match compress_metered f1 q with
      | None -> None
      | Some (raw, cw) ->
        if cw > f1 then None
        else
          match guarded_normalize_metered (f1 - cw) p raw with
          | None -> None
          | Some (result, nw) -> Some (Some result, sw + cw + nw)

let lemma_input_prepare_guarded_metered (fuel:nat) (p:pos) (q:FF.poly)
  : Lemma (match input_prepare_guarded_metered fuel p q with
           | None -> fuel < input_prepare_guarded_bound q
           | Some (result, work) ->
             result == (if sorted_monomials q then Some (normalize p (compress q)) else None) /\
             0 < work /\ work <= fuel /\ work <= input_prepare_guarded_bound q) =
  lemma_input_weight q;
  lemma_sorted_monomials_metered fuel q;
  lemma_compress_size q;
  match sorted_monomials_metered fuel q with
  | None -> ()
  | Some (ordered, sw) ->
    if sw <= fuel && ordered then (
      let f1 = fuel - sw in
      lemma_compress_metered f1 q;
      match compress_metered f1 q with
      | None -> ()
      | Some (raw, cw) ->
        if cw <= f1 then (
          lemma_guarded_normalize_bound_size raw (L.length q) (FF.poly_size q);
          lemma_guarded_normalize_metered (f1 - cw) p raw))
