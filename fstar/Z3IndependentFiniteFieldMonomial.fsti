module Z3IndependentFiniteFieldMonomial

module FF = Z3SortedFiniteField

type compact = list (nat & pos)

val compress (m:FF.mono) : Tot compact
val expand (m:compact) : Tot FF.mono
val evaluate (v:nat -> int) (m:compact) : Tot int
val multiply (a b:compact) : Tot compact
val less (a b:compact) : Tot bool
val equal_metered (fuel:nat) (a b:compact) : Tot (option (bool & nat))
val lemma_equal_metered (fuel:nat) (a b:compact)
  : Lemma (match equal_metered fuel a b with
           | None -> fuel < FStar.List.Tot.length a + FStar.List.Tot.length b + 1
           | Some (result, work) ->
             result == (a = b) /\ work <= fuel /\
             work <= FStar.List.Tot.length a + FStar.List.Tot.length b + 1)
val less_metered (fuel:nat) (a b:compact) : Tot (option (bool & nat))
val lemma_less_metered (fuel:nat) (a b:compact)
  : Lemma (match less_metered fuel a b with
           | None -> fuel < FStar.List.Tot.length a + FStar.List.Tot.length b + 1
           | Some (result, work) ->
             result == less a b /\ work <= fuel /\
             work <= FStar.List.Tot.length a + FStar.List.Tot.length b + 1)
val ordered (m:compact) : Tot bool
val sorted (m:FF.mono) : Tot bool
val degree (m:compact) : Tot nat

val lemma_degree_empty () : Lemma (degree [] == 0)
val lemma_degree_cons (x:nat) (n:pos) (rest:compact)
  : Lemma (degree ((x, n) :: rest) == n + degree rest)
val lemma_degree (m:compact)
  : Lemma (FStar.List.Tot.length (expand m) == degree m /\
           FStar.List.Tot.length m <= degree m)
val lemma_expand_compress (m:FF.mono) : Lemma (expand (compress m) == m)
val lemma_compress_ordered (m:FF.mono)
  : Lemma (requires sorted m) (ensures ordered (compress m))
val lemma_compress_expand (m:compact)
  : Lemma (requires ordered m) (ensures compress (expand m) == m)
val lemma_ordered_injective (a b:compact)
  : Lemma (requires ordered a /\ ordered b /\ expand a == expand b) (ensures a == b)
val lemma_evaluate (v:nat -> int) (m:compact)
  : Lemma (evaluate v m == FF.mval v (expand m))
val lemma_multiply (v:nat -> int) (a b:compact)
  : Lemma (evaluate v (multiply a b) == evaluate v a * evaluate v b)
val lemma_multiply_expanded (v:nat -> int) (a b:compact)
  : Lemma (evaluate v (multiply a b) == FF.mval v (FF.mono_mul (expand a) (expand b)))
val lemma_less (a b:compact)
  : Lemma (less a b == FF.mono_lt (expand a) (expand b))
val lemma_multiply_structure (a b:compact)
  : Lemma (requires ordered a /\ ordered b)
          (ensures expand (multiply a b) == FF.mono_mul (expand a) (expand b))
val lemma_multiply_ordered (a b:compact)
  : Lemma (requires ordered a /\ ordered b)
          (ensures ordered (multiply a b))
val lemma_multiply_size (a b:compact)
  : Lemma (degree (multiply a b) == degree a + degree b /\
           FStar.List.Tot.length (multiply a b) <=
             FStar.List.Tot.length a + FStar.List.Tot.length b)
val multiply_metered (fuel:nat) (a b:compact) : Tot (option (compact & nat))
val lemma_multiply_metered (fuel:nat) (a b:compact)
  : Lemma (match multiply_metered fuel a b with
           | None -> fuel < FStar.List.Tot.length a + FStar.List.Tot.length b + 1
           | Some (result, work) ->
             result == multiply a b /\ 0 < work /\ work <= fuel /\
             work <= FStar.List.Tot.length a + FStar.List.Tot.length b + 1)
val compress_metered (fuel:nat) (m:FF.mono) : Tot (option (compact & nat))
val lemma_compress_metered (fuel:nat) (m:FF.mono)
  : Lemma (match compress_metered fuel m with
           | None -> fuel < FStar.List.Tot.length m + 1
           | Some (result, work) ->
             result == compress m /\ work == FStar.List.Tot.length m + 1 /\ work <= fuel)
val sorted_metered (fuel:nat) (m:FF.mono) : Tot (option (bool & nat))
val lemma_sorted_metered (fuel:nat) (m:FF.mono)
  : Lemma (match sorted_metered fuel m with
           | None -> fuel < FStar.List.Tot.length m + 1
           | Some (result, work) ->
             result == sorted m /\ 0 < work /\ work <= fuel /\
             work <= FStar.List.Tot.length m + 1)
val ordered_metered (fuel:nat) (m:compact) : Tot (option (bool & nat))
val lemma_ordered_metered (fuel:nat) (m:compact)
  : Lemma (match ordered_metered fuel m with
           | None -> fuel < FStar.List.Tot.length m + 1
           | Some (result, work) ->
             result == ordered m /\ 0 < work /\ work <= fuel /\
             work <= FStar.List.Tot.length m + 1)

val lemma_less_irreflexive (a:compact) : Lemma (not (less a a))
val lemma_less_transitive (a b c:compact)
  : Lemma (requires less a b /\ less b c) (ensures less a c)
val lemma_less_total (a b:compact)
  : Lemma (requires ordered a /\ ordered b /\ a <> b)
          (ensures less a b \/ less b a)
