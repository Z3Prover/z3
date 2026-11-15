module Z3IndependentArrayRoot

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module TR = Z3TypedRoot
module A = Z3SortedArray
module ID = FStar.IndefiniteDescription

let supports (sigma:V.signature) (index element:sort) : Tot bool =
  TR.free sigma (ArraySort [index] element)

let read (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
         (element:sort{supports sigma index element})
         (a:A.array_value (TR.carrier u) sigma index element)
         (k:V.value (TR.carrier u) sigma index) : GTot (V.value (TR.carrier u) sigma element) =
  let arr = ArraySort [index] element in
  TR.make #u #sigma element
    (TR.read #(TR.indices u [index]) #(TR.carrier u element)
      (TR.scalar #u #sigma arr a) (TR.scalar #u #sigma index k, ()))

let write (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
          (element:sort{supports sigma index element})
          (a:A.array_value (TR.carrier u) sigma index element)
          (k:V.value (TR.carrier u) sigma index) (v:V.value (TR.carrier u) sigma element)
  : GTot (A.array_value (TR.carrier u) sigma index element) =
  let arr = ArraySort [index] element in
  TR.make #u #sigma arr
    (TR.write #(TR.indices u [index]) #(TR.carrier u element)
      (TR.scalar #u #sigma arr a) (TR.scalar #u #sigma index k, ())
      (TR.scalar #u #sigma element v))

let constant (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
             (element:sort{supports sigma index element}) (v:V.value (TR.carrier u) sigma element)
  : GTot (A.array_value (TR.carrier u) sigma index element) =
  TR.make #u #sigma (ArraySort [index] element)
    (TR.lambda_value #(TR.indices u [index]) #(TR.carrier u element)
      (fun _ -> TR.scalar #u #sigma element v))

let difference (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
               (element:sort{supports sigma index element})
               (a b:A.array_value (TR.carrier u) sigma index element)
  : GTot (V.value (TR.carrier u) sigma index) =
  let arr = ArraySort [index] element in
  let ix = TR.difference #(TR.indices u [index]) #(TR.carrier u element)
    (TR.scalar #u #sigma arr a) (TR.scalar #u #sigma arr b) (TR.default_value u index, ()) in
  TR.make #u #sigma index (fst ix)

let lemma_read_write (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
                     (element:sort{supports sigma index element})
                     (a:A.array_value (TR.carrier u) sigma index element)
                     (j k:V.value (TR.carrier u) sigma index) (v:V.value (TR.carrier u) sigma element)
  : Lemma (read u sigma index element (write u sigma index element a j v) k ==
           (if ID.strong_excluded_middle (j == k) then v else read u sigma index element a k)) =
  TR.lemma_make_scalar #u #sigma index j;
  TR.lemma_make_scalar #u #sigma index k;
  TR.lemma_make_scalar #u #sigma element v

let lemma_read_constant (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
                        (element:sort{supports sigma index element})
                        (v:V.value (TR.carrier u) sigma element) (k:V.value (TR.carrier u) sigma index)
  : Lemma (read u sigma index element (constant u sigma index element v) k == v) =
  TR.lemma_make_scalar #u #sigma element v

let lemma_extensional (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
                      (element:sort{supports sigma index element})
                      (a b:A.array_value (TR.carrier u) sigma index element)
  : Lemma (requires (forall (k:V.value (TR.carrier u) sigma index).
                      read u sigma index element a k == read u sigma index element b k))
          (ensures a == b) =
  let arr = ArraySort [index] element in
  let pointwise (ix:TR.indices u [index])
    : Lemma (TR.read #(TR.indices u [index]) #(TR.carrier u element) (TR.scalar #u #sigma arr a) ix ==
             TR.read #(TR.indices u [index]) #(TR.carrier u element) (TR.scalar #u #sigma arr b) ix) =
    assert (ix == (fst ix, ()));
    TR.lemma_scalar_make #u #sigma index (fst ix);
    assert (read u sigma index element a (TR.make #u #sigma index (fst ix)) ==
            read u sigma index element b (TR.make #u #sigma index (fst ix)));
    TR.lemma_scalar_make #u #sigma element
      (TR.read #(TR.indices u [index]) #(TR.carrier u element) (TR.scalar #u #sigma arr a) ix);
    TR.lemma_scalar_make #u #sigma element
      (TR.read #(TR.indices u [index]) #(TR.carrier u element) (TR.scalar #u #sigma arr b) ix) in
  FStar.Classical.forall_intro pointwise;
  TR.lemma_array_extensionality #u #sigma [index] element a b

let lemma_difference (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
                     (element:sort{supports sigma index element})
                     (a b:A.array_value (TR.carrier u) sigma index element)
  : Lemma (a == b \/ ~(read u sigma index element a (difference u sigma index element a b) ==
                        read u sigma index element b (difference u sigma index element a b))) =
  let arr = ArraySort [index] element in
  let ix = TR.difference #(TR.indices u [index]) #(TR.carrier u element)
    (TR.scalar #u #sigma arr a) (TR.scalar #u #sigma arr b) (TR.default_value u index, ()) in
  assert (ix == (fst ix, ()));
  TR.lemma_scalar_make #u #sigma index (fst ix);
  TR.lemma_make_scalar #u #sigma arr a;
  TR.lemma_make_scalar #u #sigma arr b;
  TR.lemma_scalar_make #u #sigma element
    (TR.read #(TR.indices u [index]) #(TR.carrier u element) (TR.scalar #u #sigma arr a) ix);
  TR.lemma_scalar_make #u #sigma element
    (TR.read #(TR.indices u [index]) #(TR.carrier u element) (TR.scalar #u #sigma arr b) ix)

let lemma_root_read (u:TR.uninterpreted) (sch:S.checked_schema) (root:TR.interp u sch)
                    (index:sort) (element:sort{supports (S.signature sch) index element})
                    (a:A.array_value (TR.carrier u) (S.signature sch) index element)
                    (k:V.value (TR.carrier u) (S.signature sch) index)
  : Lemma (requires TR.root_model u sch root)
          (ensures root.V.application (A.select_decl index element) [a; k] ==
                   read u (S.signature sch) index element a k) =
  TR.lemma_select_value root [index] element a [k]

let lemma_root_write (u:TR.uninterpreted) (sch:S.checked_schema) (root:TR.interp u sch)
                     (index:sort) (element:sort{supports (S.signature sch) index element})
                     (a:A.array_value (TR.carrier u) (S.signature sch) index element)
                     (k:V.value (TR.carrier u) (S.signature sch) index)
                     (v:V.value (TR.carrier u) (S.signature sch) element)
  : Lemma (requires TR.root_model u sch root)
          (ensures root.V.application (A.store_decl index element) [a; k; v] ==
                   write u (S.signature sch) index element a k v) =
  TR.lemma_store_value root [index] element a [k] v
