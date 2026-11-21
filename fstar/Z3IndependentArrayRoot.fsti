module Z3IndependentArrayRoot

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module TR = Z3TypedRoot
module A = Z3SortedArray

val supports (sigma:V.signature) (index element:sort)
  : Tot (b:bool{b <==> TR.free sigma (ArraySort [index] element)})

val read (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
  (element:sort{supports sigma index element})
  (a:A.array_value (TR.carrier u) sigma index element)
  (k:V.value (TR.carrier u) sigma index) : GTot (V.value (TR.carrier u) sigma element)

val write (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
  (element:sort{supports sigma index element})
  (a:A.array_value (TR.carrier u) sigma index element)
  (k:V.value (TR.carrier u) sigma index) (v:V.value (TR.carrier u) sigma element)
  : GTot (A.array_value (TR.carrier u) sigma index element)

val constant (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
  (element:sort{supports sigma index element}) (v:V.value (TR.carrier u) sigma element)
  : GTot (A.array_value (TR.carrier u) sigma index element)

val difference (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
  (element:sort{supports sigma index element})
  (a b:A.array_value (TR.carrier u) sigma index element)
  : GTot (V.value (TR.carrier u) sigma index)

val lemma_read_write (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
  (element:sort{supports sigma index element})
  (a:A.array_value (TR.carrier u) sigma index element)
  (j k:V.value (TR.carrier u) sigma index) (v:V.value (TR.carrier u) sigma element)
  : Lemma (read u sigma index element (write u sigma index element a j v) k ==
           (if FStar.IndefiniteDescription.strong_excluded_middle (j == k) then v
            else read u sigma index element a k))

val lemma_read_constant (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
  (element:sort{supports sigma index element})
  (v:V.value (TR.carrier u) sigma element) (k:V.value (TR.carrier u) sigma index)
  : Lemma (read u sigma index element (constant u sigma index element v) k == v)

val lemma_extensional (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
  (element:sort{supports sigma index element})
  (a b:A.array_value (TR.carrier u) sigma index element)
  : Lemma (requires (forall (k:V.value (TR.carrier u) sigma index).
                      read u sigma index element a k == read u sigma index element b k))
          (ensures a == b)

val lemma_difference (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
  (element:sort{supports sigma index element})
  (a b:A.array_value (TR.carrier u) sigma index element)
  : Lemma (a == b \/ ~(read u sigma index element a (difference u sigma index element a b) ==
                        read u sigma index element b (difference u sigma index element a b)))

val lemma_root_read (u:TR.uninterpreted) (sch:S.checked_schema) (root:TR.interp u sch)
  (index:sort) (element:sort{supports (S.signature sch) index element})
  (a:A.array_value (TR.carrier u) (S.signature sch) index element)
  (k:V.value (TR.carrier u) (S.signature sch) index)
  : Lemma (requires TR.root_model u sch root)
          (ensures root.V.application (A.select_decl index element) [a; k] ==
                   read u (S.signature sch) index element a k)

val lemma_root_write (u:TR.uninterpreted) (sch:S.checked_schema) (root:TR.interp u sch)
  (index:sort) (element:sort{supports (S.signature sch) index element})
  (a:A.array_value (TR.carrier u) (S.signature sch) index element)
  (k:V.value (TR.carrier u) (S.signature sch) index)
  (v:V.value (TR.carrier u) (S.signature sch) element)
  : Lemma (requires TR.root_model u sch root)
          (ensures root.V.application (A.store_decl index element) [a; k; v] ==
                   write u (S.signature sch) index element a k v)
