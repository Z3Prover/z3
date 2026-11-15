module Z3IndependentArrayFamily

open Z3AstTheory
module V = Z3DatatypeValue
module TR = Z3TypedRoot
module A = Z3SortedArray
module AR = Z3IndependentArrayRoot
module ID = FStar.IndefiniteDescription

let arrays (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
           (element:sort{AR.supports sigma index element})
  : GTot (A.algebra (V.value (TR.carrier u) sigma index)
                    (V.value (TR.carrier u) sigma element)
                    (A.array_value (TR.carrier u) sigma index element)) =
  let read = AR.read u sigma index element in
  let write = AR.write u sigma index element in
  let constant = AR.constant u sigma index element in
  let difference = AR.difference u sigma index element in
  FStar.Classical.forall_intro_4 (AR.lemma_read_write u sigma index element);
  FStar.Classical.forall_intro_2 (AR.lemma_read_constant u sigma index element);
  FStar.Classical.forall_intro_2 (AR.lemma_difference u sigma index element);
  { A.read = read; A.write = write; A.constant = constant; A.difference = difference;
    A.extensional = AR.lemma_extensional u sigma index element; A.laws = () }

let family (u:TR.uninterpreted) (sigma:V.signature) : GTot (A.family (TR.carrier u) sigma) =
  { A.supports = AR.supports sigma; A.arrays = arrays u sigma }
