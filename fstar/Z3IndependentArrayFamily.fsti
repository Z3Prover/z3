module Z3IndependentArrayFamily

open Z3AstTheory
module V = Z3DatatypeValue
module TR = Z3TypedRoot
module A = Z3SortedArray
module AR = Z3IndependentArrayRoot

val arrays (u:TR.uninterpreted) (sigma:V.signature) (index:sort)
  (element:sort{AR.supports sigma index element})
  : GTot (a:A.algebra (V.value (TR.carrier u) sigma index)
                      (V.value (TR.carrier u) sigma element)
                      (A.array_value (TR.carrier u) sigma index element){
      a.read == AR.read u sigma index element /\
      a.write == AR.write u sigma index element /\
      a.constant == AR.constant u sigma index element /\
      a.difference == AR.difference u sigma index element})

val family (u:TR.uninterpreted) (sigma:V.signature)
  : GTot (m:A.family (TR.carrier u) sigma{
      m.supports == AR.supports sigma /\
      (forall (i:sort) (e:sort{m.supports i e}).
        (m.arrays i e).read == AR.read u sigma i e /\
        (m.arrays i e).write == AR.write u sigma i e /\
        (m.arrays i e).constant == AR.constant u sigma i e /\
        (m.arrays i e).difference == AR.difference u sigma i e)})
