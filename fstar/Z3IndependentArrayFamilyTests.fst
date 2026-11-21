module Z3IndependentArrayFamilyTests

open Z3AstTheory
module TR = Z3TypedRoot
module AF = Z3IndependentArrayFamily
module AR = Z3IndependentArrayRoot

let int_s = TR.int_s
let data_s = BaseSort "data"
let ctor : func_decl =
  { decl_name = "ctor"; domain = []; range = data_s; interp = None; int_params = [] }

let family_support (u:TR.uninterpreted)
  : Lemma ((AF.family u []).supports int_s int_s /\
           not ((AF.family u [ctor]).supports data_s int_s) /\
           not ((AF.family u [ctor]).supports int_s data_s)) = ()

let family_controls (u:TR.uninterpreted)
  : Lemma (
    let m = AF.family u [] in
    let algebra = m.arrays int_s int_s in
    let zero = TR.make #u #[] int_s 0 in
    let one = TR.make #u #[] int_s 1 in
    let a = algebra.constant zero in
    let b = algebra.write a zero one in
    algebra.read b zero == one /\ algebra.read b one == zero /\
    ~(algebra.read a (algebra.difference a b) == algebra.read b (algebra.difference a b))) =
  family_support u;
  let m = AF.family u [] in
  let algebra = m.arrays int_s int_s in
  let zero = TR.make #u #[] int_s 0 in
  let one = TR.make #u #[] int_s 1 in
  let a = algebra.constant zero in
  let b = algebra.write a zero one in
  AR.lemma_read_constant u [] int_s int_s zero zero;
  AR.lemma_read_constant u [] int_s int_s zero one;
  AR.lemma_read_write u [] int_s int_s a zero zero one;
  AR.lemma_read_write u [] int_s int_s a zero one one;
  AR.lemma_difference u [] int_s int_s a b
