module Z3IndependentArrayRootTests

open Z3AstTheory
module V = Z3DatatypeValue
module TR = Z3TypedRoot
module AR = Z3IndependentArrayRoot

let int_s = TR.int_s
let data_s = BaseSort "data"
let ctor : func_decl =
  { decl_name = "ctor"; domain = []; range = data_s; interp = None; int_params = [] }

let supported_sorts ()
  : Lemma (AR.supports [] int_s int_s /\
           AR.supports [] int_s (ArraySort [int_s] int_s) /\
           not (AR.supports [ctor] data_s int_s) /\
           not (AR.supports [ctor] int_s data_s) /\
           not (AR.supports [ctor] int_s (ArraySort [int_s] data_s))) = ()

let read_write_controls (u:TR.uninterpreted)
  : Lemma (
    let zero = TR.make #u #[] int_s 0 in
    let one = TR.make #u #[] int_s 1 in
    let array = AR.constant u [] int_s int_s zero in
    AR.read u [] int_s int_s (AR.write u [] int_s int_s array zero one) zero == one /\
    AR.read u [] int_s int_s (AR.write u [] int_s int_s array zero one) one == zero) =
  supported_sorts ();
  let zero = TR.make #u #[] int_s 0 in
  let one = TR.make #u #[] int_s 1 in
  let array = AR.constant u [] int_s int_s zero in
  AR.lemma_read_write u [] int_s int_s array zero zero one;
  AR.lemma_read_write u [] int_s int_s array zero one one;
  AR.lemma_read_constant u [] int_s int_s zero one

let difference_control (u:TR.uninterpreted)
  : Lemma (
    let zero = TR.make #u #[] int_s 0 in
    let one = TR.make #u #[] int_s 1 in
    let a = AR.constant u [] int_s int_s zero in
    let b = AR.write u [] int_s int_s a zero one in
    ~(AR.read u [] int_s int_s a (AR.difference u [] int_s int_s a b) ==
      AR.read u [] int_s int_s b (AR.difference u [] int_s int_s a b))) =
  supported_sorts ();
  let zero = TR.make #u #[] int_s 0 in
  let one = TR.make #u #[] int_s 1 in
  let a = AR.constant u [] int_s int_s zero in
  let b = AR.write u [] int_s int_s a zero one in
  AR.lemma_read_constant u [] int_s int_s zero zero;
  AR.lemma_read_write u [] int_s int_s a zero zero one;
  AR.lemma_difference u [] int_s int_s a b
