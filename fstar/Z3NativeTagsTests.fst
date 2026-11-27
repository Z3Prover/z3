module Z3NativeTagsTests

open Z3AstTheory
module N = Z3Native
module Native = Z3NativeProof
module OldBv = Z3BvLemma
module OldFf = Z3FiniteFieldLemma
module OldDt = Z3DatatypeLemma

let legacy_tag_parity ()
  : Lemma (
      Native.operator_tag N.Bvand [] bool_sort == Some OldBv.op_and /\
      Native.operator_tag N.BvNumeral [] bool_sort == Some OldBv.op_numeral /\
      Native.operator_tag N.Bvzeroextend [] bool_sort == Some OldBv.op_zero_extend /\
      Native.operator_tag N.FfNum [] bool_sort == Some OldFf.op_ff_num /\
      Native.operator_tag N.FfAdd [] bool_sort == Some OldFf.op_ff_add /\
      Native.operator_tag N.FfMul [] bool_sort == Some OldFf.op_ff_mul /\
      Native.operator_tag N.FfNeg [] bool_sort == Some OldFf.op_ff_neg /\
      Native.operator_tag N.FfBitsum [] bool_sort == Some OldFf.op_ff_bitsum /\
      Native.operator_tag N.DatatypeConstructor [] bool_sort == Some OldDt.op_constructor /\
      Native.operator_tag N.DatatypeRecognizer [] bool_sort == Some OldDt.op_recognizer /\
      Native.operator_tag N.DatatypeAccessor [] bool_sort == Some OldDt.op_accessor) = ()
