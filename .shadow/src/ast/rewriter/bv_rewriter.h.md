# Shadow: src/ast/rewriter/bv_rewriter.h

**Language**: C | **Lines**: 268 | **Last modified**: 2026-07-22

## File-Level

_No discoveries yet._

## `class bv_rewriter_core`

### `bv_rewriter_core.get_fid`

_No discoveries yet._

### `bv_rewriter_core.is_numeral`

_No discoveries yet._

### `bv_rewriter_core.is_numeral`

_No discoveries yet._

### `bv_rewriter_core.is_zero`

_No discoveries yet._

### `bv_rewriter_core.is_minus_one`

_No discoveries yet._

### `bv_rewriter_core.normalize`

_No discoveries yet._

### `bv_rewriter_core.mk_numeral`

_No discoveries yet._

### `bv_rewriter_core.add_decl_kind`

_No discoveries yet._

### `bv_rewriter_core.mul_decl_kind`

_No discoveries yet._

### `bv_rewriter_core.use_power`

_No discoveries yet._

### `bv_rewriter_core.mk_power`

_No discoveries yet._

### `bv_rewriter_core.coerce`

_No discoveries yet._

### `bv_rewriter_core.power_decl_kind`

_No discoveries yet._

## `class bv_rewriter`

### `bv_rewriter.is_zero_bit`

_No discoveries yet._

### `bv_rewriter.mk_ule`

_No discoveries yet._

### `bv_rewriter.mk_uge`

_No discoveries yet._

### `bv_rewriter.mk_ult`

_No discoveries yet._

### `bv_rewriter.mk_sle`

_No discoveries yet._

### `bv_rewriter.mk_sge`

_No discoveries yet._

### `bv_rewriter.mk_slt`

_No discoveries yet._

### `bv_rewriter.rw_leq_concats`

_No discoveries yet._

### `bv_rewriter.are_eq_upto_num`

_No discoveries yet._

### `bv_rewriter.rw_leq_overflow`

_No discoveries yet._

### `bv_rewriter.mk_leq_core`

_No discoveries yet._

### `bv_rewriter.mk_concat`

_No discoveries yet._

### `bv_rewriter.propagate_extract`

_No discoveries yet._

### `bv_rewriter.mk_extract`

_No discoveries yet._

### `bv_rewriter.mk_repeat`

_No discoveries yet._

### `bv_rewriter.mk_zero_extend`

_No discoveries yet._

### `bv_rewriter.mk_sign_extend`

_No discoveries yet._

### `bv_rewriter.is_negatable`

_No discoveries yet._

### `bv_rewriter.mk_bv_not`

_No discoveries yet._

### `bv_rewriter.mk_bv_or`

_No discoveries yet._

### `bv_rewriter.mk_bv_xor`

_No discoveries yet._

### `bv_rewriter.mk_bv_and`

_No discoveries yet._

### `bv_rewriter.mk_bv_nand`

_No discoveries yet._

### `bv_rewriter.mk_bv_nor`

_No discoveries yet._

### `bv_rewriter.mk_bv_xnor`

_No discoveries yet._

### `bv_rewriter.mk_bv_rotate_left`

_No discoveries yet._

### `bv_rewriter.mk_bv_rotate_right`

_No discoveries yet._

### `bv_rewriter.mk_bv_ext_rotate_left`

_No discoveries yet._

### `bv_rewriter.mk_bv_ext_rotate_right`

_No discoveries yet._

### `bv_rewriter.mk_bv_add`

_No discoveries yet._

### `bv_rewriter.mk_bv_sub`

_No discoveries yet._

### `bv_rewriter.mk_bv_mul`

_No discoveries yet._

### `bv_rewriter.mk_bv_add`

_No discoveries yet._

### `bv_rewriter.mk_bv_mul`

_No discoveries yet._

### `bv_rewriter.mk_mul_hoist`

_No discoveries yet._

### `bv_rewriter.mk_bv_shl`

_No discoveries yet._

### `bv_rewriter.mk_bv_lshr`

_No discoveries yet._

### `bv_rewriter.mk_bv_ashr`

_No discoveries yet._

### `bv_rewriter.distribute_concat`

_No discoveries yet._

### `bv_rewriter.is_minus_one_core`

_No discoveries yet._

### `bv_rewriter.is_x_minus_one`

_No discoveries yet._

### `bv_rewriter.is_add_no_overflow`

_No discoveries yet._

### `bv_rewriter.is_mul_no_overflow`

_No discoveries yet._

### `bv_rewriter.num_leading_zero_bits`

_No discoveries yet._

### `bv_rewriter.mk_bv_sdiv_core`

_No discoveries yet._

### `bv_rewriter.mk_bv_udiv_core`

_No discoveries yet._

### `bv_rewriter.mk_bv_srem_core`

_No discoveries yet._

### `bv_rewriter.mk_bv_urem_core`

_No discoveries yet._

### `bv_rewriter.mk_bv_smod_core`

_No discoveries yet._

### `bv_rewriter.mk_bv_sdiv`

_No discoveries yet._

### `bv_rewriter.mk_bv_udiv`

_No discoveries yet._

### `bv_rewriter.mk_bv_srem`

_No discoveries yet._

### `bv_rewriter.mk_bv_urem`

_No discoveries yet._

### `bv_rewriter.mk_bv_smod`

_No discoveries yet._

### `bv_rewriter.mk_bv_sdiv_i`

_No discoveries yet._

### `bv_rewriter.mk_bv_udiv_i`

_No discoveries yet._

### `bv_rewriter.mk_bv_srem_i`

_No discoveries yet._

### `bv_rewriter.mk_bv_urem_i`

_No discoveries yet._

### `bv_rewriter.mk_bv_smod_i`

_No discoveries yet._

### `bv_rewriter.mk_int2bv`

_No discoveries yet._

### `bv_rewriter.mk_ubv2int`

_No discoveries yet._

### `bv_rewriter.mk_sbv2int`

_No discoveries yet._

### `bv_rewriter.mk_bv_redor`

_No discoveries yet._

### `bv_rewriter.mk_bv_redand`

_No discoveries yet._

### `bv_rewriter.mk_bv_comp`

_No discoveries yet._

### `bv_rewriter.mk_bit2bool`

_No discoveries yet._

### `bv_rewriter.mk_bit2bool`

_No discoveries yet._

### `bv_rewriter.mk_blast_eq_value`

_No discoveries yet._

### `bv_rewriter.mk_eq_concat`

_No discoveries yet._

### `bv_rewriter.mk_mkbv`

_No discoveries yet._

### `bv_rewriter.mk_bvsmul_no_overflow`

_No discoveries yet._

### `bv_rewriter.mk_bvumul_no_overflow`

_No discoveries yet._

### `bv_rewriter.mk_bvsmul_overflow`

_No discoveries yet._

### `bv_rewriter.mk_bvumul_overflow`

_No discoveries yet._

### `bv_rewriter.mk_bvsdiv_overflow`

_No discoveries yet._

### `bv_rewriter.mk_bvneg_overflow`

_No discoveries yet._

### `bv_rewriter.mk_bvuadd_overflow`

_No discoveries yet._

### `bv_rewriter.mk_bvsadd_overflow`

_No discoveries yet._

### `bv_rewriter.mk_bvsadd_underflow`

_No discoveries yet._

### `bv_rewriter.mk_bvsadd_over_underflow`

_No discoveries yet._

### `bv_rewriter.mk_bvusub_underflow`

_No discoveries yet._

### `bv_rewriter.mk_bvssub_under_overflow`

_No discoveries yet._

### `bv_rewriter.is_minus_one_times_t`

_No discoveries yet._

### `bv_rewriter.mk_t1_add_t2_eq_c`

_No discoveries yet._

### `bv_rewriter.is_concat_split_target`

_No discoveries yet._

### `bv_rewriter.mk_mul_eq`

_No discoveries yet._

### `bv_rewriter.is_add_mul_const`

_No discoveries yet._

### `bv_rewriter.isolate_term`

_No discoveries yet._

### `bv_rewriter.has_numeral`

_No discoveries yet._

### `bv_rewriter.is_concat_target`

_No discoveries yet._

### `bv_rewriter.updt_local_params`

_No discoveries yet._

### `bv_rewriter.concat`

_No discoveries yet._

### `bv_rewriter.updt_params`

_No discoveries yet._

### `bv_rewriter.get_param_descrs`

_No discoveries yet._

### `bv_rewriter.set_mkbv2num`

_No discoveries yet._

### `bv_rewriter.get_bv_size`

_No discoveries yet._

### `bv_rewriter.is_numeral`

_No discoveries yet._

### `bv_rewriter.is_numeral`

_No discoveries yet._

### `bv_rewriter.is_bv`

_No discoveries yet._

### `bv_rewriter.mk_numeral`

_No discoveries yet._

### `bv_rewriter.mk_numeral`

_No discoveries yet._

### `bv_rewriter.mk_zero`

_No discoveries yet._

### `bv_rewriter.mk_one`

_No discoveries yet._

### `bv_rewriter.mk_zero`

_No discoveries yet._

### `bv_rewriter.mk_one`

_No discoveries yet._

### `bv_rewriter.mk_app_core`

_No discoveries yet._

### `bv_rewriter.mk_app`

_No discoveries yet._

### `bv_rewriter.is_urem_any`

_No discoveries yet._

### `bv_rewriter.mk_eq_core`

_No discoveries yet._

### `bv_rewriter.mk_eq_bv2int`

_No discoveries yet._

### `bv_rewriter.mk_ite_core`

_No discoveries yet._

### `bv_rewriter.mk_distinct`

_No discoveries yet._

### `bv_rewriter.hi_div0`

_No discoveries yet._

### `bv_rewriter.get_util`

_No discoveries yet._

### `bv_rewriter.is_eq_bit`

_No discoveries yet._

### `bv_rewriter.is_bit`

_No discoveries yet._

### `bv_rewriter.OP`

_No discoveries yet._

### `bv_rewriter.result`

_No discoveries yet._

### `bv_rewriter.mk_zero_extend`

_No discoveries yet._

### `bv_rewriter.result`

_No discoveries yet._

### `bv_rewriter.mk_ubv2int`

_No discoveries yet._

### `bv_rewriter.result`

_No discoveries yet._

### `bv_rewriter.mk_bv_neg`

_No discoveries yet._

### `bv_rewriter.result`

_No discoveries yet._

## Cross-References

_No cross-cutting discoveries yet._
