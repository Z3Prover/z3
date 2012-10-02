# Automatically generated file, generator: api.py
import sys, os
import ctypes
from z3types import *
from z3consts import *

def _find_lib():
  _dir = os.path.dirname(os.path.abspath(__file__))
  libs = ['z3.dll', 'libz3.so', 'libz3.dylib']
  if sys.maxsize > 2**32:
     winlibdir = 'x64'
  else:
     winlibdir = 'bin'
  locs = [_dir, '%s%s..%s%s' % (_dir, os.sep, os.sep, winlibdir), '%s%s..%slib' % (_dir, os.sep, os.sep), '%s%s..%sexternal' % (_dir, os.sep, os.sep), '%s%s..%sbin%sexternal' % (_dir, os.sep, os.sep, os.sep)]
  for loc in locs:
    for lib in libs:
      f = '%s%s%s' % (loc, os.sep, lib)
      if os.path.exists(f):
        return f
  return None

_lib = None
def lib():
  if _lib == None:
    l = _find_lib()
    if l == None:
      raise Z3Exception("init(Z3_LIBRARY_PATH) must be invoked before using Z3-python")
    init(l)
    assert _lib != None
  return _lib

def init(PATH):
  global _lib
  _lib = ctypes.CDLL(PATH)
  _lib.Z3_mk_config.restype = Config
  _lib.Z3_mk_config.argtypes = []
  _lib.Z3_del_config.argtypes = [Config]
  _lib.Z3_set_param_value.argtypes = [Config, ctypes.c_char_p, ctypes.c_char_p]
  _lib.Z3_mk_context.restype = ContextObj
  _lib.Z3_mk_context.argtypes = [Config]
  _lib.Z3_mk_context_rc.restype = ContextObj
  _lib.Z3_mk_context_rc.argtypes = [Config]
  _lib.Z3_set_logic.argtypes = [ContextObj, ctypes.c_char_p]
  _lib.Z3_del_context.argtypes = [ContextObj]
  _lib.Z3_inc_ref.argtypes = [ContextObj, Ast]
  _lib.Z3_dec_ref.argtypes = [ContextObj, Ast]
  _lib.Z3_toggle_warning_messages.argtypes = [ctypes.c_bool]
  _lib.Z3_update_param_value.argtypes = [ContextObj, ctypes.c_char_p, ctypes.c_char_p]
  _lib.Z3_get_param_value.restype = ctypes.c_bool
  _lib.Z3_get_param_value.argtypes = [ContextObj, ctypes.c_char_p, ctypes.POINTER(ctypes.c_char_p)]
  _lib.Z3_mk_int_symbol.restype = Symbol
  _lib.Z3_mk_int_symbol.argtypes = [ContextObj, ctypes.c_int]
  _lib.Z3_mk_string_symbol.restype = Symbol
  _lib.Z3_mk_string_symbol.argtypes = [ContextObj, ctypes.c_char_p]
  _lib.Z3_is_eq_sort.restype = ctypes.c_bool
  _lib.Z3_is_eq_sort.argtypes = [ContextObj, Sort, Sort]
  _lib.Z3_mk_uninterpreted_sort.restype = Sort
  _lib.Z3_mk_uninterpreted_sort.argtypes = [ContextObj, Symbol]
  _lib.Z3_mk_bool_sort.restype = Sort
  _lib.Z3_mk_bool_sort.argtypes = [ContextObj]
  _lib.Z3_mk_int_sort.restype = Sort
  _lib.Z3_mk_int_sort.argtypes = [ContextObj]
  _lib.Z3_mk_real_sort.restype = Sort
  _lib.Z3_mk_real_sort.argtypes = [ContextObj]
  _lib.Z3_mk_bv_sort.restype = Sort
  _lib.Z3_mk_bv_sort.argtypes = [ContextObj, ctypes.c_uint]
  _lib.Z3_mk_array_sort.restype = Sort
  _lib.Z3_mk_array_sort.argtypes = [ContextObj, Sort, Sort]
  _lib.Z3_mk_tuple_sort.restype = Sort
  _lib.Z3_mk_tuple_sort.argtypes = [ContextObj, Symbol, ctypes.c_uint, ctypes.POINTER(Symbol), ctypes.POINTER(Sort), ctypes.POINTER(FuncDecl), ctypes.POINTER(FuncDecl)]
  _lib.Z3_mk_enumeration_sort.restype = Sort
  _lib.Z3_mk_enumeration_sort.argtypes = [ContextObj, Symbol, ctypes.c_uint, ctypes.POINTER(Symbol), ctypes.POINTER(FuncDecl), ctypes.POINTER(FuncDecl)]
  _lib.Z3_mk_list_sort.restype = Sort
  _lib.Z3_mk_list_sort.argtypes = [ContextObj, Symbol, Sort, ctypes.POINTER(FuncDecl), ctypes.POINTER(FuncDecl), ctypes.POINTER(FuncDecl), ctypes.POINTER(FuncDecl), ctypes.POINTER(FuncDecl), ctypes.POINTER(FuncDecl)]
  _lib.Z3_mk_constructor.restype = Constructor
  _lib.Z3_mk_constructor.argtypes = [ContextObj, Symbol, Symbol, ctypes.c_uint, ctypes.POINTER(Symbol), ctypes.POINTER(Sort), ctypes.POINTER(ctypes.c_uint)]
  _lib.Z3_query_constructor.argtypes = [ContextObj, Constructor, ctypes.c_uint, ctypes.POINTER(FuncDecl), ctypes.POINTER(FuncDecl), ctypes.POINTER(FuncDecl)]
  _lib.Z3_del_constructor.argtypes = [ContextObj, Constructor]
  _lib.Z3_mk_datatype.restype = Sort
  _lib.Z3_mk_datatype.argtypes = [ContextObj, Symbol, ctypes.c_uint, ctypes.POINTER(Constructor)]
  _lib.Z3_mk_constructor_list.restype = ConstructorList
  _lib.Z3_mk_constructor_list.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(Constructor)]
  _lib.Z3_del_constructor_list.argtypes = [ContextObj, ConstructorList]
  _lib.Z3_mk_datatypes.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(Symbol), ctypes.POINTER(Sort), ctypes.POINTER(ConstructorList)]
  _lib.Z3_is_eq_ast.restype = ctypes.c_bool
  _lib.Z3_is_eq_ast.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_is_eq_func_decl.restype = ctypes.c_bool
  _lib.Z3_is_eq_func_decl.argtypes = [ContextObj, FuncDecl, FuncDecl]
  _lib.Z3_mk_func_decl.restype = FuncDecl
  _lib.Z3_mk_func_decl.argtypes = [ContextObj, Symbol, ctypes.c_uint, ctypes.POINTER(Sort), Sort]
  _lib.Z3_mk_app.restype = Ast
  _lib.Z3_mk_app.argtypes = [ContextObj, FuncDecl, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_mk_const.restype = Ast
  _lib.Z3_mk_const.argtypes = [ContextObj, Symbol, Sort]
  _lib.Z3_mk_label.restype = Ast
  _lib.Z3_mk_label.argtypes = [ContextObj, Symbol, ctypes.c_bool, Ast]
  _lib.Z3_mk_fresh_func_decl.restype = FuncDecl
  _lib.Z3_mk_fresh_func_decl.argtypes = [ContextObj, ctypes.c_char_p, ctypes.c_uint, ctypes.POINTER(Sort), Sort]
  _lib.Z3_mk_fresh_const.restype = Ast
  _lib.Z3_mk_fresh_const.argtypes = [ContextObj, ctypes.c_char_p, Sort]
  _lib.Z3_mk_true.restype = Ast
  _lib.Z3_mk_true.argtypes = [ContextObj]
  _lib.Z3_mk_false.restype = Ast
  _lib.Z3_mk_false.argtypes = [ContextObj]
  _lib.Z3_mk_eq.restype = Ast
  _lib.Z3_mk_eq.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_distinct.restype = Ast
  _lib.Z3_mk_distinct.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_mk_not.restype = Ast
  _lib.Z3_mk_not.argtypes = [ContextObj, Ast]
  _lib.Z3_mk_ite.restype = Ast
  _lib.Z3_mk_ite.argtypes = [ContextObj, Ast, Ast, Ast]
  _lib.Z3_mk_iff.restype = Ast
  _lib.Z3_mk_iff.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_implies.restype = Ast
  _lib.Z3_mk_implies.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_xor.restype = Ast
  _lib.Z3_mk_xor.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_and.restype = Ast
  _lib.Z3_mk_and.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_mk_or.restype = Ast
  _lib.Z3_mk_or.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_mk_add.restype = Ast
  _lib.Z3_mk_add.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_mk_mul.restype = Ast
  _lib.Z3_mk_mul.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_mk_sub.restype = Ast
  _lib.Z3_mk_sub.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_mk_unary_minus.restype = Ast
  _lib.Z3_mk_unary_minus.argtypes = [ContextObj, Ast]
  _lib.Z3_mk_div.restype = Ast
  _lib.Z3_mk_div.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_mod.restype = Ast
  _lib.Z3_mk_mod.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_rem.restype = Ast
  _lib.Z3_mk_rem.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_power.restype = Ast
  _lib.Z3_mk_power.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_is_algebraic_number.restype = ctypes.c_bool
  _lib.Z3_is_algebraic_number.argtypes = [ContextObj, Ast]
  _lib.Z3_get_algebraic_number_lower.restype = Ast
  _lib.Z3_get_algebraic_number_lower.argtypes = [ContextObj, Ast, ctypes.c_uint]
  _lib.Z3_get_algebraic_number_upper.restype = Ast
  _lib.Z3_get_algebraic_number_upper.argtypes = [ContextObj, Ast, ctypes.c_uint]
  _lib.Z3_mk_lt.restype = Ast
  _lib.Z3_mk_lt.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_le.restype = Ast
  _lib.Z3_mk_le.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_gt.restype = Ast
  _lib.Z3_mk_gt.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_ge.restype = Ast
  _lib.Z3_mk_ge.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_int2real.restype = Ast
  _lib.Z3_mk_int2real.argtypes = [ContextObj, Ast]
  _lib.Z3_mk_real2int.restype = Ast
  _lib.Z3_mk_real2int.argtypes = [ContextObj, Ast]
  _lib.Z3_mk_is_int.restype = Ast
  _lib.Z3_mk_is_int.argtypes = [ContextObj, Ast]
  _lib.Z3_mk_bvnot.restype = Ast
  _lib.Z3_mk_bvnot.argtypes = [ContextObj, Ast]
  _lib.Z3_mk_bvredand.restype = Ast
  _lib.Z3_mk_bvredand.argtypes = [ContextObj, Ast]
  _lib.Z3_mk_bvredor.restype = Ast
  _lib.Z3_mk_bvredor.argtypes = [ContextObj, Ast]
  _lib.Z3_mk_bvand.restype = Ast
  _lib.Z3_mk_bvand.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvor.restype = Ast
  _lib.Z3_mk_bvor.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvxor.restype = Ast
  _lib.Z3_mk_bvxor.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvnand.restype = Ast
  _lib.Z3_mk_bvnand.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvnor.restype = Ast
  _lib.Z3_mk_bvnor.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvxnor.restype = Ast
  _lib.Z3_mk_bvxnor.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvneg.restype = Ast
  _lib.Z3_mk_bvneg.argtypes = [ContextObj, Ast]
  _lib.Z3_mk_bvadd.restype = Ast
  _lib.Z3_mk_bvadd.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvsub.restype = Ast
  _lib.Z3_mk_bvsub.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvmul.restype = Ast
  _lib.Z3_mk_bvmul.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvudiv.restype = Ast
  _lib.Z3_mk_bvudiv.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvsdiv.restype = Ast
  _lib.Z3_mk_bvsdiv.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvurem.restype = Ast
  _lib.Z3_mk_bvurem.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvsrem.restype = Ast
  _lib.Z3_mk_bvsrem.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvsmod.restype = Ast
  _lib.Z3_mk_bvsmod.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvult.restype = Ast
  _lib.Z3_mk_bvult.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvslt.restype = Ast
  _lib.Z3_mk_bvslt.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvule.restype = Ast
  _lib.Z3_mk_bvule.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvsle.restype = Ast
  _lib.Z3_mk_bvsle.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvuge.restype = Ast
  _lib.Z3_mk_bvuge.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvsge.restype = Ast
  _lib.Z3_mk_bvsge.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvugt.restype = Ast
  _lib.Z3_mk_bvugt.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvsgt.restype = Ast
  _lib.Z3_mk_bvsgt.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_concat.restype = Ast
  _lib.Z3_mk_concat.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_extract.restype = Ast
  _lib.Z3_mk_extract.argtypes = [ContextObj, ctypes.c_uint, ctypes.c_uint, Ast]
  _lib.Z3_mk_sign_ext.restype = Ast
  _lib.Z3_mk_sign_ext.argtypes = [ContextObj, ctypes.c_uint, Ast]
  _lib.Z3_mk_zero_ext.restype = Ast
  _lib.Z3_mk_zero_ext.argtypes = [ContextObj, ctypes.c_uint, Ast]
  _lib.Z3_mk_repeat.restype = Ast
  _lib.Z3_mk_repeat.argtypes = [ContextObj, ctypes.c_uint, Ast]
  _lib.Z3_mk_bvshl.restype = Ast
  _lib.Z3_mk_bvshl.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvlshr.restype = Ast
  _lib.Z3_mk_bvlshr.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvashr.restype = Ast
  _lib.Z3_mk_bvashr.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_rotate_left.restype = Ast
  _lib.Z3_mk_rotate_left.argtypes = [ContextObj, ctypes.c_uint, Ast]
  _lib.Z3_mk_rotate_right.restype = Ast
  _lib.Z3_mk_rotate_right.argtypes = [ContextObj, ctypes.c_uint, Ast]
  _lib.Z3_mk_ext_rotate_left.restype = Ast
  _lib.Z3_mk_ext_rotate_left.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_ext_rotate_right.restype = Ast
  _lib.Z3_mk_ext_rotate_right.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_int2bv.restype = Ast
  _lib.Z3_mk_int2bv.argtypes = [ContextObj, ctypes.c_uint, Ast]
  _lib.Z3_mk_bv2int.restype = Ast
  _lib.Z3_mk_bv2int.argtypes = [ContextObj, Ast, ctypes.c_bool]
  _lib.Z3_mk_bvadd_no_overflow.restype = Ast
  _lib.Z3_mk_bvadd_no_overflow.argtypes = [ContextObj, Ast, Ast, ctypes.c_bool]
  _lib.Z3_mk_bvadd_no_underflow.restype = Ast
  _lib.Z3_mk_bvadd_no_underflow.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvsub_no_overflow.restype = Ast
  _lib.Z3_mk_bvsub_no_overflow.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvsub_no_underflow.restype = Ast
  _lib.Z3_mk_bvsub_no_underflow.argtypes = [ContextObj, Ast, Ast, ctypes.c_bool]
  _lib.Z3_mk_bvsdiv_no_overflow.restype = Ast
  _lib.Z3_mk_bvsdiv_no_overflow.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_bvneg_no_overflow.restype = Ast
  _lib.Z3_mk_bvneg_no_overflow.argtypes = [ContextObj, Ast]
  _lib.Z3_mk_bvmul_no_overflow.restype = Ast
  _lib.Z3_mk_bvmul_no_overflow.argtypes = [ContextObj, Ast, Ast, ctypes.c_bool]
  _lib.Z3_mk_bvmul_no_underflow.restype = Ast
  _lib.Z3_mk_bvmul_no_underflow.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_select.restype = Ast
  _lib.Z3_mk_select.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_store.restype = Ast
  _lib.Z3_mk_store.argtypes = [ContextObj, Ast, Ast, Ast]
  _lib.Z3_mk_const_array.restype = Ast
  _lib.Z3_mk_const_array.argtypes = [ContextObj, Sort, Ast]
  _lib.Z3_mk_map.restype = Ast
  _lib.Z3_mk_map.argtypes = [ContextObj, FuncDecl, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_mk_array_default.restype = Ast
  _lib.Z3_mk_array_default.argtypes = [ContextObj, Ast]
  _lib.Z3_mk_set_sort.restype = Sort
  _lib.Z3_mk_set_sort.argtypes = [ContextObj, Sort]
  _lib.Z3_mk_empty_set.restype = Ast
  _lib.Z3_mk_empty_set.argtypes = [ContextObj, Sort]
  _lib.Z3_mk_full_set.restype = Ast
  _lib.Z3_mk_full_set.argtypes = [ContextObj, Sort]
  _lib.Z3_mk_set_add.restype = Ast
  _lib.Z3_mk_set_add.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_set_del.restype = Ast
  _lib.Z3_mk_set_del.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_set_union.restype = Ast
  _lib.Z3_mk_set_union.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_mk_set_intersect.restype = Ast
  _lib.Z3_mk_set_intersect.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_mk_set_difference.restype = Ast
  _lib.Z3_mk_set_difference.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_set_complement.restype = Ast
  _lib.Z3_mk_set_complement.argtypes = [ContextObj, Ast]
  _lib.Z3_mk_set_member.restype = Ast
  _lib.Z3_mk_set_member.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_set_subset.restype = Ast
  _lib.Z3_mk_set_subset.argtypes = [ContextObj, Ast, Ast]
  _lib.Z3_mk_numeral.restype = Ast
  _lib.Z3_mk_numeral.argtypes = [ContextObj, ctypes.c_char_p, Sort]
  _lib.Z3_mk_real.restype = Ast
  _lib.Z3_mk_real.argtypes = [ContextObj, ctypes.c_int, ctypes.c_int]
  _lib.Z3_mk_int.restype = Ast
  _lib.Z3_mk_int.argtypes = [ContextObj, ctypes.c_int, Sort]
  _lib.Z3_mk_unsigned_int.restype = Ast
  _lib.Z3_mk_unsigned_int.argtypes = [ContextObj, ctypes.c_uint, Sort]
  _lib.Z3_mk_int64.restype = Ast
  _lib.Z3_mk_int64.argtypes = [ContextObj, ctypes.c_longlong, Sort]
  _lib.Z3_mk_unsigned_int64.restype = Ast
  _lib.Z3_mk_unsigned_int64.argtypes = [ContextObj, ctypes.c_ulonglong, Sort]
  _lib.Z3_mk_pattern.restype = Pattern
  _lib.Z3_mk_pattern.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_mk_bound.restype = Ast
  _lib.Z3_mk_bound.argtypes = [ContextObj, ctypes.c_uint, Sort]
  _lib.Z3_mk_forall.restype = Ast
  _lib.Z3_mk_forall.argtypes = [ContextObj, ctypes.c_uint, ctypes.c_uint, ctypes.POINTER(Pattern), ctypes.c_uint, ctypes.POINTER(Sort), ctypes.POINTER(Symbol), Ast]
  _lib.Z3_mk_exists.restype = Ast
  _lib.Z3_mk_exists.argtypes = [ContextObj, ctypes.c_uint, ctypes.c_uint, ctypes.POINTER(Pattern), ctypes.c_uint, ctypes.POINTER(Sort), ctypes.POINTER(Symbol), Ast]
  _lib.Z3_mk_quantifier.restype = Ast
  _lib.Z3_mk_quantifier.argtypes = [ContextObj, ctypes.c_bool, ctypes.c_uint, ctypes.c_uint, ctypes.POINTER(Pattern), ctypes.c_uint, ctypes.POINTER(Sort), ctypes.POINTER(Symbol), Ast]
  _lib.Z3_mk_quantifier_ex.restype = Ast
  _lib.Z3_mk_quantifier_ex.argtypes = [ContextObj, ctypes.c_bool, ctypes.c_uint, Symbol, Symbol, ctypes.c_uint, ctypes.POINTER(Pattern), ctypes.c_uint, ctypes.POINTER(Ast), ctypes.c_uint, ctypes.POINTER(Sort), ctypes.POINTER(Symbol), Ast]
  _lib.Z3_mk_forall_const.restype = Ast
  _lib.Z3_mk_forall_const.argtypes = [ContextObj, ctypes.c_uint, ctypes.c_uint, ctypes.POINTER(Ast), ctypes.c_uint, ctypes.POINTER(Pattern), Ast]
  _lib.Z3_mk_exists_const.restype = Ast
  _lib.Z3_mk_exists_const.argtypes = [ContextObj, ctypes.c_uint, ctypes.c_uint, ctypes.POINTER(Ast), ctypes.c_uint, ctypes.POINTER(Pattern), Ast]
  _lib.Z3_mk_quantifier_const.restype = Ast
  _lib.Z3_mk_quantifier_const.argtypes = [ContextObj, ctypes.c_bool, ctypes.c_uint, ctypes.c_uint, ctypes.POINTER(Ast), ctypes.c_uint, ctypes.POINTER(Pattern), Ast]
  _lib.Z3_mk_quantifier_const_ex.restype = Ast
  _lib.Z3_mk_quantifier_const_ex.argtypes = [ContextObj, ctypes.c_bool, ctypes.c_uint, Symbol, Symbol, ctypes.c_uint, ctypes.POINTER(Ast), ctypes.c_uint, ctypes.POINTER(Pattern), ctypes.c_uint, ctypes.POINTER(Ast), Ast]
  _lib.Z3_get_ast_id.restype = ctypes.c_uint
  _lib.Z3_get_ast_id.argtypes = [ContextObj, Ast]
  _lib.Z3_get_func_decl_id.restype = ctypes.c_uint
  _lib.Z3_get_func_decl_id.argtypes = [ContextObj, FuncDecl]
  _lib.Z3_get_sort_id.restype = ctypes.c_uint
  _lib.Z3_get_sort_id.argtypes = [ContextObj, Sort]
  _lib.Z3_is_well_sorted.restype = ctypes.c_bool
  _lib.Z3_is_well_sorted.argtypes = [ContextObj, Ast]
  _lib.Z3_get_symbol_kind.restype = ctypes.c_uint
  _lib.Z3_get_symbol_kind.argtypes = [ContextObj, Symbol]
  _lib.Z3_get_symbol_int.restype = ctypes.c_int
  _lib.Z3_get_symbol_int.argtypes = [ContextObj, Symbol]
  _lib.Z3_get_symbol_string.restype = ctypes.c_char_p
  _lib.Z3_get_symbol_string.argtypes = [ContextObj, Symbol]
  _lib.Z3_get_ast_kind.restype = ctypes.c_uint
  _lib.Z3_get_ast_kind.argtypes = [ContextObj, Ast]
  _lib.Z3_get_ast_hash.restype = ctypes.c_uint
  _lib.Z3_get_ast_hash.argtypes = [ContextObj, Ast]
  _lib.Z3_get_numeral_string.restype = ctypes.c_char_p
  _lib.Z3_get_numeral_string.argtypes = [ContextObj, Ast]
  _lib.Z3_get_numeral_decimal_string.restype = ctypes.c_char_p
  _lib.Z3_get_numeral_decimal_string.argtypes = [ContextObj, Ast, ctypes.c_uint]
  _lib.Z3_get_numerator.restype = Ast
  _lib.Z3_get_numerator.argtypes = [ContextObj, Ast]
  _lib.Z3_get_denominator.restype = Ast
  _lib.Z3_get_denominator.argtypes = [ContextObj, Ast]
  _lib.Z3_get_numeral_small.restype = ctypes.c_bool
  _lib.Z3_get_numeral_small.argtypes = [ContextObj, Ast, ctypes.POINTER(ctypes.c_longlong), ctypes.POINTER(ctypes.c_longlong)]
  _lib.Z3_get_numeral_int.restype = ctypes.c_bool
  _lib.Z3_get_numeral_int.argtypes = [ContextObj, Ast, ctypes.POINTER(ctypes.c_int)]
  _lib.Z3_get_numeral_uint.restype = ctypes.c_bool
  _lib.Z3_get_numeral_uint.argtypes = [ContextObj, Ast, ctypes.POINTER(ctypes.c_uint)]
  _lib.Z3_get_numeral_uint64.restype = ctypes.c_bool
  _lib.Z3_get_numeral_uint64.argtypes = [ContextObj, Ast, ctypes.POINTER(ctypes.c_ulonglong)]
  _lib.Z3_get_numeral_int64.restype = ctypes.c_bool
  _lib.Z3_get_numeral_int64.argtypes = [ContextObj, Ast, ctypes.POINTER(ctypes.c_longlong)]
  _lib.Z3_get_numeral_rational_int64.restype = ctypes.c_bool
  _lib.Z3_get_numeral_rational_int64.argtypes = [ContextObj, Ast, ctypes.POINTER(ctypes.c_longlong), ctypes.POINTER(ctypes.c_longlong)]
  _lib.Z3_get_bool_value.restype = ctypes.c_uint
  _lib.Z3_get_bool_value.argtypes = [ContextObj, Ast]
  _lib.Z3_get_app_decl.restype = FuncDecl
  _lib.Z3_get_app_decl.argtypes = [ContextObj, Ast]
  _lib.Z3_get_app_num_args.restype = ctypes.c_uint
  _lib.Z3_get_app_num_args.argtypes = [ContextObj, Ast]
  _lib.Z3_get_app_arg.restype = Ast
  _lib.Z3_get_app_arg.argtypes = [ContextObj, Ast, ctypes.c_uint]
  _lib.Z3_get_index_value.restype = ctypes.c_uint
  _lib.Z3_get_index_value.argtypes = [ContextObj, Ast]
  _lib.Z3_is_quantifier_forall.restype = ctypes.c_bool
  _lib.Z3_is_quantifier_forall.argtypes = [ContextObj, Ast]
  _lib.Z3_get_quantifier_weight.restype = ctypes.c_uint
  _lib.Z3_get_quantifier_weight.argtypes = [ContextObj, Ast]
  _lib.Z3_get_quantifier_num_patterns.restype = ctypes.c_uint
  _lib.Z3_get_quantifier_num_patterns.argtypes = [ContextObj, Ast]
  _lib.Z3_get_quantifier_pattern_ast.restype = Pattern
  _lib.Z3_get_quantifier_pattern_ast.argtypes = [ContextObj, Ast, ctypes.c_uint]
  _lib.Z3_get_quantifier_num_no_patterns.restype = ctypes.c_uint
  _lib.Z3_get_quantifier_num_no_patterns.argtypes = [ContextObj, Ast]
  _lib.Z3_get_quantifier_no_pattern_ast.restype = Ast
  _lib.Z3_get_quantifier_no_pattern_ast.argtypes = [ContextObj, Ast, ctypes.c_uint]
  _lib.Z3_get_quantifier_bound_name.restype = Symbol
  _lib.Z3_get_quantifier_bound_name.argtypes = [ContextObj, Ast, ctypes.c_uint]
  _lib.Z3_get_quantifier_bound_sort.restype = Sort
  _lib.Z3_get_quantifier_bound_sort.argtypes = [ContextObj, Ast, ctypes.c_uint]
  _lib.Z3_get_quantifier_body.restype = Ast
  _lib.Z3_get_quantifier_body.argtypes = [ContextObj, Ast]
  _lib.Z3_get_quantifier_num_bound.restype = ctypes.c_uint
  _lib.Z3_get_quantifier_num_bound.argtypes = [ContextObj, Ast]
  _lib.Z3_get_decl_name.restype = Symbol
  _lib.Z3_get_decl_name.argtypes = [ContextObj, FuncDecl]
  _lib.Z3_get_decl_num_parameters.restype = ctypes.c_uint
  _lib.Z3_get_decl_num_parameters.argtypes = [ContextObj, FuncDecl]
  _lib.Z3_get_decl_parameter_kind.restype = ctypes.c_uint
  _lib.Z3_get_decl_parameter_kind.argtypes = [ContextObj, FuncDecl, ctypes.c_uint]
  _lib.Z3_get_decl_int_parameter.restype = ctypes.c_int
  _lib.Z3_get_decl_int_parameter.argtypes = [ContextObj, FuncDecl, ctypes.c_uint]
  _lib.Z3_get_decl_double_parameter.restype = ctypes.c_double
  _lib.Z3_get_decl_double_parameter.argtypes = [ContextObj, FuncDecl, ctypes.c_uint]
  _lib.Z3_get_decl_symbol_parameter.restype = Symbol
  _lib.Z3_get_decl_symbol_parameter.argtypes = [ContextObj, FuncDecl, ctypes.c_uint]
  _lib.Z3_get_decl_sort_parameter.restype = Sort
  _lib.Z3_get_decl_sort_parameter.argtypes = [ContextObj, FuncDecl, ctypes.c_uint]
  _lib.Z3_get_decl_ast_parameter.restype = Ast
  _lib.Z3_get_decl_ast_parameter.argtypes = [ContextObj, FuncDecl, ctypes.c_uint]
  _lib.Z3_get_decl_func_decl_parameter.restype = FuncDecl
  _lib.Z3_get_decl_func_decl_parameter.argtypes = [ContextObj, FuncDecl, ctypes.c_uint]
  _lib.Z3_get_decl_rational_parameter.restype = ctypes.c_char_p
  _lib.Z3_get_decl_rational_parameter.argtypes = [ContextObj, FuncDecl, ctypes.c_uint]
  _lib.Z3_get_sort_name.restype = Symbol
  _lib.Z3_get_sort_name.argtypes = [ContextObj, Sort]
  _lib.Z3_get_sort.restype = Sort
  _lib.Z3_get_sort.argtypes = [ContextObj, Ast]
  _lib.Z3_get_domain_size.restype = ctypes.c_uint
  _lib.Z3_get_domain_size.argtypes = [ContextObj, FuncDecl]
  _lib.Z3_get_domain.restype = Sort
  _lib.Z3_get_domain.argtypes = [ContextObj, FuncDecl, ctypes.c_uint]
  _lib.Z3_get_range.restype = Sort
  _lib.Z3_get_range.argtypes = [ContextObj, FuncDecl]
  _lib.Z3_get_sort_kind.restype = ctypes.c_uint
  _lib.Z3_get_sort_kind.argtypes = [ContextObj, Sort]
  _lib.Z3_get_bv_sort_size.restype = ctypes.c_uint
  _lib.Z3_get_bv_sort_size.argtypes = [ContextObj, Sort]
  _lib.Z3_get_array_sort_domain.restype = Sort
  _lib.Z3_get_array_sort_domain.argtypes = [ContextObj, Sort]
  _lib.Z3_get_array_sort_range.restype = Sort
  _lib.Z3_get_array_sort_range.argtypes = [ContextObj, Sort]
  _lib.Z3_get_tuple_sort_mk_decl.restype = FuncDecl
  _lib.Z3_get_tuple_sort_mk_decl.argtypes = [ContextObj, Sort]
  _lib.Z3_get_decl_kind.restype = ctypes.c_uint
  _lib.Z3_get_decl_kind.argtypes = [ContextObj, FuncDecl]
  _lib.Z3_get_tuple_sort_num_fields.restype = ctypes.c_uint
  _lib.Z3_get_tuple_sort_num_fields.argtypes = [ContextObj, Sort]
  _lib.Z3_get_tuple_sort_field_decl.restype = FuncDecl
  _lib.Z3_get_tuple_sort_field_decl.argtypes = [ContextObj, Sort, ctypes.c_uint]
  _lib.Z3_get_datatype_sort_num_constructors.restype = ctypes.c_uint
  _lib.Z3_get_datatype_sort_num_constructors.argtypes = [ContextObj, Sort]
  _lib.Z3_get_datatype_sort_constructor.restype = FuncDecl
  _lib.Z3_get_datatype_sort_constructor.argtypes = [ContextObj, Sort, ctypes.c_uint]
  _lib.Z3_get_datatype_sort_recognizer.restype = FuncDecl
  _lib.Z3_get_datatype_sort_recognizer.argtypes = [ContextObj, Sort, ctypes.c_uint]
  _lib.Z3_get_datatype_sort_constructor_accessor.restype = FuncDecl
  _lib.Z3_get_datatype_sort_constructor_accessor.argtypes = [ContextObj, Sort, ctypes.c_uint, ctypes.c_uint]
  _lib.Z3_get_relation_arity.restype = ctypes.c_uint
  _lib.Z3_get_relation_arity.argtypes = [ContextObj, Sort]
  _lib.Z3_get_relation_column.restype = Sort
  _lib.Z3_get_relation_column.argtypes = [ContextObj, Sort, ctypes.c_uint]
  _lib.Z3_get_finite_domain_sort_size.restype = ctypes.c_bool
  _lib.Z3_get_finite_domain_sort_size.argtypes = [ContextObj, Sort, ctypes.POINTER(ctypes.c_ulonglong)]
  _lib.Z3_mk_finite_domain_sort.restype = Sort
  _lib.Z3_mk_finite_domain_sort.argtypes = [ContextObj, Symbol, ctypes.c_ulonglong]
  _lib.Z3_get_pattern_num_terms.restype = ctypes.c_uint
  _lib.Z3_get_pattern_num_terms.argtypes = [ContextObj, Pattern]
  _lib.Z3_get_pattern.restype = Ast
  _lib.Z3_get_pattern.argtypes = [ContextObj, Pattern, ctypes.c_uint]
  _lib.Z3_simplify.restype = Ast
  _lib.Z3_simplify.argtypes = [ContextObj, Ast]
  _lib.Z3_simplify_ex.restype = Ast
  _lib.Z3_simplify_ex.argtypes = [ContextObj, Ast, Params]
  _lib.Z3_simplify_get_help.restype = ctypes.c_char_p
  _lib.Z3_simplify_get_help.argtypes = [ContextObj]
  _lib.Z3_simplify_get_param_descrs.restype = ParamDescrs
  _lib.Z3_simplify_get_param_descrs.argtypes = [ContextObj]
  _lib.Z3_update_term.restype = Ast
  _lib.Z3_update_term.argtypes = [ContextObj, Ast, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_substitute.restype = Ast
  _lib.Z3_substitute.argtypes = [ContextObj, Ast, ctypes.c_uint, ctypes.POINTER(Ast), ctypes.POINTER(Ast)]
  _lib.Z3_substitute_vars.restype = Ast
  _lib.Z3_substitute_vars.argtypes = [ContextObj, Ast, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_sort_to_ast.restype = Ast
  _lib.Z3_sort_to_ast.argtypes = [ContextObj, Sort]
  _lib.Z3_func_decl_to_ast.restype = Ast
  _lib.Z3_func_decl_to_ast.argtypes = [ContextObj, FuncDecl]
  _lib.Z3_pattern_to_ast.restype = Ast
  _lib.Z3_pattern_to_ast.argtypes = [ContextObj, Pattern]
  _lib.Z3_app_to_ast.restype = Ast
  _lib.Z3_app_to_ast.argtypes = [ContextObj, Ast]
  _lib.Z3_to_app.restype = Ast
  _lib.Z3_to_app.argtypes = [ContextObj, Ast]
  _lib.Z3_to_func_decl.restype = FuncDecl
  _lib.Z3_to_func_decl.argtypes = [ContextObj, Ast]
  _lib.Z3_push.argtypes = [ContextObj]
  _lib.Z3_pop.argtypes = [ContextObj, ctypes.c_uint]
  _lib.Z3_get_num_scopes.restype = ctypes.c_uint
  _lib.Z3_get_num_scopes.argtypes = [ContextObj]
  _lib.Z3_persist_ast.argtypes = [ContextObj, Ast, ctypes.c_uint]
  _lib.Z3_assert_cnstr.argtypes = [ContextObj, Ast]
  _lib.Z3_check_and_get_model.restype = ctypes.c_int
  _lib.Z3_check_and_get_model.argtypes = [ContextObj, ctypes.POINTER(Model)]
  _lib.Z3_check.restype = ctypes.c_int
  _lib.Z3_check.argtypes = [ContextObj]
  _lib.Z3_check_assumptions.restype = ctypes.c_int
  _lib.Z3_check_assumptions.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(Ast), ctypes.POINTER(Model), ctypes.POINTER(Ast), ctypes.POINTER(ctypes.c_uint), ctypes.POINTER(Ast)]
  _lib.Z3_get_implied_equalities.restype = ctypes.c_uint
  _lib.Z3_get_implied_equalities.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(Ast), ctypes.POINTER(ctypes.c_uint)]
  _lib.Z3_del_model.argtypes = [ContextObj, Model]
  _lib.Z3_soft_check_cancel.argtypes = [ContextObj]
  _lib.Z3_get_search_failure.restype = ctypes.c_uint
  _lib.Z3_get_search_failure.argtypes = [ContextObj]
  _lib.Z3_get_relevant_labels.restype = Literals
  _lib.Z3_get_relevant_labels.argtypes = [ContextObj]
  _lib.Z3_get_relevant_literals.restype = Literals
  _lib.Z3_get_relevant_literals.argtypes = [ContextObj]
  _lib.Z3_get_guessed_literals.restype = Literals
  _lib.Z3_get_guessed_literals.argtypes = [ContextObj]
  _lib.Z3_del_literals.argtypes = [ContextObj, Literals]
  _lib.Z3_get_num_literals.restype = ctypes.c_uint
  _lib.Z3_get_num_literals.argtypes = [ContextObj, Literals]
  _lib.Z3_get_label_symbol.restype = Symbol
  _lib.Z3_get_label_symbol.argtypes = [ContextObj, Literals, ctypes.c_uint]
  _lib.Z3_get_literal.restype = Ast
  _lib.Z3_get_literal.argtypes = [ContextObj, Literals, ctypes.c_uint]
  _lib.Z3_disable_literal.argtypes = [ContextObj, Literals, ctypes.c_uint]
  _lib.Z3_block_literals.argtypes = [ContextObj, Literals]
  _lib.Z3_model_inc_ref.argtypes = [ContextObj, Model]
  _lib.Z3_model_dec_ref.argtypes = [ContextObj, Model]
  _lib.Z3_model_get_const_interp.restype = Ast
  _lib.Z3_model_get_const_interp.argtypes = [ContextObj, Model, FuncDecl]
  _lib.Z3_model_get_func_interp.restype = FuncInterpObj
  _lib.Z3_model_get_func_interp.argtypes = [ContextObj, Model, FuncDecl]
  _lib.Z3_model_get_num_consts.restype = ctypes.c_uint
  _lib.Z3_model_get_num_consts.argtypes = [ContextObj, Model]
  _lib.Z3_model_get_const_decl.restype = FuncDecl
  _lib.Z3_model_get_const_decl.argtypes = [ContextObj, Model, ctypes.c_uint]
  _lib.Z3_model_get_num_funcs.restype = ctypes.c_uint
  _lib.Z3_model_get_num_funcs.argtypes = [ContextObj, Model]
  _lib.Z3_model_get_func_decl.restype = FuncDecl
  _lib.Z3_model_get_func_decl.argtypes = [ContextObj, Model, ctypes.c_uint]
  _lib.Z3_model_eval.restype = ctypes.c_bool
  _lib.Z3_model_eval.argtypes = [ContextObj, Model, Ast, ctypes.c_bool, ctypes.POINTER(Ast)]
  _lib.Z3_model_get_num_sorts.restype = ctypes.c_uint
  _lib.Z3_model_get_num_sorts.argtypes = [ContextObj, Model]
  _lib.Z3_model_get_sort.restype = Sort
  _lib.Z3_model_get_sort.argtypes = [ContextObj, Model, ctypes.c_uint]
  _lib.Z3_model_get_sort_universe.restype = AstVectorObj
  _lib.Z3_model_get_sort_universe.argtypes = [ContextObj, Model, Sort]
  _lib.Z3_is_as_array.restype = ctypes.c_bool
  _lib.Z3_is_as_array.argtypes = [ContextObj, Ast]
  _lib.Z3_get_as_array_func_decl.restype = FuncDecl
  _lib.Z3_get_as_array_func_decl.argtypes = [ContextObj, Ast]
  _lib.Z3_func_interp_inc_ref.argtypes = [ContextObj, FuncInterpObj]
  _lib.Z3_func_interp_dec_ref.argtypes = [ContextObj, FuncInterpObj]
  _lib.Z3_func_interp_get_num_entries.restype = ctypes.c_uint
  _lib.Z3_func_interp_get_num_entries.argtypes = [ContextObj, FuncInterpObj]
  _lib.Z3_func_interp_get_entry.restype = FuncEntryObj
  _lib.Z3_func_interp_get_entry.argtypes = [ContextObj, FuncInterpObj, ctypes.c_uint]
  _lib.Z3_func_interp_get_else.restype = Ast
  _lib.Z3_func_interp_get_else.argtypes = [ContextObj, FuncInterpObj]
  _lib.Z3_func_interp_get_arity.restype = ctypes.c_uint
  _lib.Z3_func_interp_get_arity.argtypes = [ContextObj, FuncInterpObj]
  _lib.Z3_func_entry_inc_ref.argtypes = [ContextObj, FuncEntryObj]
  _lib.Z3_func_entry_dec_ref.argtypes = [ContextObj, FuncEntryObj]
  _lib.Z3_func_entry_get_value.restype = Ast
  _lib.Z3_func_entry_get_value.argtypes = [ContextObj, FuncEntryObj]
  _lib.Z3_func_entry_get_num_args.restype = ctypes.c_uint
  _lib.Z3_func_entry_get_num_args.argtypes = [ContextObj, FuncEntryObj]
  _lib.Z3_func_entry_get_arg.restype = Ast
  _lib.Z3_func_entry_get_arg.argtypes = [ContextObj, FuncEntryObj, ctypes.c_uint]
  _lib.Z3_get_model_num_constants.restype = ctypes.c_uint
  _lib.Z3_get_model_num_constants.argtypes = [ContextObj, Model]
  _lib.Z3_get_model_constant.restype = FuncDecl
  _lib.Z3_get_model_constant.argtypes = [ContextObj, Model, ctypes.c_uint]
  _lib.Z3_eval_func_decl.restype = ctypes.c_bool
  _lib.Z3_eval_func_decl.argtypes = [ContextObj, Model, FuncDecl, ctypes.POINTER(Ast)]
  _lib.Z3_is_array_value.restype = ctypes.c_bool
  _lib.Z3_is_array_value.argtypes = [ContextObj, Model, Ast, ctypes.POINTER(ctypes.c_uint)]
  _lib.Z3_get_array_value.argtypes = [ContextObj, Model, Ast, ctypes.c_uint, ctypes.POINTER(Ast), ctypes.POINTER(Ast), ctypes.POINTER(Ast)]
  _lib.Z3_get_model_num_funcs.restype = ctypes.c_uint
  _lib.Z3_get_model_num_funcs.argtypes = [ContextObj, Model]
  _lib.Z3_get_model_func_decl.restype = FuncDecl
  _lib.Z3_get_model_func_decl.argtypes = [ContextObj, Model, ctypes.c_uint]
  _lib.Z3_get_model_func_else.restype = Ast
  _lib.Z3_get_model_func_else.argtypes = [ContextObj, Model, ctypes.c_uint]
  _lib.Z3_get_model_func_num_entries.restype = ctypes.c_uint
  _lib.Z3_get_model_func_num_entries.argtypes = [ContextObj, Model, ctypes.c_uint]
  _lib.Z3_get_model_func_entry_num_args.restype = ctypes.c_uint
  _lib.Z3_get_model_func_entry_num_args.argtypes = [ContextObj, Model, ctypes.c_uint, ctypes.c_uint]
  _lib.Z3_get_model_func_entry_arg.restype = Ast
  _lib.Z3_get_model_func_entry_arg.argtypes = [ContextObj, Model, ctypes.c_uint, ctypes.c_uint, ctypes.c_uint]
  _lib.Z3_get_model_func_entry_value.restype = Ast
  _lib.Z3_get_model_func_entry_value.argtypes = [ContextObj, Model, ctypes.c_uint, ctypes.c_uint]
  _lib.Z3_eval.restype = ctypes.c_bool
  _lib.Z3_eval.argtypes = [ContextObj, Model, Ast, ctypes.POINTER(Ast)]
  _lib.Z3_eval_decl.restype = ctypes.c_bool
  _lib.Z3_eval_decl.argtypes = [ContextObj, Model, FuncDecl, ctypes.c_uint, ctypes.POINTER(Ast), ctypes.POINTER(Ast)]
  _lib.Z3_set_ast_print_mode.argtypes = [ContextObj, ctypes.c_uint]
  _lib.Z3_ast_to_string.restype = ctypes.c_char_p
  _lib.Z3_ast_to_string.argtypes = [ContextObj, Ast]
  _lib.Z3_pattern_to_string.restype = ctypes.c_char_p
  _lib.Z3_pattern_to_string.argtypes = [ContextObj, Pattern]
  _lib.Z3_sort_to_string.restype = ctypes.c_char_p
  _lib.Z3_sort_to_string.argtypes = [ContextObj, Sort]
  _lib.Z3_func_decl_to_string.restype = ctypes.c_char_p
  _lib.Z3_func_decl_to_string.argtypes = [ContextObj, FuncDecl]
  _lib.Z3_model_to_string.restype = ctypes.c_char_p
  _lib.Z3_model_to_string.argtypes = [ContextObj, Model]
  _lib.Z3_benchmark_to_smtlib_string.restype = ctypes.c_char_p
  _lib.Z3_benchmark_to_smtlib_string.argtypes = [ContextObj, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_uint, ctypes.POINTER(Ast), Ast]
  _lib.Z3_context_to_string.restype = ctypes.c_char_p
  _lib.Z3_context_to_string.argtypes = [ContextObj]
  _lib.Z3_statistics_to_string.restype = ctypes.c_char_p
  _lib.Z3_statistics_to_string.argtypes = [ContextObj]
  _lib.Z3_get_context_assignment.restype = Ast
  _lib.Z3_get_context_assignment.argtypes = [ContextObj]
  _lib.Z3_parse_smtlib_string.argtypes = [ContextObj, ctypes.c_char_p, ctypes.c_uint, ctypes.POINTER(Symbol), ctypes.POINTER(Sort), ctypes.c_uint, ctypes.POINTER(Symbol), ctypes.POINTER(FuncDecl)]
  _lib.Z3_parse_smtlib_file.argtypes = [ContextObj, ctypes.c_char_p, ctypes.c_uint, ctypes.POINTER(Symbol), ctypes.POINTER(Sort), ctypes.c_uint, ctypes.POINTER(Symbol), ctypes.POINTER(FuncDecl)]
  _lib.Z3_get_smtlib_num_formulas.restype = ctypes.c_uint
  _lib.Z3_get_smtlib_num_formulas.argtypes = [ContextObj]
  _lib.Z3_get_smtlib_formula.restype = Ast
  _lib.Z3_get_smtlib_formula.argtypes = [ContextObj, ctypes.c_uint]
  _lib.Z3_get_smtlib_num_assumptions.restype = ctypes.c_uint
  _lib.Z3_get_smtlib_num_assumptions.argtypes = [ContextObj]
  _lib.Z3_get_smtlib_assumption.restype = Ast
  _lib.Z3_get_smtlib_assumption.argtypes = [ContextObj, ctypes.c_uint]
  _lib.Z3_get_smtlib_num_decls.restype = ctypes.c_uint
  _lib.Z3_get_smtlib_num_decls.argtypes = [ContextObj]
  _lib.Z3_get_smtlib_decl.restype = FuncDecl
  _lib.Z3_get_smtlib_decl.argtypes = [ContextObj, ctypes.c_uint]
  _lib.Z3_get_smtlib_num_sorts.restype = ctypes.c_uint
  _lib.Z3_get_smtlib_num_sorts.argtypes = [ContextObj]
  _lib.Z3_get_smtlib_sort.restype = Sort
  _lib.Z3_get_smtlib_sort.argtypes = [ContextObj, ctypes.c_uint]
  _lib.Z3_get_smtlib_error.restype = ctypes.c_char_p
  _lib.Z3_get_smtlib_error.argtypes = [ContextObj]
  _lib.Z3_parse_z3_string.restype = Ast
  _lib.Z3_parse_z3_string.argtypes = [ContextObj, ctypes.c_char_p]
  _lib.Z3_parse_z3_file.restype = Ast
  _lib.Z3_parse_z3_file.argtypes = [ContextObj, ctypes.c_char_p]
  _lib.Z3_parse_smtlib2_string.restype = Ast
  _lib.Z3_parse_smtlib2_string.argtypes = [ContextObj, ctypes.c_char_p, ctypes.c_uint, ctypes.POINTER(Symbol), ctypes.POINTER(Sort), ctypes.c_uint, ctypes.POINTER(Symbol), ctypes.POINTER(FuncDecl)]
  _lib.Z3_parse_smtlib2_file.restype = Ast
  _lib.Z3_parse_smtlib2_file.argtypes = [ContextObj, ctypes.c_char_p, ctypes.c_uint, ctypes.POINTER(Symbol), ctypes.POINTER(Sort), ctypes.c_uint, ctypes.POINTER(Symbol), ctypes.POINTER(FuncDecl)]
  _lib.Z3_get_error_code.restype = ctypes.c_uint
  _lib.Z3_get_error_code.argtypes = [ContextObj]
  _lib.Z3_set_error.argtypes = [ContextObj, ctypes.c_uint]
  _lib.Z3_get_error_msg.restype = ctypes.c_char_p
  _lib.Z3_get_error_msg.argtypes = [ctypes.c_uint]
  _lib.Z3_get_version.argtypes = [ctypes.POINTER(ctypes.c_uint), ctypes.POINTER(ctypes.c_uint), ctypes.POINTER(ctypes.c_uint), ctypes.POINTER(ctypes.c_uint)]
  _lib.Z3_reset_memory.argtypes = []
  _lib.Z3_is_app.restype = ctypes.c_bool
  _lib.Z3_is_app.argtypes = [ContextObj, Ast]
  _lib.Z3_is_numeral_ast.restype = ctypes.c_bool
  _lib.Z3_is_numeral_ast.argtypes = [ContextObj, Ast]
  _lib.Z3_get_arity.restype = ctypes.c_uint
  _lib.Z3_get_arity.argtypes = [ContextObj, FuncDecl]
  _lib.Z3_mk_injective_function.restype = FuncDecl
  _lib.Z3_mk_injective_function.argtypes = [ContextObj, Symbol, ctypes.c_uint, ctypes.POINTER(Sort), Sort]
  _lib.Z3_mk_fixedpoint.restype = FixedpointObj
  _lib.Z3_mk_fixedpoint.argtypes = [ContextObj]
  _lib.Z3_fixedpoint_inc_ref.argtypes = [ContextObj, FixedpointObj]
  _lib.Z3_fixedpoint_dec_ref.argtypes = [ContextObj, FixedpointObj]
  _lib.Z3_fixedpoint_push.argtypes = [ContextObj, FixedpointObj]
  _lib.Z3_fixedpoint_pop.argtypes = [ContextObj, FixedpointObj]
  _lib.Z3_fixedpoint_register_relation.argtypes = [ContextObj, FixedpointObj, FuncDecl]
  _lib.Z3_fixedpoint_assert.argtypes = [ContextObj, FixedpointObj, Ast]
  _lib.Z3_fixedpoint_add_rule.argtypes = [ContextObj, FixedpointObj, Ast, Symbol]
  _lib.Z3_fixedpoint_add_fact.argtypes = [ContextObj, FixedpointObj, FuncDecl, ctypes.c_uint, ctypes.POINTER(ctypes.c_uint)]
  _lib.Z3_fixedpoint_query.restype = ctypes.c_int
  _lib.Z3_fixedpoint_query.argtypes = [ContextObj, FixedpointObj, Ast]
  _lib.Z3_fixedpoint_query_relations.restype = ctypes.c_int
  _lib.Z3_fixedpoint_query_relations.argtypes = [ContextObj, FixedpointObj, ctypes.c_uint, ctypes.POINTER(FuncDecl)]
  _lib.Z3_fixedpoint_get_answer.restype = Ast
  _lib.Z3_fixedpoint_get_answer.argtypes = [ContextObj, FixedpointObj]
  _lib.Z3_fixedpoint_update_rule.argtypes = [ContextObj, FixedpointObj, Ast, Symbol]
  _lib.Z3_fixedpoint_get_num_levels.restype = ctypes.c_uint
  _lib.Z3_fixedpoint_get_num_levels.argtypes = [ContextObj, FixedpointObj, FuncDecl]
  _lib.Z3_fixedpoint_get_cover_delta.restype = Ast
  _lib.Z3_fixedpoint_get_cover_delta.argtypes = [ContextObj, FixedpointObj, ctypes.c_int, FuncDecl]
  _lib.Z3_fixedpoint_add_cover.argtypes = [ContextObj, FixedpointObj, ctypes.c_int, FuncDecl, Ast]
  _lib.Z3_fixedpoint_get_statistics.restype = StatsObj
  _lib.Z3_fixedpoint_get_statistics.argtypes = [ContextObj, FixedpointObj]
  _lib.Z3_fixedpoint_get_help.restype = ctypes.c_char_p
  _lib.Z3_fixedpoint_get_help.argtypes = [ContextObj, FixedpointObj]
  _lib.Z3_fixedpoint_get_param_descrs.restype = ParamDescrs
  _lib.Z3_fixedpoint_get_param_descrs.argtypes = [ContextObj, FixedpointObj]
  _lib.Z3_fixedpoint_set_params.argtypes = [ContextObj, FixedpointObj, Params]
  _lib.Z3_fixedpoint_to_string.restype = ctypes.c_char_p
  _lib.Z3_fixedpoint_to_string.argtypes = [ContextObj, FixedpointObj, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_fixedpoint_get_reason_unknown.restype = ctypes.c_char_p
  _lib.Z3_fixedpoint_get_reason_unknown.argtypes = [ContextObj, FixedpointObj]
  _lib.Z3_fixedpoint_set_predicate_representation.argtypes = [ContextObj, FixedpointObj, FuncDecl, ctypes.c_uint, ctypes.POINTER(Symbol)]
  _lib.Z3_fixedpoint_simplify_rules.restype = AstVectorObj
  _lib.Z3_fixedpoint_simplify_rules.argtypes = [ContextObj, FixedpointObj, ctypes.c_uint, ctypes.POINTER(Ast), ctypes.c_uint, ctypes.POINTER(FuncDecl)]
  _lib.Z3_mk_params.restype = Params
  _lib.Z3_mk_params.argtypes = [ContextObj]
  _lib.Z3_params_inc_ref.argtypes = [ContextObj, Params]
  _lib.Z3_params_dec_ref.argtypes = [ContextObj, Params]
  _lib.Z3_params_set_bool.argtypes = [ContextObj, Params, Symbol, ctypes.c_bool]
  _lib.Z3_params_set_uint.argtypes = [ContextObj, Params, Symbol, ctypes.c_uint]
  _lib.Z3_params_set_double.argtypes = [ContextObj, Params, Symbol, ctypes.c_double]
  _lib.Z3_params_set_symbol.argtypes = [ContextObj, Params, Symbol, Symbol]
  _lib.Z3_params_to_string.restype = ctypes.c_char_p
  _lib.Z3_params_to_string.argtypes = [ContextObj, Params]
  _lib.Z3_params_validate.argtypes = [ContextObj, Params, ParamDescrs]
  _lib.Z3_param_descrs_inc_ref.argtypes = [ContextObj, ParamDescrs]
  _lib.Z3_param_descrs_dec_ref.argtypes = [ContextObj, ParamDescrs]
  _lib.Z3_param_descrs_get_kind.restype = ctypes.c_uint
  _lib.Z3_param_descrs_get_kind.argtypes = [ContextObj, ParamDescrs, Symbol]
  _lib.Z3_param_descrs_size.restype = ctypes.c_uint
  _lib.Z3_param_descrs_size.argtypes = [ContextObj, ParamDescrs]
  _lib.Z3_param_descrs_get_name.restype = Symbol
  _lib.Z3_param_descrs_get_name.argtypes = [ContextObj, ParamDescrs, ctypes.c_uint]
  _lib.Z3_interrupt.argtypes = [ContextObj]
  _lib.Z3_get_error_msg_ex.restype = ctypes.c_char_p
  _lib.Z3_get_error_msg_ex.argtypes = [ContextObj, ctypes.c_uint]
  _lib.Z3_translate.restype = Ast
  _lib.Z3_translate.argtypes = [ContextObj, Ast, ContextObj]
  _lib.Z3_mk_goal.restype = GoalObj
  _lib.Z3_mk_goal.argtypes = [ContextObj, ctypes.c_bool, ctypes.c_bool, ctypes.c_bool]
  _lib.Z3_goal_inc_ref.argtypes = [ContextObj, GoalObj]
  _lib.Z3_goal_dec_ref.argtypes = [ContextObj, GoalObj]
  _lib.Z3_goal_precision.restype = ctypes.c_uint
  _lib.Z3_goal_precision.argtypes = [ContextObj, GoalObj]
  _lib.Z3_goal_assert.argtypes = [ContextObj, GoalObj, Ast]
  _lib.Z3_goal_inconsistent.restype = ctypes.c_bool
  _lib.Z3_goal_inconsistent.argtypes = [ContextObj, GoalObj]
  _lib.Z3_goal_depth.restype = ctypes.c_uint
  _lib.Z3_goal_depth.argtypes = [ContextObj, GoalObj]
  _lib.Z3_goal_reset.argtypes = [ContextObj, GoalObj]
  _lib.Z3_goal_size.restype = ctypes.c_uint
  _lib.Z3_goal_size.argtypes = [ContextObj, GoalObj]
  _lib.Z3_goal_formula.restype = Ast
  _lib.Z3_goal_formula.argtypes = [ContextObj, GoalObj, ctypes.c_uint]
  _lib.Z3_goal_num_exprs.restype = ctypes.c_uint
  _lib.Z3_goal_num_exprs.argtypes = [ContextObj, GoalObj]
  _lib.Z3_goal_is_decided_sat.restype = ctypes.c_bool
  _lib.Z3_goal_is_decided_sat.argtypes = [ContextObj, GoalObj]
  _lib.Z3_goal_is_decided_unsat.restype = ctypes.c_bool
  _lib.Z3_goal_is_decided_unsat.argtypes = [ContextObj, GoalObj]
  _lib.Z3_goal_translate.restype = GoalObj
  _lib.Z3_goal_translate.argtypes = [ContextObj, GoalObj, ContextObj]
  _lib.Z3_goal_to_string.restype = ctypes.c_char_p
  _lib.Z3_goal_to_string.argtypes = [ContextObj, GoalObj]
  _lib.Z3_mk_tactic.restype = TacticObj
  _lib.Z3_mk_tactic.argtypes = [ContextObj, ctypes.c_char_p]
  _lib.Z3_mk_probe.restype = ProbeObj
  _lib.Z3_mk_probe.argtypes = [ContextObj, ctypes.c_char_p]
  _lib.Z3_tactic_inc_ref.argtypes = [ContextObj, TacticObj]
  _lib.Z3_tactic_dec_ref.argtypes = [ContextObj, TacticObj]
  _lib.Z3_probe_inc_ref.argtypes = [ContextObj, ProbeObj]
  _lib.Z3_probe_dec_ref.argtypes = [ContextObj, ProbeObj]
  _lib.Z3_tactic_and_then.restype = TacticObj
  _lib.Z3_tactic_and_then.argtypes = [ContextObj, TacticObj, TacticObj]
  _lib.Z3_tactic_or_else.restype = TacticObj
  _lib.Z3_tactic_or_else.argtypes = [ContextObj, TacticObj, TacticObj]
  _lib.Z3_tactic_par_or.restype = TacticObj
  _lib.Z3_tactic_par_or.argtypes = [ContextObj, ctypes.c_uint, ctypes.POINTER(TacticObj)]
  _lib.Z3_tactic_par_and_then.restype = TacticObj
  _lib.Z3_tactic_par_and_then.argtypes = [ContextObj, TacticObj, TacticObj]
  _lib.Z3_tactic_try_for.restype = TacticObj
  _lib.Z3_tactic_try_for.argtypes = [ContextObj, TacticObj, ctypes.c_uint]
  _lib.Z3_tactic_when.restype = TacticObj
  _lib.Z3_tactic_when.argtypes = [ContextObj, ProbeObj, TacticObj]
  _lib.Z3_tactic_cond.restype = TacticObj
  _lib.Z3_tactic_cond.argtypes = [ContextObj, ProbeObj, TacticObj, TacticObj]
  _lib.Z3_tactic_repeat.restype = TacticObj
  _lib.Z3_tactic_repeat.argtypes = [ContextObj, TacticObj, ctypes.c_uint]
  _lib.Z3_tactic_skip.restype = TacticObj
  _lib.Z3_tactic_skip.argtypes = [ContextObj]
  _lib.Z3_tactic_fail.restype = TacticObj
  _lib.Z3_tactic_fail.argtypes = [ContextObj]
  _lib.Z3_tactic_fail_if.restype = TacticObj
  _lib.Z3_tactic_fail_if.argtypes = [ContextObj, ProbeObj]
  _lib.Z3_tactic_fail_if_not_decided.restype = TacticObj
  _lib.Z3_tactic_fail_if_not_decided.argtypes = [ContextObj]
  _lib.Z3_tactic_using_params.restype = TacticObj
  _lib.Z3_tactic_using_params.argtypes = [ContextObj, TacticObj, Params]
  _lib.Z3_probe_const.restype = ProbeObj
  _lib.Z3_probe_const.argtypes = [ContextObj, ctypes.c_double]
  _lib.Z3_probe_lt.restype = ProbeObj
  _lib.Z3_probe_lt.argtypes = [ContextObj, ProbeObj, ProbeObj]
  _lib.Z3_probe_le.restype = ProbeObj
  _lib.Z3_probe_le.argtypes = [ContextObj, ProbeObj, ProbeObj]
  _lib.Z3_probe_gt.restype = ProbeObj
  _lib.Z3_probe_gt.argtypes = [ContextObj, ProbeObj, ProbeObj]
  _lib.Z3_probe_ge.restype = ProbeObj
  _lib.Z3_probe_ge.argtypes = [ContextObj, ProbeObj, ProbeObj]
  _lib.Z3_probe_eq.restype = ProbeObj
  _lib.Z3_probe_eq.argtypes = [ContextObj, ProbeObj, ProbeObj]
  _lib.Z3_probe_and.restype = ProbeObj
  _lib.Z3_probe_and.argtypes = [ContextObj, ProbeObj, ProbeObj]
  _lib.Z3_probe_or.restype = ProbeObj
  _lib.Z3_probe_or.argtypes = [ContextObj, ProbeObj, ProbeObj]
  _lib.Z3_probe_not.restype = ProbeObj
  _lib.Z3_probe_not.argtypes = [ContextObj, ProbeObj]
  _lib.Z3_get_num_tactics.restype = ctypes.c_uint
  _lib.Z3_get_num_tactics.argtypes = [ContextObj]
  _lib.Z3_get_tactic_name.restype = ctypes.c_char_p
  _lib.Z3_get_tactic_name.argtypes = [ContextObj, ctypes.c_uint]
  _lib.Z3_get_num_probes.restype = ctypes.c_uint
  _lib.Z3_get_num_probes.argtypes = [ContextObj]
  _lib.Z3_get_probe_name.restype = ctypes.c_char_p
  _lib.Z3_get_probe_name.argtypes = [ContextObj, ctypes.c_uint]
  _lib.Z3_tactic_get_help.restype = ctypes.c_char_p
  _lib.Z3_tactic_get_help.argtypes = [ContextObj, TacticObj]
  _lib.Z3_tactic_get_param_descrs.restype = ParamDescrs
  _lib.Z3_tactic_get_param_descrs.argtypes = [ContextObj, TacticObj]
  _lib.Z3_tactic_get_descr.restype = ctypes.c_char_p
  _lib.Z3_tactic_get_descr.argtypes = [ContextObj, ctypes.c_char_p]
  _lib.Z3_probe_get_descr.restype = ctypes.c_char_p
  _lib.Z3_probe_get_descr.argtypes = [ContextObj, ctypes.c_char_p]
  _lib.Z3_probe_apply.restype = ctypes.c_double
  _lib.Z3_probe_apply.argtypes = [ContextObj, ProbeObj, GoalObj]
  _lib.Z3_tactic_apply.restype = ApplyResultObj
  _lib.Z3_tactic_apply.argtypes = [ContextObj, TacticObj, GoalObj]
  _lib.Z3_tactic_apply_ex.restype = ApplyResultObj
  _lib.Z3_tactic_apply_ex.argtypes = [ContextObj, TacticObj, GoalObj, Params]
  _lib.Z3_apply_result_inc_ref.argtypes = [ContextObj, ApplyResultObj]
  _lib.Z3_apply_result_dec_ref.argtypes = [ContextObj, ApplyResultObj]
  _lib.Z3_apply_result_to_string.restype = ctypes.c_char_p
  _lib.Z3_apply_result_to_string.argtypes = [ContextObj, ApplyResultObj]
  _lib.Z3_apply_result_get_num_subgoals.restype = ctypes.c_uint
  _lib.Z3_apply_result_get_num_subgoals.argtypes = [ContextObj, ApplyResultObj]
  _lib.Z3_apply_result_get_subgoal.restype = GoalObj
  _lib.Z3_apply_result_get_subgoal.argtypes = [ContextObj, ApplyResultObj, ctypes.c_uint]
  _lib.Z3_apply_result_convert_model.restype = Model
  _lib.Z3_apply_result_convert_model.argtypes = [ContextObj, ApplyResultObj, ctypes.c_uint, Model]
  _lib.Z3_mk_solver.restype = SolverObj
  _lib.Z3_mk_solver.argtypes = [ContextObj]
  _lib.Z3_mk_simple_solver.restype = SolverObj
  _lib.Z3_mk_simple_solver.argtypes = [ContextObj]
  _lib.Z3_mk_solver_for_logic.restype = SolverObj
  _lib.Z3_mk_solver_for_logic.argtypes = [ContextObj, Symbol]
  _lib.Z3_mk_solver_from_tactic.restype = SolverObj
  _lib.Z3_mk_solver_from_tactic.argtypes = [ContextObj, TacticObj]
  _lib.Z3_solver_get_help.restype = ctypes.c_char_p
  _lib.Z3_solver_get_help.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_get_param_descrs.restype = ParamDescrs
  _lib.Z3_solver_get_param_descrs.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_set_params.argtypes = [ContextObj, SolverObj, Params]
  _lib.Z3_solver_inc_ref.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_dec_ref.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_push.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_pop.argtypes = [ContextObj, SolverObj, ctypes.c_uint]
  _lib.Z3_solver_reset.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_get_num_scopes.restype = ctypes.c_uint
  _lib.Z3_solver_get_num_scopes.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_assert.argtypes = [ContextObj, SolverObj, Ast]
  _lib.Z3_solver_get_assertions.restype = AstVectorObj
  _lib.Z3_solver_get_assertions.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_check.restype = ctypes.c_int
  _lib.Z3_solver_check.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_check_assumptions.restype = ctypes.c_int
  _lib.Z3_solver_check_assumptions.argtypes = [ContextObj, SolverObj, ctypes.c_uint, ctypes.POINTER(Ast)]
  _lib.Z3_solver_get_model.restype = Model
  _lib.Z3_solver_get_model.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_get_proof.restype = Ast
  _lib.Z3_solver_get_proof.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_get_unsat_core.restype = AstVectorObj
  _lib.Z3_solver_get_unsat_core.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_get_reason_unknown.restype = ctypes.c_char_p
  _lib.Z3_solver_get_reason_unknown.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_get_statistics.restype = StatsObj
  _lib.Z3_solver_get_statistics.argtypes = [ContextObj, SolverObj]
  _lib.Z3_solver_to_string.restype = ctypes.c_char_p
  _lib.Z3_solver_to_string.argtypes = [ContextObj, SolverObj]
  _lib.Z3_stats_to_string.restype = ctypes.c_char_p
  _lib.Z3_stats_to_string.argtypes = [ContextObj, StatsObj]
  _lib.Z3_stats_inc_ref.argtypes = [ContextObj, StatsObj]
  _lib.Z3_stats_dec_ref.argtypes = [ContextObj, StatsObj]
  _lib.Z3_stats_size.restype = ctypes.c_uint
  _lib.Z3_stats_size.argtypes = [ContextObj, StatsObj]
  _lib.Z3_stats_get_key.restype = ctypes.c_char_p
  _lib.Z3_stats_get_key.argtypes = [ContextObj, StatsObj, ctypes.c_uint]
  _lib.Z3_stats_is_uint.restype = ctypes.c_bool
  _lib.Z3_stats_is_uint.argtypes = [ContextObj, StatsObj, ctypes.c_uint]
  _lib.Z3_stats_is_double.restype = ctypes.c_bool
  _lib.Z3_stats_is_double.argtypes = [ContextObj, StatsObj, ctypes.c_uint]
  _lib.Z3_stats_get_uint_value.restype = ctypes.c_uint
  _lib.Z3_stats_get_uint_value.argtypes = [ContextObj, StatsObj, ctypes.c_uint]
  _lib.Z3_stats_get_double_value.restype = ctypes.c_double
  _lib.Z3_stats_get_double_value.argtypes = [ContextObj, StatsObj, ctypes.c_uint]
  _lib.Z3_mk_ast_vector.restype = AstVectorObj
  _lib.Z3_mk_ast_vector.argtypes = [ContextObj]
  _lib.Z3_ast_vector_inc_ref.argtypes = [ContextObj, AstVectorObj]
  _lib.Z3_ast_vector_dec_ref.argtypes = [ContextObj, AstVectorObj]
  _lib.Z3_ast_vector_size.restype = ctypes.c_uint
  _lib.Z3_ast_vector_size.argtypes = [ContextObj, AstVectorObj]
  _lib.Z3_ast_vector_get.restype = Ast
  _lib.Z3_ast_vector_get.argtypes = [ContextObj, AstVectorObj, ctypes.c_uint]
  _lib.Z3_ast_vector_set.argtypes = [ContextObj, AstVectorObj, ctypes.c_uint, Ast]
  _lib.Z3_ast_vector_resize.argtypes = [ContextObj, AstVectorObj, ctypes.c_uint]
  _lib.Z3_ast_vector_push.argtypes = [ContextObj, AstVectorObj, Ast]
  _lib.Z3_ast_vector_translate.restype = AstVectorObj
  _lib.Z3_ast_vector_translate.argtypes = [ContextObj, AstVectorObj, ContextObj]
  _lib.Z3_ast_vector_to_string.restype = ctypes.c_char_p
  _lib.Z3_ast_vector_to_string.argtypes = [ContextObj, AstVectorObj]
  _lib.Z3_mk_ast_map.restype = AstMapObj
  _lib.Z3_mk_ast_map.argtypes = [ContextObj]
  _lib.Z3_ast_map_inc_ref.argtypes = [ContextObj, AstMapObj]
  _lib.Z3_ast_map_dec_ref.argtypes = [ContextObj, AstMapObj]
  _lib.Z3_ast_map_contains.restype = ctypes.c_bool
  _lib.Z3_ast_map_contains.argtypes = [ContextObj, AstMapObj, Ast]
  _lib.Z3_ast_map_find.restype = Ast
  _lib.Z3_ast_map_find.argtypes = [ContextObj, AstMapObj, Ast]
  _lib.Z3_ast_map_insert.argtypes = [ContextObj, AstMapObj, Ast, Ast]
  _lib.Z3_ast_map_erase.argtypes = [ContextObj, AstMapObj, Ast]
  _lib.Z3_ast_map_size.restype = ctypes.c_uint
  _lib.Z3_ast_map_size.argtypes = [ContextObj, AstMapObj]
  _lib.Z3_ast_map_reset.argtypes = [ContextObj, AstMapObj]
  _lib.Z3_ast_map_keys.restype = AstVectorObj
  _lib.Z3_ast_map_keys.argtypes = [ContextObj, AstMapObj]
  _lib.Z3_ast_map_to_string.restype = ctypes.c_char_p
  _lib.Z3_ast_map_to_string.argtypes = [ContextObj, AstMapObj]
  _lib.Z3_open_log.restype = ctypes.c_int
  _lib.Z3_open_log.argtypes = [ctypes.c_char_p]
  _lib.Z3_append_log.argtypes = [ctypes.c_char_p]
  _lib.Z3_close_log.argtypes = []

def Z3_mk_config():
  r = lib().Z3_mk_config()
  return r

def Z3_del_config(a0):
  lib().Z3_del_config(a0)

def Z3_set_param_value(a0, a1, a2):
  lib().Z3_set_param_value(a0, a1, a2)

def Z3_mk_context(a0):
  r = lib().Z3_mk_context(a0)
  return r

def Z3_mk_context_rc(a0):
  r = lib().Z3_mk_context_rc(a0)
  return r

def Z3_set_logic(a0, a1):
  lib().Z3_set_logic(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_del_context(a0):
  lib().Z3_del_context(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_inc_ref(a0, a1):
  lib().Z3_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_dec_ref(a0, a1):
  lib().Z3_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_toggle_warning_messages(a0):
  lib().Z3_toggle_warning_messages(a0)

def Z3_update_param_value(a0, a1, a2):
  lib().Z3_update_param_value(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_get_param_value(a0, a1, a2):
  r = lib().Z3_get_param_value(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_int_symbol(a0, a1):
  r = lib().Z3_mk_int_symbol(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_string_symbol(a0, a1):
  r = lib().Z3_mk_string_symbol(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_is_eq_sort(a0, a1, a2):
  r = lib().Z3_is_eq_sort(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_uninterpreted_sort(a0, a1):
  r = lib().Z3_mk_uninterpreted_sort(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bool_sort(a0):
  r = lib().Z3_mk_bool_sort(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_int_sort(a0):
  r = lib().Z3_mk_int_sort(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_real_sort(a0):
  r = lib().Z3_mk_real_sort(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bv_sort(a0, a1):
  r = lib().Z3_mk_bv_sort(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_array_sort(a0, a1, a2):
  r = lib().Z3_mk_array_sort(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_tuple_sort(a0, a1, a2, a3, a4, a5, a6):
  r = lib().Z3_mk_tuple_sort(a0, a1, a2, a3, a4, a5, a6)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_enumeration_sort(a0, a1, a2, a3, a4, a5):
  r = lib().Z3_mk_enumeration_sort(a0, a1, a2, a3, a4, a5)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_list_sort(a0, a1, a2, a3, a4, a5, a6, a7, a8):
  r = lib().Z3_mk_list_sort(a0, a1, a2, a3, a4, a5, a6, a7, a8)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_constructor(a0, a1, a2, a3, a4, a5, a6):
  r = lib().Z3_mk_constructor(a0, a1, a2, a3, a4, a5, a6)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_query_constructor(a0, a1, a2, a3, a4, a5):
  lib().Z3_query_constructor(a0, a1, a2, a3, a4, a5)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_del_constructor(a0, a1):
  lib().Z3_del_constructor(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_mk_datatype(a0, a1, a2, a3):
  r = lib().Z3_mk_datatype(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_constructor_list(a0, a1, a2):
  r = lib().Z3_mk_constructor_list(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_del_constructor_list(a0, a1):
  lib().Z3_del_constructor_list(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_mk_datatypes(a0, a1, a2, a3, a4):
  lib().Z3_mk_datatypes(a0, a1, a2, a3, a4)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_is_eq_ast(a0, a1, a2):
  r = lib().Z3_is_eq_ast(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_is_eq_func_decl(a0, a1, a2):
  r = lib().Z3_is_eq_func_decl(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_func_decl(a0, a1, a2, a3, a4):
  r = lib().Z3_mk_func_decl(a0, a1, a2, a3, a4)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_app(a0, a1, a2, a3):
  r = lib().Z3_mk_app(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_const(a0, a1, a2):
  r = lib().Z3_mk_const(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_label(a0, a1, a2, a3):
  r = lib().Z3_mk_label(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_fresh_func_decl(a0, a1, a2, a3, a4):
  r = lib().Z3_mk_fresh_func_decl(a0, a1, a2, a3, a4)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_fresh_const(a0, a1, a2):
  r = lib().Z3_mk_fresh_const(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_true(a0):
  r = lib().Z3_mk_true(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_false(a0):
  r = lib().Z3_mk_false(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_eq(a0, a1, a2):
  r = lib().Z3_mk_eq(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_distinct(a0, a1, a2):
  r = lib().Z3_mk_distinct(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_not(a0, a1):
  r = lib().Z3_mk_not(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_ite(a0, a1, a2, a3):
  r = lib().Z3_mk_ite(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_iff(a0, a1, a2):
  r = lib().Z3_mk_iff(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_implies(a0, a1, a2):
  r = lib().Z3_mk_implies(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_xor(a0, a1, a2):
  r = lib().Z3_mk_xor(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_and(a0, a1, a2):
  r = lib().Z3_mk_and(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_or(a0, a1, a2):
  r = lib().Z3_mk_or(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_add(a0, a1, a2):
  r = lib().Z3_mk_add(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_mul(a0, a1, a2):
  r = lib().Z3_mk_mul(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_sub(a0, a1, a2):
  r = lib().Z3_mk_sub(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_unary_minus(a0, a1):
  r = lib().Z3_mk_unary_minus(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_div(a0, a1, a2):
  r = lib().Z3_mk_div(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_mod(a0, a1, a2):
  r = lib().Z3_mk_mod(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_rem(a0, a1, a2):
  r = lib().Z3_mk_rem(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_power(a0, a1, a2):
  r = lib().Z3_mk_power(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_is_algebraic_number(a0, a1):
  r = lib().Z3_is_algebraic_number(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_algebraic_number_lower(a0, a1, a2):
  r = lib().Z3_get_algebraic_number_lower(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_algebraic_number_upper(a0, a1, a2):
  r = lib().Z3_get_algebraic_number_upper(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_lt(a0, a1, a2):
  r = lib().Z3_mk_lt(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_le(a0, a1, a2):
  r = lib().Z3_mk_le(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_gt(a0, a1, a2):
  r = lib().Z3_mk_gt(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_ge(a0, a1, a2):
  r = lib().Z3_mk_ge(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_int2real(a0, a1):
  r = lib().Z3_mk_int2real(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_real2int(a0, a1):
  r = lib().Z3_mk_real2int(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_is_int(a0, a1):
  r = lib().Z3_mk_is_int(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvnot(a0, a1):
  r = lib().Z3_mk_bvnot(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvredand(a0, a1):
  r = lib().Z3_mk_bvredand(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvredor(a0, a1):
  r = lib().Z3_mk_bvredor(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvand(a0, a1, a2):
  r = lib().Z3_mk_bvand(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvor(a0, a1, a2):
  r = lib().Z3_mk_bvor(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvxor(a0, a1, a2):
  r = lib().Z3_mk_bvxor(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvnand(a0, a1, a2):
  r = lib().Z3_mk_bvnand(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvnor(a0, a1, a2):
  r = lib().Z3_mk_bvnor(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvxnor(a0, a1, a2):
  r = lib().Z3_mk_bvxnor(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvneg(a0, a1):
  r = lib().Z3_mk_bvneg(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvadd(a0, a1, a2):
  r = lib().Z3_mk_bvadd(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvsub(a0, a1, a2):
  r = lib().Z3_mk_bvsub(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvmul(a0, a1, a2):
  r = lib().Z3_mk_bvmul(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvudiv(a0, a1, a2):
  r = lib().Z3_mk_bvudiv(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvsdiv(a0, a1, a2):
  r = lib().Z3_mk_bvsdiv(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvurem(a0, a1, a2):
  r = lib().Z3_mk_bvurem(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvsrem(a0, a1, a2):
  r = lib().Z3_mk_bvsrem(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvsmod(a0, a1, a2):
  r = lib().Z3_mk_bvsmod(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvult(a0, a1, a2):
  r = lib().Z3_mk_bvult(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvslt(a0, a1, a2):
  r = lib().Z3_mk_bvslt(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvule(a0, a1, a2):
  r = lib().Z3_mk_bvule(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvsle(a0, a1, a2):
  r = lib().Z3_mk_bvsle(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvuge(a0, a1, a2):
  r = lib().Z3_mk_bvuge(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvsge(a0, a1, a2):
  r = lib().Z3_mk_bvsge(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvugt(a0, a1, a2):
  r = lib().Z3_mk_bvugt(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvsgt(a0, a1, a2):
  r = lib().Z3_mk_bvsgt(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_concat(a0, a1, a2):
  r = lib().Z3_mk_concat(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_extract(a0, a1, a2, a3):
  r = lib().Z3_mk_extract(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_sign_ext(a0, a1, a2):
  r = lib().Z3_mk_sign_ext(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_zero_ext(a0, a1, a2):
  r = lib().Z3_mk_zero_ext(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_repeat(a0, a1, a2):
  r = lib().Z3_mk_repeat(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvshl(a0, a1, a2):
  r = lib().Z3_mk_bvshl(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvlshr(a0, a1, a2):
  r = lib().Z3_mk_bvlshr(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvashr(a0, a1, a2):
  r = lib().Z3_mk_bvashr(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_rotate_left(a0, a1, a2):
  r = lib().Z3_mk_rotate_left(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_rotate_right(a0, a1, a2):
  r = lib().Z3_mk_rotate_right(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_ext_rotate_left(a0, a1, a2):
  r = lib().Z3_mk_ext_rotate_left(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_ext_rotate_right(a0, a1, a2):
  r = lib().Z3_mk_ext_rotate_right(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_int2bv(a0, a1, a2):
  r = lib().Z3_mk_int2bv(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bv2int(a0, a1, a2):
  r = lib().Z3_mk_bv2int(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvadd_no_overflow(a0, a1, a2, a3):
  r = lib().Z3_mk_bvadd_no_overflow(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvadd_no_underflow(a0, a1, a2):
  r = lib().Z3_mk_bvadd_no_underflow(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvsub_no_overflow(a0, a1, a2):
  r = lib().Z3_mk_bvsub_no_overflow(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvsub_no_underflow(a0, a1, a2, a3):
  r = lib().Z3_mk_bvsub_no_underflow(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvsdiv_no_overflow(a0, a1, a2):
  r = lib().Z3_mk_bvsdiv_no_overflow(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvneg_no_overflow(a0, a1):
  r = lib().Z3_mk_bvneg_no_overflow(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvmul_no_overflow(a0, a1, a2, a3):
  r = lib().Z3_mk_bvmul_no_overflow(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bvmul_no_underflow(a0, a1, a2):
  r = lib().Z3_mk_bvmul_no_underflow(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_select(a0, a1, a2):
  r = lib().Z3_mk_select(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_store(a0, a1, a2, a3):
  r = lib().Z3_mk_store(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_const_array(a0, a1, a2):
  r = lib().Z3_mk_const_array(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_map(a0, a1, a2, a3):
  r = lib().Z3_mk_map(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_array_default(a0, a1):
  r = lib().Z3_mk_array_default(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_set_sort(a0, a1):
  r = lib().Z3_mk_set_sort(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_empty_set(a0, a1):
  r = lib().Z3_mk_empty_set(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_full_set(a0, a1):
  r = lib().Z3_mk_full_set(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_set_add(a0, a1, a2):
  r = lib().Z3_mk_set_add(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_set_del(a0, a1, a2):
  r = lib().Z3_mk_set_del(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_set_union(a0, a1, a2):
  r = lib().Z3_mk_set_union(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_set_intersect(a0, a1, a2):
  r = lib().Z3_mk_set_intersect(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_set_difference(a0, a1, a2):
  r = lib().Z3_mk_set_difference(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_set_complement(a0, a1):
  r = lib().Z3_mk_set_complement(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_set_member(a0, a1, a2):
  r = lib().Z3_mk_set_member(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_set_subset(a0, a1, a2):
  r = lib().Z3_mk_set_subset(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_numeral(a0, a1, a2):
  r = lib().Z3_mk_numeral(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_real(a0, a1, a2):
  r = lib().Z3_mk_real(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_int(a0, a1, a2):
  r = lib().Z3_mk_int(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_unsigned_int(a0, a1, a2):
  r = lib().Z3_mk_unsigned_int(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_int64(a0, a1, a2):
  r = lib().Z3_mk_int64(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_unsigned_int64(a0, a1, a2):
  r = lib().Z3_mk_unsigned_int64(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_pattern(a0, a1, a2):
  r = lib().Z3_mk_pattern(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_bound(a0, a1, a2):
  r = lib().Z3_mk_bound(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_forall(a0, a1, a2, a3, a4, a5, a6, a7):
  r = lib().Z3_mk_forall(a0, a1, a2, a3, a4, a5, a6, a7)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_exists(a0, a1, a2, a3, a4, a5, a6, a7):
  r = lib().Z3_mk_exists(a0, a1, a2, a3, a4, a5, a6, a7)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_quantifier(a0, a1, a2, a3, a4, a5, a6, a7, a8):
  r = lib().Z3_mk_quantifier(a0, a1, a2, a3, a4, a5, a6, a7, a8)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_quantifier_ex(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12):
  r = lib().Z3_mk_quantifier_ex(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_forall_const(a0, a1, a2, a3, a4, a5, a6):
  r = lib().Z3_mk_forall_const(a0, a1, a2, a3, a4, a5, a6)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_exists_const(a0, a1, a2, a3, a4, a5, a6):
  r = lib().Z3_mk_exists_const(a0, a1, a2, a3, a4, a5, a6)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_quantifier_const(a0, a1, a2, a3, a4, a5, a6, a7):
  r = lib().Z3_mk_quantifier_const(a0, a1, a2, a3, a4, a5, a6, a7)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_quantifier_const_ex(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11):
  r = lib().Z3_mk_quantifier_const_ex(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_ast_id(a0, a1):
  r = lib().Z3_get_ast_id(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_func_decl_id(a0, a1):
  r = lib().Z3_get_func_decl_id(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_sort_id(a0, a1):
  r = lib().Z3_get_sort_id(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_is_well_sorted(a0, a1):
  r = lib().Z3_is_well_sorted(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_symbol_kind(a0, a1):
  r = lib().Z3_get_symbol_kind(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_symbol_int(a0, a1):
  r = lib().Z3_get_symbol_int(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_symbol_string(a0, a1):
  r = lib().Z3_get_symbol_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_ast_kind(a0, a1):
  r = lib().Z3_get_ast_kind(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_ast_hash(a0, a1):
  r = lib().Z3_get_ast_hash(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_numeral_string(a0, a1):
  r = lib().Z3_get_numeral_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_numeral_decimal_string(a0, a1, a2):
  r = lib().Z3_get_numeral_decimal_string(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_numerator(a0, a1):
  r = lib().Z3_get_numerator(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_denominator(a0, a1):
  r = lib().Z3_get_denominator(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_numeral_small(a0, a1, a2, a3):
  r = lib().Z3_get_numeral_small(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_numeral_int(a0, a1, a2):
  r = lib().Z3_get_numeral_int(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_numeral_uint(a0, a1, a2):
  r = lib().Z3_get_numeral_uint(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_numeral_uint64(a0, a1, a2):
  r = lib().Z3_get_numeral_uint64(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_numeral_int64(a0, a1, a2):
  r = lib().Z3_get_numeral_int64(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_numeral_rational_int64(a0, a1, a2, a3):
  r = lib().Z3_get_numeral_rational_int64(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_bool_value(a0, a1):
  r = lib().Z3_get_bool_value(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_app_decl(a0, a1):
  r = lib().Z3_get_app_decl(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_app_num_args(a0, a1):
  r = lib().Z3_get_app_num_args(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_app_arg(a0, a1, a2):
  r = lib().Z3_get_app_arg(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_index_value(a0, a1):
  r = lib().Z3_get_index_value(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_is_quantifier_forall(a0, a1):
  r = lib().Z3_is_quantifier_forall(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_quantifier_weight(a0, a1):
  r = lib().Z3_get_quantifier_weight(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_quantifier_num_patterns(a0, a1):
  r = lib().Z3_get_quantifier_num_patterns(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_quantifier_pattern_ast(a0, a1, a2):
  r = lib().Z3_get_quantifier_pattern_ast(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_quantifier_num_no_patterns(a0, a1):
  r = lib().Z3_get_quantifier_num_no_patterns(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_quantifier_no_pattern_ast(a0, a1, a2):
  r = lib().Z3_get_quantifier_no_pattern_ast(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_quantifier_bound_name(a0, a1, a2):
  r = lib().Z3_get_quantifier_bound_name(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_quantifier_bound_sort(a0, a1, a2):
  r = lib().Z3_get_quantifier_bound_sort(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_quantifier_body(a0, a1):
  r = lib().Z3_get_quantifier_body(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_quantifier_num_bound(a0, a1):
  r = lib().Z3_get_quantifier_num_bound(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_decl_name(a0, a1):
  r = lib().Z3_get_decl_name(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_decl_num_parameters(a0, a1):
  r = lib().Z3_get_decl_num_parameters(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_decl_parameter_kind(a0, a1, a2):
  r = lib().Z3_get_decl_parameter_kind(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_decl_int_parameter(a0, a1, a2):
  r = lib().Z3_get_decl_int_parameter(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_decl_double_parameter(a0, a1, a2):
  r = lib().Z3_get_decl_double_parameter(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_decl_symbol_parameter(a0, a1, a2):
  r = lib().Z3_get_decl_symbol_parameter(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_decl_sort_parameter(a0, a1, a2):
  r = lib().Z3_get_decl_sort_parameter(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_decl_ast_parameter(a0, a1, a2):
  r = lib().Z3_get_decl_ast_parameter(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_decl_func_decl_parameter(a0, a1, a2):
  r = lib().Z3_get_decl_func_decl_parameter(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_decl_rational_parameter(a0, a1, a2):
  r = lib().Z3_get_decl_rational_parameter(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_sort_name(a0, a1):
  r = lib().Z3_get_sort_name(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_sort(a0, a1):
  r = lib().Z3_get_sort(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_domain_size(a0, a1):
  r = lib().Z3_get_domain_size(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_domain(a0, a1, a2):
  r = lib().Z3_get_domain(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_range(a0, a1):
  r = lib().Z3_get_range(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_sort_kind(a0, a1):
  r = lib().Z3_get_sort_kind(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_bv_sort_size(a0, a1):
  r = lib().Z3_get_bv_sort_size(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_array_sort_domain(a0, a1):
  r = lib().Z3_get_array_sort_domain(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_array_sort_range(a0, a1):
  r = lib().Z3_get_array_sort_range(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_tuple_sort_mk_decl(a0, a1):
  r = lib().Z3_get_tuple_sort_mk_decl(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_decl_kind(a0, a1):
  r = lib().Z3_get_decl_kind(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_tuple_sort_num_fields(a0, a1):
  r = lib().Z3_get_tuple_sort_num_fields(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_tuple_sort_field_decl(a0, a1, a2):
  r = lib().Z3_get_tuple_sort_field_decl(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_datatype_sort_num_constructors(a0, a1):
  r = lib().Z3_get_datatype_sort_num_constructors(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_datatype_sort_constructor(a0, a1, a2):
  r = lib().Z3_get_datatype_sort_constructor(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_datatype_sort_recognizer(a0, a1, a2):
  r = lib().Z3_get_datatype_sort_recognizer(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_datatype_sort_constructor_accessor(a0, a1, a2, a3):
  r = lib().Z3_get_datatype_sort_constructor_accessor(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_relation_arity(a0, a1):
  r = lib().Z3_get_relation_arity(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_relation_column(a0, a1, a2):
  r = lib().Z3_get_relation_column(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_finite_domain_sort_size(a0, a1, a2):
  r = lib().Z3_get_finite_domain_sort_size(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_finite_domain_sort(a0, a1, a2):
  r = lib().Z3_mk_finite_domain_sort(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_pattern_num_terms(a0, a1):
  r = lib().Z3_get_pattern_num_terms(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_pattern(a0, a1, a2):
  r = lib().Z3_get_pattern(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_simplify(a0, a1):
  r = lib().Z3_simplify(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_simplify_ex(a0, a1, a2):
  r = lib().Z3_simplify_ex(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_simplify_get_help(a0):
  r = lib().Z3_simplify_get_help(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_simplify_get_param_descrs(a0):
  r = lib().Z3_simplify_get_param_descrs(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_update_term(a0, a1, a2, a3):
  r = lib().Z3_update_term(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_substitute(a0, a1, a2, a3, a4):
  r = lib().Z3_substitute(a0, a1, a2, a3, a4)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_substitute_vars(a0, a1, a2, a3):
  r = lib().Z3_substitute_vars(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_sort_to_ast(a0, a1):
  r = lib().Z3_sort_to_ast(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_func_decl_to_ast(a0, a1):
  r = lib().Z3_func_decl_to_ast(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_pattern_to_ast(a0, a1):
  r = lib().Z3_pattern_to_ast(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_app_to_ast(a0, a1):
  r = lib().Z3_app_to_ast(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_to_app(a0, a1):
  r = lib().Z3_to_app(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_to_func_decl(a0, a1):
  r = lib().Z3_to_func_decl(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_push(a0):
  lib().Z3_push(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_pop(a0, a1):
  lib().Z3_pop(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_get_num_scopes(a0):
  r = lib().Z3_get_num_scopes(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_persist_ast(a0, a1, a2):
  lib().Z3_persist_ast(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_assert_cnstr(a0, a1):
  lib().Z3_assert_cnstr(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_check_and_get_model(a0, a1):
  r = lib().Z3_check_and_get_model(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_check(a0):
  r = lib().Z3_check(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_check_assumptions(a0, a1, a2, a3, a4, a5, a6):
  r = lib().Z3_check_assumptions(a0, a1, a2, a3, a4, a5, a6)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_implied_equalities(a0, a1, a2, a3):
  r = lib().Z3_get_implied_equalities(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_del_model(a0, a1):
  lib().Z3_del_model(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_soft_check_cancel(a0):
  lib().Z3_soft_check_cancel(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_get_search_failure(a0):
  r = lib().Z3_get_search_failure(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_relevant_labels(a0):
  r = lib().Z3_get_relevant_labels(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_relevant_literals(a0):
  r = lib().Z3_get_relevant_literals(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_guessed_literals(a0):
  r = lib().Z3_get_guessed_literals(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_del_literals(a0, a1):
  lib().Z3_del_literals(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_get_num_literals(a0, a1):
  r = lib().Z3_get_num_literals(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_label_symbol(a0, a1, a2):
  r = lib().Z3_get_label_symbol(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_literal(a0, a1, a2):
  r = lib().Z3_get_literal(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_disable_literal(a0, a1, a2):
  lib().Z3_disable_literal(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_block_literals(a0, a1):
  lib().Z3_block_literals(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_model_inc_ref(a0, a1):
  lib().Z3_model_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_model_dec_ref(a0, a1):
  lib().Z3_model_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_model_get_const_interp(a0, a1, a2):
  r = lib().Z3_model_get_const_interp(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_model_get_func_interp(a0, a1, a2):
  r = lib().Z3_model_get_func_interp(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_model_get_num_consts(a0, a1):
  r = lib().Z3_model_get_num_consts(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_model_get_const_decl(a0, a1, a2):
  r = lib().Z3_model_get_const_decl(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_model_get_num_funcs(a0, a1):
  r = lib().Z3_model_get_num_funcs(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_model_get_func_decl(a0, a1, a2):
  r = lib().Z3_model_get_func_decl(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_model_eval(a0, a1, a2, a3, a4):
  r = lib().Z3_model_eval(a0, a1, a2, a3, a4)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_model_get_num_sorts(a0, a1):
  r = lib().Z3_model_get_num_sorts(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_model_get_sort(a0, a1, a2):
  r = lib().Z3_model_get_sort(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_model_get_sort_universe(a0, a1, a2):
  r = lib().Z3_model_get_sort_universe(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_is_as_array(a0, a1):
  r = lib().Z3_is_as_array(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_as_array_func_decl(a0, a1):
  r = lib().Z3_get_as_array_func_decl(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_func_interp_inc_ref(a0, a1):
  lib().Z3_func_interp_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_func_interp_dec_ref(a0, a1):
  lib().Z3_func_interp_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_func_interp_get_num_entries(a0, a1):
  r = lib().Z3_func_interp_get_num_entries(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_func_interp_get_entry(a0, a1, a2):
  r = lib().Z3_func_interp_get_entry(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_func_interp_get_else(a0, a1):
  r = lib().Z3_func_interp_get_else(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_func_interp_get_arity(a0, a1):
  r = lib().Z3_func_interp_get_arity(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_func_entry_inc_ref(a0, a1):
  lib().Z3_func_entry_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_func_entry_dec_ref(a0, a1):
  lib().Z3_func_entry_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_func_entry_get_value(a0, a1):
  r = lib().Z3_func_entry_get_value(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_func_entry_get_num_args(a0, a1):
  r = lib().Z3_func_entry_get_num_args(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_func_entry_get_arg(a0, a1, a2):
  r = lib().Z3_func_entry_get_arg(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_model_num_constants(a0, a1):
  r = lib().Z3_get_model_num_constants(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_model_constant(a0, a1, a2):
  r = lib().Z3_get_model_constant(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_eval_func_decl(a0, a1, a2, a3):
  r = lib().Z3_eval_func_decl(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_is_array_value(a0, a1, a2, a3):
  r = lib().Z3_is_array_value(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_array_value(a0, a1, a2, a3, a4, a5, a6):
  lib().Z3_get_array_value(a0, a1, a2, a3, a4, a5, a6)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_get_model_num_funcs(a0, a1):
  r = lib().Z3_get_model_num_funcs(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_model_func_decl(a0, a1, a2):
  r = lib().Z3_get_model_func_decl(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_model_func_else(a0, a1, a2):
  r = lib().Z3_get_model_func_else(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_model_func_num_entries(a0, a1, a2):
  r = lib().Z3_get_model_func_num_entries(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_model_func_entry_num_args(a0, a1, a2, a3):
  r = lib().Z3_get_model_func_entry_num_args(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_model_func_entry_arg(a0, a1, a2, a3, a4):
  r = lib().Z3_get_model_func_entry_arg(a0, a1, a2, a3, a4)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_model_func_entry_value(a0, a1, a2, a3):
  r = lib().Z3_get_model_func_entry_value(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_eval(a0, a1, a2, a3):
  r = lib().Z3_eval(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_eval_decl(a0, a1, a2, a3, a4, a5):
  r = lib().Z3_eval_decl(a0, a1, a2, a3, a4, a5)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_set_ast_print_mode(a0, a1):
  lib().Z3_set_ast_print_mode(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_ast_to_string(a0, a1):
  r = lib().Z3_ast_to_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_pattern_to_string(a0, a1):
  r = lib().Z3_pattern_to_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_sort_to_string(a0, a1):
  r = lib().Z3_sort_to_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_func_decl_to_string(a0, a1):
  r = lib().Z3_func_decl_to_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_model_to_string(a0, a1):
  r = lib().Z3_model_to_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_benchmark_to_smtlib_string(a0, a1, a2, a3, a4, a5, a6, a7):
  r = lib().Z3_benchmark_to_smtlib_string(a0, a1, a2, a3, a4, a5, a6, a7)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_context_to_string(a0):
  r = lib().Z3_context_to_string(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_statistics_to_string(a0):
  r = lib().Z3_statistics_to_string(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_context_assignment(a0):
  r = lib().Z3_get_context_assignment(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_parse_smtlib_string(a0, a1, a2, a3, a4, a5, a6, a7):
  lib().Z3_parse_smtlib_string(a0, a1, a2, a3, a4, a5, a6, a7)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_parse_smtlib_file(a0, a1, a2, a3, a4, a5, a6, a7):
  lib().Z3_parse_smtlib_file(a0, a1, a2, a3, a4, a5, a6, a7)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_get_smtlib_num_formulas(a0):
  r = lib().Z3_get_smtlib_num_formulas(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_smtlib_formula(a0, a1):
  r = lib().Z3_get_smtlib_formula(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_smtlib_num_assumptions(a0):
  r = lib().Z3_get_smtlib_num_assumptions(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_smtlib_assumption(a0, a1):
  r = lib().Z3_get_smtlib_assumption(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_smtlib_num_decls(a0):
  r = lib().Z3_get_smtlib_num_decls(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_smtlib_decl(a0, a1):
  r = lib().Z3_get_smtlib_decl(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_smtlib_num_sorts(a0):
  r = lib().Z3_get_smtlib_num_sorts(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_smtlib_sort(a0, a1):
  r = lib().Z3_get_smtlib_sort(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_smtlib_error(a0):
  r = lib().Z3_get_smtlib_error(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_parse_z3_string(a0, a1):
  r = lib().Z3_parse_z3_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_parse_z3_file(a0, a1):
  r = lib().Z3_parse_z3_file(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_parse_smtlib2_string(a0, a1, a2, a3, a4, a5, a6, a7):
  r = lib().Z3_parse_smtlib2_string(a0, a1, a2, a3, a4, a5, a6, a7)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_parse_smtlib2_file(a0, a1, a2, a3, a4, a5, a6, a7):
  r = lib().Z3_parse_smtlib2_file(a0, a1, a2, a3, a4, a5, a6, a7)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_error_code(a0):
  r = lib().Z3_get_error_code(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_set_error(a0, a1):
  lib().Z3_set_error(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_get_error_msg(a0):
  r = lib().Z3_get_error_msg(a0)
  return r

def Z3_get_version(a0, a1, a2, a3):
  lib().Z3_get_version(a0, a1, a2, a3)

def Z3_reset_memory():
  lib().Z3_reset_memory()

def Z3_is_app(a0, a1):
  r = lib().Z3_is_app(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_is_numeral_ast(a0, a1):
  r = lib().Z3_is_numeral_ast(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_arity(a0, a1):
  r = lib().Z3_get_arity(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_injective_function(a0, a1, a2, a3, a4):
  r = lib().Z3_mk_injective_function(a0, a1, a2, a3, a4)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_fixedpoint(a0):
  r = lib().Z3_mk_fixedpoint(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_fixedpoint_inc_ref(a0, a1):
  lib().Z3_fixedpoint_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_fixedpoint_dec_ref(a0, a1):
  lib().Z3_fixedpoint_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_fixedpoint_push(a0, a1):
  lib().Z3_fixedpoint_push(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_fixedpoint_pop(a0, a1):
  lib().Z3_fixedpoint_pop(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_fixedpoint_register_relation(a0, a1, a2):
  lib().Z3_fixedpoint_register_relation(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_fixedpoint_assert(a0, a1, a2):
  lib().Z3_fixedpoint_assert(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_fixedpoint_add_rule(a0, a1, a2, a3):
  lib().Z3_fixedpoint_add_rule(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_fixedpoint_add_fact(a0, a1, a2, a3, a4):
  lib().Z3_fixedpoint_add_fact(a0, a1, a2, a3, a4)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_fixedpoint_query(a0, a1, a2):
  r = lib().Z3_fixedpoint_query(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_fixedpoint_query_relations(a0, a1, a2, a3):
  r = lib().Z3_fixedpoint_query_relations(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_fixedpoint_get_answer(a0, a1):
  r = lib().Z3_fixedpoint_get_answer(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_fixedpoint_update_rule(a0, a1, a2, a3):
  lib().Z3_fixedpoint_update_rule(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_fixedpoint_get_num_levels(a0, a1, a2):
  r = lib().Z3_fixedpoint_get_num_levels(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_fixedpoint_get_cover_delta(a0, a1, a2, a3):
  r = lib().Z3_fixedpoint_get_cover_delta(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_fixedpoint_add_cover(a0, a1, a2, a3, a4):
  lib().Z3_fixedpoint_add_cover(a0, a1, a2, a3, a4)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_fixedpoint_get_statistics(a0, a1):
  r = lib().Z3_fixedpoint_get_statistics(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_fixedpoint_get_help(a0, a1):
  r = lib().Z3_fixedpoint_get_help(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_fixedpoint_get_param_descrs(a0, a1):
  r = lib().Z3_fixedpoint_get_param_descrs(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_fixedpoint_set_params(a0, a1, a2):
  lib().Z3_fixedpoint_set_params(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_fixedpoint_to_string(a0, a1, a2, a3):
  r = lib().Z3_fixedpoint_to_string(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_fixedpoint_get_reason_unknown(a0, a1):
  r = lib().Z3_fixedpoint_get_reason_unknown(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_fixedpoint_set_predicate_representation(a0, a1, a2, a3, a4):
  lib().Z3_fixedpoint_set_predicate_representation(a0, a1, a2, a3, a4)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_fixedpoint_simplify_rules(a0, a1, a2, a3, a4, a5):
  r = lib().Z3_fixedpoint_simplify_rules(a0, a1, a2, a3, a4, a5)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_params(a0):
  r = lib().Z3_mk_params(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_params_inc_ref(a0, a1):
  lib().Z3_params_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_params_dec_ref(a0, a1):
  lib().Z3_params_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_params_set_bool(a0, a1, a2, a3):
  lib().Z3_params_set_bool(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_params_set_uint(a0, a1, a2, a3):
  lib().Z3_params_set_uint(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_params_set_double(a0, a1, a2, a3):
  lib().Z3_params_set_double(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_params_set_symbol(a0, a1, a2, a3):
  lib().Z3_params_set_symbol(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_params_to_string(a0, a1):
  r = lib().Z3_params_to_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_params_validate(a0, a1, a2):
  lib().Z3_params_validate(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_param_descrs_inc_ref(a0, a1):
  lib().Z3_param_descrs_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_param_descrs_dec_ref(a0, a1):
  lib().Z3_param_descrs_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_param_descrs_get_kind(a0, a1, a2):
  r = lib().Z3_param_descrs_get_kind(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_param_descrs_size(a0, a1):
  r = lib().Z3_param_descrs_size(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_param_descrs_get_name(a0, a1, a2):
  r = lib().Z3_param_descrs_get_name(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_interrupt(a0):
  lib().Z3_interrupt(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_get_error_msg_ex(a0, a1):
  r = lib().Z3_get_error_msg_ex(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_translate(a0, a1, a2):
  r = lib().Z3_translate(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_goal(a0, a1, a2, a3):
  r = lib().Z3_mk_goal(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_goal_inc_ref(a0, a1):
  lib().Z3_goal_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_goal_dec_ref(a0, a1):
  lib().Z3_goal_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_goal_precision(a0, a1):
  r = lib().Z3_goal_precision(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_goal_assert(a0, a1, a2):
  lib().Z3_goal_assert(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_goal_inconsistent(a0, a1):
  r = lib().Z3_goal_inconsistent(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_goal_depth(a0, a1):
  r = lib().Z3_goal_depth(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_goal_reset(a0, a1):
  lib().Z3_goal_reset(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_goal_size(a0, a1):
  r = lib().Z3_goal_size(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_goal_formula(a0, a1, a2):
  r = lib().Z3_goal_formula(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_goal_num_exprs(a0, a1):
  r = lib().Z3_goal_num_exprs(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_goal_is_decided_sat(a0, a1):
  r = lib().Z3_goal_is_decided_sat(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_goal_is_decided_unsat(a0, a1):
  r = lib().Z3_goal_is_decided_unsat(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_goal_translate(a0, a1, a2):
  r = lib().Z3_goal_translate(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_goal_to_string(a0, a1):
  r = lib().Z3_goal_to_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_tactic(a0, a1):
  r = lib().Z3_mk_tactic(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_probe(a0, a1):
  r = lib().Z3_mk_probe(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_inc_ref(a0, a1):
  lib().Z3_tactic_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_tactic_dec_ref(a0, a1):
  lib().Z3_tactic_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_probe_inc_ref(a0, a1):
  lib().Z3_probe_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_probe_dec_ref(a0, a1):
  lib().Z3_probe_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_tactic_and_then(a0, a1, a2):
  r = lib().Z3_tactic_and_then(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_or_else(a0, a1, a2):
  r = lib().Z3_tactic_or_else(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_par_or(a0, a1, a2):
  r = lib().Z3_tactic_par_or(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_par_and_then(a0, a1, a2):
  r = lib().Z3_tactic_par_and_then(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_try_for(a0, a1, a2):
  r = lib().Z3_tactic_try_for(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_when(a0, a1, a2):
  r = lib().Z3_tactic_when(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_cond(a0, a1, a2, a3):
  r = lib().Z3_tactic_cond(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_repeat(a0, a1, a2):
  r = lib().Z3_tactic_repeat(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_skip(a0):
  r = lib().Z3_tactic_skip(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_fail(a0):
  r = lib().Z3_tactic_fail(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_fail_if(a0, a1):
  r = lib().Z3_tactic_fail_if(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_fail_if_not_decided(a0):
  r = lib().Z3_tactic_fail_if_not_decided(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_using_params(a0, a1, a2):
  r = lib().Z3_tactic_using_params(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_probe_const(a0, a1):
  r = lib().Z3_probe_const(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_probe_lt(a0, a1, a2):
  r = lib().Z3_probe_lt(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_probe_le(a0, a1, a2):
  r = lib().Z3_probe_le(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_probe_gt(a0, a1, a2):
  r = lib().Z3_probe_gt(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_probe_ge(a0, a1, a2):
  r = lib().Z3_probe_ge(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_probe_eq(a0, a1, a2):
  r = lib().Z3_probe_eq(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_probe_and(a0, a1, a2):
  r = lib().Z3_probe_and(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_probe_or(a0, a1, a2):
  r = lib().Z3_probe_or(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_probe_not(a0, a1):
  r = lib().Z3_probe_not(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_num_tactics(a0):
  r = lib().Z3_get_num_tactics(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_tactic_name(a0, a1):
  r = lib().Z3_get_tactic_name(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_num_probes(a0):
  r = lib().Z3_get_num_probes(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_get_probe_name(a0, a1):
  r = lib().Z3_get_probe_name(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_get_help(a0, a1):
  r = lib().Z3_tactic_get_help(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_get_param_descrs(a0, a1):
  r = lib().Z3_tactic_get_param_descrs(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_get_descr(a0, a1):
  r = lib().Z3_tactic_get_descr(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_probe_get_descr(a0, a1):
  r = lib().Z3_probe_get_descr(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_probe_apply(a0, a1, a2):
  r = lib().Z3_probe_apply(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_apply(a0, a1, a2):
  r = lib().Z3_tactic_apply(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_tactic_apply_ex(a0, a1, a2, a3):
  r = lib().Z3_tactic_apply_ex(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_apply_result_inc_ref(a0, a1):
  lib().Z3_apply_result_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_apply_result_dec_ref(a0, a1):
  lib().Z3_apply_result_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_apply_result_to_string(a0, a1):
  r = lib().Z3_apply_result_to_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_apply_result_get_num_subgoals(a0, a1):
  r = lib().Z3_apply_result_get_num_subgoals(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_apply_result_get_subgoal(a0, a1, a2):
  r = lib().Z3_apply_result_get_subgoal(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_apply_result_convert_model(a0, a1, a2, a3):
  r = lib().Z3_apply_result_convert_model(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_solver(a0):
  r = lib().Z3_mk_solver(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_simple_solver(a0):
  r = lib().Z3_mk_simple_solver(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_solver_for_logic(a0, a1):
  r = lib().Z3_mk_solver_for_logic(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_solver_from_tactic(a0, a1):
  r = lib().Z3_mk_solver_from_tactic(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_solver_get_help(a0, a1):
  r = lib().Z3_solver_get_help(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_solver_get_param_descrs(a0, a1):
  r = lib().Z3_solver_get_param_descrs(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_solver_set_params(a0, a1, a2):
  lib().Z3_solver_set_params(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_solver_inc_ref(a0, a1):
  lib().Z3_solver_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_solver_dec_ref(a0, a1):
  lib().Z3_solver_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_solver_push(a0, a1):
  lib().Z3_solver_push(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_solver_pop(a0, a1, a2):
  lib().Z3_solver_pop(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_solver_reset(a0, a1):
  lib().Z3_solver_reset(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_solver_get_num_scopes(a0, a1):
  r = lib().Z3_solver_get_num_scopes(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_solver_assert(a0, a1, a2):
  lib().Z3_solver_assert(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_solver_get_assertions(a0, a1):
  r = lib().Z3_solver_get_assertions(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_solver_check(a0, a1):
  r = lib().Z3_solver_check(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_solver_check_assumptions(a0, a1, a2, a3):
  r = lib().Z3_solver_check_assumptions(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_solver_get_model(a0, a1):
  r = lib().Z3_solver_get_model(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_solver_get_proof(a0, a1):
  r = lib().Z3_solver_get_proof(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_solver_get_unsat_core(a0, a1):
  r = lib().Z3_solver_get_unsat_core(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_solver_get_reason_unknown(a0, a1):
  r = lib().Z3_solver_get_reason_unknown(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_solver_get_statistics(a0, a1):
  r = lib().Z3_solver_get_statistics(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_solver_to_string(a0, a1):
  r = lib().Z3_solver_to_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_stats_to_string(a0, a1):
  r = lib().Z3_stats_to_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_stats_inc_ref(a0, a1):
  lib().Z3_stats_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_stats_dec_ref(a0, a1):
  lib().Z3_stats_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_stats_size(a0, a1):
  r = lib().Z3_stats_size(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_stats_get_key(a0, a1, a2):
  r = lib().Z3_stats_get_key(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_stats_is_uint(a0, a1, a2):
  r = lib().Z3_stats_is_uint(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_stats_is_double(a0, a1, a2):
  r = lib().Z3_stats_is_double(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_stats_get_uint_value(a0, a1, a2):
  r = lib().Z3_stats_get_uint_value(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_stats_get_double_value(a0, a1, a2):
  r = lib().Z3_stats_get_double_value(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_ast_vector(a0):
  r = lib().Z3_mk_ast_vector(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_ast_vector_inc_ref(a0, a1):
  lib().Z3_ast_vector_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_ast_vector_dec_ref(a0, a1):
  lib().Z3_ast_vector_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_ast_vector_size(a0, a1):
  r = lib().Z3_ast_vector_size(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_ast_vector_get(a0, a1, a2):
  r = lib().Z3_ast_vector_get(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_ast_vector_set(a0, a1, a2, a3):
  lib().Z3_ast_vector_set(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_ast_vector_resize(a0, a1, a2):
  lib().Z3_ast_vector_resize(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_ast_vector_push(a0, a1, a2):
  lib().Z3_ast_vector_push(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_ast_vector_translate(a0, a1, a2):
  r = lib().Z3_ast_vector_translate(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_ast_vector_to_string(a0, a1):
  r = lib().Z3_ast_vector_to_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_mk_ast_map(a0):
  r = lib().Z3_mk_ast_map(a0)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_ast_map_inc_ref(a0, a1):
  lib().Z3_ast_map_inc_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_ast_map_dec_ref(a0, a1):
  lib().Z3_ast_map_dec_ref(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_ast_map_contains(a0, a1, a2):
  r = lib().Z3_ast_map_contains(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_ast_map_find(a0, a1, a2):
  r = lib().Z3_ast_map_find(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_ast_map_insert(a0, a1, a2, a3):
  lib().Z3_ast_map_insert(a0, a1, a2, a3)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_ast_map_erase(a0, a1, a2):
  lib().Z3_ast_map_erase(a0, a1, a2)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_ast_map_size(a0, a1):
  r = lib().Z3_ast_map_size(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_ast_map_reset(a0, a1):
  lib().Z3_ast_map_reset(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))

def Z3_ast_map_keys(a0, a1):
  r = lib().Z3_ast_map_keys(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_ast_map_to_string(a0, a1):
  r = lib().Z3_ast_map_to_string(a0, a1)
  err = lib().Z3_get_error_code(a0)
  if err != Z3_OK:
    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))
  return r

def Z3_open_log(a0):
  r = lib().Z3_open_log(a0)
  return r

def Z3_append_log(a0):
  lib().Z3_append_log(a0)

def Z3_close_log():
  lib().Z3_close_log()

