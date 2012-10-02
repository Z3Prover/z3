// Automatically generated file, generator: api.py
#include"z3.h"
#include"z3_replayer.h"
void Z3_replacer_error_handler(Z3_context ctx, Z3_error_code c) { printf("[REPLAYER ERROR HANDLER]: %s\n", Z3_get_error_msg_ex(ctx, c)); }
void exec_Z3_mk_config(z3_replayer & in) {
  Z3_config result = Z3_mk_config(
    );
  in.store_result(result);
}
void exec_Z3_del_config(z3_replayer & in) {
  Z3_del_config(
    reinterpret_cast<Z3_config>(in.get_obj(0)));
}
void exec_Z3_set_param_value(z3_replayer & in) {
  Z3_set_param_value(
    reinterpret_cast<Z3_config>(in.get_obj(0)),
    in.get_str(1),
    in.get_str(2));
}
void exec_Z3_mk_context(z3_replayer & in) {
  Z3_context result = Z3_mk_context(
    reinterpret_cast<Z3_config>(in.get_obj(0)));
  in.store_result(result);
  Z3_set_error_handler(result, Z3_replacer_error_handler);}
void exec_Z3_mk_context_rc(z3_replayer & in) {
  Z3_context result = Z3_mk_context_rc(
    reinterpret_cast<Z3_config>(in.get_obj(0)));
  in.store_result(result);
  Z3_set_error_handler(result, Z3_replacer_error_handler);}
void exec_Z3_set_logic(z3_replayer & in) {
  Z3_set_logic(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1));
}
void exec_Z3_del_context(z3_replayer & in) {
  Z3_del_context(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_inc_ref(z3_replayer & in) {
  Z3_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_dec_ref(z3_replayer & in) {
  Z3_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_toggle_warning_messages(z3_replayer & in) {
  Z3_toggle_warning_messages(
    in.get_bool(0));
}
void exec_Z3_update_param_value(z3_replayer & in) {
  Z3_update_param_value(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1),
    in.get_str(2));
}
void exec_Z3_get_param_value(z3_replayer & in) {
  Z3_get_param_value(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1),
    in.get_str_addr(2));
}
void exec_Z3_mk_int_symbol(z3_replayer & in) {
  Z3_mk_int_symbol(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_int(1));
}
void exec_Z3_mk_string_symbol(z3_replayer & in) {
  Z3_mk_string_symbol(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1));
}
void exec_Z3_is_eq_sort(z3_replayer & in) {
  Z3_is_eq_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)),
    reinterpret_cast<Z3_sort>(in.get_obj(2)));
}
void exec_Z3_mk_uninterpreted_sort(z3_replayer & in) {
  Z3_sort result = Z3_mk_uninterpreted_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1));
  in.store_result(result);
}
void exec_Z3_mk_bool_sort(z3_replayer & in) {
  Z3_sort result = Z3_mk_bool_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_mk_int_sort(z3_replayer & in) {
  Z3_sort result = Z3_mk_int_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_mk_real_sort(z3_replayer & in) {
  Z3_sort result = Z3_mk_real_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_mk_bv_sort(z3_replayer & in) {
  Z3_sort result = Z3_mk_bv_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1));
  in.store_result(result);
}
void exec_Z3_mk_array_sort(z3_replayer & in) {
  Z3_sort result = Z3_mk_array_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)),
    reinterpret_cast<Z3_sort>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_tuple_sort(z3_replayer & in) {
  Z3_sort result = Z3_mk_tuple_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1),
    in.get_uint(2),
    in.get_symbol_array(3),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(4)),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_addr(5)),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_array(6)));
  in.store_result(result);
}
void exec_Z3_mk_enumeration_sort(z3_replayer & in) {
  Z3_sort result = Z3_mk_enumeration_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1),
    in.get_uint(2),
    in.get_symbol_array(3),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_array(4)),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_array(5)));
  in.store_result(result);
}
void exec_Z3_mk_list_sort(z3_replayer & in) {
  Z3_sort result = Z3_mk_list_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1),
    reinterpret_cast<Z3_sort>(in.get_obj(2)),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_addr(3)),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_addr(4)),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_addr(5)),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_addr(6)),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_addr(7)),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_addr(8)));
  in.store_result(result);
}
void exec_Z3_mk_constructor(z3_replayer & in) {
  Z3_constructor result = Z3_mk_constructor(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1),
    in.get_symbol(2),
    in.get_uint(3),
    in.get_symbol_array(4),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(5)),
    in.get_uint_array(6));
  in.store_result(result);
}
void exec_Z3_query_constructor(z3_replayer & in) {
  Z3_query_constructor(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_constructor>(in.get_obj(1)),
    in.get_uint(2),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_addr(3)),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_addr(4)),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_array(5)));
}
void exec_Z3_del_constructor(z3_replayer & in) {
  Z3_del_constructor(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_constructor>(in.get_obj(1)));
}
void exec_Z3_mk_datatype(z3_replayer & in) {
  Z3_sort result = Z3_mk_datatype(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1),
    in.get_uint(2),
    reinterpret_cast<Z3_constructor*>(in.get_obj_array(3)));
  in.store_result(result);
}
void exec_Z3_mk_constructor_list(z3_replayer & in) {
  Z3_constructor_list result = Z3_mk_constructor_list(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_constructor*>(in.get_obj_array(2)));
  in.store_result(result);
}
void exec_Z3_del_constructor_list(z3_replayer & in) {
  Z3_del_constructor_list(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_constructor_list>(in.get_obj(1)));
}
void exec_Z3_mk_datatypes(z3_replayer & in) {
  Z3_mk_datatypes(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    in.get_symbol_array(2),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(3)),
    reinterpret_cast<Z3_constructor_list*>(in.get_obj_array(4)));
}
void exec_Z3_is_eq_ast(z3_replayer & in) {
  Z3_is_eq_ast(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
}
void exec_Z3_is_eq_func_decl(z3_replayer & in) {
  Z3_is_eq_func_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(2)));
}
void exec_Z3_mk_func_decl(z3_replayer & in) {
  Z3_func_decl result = Z3_mk_func_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1),
    in.get_uint(2),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(3)),
    reinterpret_cast<Z3_sort>(in.get_obj(4)));
  in.store_result(result);
}
void exec_Z3_mk_app(z3_replayer & in) {
  Z3_ast result = Z3_mk_app(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)),
    in.get_uint(2),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(3)));
  in.store_result(result);
}
void exec_Z3_mk_const(z3_replayer & in) {
  Z3_ast result = Z3_mk_const(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1),
    reinterpret_cast<Z3_sort>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_label(z3_replayer & in) {
  Z3_ast result = Z3_mk_label(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1),
    in.get_bool(2),
    reinterpret_cast<Z3_ast>(in.get_obj(3)));
  in.store_result(result);
}
void exec_Z3_mk_fresh_func_decl(z3_replayer & in) {
  Z3_func_decl result = Z3_mk_fresh_func_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1),
    in.get_uint(2),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(3)),
    reinterpret_cast<Z3_sort>(in.get_obj(4)));
  in.store_result(result);
}
void exec_Z3_mk_fresh_const(z3_replayer & in) {
  Z3_ast result = Z3_mk_fresh_const(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1),
    reinterpret_cast<Z3_sort>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_true(z3_replayer & in) {
  Z3_ast result = Z3_mk_true(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_mk_false(z3_replayer & in) {
  Z3_ast result = Z3_mk_false(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_mk_eq(z3_replayer & in) {
  Z3_ast result = Z3_mk_eq(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_distinct(z3_replayer & in) {
  Z3_ast result = Z3_mk_distinct(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(2)));
  in.store_result(result);
}
void exec_Z3_mk_not(z3_replayer & in) {
  Z3_ast result = Z3_mk_not(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_ite(z3_replayer & in) {
  Z3_ast result = Z3_mk_ite(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)),
    reinterpret_cast<Z3_ast>(in.get_obj(3)));
  in.store_result(result);
}
void exec_Z3_mk_iff(z3_replayer & in) {
  Z3_ast result = Z3_mk_iff(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_implies(z3_replayer & in) {
  Z3_ast result = Z3_mk_implies(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_xor(z3_replayer & in) {
  Z3_ast result = Z3_mk_xor(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_and(z3_replayer & in) {
  Z3_ast result = Z3_mk_and(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(2)));
  in.store_result(result);
}
void exec_Z3_mk_or(z3_replayer & in) {
  Z3_ast result = Z3_mk_or(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(2)));
  in.store_result(result);
}
void exec_Z3_mk_add(z3_replayer & in) {
  Z3_ast result = Z3_mk_add(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(2)));
  in.store_result(result);
}
void exec_Z3_mk_mul(z3_replayer & in) {
  Z3_ast result = Z3_mk_mul(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(2)));
  in.store_result(result);
}
void exec_Z3_mk_sub(z3_replayer & in) {
  Z3_ast result = Z3_mk_sub(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(2)));
  in.store_result(result);
}
void exec_Z3_mk_unary_minus(z3_replayer & in) {
  Z3_ast result = Z3_mk_unary_minus(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_div(z3_replayer & in) {
  Z3_ast result = Z3_mk_div(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_mod(z3_replayer & in) {
  Z3_ast result = Z3_mk_mod(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_rem(z3_replayer & in) {
  Z3_ast result = Z3_mk_rem(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_power(z3_replayer & in) {
  Z3_ast result = Z3_mk_power(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_is_algebraic_number(z3_replayer & in) {
  Z3_is_algebraic_number(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_algebraic_number_lower(z3_replayer & in) {
  Z3_ast result = Z3_get_algebraic_number_lower(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_algebraic_number_upper(z3_replayer & in) {
  Z3_ast result = Z3_get_algebraic_number_upper(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_mk_lt(z3_replayer & in) {
  Z3_ast result = Z3_mk_lt(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_le(z3_replayer & in) {
  Z3_ast result = Z3_mk_le(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_gt(z3_replayer & in) {
  Z3_ast result = Z3_mk_gt(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_ge(z3_replayer & in) {
  Z3_ast result = Z3_mk_ge(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_int2real(z3_replayer & in) {
  Z3_ast result = Z3_mk_int2real(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_real2int(z3_replayer & in) {
  Z3_ast result = Z3_mk_real2int(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_is_int(z3_replayer & in) {
  Z3_ast result = Z3_mk_is_int(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_bvnot(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvnot(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_bvredand(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvredand(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_bvredor(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvredor(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_bvand(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvand(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvor(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvor(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvxor(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvxor(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvnand(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvnand(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvnor(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvnor(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvxnor(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvxnor(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvneg(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvneg(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_bvadd(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvadd(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvsub(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvsub(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvmul(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvmul(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvudiv(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvudiv(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvsdiv(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvsdiv(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvurem(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvurem(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvsrem(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvsrem(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvsmod(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvsmod(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvult(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvult(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvslt(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvslt(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvule(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvule(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvsle(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvsle(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvuge(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvuge(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvsge(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvsge(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvugt(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvugt(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvsgt(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvsgt(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_concat(z3_replayer & in) {
  Z3_ast result = Z3_mk_concat(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_extract(z3_replayer & in) {
  Z3_ast result = Z3_mk_extract(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    in.get_uint(2),
    reinterpret_cast<Z3_ast>(in.get_obj(3)));
  in.store_result(result);
}
void exec_Z3_mk_sign_ext(z3_replayer & in) {
  Z3_ast result = Z3_mk_sign_ext(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_zero_ext(z3_replayer & in) {
  Z3_ast result = Z3_mk_zero_ext(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_repeat(z3_replayer & in) {
  Z3_ast result = Z3_mk_repeat(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvshl(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvshl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvlshr(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvlshr(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvashr(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvashr(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_rotate_left(z3_replayer & in) {
  Z3_ast result = Z3_mk_rotate_left(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_rotate_right(z3_replayer & in) {
  Z3_ast result = Z3_mk_rotate_right(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_ext_rotate_left(z3_replayer & in) {
  Z3_ast result = Z3_mk_ext_rotate_left(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_ext_rotate_right(z3_replayer & in) {
  Z3_ast result = Z3_mk_ext_rotate_right(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_int2bv(z3_replayer & in) {
  Z3_ast result = Z3_mk_int2bv(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bv2int(z3_replayer & in) {
  Z3_ast result = Z3_mk_bv2int(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_bool(2));
  in.store_result(result);
}
void exec_Z3_mk_bvadd_no_overflow(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvadd_no_overflow(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)),
    in.get_bool(3));
  in.store_result(result);
}
void exec_Z3_mk_bvadd_no_underflow(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvadd_no_underflow(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvsub_no_overflow(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvsub_no_overflow(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvsub_no_underflow(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvsub_no_underflow(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)),
    in.get_bool(3));
  in.store_result(result);
}
void exec_Z3_mk_bvsdiv_no_overflow(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvsdiv_no_overflow(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_bvneg_no_overflow(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvneg_no_overflow(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_bvmul_no_overflow(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvmul_no_overflow(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)),
    in.get_bool(3));
  in.store_result(result);
}
void exec_Z3_mk_bvmul_no_underflow(z3_replayer & in) {
  Z3_ast result = Z3_mk_bvmul_no_underflow(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_select(z3_replayer & in) {
  Z3_ast result = Z3_mk_select(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_store(z3_replayer & in) {
  Z3_ast result = Z3_mk_store(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)),
    reinterpret_cast<Z3_ast>(in.get_obj(3)));
  in.store_result(result);
}
void exec_Z3_mk_const_array(z3_replayer & in) {
  Z3_ast result = Z3_mk_const_array(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_map(z3_replayer & in) {
  Z3_ast result = Z3_mk_map(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)),
    in.get_uint(2),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(3)));
  in.store_result(result);
}
void exec_Z3_mk_array_default(z3_replayer & in) {
  Z3_ast result = Z3_mk_array_default(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_set_sort(z3_replayer & in) {
  Z3_sort result = Z3_mk_set_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_empty_set(z3_replayer & in) {
  Z3_ast result = Z3_mk_empty_set(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_full_set(z3_replayer & in) {
  Z3_ast result = Z3_mk_full_set(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_set_add(z3_replayer & in) {
  Z3_ast result = Z3_mk_set_add(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_set_del(z3_replayer & in) {
  Z3_ast result = Z3_mk_set_del(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_set_union(z3_replayer & in) {
  Z3_ast result = Z3_mk_set_union(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(2)));
  in.store_result(result);
}
void exec_Z3_mk_set_intersect(z3_replayer & in) {
  Z3_ast result = Z3_mk_set_intersect(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(2)));
  in.store_result(result);
}
void exec_Z3_mk_set_difference(z3_replayer & in) {
  Z3_ast result = Z3_mk_set_difference(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_set_complement(z3_replayer & in) {
  Z3_ast result = Z3_mk_set_complement(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_mk_set_member(z3_replayer & in) {
  Z3_ast result = Z3_mk_set_member(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_set_subset(z3_replayer & in) {
  Z3_ast result = Z3_mk_set_subset(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_numeral(z3_replayer & in) {
  Z3_ast result = Z3_mk_numeral(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1),
    reinterpret_cast<Z3_sort>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_real(z3_replayer & in) {
  Z3_ast result = Z3_mk_real(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_int(1),
    in.get_int(2));
  in.store_result(result);
}
void exec_Z3_mk_int(z3_replayer & in) {
  Z3_ast result = Z3_mk_int(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_int(1),
    reinterpret_cast<Z3_sort>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_unsigned_int(z3_replayer & in) {
  Z3_ast result = Z3_mk_unsigned_int(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_sort>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_int64(z3_replayer & in) {
  Z3_ast result = Z3_mk_int64(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_int64(1),
    reinterpret_cast<Z3_sort>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_unsigned_int64(z3_replayer & in) {
  Z3_ast result = Z3_mk_unsigned_int64(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint64(1),
    reinterpret_cast<Z3_sort>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_pattern(z3_replayer & in) {
  Z3_pattern result = Z3_mk_pattern(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(2)));
  in.store_result(result);
}
void exec_Z3_mk_bound(z3_replayer & in) {
  Z3_ast result = Z3_mk_bound(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_sort>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_forall(z3_replayer & in) {
  Z3_ast result = Z3_mk_forall(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    in.get_uint(2),
    reinterpret_cast<Z3_pattern*>(in.get_obj_array(3)),
    in.get_uint(4),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(5)),
    in.get_symbol_array(6),
    reinterpret_cast<Z3_ast>(in.get_obj(7)));
  in.store_result(result);
}
void exec_Z3_mk_exists(z3_replayer & in) {
  Z3_ast result = Z3_mk_exists(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    in.get_uint(2),
    reinterpret_cast<Z3_pattern*>(in.get_obj_array(3)),
    in.get_uint(4),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(5)),
    in.get_symbol_array(6),
    reinterpret_cast<Z3_ast>(in.get_obj(7)));
  in.store_result(result);
}
void exec_Z3_mk_quantifier(z3_replayer & in) {
  Z3_ast result = Z3_mk_quantifier(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_bool(1),
    in.get_uint(2),
    in.get_uint(3),
    reinterpret_cast<Z3_pattern*>(in.get_obj_array(4)),
    in.get_uint(5),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(6)),
    in.get_symbol_array(7),
    reinterpret_cast<Z3_ast>(in.get_obj(8)));
  in.store_result(result);
}
void exec_Z3_mk_quantifier_ex(z3_replayer & in) {
  Z3_ast result = Z3_mk_quantifier_ex(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_bool(1),
    in.get_uint(2),
    in.get_symbol(3),
    in.get_symbol(4),
    in.get_uint(5),
    reinterpret_cast<Z3_pattern*>(in.get_obj_array(6)),
    in.get_uint(7),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(8)),
    in.get_uint(9),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(10)),
    in.get_symbol_array(11),
    reinterpret_cast<Z3_ast>(in.get_obj(12)));
  in.store_result(result);
}
void exec_Z3_mk_forall_const(z3_replayer & in) {
  Z3_ast result = Z3_mk_forall_const(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    in.get_uint(2),
    reinterpret_cast<Z3_app*>(in.get_obj_array(3)),
    in.get_uint(4),
    reinterpret_cast<Z3_pattern*>(in.get_obj_array(5)),
    reinterpret_cast<Z3_ast>(in.get_obj(6)));
  in.store_result(result);
}
void exec_Z3_mk_exists_const(z3_replayer & in) {
  Z3_ast result = Z3_mk_exists_const(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    in.get_uint(2),
    reinterpret_cast<Z3_app*>(in.get_obj_array(3)),
    in.get_uint(4),
    reinterpret_cast<Z3_pattern*>(in.get_obj_array(5)),
    reinterpret_cast<Z3_ast>(in.get_obj(6)));
  in.store_result(result);
}
void exec_Z3_mk_quantifier_const(z3_replayer & in) {
  Z3_ast result = Z3_mk_quantifier_const(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_bool(1),
    in.get_uint(2),
    in.get_uint(3),
    reinterpret_cast<Z3_app*>(in.get_obj_array(4)),
    in.get_uint(5),
    reinterpret_cast<Z3_pattern*>(in.get_obj_array(6)),
    reinterpret_cast<Z3_ast>(in.get_obj(7)));
  in.store_result(result);
}
void exec_Z3_mk_quantifier_const_ex(z3_replayer & in) {
  Z3_ast result = Z3_mk_quantifier_const_ex(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_bool(1),
    in.get_uint(2),
    in.get_symbol(3),
    in.get_symbol(4),
    in.get_uint(5),
    reinterpret_cast<Z3_app*>(in.get_obj_array(6)),
    in.get_uint(7),
    reinterpret_cast<Z3_pattern*>(in.get_obj_array(8)),
    in.get_uint(9),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(10)),
    reinterpret_cast<Z3_ast>(in.get_obj(11)));
  in.store_result(result);
}
void exec_Z3_get_ast_id(z3_replayer & in) {
  Z3_get_ast_id(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_func_decl_id(z3_replayer & in) {
  Z3_get_func_decl_id(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)));
}
void exec_Z3_get_sort_id(z3_replayer & in) {
  Z3_get_sort_id(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
}
void exec_Z3_is_well_sorted(z3_replayer & in) {
  Z3_is_well_sorted(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_symbol_kind(z3_replayer & in) {
  Z3_get_symbol_kind(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1));
}
void exec_Z3_get_symbol_int(z3_replayer & in) {
  Z3_get_symbol_int(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1));
}
void exec_Z3_get_symbol_string(z3_replayer & in) {
  Z3_get_symbol_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1));
}
void exec_Z3_get_ast_kind(z3_replayer & in) {
  Z3_get_ast_kind(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_ast_hash(z3_replayer & in) {
  Z3_get_ast_hash(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_numeral_string(z3_replayer & in) {
  Z3_get_numeral_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_numeral_decimal_string(z3_replayer & in) {
  Z3_get_numeral_decimal_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_get_numerator(z3_replayer & in) {
  Z3_ast result = Z3_get_numerator(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_get_denominator(z3_replayer & in) {
  Z3_ast result = Z3_get_denominator(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_get_numeral_small(z3_replayer & in) {
  Z3_get_numeral_small(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_int64_addr(2),
    in.get_int64_addr(3));
}
void exec_Z3_get_numeral_int(z3_replayer & in) {
  Z3_get_numeral_int(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_int_addr(2));
}
void exec_Z3_get_numeral_uint(z3_replayer & in) {
  Z3_get_numeral_uint(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_uint_addr(2));
}
void exec_Z3_get_numeral_uint64(z3_replayer & in) {
  Z3_get_numeral_uint64(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_uint64_addr(2));
}
void exec_Z3_get_numeral_int64(z3_replayer & in) {
  Z3_get_numeral_int64(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_int64_addr(2));
}
void exec_Z3_get_numeral_rational_int64(z3_replayer & in) {
  Z3_get_numeral_rational_int64(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_int64_addr(2),
    in.get_int64_addr(3));
}
void exec_Z3_get_bool_value(z3_replayer & in) {
  Z3_get_bool_value(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_app_decl(z3_replayer & in) {
  Z3_func_decl result = Z3_get_app_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_app>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_get_app_num_args(z3_replayer & in) {
  Z3_get_app_num_args(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_app>(in.get_obj(1)));
}
void exec_Z3_get_app_arg(z3_replayer & in) {
  Z3_ast result = Z3_get_app_arg(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_app>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_index_value(z3_replayer & in) {
  Z3_get_index_value(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_is_quantifier_forall(z3_replayer & in) {
  Z3_is_quantifier_forall(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_quantifier_weight(z3_replayer & in) {
  Z3_get_quantifier_weight(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_quantifier_num_patterns(z3_replayer & in) {
  Z3_get_quantifier_num_patterns(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_quantifier_pattern_ast(z3_replayer & in) {
  Z3_pattern result = Z3_get_quantifier_pattern_ast(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_quantifier_num_no_patterns(z3_replayer & in) {
  Z3_get_quantifier_num_no_patterns(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_quantifier_no_pattern_ast(z3_replayer & in) {
  Z3_ast result = Z3_get_quantifier_no_pattern_ast(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_quantifier_bound_name(z3_replayer & in) {
  Z3_get_quantifier_bound_name(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_get_quantifier_bound_sort(z3_replayer & in) {
  Z3_sort result = Z3_get_quantifier_bound_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_quantifier_body(z3_replayer & in) {
  Z3_ast result = Z3_get_quantifier_body(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_get_quantifier_num_bound(z3_replayer & in) {
  Z3_get_quantifier_num_bound(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_decl_name(z3_replayer & in) {
  Z3_get_decl_name(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)));
}
void exec_Z3_get_decl_num_parameters(z3_replayer & in) {
  Z3_get_decl_num_parameters(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)));
}
void exec_Z3_get_decl_parameter_kind(z3_replayer & in) {
  Z3_get_decl_parameter_kind(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_get_decl_int_parameter(z3_replayer & in) {
  Z3_get_decl_int_parameter(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_get_decl_double_parameter(z3_replayer & in) {
  Z3_get_decl_double_parameter(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_get_decl_symbol_parameter(z3_replayer & in) {
  Z3_get_decl_symbol_parameter(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_get_decl_sort_parameter(z3_replayer & in) {
  Z3_sort result = Z3_get_decl_sort_parameter(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_decl_ast_parameter(z3_replayer & in) {
  Z3_ast result = Z3_get_decl_ast_parameter(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_decl_func_decl_parameter(z3_replayer & in) {
  Z3_func_decl result = Z3_get_decl_func_decl_parameter(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_decl_rational_parameter(z3_replayer & in) {
  Z3_get_decl_rational_parameter(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_get_sort_name(z3_replayer & in) {
  Z3_get_sort_name(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
}
void exec_Z3_get_sort(z3_replayer & in) {
  Z3_sort result = Z3_get_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_get_domain_size(z3_replayer & in) {
  Z3_get_domain_size(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)));
}
void exec_Z3_get_domain(z3_replayer & in) {
  Z3_sort result = Z3_get_domain(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_range(z3_replayer & in) {
  Z3_sort result = Z3_get_range(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_get_sort_kind(z3_replayer & in) {
  Z3_get_sort_kind(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
}
void exec_Z3_get_bv_sort_size(z3_replayer & in) {
  Z3_get_bv_sort_size(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
}
void exec_Z3_get_array_sort_domain(z3_replayer & in) {
  Z3_sort result = Z3_get_array_sort_domain(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_get_array_sort_range(z3_replayer & in) {
  Z3_sort result = Z3_get_array_sort_range(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_get_tuple_sort_mk_decl(z3_replayer & in) {
  Z3_func_decl result = Z3_get_tuple_sort_mk_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_get_decl_kind(z3_replayer & in) {
  Z3_get_decl_kind(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)));
}
void exec_Z3_get_tuple_sort_num_fields(z3_replayer & in) {
  Z3_get_tuple_sort_num_fields(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
}
void exec_Z3_get_tuple_sort_field_decl(z3_replayer & in) {
  Z3_func_decl result = Z3_get_tuple_sort_field_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_datatype_sort_num_constructors(z3_replayer & in) {
  Z3_get_datatype_sort_num_constructors(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
}
void exec_Z3_get_datatype_sort_constructor(z3_replayer & in) {
  Z3_func_decl result = Z3_get_datatype_sort_constructor(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_datatype_sort_recognizer(z3_replayer & in) {
  Z3_func_decl result = Z3_get_datatype_sort_recognizer(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_datatype_sort_constructor_accessor(z3_replayer & in) {
  Z3_func_decl result = Z3_get_datatype_sort_constructor_accessor(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)),
    in.get_uint(2),
    in.get_uint(3));
  in.store_result(result);
}
void exec_Z3_get_relation_arity(z3_replayer & in) {
  Z3_get_relation_arity(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
}
void exec_Z3_get_relation_column(z3_replayer & in) {
  Z3_sort result = Z3_get_relation_column(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_finite_domain_sort_size(z3_replayer & in) {
  Z3_get_finite_domain_sort_size(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)),
    in.get_uint64_addr(2));
}
void exec_Z3_mk_finite_domain_sort(z3_replayer & in) {
  Z3_sort result = Z3_mk_finite_domain_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1),
    in.get_uint64(2));
  in.store_result(result);
}
void exec_Z3_get_pattern_num_terms(z3_replayer & in) {
  Z3_get_pattern_num_terms(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_pattern>(in.get_obj(1)));
}
void exec_Z3_get_pattern(z3_replayer & in) {
  Z3_ast result = Z3_get_pattern(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_pattern>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_simplify(z3_replayer & in) {
  Z3_ast result = Z3_simplify(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_simplify_ex(z3_replayer & in) {
  Z3_ast result = Z3_simplify_ex(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_params>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_simplify_get_help(z3_replayer & in) {
  Z3_simplify_get_help(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_simplify_get_param_descrs(z3_replayer & in) {
  Z3_param_descrs result = Z3_simplify_get_param_descrs(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_update_term(z3_replayer & in) {
  Z3_ast result = Z3_update_term(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_uint(2),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(3)));
  in.store_result(result);
}
void exec_Z3_substitute(z3_replayer & in) {
  Z3_ast result = Z3_substitute(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_uint(2),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(3)),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(4)));
  in.store_result(result);
}
void exec_Z3_substitute_vars(z3_replayer & in) {
  Z3_ast result = Z3_substitute_vars(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_uint(2),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(3)));
  in.store_result(result);
}
void exec_Z3_sort_to_ast(z3_replayer & in) {
  Z3_ast result = Z3_sort_to_ast(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_func_decl_to_ast(z3_replayer & in) {
  Z3_ast result = Z3_func_decl_to_ast(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_pattern_to_ast(z3_replayer & in) {
  Z3_ast result = Z3_pattern_to_ast(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_pattern>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_app_to_ast(z3_replayer & in) {
  Z3_ast result = Z3_app_to_ast(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_app>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_to_app(z3_replayer & in) {
  Z3_app result = Z3_to_app(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_to_func_decl(z3_replayer & in) {
  Z3_func_decl result = Z3_to_func_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_push(z3_replayer & in) {
  Z3_push(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_pop(z3_replayer & in) {
  Z3_pop(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1));
}
void exec_Z3_get_num_scopes(z3_replayer & in) {
  Z3_get_num_scopes(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_persist_ast(z3_replayer & in) {
  Z3_persist_ast(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_assert_cnstr(z3_replayer & in) {
  Z3_assert_cnstr(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_check_and_get_model(z3_replayer & in) {
  Z3_check_and_get_model(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model*>(in.get_obj_addr(1)));
}
void exec_Z3_check(z3_replayer & in) {
  Z3_check(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_check_assumptions(z3_replayer & in) {
  Z3_check_assumptions(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(2)),
    reinterpret_cast<Z3_model*>(in.get_obj_addr(3)),
    reinterpret_cast<Z3_ast*>(in.get_obj_addr(4)),
    in.get_uint_addr(5),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(6)));
}
void exec_Z3_get_implied_equalities(z3_replayer & in) {
  Z3_get_implied_equalities(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(2)),
    in.get_uint_array(3));
}
void exec_Z3_del_model(z3_replayer & in) {
  Z3_del_model(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)));
}
void exec_Z3_soft_check_cancel(z3_replayer & in) {
  Z3_soft_check_cancel(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_get_search_failure(z3_replayer & in) {
  Z3_get_search_failure(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_get_relevant_labels(z3_replayer & in) {
  Z3_literals result = Z3_get_relevant_labels(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_get_relevant_literals(z3_replayer & in) {
  Z3_literals result = Z3_get_relevant_literals(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_get_guessed_literals(z3_replayer & in) {
  Z3_literals result = Z3_get_guessed_literals(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_del_literals(z3_replayer & in) {
  Z3_del_literals(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_literals>(in.get_obj(1)));
}
void exec_Z3_get_num_literals(z3_replayer & in) {
  Z3_get_num_literals(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_literals>(in.get_obj(1)));
}
void exec_Z3_get_label_symbol(z3_replayer & in) {
  Z3_get_label_symbol(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_literals>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_get_literal(z3_replayer & in) {
  Z3_ast result = Z3_get_literal(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_literals>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_disable_literal(z3_replayer & in) {
  Z3_disable_literal(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_literals>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_block_literals(z3_replayer & in) {
  Z3_block_literals(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_literals>(in.get_obj(1)));
}
void exec_Z3_model_inc_ref(z3_replayer & in) {
  Z3_model_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)));
}
void exec_Z3_model_dec_ref(z3_replayer & in) {
  Z3_model_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)));
}
void exec_Z3_model_get_const_interp(z3_replayer & in) {
  Z3_ast result = Z3_model_get_const_interp(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_model_get_func_interp(z3_replayer & in) {
  Z3_func_interp result = Z3_model_get_func_interp(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_model_get_num_consts(z3_replayer & in) {
  Z3_model_get_num_consts(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)));
}
void exec_Z3_model_get_const_decl(z3_replayer & in) {
  Z3_func_decl result = Z3_model_get_const_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_model_get_num_funcs(z3_replayer & in) {
  Z3_model_get_num_funcs(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)));
}
void exec_Z3_model_get_func_decl(z3_replayer & in) {
  Z3_func_decl result = Z3_model_get_func_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_model_eval(z3_replayer & in) {
  Z3_model_eval(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)),
    in.get_bool(3),
    reinterpret_cast<Z3_ast*>(in.get_obj_addr(4)));
}
void exec_Z3_model_get_num_sorts(z3_replayer & in) {
  Z3_model_get_num_sorts(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)));
}
void exec_Z3_model_get_sort(z3_replayer & in) {
  Z3_sort result = Z3_model_get_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_model_get_sort_universe(z3_replayer & in) {
  Z3_ast_vector result = Z3_model_get_sort_universe(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    reinterpret_cast<Z3_sort>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_is_as_array(z3_replayer & in) {
  Z3_is_as_array(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_as_array_func_decl(z3_replayer & in) {
  Z3_func_decl result = Z3_get_as_array_func_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_func_interp_inc_ref(z3_replayer & in) {
  Z3_func_interp_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_interp>(in.get_obj(1)));
}
void exec_Z3_func_interp_dec_ref(z3_replayer & in) {
  Z3_func_interp_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_interp>(in.get_obj(1)));
}
void exec_Z3_func_interp_get_num_entries(z3_replayer & in) {
  Z3_func_interp_get_num_entries(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_interp>(in.get_obj(1)));
}
void exec_Z3_func_interp_get_entry(z3_replayer & in) {
  Z3_func_entry result = Z3_func_interp_get_entry(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_interp>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_func_interp_get_else(z3_replayer & in) {
  Z3_ast result = Z3_func_interp_get_else(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_interp>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_func_interp_get_arity(z3_replayer & in) {
  Z3_func_interp_get_arity(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_interp>(in.get_obj(1)));
}
void exec_Z3_func_entry_inc_ref(z3_replayer & in) {
  Z3_func_entry_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_entry>(in.get_obj(1)));
}
void exec_Z3_func_entry_dec_ref(z3_replayer & in) {
  Z3_func_entry_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_entry>(in.get_obj(1)));
}
void exec_Z3_func_entry_get_value(z3_replayer & in) {
  Z3_ast result = Z3_func_entry_get_value(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_entry>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_func_entry_get_num_args(z3_replayer & in) {
  Z3_func_entry_get_num_args(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_entry>(in.get_obj(1)));
}
void exec_Z3_func_entry_get_arg(z3_replayer & in) {
  Z3_ast result = Z3_func_entry_get_arg(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_entry>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_model_num_constants(z3_replayer & in) {
  Z3_get_model_num_constants(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)));
}
void exec_Z3_get_model_constant(z3_replayer & in) {
  Z3_func_decl result = Z3_get_model_constant(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_eval_func_decl(z3_replayer & in) {
  Z3_eval_func_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(2)),
    reinterpret_cast<Z3_ast*>(in.get_obj_addr(3)));
}
void exec_Z3_is_array_value(z3_replayer & in) {
  Z3_is_array_value(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)),
    in.get_uint_addr(3));
}
void exec_Z3_get_array_value(z3_replayer & in) {
  Z3_get_array_value(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)),
    in.get_uint(3),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(4)),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(5)),
    reinterpret_cast<Z3_ast*>(in.get_obj_addr(6)));
}
void exec_Z3_get_model_num_funcs(z3_replayer & in) {
  Z3_get_model_num_funcs(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)));
}
void exec_Z3_get_model_func_decl(z3_replayer & in) {
  Z3_func_decl result = Z3_get_model_func_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_model_func_else(z3_replayer & in) {
  Z3_ast result = Z3_get_model_func_else(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_get_model_func_num_entries(z3_replayer & in) {
  Z3_get_model_func_num_entries(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_get_model_func_entry_num_args(z3_replayer & in) {
  Z3_get_model_func_entry_num_args(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    in.get_uint(2),
    in.get_uint(3));
}
void exec_Z3_get_model_func_entry_arg(z3_replayer & in) {
  Z3_ast result = Z3_get_model_func_entry_arg(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    in.get_uint(2),
    in.get_uint(3),
    in.get_uint(4));
  in.store_result(result);
}
void exec_Z3_get_model_func_entry_value(z3_replayer & in) {
  Z3_ast result = Z3_get_model_func_entry_value(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    in.get_uint(2),
    in.get_uint(3));
  in.store_result(result);
}
void exec_Z3_eval(z3_replayer & in) {
  Z3_eval(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)),
    reinterpret_cast<Z3_ast*>(in.get_obj_addr(3)));
}
void exec_Z3_eval_decl(z3_replayer & in) {
  Z3_eval_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(2)),
    in.get_uint(3),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(4)),
    reinterpret_cast<Z3_ast*>(in.get_obj_addr(5)));
}
void exec_Z3_set_ast_print_mode(z3_replayer & in) {
  Z3_set_ast_print_mode(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    static_cast<Z3_ast_print_mode>(in.get_uint(1)));
}
void exec_Z3_ast_to_string(z3_replayer & in) {
  Z3_ast_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_pattern_to_string(z3_replayer & in) {
  Z3_pattern_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_pattern>(in.get_obj(1)));
}
void exec_Z3_sort_to_string(z3_replayer & in) {
  Z3_sort_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_sort>(in.get_obj(1)));
}
void exec_Z3_func_decl_to_string(z3_replayer & in) {
  Z3_func_decl_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)));
}
void exec_Z3_model_to_string(z3_replayer & in) {
  Z3_model_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_model>(in.get_obj(1)));
}
void exec_Z3_benchmark_to_smtlib_string(z3_replayer & in) {
  Z3_benchmark_to_smtlib_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1),
    in.get_str(2),
    in.get_str(3),
    in.get_str(4),
    in.get_uint(5),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(6)),
    reinterpret_cast<Z3_ast>(in.get_obj(7)));
}
void exec_Z3_context_to_string(z3_replayer & in) {
  Z3_context_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_statistics_to_string(z3_replayer & in) {
  Z3_statistics_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_get_context_assignment(z3_replayer & in) {
  Z3_ast result = Z3_get_context_assignment(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_parse_smtlib_string(z3_replayer & in) {
  Z3_parse_smtlib_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1),
    in.get_uint(2),
    in.get_symbol_array(3),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(4)),
    in.get_uint(5),
    in.get_symbol_array(6),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_array(7)));
}
void exec_Z3_parse_smtlib_file(z3_replayer & in) {
  Z3_parse_smtlib_file(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1),
    in.get_uint(2),
    in.get_symbol_array(3),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(4)),
    in.get_uint(5),
    in.get_symbol_array(6),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_array(7)));
}
void exec_Z3_get_smtlib_num_formulas(z3_replayer & in) {
  Z3_get_smtlib_num_formulas(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_get_smtlib_formula(z3_replayer & in) {
  Z3_ast result = Z3_get_smtlib_formula(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1));
  in.store_result(result);
}
void exec_Z3_get_smtlib_num_assumptions(z3_replayer & in) {
  Z3_get_smtlib_num_assumptions(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_get_smtlib_assumption(z3_replayer & in) {
  Z3_ast result = Z3_get_smtlib_assumption(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1));
  in.store_result(result);
}
void exec_Z3_get_smtlib_num_decls(z3_replayer & in) {
  Z3_get_smtlib_num_decls(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_get_smtlib_decl(z3_replayer & in) {
  Z3_func_decl result = Z3_get_smtlib_decl(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1));
  in.store_result(result);
}
void exec_Z3_get_smtlib_num_sorts(z3_replayer & in) {
  Z3_get_smtlib_num_sorts(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_get_smtlib_sort(z3_replayer & in) {
  Z3_sort result = Z3_get_smtlib_sort(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1));
  in.store_result(result);
}
void exec_Z3_get_smtlib_error(z3_replayer & in) {
  Z3_get_smtlib_error(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_parse_z3_string(z3_replayer & in) {
  Z3_ast result = Z3_parse_z3_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1));
  in.store_result(result);
}
void exec_Z3_parse_z3_file(z3_replayer & in) {
  Z3_ast result = Z3_parse_z3_file(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1));
  in.store_result(result);
}
void exec_Z3_parse_smtlib2_string(z3_replayer & in) {
  Z3_ast result = Z3_parse_smtlib2_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1),
    in.get_uint(2),
    in.get_symbol_array(3),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(4)),
    in.get_uint(5),
    in.get_symbol_array(6),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_array(7)));
  in.store_result(result);
}
void exec_Z3_parse_smtlib2_file(z3_replayer & in) {
  Z3_ast result = Z3_parse_smtlib2_file(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1),
    in.get_uint(2),
    in.get_symbol_array(3),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(4)),
    in.get_uint(5),
    in.get_symbol_array(6),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_array(7)));
  in.store_result(result);
}
void exec_Z3_get_error_code(z3_replayer & in) {
  Z3_get_error_code(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_set_error(z3_replayer & in) {
  Z3_set_error(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    static_cast<Z3_error_code>(in.get_uint(1)));
}
void exec_Z3_get_error_msg(z3_replayer & in) {
  Z3_get_error_msg(
    static_cast<Z3_error_code>(in.get_uint(0)));
}
void exec_Z3_get_version(z3_replayer & in) {
  Z3_get_version(
    in.get_uint_addr(0),
    in.get_uint_addr(1),
    in.get_uint_addr(2),
    in.get_uint_addr(3));
}
void exec_Z3_reset_memory(z3_replayer & in) {
  Z3_reset_memory(
    );
}
void exec_Z3_is_app(z3_replayer & in) {
  Z3_is_app(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_is_numeral_ast(z3_replayer & in) {
  Z3_is_numeral_ast(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)));
}
void exec_Z3_get_arity(z3_replayer & in) {
  Z3_get_arity(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(1)));
}
void exec_Z3_mk_injective_function(z3_replayer & in) {
  Z3_func_decl result = Z3_mk_injective_function(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1),
    in.get_uint(2),
    reinterpret_cast<Z3_sort*>(in.get_obj_array(3)),
    reinterpret_cast<Z3_sort>(in.get_obj(4)));
  in.store_result(result);
}
void exec_Z3_mk_fixedpoint(z3_replayer & in) {
  Z3_fixedpoint result = Z3_mk_fixedpoint(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_fixedpoint_inc_ref(z3_replayer & in) {
  Z3_fixedpoint_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)));
}
void exec_Z3_fixedpoint_dec_ref(z3_replayer & in) {
  Z3_fixedpoint_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)));
}
void exec_Z3_fixedpoint_push(z3_replayer & in) {
  Z3_fixedpoint_push(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)));
}
void exec_Z3_fixedpoint_pop(z3_replayer & in) {
  Z3_fixedpoint_pop(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)));
}
void exec_Z3_fixedpoint_register_relation(z3_replayer & in) {
  Z3_fixedpoint_register_relation(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(2)));
}
void exec_Z3_fixedpoint_assert(z3_replayer & in) {
  Z3_fixedpoint_assert(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
}
void exec_Z3_fixedpoint_add_rule(z3_replayer & in) {
  Z3_fixedpoint_add_rule(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)),
    in.get_symbol(3));
}
void exec_Z3_fixedpoint_add_fact(z3_replayer & in) {
  Z3_fixedpoint_add_fact(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(2)),
    in.get_uint(3),
    in.get_uint_array(4));
}
void exec_Z3_fixedpoint_query(z3_replayer & in) {
  Z3_fixedpoint_query(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
}
void exec_Z3_fixedpoint_query_relations(z3_replayer & in) {
  Z3_fixedpoint_query_relations(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    in.get_uint(2),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_array(3)));
}
void exec_Z3_fixedpoint_get_answer(z3_replayer & in) {
  Z3_ast result = Z3_fixedpoint_get_answer(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_fixedpoint_update_rule(z3_replayer & in) {
  Z3_fixedpoint_update_rule(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)),
    in.get_symbol(3));
}
void exec_Z3_fixedpoint_get_num_levels(z3_replayer & in) {
  Z3_fixedpoint_get_num_levels(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(2)));
}
void exec_Z3_fixedpoint_get_cover_delta(z3_replayer & in) {
  Z3_ast result = Z3_fixedpoint_get_cover_delta(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    in.get_int(2),
    reinterpret_cast<Z3_func_decl>(in.get_obj(3)));
  in.store_result(result);
}
void exec_Z3_fixedpoint_add_cover(z3_replayer & in) {
  Z3_fixedpoint_add_cover(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    in.get_int(2),
    reinterpret_cast<Z3_func_decl>(in.get_obj(3)),
    reinterpret_cast<Z3_ast>(in.get_obj(4)));
}
void exec_Z3_fixedpoint_get_statistics(z3_replayer & in) {
  Z3_stats result = Z3_fixedpoint_get_statistics(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_fixedpoint_get_help(z3_replayer & in) {
  Z3_fixedpoint_get_help(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)));
}
void exec_Z3_fixedpoint_get_param_descrs(z3_replayer & in) {
  Z3_param_descrs result = Z3_fixedpoint_get_param_descrs(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_fixedpoint_set_params(z3_replayer & in) {
  Z3_fixedpoint_set_params(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    reinterpret_cast<Z3_params>(in.get_obj(2)));
}
void exec_Z3_fixedpoint_to_string(z3_replayer & in) {
  Z3_fixedpoint_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    in.get_uint(2),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(3)));
}
void exec_Z3_fixedpoint_get_reason_unknown(z3_replayer & in) {
  Z3_fixedpoint_get_reason_unknown(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)));
}
void exec_Z3_fixedpoint_set_predicate_representation(z3_replayer & in) {
  Z3_fixedpoint_set_predicate_representation(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    reinterpret_cast<Z3_func_decl>(in.get_obj(2)),
    in.get_uint(3),
    in.get_symbol_array(4));
}
void exec_Z3_fixedpoint_simplify_rules(z3_replayer & in) {
  Z3_ast_vector result = Z3_fixedpoint_simplify_rules(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_fixedpoint>(in.get_obj(1)),
    in.get_uint(2),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(3)),
    in.get_uint(4),
    reinterpret_cast<Z3_func_decl*>(in.get_obj_array(5)));
  in.store_result(result);
}
void exec_Z3_mk_params(z3_replayer & in) {
  Z3_params result = Z3_mk_params(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_params_inc_ref(z3_replayer & in) {
  Z3_params_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_params>(in.get_obj(1)));
}
void exec_Z3_params_dec_ref(z3_replayer & in) {
  Z3_params_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_params>(in.get_obj(1)));
}
void exec_Z3_params_set_bool(z3_replayer & in) {
  Z3_params_set_bool(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_params>(in.get_obj(1)),
    in.get_symbol(2),
    in.get_bool(3));
}
void exec_Z3_params_set_uint(z3_replayer & in) {
  Z3_params_set_uint(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_params>(in.get_obj(1)),
    in.get_symbol(2),
    in.get_uint(3));
}
void exec_Z3_params_set_double(z3_replayer & in) {
  Z3_params_set_double(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_params>(in.get_obj(1)),
    in.get_symbol(2),
    in.get_double(3));
}
void exec_Z3_params_set_symbol(z3_replayer & in) {
  Z3_params_set_symbol(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_params>(in.get_obj(1)),
    in.get_symbol(2),
    in.get_symbol(3));
}
void exec_Z3_params_to_string(z3_replayer & in) {
  Z3_params_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_params>(in.get_obj(1)));
}
void exec_Z3_params_validate(z3_replayer & in) {
  Z3_params_validate(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_params>(in.get_obj(1)),
    reinterpret_cast<Z3_param_descrs>(in.get_obj(2)));
}
void exec_Z3_param_descrs_inc_ref(z3_replayer & in) {
  Z3_param_descrs_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_param_descrs>(in.get_obj(1)));
}
void exec_Z3_param_descrs_dec_ref(z3_replayer & in) {
  Z3_param_descrs_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_param_descrs>(in.get_obj(1)));
}
void exec_Z3_param_descrs_get_kind(z3_replayer & in) {
  Z3_param_descrs_get_kind(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_param_descrs>(in.get_obj(1)),
    in.get_symbol(2));
}
void exec_Z3_param_descrs_size(z3_replayer & in) {
  Z3_param_descrs_size(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_param_descrs>(in.get_obj(1)));
}
void exec_Z3_param_descrs_get_name(z3_replayer & in) {
  Z3_param_descrs_get_name(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_param_descrs>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_interrupt(z3_replayer & in) {
  Z3_interrupt(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_get_error_msg_ex(z3_replayer & in) {
  Z3_get_error_msg_ex(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    static_cast<Z3_error_code>(in.get_uint(1)));
}
void exec_Z3_translate(z3_replayer & in) {
  Z3_ast result = Z3_translate(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast>(in.get_obj(1)),
    reinterpret_cast<Z3_context>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_mk_goal(z3_replayer & in) {
  Z3_goal result = Z3_mk_goal(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_bool(1),
    in.get_bool(2),
    in.get_bool(3));
  in.store_result(result);
}
void exec_Z3_goal_inc_ref(z3_replayer & in) {
  Z3_goal_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)));
}
void exec_Z3_goal_dec_ref(z3_replayer & in) {
  Z3_goal_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)));
}
void exec_Z3_goal_precision(z3_replayer & in) {
  Z3_goal_precision(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)));
}
void exec_Z3_goal_assert(z3_replayer & in) {
  Z3_goal_assert(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
}
void exec_Z3_goal_inconsistent(z3_replayer & in) {
  Z3_goal_inconsistent(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)));
}
void exec_Z3_goal_depth(z3_replayer & in) {
  Z3_goal_depth(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)));
}
void exec_Z3_goal_reset(z3_replayer & in) {
  Z3_goal_reset(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)));
}
void exec_Z3_goal_size(z3_replayer & in) {
  Z3_goal_size(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)));
}
void exec_Z3_goal_formula(z3_replayer & in) {
  Z3_ast result = Z3_goal_formula(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_goal_num_exprs(z3_replayer & in) {
  Z3_goal_num_exprs(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)));
}
void exec_Z3_goal_is_decided_sat(z3_replayer & in) {
  Z3_goal_is_decided_sat(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)));
}
void exec_Z3_goal_is_decided_unsat(z3_replayer & in) {
  Z3_goal_is_decided_unsat(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)));
}
void exec_Z3_goal_translate(z3_replayer & in) {
  Z3_goal result = Z3_goal_translate(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)),
    reinterpret_cast<Z3_context>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_goal_to_string(z3_replayer & in) {
  Z3_goal_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_goal>(in.get_obj(1)));
}
void exec_Z3_mk_tactic(z3_replayer & in) {
  Z3_tactic result = Z3_mk_tactic(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1));
  in.store_result(result);
}
void exec_Z3_mk_probe(z3_replayer & in) {
  Z3_probe result = Z3_mk_probe(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1));
  in.store_result(result);
}
void exec_Z3_tactic_inc_ref(z3_replayer & in) {
  Z3_tactic_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_tactic>(in.get_obj(1)));
}
void exec_Z3_tactic_dec_ref(z3_replayer & in) {
  Z3_tactic_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_tactic>(in.get_obj(1)));
}
void exec_Z3_probe_inc_ref(z3_replayer & in) {
  Z3_probe_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)));
}
void exec_Z3_probe_dec_ref(z3_replayer & in) {
  Z3_probe_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)));
}
void exec_Z3_tactic_and_then(z3_replayer & in) {
  Z3_tactic result = Z3_tactic_and_then(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_tactic>(in.get_obj(1)),
    reinterpret_cast<Z3_tactic>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_tactic_or_else(z3_replayer & in) {
  Z3_tactic result = Z3_tactic_or_else(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_tactic>(in.get_obj(1)),
    reinterpret_cast<Z3_tactic>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_tactic_par_or(z3_replayer & in) {
  Z3_tactic result = Z3_tactic_par_or(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1),
    reinterpret_cast<Z3_tactic*>(in.get_obj_array(2)));
  in.store_result(result);
}
void exec_Z3_tactic_par_and_then(z3_replayer & in) {
  Z3_tactic result = Z3_tactic_par_and_then(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_tactic>(in.get_obj(1)),
    reinterpret_cast<Z3_tactic>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_tactic_try_for(z3_replayer & in) {
  Z3_tactic result = Z3_tactic_try_for(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_tactic>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_tactic_when(z3_replayer & in) {
  Z3_tactic result = Z3_tactic_when(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)),
    reinterpret_cast<Z3_tactic>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_tactic_cond(z3_replayer & in) {
  Z3_tactic result = Z3_tactic_cond(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)),
    reinterpret_cast<Z3_tactic>(in.get_obj(2)),
    reinterpret_cast<Z3_tactic>(in.get_obj(3)));
  in.store_result(result);
}
void exec_Z3_tactic_repeat(z3_replayer & in) {
  Z3_tactic result = Z3_tactic_repeat(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_tactic>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_tactic_skip(z3_replayer & in) {
  Z3_tactic result = Z3_tactic_skip(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_tactic_fail(z3_replayer & in) {
  Z3_tactic result = Z3_tactic_fail(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_tactic_fail_if(z3_replayer & in) {
  Z3_tactic result = Z3_tactic_fail_if(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_tactic_fail_if_not_decided(z3_replayer & in) {
  Z3_tactic result = Z3_tactic_fail_if_not_decided(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_tactic_using_params(z3_replayer & in) {
  Z3_tactic result = Z3_tactic_using_params(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_tactic>(in.get_obj(1)),
    reinterpret_cast<Z3_params>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_probe_const(z3_replayer & in) {
  Z3_probe result = Z3_probe_const(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_double(1));
  in.store_result(result);
}
void exec_Z3_probe_lt(z3_replayer & in) {
  Z3_probe result = Z3_probe_lt(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)),
    reinterpret_cast<Z3_probe>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_probe_le(z3_replayer & in) {
  Z3_probe result = Z3_probe_le(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)),
    reinterpret_cast<Z3_probe>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_probe_gt(z3_replayer & in) {
  Z3_probe result = Z3_probe_gt(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)),
    reinterpret_cast<Z3_probe>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_probe_ge(z3_replayer & in) {
  Z3_probe result = Z3_probe_ge(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)),
    reinterpret_cast<Z3_probe>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_probe_eq(z3_replayer & in) {
  Z3_probe result = Z3_probe_eq(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)),
    reinterpret_cast<Z3_probe>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_probe_and(z3_replayer & in) {
  Z3_probe result = Z3_probe_and(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)),
    reinterpret_cast<Z3_probe>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_probe_or(z3_replayer & in) {
  Z3_probe result = Z3_probe_or(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)),
    reinterpret_cast<Z3_probe>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_probe_not(z3_replayer & in) {
  Z3_probe result = Z3_probe_not(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_get_num_tactics(z3_replayer & in) {
  Z3_get_num_tactics(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_get_tactic_name(z3_replayer & in) {
  Z3_get_tactic_name(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1));
}
void exec_Z3_get_num_probes(z3_replayer & in) {
  Z3_get_num_probes(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
}
void exec_Z3_get_probe_name(z3_replayer & in) {
  Z3_get_probe_name(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_uint(1));
}
void exec_Z3_tactic_get_help(z3_replayer & in) {
  Z3_tactic_get_help(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_tactic>(in.get_obj(1)));
}
void exec_Z3_tactic_get_param_descrs(z3_replayer & in) {
  Z3_param_descrs result = Z3_tactic_get_param_descrs(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_tactic>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_tactic_get_descr(z3_replayer & in) {
  Z3_tactic_get_descr(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1));
}
void exec_Z3_probe_get_descr(z3_replayer & in) {
  Z3_probe_get_descr(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_str(1));
}
void exec_Z3_probe_apply(z3_replayer & in) {
  Z3_probe_apply(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_probe>(in.get_obj(1)),
    reinterpret_cast<Z3_goal>(in.get_obj(2)));
}
void exec_Z3_tactic_apply(z3_replayer & in) {
  Z3_apply_result result = Z3_tactic_apply(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_tactic>(in.get_obj(1)),
    reinterpret_cast<Z3_goal>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_tactic_apply_ex(z3_replayer & in) {
  Z3_apply_result result = Z3_tactic_apply_ex(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_tactic>(in.get_obj(1)),
    reinterpret_cast<Z3_goal>(in.get_obj(2)),
    reinterpret_cast<Z3_params>(in.get_obj(3)));
  in.store_result(result);
}
void exec_Z3_apply_result_inc_ref(z3_replayer & in) {
  Z3_apply_result_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_apply_result>(in.get_obj(1)));
}
void exec_Z3_apply_result_dec_ref(z3_replayer & in) {
  Z3_apply_result_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_apply_result>(in.get_obj(1)));
}
void exec_Z3_apply_result_to_string(z3_replayer & in) {
  Z3_apply_result_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_apply_result>(in.get_obj(1)));
}
void exec_Z3_apply_result_get_num_subgoals(z3_replayer & in) {
  Z3_apply_result_get_num_subgoals(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_apply_result>(in.get_obj(1)));
}
void exec_Z3_apply_result_get_subgoal(z3_replayer & in) {
  Z3_goal result = Z3_apply_result_get_subgoal(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_apply_result>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_apply_result_convert_model(z3_replayer & in) {
  Z3_model result = Z3_apply_result_convert_model(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_apply_result>(in.get_obj(1)),
    in.get_uint(2),
    reinterpret_cast<Z3_model>(in.get_obj(3)));
  in.store_result(result);
}
void exec_Z3_mk_solver(z3_replayer & in) {
  Z3_solver result = Z3_mk_solver(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_mk_simple_solver(z3_replayer & in) {
  Z3_solver result = Z3_mk_simple_solver(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_mk_solver_for_logic(z3_replayer & in) {
  Z3_solver result = Z3_mk_solver_for_logic(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    in.get_symbol(1));
  in.store_result(result);
}
void exec_Z3_mk_solver_from_tactic(z3_replayer & in) {
  Z3_solver result = Z3_mk_solver_from_tactic(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_tactic>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_solver_get_help(z3_replayer & in) {
  Z3_solver_get_help(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
}
void exec_Z3_solver_get_param_descrs(z3_replayer & in) {
  Z3_param_descrs result = Z3_solver_get_param_descrs(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_solver_set_params(z3_replayer & in) {
  Z3_solver_set_params(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)),
    reinterpret_cast<Z3_params>(in.get_obj(2)));
}
void exec_Z3_solver_inc_ref(z3_replayer & in) {
  Z3_solver_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
}
void exec_Z3_solver_dec_ref(z3_replayer & in) {
  Z3_solver_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
}
void exec_Z3_solver_push(z3_replayer & in) {
  Z3_solver_push(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
}
void exec_Z3_solver_pop(z3_replayer & in) {
  Z3_solver_pop(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_solver_reset(z3_replayer & in) {
  Z3_solver_reset(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
}
void exec_Z3_solver_get_num_scopes(z3_replayer & in) {
  Z3_solver_get_num_scopes(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
}
void exec_Z3_solver_assert(z3_replayer & in) {
  Z3_solver_assert(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
}
void exec_Z3_solver_get_assertions(z3_replayer & in) {
  Z3_ast_vector result = Z3_solver_get_assertions(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_solver_check(z3_replayer & in) {
  Z3_solver_check(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
}
void exec_Z3_solver_check_assumptions(z3_replayer & in) {
  Z3_solver_check_assumptions(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)),
    in.get_uint(2),
    reinterpret_cast<Z3_ast*>(in.get_obj_array(3)));
}
void exec_Z3_solver_get_model(z3_replayer & in) {
  Z3_model result = Z3_solver_get_model(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_solver_get_proof(z3_replayer & in) {
  Z3_ast result = Z3_solver_get_proof(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_solver_get_unsat_core(z3_replayer & in) {
  Z3_ast_vector result = Z3_solver_get_unsat_core(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_solver_get_reason_unknown(z3_replayer & in) {
  Z3_solver_get_reason_unknown(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
}
void exec_Z3_solver_get_statistics(z3_replayer & in) {
  Z3_stats result = Z3_solver_get_statistics(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_solver_to_string(z3_replayer & in) {
  Z3_solver_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_solver>(in.get_obj(1)));
}
void exec_Z3_stats_to_string(z3_replayer & in) {
  Z3_stats_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_stats>(in.get_obj(1)));
}
void exec_Z3_stats_inc_ref(z3_replayer & in) {
  Z3_stats_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_stats>(in.get_obj(1)));
}
void exec_Z3_stats_dec_ref(z3_replayer & in) {
  Z3_stats_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_stats>(in.get_obj(1)));
}
void exec_Z3_stats_size(z3_replayer & in) {
  Z3_stats_size(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_stats>(in.get_obj(1)));
}
void exec_Z3_stats_get_key(z3_replayer & in) {
  Z3_stats_get_key(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_stats>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_stats_is_uint(z3_replayer & in) {
  Z3_stats_is_uint(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_stats>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_stats_is_double(z3_replayer & in) {
  Z3_stats_is_double(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_stats>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_stats_get_uint_value(z3_replayer & in) {
  Z3_stats_get_uint_value(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_stats>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_stats_get_double_value(z3_replayer & in) {
  Z3_stats_get_double_value(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_stats>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_mk_ast_vector(z3_replayer & in) {
  Z3_ast_vector result = Z3_mk_ast_vector(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_ast_vector_inc_ref(z3_replayer & in) {
  Z3_ast_vector_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_vector>(in.get_obj(1)));
}
void exec_Z3_ast_vector_dec_ref(z3_replayer & in) {
  Z3_ast_vector_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_vector>(in.get_obj(1)));
}
void exec_Z3_ast_vector_size(z3_replayer & in) {
  Z3_ast_vector_size(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_vector>(in.get_obj(1)));
}
void exec_Z3_ast_vector_get(z3_replayer & in) {
  Z3_ast result = Z3_ast_vector_get(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_vector>(in.get_obj(1)),
    in.get_uint(2));
  in.store_result(result);
}
void exec_Z3_ast_vector_set(z3_replayer & in) {
  Z3_ast_vector_set(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_vector>(in.get_obj(1)),
    in.get_uint(2),
    reinterpret_cast<Z3_ast>(in.get_obj(3)));
}
void exec_Z3_ast_vector_resize(z3_replayer & in) {
  Z3_ast_vector_resize(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_vector>(in.get_obj(1)),
    in.get_uint(2));
}
void exec_Z3_ast_vector_push(z3_replayer & in) {
  Z3_ast_vector_push(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_vector>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
}
void exec_Z3_ast_vector_translate(z3_replayer & in) {
  Z3_ast_vector result = Z3_ast_vector_translate(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_vector>(in.get_obj(1)),
    reinterpret_cast<Z3_context>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_ast_vector_to_string(z3_replayer & in) {
  Z3_ast_vector_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_vector>(in.get_obj(1)));
}
void exec_Z3_mk_ast_map(z3_replayer & in) {
  Z3_ast_map result = Z3_mk_ast_map(
    reinterpret_cast<Z3_context>(in.get_obj(0)));
  in.store_result(result);
}
void exec_Z3_ast_map_inc_ref(z3_replayer & in) {
  Z3_ast_map_inc_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_map>(in.get_obj(1)));
}
void exec_Z3_ast_map_dec_ref(z3_replayer & in) {
  Z3_ast_map_dec_ref(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_map>(in.get_obj(1)));
}
void exec_Z3_ast_map_contains(z3_replayer & in) {
  Z3_ast_map_contains(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_map>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
}
void exec_Z3_ast_map_find(z3_replayer & in) {
  Z3_ast result = Z3_ast_map_find(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_map>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
  in.store_result(result);
}
void exec_Z3_ast_map_insert(z3_replayer & in) {
  Z3_ast_map_insert(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_map>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)),
    reinterpret_cast<Z3_ast>(in.get_obj(3)));
}
void exec_Z3_ast_map_erase(z3_replayer & in) {
  Z3_ast_map_erase(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_map>(in.get_obj(1)),
    reinterpret_cast<Z3_ast>(in.get_obj(2)));
}
void exec_Z3_ast_map_size(z3_replayer & in) {
  Z3_ast_map_size(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_map>(in.get_obj(1)));
}
void exec_Z3_ast_map_reset(z3_replayer & in) {
  Z3_ast_map_reset(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_map>(in.get_obj(1)));
}
void exec_Z3_ast_map_keys(z3_replayer & in) {
  Z3_ast_vector result = Z3_ast_map_keys(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_map>(in.get_obj(1)));
  in.store_result(result);
}
void exec_Z3_ast_map_to_string(z3_replayer & in) {
  Z3_ast_map_to_string(
    reinterpret_cast<Z3_context>(in.get_obj(0)),
    reinterpret_cast<Z3_ast_map>(in.get_obj(1)));
}
void register_z3_replayer_cmds(z3_replayer & in) {
  in.register_cmd(0, exec_Z3_mk_config);
  in.register_cmd(1, exec_Z3_del_config);
  in.register_cmd(2, exec_Z3_set_param_value);
  in.register_cmd(3, exec_Z3_mk_context);
  in.register_cmd(4, exec_Z3_mk_context_rc);
  in.register_cmd(5, exec_Z3_set_logic);
  in.register_cmd(6, exec_Z3_del_context);
  in.register_cmd(7, exec_Z3_inc_ref);
  in.register_cmd(8, exec_Z3_dec_ref);
  in.register_cmd(9, exec_Z3_toggle_warning_messages);
  in.register_cmd(10, exec_Z3_update_param_value);
  in.register_cmd(11, exec_Z3_get_param_value);
  in.register_cmd(12, exec_Z3_mk_int_symbol);
  in.register_cmd(13, exec_Z3_mk_string_symbol);
  in.register_cmd(14, exec_Z3_is_eq_sort);
  in.register_cmd(15, exec_Z3_mk_uninterpreted_sort);
  in.register_cmd(16, exec_Z3_mk_bool_sort);
  in.register_cmd(17, exec_Z3_mk_int_sort);
  in.register_cmd(18, exec_Z3_mk_real_sort);
  in.register_cmd(19, exec_Z3_mk_bv_sort);
  in.register_cmd(20, exec_Z3_mk_array_sort);
  in.register_cmd(21, exec_Z3_mk_tuple_sort);
  in.register_cmd(22, exec_Z3_mk_enumeration_sort);
  in.register_cmd(23, exec_Z3_mk_list_sort);
  in.register_cmd(24, exec_Z3_mk_constructor);
  in.register_cmd(25, exec_Z3_query_constructor);
  in.register_cmd(26, exec_Z3_del_constructor);
  in.register_cmd(27, exec_Z3_mk_datatype);
  in.register_cmd(28, exec_Z3_mk_constructor_list);
  in.register_cmd(29, exec_Z3_del_constructor_list);
  in.register_cmd(30, exec_Z3_mk_datatypes);
  in.register_cmd(31, exec_Z3_is_eq_ast);
  in.register_cmd(32, exec_Z3_is_eq_func_decl);
  in.register_cmd(33, exec_Z3_mk_func_decl);
  in.register_cmd(34, exec_Z3_mk_app);
  in.register_cmd(35, exec_Z3_mk_const);
  in.register_cmd(36, exec_Z3_mk_label);
  in.register_cmd(37, exec_Z3_mk_fresh_func_decl);
  in.register_cmd(38, exec_Z3_mk_fresh_const);
  in.register_cmd(39, exec_Z3_mk_true);
  in.register_cmd(40, exec_Z3_mk_false);
  in.register_cmd(41, exec_Z3_mk_eq);
  in.register_cmd(42, exec_Z3_mk_distinct);
  in.register_cmd(43, exec_Z3_mk_not);
  in.register_cmd(44, exec_Z3_mk_ite);
  in.register_cmd(45, exec_Z3_mk_iff);
  in.register_cmd(46, exec_Z3_mk_implies);
  in.register_cmd(47, exec_Z3_mk_xor);
  in.register_cmd(48, exec_Z3_mk_and);
  in.register_cmd(49, exec_Z3_mk_or);
  in.register_cmd(50, exec_Z3_mk_add);
  in.register_cmd(51, exec_Z3_mk_mul);
  in.register_cmd(52, exec_Z3_mk_sub);
  in.register_cmd(53, exec_Z3_mk_unary_minus);
  in.register_cmd(54, exec_Z3_mk_div);
  in.register_cmd(55, exec_Z3_mk_mod);
  in.register_cmd(56, exec_Z3_mk_rem);
  in.register_cmd(57, exec_Z3_mk_power);
  in.register_cmd(58, exec_Z3_is_algebraic_number);
  in.register_cmd(59, exec_Z3_get_algebraic_number_lower);
  in.register_cmd(60, exec_Z3_get_algebraic_number_upper);
  in.register_cmd(61, exec_Z3_mk_lt);
  in.register_cmd(62, exec_Z3_mk_le);
  in.register_cmd(63, exec_Z3_mk_gt);
  in.register_cmd(64, exec_Z3_mk_ge);
  in.register_cmd(65, exec_Z3_mk_int2real);
  in.register_cmd(66, exec_Z3_mk_real2int);
  in.register_cmd(67, exec_Z3_mk_is_int);
  in.register_cmd(68, exec_Z3_mk_bvnot);
  in.register_cmd(69, exec_Z3_mk_bvredand);
  in.register_cmd(70, exec_Z3_mk_bvredor);
  in.register_cmd(71, exec_Z3_mk_bvand);
  in.register_cmd(72, exec_Z3_mk_bvor);
  in.register_cmd(73, exec_Z3_mk_bvxor);
  in.register_cmd(74, exec_Z3_mk_bvnand);
  in.register_cmd(75, exec_Z3_mk_bvnor);
  in.register_cmd(76, exec_Z3_mk_bvxnor);
  in.register_cmd(77, exec_Z3_mk_bvneg);
  in.register_cmd(78, exec_Z3_mk_bvadd);
  in.register_cmd(79, exec_Z3_mk_bvsub);
  in.register_cmd(80, exec_Z3_mk_bvmul);
  in.register_cmd(81, exec_Z3_mk_bvudiv);
  in.register_cmd(82, exec_Z3_mk_bvsdiv);
  in.register_cmd(83, exec_Z3_mk_bvurem);
  in.register_cmd(84, exec_Z3_mk_bvsrem);
  in.register_cmd(85, exec_Z3_mk_bvsmod);
  in.register_cmd(86, exec_Z3_mk_bvult);
  in.register_cmd(87, exec_Z3_mk_bvslt);
  in.register_cmd(88, exec_Z3_mk_bvule);
  in.register_cmd(89, exec_Z3_mk_bvsle);
  in.register_cmd(90, exec_Z3_mk_bvuge);
  in.register_cmd(91, exec_Z3_mk_bvsge);
  in.register_cmd(92, exec_Z3_mk_bvugt);
  in.register_cmd(93, exec_Z3_mk_bvsgt);
  in.register_cmd(94, exec_Z3_mk_concat);
  in.register_cmd(95, exec_Z3_mk_extract);
  in.register_cmd(96, exec_Z3_mk_sign_ext);
  in.register_cmd(97, exec_Z3_mk_zero_ext);
  in.register_cmd(98, exec_Z3_mk_repeat);
  in.register_cmd(99, exec_Z3_mk_bvshl);
  in.register_cmd(100, exec_Z3_mk_bvlshr);
  in.register_cmd(101, exec_Z3_mk_bvashr);
  in.register_cmd(102, exec_Z3_mk_rotate_left);
  in.register_cmd(103, exec_Z3_mk_rotate_right);
  in.register_cmd(104, exec_Z3_mk_ext_rotate_left);
  in.register_cmd(105, exec_Z3_mk_ext_rotate_right);
  in.register_cmd(106, exec_Z3_mk_int2bv);
  in.register_cmd(107, exec_Z3_mk_bv2int);
  in.register_cmd(108, exec_Z3_mk_bvadd_no_overflow);
  in.register_cmd(109, exec_Z3_mk_bvadd_no_underflow);
  in.register_cmd(110, exec_Z3_mk_bvsub_no_overflow);
  in.register_cmd(111, exec_Z3_mk_bvsub_no_underflow);
  in.register_cmd(112, exec_Z3_mk_bvsdiv_no_overflow);
  in.register_cmd(113, exec_Z3_mk_bvneg_no_overflow);
  in.register_cmd(114, exec_Z3_mk_bvmul_no_overflow);
  in.register_cmd(115, exec_Z3_mk_bvmul_no_underflow);
  in.register_cmd(116, exec_Z3_mk_select);
  in.register_cmd(117, exec_Z3_mk_store);
  in.register_cmd(118, exec_Z3_mk_const_array);
  in.register_cmd(119, exec_Z3_mk_map);
  in.register_cmd(120, exec_Z3_mk_array_default);
  in.register_cmd(121, exec_Z3_mk_set_sort);
  in.register_cmd(122, exec_Z3_mk_empty_set);
  in.register_cmd(123, exec_Z3_mk_full_set);
  in.register_cmd(124, exec_Z3_mk_set_add);
  in.register_cmd(125, exec_Z3_mk_set_del);
  in.register_cmd(126, exec_Z3_mk_set_union);
  in.register_cmd(127, exec_Z3_mk_set_intersect);
  in.register_cmd(128, exec_Z3_mk_set_difference);
  in.register_cmd(129, exec_Z3_mk_set_complement);
  in.register_cmd(130, exec_Z3_mk_set_member);
  in.register_cmd(131, exec_Z3_mk_set_subset);
  in.register_cmd(132, exec_Z3_mk_numeral);
  in.register_cmd(133, exec_Z3_mk_real);
  in.register_cmd(134, exec_Z3_mk_int);
  in.register_cmd(135, exec_Z3_mk_unsigned_int);
  in.register_cmd(136, exec_Z3_mk_int64);
  in.register_cmd(137, exec_Z3_mk_unsigned_int64);
  in.register_cmd(138, exec_Z3_mk_pattern);
  in.register_cmd(139, exec_Z3_mk_bound);
  in.register_cmd(140, exec_Z3_mk_forall);
  in.register_cmd(141, exec_Z3_mk_exists);
  in.register_cmd(142, exec_Z3_mk_quantifier);
  in.register_cmd(143, exec_Z3_mk_quantifier_ex);
  in.register_cmd(144, exec_Z3_mk_forall_const);
  in.register_cmd(145, exec_Z3_mk_exists_const);
  in.register_cmd(146, exec_Z3_mk_quantifier_const);
  in.register_cmd(147, exec_Z3_mk_quantifier_const_ex);
  in.register_cmd(148, exec_Z3_get_ast_id);
  in.register_cmd(149, exec_Z3_get_func_decl_id);
  in.register_cmd(150, exec_Z3_get_sort_id);
  in.register_cmd(151, exec_Z3_is_well_sorted);
  in.register_cmd(152, exec_Z3_get_symbol_kind);
  in.register_cmd(153, exec_Z3_get_symbol_int);
  in.register_cmd(154, exec_Z3_get_symbol_string);
  in.register_cmd(155, exec_Z3_get_ast_kind);
  in.register_cmd(156, exec_Z3_get_ast_hash);
  in.register_cmd(157, exec_Z3_get_numeral_string);
  in.register_cmd(158, exec_Z3_get_numeral_decimal_string);
  in.register_cmd(159, exec_Z3_get_numerator);
  in.register_cmd(160, exec_Z3_get_denominator);
  in.register_cmd(161, exec_Z3_get_numeral_small);
  in.register_cmd(162, exec_Z3_get_numeral_int);
  in.register_cmd(163, exec_Z3_get_numeral_uint);
  in.register_cmd(164, exec_Z3_get_numeral_uint64);
  in.register_cmd(165, exec_Z3_get_numeral_int64);
  in.register_cmd(166, exec_Z3_get_numeral_rational_int64);
  in.register_cmd(167, exec_Z3_get_bool_value);
  in.register_cmd(168, exec_Z3_get_app_decl);
  in.register_cmd(169, exec_Z3_get_app_num_args);
  in.register_cmd(170, exec_Z3_get_app_arg);
  in.register_cmd(171, exec_Z3_get_index_value);
  in.register_cmd(172, exec_Z3_is_quantifier_forall);
  in.register_cmd(173, exec_Z3_get_quantifier_weight);
  in.register_cmd(174, exec_Z3_get_quantifier_num_patterns);
  in.register_cmd(175, exec_Z3_get_quantifier_pattern_ast);
  in.register_cmd(176, exec_Z3_get_quantifier_num_no_patterns);
  in.register_cmd(177, exec_Z3_get_quantifier_no_pattern_ast);
  in.register_cmd(178, exec_Z3_get_quantifier_bound_name);
  in.register_cmd(179, exec_Z3_get_quantifier_bound_sort);
  in.register_cmd(180, exec_Z3_get_quantifier_body);
  in.register_cmd(181, exec_Z3_get_quantifier_num_bound);
  in.register_cmd(182, exec_Z3_get_decl_name);
  in.register_cmd(183, exec_Z3_get_decl_num_parameters);
  in.register_cmd(184, exec_Z3_get_decl_parameter_kind);
  in.register_cmd(185, exec_Z3_get_decl_int_parameter);
  in.register_cmd(186, exec_Z3_get_decl_double_parameter);
  in.register_cmd(187, exec_Z3_get_decl_symbol_parameter);
  in.register_cmd(188, exec_Z3_get_decl_sort_parameter);
  in.register_cmd(189, exec_Z3_get_decl_ast_parameter);
  in.register_cmd(190, exec_Z3_get_decl_func_decl_parameter);
  in.register_cmd(191, exec_Z3_get_decl_rational_parameter);
  in.register_cmd(192, exec_Z3_get_sort_name);
  in.register_cmd(193, exec_Z3_get_sort);
  in.register_cmd(194, exec_Z3_get_domain_size);
  in.register_cmd(195, exec_Z3_get_domain);
  in.register_cmd(196, exec_Z3_get_range);
  in.register_cmd(197, exec_Z3_get_sort_kind);
  in.register_cmd(198, exec_Z3_get_bv_sort_size);
  in.register_cmd(199, exec_Z3_get_array_sort_domain);
  in.register_cmd(200, exec_Z3_get_array_sort_range);
  in.register_cmd(201, exec_Z3_get_tuple_sort_mk_decl);
  in.register_cmd(202, exec_Z3_get_decl_kind);
  in.register_cmd(203, exec_Z3_get_tuple_sort_num_fields);
  in.register_cmd(204, exec_Z3_get_tuple_sort_field_decl);
  in.register_cmd(205, exec_Z3_get_datatype_sort_num_constructors);
  in.register_cmd(206, exec_Z3_get_datatype_sort_constructor);
  in.register_cmd(207, exec_Z3_get_datatype_sort_recognizer);
  in.register_cmd(208, exec_Z3_get_datatype_sort_constructor_accessor);
  in.register_cmd(209, exec_Z3_get_relation_arity);
  in.register_cmd(210, exec_Z3_get_relation_column);
  in.register_cmd(211, exec_Z3_get_finite_domain_sort_size);
  in.register_cmd(212, exec_Z3_mk_finite_domain_sort);
  in.register_cmd(213, exec_Z3_get_pattern_num_terms);
  in.register_cmd(214, exec_Z3_get_pattern);
  in.register_cmd(215, exec_Z3_simplify);
  in.register_cmd(216, exec_Z3_simplify_ex);
  in.register_cmd(217, exec_Z3_simplify_get_help);
  in.register_cmd(218, exec_Z3_simplify_get_param_descrs);
  in.register_cmd(219, exec_Z3_update_term);
  in.register_cmd(220, exec_Z3_substitute);
  in.register_cmd(221, exec_Z3_substitute_vars);
  in.register_cmd(222, exec_Z3_sort_to_ast);
  in.register_cmd(223, exec_Z3_func_decl_to_ast);
  in.register_cmd(224, exec_Z3_pattern_to_ast);
  in.register_cmd(225, exec_Z3_app_to_ast);
  in.register_cmd(226, exec_Z3_to_app);
  in.register_cmd(227, exec_Z3_to_func_decl);
  in.register_cmd(228, exec_Z3_push);
  in.register_cmd(229, exec_Z3_pop);
  in.register_cmd(230, exec_Z3_get_num_scopes);
  in.register_cmd(231, exec_Z3_persist_ast);
  in.register_cmd(232, exec_Z3_assert_cnstr);
  in.register_cmd(233, exec_Z3_check_and_get_model);
  in.register_cmd(234, exec_Z3_check);
  in.register_cmd(235, exec_Z3_check_assumptions);
  in.register_cmd(236, exec_Z3_get_implied_equalities);
  in.register_cmd(237, exec_Z3_del_model);
  in.register_cmd(238, exec_Z3_soft_check_cancel);
  in.register_cmd(239, exec_Z3_get_search_failure);
  in.register_cmd(240, exec_Z3_get_relevant_labels);
  in.register_cmd(241, exec_Z3_get_relevant_literals);
  in.register_cmd(242, exec_Z3_get_guessed_literals);
  in.register_cmd(243, exec_Z3_del_literals);
  in.register_cmd(244, exec_Z3_get_num_literals);
  in.register_cmd(245, exec_Z3_get_label_symbol);
  in.register_cmd(246, exec_Z3_get_literal);
  in.register_cmd(247, exec_Z3_disable_literal);
  in.register_cmd(248, exec_Z3_block_literals);
  in.register_cmd(249, exec_Z3_model_inc_ref);
  in.register_cmd(250, exec_Z3_model_dec_ref);
  in.register_cmd(251, exec_Z3_model_get_const_interp);
  in.register_cmd(252, exec_Z3_model_get_func_interp);
  in.register_cmd(253, exec_Z3_model_get_num_consts);
  in.register_cmd(254, exec_Z3_model_get_const_decl);
  in.register_cmd(255, exec_Z3_model_get_num_funcs);
  in.register_cmd(256, exec_Z3_model_get_func_decl);
  in.register_cmd(257, exec_Z3_model_eval);
  in.register_cmd(258, exec_Z3_model_get_num_sorts);
  in.register_cmd(259, exec_Z3_model_get_sort);
  in.register_cmd(260, exec_Z3_model_get_sort_universe);
  in.register_cmd(261, exec_Z3_is_as_array);
  in.register_cmd(262, exec_Z3_get_as_array_func_decl);
  in.register_cmd(263, exec_Z3_func_interp_inc_ref);
  in.register_cmd(264, exec_Z3_func_interp_dec_ref);
  in.register_cmd(265, exec_Z3_func_interp_get_num_entries);
  in.register_cmd(266, exec_Z3_func_interp_get_entry);
  in.register_cmd(267, exec_Z3_func_interp_get_else);
  in.register_cmd(268, exec_Z3_func_interp_get_arity);
  in.register_cmd(269, exec_Z3_func_entry_inc_ref);
  in.register_cmd(270, exec_Z3_func_entry_dec_ref);
  in.register_cmd(271, exec_Z3_func_entry_get_value);
  in.register_cmd(272, exec_Z3_func_entry_get_num_args);
  in.register_cmd(273, exec_Z3_func_entry_get_arg);
  in.register_cmd(274, exec_Z3_get_model_num_constants);
  in.register_cmd(275, exec_Z3_get_model_constant);
  in.register_cmd(276, exec_Z3_eval_func_decl);
  in.register_cmd(277, exec_Z3_is_array_value);
  in.register_cmd(278, exec_Z3_get_array_value);
  in.register_cmd(279, exec_Z3_get_model_num_funcs);
  in.register_cmd(280, exec_Z3_get_model_func_decl);
  in.register_cmd(281, exec_Z3_get_model_func_else);
  in.register_cmd(282, exec_Z3_get_model_func_num_entries);
  in.register_cmd(283, exec_Z3_get_model_func_entry_num_args);
  in.register_cmd(284, exec_Z3_get_model_func_entry_arg);
  in.register_cmd(285, exec_Z3_get_model_func_entry_value);
  in.register_cmd(286, exec_Z3_eval);
  in.register_cmd(287, exec_Z3_eval_decl);
  in.register_cmd(288, exec_Z3_set_ast_print_mode);
  in.register_cmd(289, exec_Z3_ast_to_string);
  in.register_cmd(290, exec_Z3_pattern_to_string);
  in.register_cmd(291, exec_Z3_sort_to_string);
  in.register_cmd(292, exec_Z3_func_decl_to_string);
  in.register_cmd(293, exec_Z3_model_to_string);
  in.register_cmd(294, exec_Z3_benchmark_to_smtlib_string);
  in.register_cmd(295, exec_Z3_context_to_string);
  in.register_cmd(296, exec_Z3_statistics_to_string);
  in.register_cmd(297, exec_Z3_get_context_assignment);
  in.register_cmd(298, exec_Z3_parse_smtlib_string);
  in.register_cmd(299, exec_Z3_parse_smtlib_file);
  in.register_cmd(300, exec_Z3_get_smtlib_num_formulas);
  in.register_cmd(301, exec_Z3_get_smtlib_formula);
  in.register_cmd(302, exec_Z3_get_smtlib_num_assumptions);
  in.register_cmd(303, exec_Z3_get_smtlib_assumption);
  in.register_cmd(304, exec_Z3_get_smtlib_num_decls);
  in.register_cmd(305, exec_Z3_get_smtlib_decl);
  in.register_cmd(306, exec_Z3_get_smtlib_num_sorts);
  in.register_cmd(307, exec_Z3_get_smtlib_sort);
  in.register_cmd(308, exec_Z3_get_smtlib_error);
  in.register_cmd(309, exec_Z3_parse_z3_string);
  in.register_cmd(310, exec_Z3_parse_z3_file);
  in.register_cmd(311, exec_Z3_parse_smtlib2_string);
  in.register_cmd(312, exec_Z3_parse_smtlib2_file);
  in.register_cmd(313, exec_Z3_get_error_code);
  in.register_cmd(314, exec_Z3_set_error);
  in.register_cmd(315, exec_Z3_get_error_msg);
  in.register_cmd(316, exec_Z3_get_version);
  in.register_cmd(317, exec_Z3_reset_memory);
  in.register_cmd(318, exec_Z3_is_app);
  in.register_cmd(319, exec_Z3_is_numeral_ast);
  in.register_cmd(320, exec_Z3_get_arity);
  in.register_cmd(321, exec_Z3_mk_injective_function);
  in.register_cmd(322, exec_Z3_mk_fixedpoint);
  in.register_cmd(323, exec_Z3_fixedpoint_inc_ref);
  in.register_cmd(324, exec_Z3_fixedpoint_dec_ref);
  in.register_cmd(325, exec_Z3_fixedpoint_push);
  in.register_cmd(326, exec_Z3_fixedpoint_pop);
  in.register_cmd(327, exec_Z3_fixedpoint_register_relation);
  in.register_cmd(328, exec_Z3_fixedpoint_assert);
  in.register_cmd(329, exec_Z3_fixedpoint_add_rule);
  in.register_cmd(330, exec_Z3_fixedpoint_add_fact);
  in.register_cmd(331, exec_Z3_fixedpoint_query);
  in.register_cmd(332, exec_Z3_fixedpoint_query_relations);
  in.register_cmd(333, exec_Z3_fixedpoint_get_answer);
  in.register_cmd(334, exec_Z3_fixedpoint_update_rule);
  in.register_cmd(335, exec_Z3_fixedpoint_get_num_levels);
  in.register_cmd(336, exec_Z3_fixedpoint_get_cover_delta);
  in.register_cmd(337, exec_Z3_fixedpoint_add_cover);
  in.register_cmd(338, exec_Z3_fixedpoint_get_statistics);
  in.register_cmd(339, exec_Z3_fixedpoint_get_help);
  in.register_cmd(340, exec_Z3_fixedpoint_get_param_descrs);
  in.register_cmd(341, exec_Z3_fixedpoint_set_params);
  in.register_cmd(342, exec_Z3_fixedpoint_to_string);
  in.register_cmd(343, exec_Z3_fixedpoint_get_reason_unknown);
  in.register_cmd(344, exec_Z3_fixedpoint_set_predicate_representation);
  in.register_cmd(345, exec_Z3_fixedpoint_simplify_rules);
  in.register_cmd(346, exec_Z3_mk_params);
  in.register_cmd(347, exec_Z3_params_inc_ref);
  in.register_cmd(348, exec_Z3_params_dec_ref);
  in.register_cmd(349, exec_Z3_params_set_bool);
  in.register_cmd(350, exec_Z3_params_set_uint);
  in.register_cmd(351, exec_Z3_params_set_double);
  in.register_cmd(352, exec_Z3_params_set_symbol);
  in.register_cmd(353, exec_Z3_params_to_string);
  in.register_cmd(354, exec_Z3_params_validate);
  in.register_cmd(355, exec_Z3_param_descrs_inc_ref);
  in.register_cmd(356, exec_Z3_param_descrs_dec_ref);
  in.register_cmd(357, exec_Z3_param_descrs_get_kind);
  in.register_cmd(358, exec_Z3_param_descrs_size);
  in.register_cmd(359, exec_Z3_param_descrs_get_name);
  in.register_cmd(360, exec_Z3_interrupt);
  in.register_cmd(361, exec_Z3_get_error_msg_ex);
  in.register_cmd(362, exec_Z3_translate);
  in.register_cmd(363, exec_Z3_mk_goal);
  in.register_cmd(364, exec_Z3_goal_inc_ref);
  in.register_cmd(365, exec_Z3_goal_dec_ref);
  in.register_cmd(366, exec_Z3_goal_precision);
  in.register_cmd(367, exec_Z3_goal_assert);
  in.register_cmd(368, exec_Z3_goal_inconsistent);
  in.register_cmd(369, exec_Z3_goal_depth);
  in.register_cmd(370, exec_Z3_goal_reset);
  in.register_cmd(371, exec_Z3_goal_size);
  in.register_cmd(372, exec_Z3_goal_formula);
  in.register_cmd(373, exec_Z3_goal_num_exprs);
  in.register_cmd(374, exec_Z3_goal_is_decided_sat);
  in.register_cmd(375, exec_Z3_goal_is_decided_unsat);
  in.register_cmd(376, exec_Z3_goal_translate);
  in.register_cmd(377, exec_Z3_goal_to_string);
  in.register_cmd(378, exec_Z3_mk_tactic);
  in.register_cmd(379, exec_Z3_mk_probe);
  in.register_cmd(380, exec_Z3_tactic_inc_ref);
  in.register_cmd(381, exec_Z3_tactic_dec_ref);
  in.register_cmd(382, exec_Z3_probe_inc_ref);
  in.register_cmd(383, exec_Z3_probe_dec_ref);
  in.register_cmd(384, exec_Z3_tactic_and_then);
  in.register_cmd(385, exec_Z3_tactic_or_else);
  in.register_cmd(386, exec_Z3_tactic_par_or);
  in.register_cmd(387, exec_Z3_tactic_par_and_then);
  in.register_cmd(388, exec_Z3_tactic_try_for);
  in.register_cmd(389, exec_Z3_tactic_when);
  in.register_cmd(390, exec_Z3_tactic_cond);
  in.register_cmd(391, exec_Z3_tactic_repeat);
  in.register_cmd(392, exec_Z3_tactic_skip);
  in.register_cmd(393, exec_Z3_tactic_fail);
  in.register_cmd(394, exec_Z3_tactic_fail_if);
  in.register_cmd(395, exec_Z3_tactic_fail_if_not_decided);
  in.register_cmd(396, exec_Z3_tactic_using_params);
  in.register_cmd(397, exec_Z3_probe_const);
  in.register_cmd(398, exec_Z3_probe_lt);
  in.register_cmd(399, exec_Z3_probe_le);
  in.register_cmd(400, exec_Z3_probe_gt);
  in.register_cmd(401, exec_Z3_probe_ge);
  in.register_cmd(402, exec_Z3_probe_eq);
  in.register_cmd(403, exec_Z3_probe_and);
  in.register_cmd(404, exec_Z3_probe_or);
  in.register_cmd(405, exec_Z3_probe_not);
  in.register_cmd(406, exec_Z3_get_num_tactics);
  in.register_cmd(407, exec_Z3_get_tactic_name);
  in.register_cmd(408, exec_Z3_get_num_probes);
  in.register_cmd(409, exec_Z3_get_probe_name);
  in.register_cmd(410, exec_Z3_tactic_get_help);
  in.register_cmd(411, exec_Z3_tactic_get_param_descrs);
  in.register_cmd(412, exec_Z3_tactic_get_descr);
  in.register_cmd(413, exec_Z3_probe_get_descr);
  in.register_cmd(414, exec_Z3_probe_apply);
  in.register_cmd(415, exec_Z3_tactic_apply);
  in.register_cmd(416, exec_Z3_tactic_apply_ex);
  in.register_cmd(417, exec_Z3_apply_result_inc_ref);
  in.register_cmd(418, exec_Z3_apply_result_dec_ref);
  in.register_cmd(419, exec_Z3_apply_result_to_string);
  in.register_cmd(420, exec_Z3_apply_result_get_num_subgoals);
  in.register_cmd(421, exec_Z3_apply_result_get_subgoal);
  in.register_cmd(422, exec_Z3_apply_result_convert_model);
  in.register_cmd(423, exec_Z3_mk_solver);
  in.register_cmd(424, exec_Z3_mk_simple_solver);
  in.register_cmd(425, exec_Z3_mk_solver_for_logic);
  in.register_cmd(426, exec_Z3_mk_solver_from_tactic);
  in.register_cmd(427, exec_Z3_solver_get_help);
  in.register_cmd(428, exec_Z3_solver_get_param_descrs);
  in.register_cmd(429, exec_Z3_solver_set_params);
  in.register_cmd(430, exec_Z3_solver_inc_ref);
  in.register_cmd(431, exec_Z3_solver_dec_ref);
  in.register_cmd(432, exec_Z3_solver_push);
  in.register_cmd(433, exec_Z3_solver_pop);
  in.register_cmd(434, exec_Z3_solver_reset);
  in.register_cmd(435, exec_Z3_solver_get_num_scopes);
  in.register_cmd(436, exec_Z3_solver_assert);
  in.register_cmd(437, exec_Z3_solver_get_assertions);
  in.register_cmd(438, exec_Z3_solver_check);
  in.register_cmd(439, exec_Z3_solver_check_assumptions);
  in.register_cmd(440, exec_Z3_solver_get_model);
  in.register_cmd(441, exec_Z3_solver_get_proof);
  in.register_cmd(442, exec_Z3_solver_get_unsat_core);
  in.register_cmd(443, exec_Z3_solver_get_reason_unknown);
  in.register_cmd(444, exec_Z3_solver_get_statistics);
  in.register_cmd(445, exec_Z3_solver_to_string);
  in.register_cmd(446, exec_Z3_stats_to_string);
  in.register_cmd(447, exec_Z3_stats_inc_ref);
  in.register_cmd(448, exec_Z3_stats_dec_ref);
  in.register_cmd(449, exec_Z3_stats_size);
  in.register_cmd(450, exec_Z3_stats_get_key);
  in.register_cmd(451, exec_Z3_stats_is_uint);
  in.register_cmd(452, exec_Z3_stats_is_double);
  in.register_cmd(453, exec_Z3_stats_get_uint_value);
  in.register_cmd(454, exec_Z3_stats_get_double_value);
  in.register_cmd(455, exec_Z3_mk_ast_vector);
  in.register_cmd(456, exec_Z3_ast_vector_inc_ref);
  in.register_cmd(457, exec_Z3_ast_vector_dec_ref);
  in.register_cmd(458, exec_Z3_ast_vector_size);
  in.register_cmd(459, exec_Z3_ast_vector_get);
  in.register_cmd(460, exec_Z3_ast_vector_set);
  in.register_cmd(461, exec_Z3_ast_vector_resize);
  in.register_cmd(462, exec_Z3_ast_vector_push);
  in.register_cmd(463, exec_Z3_ast_vector_translate);
  in.register_cmd(464, exec_Z3_ast_vector_to_string);
  in.register_cmd(465, exec_Z3_mk_ast_map);
  in.register_cmd(466, exec_Z3_ast_map_inc_ref);
  in.register_cmd(467, exec_Z3_ast_map_dec_ref);
  in.register_cmd(468, exec_Z3_ast_map_contains);
  in.register_cmd(469, exec_Z3_ast_map_find);
  in.register_cmd(470, exec_Z3_ast_map_insert);
  in.register_cmd(471, exec_Z3_ast_map_erase);
  in.register_cmd(472, exec_Z3_ast_map_size);
  in.register_cmd(473, exec_Z3_ast_map_reset);
  in.register_cmd(474, exec_Z3_ast_map_keys);
  in.register_cmd(475, exec_Z3_ast_map_to_string);
}
