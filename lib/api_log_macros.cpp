// Automatically generated file, generator: api.py
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"z3_logger.h"
void log_Z3_mk_config() {
  R();
  C(0);
}
void log_Z3_del_config(Z3_config a0) {
  R();
  P(a0);
  C(1);
}
void log_Z3_set_param_value(Z3_config a0, Z3_string a1, Z3_string a2) {
  R();
  P(a0);
  S(a1);
  S(a2);
  C(2);
}
void log_Z3_mk_context(Z3_config a0) {
  R();
  P(a0);
  C(3);
}
void log_Z3_mk_context_rc(Z3_config a0) {
  R();
  P(a0);
  C(4);
}
void log_Z3_set_logic(Z3_context a0, Z3_string a1) {
  R();
  P(a0);
  S(a1);
  C(5);
}
void log_Z3_del_context(Z3_context a0) {
  R();
  P(a0);
  C(6);
}
void log_Z3_inc_ref(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(7);
}
void log_Z3_dec_ref(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(8);
}
void log_Z3_toggle_warning_messages(Z3_bool a0) {
  R();
  I(a0);
  C(9);
}
void log_Z3_update_param_value(Z3_context a0, Z3_string a1, Z3_string a2) {
  R();
  P(a0);
  S(a1);
  S(a2);
  C(10);
}
void log_Z3_get_param_value(Z3_context a0, Z3_string a1, Z3_string* a2) {
  R();
  P(a0);
  S(a1);
  S("");
  C(11);
}
void log_Z3_mk_int_symbol(Z3_context a0, int a1) {
  R();
  P(a0);
  I(a1);
  C(12);
}
void log_Z3_mk_string_symbol(Z3_context a0, Z3_string a1) {
  R();
  P(a0);
  S(a1);
  C(13);
}
void log_Z3_is_eq_sort(Z3_context a0, Z3_sort a1, Z3_sort a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(14);
}
void log_Z3_mk_uninterpreted_sort(Z3_context a0, Z3_symbol a1) {
  R();
  P(a0);
  Sy(a1);
  C(15);
}
void log_Z3_mk_bool_sort(Z3_context a0) {
  R();
  P(a0);
  C(16);
}
void log_Z3_mk_int_sort(Z3_context a0) {
  R();
  P(a0);
  C(17);
}
void log_Z3_mk_real_sort(Z3_context a0) {
  R();
  P(a0);
  C(18);
}
void log_Z3_mk_bv_sort(Z3_context a0, unsigned a1) {
  R();
  P(a0);
  U(a1);
  C(19);
}
void log_Z3_mk_array_sort(Z3_context a0, Z3_sort a1, Z3_sort a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(20);
}
void log_Z3_mk_tuple_sort(Z3_context a0, Z3_symbol a1, unsigned a2, Z3_symbol const * a3, Z3_sort const * a4, Z3_func_decl* a5, Z3_func_decl* a6) {
  R();
  P(a0);
  Sy(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { Sy(a3[i]); }
  Asy(a2);
  for (unsigned i = 0; i < a2; i++) { P(a4[i]); }
  Ap(a2);
  P(0);
  for (unsigned i = 0; i < a2; i++) { P(0); }
  Ap(a2);
  C(21);
}
void log_Z3_mk_enumeration_sort(Z3_context a0, Z3_symbol a1, unsigned a2, Z3_symbol const * a3, Z3_func_decl* a4, Z3_func_decl* a5) {
  R();
  P(a0);
  Sy(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { Sy(a3[i]); }
  Asy(a2);
  for (unsigned i = 0; i < a2; i++) { P(0); }
  Ap(a2);
  for (unsigned i = 0; i < a2; i++) { P(0); }
  Ap(a2);
  C(22);
}
void log_Z3_mk_list_sort(Z3_context a0, Z3_symbol a1, Z3_sort a2, Z3_func_decl* a3, Z3_func_decl* a4, Z3_func_decl* a5, Z3_func_decl* a6, Z3_func_decl* a7, Z3_func_decl* a8) {
  R();
  P(a0);
  Sy(a1);
  P(a2);
  P(0);
  P(0);
  P(0);
  P(0);
  P(0);
  P(0);
  C(23);
}
void log_Z3_mk_constructor(Z3_context a0, Z3_symbol a1, Z3_symbol a2, unsigned a3, Z3_symbol const * a4, Z3_sort const * a5, unsigned const * a6) {
  R();
  P(a0);
  Sy(a1);
  Sy(a2);
  U(a3);
  for (unsigned i = 0; i < a3; i++) { Sy(a4[i]); }
  Asy(a3);
  for (unsigned i = 0; i < a3; i++) { P(a5[i]); }
  Ap(a3);
  for (unsigned i = 0; i < a3; i++) { U(a6[i]); }
  Au(a3);
  C(24);
}
void log_Z3_query_constructor(Z3_context a0, Z3_constructor a1, unsigned a2, Z3_func_decl* a3, Z3_func_decl* a4, Z3_func_decl* a5) {
  R();
  P(a0);
  P(a1);
  U(a2);
  P(0);
  P(0);
  for (unsigned i = 0; i < a2; i++) { P(0); }
  Ap(a2);
  C(25);
}
void log_Z3_del_constructor(Z3_context a0, Z3_constructor a1) {
  R();
  P(a0);
  P(a1);
  C(26);
}
void log_Z3_mk_datatype(Z3_context a0, Z3_symbol a1, unsigned a2, Z3_constructor* a3) {
  R();
  P(a0);
  Sy(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  C(27);
}
void log_Z3_mk_constructor_list(Z3_context a0, unsigned a1, Z3_constructor const * a2) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { P(a2[i]); }
  Ap(a1);
  C(28);
}
void log_Z3_del_constructor_list(Z3_context a0, Z3_constructor_list a1) {
  R();
  P(a0);
  P(a1);
  C(29);
}
void log_Z3_mk_datatypes(Z3_context a0, unsigned a1, Z3_symbol const * a2, Z3_sort* a3, Z3_constructor_list* a4) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { Sy(a2[i]); }
  Asy(a1);
  for (unsigned i = 0; i < a1; i++) { P(0); }
  Ap(a1);
  for (unsigned i = 0; i < a1; i++) { P(a4[i]); }
  Ap(a1);
  C(30);
}
void log_Z3_is_eq_ast(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(31);
}
void log_Z3_is_eq_func_decl(Z3_context a0, Z3_func_decl a1, Z3_func_decl a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(32);
}
void log_Z3_mk_func_decl(Z3_context a0, Z3_symbol a1, unsigned a2, Z3_sort const * a3, Z3_sort a4) {
  R();
  P(a0);
  Sy(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  P(a4);
  C(33);
}
void log_Z3_mk_app(Z3_context a0, Z3_func_decl a1, unsigned a2, Z3_ast const * a3) {
  R();
  P(a0);
  P(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  C(34);
}
void log_Z3_mk_const(Z3_context a0, Z3_symbol a1, Z3_sort a2) {
  R();
  P(a0);
  Sy(a1);
  P(a2);
  C(35);
}
void log_Z3_mk_label(Z3_context a0, Z3_symbol a1, Z3_bool a2, Z3_ast a3) {
  R();
  P(a0);
  Sy(a1);
  I(a2);
  P(a3);
  C(36);
}
void log_Z3_mk_fresh_func_decl(Z3_context a0, Z3_string a1, unsigned a2, Z3_sort const * a3, Z3_sort a4) {
  R();
  P(a0);
  S(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  P(a4);
  C(37);
}
void log_Z3_mk_fresh_const(Z3_context a0, Z3_string a1, Z3_sort a2) {
  R();
  P(a0);
  S(a1);
  P(a2);
  C(38);
}
void log_Z3_mk_true(Z3_context a0) {
  R();
  P(a0);
  C(39);
}
void log_Z3_mk_false(Z3_context a0) {
  R();
  P(a0);
  C(40);
}
void log_Z3_mk_eq(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(41);
}
void log_Z3_mk_distinct(Z3_context a0, unsigned a1, Z3_ast const * a2) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { P(a2[i]); }
  Ap(a1);
  C(42);
}
void log_Z3_mk_not(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(43);
}
void log_Z3_mk_ite(Z3_context a0, Z3_ast a1, Z3_ast a2, Z3_ast a3) {
  R();
  P(a0);
  P(a1);
  P(a2);
  P(a3);
  C(44);
}
void log_Z3_mk_iff(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(45);
}
void log_Z3_mk_implies(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(46);
}
void log_Z3_mk_xor(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(47);
}
void log_Z3_mk_and(Z3_context a0, unsigned a1, Z3_ast const * a2) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { P(a2[i]); }
  Ap(a1);
  C(48);
}
void log_Z3_mk_or(Z3_context a0, unsigned a1, Z3_ast const * a2) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { P(a2[i]); }
  Ap(a1);
  C(49);
}
void log_Z3_mk_add(Z3_context a0, unsigned a1, Z3_ast const * a2) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { P(a2[i]); }
  Ap(a1);
  C(50);
}
void log_Z3_mk_mul(Z3_context a0, unsigned a1, Z3_ast const * a2) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { P(a2[i]); }
  Ap(a1);
  C(51);
}
void log_Z3_mk_sub(Z3_context a0, unsigned a1, Z3_ast const * a2) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { P(a2[i]); }
  Ap(a1);
  C(52);
}
void log_Z3_mk_unary_minus(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(53);
}
void log_Z3_mk_div(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(54);
}
void log_Z3_mk_mod(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(55);
}
void log_Z3_mk_rem(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(56);
}
void log_Z3_mk_power(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(57);
}
void log_Z3_is_algebraic_number(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(58);
}
void log_Z3_get_algebraic_number_lower(Z3_context a0, Z3_ast a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(59);
}
void log_Z3_get_algebraic_number_upper(Z3_context a0, Z3_ast a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(60);
}
void log_Z3_mk_lt(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(61);
}
void log_Z3_mk_le(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(62);
}
void log_Z3_mk_gt(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(63);
}
void log_Z3_mk_ge(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(64);
}
void log_Z3_mk_int2real(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(65);
}
void log_Z3_mk_real2int(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(66);
}
void log_Z3_mk_is_int(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(67);
}
void log_Z3_mk_bvnot(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(68);
}
void log_Z3_mk_bvredand(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(69);
}
void log_Z3_mk_bvredor(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(70);
}
void log_Z3_mk_bvand(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(71);
}
void log_Z3_mk_bvor(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(72);
}
void log_Z3_mk_bvxor(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(73);
}
void log_Z3_mk_bvnand(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(74);
}
void log_Z3_mk_bvnor(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(75);
}
void log_Z3_mk_bvxnor(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(76);
}
void log_Z3_mk_bvneg(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(77);
}
void log_Z3_mk_bvadd(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(78);
}
void log_Z3_mk_bvsub(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(79);
}
void log_Z3_mk_bvmul(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(80);
}
void log_Z3_mk_bvudiv(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(81);
}
void log_Z3_mk_bvsdiv(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(82);
}
void log_Z3_mk_bvurem(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(83);
}
void log_Z3_mk_bvsrem(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(84);
}
void log_Z3_mk_bvsmod(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(85);
}
void log_Z3_mk_bvult(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(86);
}
void log_Z3_mk_bvslt(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(87);
}
void log_Z3_mk_bvule(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(88);
}
void log_Z3_mk_bvsle(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(89);
}
void log_Z3_mk_bvuge(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(90);
}
void log_Z3_mk_bvsge(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(91);
}
void log_Z3_mk_bvugt(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(92);
}
void log_Z3_mk_bvsgt(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(93);
}
void log_Z3_mk_concat(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(94);
}
void log_Z3_mk_extract(Z3_context a0, unsigned a1, unsigned a2, Z3_ast a3) {
  R();
  P(a0);
  U(a1);
  U(a2);
  P(a3);
  C(95);
}
void log_Z3_mk_sign_ext(Z3_context a0, unsigned a1, Z3_ast a2) {
  R();
  P(a0);
  U(a1);
  P(a2);
  C(96);
}
void log_Z3_mk_zero_ext(Z3_context a0, unsigned a1, Z3_ast a2) {
  R();
  P(a0);
  U(a1);
  P(a2);
  C(97);
}
void log_Z3_mk_repeat(Z3_context a0, unsigned a1, Z3_ast a2) {
  R();
  P(a0);
  U(a1);
  P(a2);
  C(98);
}
void log_Z3_mk_bvshl(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(99);
}
void log_Z3_mk_bvlshr(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(100);
}
void log_Z3_mk_bvashr(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(101);
}
void log_Z3_mk_rotate_left(Z3_context a0, unsigned a1, Z3_ast a2) {
  R();
  P(a0);
  U(a1);
  P(a2);
  C(102);
}
void log_Z3_mk_rotate_right(Z3_context a0, unsigned a1, Z3_ast a2) {
  R();
  P(a0);
  U(a1);
  P(a2);
  C(103);
}
void log_Z3_mk_ext_rotate_left(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(104);
}
void log_Z3_mk_ext_rotate_right(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(105);
}
void log_Z3_mk_int2bv(Z3_context a0, unsigned a1, Z3_ast a2) {
  R();
  P(a0);
  U(a1);
  P(a2);
  C(106);
}
void log_Z3_mk_bv2int(Z3_context a0, Z3_ast a1, Z3_bool a2) {
  R();
  P(a0);
  P(a1);
  I(a2);
  C(107);
}
void log_Z3_mk_bvadd_no_overflow(Z3_context a0, Z3_ast a1, Z3_ast a2, Z3_bool a3) {
  R();
  P(a0);
  P(a1);
  P(a2);
  I(a3);
  C(108);
}
void log_Z3_mk_bvadd_no_underflow(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(109);
}
void log_Z3_mk_bvsub_no_overflow(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(110);
}
void log_Z3_mk_bvsub_no_underflow(Z3_context a0, Z3_ast a1, Z3_ast a2, Z3_bool a3) {
  R();
  P(a0);
  P(a1);
  P(a2);
  I(a3);
  C(111);
}
void log_Z3_mk_bvsdiv_no_overflow(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(112);
}
void log_Z3_mk_bvneg_no_overflow(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(113);
}
void log_Z3_mk_bvmul_no_overflow(Z3_context a0, Z3_ast a1, Z3_ast a2, Z3_bool a3) {
  R();
  P(a0);
  P(a1);
  P(a2);
  I(a3);
  C(114);
}
void log_Z3_mk_bvmul_no_underflow(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(115);
}
void log_Z3_mk_select(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(116);
}
void log_Z3_mk_store(Z3_context a0, Z3_ast a1, Z3_ast a2, Z3_ast a3) {
  R();
  P(a0);
  P(a1);
  P(a2);
  P(a3);
  C(117);
}
void log_Z3_mk_const_array(Z3_context a0, Z3_sort a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(118);
}
void log_Z3_mk_map(Z3_context a0, Z3_func_decl a1, unsigned a2, Z3_ast const * a3) {
  R();
  P(a0);
  P(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  C(119);
}
void log_Z3_mk_array_default(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(120);
}
void log_Z3_mk_set_sort(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(121);
}
void log_Z3_mk_empty_set(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(122);
}
void log_Z3_mk_full_set(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(123);
}
void log_Z3_mk_set_add(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(124);
}
void log_Z3_mk_set_del(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(125);
}
void log_Z3_mk_set_union(Z3_context a0, unsigned a1, Z3_ast const * a2) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { P(a2[i]); }
  Ap(a1);
  C(126);
}
void log_Z3_mk_set_intersect(Z3_context a0, unsigned a1, Z3_ast const * a2) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { P(a2[i]); }
  Ap(a1);
  C(127);
}
void log_Z3_mk_set_difference(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(128);
}
void log_Z3_mk_set_complement(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(129);
}
void log_Z3_mk_set_member(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(130);
}
void log_Z3_mk_set_subset(Z3_context a0, Z3_ast a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(131);
}
void log_Z3_mk_numeral(Z3_context a0, Z3_string a1, Z3_sort a2) {
  R();
  P(a0);
  S(a1);
  P(a2);
  C(132);
}
void log_Z3_mk_real(Z3_context a0, int a1, int a2) {
  R();
  P(a0);
  I(a1);
  I(a2);
  C(133);
}
void log_Z3_mk_int(Z3_context a0, int a1, Z3_sort a2) {
  R();
  P(a0);
  I(a1);
  P(a2);
  C(134);
}
void log_Z3_mk_unsigned_int(Z3_context a0, unsigned a1, Z3_sort a2) {
  R();
  P(a0);
  U(a1);
  P(a2);
  C(135);
}
void log_Z3_mk_int64(Z3_context a0, __int64 a1, Z3_sort a2) {
  R();
  P(a0);
  I(a1);
  P(a2);
  C(136);
}
void log_Z3_mk_unsigned_int64(Z3_context a0, __uint64 a1, Z3_sort a2) {
  R();
  P(a0);
  U(a1);
  P(a2);
  C(137);
}
void log_Z3_mk_pattern(Z3_context a0, unsigned a1, Z3_ast const * a2) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { P(a2[i]); }
  Ap(a1);
  C(138);
}
void log_Z3_mk_bound(Z3_context a0, unsigned a1, Z3_sort a2) {
  R();
  P(a0);
  U(a1);
  P(a2);
  C(139);
}
void log_Z3_mk_forall(Z3_context a0, unsigned a1, unsigned a2, Z3_pattern const * a3, unsigned a4, Z3_sort const * a5, Z3_symbol const * a6, Z3_ast a7) {
  R();
  P(a0);
  U(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  U(a4);
  for (unsigned i = 0; i < a4; i++) { P(a5[i]); }
  Ap(a4);
  for (unsigned i = 0; i < a4; i++) { Sy(a6[i]); }
  Asy(a4);
  P(a7);
  C(140);
}
void log_Z3_mk_exists(Z3_context a0, unsigned a1, unsigned a2, Z3_pattern const * a3, unsigned a4, Z3_sort const * a5, Z3_symbol const * a6, Z3_ast a7) {
  R();
  P(a0);
  U(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  U(a4);
  for (unsigned i = 0; i < a4; i++) { P(a5[i]); }
  Ap(a4);
  for (unsigned i = 0; i < a4; i++) { Sy(a6[i]); }
  Asy(a4);
  P(a7);
  C(141);
}
void log_Z3_mk_quantifier(Z3_context a0, Z3_bool a1, unsigned a2, unsigned a3, Z3_pattern const * a4, unsigned a5, Z3_sort const * a6, Z3_symbol const * a7, Z3_ast a8) {
  R();
  P(a0);
  I(a1);
  U(a2);
  U(a3);
  for (unsigned i = 0; i < a3; i++) { P(a4[i]); }
  Ap(a3);
  U(a5);
  for (unsigned i = 0; i < a5; i++) { P(a6[i]); }
  Ap(a5);
  for (unsigned i = 0; i < a5; i++) { Sy(a7[i]); }
  Asy(a5);
  P(a8);
  C(142);
}
void log_Z3_mk_quantifier_ex(Z3_context a0, Z3_bool a1, unsigned a2, Z3_symbol a3, Z3_symbol a4, unsigned a5, Z3_pattern const * a6, unsigned a7, Z3_ast const * a8, unsigned a9, Z3_sort const * a10, Z3_symbol const * a11, Z3_ast a12) {
  R();
  P(a0);
  I(a1);
  U(a2);
  Sy(a3);
  Sy(a4);
  U(a5);
  for (unsigned i = 0; i < a5; i++) { P(a6[i]); }
  Ap(a5);
  U(a7);
  for (unsigned i = 0; i < a7; i++) { P(a8[i]); }
  Ap(a7);
  U(a9);
  for (unsigned i = 0; i < a9; i++) { P(a10[i]); }
  Ap(a9);
  for (unsigned i = 0; i < a9; i++) { Sy(a11[i]); }
  Asy(a9);
  P(a12);
  C(143);
}
void log_Z3_mk_forall_const(Z3_context a0, unsigned a1, unsigned a2, Z3_app const * a3, unsigned a4, Z3_pattern const * a5, Z3_ast a6) {
  R();
  P(a0);
  U(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  U(a4);
  for (unsigned i = 0; i < a4; i++) { P(a5[i]); }
  Ap(a4);
  P(a6);
  C(144);
}
void log_Z3_mk_exists_const(Z3_context a0, unsigned a1, unsigned a2, Z3_app const * a3, unsigned a4, Z3_pattern const * a5, Z3_ast a6) {
  R();
  P(a0);
  U(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  U(a4);
  for (unsigned i = 0; i < a4; i++) { P(a5[i]); }
  Ap(a4);
  P(a6);
  C(145);
}
void log_Z3_mk_quantifier_const(Z3_context a0, Z3_bool a1, unsigned a2, unsigned a3, Z3_app const * a4, unsigned a5, Z3_pattern const * a6, Z3_ast a7) {
  R();
  P(a0);
  I(a1);
  U(a2);
  U(a3);
  for (unsigned i = 0; i < a3; i++) { P(a4[i]); }
  Ap(a3);
  U(a5);
  for (unsigned i = 0; i < a5; i++) { P(a6[i]); }
  Ap(a5);
  P(a7);
  C(146);
}
void log_Z3_mk_quantifier_const_ex(Z3_context a0, Z3_bool a1, unsigned a2, Z3_symbol a3, Z3_symbol a4, unsigned a5, Z3_app const * a6, unsigned a7, Z3_pattern const * a8, unsigned a9, Z3_ast const * a10, Z3_ast a11) {
  R();
  P(a0);
  I(a1);
  U(a2);
  Sy(a3);
  Sy(a4);
  U(a5);
  for (unsigned i = 0; i < a5; i++) { P(a6[i]); }
  Ap(a5);
  U(a7);
  for (unsigned i = 0; i < a7; i++) { P(a8[i]); }
  Ap(a7);
  U(a9);
  for (unsigned i = 0; i < a9; i++) { P(a10[i]); }
  Ap(a9);
  P(a11);
  C(147);
}
void log_Z3_get_ast_id(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(148);
}
void log_Z3_get_func_decl_id(Z3_context a0, Z3_func_decl a1) {
  R();
  P(a0);
  P(a1);
  C(149);
}
void log_Z3_get_sort_id(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(150);
}
void log_Z3_is_well_sorted(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(151);
}
void log_Z3_get_symbol_kind(Z3_context a0, Z3_symbol a1) {
  R();
  P(a0);
  Sy(a1);
  C(152);
}
void log_Z3_get_symbol_int(Z3_context a0, Z3_symbol a1) {
  R();
  P(a0);
  Sy(a1);
  C(153);
}
void log_Z3_get_symbol_string(Z3_context a0, Z3_symbol a1) {
  R();
  P(a0);
  Sy(a1);
  C(154);
}
void log_Z3_get_ast_kind(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(155);
}
void log_Z3_get_ast_hash(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(156);
}
void log_Z3_get_numeral_string(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(157);
}
void log_Z3_get_numeral_decimal_string(Z3_context a0, Z3_ast a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(158);
}
void log_Z3_get_numerator(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(159);
}
void log_Z3_get_denominator(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(160);
}
void log_Z3_get_numeral_small(Z3_context a0, Z3_ast a1, __int64* a2, __int64* a3) {
  R();
  P(a0);
  P(a1);
  I(0);
  I(0);
  C(161);
}
void log_Z3_get_numeral_int(Z3_context a0, Z3_ast a1, int* a2) {
  R();
  P(a0);
  P(a1);
  I(0);
  C(162);
}
void log_Z3_get_numeral_uint(Z3_context a0, Z3_ast a1, unsigned* a2) {
  R();
  P(a0);
  P(a1);
  U(0);
  C(163);
}
void log_Z3_get_numeral_uint64(Z3_context a0, Z3_ast a1, __uint64* a2) {
  R();
  P(a0);
  P(a1);
  U(0);
  C(164);
}
void log_Z3_get_numeral_int64(Z3_context a0, Z3_ast a1, __int64* a2) {
  R();
  P(a0);
  P(a1);
  I(0);
  C(165);
}
void log_Z3_get_numeral_rational_int64(Z3_context a0, Z3_ast a1, __int64* a2, __int64* a3) {
  R();
  P(a0);
  P(a1);
  I(0);
  I(0);
  C(166);
}
void log_Z3_get_bool_value(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(167);
}
void log_Z3_get_app_decl(Z3_context a0, Z3_app a1) {
  R();
  P(a0);
  P(a1);
  C(168);
}
void log_Z3_get_app_num_args(Z3_context a0, Z3_app a1) {
  R();
  P(a0);
  P(a1);
  C(169);
}
void log_Z3_get_app_arg(Z3_context a0, Z3_app a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(170);
}
void log_Z3_get_index_value(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(171);
}
void log_Z3_is_quantifier_forall(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(172);
}
void log_Z3_get_quantifier_weight(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(173);
}
void log_Z3_get_quantifier_num_patterns(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(174);
}
void log_Z3_get_quantifier_pattern_ast(Z3_context a0, Z3_ast a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(175);
}
void log_Z3_get_quantifier_num_no_patterns(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(176);
}
void log_Z3_get_quantifier_no_pattern_ast(Z3_context a0, Z3_ast a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(177);
}
void log_Z3_get_quantifier_bound_name(Z3_context a0, Z3_ast a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(178);
}
void log_Z3_get_quantifier_bound_sort(Z3_context a0, Z3_ast a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(179);
}
void log_Z3_get_quantifier_body(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(180);
}
void log_Z3_get_quantifier_num_bound(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(181);
}
void log_Z3_get_decl_name(Z3_context a0, Z3_func_decl a1) {
  R();
  P(a0);
  P(a1);
  C(182);
}
void log_Z3_get_decl_num_parameters(Z3_context a0, Z3_func_decl a1) {
  R();
  P(a0);
  P(a1);
  C(183);
}
void log_Z3_get_decl_parameter_kind(Z3_context a0, Z3_func_decl a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(184);
}
void log_Z3_get_decl_int_parameter(Z3_context a0, Z3_func_decl a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(185);
}
void log_Z3_get_decl_double_parameter(Z3_context a0, Z3_func_decl a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(186);
}
void log_Z3_get_decl_symbol_parameter(Z3_context a0, Z3_func_decl a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(187);
}
void log_Z3_get_decl_sort_parameter(Z3_context a0, Z3_func_decl a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(188);
}
void log_Z3_get_decl_ast_parameter(Z3_context a0, Z3_func_decl a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(189);
}
void log_Z3_get_decl_func_decl_parameter(Z3_context a0, Z3_func_decl a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(190);
}
void log_Z3_get_decl_rational_parameter(Z3_context a0, Z3_func_decl a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(191);
}
void log_Z3_get_sort_name(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(192);
}
void log_Z3_get_sort(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(193);
}
void log_Z3_get_domain_size(Z3_context a0, Z3_func_decl a1) {
  R();
  P(a0);
  P(a1);
  C(194);
}
void log_Z3_get_domain(Z3_context a0, Z3_func_decl a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(195);
}
void log_Z3_get_range(Z3_context a0, Z3_func_decl a1) {
  R();
  P(a0);
  P(a1);
  C(196);
}
void log_Z3_get_sort_kind(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(197);
}
void log_Z3_get_bv_sort_size(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(198);
}
void log_Z3_get_array_sort_domain(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(199);
}
void log_Z3_get_array_sort_range(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(200);
}
void log_Z3_get_tuple_sort_mk_decl(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(201);
}
void log_Z3_get_decl_kind(Z3_context a0, Z3_func_decl a1) {
  R();
  P(a0);
  P(a1);
  C(202);
}
void log_Z3_get_tuple_sort_num_fields(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(203);
}
void log_Z3_get_tuple_sort_field_decl(Z3_context a0, Z3_sort a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(204);
}
void log_Z3_get_datatype_sort_num_constructors(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(205);
}
void log_Z3_get_datatype_sort_constructor(Z3_context a0, Z3_sort a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(206);
}
void log_Z3_get_datatype_sort_recognizer(Z3_context a0, Z3_sort a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(207);
}
void log_Z3_get_datatype_sort_constructor_accessor(Z3_context a0, Z3_sort a1, unsigned a2, unsigned a3) {
  R();
  P(a0);
  P(a1);
  U(a2);
  U(a3);
  C(208);
}
void log_Z3_get_relation_arity(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(209);
}
void log_Z3_get_relation_column(Z3_context a0, Z3_sort a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(210);
}
void log_Z3_get_finite_domain_sort_size(Z3_context a0, Z3_sort a1, __uint64* a2) {
  R();
  P(a0);
  P(a1);
  U(0);
  C(211);
}
void log_Z3_mk_finite_domain_sort(Z3_context a0, Z3_symbol a1, __uint64 a2) {
  R();
  P(a0);
  Sy(a1);
  U(a2);
  C(212);
}
void log_Z3_get_pattern_num_terms(Z3_context a0, Z3_pattern a1) {
  R();
  P(a0);
  P(a1);
  C(213);
}
void log_Z3_get_pattern(Z3_context a0, Z3_pattern a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(214);
}
void log_Z3_simplify(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(215);
}
void log_Z3_simplify_ex(Z3_context a0, Z3_ast a1, Z3_params a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(216);
}
void log_Z3_simplify_get_help(Z3_context a0) {
  R();
  P(a0);
  C(217);
}
void log_Z3_simplify_get_param_descrs(Z3_context a0) {
  R();
  P(a0);
  C(218);
}
void log_Z3_update_term(Z3_context a0, Z3_ast a1, unsigned a2, Z3_ast const * a3) {
  R();
  P(a0);
  P(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  C(219);
}
void log_Z3_substitute(Z3_context a0, Z3_ast a1, unsigned a2, Z3_ast const * a3, Z3_ast const * a4) {
  R();
  P(a0);
  P(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  for (unsigned i = 0; i < a2; i++) { P(a4[i]); }
  Ap(a2);
  C(220);
}
void log_Z3_substitute_vars(Z3_context a0, Z3_ast a1, unsigned a2, Z3_ast const * a3) {
  R();
  P(a0);
  P(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  C(221);
}
void log_Z3_sort_to_ast(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(222);
}
void log_Z3_func_decl_to_ast(Z3_context a0, Z3_func_decl a1) {
  R();
  P(a0);
  P(a1);
  C(223);
}
void log_Z3_pattern_to_ast(Z3_context a0, Z3_pattern a1) {
  R();
  P(a0);
  P(a1);
  C(224);
}
void log_Z3_app_to_ast(Z3_context a0, Z3_app a1) {
  R();
  P(a0);
  P(a1);
  C(225);
}
void log_Z3_to_app(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(226);
}
void log_Z3_to_func_decl(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(227);
}
void log_Z3_push(Z3_context a0) {
  R();
  P(a0);
  C(228);
}
void log_Z3_pop(Z3_context a0, unsigned a1) {
  R();
  P(a0);
  U(a1);
  C(229);
}
void log_Z3_get_num_scopes(Z3_context a0) {
  R();
  P(a0);
  C(230);
}
void log_Z3_persist_ast(Z3_context a0, Z3_ast a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(231);
}
void log_Z3_assert_cnstr(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(232);
}
void log_Z3_check_and_get_model(Z3_context a0, Z3_model* a1) {
  R();
  P(a0);
  P(0);
  C(233);
}
void log_Z3_check(Z3_context a0) {
  R();
  P(a0);
  C(234);
}
void log_Z3_check_assumptions(Z3_context a0, unsigned a1, Z3_ast const * a2, Z3_model* a3, Z3_ast* a4, unsigned* a5, Z3_ast* a6) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { P(a2[i]); }
  Ap(a1);
  P(0);
  P(0);
  U(0);
  for (unsigned i = 0; i < a1; i++) { P(0); }
  Ap(a1);
  C(235);
}
void log_Z3_get_implied_equalities(Z3_context a0, unsigned a1, Z3_ast const * a2, unsigned* a3) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { P(a2[i]); }
  Ap(a1);
  for (unsigned i = 0; i < a1; i++) { U(0); }
  Au(a1);
  C(236);
}
void log_Z3_del_model(Z3_context a0, Z3_model a1) {
  R();
  P(a0);
  P(a1);
  C(237);
}
void log_Z3_soft_check_cancel(Z3_context a0) {
  R();
  P(a0);
  C(238);
}
void log_Z3_get_search_failure(Z3_context a0) {
  R();
  P(a0);
  C(239);
}
void log_Z3_get_relevant_labels(Z3_context a0) {
  R();
  P(a0);
  C(240);
}
void log_Z3_get_relevant_literals(Z3_context a0) {
  R();
  P(a0);
  C(241);
}
void log_Z3_get_guessed_literals(Z3_context a0) {
  R();
  P(a0);
  C(242);
}
void log_Z3_del_literals(Z3_context a0, Z3_literals a1) {
  R();
  P(a0);
  P(a1);
  C(243);
}
void log_Z3_get_num_literals(Z3_context a0, Z3_literals a1) {
  R();
  P(a0);
  P(a1);
  C(244);
}
void log_Z3_get_label_symbol(Z3_context a0, Z3_literals a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(245);
}
void log_Z3_get_literal(Z3_context a0, Z3_literals a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(246);
}
void log_Z3_disable_literal(Z3_context a0, Z3_literals a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(247);
}
void log_Z3_block_literals(Z3_context a0, Z3_literals a1) {
  R();
  P(a0);
  P(a1);
  C(248);
}
void log_Z3_model_inc_ref(Z3_context a0, Z3_model a1) {
  R();
  P(a0);
  P(a1);
  C(249);
}
void log_Z3_model_dec_ref(Z3_context a0, Z3_model a1) {
  R();
  P(a0);
  P(a1);
  C(250);
}
void log_Z3_model_get_const_interp(Z3_context a0, Z3_model a1, Z3_func_decl a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(251);
}
void log_Z3_model_get_func_interp(Z3_context a0, Z3_model a1, Z3_func_decl a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(252);
}
void log_Z3_model_get_num_consts(Z3_context a0, Z3_model a1) {
  R();
  P(a0);
  P(a1);
  C(253);
}
void log_Z3_model_get_const_decl(Z3_context a0, Z3_model a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(254);
}
void log_Z3_model_get_num_funcs(Z3_context a0, Z3_model a1) {
  R();
  P(a0);
  P(a1);
  C(255);
}
void log_Z3_model_get_func_decl(Z3_context a0, Z3_model a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(256);
}
void log_Z3_model_eval(Z3_context a0, Z3_model a1, Z3_ast a2, Z3_bool a3, Z3_ast* a4) {
  R();
  P(a0);
  P(a1);
  P(a2);
  I(a3);
  P(0);
  C(257);
}
void log_Z3_model_get_num_sorts(Z3_context a0, Z3_model a1) {
  R();
  P(a0);
  P(a1);
  C(258);
}
void log_Z3_model_get_sort(Z3_context a0, Z3_model a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(259);
}
void log_Z3_model_get_sort_universe(Z3_context a0, Z3_model a1, Z3_sort a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(260);
}
void log_Z3_is_as_array(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(261);
}
void log_Z3_get_as_array_func_decl(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(262);
}
void log_Z3_func_interp_inc_ref(Z3_context a0, Z3_func_interp a1) {
  R();
  P(a0);
  P(a1);
  C(263);
}
void log_Z3_func_interp_dec_ref(Z3_context a0, Z3_func_interp a1) {
  R();
  P(a0);
  P(a1);
  C(264);
}
void log_Z3_func_interp_get_num_entries(Z3_context a0, Z3_func_interp a1) {
  R();
  P(a0);
  P(a1);
  C(265);
}
void log_Z3_func_interp_get_entry(Z3_context a0, Z3_func_interp a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(266);
}
void log_Z3_func_interp_get_else(Z3_context a0, Z3_func_interp a1) {
  R();
  P(a0);
  P(a1);
  C(267);
}
void log_Z3_func_interp_get_arity(Z3_context a0, Z3_func_interp a1) {
  R();
  P(a0);
  P(a1);
  C(268);
}
void log_Z3_func_entry_inc_ref(Z3_context a0, Z3_func_entry a1) {
  R();
  P(a0);
  P(a1);
  C(269);
}
void log_Z3_func_entry_dec_ref(Z3_context a0, Z3_func_entry a1) {
  R();
  P(a0);
  P(a1);
  C(270);
}
void log_Z3_func_entry_get_value(Z3_context a0, Z3_func_entry a1) {
  R();
  P(a0);
  P(a1);
  C(271);
}
void log_Z3_func_entry_get_num_args(Z3_context a0, Z3_func_entry a1) {
  R();
  P(a0);
  P(a1);
  C(272);
}
void log_Z3_func_entry_get_arg(Z3_context a0, Z3_func_entry a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(273);
}
void log_Z3_get_model_num_constants(Z3_context a0, Z3_model a1) {
  R();
  P(a0);
  P(a1);
  C(274);
}
void log_Z3_get_model_constant(Z3_context a0, Z3_model a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(275);
}
void log_Z3_eval_func_decl(Z3_context a0, Z3_model a1, Z3_func_decl a2, Z3_ast* a3) {
  R();
  P(a0);
  P(a1);
  P(a2);
  P(0);
  C(276);
}
void log_Z3_is_array_value(Z3_context a0, Z3_model a1, Z3_ast a2, unsigned* a3) {
  R();
  P(a0);
  P(a1);
  P(a2);
  U(0);
  C(277);
}
void log_Z3_get_array_value(Z3_context a0, Z3_model a1, Z3_ast a2, unsigned a3, Z3_ast* a4, Z3_ast* a5, Z3_ast* a6) {
  R();
  P(a0);
  P(a1);
  P(a2);
  U(a3);
  for (unsigned i = 0; i < a3; i++) { P(0); }
  Ap(a3);
  for (unsigned i = 0; i < a3; i++) { P(0); }
  Ap(a3);
  P(0);
  C(278);
}
void log_Z3_get_model_num_funcs(Z3_context a0, Z3_model a1) {
  R();
  P(a0);
  P(a1);
  C(279);
}
void log_Z3_get_model_func_decl(Z3_context a0, Z3_model a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(280);
}
void log_Z3_get_model_func_else(Z3_context a0, Z3_model a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(281);
}
void log_Z3_get_model_func_num_entries(Z3_context a0, Z3_model a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(282);
}
void log_Z3_get_model_func_entry_num_args(Z3_context a0, Z3_model a1, unsigned a2, unsigned a3) {
  R();
  P(a0);
  P(a1);
  U(a2);
  U(a3);
  C(283);
}
void log_Z3_get_model_func_entry_arg(Z3_context a0, Z3_model a1, unsigned a2, unsigned a3, unsigned a4) {
  R();
  P(a0);
  P(a1);
  U(a2);
  U(a3);
  U(a4);
  C(284);
}
void log_Z3_get_model_func_entry_value(Z3_context a0, Z3_model a1, unsigned a2, unsigned a3) {
  R();
  P(a0);
  P(a1);
  U(a2);
  U(a3);
  C(285);
}
void log_Z3_eval(Z3_context a0, Z3_model a1, Z3_ast a2, Z3_ast* a3) {
  R();
  P(a0);
  P(a1);
  P(a2);
  P(0);
  C(286);
}
void log_Z3_eval_decl(Z3_context a0, Z3_model a1, Z3_func_decl a2, unsigned a3, Z3_ast const * a4, Z3_ast* a5) {
  R();
  P(a0);
  P(a1);
  P(a2);
  U(a3);
  for (unsigned i = 0; i < a3; i++) { P(a4[i]); }
  Ap(a3);
  P(0);
  C(287);
}
void log_Z3_set_ast_print_mode(Z3_context a0, Z3_ast_print_mode a1) {
  R();
  P(a0);
  U(static_cast<unsigned>(a1));
  C(288);
}
void log_Z3_ast_to_string(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(289);
}
void log_Z3_pattern_to_string(Z3_context a0, Z3_pattern a1) {
  R();
  P(a0);
  P(a1);
  C(290);
}
void log_Z3_sort_to_string(Z3_context a0, Z3_sort a1) {
  R();
  P(a0);
  P(a1);
  C(291);
}
void log_Z3_func_decl_to_string(Z3_context a0, Z3_func_decl a1) {
  R();
  P(a0);
  P(a1);
  C(292);
}
void log_Z3_model_to_string(Z3_context a0, Z3_model a1) {
  R();
  P(a0);
  P(a1);
  C(293);
}
void log_Z3_benchmark_to_smtlib_string(Z3_context a0, Z3_string a1, Z3_string a2, Z3_string a3, Z3_string a4, unsigned a5, Z3_ast const * a6, Z3_ast a7) {
  R();
  P(a0);
  S(a1);
  S(a2);
  S(a3);
  S(a4);
  U(a5);
  for (unsigned i = 0; i < a5; i++) { P(a6[i]); }
  Ap(a5);
  P(a7);
  C(294);
}
void log_Z3_context_to_string(Z3_context a0) {
  R();
  P(a0);
  C(295);
}
void log_Z3_statistics_to_string(Z3_context a0) {
  R();
  P(a0);
  C(296);
}
void log_Z3_get_context_assignment(Z3_context a0) {
  R();
  P(a0);
  C(297);
}
void log_Z3_parse_smtlib_string(Z3_context a0, Z3_string a1, unsigned a2, Z3_symbol const * a3, Z3_sort const * a4, unsigned a5, Z3_symbol const * a6, Z3_func_decl const * a7) {
  R();
  P(a0);
  S(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { Sy(a3[i]); }
  Asy(a2);
  for (unsigned i = 0; i < a2; i++) { P(a4[i]); }
  Ap(a2);
  U(a5);
  for (unsigned i = 0; i < a5; i++) { Sy(a6[i]); }
  Asy(a5);
  for (unsigned i = 0; i < a5; i++) { P(a7[i]); }
  Ap(a5);
  C(298);
}
void log_Z3_parse_smtlib_file(Z3_context a0, Z3_string a1, unsigned a2, Z3_symbol const * a3, Z3_sort const * a4, unsigned a5, Z3_symbol const * a6, Z3_func_decl const * a7) {
  R();
  P(a0);
  S(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { Sy(a3[i]); }
  Asy(a2);
  for (unsigned i = 0; i < a2; i++) { P(a4[i]); }
  Ap(a2);
  U(a5);
  for (unsigned i = 0; i < a5; i++) { Sy(a6[i]); }
  Asy(a5);
  for (unsigned i = 0; i < a5; i++) { P(a7[i]); }
  Ap(a5);
  C(299);
}
void log_Z3_get_smtlib_num_formulas(Z3_context a0) {
  R();
  P(a0);
  C(300);
}
void log_Z3_get_smtlib_formula(Z3_context a0, unsigned a1) {
  R();
  P(a0);
  U(a1);
  C(301);
}
void log_Z3_get_smtlib_num_assumptions(Z3_context a0) {
  R();
  P(a0);
  C(302);
}
void log_Z3_get_smtlib_assumption(Z3_context a0, unsigned a1) {
  R();
  P(a0);
  U(a1);
  C(303);
}
void log_Z3_get_smtlib_num_decls(Z3_context a0) {
  R();
  P(a0);
  C(304);
}
void log_Z3_get_smtlib_decl(Z3_context a0, unsigned a1) {
  R();
  P(a0);
  U(a1);
  C(305);
}
void log_Z3_get_smtlib_num_sorts(Z3_context a0) {
  R();
  P(a0);
  C(306);
}
void log_Z3_get_smtlib_sort(Z3_context a0, unsigned a1) {
  R();
  P(a0);
  U(a1);
  C(307);
}
void log_Z3_get_smtlib_error(Z3_context a0) {
  R();
  P(a0);
  C(308);
}
void log_Z3_parse_z3_string(Z3_context a0, Z3_string a1) {
  R();
  P(a0);
  S(a1);
  C(309);
}
void log_Z3_parse_z3_file(Z3_context a0, Z3_string a1) {
  R();
  P(a0);
  S(a1);
  C(310);
}
void log_Z3_parse_smtlib2_string(Z3_context a0, Z3_string a1, unsigned a2, Z3_symbol const * a3, Z3_sort const * a4, unsigned a5, Z3_symbol const * a6, Z3_func_decl const * a7) {
  R();
  P(a0);
  S(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { Sy(a3[i]); }
  Asy(a2);
  for (unsigned i = 0; i < a2; i++) { P(a4[i]); }
  Ap(a2);
  U(a5);
  for (unsigned i = 0; i < a5; i++) { Sy(a6[i]); }
  Asy(a5);
  for (unsigned i = 0; i < a5; i++) { P(a7[i]); }
  Ap(a5);
  C(311);
}
void log_Z3_parse_smtlib2_file(Z3_context a0, Z3_string a1, unsigned a2, Z3_symbol const * a3, Z3_sort const * a4, unsigned a5, Z3_symbol const * a6, Z3_func_decl const * a7) {
  R();
  P(a0);
  S(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { Sy(a3[i]); }
  Asy(a2);
  for (unsigned i = 0; i < a2; i++) { P(a4[i]); }
  Ap(a2);
  U(a5);
  for (unsigned i = 0; i < a5; i++) { Sy(a6[i]); }
  Asy(a5);
  for (unsigned i = 0; i < a5; i++) { P(a7[i]); }
  Ap(a5);
  C(312);
}
void log_Z3_get_error_code(Z3_context a0) {
  R();
  P(a0);
  C(313);
}
void log_Z3_set_error(Z3_context a0, Z3_error_code a1) {
  R();
  P(a0);
  U(static_cast<unsigned>(a1));
  C(314);
}
void log_Z3_get_error_msg(Z3_error_code a0) {
  R();
  U(static_cast<unsigned>(a0));
  C(315);
}
void log_Z3_get_version(unsigned* a0, unsigned* a1, unsigned* a2, unsigned* a3) {
  R();
  U(0);
  U(0);
  U(0);
  U(0);
  C(316);
}
void log_Z3_reset_memory() {
  R();
  C(317);
}
void log_Z3_is_app(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(318);
}
void log_Z3_is_numeral_ast(Z3_context a0, Z3_ast a1) {
  R();
  P(a0);
  P(a1);
  C(319);
}
void log_Z3_get_arity(Z3_context a0, Z3_func_decl a1) {
  R();
  P(a0);
  P(a1);
  C(320);
}
void log_Z3_mk_injective_function(Z3_context a0, Z3_symbol a1, unsigned a2, Z3_sort const * a3, Z3_sort a4) {
  R();
  P(a0);
  Sy(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  P(a4);
  C(321);
}
void log_Z3_mk_fixedpoint(Z3_context a0) {
  R();
  P(a0);
  C(322);
}
void log_Z3_fixedpoint_inc_ref(Z3_context a0, Z3_fixedpoint a1) {
  R();
  P(a0);
  P(a1);
  C(323);
}
void log_Z3_fixedpoint_dec_ref(Z3_context a0, Z3_fixedpoint a1) {
  R();
  P(a0);
  P(a1);
  C(324);
}
void log_Z3_fixedpoint_push(Z3_context a0, Z3_fixedpoint a1) {
  R();
  P(a0);
  P(a1);
  C(325);
}
void log_Z3_fixedpoint_pop(Z3_context a0, Z3_fixedpoint a1) {
  R();
  P(a0);
  P(a1);
  C(326);
}
void log_Z3_fixedpoint_register_relation(Z3_context a0, Z3_fixedpoint a1, Z3_func_decl a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(327);
}
void log_Z3_fixedpoint_assert(Z3_context a0, Z3_fixedpoint a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(328);
}
void log_Z3_fixedpoint_add_rule(Z3_context a0, Z3_fixedpoint a1, Z3_ast a2, Z3_symbol a3) {
  R();
  P(a0);
  P(a1);
  P(a2);
  Sy(a3);
  C(329);
}
void log_Z3_fixedpoint_add_fact(Z3_context a0, Z3_fixedpoint a1, Z3_func_decl a2, unsigned a3, unsigned const * a4) {
  R();
  P(a0);
  P(a1);
  P(a2);
  U(a3);
  for (unsigned i = 0; i < a3; i++) { U(a4[i]); }
  Au(a3);
  C(330);
}
void log_Z3_fixedpoint_query(Z3_context a0, Z3_fixedpoint a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(331);
}
void log_Z3_fixedpoint_query_relations(Z3_context a0, Z3_fixedpoint a1, unsigned a2, Z3_func_decl const * a3) {
  R();
  P(a0);
  P(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  C(332);
}
void log_Z3_fixedpoint_get_answer(Z3_context a0, Z3_fixedpoint a1) {
  R();
  P(a0);
  P(a1);
  C(333);
}
void log_Z3_fixedpoint_update_rule(Z3_context a0, Z3_fixedpoint a1, Z3_ast a2, Z3_symbol a3) {
  R();
  P(a0);
  P(a1);
  P(a2);
  Sy(a3);
  C(334);
}
void log_Z3_fixedpoint_get_num_levels(Z3_context a0, Z3_fixedpoint a1, Z3_func_decl a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(335);
}
void log_Z3_fixedpoint_get_cover_delta(Z3_context a0, Z3_fixedpoint a1, int a2, Z3_func_decl a3) {
  R();
  P(a0);
  P(a1);
  I(a2);
  P(a3);
  C(336);
}
void log_Z3_fixedpoint_add_cover(Z3_context a0, Z3_fixedpoint a1, int a2, Z3_func_decl a3, Z3_ast a4) {
  R();
  P(a0);
  P(a1);
  I(a2);
  P(a3);
  P(a4);
  C(337);
}
void log_Z3_fixedpoint_get_statistics(Z3_context a0, Z3_fixedpoint a1) {
  R();
  P(a0);
  P(a1);
  C(338);
}
void log_Z3_fixedpoint_get_help(Z3_context a0, Z3_fixedpoint a1) {
  R();
  P(a0);
  P(a1);
  C(339);
}
void log_Z3_fixedpoint_get_param_descrs(Z3_context a0, Z3_fixedpoint a1) {
  R();
  P(a0);
  P(a1);
  C(340);
}
void log_Z3_fixedpoint_set_params(Z3_context a0, Z3_fixedpoint a1, Z3_params a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(341);
}
void log_Z3_fixedpoint_to_string(Z3_context a0, Z3_fixedpoint a1, unsigned a2, Z3_ast const * a3) {
  R();
  P(a0);
  P(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  C(342);
}
void log_Z3_fixedpoint_get_reason_unknown(Z3_context a0, Z3_fixedpoint a1) {
  R();
  P(a0);
  P(a1);
  C(343);
}
void log_Z3_fixedpoint_set_predicate_representation(Z3_context a0, Z3_fixedpoint a1, Z3_func_decl a2, unsigned a3, Z3_symbol const * a4) {
  R();
  P(a0);
  P(a1);
  P(a2);
  U(a3);
  for (unsigned i = 0; i < a3; i++) { Sy(a4[i]); }
  Asy(a3);
  C(344);
}
void log_Z3_fixedpoint_simplify_rules(Z3_context a0, Z3_fixedpoint a1, unsigned a2, Z3_ast const * a3, unsigned a4, Z3_func_decl const * a5) {
  R();
  P(a0);
  P(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  U(a4);
  for (unsigned i = 0; i < a4; i++) { P(a5[i]); }
  Ap(a4);
  C(345);
}
void log_Z3_mk_params(Z3_context a0) {
  R();
  P(a0);
  C(346);
}
void log_Z3_params_inc_ref(Z3_context a0, Z3_params a1) {
  R();
  P(a0);
  P(a1);
  C(347);
}
void log_Z3_params_dec_ref(Z3_context a0, Z3_params a1) {
  R();
  P(a0);
  P(a1);
  C(348);
}
void log_Z3_params_set_bool(Z3_context a0, Z3_params a1, Z3_symbol a2, Z3_bool a3) {
  R();
  P(a0);
  P(a1);
  Sy(a2);
  I(a3);
  C(349);
}
void log_Z3_params_set_uint(Z3_context a0, Z3_params a1, Z3_symbol a2, unsigned a3) {
  R();
  P(a0);
  P(a1);
  Sy(a2);
  U(a3);
  C(350);
}
void log_Z3_params_set_double(Z3_context a0, Z3_params a1, Z3_symbol a2, double a3) {
  R();
  P(a0);
  P(a1);
  Sy(a2);
  D(a3);
  C(351);
}
void log_Z3_params_set_symbol(Z3_context a0, Z3_params a1, Z3_symbol a2, Z3_symbol a3) {
  R();
  P(a0);
  P(a1);
  Sy(a2);
  Sy(a3);
  C(352);
}
void log_Z3_params_to_string(Z3_context a0, Z3_params a1) {
  R();
  P(a0);
  P(a1);
  C(353);
}
void log_Z3_params_validate(Z3_context a0, Z3_params a1, Z3_param_descrs a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(354);
}
void log_Z3_param_descrs_inc_ref(Z3_context a0, Z3_param_descrs a1) {
  R();
  P(a0);
  P(a1);
  C(355);
}
void log_Z3_param_descrs_dec_ref(Z3_context a0, Z3_param_descrs a1) {
  R();
  P(a0);
  P(a1);
  C(356);
}
void log_Z3_param_descrs_get_kind(Z3_context a0, Z3_param_descrs a1, Z3_symbol a2) {
  R();
  P(a0);
  P(a1);
  Sy(a2);
  C(357);
}
void log_Z3_param_descrs_size(Z3_context a0, Z3_param_descrs a1) {
  R();
  P(a0);
  P(a1);
  C(358);
}
void log_Z3_param_descrs_get_name(Z3_context a0, Z3_param_descrs a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(359);
}
void log_Z3_interrupt(Z3_context a0) {
  R();
  P(a0);
  C(360);
}
void log_Z3_get_error_msg_ex(Z3_context a0, Z3_error_code a1) {
  R();
  P(a0);
  U(static_cast<unsigned>(a1));
  C(361);
}
void log_Z3_translate(Z3_context a0, Z3_ast a1, Z3_context a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(362);
}
void log_Z3_mk_goal(Z3_context a0, Z3_bool a1, Z3_bool a2, Z3_bool a3) {
  R();
  P(a0);
  I(a1);
  I(a2);
  I(a3);
  C(363);
}
void log_Z3_goal_inc_ref(Z3_context a0, Z3_goal a1) {
  R();
  P(a0);
  P(a1);
  C(364);
}
void log_Z3_goal_dec_ref(Z3_context a0, Z3_goal a1) {
  R();
  P(a0);
  P(a1);
  C(365);
}
void log_Z3_goal_precision(Z3_context a0, Z3_goal a1) {
  R();
  P(a0);
  P(a1);
  C(366);
}
void log_Z3_goal_assert(Z3_context a0, Z3_goal a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(367);
}
void log_Z3_goal_inconsistent(Z3_context a0, Z3_goal a1) {
  R();
  P(a0);
  P(a1);
  C(368);
}
void log_Z3_goal_depth(Z3_context a0, Z3_goal a1) {
  R();
  P(a0);
  P(a1);
  C(369);
}
void log_Z3_goal_reset(Z3_context a0, Z3_goal a1) {
  R();
  P(a0);
  P(a1);
  C(370);
}
void log_Z3_goal_size(Z3_context a0, Z3_goal a1) {
  R();
  P(a0);
  P(a1);
  C(371);
}
void log_Z3_goal_formula(Z3_context a0, Z3_goal a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(372);
}
void log_Z3_goal_num_exprs(Z3_context a0, Z3_goal a1) {
  R();
  P(a0);
  P(a1);
  C(373);
}
void log_Z3_goal_is_decided_sat(Z3_context a0, Z3_goal a1) {
  R();
  P(a0);
  P(a1);
  C(374);
}
void log_Z3_goal_is_decided_unsat(Z3_context a0, Z3_goal a1) {
  R();
  P(a0);
  P(a1);
  C(375);
}
void log_Z3_goal_translate(Z3_context a0, Z3_goal a1, Z3_context a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(376);
}
void log_Z3_goal_to_string(Z3_context a0, Z3_goal a1) {
  R();
  P(a0);
  P(a1);
  C(377);
}
void log_Z3_mk_tactic(Z3_context a0, Z3_string a1) {
  R();
  P(a0);
  S(a1);
  C(378);
}
void log_Z3_mk_probe(Z3_context a0, Z3_string a1) {
  R();
  P(a0);
  S(a1);
  C(379);
}
void log_Z3_tactic_inc_ref(Z3_context a0, Z3_tactic a1) {
  R();
  P(a0);
  P(a1);
  C(380);
}
void log_Z3_tactic_dec_ref(Z3_context a0, Z3_tactic a1) {
  R();
  P(a0);
  P(a1);
  C(381);
}
void log_Z3_probe_inc_ref(Z3_context a0, Z3_probe a1) {
  R();
  P(a0);
  P(a1);
  C(382);
}
void log_Z3_probe_dec_ref(Z3_context a0, Z3_probe a1) {
  R();
  P(a0);
  P(a1);
  C(383);
}
void log_Z3_tactic_and_then(Z3_context a0, Z3_tactic a1, Z3_tactic a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(384);
}
void log_Z3_tactic_or_else(Z3_context a0, Z3_tactic a1, Z3_tactic a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(385);
}
void log_Z3_tactic_par_or(Z3_context a0, unsigned a1, Z3_tactic const * a2) {
  R();
  P(a0);
  U(a1);
  for (unsigned i = 0; i < a1; i++) { P(a2[i]); }
  Ap(a1);
  C(386);
}
void log_Z3_tactic_par_and_then(Z3_context a0, Z3_tactic a1, Z3_tactic a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(387);
}
void log_Z3_tactic_try_for(Z3_context a0, Z3_tactic a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(388);
}
void log_Z3_tactic_when(Z3_context a0, Z3_probe a1, Z3_tactic a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(389);
}
void log_Z3_tactic_cond(Z3_context a0, Z3_probe a1, Z3_tactic a2, Z3_tactic a3) {
  R();
  P(a0);
  P(a1);
  P(a2);
  P(a3);
  C(390);
}
void log_Z3_tactic_repeat(Z3_context a0, Z3_tactic a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(391);
}
void log_Z3_tactic_skip(Z3_context a0) {
  R();
  P(a0);
  C(392);
}
void log_Z3_tactic_fail(Z3_context a0) {
  R();
  P(a0);
  C(393);
}
void log_Z3_tactic_fail_if(Z3_context a0, Z3_probe a1) {
  R();
  P(a0);
  P(a1);
  C(394);
}
void log_Z3_tactic_fail_if_not_decided(Z3_context a0) {
  R();
  P(a0);
  C(395);
}
void log_Z3_tactic_using_params(Z3_context a0, Z3_tactic a1, Z3_params a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(396);
}
void log_Z3_probe_const(Z3_context a0, double a1) {
  R();
  P(a0);
  D(a1);
  C(397);
}
void log_Z3_probe_lt(Z3_context a0, Z3_probe a1, Z3_probe a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(398);
}
void log_Z3_probe_le(Z3_context a0, Z3_probe a1, Z3_probe a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(399);
}
void log_Z3_probe_gt(Z3_context a0, Z3_probe a1, Z3_probe a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(400);
}
void log_Z3_probe_ge(Z3_context a0, Z3_probe a1, Z3_probe a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(401);
}
void log_Z3_probe_eq(Z3_context a0, Z3_probe a1, Z3_probe a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(402);
}
void log_Z3_probe_and(Z3_context a0, Z3_probe a1, Z3_probe a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(403);
}
void log_Z3_probe_or(Z3_context a0, Z3_probe a1, Z3_probe a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(404);
}
void log_Z3_probe_not(Z3_context a0, Z3_probe a1) {
  R();
  P(a0);
  P(a1);
  C(405);
}
void log_Z3_get_num_tactics(Z3_context a0) {
  R();
  P(a0);
  C(406);
}
void log_Z3_get_tactic_name(Z3_context a0, unsigned a1) {
  R();
  P(a0);
  U(a1);
  C(407);
}
void log_Z3_get_num_probes(Z3_context a0) {
  R();
  P(a0);
  C(408);
}
void log_Z3_get_probe_name(Z3_context a0, unsigned a1) {
  R();
  P(a0);
  U(a1);
  C(409);
}
void log_Z3_tactic_get_help(Z3_context a0, Z3_tactic a1) {
  R();
  P(a0);
  P(a1);
  C(410);
}
void log_Z3_tactic_get_param_descrs(Z3_context a0, Z3_tactic a1) {
  R();
  P(a0);
  P(a1);
  C(411);
}
void log_Z3_tactic_get_descr(Z3_context a0, Z3_string a1) {
  R();
  P(a0);
  S(a1);
  C(412);
}
void log_Z3_probe_get_descr(Z3_context a0, Z3_string a1) {
  R();
  P(a0);
  S(a1);
  C(413);
}
void log_Z3_probe_apply(Z3_context a0, Z3_probe a1, Z3_goal a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(414);
}
void log_Z3_tactic_apply(Z3_context a0, Z3_tactic a1, Z3_goal a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(415);
}
void log_Z3_tactic_apply_ex(Z3_context a0, Z3_tactic a1, Z3_goal a2, Z3_params a3) {
  R();
  P(a0);
  P(a1);
  P(a2);
  P(a3);
  C(416);
}
void log_Z3_apply_result_inc_ref(Z3_context a0, Z3_apply_result a1) {
  R();
  P(a0);
  P(a1);
  C(417);
}
void log_Z3_apply_result_dec_ref(Z3_context a0, Z3_apply_result a1) {
  R();
  P(a0);
  P(a1);
  C(418);
}
void log_Z3_apply_result_to_string(Z3_context a0, Z3_apply_result a1) {
  R();
  P(a0);
  P(a1);
  C(419);
}
void log_Z3_apply_result_get_num_subgoals(Z3_context a0, Z3_apply_result a1) {
  R();
  P(a0);
  P(a1);
  C(420);
}
void log_Z3_apply_result_get_subgoal(Z3_context a0, Z3_apply_result a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(421);
}
void log_Z3_apply_result_convert_model(Z3_context a0, Z3_apply_result a1, unsigned a2, Z3_model a3) {
  R();
  P(a0);
  P(a1);
  U(a2);
  P(a3);
  C(422);
}
void log_Z3_mk_solver(Z3_context a0) {
  R();
  P(a0);
  C(423);
}
void log_Z3_mk_simple_solver(Z3_context a0) {
  R();
  P(a0);
  C(424);
}
void log_Z3_mk_solver_for_logic(Z3_context a0, Z3_symbol a1) {
  R();
  P(a0);
  Sy(a1);
  C(425);
}
void log_Z3_mk_solver_from_tactic(Z3_context a0, Z3_tactic a1) {
  R();
  P(a0);
  P(a1);
  C(426);
}
void log_Z3_solver_get_help(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(427);
}
void log_Z3_solver_get_param_descrs(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(428);
}
void log_Z3_solver_set_params(Z3_context a0, Z3_solver a1, Z3_params a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(429);
}
void log_Z3_solver_inc_ref(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(430);
}
void log_Z3_solver_dec_ref(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(431);
}
void log_Z3_solver_push(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(432);
}
void log_Z3_solver_pop(Z3_context a0, Z3_solver a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(433);
}
void log_Z3_solver_reset(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(434);
}
void log_Z3_solver_get_num_scopes(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(435);
}
void log_Z3_solver_assert(Z3_context a0, Z3_solver a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(436);
}
void log_Z3_solver_get_assertions(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(437);
}
void log_Z3_solver_check(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(438);
}
void log_Z3_solver_check_assumptions(Z3_context a0, Z3_solver a1, unsigned a2, Z3_ast const * a3) {
  R();
  P(a0);
  P(a1);
  U(a2);
  for (unsigned i = 0; i < a2; i++) { P(a3[i]); }
  Ap(a2);
  C(439);
}
void log_Z3_solver_get_model(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(440);
}
void log_Z3_solver_get_proof(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(441);
}
void log_Z3_solver_get_unsat_core(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(442);
}
void log_Z3_solver_get_reason_unknown(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(443);
}
void log_Z3_solver_get_statistics(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(444);
}
void log_Z3_solver_to_string(Z3_context a0, Z3_solver a1) {
  R();
  P(a0);
  P(a1);
  C(445);
}
void log_Z3_stats_to_string(Z3_context a0, Z3_stats a1) {
  R();
  P(a0);
  P(a1);
  C(446);
}
void log_Z3_stats_inc_ref(Z3_context a0, Z3_stats a1) {
  R();
  P(a0);
  P(a1);
  C(447);
}
void log_Z3_stats_dec_ref(Z3_context a0, Z3_stats a1) {
  R();
  P(a0);
  P(a1);
  C(448);
}
void log_Z3_stats_size(Z3_context a0, Z3_stats a1) {
  R();
  P(a0);
  P(a1);
  C(449);
}
void log_Z3_stats_get_key(Z3_context a0, Z3_stats a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(450);
}
void log_Z3_stats_is_uint(Z3_context a0, Z3_stats a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(451);
}
void log_Z3_stats_is_double(Z3_context a0, Z3_stats a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(452);
}
void log_Z3_stats_get_uint_value(Z3_context a0, Z3_stats a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(453);
}
void log_Z3_stats_get_double_value(Z3_context a0, Z3_stats a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(454);
}
void log_Z3_mk_ast_vector(Z3_context a0) {
  R();
  P(a0);
  C(455);
}
void log_Z3_ast_vector_inc_ref(Z3_context a0, Z3_ast_vector a1) {
  R();
  P(a0);
  P(a1);
  C(456);
}
void log_Z3_ast_vector_dec_ref(Z3_context a0, Z3_ast_vector a1) {
  R();
  P(a0);
  P(a1);
  C(457);
}
void log_Z3_ast_vector_size(Z3_context a0, Z3_ast_vector a1) {
  R();
  P(a0);
  P(a1);
  C(458);
}
void log_Z3_ast_vector_get(Z3_context a0, Z3_ast_vector a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(459);
}
void log_Z3_ast_vector_set(Z3_context a0, Z3_ast_vector a1, unsigned a2, Z3_ast a3) {
  R();
  P(a0);
  P(a1);
  U(a2);
  P(a3);
  C(460);
}
void log_Z3_ast_vector_resize(Z3_context a0, Z3_ast_vector a1, unsigned a2) {
  R();
  P(a0);
  P(a1);
  U(a2);
  C(461);
}
void log_Z3_ast_vector_push(Z3_context a0, Z3_ast_vector a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(462);
}
void log_Z3_ast_vector_translate(Z3_context a0, Z3_ast_vector a1, Z3_context a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(463);
}
void log_Z3_ast_vector_to_string(Z3_context a0, Z3_ast_vector a1) {
  R();
  P(a0);
  P(a1);
  C(464);
}
void log_Z3_mk_ast_map(Z3_context a0) {
  R();
  P(a0);
  C(465);
}
void log_Z3_ast_map_inc_ref(Z3_context a0, Z3_ast_map a1) {
  R();
  P(a0);
  P(a1);
  C(466);
}
void log_Z3_ast_map_dec_ref(Z3_context a0, Z3_ast_map a1) {
  R();
  P(a0);
  P(a1);
  C(467);
}
void log_Z3_ast_map_contains(Z3_context a0, Z3_ast_map a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(468);
}
void log_Z3_ast_map_find(Z3_context a0, Z3_ast_map a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(469);
}
void log_Z3_ast_map_insert(Z3_context a0, Z3_ast_map a1, Z3_ast a2, Z3_ast a3) {
  R();
  P(a0);
  P(a1);
  P(a2);
  P(a3);
  C(470);
}
void log_Z3_ast_map_erase(Z3_context a0, Z3_ast_map a1, Z3_ast a2) {
  R();
  P(a0);
  P(a1);
  P(a2);
  C(471);
}
void log_Z3_ast_map_size(Z3_context a0, Z3_ast_map a1) {
  R();
  P(a0);
  P(a1);
  C(472);
}
void log_Z3_ast_map_reset(Z3_context a0, Z3_ast_map a1) {
  R();
  P(a0);
  P(a1);
  C(473);
}
void log_Z3_ast_map_keys(Z3_context a0, Z3_ast_map a1) {
  R();
  P(a0);
  P(a1);
  C(474);
}
void log_Z3_ast_map_to_string(Z3_context a0, Z3_ast_map a1) {
  R();
  P(a0);
  P(a1);
  C(475);
}
