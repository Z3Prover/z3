/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv_rewriter.h

Abstract:

    Basic rewriting rules for bit-vectors

Author:

    Leonardo (leonardo) 2011-04-14

Notes:

--*/
#ifndef BV_REWRITER_H_
#define BV_REWRITER_H_

#include "ast/rewriter/poly_rewriter.h"
#include "ast/bv_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/mk_extract_proc.h"
#include "ast/rewriter/bv_trailing.h"

class bv_rewriter_core {
protected:
    typedef rational numeral;
    bv_util         m_util;
    ast_manager & m() const { return m_util.get_manager(); }
    family_id get_fid() const { return m_util.get_family_id(); }

    bool is_numeral(expr * n) const { return m_util.is_numeral(n); }
    bool is_numeral(expr * n, numeral & r) const { unsigned sz; return m_util.is_numeral(n, r, sz); }
    bool is_zero(expr * n) const { return m_util.is_zero(n); }
    bool is_minus_one(expr * n) const { return m_util.is_allone(n); }
    void normalize(numeral & c, sort * s) { unsigned bv_size = m_util.get_bv_size(s); c = m_util.norm(c, bv_size); }
    app * mk_numeral(numeral const & r, sort * s) { return m_util.mk_numeral(r, s); }
    decl_kind add_decl_kind() const { return OP_BADD; }
    decl_kind mul_decl_kind() const { return OP_BMUL; }
    bool use_power() const { return false; }
    decl_kind power_decl_kind() const { UNREACHABLE(); return static_cast<decl_kind>(UINT_MAX); }

public:
    bv_rewriter_core(ast_manager & m):m_util(m) {}
};

class bv_rewriter : public poly_rewriter<bv_rewriter_core> {
    mk_extract_proc m_mk_extract;
    bv_trailing     m_rm_trailing;
    arith_util m_autil;
    bool       m_hi_div0;
    bool       m_elim_sign_ext;
    bool       m_mul2concat;
    bool       m_bit2bool;
    bool       m_blast_eq_value;
    bool       m_mkbv2num;
    bool       m_ite2id;
    bool       m_split_concat_eq;
    bool       m_udiv2mul;
    bool       m_bvnot2arith;
    bool       m_bv_sort_ac;
    bool       m_trailing;
    bool       m_extract_prop;
    bool       m_bvnot_simpl;
    bool       m_le_extra;
    bool       m_urem_simpl;

    bool is_zero_bit(expr * x, unsigned idx);

    br_status mk_ule(expr * a, expr * b, expr_ref & result);
    br_status mk_uge(expr * a, expr * b, expr_ref & result);
    br_status mk_ult(expr * a, expr * b, expr_ref & result);
    br_status mk_sle(expr * a, expr * b, expr_ref & result);
    br_status mk_sge(expr * a, expr * b, expr_ref & result);
    br_status mk_slt(expr * a, expr * b, expr_ref & result);
    br_status rw_leq_concats(bool is_signed, expr * a, expr * b, expr_ref & result);
    bool are_eq_upto_num(expr * a, expr * b, expr_ref& common, numeral& a0_val, numeral& b0_val);
    br_status rw_leq_overflow(bool is_signed, expr * _a, expr * _b, expr_ref & result);
    br_status mk_leq_core(bool is_signed, expr * a, expr * b, expr_ref & result);

    br_status mk_concat(unsigned num_args, expr * const * args, expr_ref & result);
    unsigned propagate_extract(unsigned high,  expr * arg, expr_ref & result);
    br_status mk_extract(unsigned high, unsigned low, expr * arg, expr_ref & result);
    br_status mk_repeat(unsigned n, expr * arg, expr_ref & result);
    br_status mk_zero_extend(unsigned n, expr * arg, expr_ref & result);
    br_status mk_sign_extend(unsigned n, expr * arg, expr_ref & result);
    bool is_negatable(expr * arg, expr_ref& x);
    br_status mk_bv_not(expr * arg, expr_ref & result);
    br_status mk_bv_or(unsigned num, expr * const * args, expr_ref & result);
    br_status mk_bv_xor(unsigned num, expr * const * args, expr_ref & result);
    br_status mk_bv_and(unsigned num, expr * const * args, expr_ref & result);
    br_status mk_bv_nand(unsigned num, expr * const * args, expr_ref & result);
    br_status mk_bv_nor(unsigned num, expr * const * args, expr_ref & result);
    br_status mk_bv_xnor(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_bv_rotate_left(unsigned n, expr * arg, expr_ref & result);
    br_status mk_bv_rotate_right(unsigned n, expr * arg, expr_ref & result);
    br_status mk_bv_ext_rotate_left(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_bv_ext_rotate_right(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_bv_add(expr* a, expr* b, expr_ref& result) { expr* args[2] = { a, b }; return mk_bv_add(2, args, result); }
    br_status mk_bv_sub(expr* a, expr* b, expr_ref& result) { expr* args[2] = { a, b }; return mk_sub(2, args, result); }
    br_status mk_bv_mul(expr* a, expr* b, expr_ref& result) { expr* args[2] = { a, b }; return mk_bv_mul(2, args, result); }
    br_status mk_bv_add(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_bv_mul(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_bv_shl(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_bv_lshr(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_bv_ashr(expr * arg1, expr * arg2, expr_ref & result);
    bool is_minus_one_core(expr * arg) const;
    bool is_x_minus_one(expr * arg, expr * & x);
    bool is_add_no_overflow(expr* e);
    bool is_mul_no_overflow(expr* e);
    unsigned num_leading_zero_bits(expr* e);

    br_status mk_bv_sdiv_core(expr * arg1, expr * arg2, bool hi_div0, expr_ref & result);
    br_status mk_bv_udiv_core(expr * arg1, expr * arg2, bool hi_div0, expr_ref & result);
    br_status mk_bv_srem_core(expr * arg1, expr * arg2, bool hi_div0, expr_ref & result);
    br_status mk_bv_urem_core(expr * arg1, expr * arg2, bool hi_div0, expr_ref & result);
    br_status mk_bv_smod_core(expr * arg1, expr * arg2, bool hi_div0, expr_ref & result);
    br_status mk_bv_sdiv(expr * arg1, expr * arg2, expr_ref & result) { return mk_bv_sdiv_core(arg1, arg2, m_hi_div0, result); }
    br_status mk_bv_udiv(expr * arg1, expr * arg2, expr_ref & result) { return mk_bv_udiv_core(arg1, arg2, m_hi_div0, result); }
    br_status mk_bv_srem(expr * arg1, expr * arg2, expr_ref & result) { return mk_bv_srem_core(arg1, arg2, m_hi_div0, result); }
    br_status mk_bv_urem(expr * arg1, expr * arg2, expr_ref & result) { return mk_bv_urem_core(arg1, arg2, m_hi_div0, result); }
    br_status mk_bv_smod(expr * arg1, expr * arg2, expr_ref & result) { return mk_bv_smod_core(arg1, arg2, m_hi_div0, result); }
    br_status mk_bv_sdiv_i(expr * arg1, expr * arg2, expr_ref & result) { return mk_bv_sdiv_core(arg1, arg2, true, result); }
    br_status mk_bv_udiv_i(expr * arg1, expr * arg2, expr_ref & result) { return mk_bv_udiv_core(arg1, arg2, true, result); }
    br_status mk_bv_srem_i(expr * arg1, expr * arg2, expr_ref & result) { return mk_bv_srem_core(arg1, arg2, true, result); }
    br_status mk_bv_urem_i(expr * arg1, expr * arg2, expr_ref & result) { return mk_bv_urem_core(arg1, arg2, true, result); }
    br_status mk_bv_smod_i(expr * arg1, expr * arg2, expr_ref & result) { return mk_bv_smod_core(arg1, arg2, true, result); }
    br_status mk_int2bv(unsigned bv_size, expr * arg, expr_ref & result);
    br_status mk_bv2int(expr * arg, expr_ref & result);
    br_status mk_bv_redor(expr * arg, expr_ref & result);
    br_status mk_bv_redand(expr * arg, expr_ref & result);
    br_status mk_bv_comp(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_bit2bool(expr * lhs, expr * rhs, expr_ref & result);
    br_status mk_blast_eq_value(expr * lhs, expr * rhs, expr_ref & result);
    br_status mk_eq_concat(expr * lhs, expr * rhs, expr_ref & result);
    br_status mk_mkbv(unsigned num, expr * const * args, expr_ref & result);
    br_status mk_bvsmul_no_overflow(unsigned num, expr * const * args, expr_ref & result);
    br_status mk_bvumul_no_overflow(unsigned num, expr * const * args, expr_ref & result);
    br_status mk_bvsmul_no_underflow(unsigned num, expr * const * args, expr_ref & result);
    bool is_minus_one_times_t(expr * arg);
    void mk_t1_add_t2_eq_c(expr * t1, expr * t2, expr * c, expr_ref & result);

    bool is_concat_split_target(expr * t) const;

    br_status mk_mul_eq(expr * lhs, expr * rhs, expr_ref & result);
    bool is_add_mul_const(expr* e) const;
    bool isolate_term(expr* lhs, expr* rhs, expr_ref & result);
    bool has_numeral(app* e) const;
    bool is_concat_target(expr* lhs, expr* rhs) const;

    void updt_local_params(params_ref const & p);

    expr * concat(unsigned num_args, expr * const * args);
public:
    bv_rewriter(ast_manager & m, params_ref const & p = params_ref()):
        poly_rewriter<bv_rewriter_core>(m, p),
        m_mk_extract(m_util),
        m_rm_trailing(m_mk_extract),
        m_autil(m) {
        updt_local_params(p);
    }

    void updt_params(params_ref const & p);

    static void get_param_descrs(param_descrs & r);

    void set_mkbv2num(bool f) { m_mkbv2num = f; }

    unsigned get_bv_size(expr * t) const {return m_util.get_bv_size(t); }
    bool is_numeral(expr * t) const { return m_util.is_numeral(t); }
    bool is_numeral(expr * t, numeral & r, unsigned & sz) const { return m_util.is_numeral(t, r, sz); }
    bool is_bv(expr * t) const { return m_util.is_bv(t); }
    expr * mk_numeral(numeral const & v, unsigned sz) { return m_util.mk_numeral(v, sz); }
    expr * mk_numeral(unsigned v, unsigned sz) { return m_util.mk_numeral(numeral(v), sz); }

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    void mk_app(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
        if (mk_app_core(f, num_args, args, result) == BR_FAILED)
            result = m().mk_app(f, num_args, args);
    }

    bool is_urem_any(expr * e, expr * & dividend,  expr * & divisor);
    br_status mk_eq_core(expr * lhs, expr * rhs, expr_ref & result);
    br_status mk_ite_core(expr * c, expr * t, expr * e, expr_ref & resul);

    bool hi_div0() const { return m_hi_div0; }

    bv_util & get_util() { return m_util; }

#define MK_BV_BINARY(OP)                         \
    expr_ref OP(expr* a, expr* b) {              \
        expr_ref result(m());                    \
        if (BR_FAILED == OP(a, b, result))       \
            result = m_util.OP(a, b);            \
        return result;                           \
    }                                            \
    
    expr_ref mk_zero_extend(unsigned n, expr * arg) {       
        expr_ref result(m());                   
        if (BR_FAILED == mk_zero_extend(n, arg, result))    
            result = m_util.mk_zero_extend(n, arg);         
        return result;                          
    }                                           

    MK_BV_BINARY(mk_bv_urem);
    MK_BV_BINARY(mk_ule);
    MK_BV_BINARY(mk_bv_add);
    MK_BV_BINARY(mk_bv_mul);
    MK_BV_BINARY(mk_bv_sub);


    expr_ref mk_bv2int(expr* a) {
        expr_ref result(m());
        if (BR_FAILED == mk_bv2int(a, result)) 
            result = m_util.mk_bv2int(a);
        return result;        
    }



};

#endif
