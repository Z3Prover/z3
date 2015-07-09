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

#include"poly_rewriter.h"
#include"bv_decl_plugin.h"
#include"arith_decl_plugin.h"

class mk_extract_proc {
    bv_util &     m_util;
    unsigned      m_high;
    unsigned      m_low;
    sort *        m_domain;
    func_decl *   m_f_cached;
public:
    mk_extract_proc(bv_util & u);
    ~mk_extract_proc();
    app * operator()(unsigned high, unsigned low, expr * arg);
};

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
    arith_util m_autil;
    bool       m_hi_div0;
    bool       m_elim_sign_ext;
    bool       m_mul2concat;
    bool       m_bit2bool;
    bool       m_blast_eq_value;
    bool       m_mkbv2num;
    bool       m_split_concat_eq;
    bool       m_udiv2mul;
    bool       m_bvnot2arith;
    bool       m_bv_sort_ac;

    bool is_zero_bit(expr * x, unsigned idx);

    br_status mk_ule(expr * a, expr * b, expr_ref & result);
    br_status mk_uge(expr * a, expr * b, expr_ref & result);
    br_status mk_ult(expr * a, expr * b, expr_ref & result);
    br_status mk_sle(expr * a, expr * b, expr_ref & result);
    br_status mk_sge(expr * a, expr * b, expr_ref & result);
    br_status mk_slt(expr * a, expr * b, expr_ref & result);
    br_status mk_leq_core(bool is_signed, expr * a, expr * b, expr_ref & result);

    br_status mk_concat(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_extract(unsigned high, unsigned low, expr * arg, expr_ref & result);
    br_status mk_repeat(unsigned n, expr * arg, expr_ref & result);
    br_status mk_zero_extend(unsigned n, expr * arg, expr_ref & result);
    br_status mk_sign_extend(unsigned n, expr * arg, expr_ref & result);
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
    br_status mk_bv_add(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_bv_add(expr * arg1, expr * arg2, expr_ref & result) {
        expr * args[2] = { arg1, arg2 };
        return mk_bv_add(2, args, result);
    }
    br_status mk_bv_mul(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_bv_shl(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_bv_lshr(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_bv_ashr(expr * arg1, expr * arg2, expr_ref & result);
    bool is_minus_one_core(expr * arg) const;
    bool is_x_minus_one(expr * arg, expr * & x);
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
    bool is_minus_one_times_t(expr * arg);
    void mk_t1_add_t2_eq_c(expr * t1, expr * t2, expr * c, expr_ref & result);

    bool is_concat_split_target(expr * t) const;

    br_status mk_mul_eq(expr * lhs, expr * rhs, expr_ref & result);

    void updt_local_params(params_ref const & p);

public:
    bv_rewriter(ast_manager & m, params_ref const & p = params_ref()):
        poly_rewriter<bv_rewriter_core>(m, p),
        m_mk_extract(m_util),
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

    br_status mk_eq_core(expr * lhs, expr * rhs, expr_ref & result);
};

#endif
