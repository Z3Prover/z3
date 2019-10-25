/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa_decl_plugin.h

Abstract:

    Floating point decl plugin

Author:

    Leonardo de Moura (leonardo) 2012-01-15.

Revision History:

--*/
#ifndef fpa_decl_plugin_H_
#define fpa_decl_plugin_H_

#include "ast/ast.h"
#include "util/id_gen.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "util/mpf.h"

enum fpa_sort_kind {
    FLOATING_POINT_SORT,
    ROUNDING_MODE_SORT,
    FLOAT16_SORT,
    FLOAT32_SORT,
    FLOAT64_SORT,
    FLOAT128_SORT
};

typedef enum { BV_RM_TIES_TO_EVEN, BV_RM_TIES_TO_AWAY, BV_RM_TO_POSITIVE, BV_RM_TO_NEGATIVE, BV_RM_TO_ZERO = 4 } BV_RM_VAL;

enum fpa_op_kind {
    OP_FPA_RM_NEAREST_TIES_TO_EVEN,
    OP_FPA_RM_NEAREST_TIES_TO_AWAY,
    OP_FPA_RM_TOWARD_POSITIVE,
    OP_FPA_RM_TOWARD_NEGATIVE,
    OP_FPA_RM_TOWARD_ZERO,

    OP_FPA_NUM,
    OP_FPA_PLUS_INF,
    OP_FPA_MINUS_INF,
    OP_FPA_NAN,
    OP_FPA_PLUS_ZERO,
    OP_FPA_MINUS_ZERO,

    OP_FPA_ADD,
    OP_FPA_SUB,
    OP_FPA_NEG,
    OP_FPA_MUL,
    OP_FPA_DIV,
    OP_FPA_REM,
    OP_FPA_ABS,
    OP_FPA_MIN,
    OP_FPA_MAX,
    OP_FPA_FMA, // x*y + z
    OP_FPA_SQRT,
    OP_FPA_ROUND_TO_INTEGRAL,

    OP_FPA_EQ,
    OP_FPA_LT,
    OP_FPA_GT,
    OP_FPA_LE,
    OP_FPA_GE,
    OP_FPA_IS_NAN,
    OP_FPA_IS_INF,
    OP_FPA_IS_ZERO,
    OP_FPA_IS_NORMAL,
    OP_FPA_IS_SUBNORMAL,
    OP_FPA_IS_NEGATIVE,
    OP_FPA_IS_POSITIVE,

    OP_FPA_FP,
    OP_FPA_TO_FP,
    OP_FPA_TO_FP_UNSIGNED,
    OP_FPA_TO_UBV,
    OP_FPA_TO_SBV,
    OP_FPA_TO_REAL,

    /* Extensions */
    OP_FPA_TO_IEEE_BV,

    OP_FPA_BVWRAP,
    OP_FPA_BV2RM,

    LAST_FLOAT_OP
};

class fpa_decl_plugin : public decl_plugin {
    struct mpf_hash_proc {
        scoped_mpf_vector const & m_values;
        mpf_hash_proc(scoped_mpf_vector const & values):m_values(values) {}
        unsigned operator()(unsigned id) const { return m_values.m().hash(m_values[id]); }
    };

    struct mpf_eq_proc {
        scoped_mpf_vector const & m_values;
        mpf_eq_proc(scoped_mpf_vector const & values):m_values(values) {}
        bool operator()(unsigned id1, unsigned id2) const { return m_values.m().eq_core(m_values[id1], m_values[id2]); }
    };

    typedef chashtable<unsigned, mpf_hash_proc, mpf_eq_proc> value_table;


    mpf_manager         m_fm;
    id_gen              m_id_gen;
    scoped_mpf_vector   m_values;
    value_table         m_value_table;
    sort *              m_real_sort;
    sort *              m_int_sort;
    family_id           m_arith_fid;
    family_id           m_bv_fid;
    bv_decl_plugin *    m_bv_plugin;

    sort * mk_float_sort(unsigned ebits, unsigned sbits);
    sort * mk_rm_sort();

    func_decl * mk_rm_const_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                 unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_float_const_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                    unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_bin_rel_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_unary_rel_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                  unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_unary_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                              unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_binary_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                               unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_rm_binary_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                  unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_rm_unary_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                 unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_fma(decl_kind k, unsigned num_parameters, parameter const * parameters,
                       unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_fp(decl_kind k, unsigned num_parameters, parameter const * parameters,
                      unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_to_fp(decl_kind k, unsigned num_parameters, parameter const * parameters,
                         unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_to_fp_unsigned(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                  unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_to_ubv(decl_kind k, unsigned num_parameters, parameter const * parameters,
                          unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_to_sbv(decl_kind k, unsigned num_parameters, parameter const * parameters,
                          unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_to_real(decl_kind k, unsigned num_parameters, parameter const * parameters,
                           unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_to_ieee_bv(decl_kind k, unsigned num_parameters, parameter const * parameters,
                              unsigned arity, sort * const * domain, sort * range);

    func_decl * mk_bv2rm(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                  unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_bv_wrap(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                    unsigned arity, sort * const * domain, sort * range);

    void set_manager(ast_manager * m, family_id id) override;
    unsigned mk_id(mpf const & v);
    void recycled_id(unsigned id);

public:
    fpa_decl_plugin();

    bool is_float_sort(sort * s) const { return is_sort_of(s, m_family_id, FLOATING_POINT_SORT); }
    bool is_rm_sort(sort * s) const { return is_sort_of(s, m_family_id, ROUNDING_MODE_SORT); }

    ~fpa_decl_plugin() override;
    void finalize() override;

    decl_plugin * mk_fresh() override;
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;
    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range) override;
    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;
    expr * get_some_value(sort * s) override;
    bool is_value(app* e) const override;
    bool is_unique_value(app* e) const override;

    mpf_manager & fm() { return m_fm; }
    func_decl * mk_numeral_decl(mpf const & v);
    app * mk_numeral(mpf const & v);
    bool is_numeral(expr * n);
    bool is_numeral(expr * n, mpf & val);
    bool is_rm_numeral(expr * n, mpf_rounding_mode & val);
    bool is_rm_numeral(expr * n);

    mpf const & get_value(unsigned id) const {
        SASSERT(m_value_table.contains(id));
        return m_values[id];
    }

    void del(parameter const & p) override;
    parameter translate(parameter const & p, decl_plugin & target) override;

    bool is_considered_uninterpreted(func_decl * f) override;
};

class fpa_util {
    ast_manager     & m_manager;
    fpa_decl_plugin * m_plugin;
    family_id         m_fid;
    arith_util        m_a_util;
    bv_util           m_bv_util;

public:
    fpa_util(ast_manager & m);
    ~fpa_util();

    ast_manager & m() const { return m_manager; }
    mpf_manager & fm() const { return m_plugin->fm(); }
    family_id get_fid() const { return m_fid; }
    family_id get_family_id() const { return m_fid; }
    arith_util & au() { return m_a_util; }
    bv_util & bu() { return m_bv_util; }
    fpa_decl_plugin & plugin() { return *m_plugin; }

    sort * mk_float_sort(unsigned ebits, unsigned sbits);
    sort * mk_rm_sort() { return m().mk_sort(m_fid, ROUNDING_MODE_SORT); }
    bool is_float(sort * s) const { return is_sort_of(s, m_fid, FLOATING_POINT_SORT); }
    bool is_rm(sort * s) const { return is_sort_of(s, m_fid, ROUNDING_MODE_SORT); }
    bool is_float(expr * e) const { return is_float(m_manager.get_sort(e)); }
    bool is_rm(expr * e) const { return is_rm(m_manager.get_sort(e)); }
    bool is_fp(expr const * e) const { return is_app_of(e, m_fid, OP_FPA_FP); }
    unsigned get_ebits(sort * s) const;
    unsigned get_sbits(sort * s) const;

    app * mk_round_nearest_ties_to_even() { return m().mk_const(m_fid, OP_FPA_RM_NEAREST_TIES_TO_EVEN); }
    app * mk_round_nearest_ties_to_away() { return m().mk_const(m_fid, OP_FPA_RM_NEAREST_TIES_TO_AWAY); }
    app * mk_round_toward_positive() { return m().mk_const(m_fid, OP_FPA_RM_TOWARD_POSITIVE); }
    app * mk_round_toward_negative() { return m().mk_const(m_fid, OP_FPA_RM_TOWARD_NEGATIVE); }
    app * mk_round_toward_zero() { return m().mk_const(m_fid, OP_FPA_RM_TOWARD_ZERO); }

    app * mk_nan(unsigned ebits, unsigned sbits);
    app * mk_pinf(unsigned ebits, unsigned sbits);
    app * mk_ninf(unsigned ebits, unsigned sbits);
    app * mk_nan(sort * s) { return mk_nan(get_ebits(s), get_sbits(s)); }
    app * mk_pinf(sort * s) { return mk_pinf(get_ebits(s), get_sbits(s)); }
    app * mk_ninf(sort * s) { return mk_ninf(get_ebits(s), get_sbits(s)); }

    app * mk_value(mpf const & v) { return m_plugin->mk_numeral(v); }
    bool is_numeral(expr * n) { return m_plugin->is_numeral(n); }
    bool is_numeral(expr * n, mpf & v) { return m_plugin->is_numeral(n, v); }
    bool is_rm_numeral(expr * n) { return m_plugin->is_rm_numeral(n); }
    bool is_rm_numeral(expr * n, mpf_rounding_mode & v) { return m_plugin->is_rm_numeral(n, v); }

    app * mk_pzero(unsigned ebits, unsigned sbits);
    app * mk_nzero(unsigned ebits, unsigned sbits);
    app * mk_pzero(sort * s) { return mk_pzero(get_ebits(s), get_sbits(s)); }
    app * mk_nzero(sort * s) { return mk_nzero(get_ebits(s), get_sbits(s)); }

    bool is_nan(expr * n) { scoped_mpf v(fm()); return is_numeral(n, v) && fm().is_nan(v); }
    bool is_inf(expr * n) { scoped_mpf v(fm()); return is_numeral(n, v) && fm().is_inf(v); }
    bool is_pinf(expr * n) { scoped_mpf v(fm()); return is_numeral(n, v) && fm().is_pinf(v); }
    bool is_ninf(expr * n) { scoped_mpf v(fm()); return is_numeral(n, v) && fm().is_ninf(v); }
    bool is_zero(expr * n) { scoped_mpf v(fm()); return is_numeral(n, v) && fm().is_zero(v); }
    bool is_pzero(expr * n) { scoped_mpf v(fm()); return is_numeral(n, v) && fm().is_pzero(v); }
    bool is_nzero(expr * n) { scoped_mpf v(fm()); return is_numeral(n, v) && fm().is_nzero(v); }
    bool is_normal(expr * n) { scoped_mpf v(fm()); return is_numeral(n, v) && fm().is_normal(v); }
    bool is_subnormal(expr * n) { scoped_mpf v(fm()); return is_numeral(n, v) && fm().is_denormal(v); }
    bool is_positive(expr * n) { scoped_mpf v(fm()); return is_numeral(n, v) && fm().is_pos(v); }
    bool is_negative(expr * n) { scoped_mpf v(fm()); return is_numeral(n, v) && fm().is_neg(v); }

    app * mk_fp(expr * sgn, expr * exp, expr * sig) {
        SASSERT(m_bv_util.is_bv(sgn) && m_bv_util.get_bv_size(sgn) == 1);
        SASSERT(m_bv_util.is_bv(exp));
        SASSERT(m_bv_util.is_bv(sig));
        return m().mk_app(m_fid, OP_FPA_FP, sgn, exp, sig);
    }

    app * mk_to_fp(sort * s, expr * bv_t) {
        SASSERT(is_float(s) && s->get_num_parameters() == 2);
        return m().mk_app(m_fid, OP_FPA_TO_FP, 2, s->get_parameters(), 1, &bv_t);
    }
    app * mk_to_fp(sort * s, expr * rm, expr * t) {
        SASSERT(is_float(s) && s->get_num_parameters() == 2);
        expr * args[] = { rm, t };
        return m().mk_app(m_fid, OP_FPA_TO_FP, 2, s->get_parameters(), 2, args);
    }
    app * mk_to_fp(sort * s, expr * rm, expr * exp, expr * sig) {
        SASSERT(is_float(s) && s->get_num_parameters() == 2);
        expr * args[] = { rm, exp, sig};
        return m().mk_app(m_fid, OP_FPA_TO_FP, 2, s->get_parameters(), 3, args);
    }
    app * mk_to_fp_unsigned(sort * s, expr * rm, expr * t) {
        SASSERT(is_float(s) && s->get_num_parameters() == 2);
        expr * args[] = { rm, t };
        return m().mk_app(m_fid, OP_FPA_TO_FP_UNSIGNED, 2, s->get_parameters(), 2, args);
    }

    bool is_to_fp(expr * n) { return is_app_of(n, m_fid, OP_FPA_TO_FP); }

    app * mk_to_ubv(expr * rm, expr * t, unsigned sz) {
        parameter ps[] = { parameter(sz) };
        expr * args[] = { rm, t };
        return m().mk_app(m_fid, OP_FPA_TO_UBV, 1, ps, 2, args); }
    app * mk_to_sbv(expr * rm, expr * t, unsigned sz) {
        parameter ps[] = { parameter(sz) };
        expr * args[] = { rm, t };
        return m().mk_app(m_fid, OP_FPA_TO_SBV, 1, ps, 2, args);
    }
    app * mk_to_real(expr * t) { return m().mk_app(m_fid, OP_FPA_TO_REAL, t); }

    app * mk_add(expr * arg1, expr * arg2, expr * arg3) { return m().mk_app(m_fid, OP_FPA_ADD, arg1, arg2, arg3); }
    app * mk_mul(expr * arg1, expr * arg2, expr * arg3) { return m().mk_app(m_fid, OP_FPA_MUL, arg1, arg2, arg3); }
    app * mk_sub(expr * arg1, expr * arg2, expr * arg3) { return m().mk_app(m_fid, OP_FPA_SUB, arg1, arg2, arg3); }
    app * mk_div(expr * arg1, expr * arg2, expr * arg3) { return m().mk_app(m_fid, OP_FPA_DIV, arg1, arg2, arg3); }
    app * mk_neg(expr * arg1) { return m().mk_app(m_fid, OP_FPA_NEG, arg1); }
    app * mk_rem(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FPA_REM, arg1, arg2); }
    app * mk_max(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FPA_MAX, arg1, arg2); }
    app * mk_min(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FPA_MIN, arg1, arg2); }
    app * mk_abs(expr * arg1) { return m().mk_app(m_fid, OP_FPA_ABS, arg1); }
    app * mk_sqrt(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FPA_SQRT, arg1, arg2); }
    app * mk_round_to_integral(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FPA_ROUND_TO_INTEGRAL, arg1, arg2); }
    app * mk_fma(expr * arg1, expr * arg2, expr * arg3, expr * arg4) {
        expr * args[4] = { arg1, arg2, arg3, arg4 };
        return m().mk_app(m_fid, OP_FPA_FMA, 4, args);
    }

    app * mk_float_eq(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FPA_EQ, arg1, arg2); }
    app * mk_lt(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FPA_LT, arg1, arg2); }
    app * mk_gt(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FPA_GT, arg1, arg2); }
    app * mk_le(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FPA_LE, arg1, arg2); }
    app * mk_ge(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FPA_GE, arg1, arg2); }

    app * mk_is_nan(expr * arg1) { return m().mk_app(m_fid, OP_FPA_IS_NAN, arg1); }
    app * mk_is_inf(expr * arg1) { return m().mk_app(m_fid, OP_FPA_IS_INF, arg1); }
    app * mk_is_zero(expr * arg1) { return m().mk_app(m_fid, OP_FPA_IS_ZERO, arg1); }
    app * mk_is_normal(expr * arg1) { return m().mk_app(m_fid, OP_FPA_IS_NORMAL, arg1); }
    app * mk_is_subnormal(expr * arg1) { return m().mk_app(m_fid, OP_FPA_IS_SUBNORMAL, arg1); }
    app * mk_is_positive(expr * arg1) { return m().mk_app(m_fid, OP_FPA_IS_POSITIVE, arg1); }
    app * mk_is_negative(expr * arg1) { return m().mk_app(m_fid, OP_FPA_IS_NEGATIVE, arg1); }

    bool is_neg(expr * a) { return is_app_of(a, m_fid, OP_FPA_NEG); }

    app * mk_to_ieee_bv(expr * arg1) { return m().mk_app(m_fid, OP_FPA_TO_IEEE_BV, arg1); }

    app * mk_bv2rm(expr * bv3) {
        SASSERT(m_bv_util.is_bv(bv3) && m_bv_util.get_bv_size(bv3) == 3);
        return m().mk_app(m_fid, OP_FPA_BV2RM, 0, nullptr, 1, &bv3, mk_rm_sort());
    }

    bool is_bvwrap(expr const * e) const { return is_app_of(e, get_family_id(), OP_FPA_BVWRAP); }
    bool is_bv2rm(expr const * e) const { return is_app_of(e, get_family_id(), OP_FPA_BV2RM); }
    bool is_to_ubv(expr const * e) const { return is_app_of(e, get_family_id(), OP_FPA_TO_UBV); }
    bool is_to_sbv(expr const * e) const { return is_app_of(e, get_family_id(), OP_FPA_TO_SBV); }

    bool is_bvwrap(func_decl const * f) const { return f->get_family_id() == get_family_id() && f->get_decl_kind() == OP_FPA_BVWRAP; }
    bool is_bv2rm(func_decl const * f) const { return f->get_family_id() == get_family_id() && f->get_decl_kind() == OP_FPA_BV2RM; }
    bool is_to_ubv(func_decl const * f) const { return f->get_family_id() == get_family_id() && f->get_decl_kind() == OP_FPA_TO_UBV; }
    bool is_to_sbv(func_decl const * f) const { return f->get_family_id() == get_family_id() && f->get_decl_kind() == OP_FPA_TO_SBV; }
    bool is_to_ieee_bv(func_decl const * f) const { return f->get_family_id() == get_family_id() && f->get_decl_kind() == OP_FPA_TO_IEEE_BV; }

    bool contains_floats(ast * a);

    bool is_considered_uninterpreted(func_decl* f, unsigned n, expr* const* args);

    MATCH_TERNARY(is_fp);
};

#endif
