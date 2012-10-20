/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    float_decl_plugin.h

Abstract:

    Floating point decl plugin

Author:

    Leonardo de Moura (leonardo) 2012-01-15.

Revision History:

--*/
#ifndef _FLOAT_DECL_PLUGIN_H_
#define _FLOAT_DECL_PLUGIN_H_

#include"ast.h"
#include"id_gen.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"mpf.h"
 
enum float_sort_kind {
    FLOAT_SORT,
    ROUNDING_MODE_SORT
};

enum float_op_kind {
    OP_RM_NEAREST_TIES_TO_EVEN,
    OP_RM_NEAREST_TIES_TO_AWAY,
    OP_RM_TOWARD_POSITIVE,
    OP_RM_TOWARD_NEGATIVE,
    OP_RM_TOWARD_ZERO,

    
    OP_FLOAT_VALUE,
    OP_FLOAT_PLUS_INF,
    OP_FLOAT_MINUS_INF,
    OP_FLOAT_NAN,
    
    OP_FLOAT_ADD,
    OP_FLOAT_SUB,
    OP_FLOAT_UMINUS,
    OP_FLOAT_MUL,
    OP_FLOAT_DIV,
    OP_FLOAT_REM,
    OP_FLOAT_ABS,
    OP_FLOAT_MIN,
    OP_FLOAT_MAX,
    OP_FLOAT_FUSED_MA, // x*y + z
    OP_FLOAT_SQRT,
    OP_FLOAT_ROUND_TO_INTEGRAL,

    OP_FLOAT_EQ,
    OP_FLOAT_LT,
    OP_FLOAT_GT,
    OP_FLOAT_LE,
    OP_FLOAT_GE,
    OP_FLOAT_IS_ZERO,
    OP_FLOAT_IS_NZERO,
    OP_FLOAT_IS_PZERO,
    OP_FLOAT_IS_SIGN_MINUS,

    OP_TO_FLOAT,
    
    LAST_FLOAT_OP
};

class float_decl_plugin : public decl_plugin {
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
    func_decl * mk_fused_ma(decl_kind k, unsigned num_parameters, parameter const * parameters,
                            unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_to_float(decl_kind k, unsigned num_parameters, parameter const * parameters,
                            unsigned arity, sort * const * domain, sort * range);

    virtual void set_manager(ast_manager * m, family_id id);
    unsigned mk_id(mpf const & v);
    void recycled_id(unsigned id);
public:
    float_decl_plugin();
    
    bool is_float_sort(sort * s) const { return is_sort_of(s, m_family_id, FLOAT_SORT); }
    bool is_rm_sort(sort * s) const { return is_sort_of(s, m_family_id, ROUNDING_MODE_SORT); }

    virtual ~float_decl_plugin();
    virtual void finalize();
    
    virtual decl_plugin * mk_fresh();
    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters);
    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                     unsigned arity, sort * const * domain, sort * range);
    virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);
    virtual void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic);
    virtual bool is_value(app* e) const;
    
    mpf_manager & fm() { return m_fm; }
    func_decl * mk_value_decl(mpf const & v);
    app * mk_value(mpf const & v);
    bool is_value(expr * n) { return is_app_of(n, m_family_id, OP_FLOAT_VALUE); }
    bool is_value(expr * n, mpf & val);
    bool is_rm(expr * n, mpf_rounding_mode & val);

    mpf const & get_value(unsigned id) const { 
        SASSERT(m_value_table.contains(id));
        return m_values[id];
    }

    virtual void del(parameter const & p);
    virtual parameter translate(parameter const & p, decl_plugin & target);
};

class float_util {
    ast_manager &       m_manager;
    float_decl_plugin * m_plugin;
    family_id           m_fid;
    arith_util          m_a_util;
public:
    float_util(ast_manager & m);
    ~float_util();

    ast_manager & m() const { return m_manager; }
    mpf_manager & fm() const { return m_plugin->fm(); }
    family_id get_fid() const { return m_fid; }
    family_id get_family_id() const { return m_fid; }
    arith_util & au() { return m_a_util; }

    sort * mk_float_sort(unsigned ebits, unsigned sbits);
    sort * mk_rm_sort() { return m().mk_sort(m_fid, ROUNDING_MODE_SORT); }
    bool is_float(sort * s) { return is_sort_of(s, m_fid, FLOAT_SORT); }
    bool is_rm(sort * s) { return is_sort_of(s, m_fid, ROUNDING_MODE_SORT); }    
    unsigned get_ebits(sort * s);
    unsigned get_sbits(sort * s);

    app * mk_round_nearest_ties_to_even() { return m().mk_const(m_fid, OP_RM_NEAREST_TIES_TO_EVEN); }
    app * mk_round_nearest_ties_to_away() { return m().mk_const(m_fid, OP_RM_NEAREST_TIES_TO_AWAY); }
    app * mk_round_toward_positive() { return m().mk_const(m_fid, OP_RM_TOWARD_POSITIVE); }
    app * mk_round_toward_negative() { return m().mk_const(m_fid, OP_RM_TOWARD_NEGATIVE); }
    app * mk_round_toward_zero() { return m().mk_const(m_fid, OP_RM_TOWARD_ZERO); }

    app * mk_nan(unsigned ebits, unsigned sbits);
    app * mk_plus_inf(unsigned ebits, unsigned sbits);
    app * mk_minus_inf(unsigned ebits, unsigned sbits);
    app * mk_nan(sort * s) { return mk_nan(get_ebits(s), get_sbits(s)); }
    app * mk_plus_inf(sort * s) { return mk_plus_inf(get_ebits(s), get_sbits(s)); }
    app * mk_minus_inf(sort * s) { return mk_minus_inf(get_ebits(s), get_sbits(s)); }

    app * mk_value(mpf const & v) { return m_plugin->mk_value(v); }
    bool is_value(expr * n) { return m_plugin->is_value(n); }
    bool is_value(expr * n, mpf & v) { return m_plugin->is_value(n, v); }    
    bool is_rm(expr * n, mpf_rounding_mode & v) { return m_plugin->is_rm(n, v); }

    app * mk_pzero(unsigned ebits, unsigned sbits);
    app * mk_nzero(unsigned ebits, unsigned sbits);
    app * mk_pzero(sort * s) { return mk_pzero(get_ebits(s), get_sbits(s)); }
    app * mk_nzero(sort * s) { return mk_nzero(get_ebits(s), get_sbits(s)); }

    bool is_nan(expr * n) { scoped_mpf v(fm()); return is_value(n, v) && fm().is_nan(v); } 
    bool is_plus_inf(expr * n) { scoped_mpf v(fm()); return is_value(n, v) && fm().is_pinf(v); }
    bool is_minus_inf(expr * n) { scoped_mpf v(fm()); return is_value(n, v) && fm().is_ninf(v); }
    bool is_zero(expr * n) { scoped_mpf v(fm()); return is_value(n, v) && fm().is_zero(v); }
    bool is_pzero(expr * n) { scoped_mpf v(fm()); return is_value(n, v) && fm().is_pzero(v); }
    bool is_nzero(expr * n) { scoped_mpf v(fm()); return is_value(n, v) && fm().is_nzero(v); }

    bool is_to_float(expr * n) { return is_app_of(n, m_fid, OP_TO_FLOAT); }

    app * mk_to_float(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_TO_FLOAT, arg1, arg2); }
    app * mk_add(expr * arg1, expr * arg2, expr * arg3) { return m().mk_app(m_fid, OP_FLOAT_ADD, arg1, arg2, arg3); }
    app * mk_mul(expr * arg1, expr * arg2, expr * arg3) { return m().mk_app(m_fid, OP_FLOAT_MUL, arg1, arg2, arg3); }
    app * mk_sub(expr * arg1, expr * arg2, expr * arg3) { return m().mk_app(m_fid, OP_FLOAT_SUB, arg1, arg2, arg3); }
    app * mk_div(expr * arg1, expr * arg2, expr * arg3) { return m().mk_app(m_fid, OP_FLOAT_DIV, arg1, arg2, arg3); }
    app * mk_uminus(expr * arg1) { return m().mk_app(m_fid, OP_FLOAT_UMINUS, arg1); }
    app * mk_rem(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FLOAT_REM, arg1, arg2); }
    app * mk_max(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FLOAT_MAX, arg1, arg2); }
    app * mk_min(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FLOAT_MIN, arg1, arg2); }
    app * mk_abs(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FLOAT_ABS, arg1, arg2); }
    app * mk_sqrt(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FLOAT_SQRT, arg1, arg2); }
    app * mk_round(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FLOAT_ROUND_TO_INTEGRAL, arg1, arg2); }
    app * mk_fused_ma(expr * arg1, expr * arg2, expr * arg3, expr * arg4) {
        expr * args[4] = { arg1, arg2, arg3, arg4 };
        return m().mk_app(m_fid, OP_FLOAT_FUSED_MA, 4, args);
    }

    app * mk_float_eq(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FLOAT_EQ, arg1, arg2); }
    app * mk_lt(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FLOAT_LT, arg1, arg2); }
    app * mk_gt(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FLOAT_GT, arg1, arg2); }
    app * mk_le(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FLOAT_LE, arg1, arg2); }
    app * mk_ge(expr * arg1, expr * arg2) { return m().mk_app(m_fid, OP_FLOAT_GE, arg1, arg2); }

    app * mk_is_zero(expr * arg1) { return m().mk_app(m_fid, OP_FLOAT_IS_ZERO, arg1); }
    app * mk_is_nzero(expr * arg1) { return m().mk_app(m_fid, OP_FLOAT_IS_NZERO, arg1); }
    app * mk_is_pzero(expr * arg1) { return m().mk_app(m_fid, OP_FLOAT_IS_PZERO, arg1); }
    app * mk_is_sign_minus(expr * arg1) { return m().mk_app(m_fid, OP_FLOAT_IS_SIGN_MINUS, arg1); }

    bool is_uminus(expr * a) { return is_app_of(a, m_fid, OP_FLOAT_UMINUS); }
};

#endif
