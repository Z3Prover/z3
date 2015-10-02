/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    arith_decl_plugin.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-09

Revision History:

--*/
#ifndef ARITH_DECL_PLUGIN_H_
#define ARITH_DECL_PLUGIN_H_

#include"ast.h"
class sexpr;

namespace algebraic_numbers {
    class anum;
    class manager;
};

enum arith_sort_kind {
    REAL_SORT,
    INT_SORT
};

enum arith_op_kind {
    OP_NUM, // rational & integers
    OP_IRRATIONAL_ALGEBRAIC_NUM,  // irrationals that are roots of polynomials with integer coefficients
    //
    OP_LE,
    OP_GE,
    OP_LT,
    OP_GT,
    OP_ADD,
    OP_SUB,
    OP_UMINUS,
    OP_MUL,
    OP_DIV,
    OP_IDIV,
    OP_REM,
    OP_MOD,
    OP_TO_REAL,
    OP_TO_INT,
    OP_IS_INT,
    OP_ABS,
    OP_POWER,
    // hyperbolic and trigonometric functions
    OP_SIN,
    OP_COS,
    OP_TAN,
    OP_ASIN,
    OP_ACOS,
    OP_ATAN,
    OP_SINH,
    OP_COSH,
    OP_TANH,
    OP_ASINH,
    OP_ACOSH,
    OP_ATANH,
    // constants
    OP_PI,
    OP_E,
    // under-specified symbols
    OP_0_PW_0_INT,    // 0^0 for integers
    OP_0_PW_0_REAL,   // 0^0 for reals
    OP_NEG_ROOT,      // x^n when n is even and x is negative
    OP_DIV_0,         // x/0
    OP_IDIV_0,        // x div 0
    OP_MOD_0,         // x mod 0
    OP_U_ASIN,        // asin(x) for x < -1 or x > 1
    OP_U_ACOS,        // acos(x) for x < -1 or x > 1
    LAST_ARITH_OP
};

class arith_util;

class arith_decl_plugin : public decl_plugin {
protected:
    struct algebraic_numbers_wrapper;
    algebraic_numbers_wrapper * m_aw;
    symbol      m_intv_sym;
    symbol      m_realv_sym;
    symbol      m_rootv_sym;
    sort *      m_real_decl;
    sort *      m_int_decl;
    func_decl * m_r_le_decl;
    func_decl * m_r_ge_decl;
    func_decl * m_r_lt_decl;
    func_decl * m_r_gt_decl;

    func_decl * m_r_add_decl;
    func_decl * m_r_sub_decl;
    func_decl * m_r_uminus_decl;
    func_decl * m_r_mul_decl;
    func_decl * m_r_div_decl;

    func_decl * m_i_le_decl;
    func_decl * m_i_ge_decl;
    func_decl * m_i_lt_decl;
    func_decl * m_i_gt_decl;

    func_decl * m_i_add_decl;
    func_decl * m_i_sub_decl;
    func_decl * m_i_uminus_decl;
    func_decl * m_i_mul_decl;
    func_decl * m_i_div_decl;
    func_decl * m_i_mod_decl;
    func_decl * m_i_rem_decl;
    
    func_decl * m_to_real_decl;
    func_decl * m_to_int_decl;
    func_decl * m_is_int_decl;
    func_decl * m_r_power_decl;
    func_decl * m_i_power_decl;

    func_decl * m_r_abs_decl;
    func_decl * m_i_abs_decl;

    func_decl * m_sin_decl;
    func_decl * m_cos_decl;
    func_decl * m_tan_decl;
    func_decl * m_asin_decl;
    func_decl * m_acos_decl;
    func_decl * m_atan_decl;
    func_decl * m_sinh_decl;
    func_decl * m_cosh_decl;
    func_decl * m_tanh_decl;
    func_decl * m_asinh_decl;
    func_decl * m_acosh_decl;
    func_decl * m_atanh_decl;

    app       * m_pi;
    app       * m_e;
 
    app       * m_0_pw_0_int;
    app       * m_0_pw_0_real;
    func_decl * m_neg_root_decl;
    func_decl * m_div_0_decl;
    func_decl * m_idiv_0_decl;
    func_decl * m_mod_0_decl;
    func_decl * m_u_asin_decl;
    func_decl * m_u_acos_decl;
   
    ptr_vector<app> m_small_ints;
    ptr_vector<app> m_small_reals;

    func_decl * mk_func_decl(decl_kind k, bool is_real);
    virtual void set_manager(ast_manager * m, family_id id);
    decl_kind fix_kind(decl_kind k, unsigned arity);
    func_decl * mk_num_decl(unsigned num_parameters, parameter const * parameters, unsigned arity);

public:
    arith_decl_plugin();

    virtual ~arith_decl_plugin();
    virtual void finalize();

    algebraic_numbers::manager & am() const;
    algebraic_numbers_wrapper & aw() const;

    virtual void del(parameter const & p);
    virtual parameter translate(parameter const & p, decl_plugin & target);

    virtual decl_plugin * mk_fresh() {
        return alloc(arith_decl_plugin);
    }

    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters);
    
    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                     unsigned arity, sort * const * domain, sort * range);

    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                     unsigned num_args, expr * const * args, sort * range);

    virtual bool is_value(app * e) const;

    virtual bool is_unique_value(app * e) const;

    virtual bool are_equal(app * a, app * b) const;

    virtual bool are_distinct(app * a, app * b) const;

    virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);

    virtual void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic);

    app * mk_numeral(rational const & n, bool is_int);

    app * mk_numeral(algebraic_numbers::anum const & val, bool is_int);

    // Create a (real) numeral that is the i-th root of the polynomial encoded using the given sexpr.
    app * mk_numeral(sexpr const * p, unsigned i);

    app * mk_pi() const { return m_pi; }
    
    app * mk_e() const { return m_e; }

    app * mk_0_pw_0_int() const { return m_0_pw_0_int; }
    
    app * mk_0_pw_0_real() const { return m_0_pw_0_real; }

    virtual expr * get_some_value(sort * s);

    virtual void set_cancel(bool f);
};

/**
   \brief Procedures for recognizing arithmetic expressions.
   We don't need access to ast_manager, and operations can be simultaneously
   executed in different threads.
*/
class arith_recognizers {
protected:
    family_id           m_afid;
public:
    arith_recognizers(family_id id):m_afid(id) {}

    family_id get_family_id() const { return m_afid; }

    bool is_arith_expr(expr const * n) const { return is_app(n) && to_app(n)->get_family_id() == m_afid; }
    bool is_irrational_algebraic_numeral(expr const * n) const { return is_app_of(n, m_afid, OP_IRRATIONAL_ALGEBRAIC_NUM); }
    bool is_numeral(expr const * n, rational & val, bool & is_int) const;
    bool is_numeral(expr const * n, rational & val) const { bool is_int; return is_numeral(n, val, is_int); }
    bool is_numeral(expr const * n) const { return is_app_of(n, m_afid, OP_NUM); }
    bool is_zero(expr const * n) const { rational val; return is_numeral(n, val) && val.is_zero(); }
    bool is_minus_one(expr * n) const { rational tmp; return is_numeral(n, tmp) && tmp.is_minus_one(); }
    // return true if \c n is a term of the form (* -1 r)
    bool is_times_minus_one(expr * n, expr * & r) const {
        if (is_mul(n) && to_app(n)->get_num_args() == 2 && is_minus_one(to_app(n)->get_arg(0))) {
            r = to_app(n)->get_arg(1);
            return true;
        }
        return false;
    }

    bool is_le(expr const * n) const { return is_app_of(n, m_afid, OP_LE); }
    bool is_ge(expr const * n) const { return is_app_of(n, m_afid, OP_GE); }
    bool is_lt(expr const * n) const { return is_app_of(n, m_afid, OP_LT); }
    bool is_gt(expr const * n) const { return is_app_of(n, m_afid, OP_GT); }
    bool is_add(expr const * n) const { return is_app_of(n, m_afid, OP_ADD); }
    bool is_sub(expr const * n) const { return is_app_of(n, m_afid, OP_SUB); }
    bool is_uminus(expr const * n) const { return is_app_of(n, m_afid, OP_UMINUS); }
    bool is_mul(expr const * n) const { return is_app_of(n, m_afid, OP_MUL); }
    bool is_div(expr const * n) const { return is_app_of(n, m_afid, OP_DIV); }
    bool is_idiv(expr const * n) const { return is_app_of(n, m_afid, OP_IDIV); }
    bool is_mod(expr const * n) const { return is_app_of(n, m_afid, OP_MOD); }
    bool is_rem(expr const * n) const { return is_app_of(n, m_afid, OP_REM); }
    bool is_to_real(expr const * n) const { return is_app_of(n, m_afid, OP_TO_REAL); }
    bool is_to_int(expr const * n) const { return is_app_of(n, m_afid, OP_TO_INT); }
    bool is_is_int(expr const * n) const { return is_app_of(n, m_afid, OP_IS_INT); }
    bool is_power(expr const * n) const { return is_app_of(n, m_afid, OP_POWER); }
    
    bool is_int(sort const * s) const { return is_sort_of(s, m_afid, INT_SORT); }
    bool is_int(expr const * n) const { return is_int(get_sort(n)); }
    bool is_real(sort const * s) const { return is_sort_of(s, m_afid, REAL_SORT); }
    bool is_real(expr const * n) const { return is_real(get_sort(n)); }
    bool is_int_real(sort const * s) const { return s->get_family_id() == m_afid; }
    bool is_int_real(expr const * n) const { return is_int_real(get_sort(n)); }

    MATCH_UNARY(is_uminus);
    MATCH_UNARY(is_to_real);
    MATCH_UNARY(is_to_int);
    MATCH_BINARY(is_sub);
    MATCH_BINARY(is_add);
    MATCH_BINARY(is_mul);
    MATCH_BINARY(is_le);
    MATCH_BINARY(is_ge);
    MATCH_BINARY(is_lt);
    MATCH_BINARY(is_gt);    
    MATCH_BINARY(is_mod);
    MATCH_BINARY(is_rem);
    MATCH_BINARY(is_div);
    MATCH_BINARY(is_idiv);

    bool is_pi(expr * arg) { return is_app_of(arg, m_afid, OP_PI); }
    bool is_e(expr * arg) { return is_app_of(arg, m_afid, OP_E); }
};

class arith_util : public arith_recognizers {
    ast_manager &       m_manager;
    arith_decl_plugin * m_plugin;

    void init_plugin();

    arith_decl_plugin & plugin() const {
        if (!m_plugin) const_cast<arith_util*>(this)->init_plugin();
        SASSERT(m_plugin != 0);
        return *m_plugin;
    }
    
public:
    arith_util(ast_manager & m);

    ast_manager & get_manager() const { return m_manager; }

    algebraic_numbers::manager & am() { 
        return plugin().am(); 
    }

    bool is_irrational_algebraic_numeral(expr const * n) const { return is_app_of(n, m_afid, OP_IRRATIONAL_ALGEBRAIC_NUM); }
    bool is_irrational_algebraic_numeral(expr const * n, algebraic_numbers::anum & val);
    algebraic_numbers::anum const & to_irrational_algebraic_numeral(expr const * n);
    
    sort * mk_int() { return m_manager.mk_sort(m_afid, INT_SORT); }
    sort * mk_real() { return m_manager.mk_sort(m_afid, REAL_SORT); }

    app * mk_numeral(rational const & val, bool is_int) const { 
        return plugin().mk_numeral(val, is_int); 
    }
    app * mk_numeral(rational const & val, sort const * s) const {
        SASSERT(is_int(s) || is_real(s));
        return mk_numeral(val, is_int(s));
    }
    app * mk_numeral(algebraic_numbers::anum const & val, bool is_int) {
        return plugin().mk_numeral(val, is_int);
    }
    app * mk_numeral(sexpr const * p, unsigned i) {
        return plugin().mk_numeral(p, i);
    }
    app * mk_le(expr * arg1, expr * arg2) const { return m_manager.mk_app(m_afid, OP_LE, arg1, arg2); }
    app * mk_ge(expr * arg1, expr * arg2) const { return m_manager.mk_app(m_afid, OP_GE, arg1, arg2); }
    app * mk_lt(expr * arg1, expr * arg2) const { return m_manager.mk_app(m_afid, OP_LT, arg1, arg2); }
    app * mk_gt(expr * arg1, expr * arg2) const { return m_manager.mk_app(m_afid, OP_GT, arg1, arg2); }

    app * mk_add(unsigned num_args, expr * const * args) { return m_manager.mk_app(m_afid, OP_ADD, num_args, args); }
    app * mk_add(expr * arg1, expr * arg2) { return m_manager.mk_app(m_afid, OP_ADD, arg1, arg2); }
    app * mk_add(expr * arg1, expr * arg2, expr* arg3) { return m_manager.mk_app(m_afid, OP_ADD, arg1, arg2, arg3); }

    app * mk_sub(expr * arg1, expr * arg2) { return m_manager.mk_app(m_afid, OP_SUB, arg1, arg2); }
    app * mk_sub(unsigned num_args, expr * const * args) { return m_manager.mk_app(m_afid, OP_SUB, num_args, args); }
    app * mk_mul(expr * arg1, expr * arg2) { return m_manager.mk_app(m_afid, OP_MUL, arg1, arg2); }
    app * mk_mul(expr * arg1, expr * arg2, expr* arg3) { return m_manager.mk_app(m_afid, OP_MUL, arg1, arg2, arg3); }
    app * mk_mul(unsigned num_args, expr * const * args) { return m_manager.mk_app(m_afid, OP_MUL, num_args, args); }
    app * mk_uminus(expr * arg) { return m_manager.mk_app(m_afid, OP_UMINUS, arg); }
    app * mk_div(expr * arg1, expr * arg2) { return m_manager.mk_app(m_afid, OP_DIV, arg1, arg2); }
    app * mk_idiv(expr * arg1, expr * arg2) { return m_manager.mk_app(m_afid, OP_IDIV, arg1, arg2); }
    app * mk_rem(expr * arg1, expr * arg2) { return m_manager.mk_app(m_afid, OP_REM, arg1, arg2); }
    app * mk_mod(expr * arg1, expr * arg2) { return m_manager.mk_app(m_afid, OP_MOD, arg1, arg2); }
    app * mk_to_real(expr * arg1) { return m_manager.mk_app(m_afid, OP_TO_REAL, arg1); }
    app * mk_to_int(expr * arg1) { return m_manager.mk_app(m_afid, OP_TO_INT, arg1); }
    app * mk_is_int(expr * arg1) { return m_manager.mk_app(m_afid, OP_IS_INT, arg1); }
    app * mk_power(expr* arg1, expr* arg2) { return m_manager.mk_app(m_afid, OP_POWER, arg1, arg2); }

    app * mk_sin(expr * arg) { return m_manager.mk_app(m_afid, OP_SIN, arg); }
    app * mk_cos(expr * arg) { return m_manager.mk_app(m_afid, OP_COS, arg); }
    app * mk_tan(expr * arg) { return m_manager.mk_app(m_afid, OP_TAN, arg); }
    app * mk_asin(expr * arg) { return m_manager.mk_app(m_afid, OP_ASIN, arg); }
    app * mk_acos(expr * arg) { return m_manager.mk_app(m_afid, OP_ACOS, arg); }
    app * mk_atan(expr * arg) { return m_manager.mk_app(m_afid, OP_ATAN, arg); }

    app * mk_sinh(expr * arg) { return m_manager.mk_app(m_afid, OP_SINH, arg); }
    app * mk_cosh(expr * arg) { return m_manager.mk_app(m_afid, OP_COSH, arg); }
    app * mk_tanh(expr * arg) { return m_manager.mk_app(m_afid, OP_TANH, arg); }
    app * mk_asinh(expr * arg) { return m_manager.mk_app(m_afid, OP_ASINH, arg); }
    app * mk_acosh(expr * arg) { return m_manager.mk_app(m_afid, OP_ACOSH, arg); }
    app * mk_atanh(expr * arg) { return m_manager.mk_app(m_afid, OP_ATANH, arg); }

    app * mk_pi() { return plugin().mk_pi(); }
    app * mk_e()  { return plugin().mk_e(); }

    app * mk_0_pw_0_int() { return plugin().mk_0_pw_0_int(); }
    app * mk_0_pw_0_real() { return plugin().mk_0_pw_0_real(); }
    app * mk_div0(expr * arg) { return m_manager.mk_app(m_afid, OP_DIV_0, arg); }
    app * mk_idiv0(expr * arg) { return m_manager.mk_app(m_afid, OP_IDIV_0, arg); }
    app * mk_mod0(expr * arg) { return m_manager.mk_app(m_afid, OP_MOD_0, arg); }
    app * mk_neg_root(expr * arg1, expr * arg2) { return m_manager.mk_app(m_afid, OP_NEG_ROOT, arg1, arg2); }
    app * mk_u_asin(expr * arg) { return m_manager.mk_app(m_afid, OP_U_ASIN, arg); }
    app * mk_u_acos(expr * arg) { return m_manager.mk_app(m_afid, OP_U_ACOS, arg); }
    
    /**
       \brief Return the equality (= lhs rhs), but it makes sure that 
       if one of the arguments is a numeral, then it will be in the right-hand-side;
       if none of them are numerals, then the left-hand-side has a smaller id than the right hand side.
    */
    app * mk_eq(expr * lhs, expr * rhs) {
        if (is_numeral(lhs) || (!is_numeral(rhs) && lhs->get_id() > rhs->get_id()))
            std::swap(lhs, rhs);
        if (lhs == rhs)
            return m_manager.mk_true();
        if (is_numeral(lhs) && is_numeral(rhs)) {
            SASSERT(lhs != rhs);
            return m_manager.mk_false();
        }
        return m_manager.mk_eq(lhs, rhs);
    }

    void set_cancel(bool f) {
        plugin().set_cancel(f);
    }
};

#endif /* ARITH_DECL_PLUGIN_H_ */

