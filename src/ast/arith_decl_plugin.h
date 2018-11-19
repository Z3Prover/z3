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

#include "ast/ast.h"
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
    OP_IDIVIDES,
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
    OP_NEG_ROOT,      // x^n when n is even and x is negative
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

    func_decl * m_neg_root_decl;
    func_decl * m_u_asin_decl;
    func_decl * m_u_acos_decl;
    ptr_vector<app> m_small_ints;
    ptr_vector<app> m_small_reals;

    bool        m_convert_int_numerals_to_real;

    func_decl * mk_func_decl(decl_kind k, bool is_real);
    void set_manager(ast_manager * m, family_id id) override;
    decl_kind fix_kind(decl_kind k, unsigned arity);
    void check_arity(unsigned arity, unsigned expected_arity);
    func_decl * mk_num_decl(unsigned num_parameters, parameter const * parameters, unsigned arity);

public:
    arith_decl_plugin();

    ~arith_decl_plugin() override;
    void finalize() override;

    algebraic_numbers::manager & am() const;
    algebraic_numbers_wrapper & aw() const;

    void del(parameter const & p) override;
    parameter translate(parameter const & p, decl_plugin & target) override;

    decl_plugin * mk_fresh() override {
        return alloc(arith_decl_plugin);
    }

    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range) override;

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned num_args, expr * const * args, sort * range) override;

    bool is_value(app * e) const override;

    bool is_unique_value(app * e) const override;

    bool are_equal(app * a, app * b) const override;

    bool are_distinct(app * a, app * b) const override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;

    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    app * mk_numeral(rational const & n, bool is_int);

    app * mk_numeral(algebraic_numbers::anum const & val, bool is_int);

    // Create a (real) numeral that is the i-th root of the polynomial encoded using the given sexpr.
    app * mk_numeral(sexpr const * p, unsigned i);

    app * mk_pi() const { return m_pi; }

    app * mk_e() const { return m_e; }

    expr * get_some_value(sort * s) override;

    bool is_considered_uninterpreted(func_decl * f) override {
        if (f->get_family_id() != get_family_id())
            return false;
        switch (f->get_decl_kind())
        {
        case OP_NEG_ROOT:
        case OP_U_ASIN:
        case OP_U_ACOS:
            return true;
        default:
            return false;
        }
        return false;
    }
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
    bool is_irrational_algebraic_numeral(expr const * n) const;
    bool is_unsigned(expr const * n, unsigned& u) const { 
        rational val;
        bool is_int = true;
        return is_numeral(n, val, is_int) && is_int && val.is_unsigned(), u = val.get_unsigned(), true; 
    }
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

    bool is_int_expr(expr const * e) const;

    bool is_le(expr const * n) const { return is_app_of(n, m_afid, OP_LE); }
    bool is_ge(expr const * n) const { return is_app_of(n, m_afid, OP_GE); }
    bool is_lt(expr const * n) const { return is_app_of(n, m_afid, OP_LT); }
    bool is_gt(expr const * n) const { return is_app_of(n, m_afid, OP_GT); }
    bool is_le(func_decl const * n) const { return is_decl_of(n, m_afid, OP_LE); }
    bool is_ge(func_decl const * n) const { return is_decl_of(n, m_afid, OP_GE); }
    bool is_lt(func_decl const * n) const { return is_decl_of(n, m_afid, OP_LT); }
    bool is_gt(func_decl const * n) const { return is_decl_of(n, m_afid, OP_GT); }
    bool is_add(expr const * n) const { return is_app_of(n, m_afid, OP_ADD); }
    bool is_sub(expr const * n) const { return is_app_of(n, m_afid, OP_SUB); }
    bool is_uminus(expr const * n) const { return is_app_of(n, m_afid, OP_UMINUS); }
    bool is_mul(expr const * n) const { return is_app_of(n, m_afid, OP_MUL); }
    bool is_div(expr const * n) const { return is_app_of(n, m_afid, OP_DIV); }
    //bool is_div0(expr const * n) const { return is_app_of(n, m_afid, OP_DIV_0); }
    bool is_idiv(expr const * n) const { return is_app_of(n, m_afid, OP_IDIV); }
    //bool is_idiv0(expr const * n) const { return is_app_of(n, m_afid, OP_IDIV_0); }
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

    bool is_sin(expr const* n) const { return is_app_of(n, m_afid, OP_SIN); }
    bool is_cos(expr const* n) const { return is_app_of(n, m_afid, OP_COS); }
    bool is_tan(expr const* n) const { return is_app_of(n, m_afid, OP_TAN); }
    bool is_asin(expr const* n) const { return is_app_of(n, m_afid, OP_ASIN); }
    bool is_acos(expr const* n) const { return is_app_of(n, m_afid, OP_ACOS); }
    bool is_atan(expr const* n) const { return is_app_of(n, m_afid, OP_ATAN); }
    bool is_asinh(expr const* n) const { return is_app_of(n, m_afid, OP_ASINH); }
    bool is_acosh(expr const* n) const { return is_app_of(n, m_afid, OP_ACOSH); }
    bool is_atanh(expr const* n) const { return is_app_of(n, m_afid, OP_ATANH); }
    bool is_pi(expr * arg) { return is_app_of(arg, m_afid, OP_PI); }
    bool is_e(expr * arg) { return is_app_of(arg, m_afid, OP_E); }

    MATCH_UNARY(is_uminus);
    MATCH_UNARY(is_to_real);
    MATCH_UNARY(is_to_int);
    MATCH_UNARY(is_is_int);
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
    MATCH_BINARY(is_power);

    MATCH_UNARY(is_sin);
    MATCH_UNARY(is_asin);
    MATCH_UNARY(is_asinh);
    MATCH_UNARY(is_cos);
    MATCH_UNARY(is_acos);
    MATCH_UNARY(is_acosh);
    MATCH_UNARY(is_tan);
    MATCH_UNARY(is_atan);
    MATCH_UNARY(is_atanh);

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

    bool is_irrational_algebraic_numeral2(expr const * n, algebraic_numbers::anum & val);
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
    app * mk_int(int i) {
        return mk_numeral(rational(i), true);
    }
    app * mk_int(rational const& r) {
        return mk_numeral(r, true);
    }
    app * mk_real(int i) {
        return mk_numeral(rational(i), false);
    }
    app * mk_real(rational const& r) {
        return mk_numeral(r, false);
    }
    app * mk_le(expr * arg1, expr * arg2) const { return m_manager.mk_app(m_afid, OP_LE, arg1, arg2); }
    app * mk_ge(expr * arg1, expr * arg2) const { return m_manager.mk_app(m_afid, OP_GE, arg1, arg2); }
    app * mk_lt(expr * arg1, expr * arg2) const { return m_manager.mk_app(m_afid, OP_LT, arg1, arg2); }
    app * mk_gt(expr * arg1, expr * arg2) const { return m_manager.mk_app(m_afid, OP_GT, arg1, arg2); }

    app * mk_add(unsigned num_args, expr * const * args) const { return num_args == 1 && is_app(args[0]) ? to_app(args[0]) : m_manager.mk_app(m_afid, OP_ADD, num_args, args); }
    app * mk_add(expr * arg1, expr * arg2) const { return m_manager.mk_app(m_afid, OP_ADD, arg1, arg2); }
    app * mk_add(expr * arg1, expr * arg2, expr* arg3) const { return m_manager.mk_app(m_afid, OP_ADD, arg1, arg2, arg3); }

    app * mk_sub(expr * arg1, expr * arg2) const { return m_manager.mk_app(m_afid, OP_SUB, arg1, arg2); }
    app * mk_sub(unsigned num_args, expr * const * args) const { return m_manager.mk_app(m_afid, OP_SUB, num_args, args); }
    app * mk_mul(expr * arg1, expr * arg2) const { return m_manager.mk_app(m_afid, OP_MUL, arg1, arg2); }
    app * mk_mul(expr * arg1, expr * arg2, expr* arg3) const { return m_manager.mk_app(m_afid, OP_MUL, arg1, arg2, arg3); }
    app * mk_mul(unsigned num_args, expr * const * args) const { return num_args == 1 && is_app(args[0]) ? to_app(args[0]) : m_manager.mk_app(m_afid, OP_MUL, num_args, args); }
    app * mk_uminus(expr * arg) const { return m_manager.mk_app(m_afid, OP_UMINUS, arg); }
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

    expr_ref mk_mul_simplify(expr_ref_vector const& args);
    expr_ref mk_mul_simplify(unsigned sz, expr* const* args);

    expr_ref mk_add_simplify(expr_ref_vector const& args);
    expr_ref mk_add_simplify(unsigned sz, expr* const* args);
};


inline app_ref mk_numeral(rational const& r, app_ref const& x) {
    arith_util a(x.get_manager());
    return app_ref(a.mk_numeral(r, r.is_int() && a.is_int(x)), x.get_manager());
}

inline app_ref operator+(app_ref const& x, app_ref const& y) {
    arith_util a(x.get_manager());
    return app_ref(a.mk_add(x, y), x.get_manager());
}

inline app_ref operator+(app_ref const& x, rational const& y) {
    return x + mk_numeral(y, x);
}

inline app_ref operator+(app_ref const& x, int y) {
    return x + rational(y);
}

inline app_ref operator+(rational const& x, app_ref const& y) {
    return mk_numeral(x, y) + y;
}

inline app_ref operator+(int x, app_ref const& y) {
    return rational(x) + y;
}

inline app_ref operator-(app_ref const& x, app_ref const& y) {
    arith_util a(x.get_manager());
    return app_ref(a.mk_sub(x, y), x.get_manager());
}

inline app_ref operator-(app_ref const& x, rational const& y) {
    return x - mk_numeral(y, x);
}

inline app_ref operator-(app_ref const& x, int y) {
    return x - rational(y);
}

inline app_ref operator-(rational const& x, app_ref const& y) {
    return mk_numeral(x, y) - y;
}

inline app_ref operator-(int x, app_ref const& y) {
    return rational(x) - y;
}


inline app_ref operator*(app_ref const& x, app_ref const& y) {
    arith_util a(x.get_manager());
    return app_ref(a.mk_mul(x, y), x.get_manager());
}

inline app_ref operator*(app_ref const& x, rational const& y) {
    return x * mk_numeral(y, x);
}

inline app_ref operator*(rational const& x, app_ref const& y) {
    return mk_numeral(x, y) * y;
}

inline app_ref operator*(app_ref const& x, int y) {
    return x * rational(y);
}

inline app_ref operator*(int x, app_ref const& y) {
    return rational(x) * y;
}

inline app_ref operator<=(app_ref const& x, app_ref const& y) {
    arith_util a(x.get_manager());
    return app_ref(a.mk_le(x, y), x.get_manager());
}

inline app_ref operator<=(app_ref const& x, rational const& y) {
    return x <= mk_numeral(y, x);
}

inline app_ref operator<=(app_ref const& x, int y) {
    return x <= rational(y);
}

inline app_ref operator>=(app_ref const& x, app_ref const& y) {
    arith_util a(x.get_manager());
    return app_ref(a.mk_ge(x, y), x.get_manager());
}

inline app_ref operator<(app_ref const& x, app_ref const& y) {
    arith_util a(x.get_manager());
    return app_ref(a.mk_lt(x, y), x.get_manager());
}

inline app_ref operator>(app_ref const& x, app_ref const& y) {
    arith_util a(x.get_manager());
    return app_ref(a.mk_gt(x, y), x.get_manager());
}

#endif /* ARITH_DECL_PLUGIN_H_ */

