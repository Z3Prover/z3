/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    arith_decl_plugin.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-09

Revision History:

--*/
#include "ast/arith_decl_plugin.h"
#include "util/warning.h"
#include "math/polynomial/algebraic_numbers.h"
#include "util/id_gen.h"
#include "ast/ast_smt2_pp.h"
#include "util/gparams.h"

struct arith_decl_plugin::algebraic_numbers_wrapper {
    unsynch_mpq_manager           m_qmanager;
    algebraic_numbers::manager    m_amanager;
    id_gen                        m_id_gen;
    scoped_anum_vector            m_nums;

    algebraic_numbers_wrapper(reslimit& lim):
        m_amanager(lim, m_qmanager),
        m_nums(m_amanager) {
    }

    ~algebraic_numbers_wrapper() {
    }

    unsigned mk_id(algebraic_numbers::anum const & val) {
        SASSERT(!m_amanager.is_rational(val));
        unsigned new_id = m_id_gen.mk();
        m_nums.reserve(new_id+1);
        m_amanager.set(m_nums[new_id], val);
        TRACE("algebraic2expr", tout << "mk_id -> " << new_id << "\n"; m_amanager.display(tout, val); tout << "\n";);
        return new_id;
    }

    void recycle_id(unsigned idx) {
        SASSERT(idx < m_nums.size());
        SASSERT(!m_amanager.is_zero(m_nums[idx]));
        TRACE("algebraic2expr", tout << "recycling: " << idx << "\n";);
        m_id_gen.recycle(idx);
        m_amanager.del(m_nums[idx]);
    }

    algebraic_numbers::anum const & idx2anum(unsigned idx) {
        return m_nums[idx];
    }

    algebraic_numbers::anum const & to_anum(func_decl * f) {
        SASSERT(f->get_decl_kind() == OP_IRRATIONAL_ALGEBRAIC_NUM);
        return idx2anum(f->get_parameter(0).get_ext_id());
    }

};

arith_decl_plugin::algebraic_numbers_wrapper & arith_decl_plugin::aw() const {
    if (m_aw == nullptr)
        const_cast<arith_decl_plugin*>(this)->m_aw = alloc(algebraic_numbers_wrapper, m_manager->limit());
    return *m_aw;
}

algebraic_numbers::manager & arith_decl_plugin::am() const {
    return aw().m_amanager;
}

app * arith_decl_plugin::mk_numeral(algebraic_numbers::anum const & val, bool is_int) {
    if (am().is_rational(val)) {
        rational rval;
        am().to_rational(val, rval);
        return mk_numeral(rval, is_int);
    }
    else {
        if (is_int) {
            m_manager->raise_exception("invalid irrational value passed as an integer");
        }
        unsigned idx = aw().mk_id(val);
        parameter p(idx, true);
        SASSERT(p.is_external());
        func_decl * decl = m_manager->mk_const_decl(m_rootv_sym, m_real_decl, func_decl_info(m_family_id, OP_IRRATIONAL_ALGEBRAIC_NUM, 1, &p));
        app * r = m_manager->mk_const(decl);

        if (log_constant_meaning_prelude(r)) {
            am().display_root_smt2(m_manager->trace_stream(), val);
            m_manager->trace_stream() << "\n";
        }

        return r;
    }
}

app * arith_decl_plugin::mk_numeral(sexpr const * p, unsigned i) {
    scoped_anum r(am());
    am().mk_root(p, i, r);
    return mk_numeral(r, false);
}

void arith_decl_plugin::del(parameter const & p) {
    SASSERT(p.is_external());
    if (m_aw != nullptr) {
        aw().recycle_id(p.get_ext_id());
    }
}

parameter arith_decl_plugin::translate(parameter const & p, decl_plugin & target) {
    SASSERT(p.is_external());
    arith_decl_plugin & _target = static_cast<arith_decl_plugin&>(target);
    return parameter(_target.aw().mk_id(aw().idx2anum(p.get_ext_id())), true);
}


void arith_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);

    m_real_decl = m->mk_sort(symbol("Real"), sort_info(id, REAL_SORT));
    m->inc_ref(m_real_decl);
    sort * r = m_real_decl;

    m_int_decl = m->mk_sort(symbol("Int"), sort_info(id, INT_SORT));
    m->inc_ref(m_int_decl);
    sort * i = m_int_decl;

    sort * b = m->mk_bool_sort();

#define MK_PRED(FIELD, NAME, KIND, SORT) {                      \
    func_decl_info info(id, KIND);                              \
    info.set_chainable(true);                                   \
    FIELD = m->mk_func_decl(symbol(NAME), SORT, SORT, b, info); \
    m->inc_ref(FIELD);                                          \
    }

    MK_PRED(m_r_le_decl, "<=", OP_LE, r);
    MK_PRED(m_r_ge_decl, ">=", OP_GE, r);
    MK_PRED(m_r_lt_decl, "<",  OP_LT, r);
    MK_PRED(m_r_gt_decl, ">",  OP_GT, r);

    MK_PRED(m_i_le_decl, "<=", OP_LE, i);
    MK_PRED(m_i_ge_decl, ">=", OP_GE, i);
    MK_PRED(m_i_lt_decl, "<",  OP_LT, i);
    MK_PRED(m_i_gt_decl, ">",  OP_GT, i);

#define MK_AC_OP(FIELD, NAME, KIND, SORT) {                             \
        func_decl_info info(id, KIND);                                  \
        info.set_associative();                                         \
        info.set_flat_associative();                                    \
        info.set_commutative();                                         \
        FIELD = m->mk_func_decl(symbol(NAME), SORT, SORT, SORT, info);  \
        m->inc_ref(FIELD);                                              \
    }

#define MK_LEFT_ASSOC_OP(FIELD, NAME, KIND, SORT) {                     \
        func_decl_info info(id, KIND);                                  \
        info.set_left_associative();                                    \
        FIELD = m->mk_func_decl(symbol(NAME), SORT, SORT, SORT, info);  \
        m->inc_ref(FIELD);                                              \
    }


#define MK_OP(FIELD, NAME, KIND, SORT)                                                  \
    FIELD = m->mk_func_decl(symbol(NAME), SORT, SORT, SORT, func_decl_info(id, KIND));  \
    m->inc_ref(FIELD)

#define MK_UNARY(FIELD, NAME, KIND, SORT)                                               \
    FIELD = m->mk_func_decl(symbol(NAME), SORT, SORT, func_decl_info(id, KIND));        \
    m->inc_ref(FIELD)

    MK_AC_OP(m_r_add_decl, "+", OP_ADD, r);
    MK_LEFT_ASSOC_OP(m_r_sub_decl, "-", OP_SUB, r);
    MK_AC_OP(m_r_mul_decl, "*", OP_MUL, r);
    MK_LEFT_ASSOC_OP(m_r_div_decl, "/", OP_DIV, r);
    MK_UNARY(m_r_uminus_decl, "-", OP_UMINUS, r);

    MK_AC_OP(m_i_add_decl, "+", OP_ADD, i);
    MK_LEFT_ASSOC_OP(m_i_sub_decl, "-", OP_SUB, i);
    MK_AC_OP(m_i_mul_decl, "*", OP_MUL, i);
    MK_LEFT_ASSOC_OP(m_i_div_decl, "div", OP_IDIV, i);
    MK_OP(m_i_rem_decl, "rem", OP_REM, i);
    MK_OP(m_i_mod_decl, "mod", OP_MOD, i);
    MK_UNARY(m_i_uminus_decl, "-", OP_UMINUS, i);

    m_to_real_decl = m->mk_func_decl(symbol("to_real"), i, r, func_decl_info(id, OP_TO_REAL));
    m->inc_ref(m_to_real_decl);
    m_to_int_decl = m->mk_func_decl(symbol("to_int"), r, i, func_decl_info(id, OP_TO_INT));
    m->inc_ref(m_to_int_decl);
    m_is_int_decl = m->mk_func_decl(symbol("is_int"), r, m->mk_bool_sort(), func_decl_info(id, OP_IS_INT));
    m->inc_ref(m_is_int_decl);

    MK_OP(m_r_power_decl, "^", OP_POWER, r);
    MK_OP(m_i_power_decl, "^", OP_POWER, i);

    MK_UNARY(m_i_abs_decl, "abs", OP_ABS, i);
    MK_UNARY(m_r_abs_decl, "abs", OP_ABS, r);

    MK_UNARY(m_sin_decl, "sin", OP_SIN, r);
    MK_UNARY(m_cos_decl, "cos", OP_COS, r);
    MK_UNARY(m_tan_decl, "tan", OP_TAN, r);
    MK_UNARY(m_asin_decl, "asin", OP_ASIN, r);
    MK_UNARY(m_acos_decl, "acos", OP_ACOS, r);
    MK_UNARY(m_atan_decl, "atan", OP_ATAN, r);
    MK_UNARY(m_sinh_decl, "sinh", OP_SINH, r);
    MK_UNARY(m_cosh_decl, "cosh", OP_COSH, r);
    MK_UNARY(m_tanh_decl, "tanh", OP_TANH, r);
    MK_UNARY(m_asinh_decl, "asinh", OP_ASINH, r);
    MK_UNARY(m_acosh_decl, "acosh", OP_ACOSH, r);
    MK_UNARY(m_atanh_decl, "atanh", OP_ATANH, r);

    func_decl * pi_decl = m->mk_const_decl(symbol("pi"), r, func_decl_info(id, OP_PI));
    m_pi = m->mk_const(pi_decl);
    m->inc_ref(m_pi);

    func_decl * e_decl  = m->mk_const_decl(symbol("euler"), r, func_decl_info(id, OP_E));
    m_e = m->mk_const(e_decl);
    m->inc_ref(m_e);


    MK_OP(m_neg_root_decl, "neg-root", OP_NEG_ROOT, r);
    MK_UNARY(m_u_asin_decl, "asin-u", OP_U_ASIN, r);
    MK_UNARY(m_u_acos_decl, "acos-u", OP_U_ACOS, r);
}

arith_decl_plugin::arith_decl_plugin():
    m_aw(nullptr),
    m_intv_sym("Int"),
    m_realv_sym("Real"),
    m_rootv_sym("RootObject"),
    m_real_decl(nullptr),
    m_int_decl(nullptr),
    m_r_le_decl(nullptr),
    m_r_ge_decl(nullptr),
    m_r_lt_decl(nullptr),
    m_r_gt_decl(nullptr),
    m_r_add_decl(nullptr),
    m_r_sub_decl(nullptr),
    m_r_uminus_decl(nullptr),
    m_r_mul_decl(nullptr),
    m_r_div_decl(nullptr),
    m_i_le_decl(nullptr),
    m_i_ge_decl(nullptr),
    m_i_lt_decl(nullptr),
    m_i_gt_decl(nullptr),
    m_i_add_decl(nullptr),
    m_i_sub_decl(nullptr),
    m_i_uminus_decl(nullptr),
    m_i_mul_decl(nullptr),
    m_i_div_decl(nullptr),
    m_i_mod_decl(nullptr),
    m_i_rem_decl(nullptr),
    m_to_real_decl(nullptr),
    m_to_int_decl(nullptr),
    m_is_int_decl(nullptr),
    m_r_power_decl(nullptr),
    m_i_power_decl(nullptr),
    m_r_abs_decl(nullptr),
    m_i_abs_decl(nullptr),
    m_sin_decl(nullptr),
    m_cos_decl(nullptr),
    m_tan_decl(nullptr),
    m_asin_decl(nullptr),
    m_acos_decl(nullptr),
    m_atan_decl(nullptr),
    m_sinh_decl(nullptr),
    m_cosh_decl(nullptr),
    m_tanh_decl(nullptr),
    m_asinh_decl(nullptr),
    m_acosh_decl(nullptr),
    m_atanh_decl(nullptr),
    m_pi(nullptr),
    m_e(nullptr),
    m_neg_root_decl(nullptr),
    m_u_asin_decl(nullptr),
    m_u_acos_decl(nullptr),
    m_convert_int_numerals_to_real(false) {
}

arith_decl_plugin::~arith_decl_plugin() {
    dealloc(m_aw);
}

void arith_decl_plugin::finalize() {
#define DEC_REF(decl) if (decl) { m_manager->dec_ref(decl); } ((void) 0)
    DEC_REF(m_real_decl);
    DEC_REF(m_int_decl);
    DEC_REF(m_r_le_decl);
    DEC_REF(m_r_ge_decl);
    DEC_REF(m_r_lt_decl);
    DEC_REF(m_r_gt_decl);
    DEC_REF(m_r_add_decl);
    DEC_REF(m_r_sub_decl);
    DEC_REF(m_r_uminus_decl);
    DEC_REF(m_r_mul_decl);
    DEC_REF(m_r_div_decl);
    DEC_REF(m_i_le_decl);
    DEC_REF(m_i_ge_decl);
    DEC_REF(m_i_lt_decl);
    DEC_REF(m_i_gt_decl);
    DEC_REF(m_i_add_decl);
    DEC_REF(m_i_sub_decl);
    DEC_REF(m_i_uminus_decl);
    DEC_REF(m_i_mul_decl);
    DEC_REF(m_i_div_decl);
    DEC_REF(m_i_mod_decl);
    DEC_REF(m_i_rem_decl);
    DEC_REF(m_to_real_decl);
    DEC_REF(m_to_int_decl);
    DEC_REF(m_is_int_decl);
    DEC_REF(m_i_power_decl);
    DEC_REF(m_r_power_decl);
    DEC_REF(m_i_abs_decl);
    DEC_REF(m_r_abs_decl);
    DEC_REF(m_sin_decl);
    DEC_REF(m_cos_decl);
    DEC_REF(m_tan_decl);
    DEC_REF(m_asin_decl);
    DEC_REF(m_acos_decl);
    DEC_REF(m_atan_decl);
    DEC_REF(m_sinh_decl);
    DEC_REF(m_cosh_decl);
    DEC_REF(m_tanh_decl);
    DEC_REF(m_asinh_decl);
    DEC_REF(m_acosh_decl);
    DEC_REF(m_atanh_decl);
    DEC_REF(m_pi);
    DEC_REF(m_e);
    DEC_REF(m_neg_root_decl);
    DEC_REF(m_u_asin_decl);
    DEC_REF(m_u_acos_decl);
    m_manager->dec_array_ref(m_small_ints.size(), m_small_ints.c_ptr());
    m_manager->dec_array_ref(m_small_reals.size(), m_small_reals.c_ptr());
}

sort * arith_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    switch (k) {
    case REAL_SORT: return m_real_decl;
    case INT_SORT:  return m_int_decl;
    default: return nullptr;
    }
}

inline func_decl * arith_decl_plugin::mk_func_decl(decl_kind k, bool is_real) {
    switch (k) {
    case OP_LE:      return is_real ? m_r_le_decl : m_i_le_decl;
    case OP_GE:      return is_real ? m_r_ge_decl : m_i_ge_decl;
    case OP_LT:      return is_real ? m_r_lt_decl : m_i_lt_decl;
    case OP_GT:      return is_real ? m_r_gt_decl : m_i_gt_decl;
    case OP_ADD:     return is_real ? m_r_add_decl : m_i_add_decl;
    case OP_SUB:     return is_real ? m_r_sub_decl : m_i_sub_decl;
    case OP_UMINUS:  return is_real ? m_r_uminus_decl : m_i_uminus_decl;
    case OP_MUL:     return is_real ? m_r_mul_decl : m_i_mul_decl;
    case OP_DIV:     return m_r_div_decl;
    case OP_IDIV:    return m_i_div_decl;
    case OP_IDIVIDES: UNREACHABLE(); 
    case OP_REM:     return m_i_rem_decl;
    case OP_MOD:     return m_i_mod_decl;
    case OP_DIV0:    return m_manager->mk_func_decl(symbol("/0"), m_real_decl, m_real_decl, m_real_decl, func_decl_info(m_family_id, OP_DIV0));
    case OP_IDIV0:   return m_manager->mk_func_decl(symbol("div0"), m_int_decl, m_int_decl, m_int_decl, func_decl_info(m_family_id, OP_IDIV0));
    case OP_REM0:    return m_manager->mk_func_decl(symbol("rem0"), m_int_decl, m_int_decl, m_int_decl, func_decl_info(m_family_id, OP_REM0));
    case OP_MOD0:    return m_manager->mk_func_decl(symbol("mod0"), m_int_decl, m_int_decl, m_int_decl, func_decl_info(m_family_id, OP_MOD0));
    case OP_POWER0:  
        if (is_real) { 
            return m_manager->mk_func_decl(symbol("^0"), m_real_decl, m_real_decl, m_real_decl, func_decl_info(m_family_id, OP_POWER0));
        }
        return m_manager->mk_func_decl(symbol("^0"), m_int_decl, m_int_decl, m_int_decl, func_decl_info(m_family_id, OP_POWER0));
    case OP_TO_REAL: return m_to_real_decl;
    case OP_TO_INT:  return m_to_int_decl;
    case OP_IS_INT:  return m_is_int_decl;
    case OP_POWER:   return is_real ? m_r_power_decl : m_i_power_decl;
    case OP_ABS:     return is_real ? m_r_abs_decl : m_i_abs_decl;
    case OP_SIN:     return m_sin_decl;
    case OP_COS:     return m_cos_decl;
    case OP_TAN:     return m_tan_decl;
    case OP_ASIN:     return m_asin_decl;
    case OP_ACOS:     return m_acos_decl;
    case OP_ATAN:     return m_atan_decl;
    case OP_SINH:     return m_sinh_decl;
    case OP_COSH:     return m_cosh_decl;
    case OP_TANH:     return m_tanh_decl;
    case OP_ASINH:     return m_asinh_decl;
    case OP_ACOSH:     return m_acosh_decl;
    case OP_ATANH:     return m_atanh_decl;
    case OP_PI:        return m_pi->get_decl();
    case OP_E:         return m_e->get_decl();
    //case OP_0_PW_0_INT:  return m_0_pw_0_int->get_decl();
    //case OP_0_PW_0_REAL: return m_0_pw_0_real->get_decl();
    case OP_NEG_ROOT:    return m_neg_root_decl;
    //case OP_DIV_0:       return m_div_0_decl;
    //case OP_IDIV_0:      return m_idiv_0_decl;
    //case OP_MOD_0:       return m_mod_0_decl;
    case OP_U_ASIN:      return m_u_asin_decl;
    case OP_U_ACOS:      return m_u_acos_decl;
    default: return nullptr;
    }
}

void arith_decl_plugin::check_arity(unsigned arity, unsigned expected_arity) {
    if (arity != expected_arity) {
        m_manager->raise_exception("invalid number of arguments passed to function");
    }
}

inline decl_kind arith_decl_plugin::fix_kind(decl_kind k, unsigned arity) {
    if (k == OP_SUB && arity == 1) {
        return OP_UMINUS;
    }
    return k;
}

#define MAX_SMALL_NUM_TO_CACHE 16

app * arith_decl_plugin::mk_numeral(rational const & val, bool is_int) {
    if (is_int && !val.is_int()) {
        m_manager->raise_exception("invalid rational value passed as an integer");
    }
    if (val.is_unsigned()) {
        unsigned u_val = val.get_unsigned();
        if (u_val < MAX_SMALL_NUM_TO_CACHE) {
            if (is_int && !m_convert_int_numerals_to_real) {
                app * r = m_small_ints.get(u_val, 0);
                if (r == nullptr) {
                    parameter p[2] = { parameter(val), parameter(1) };
                    r = m_manager->mk_const(m_manager->mk_const_decl(m_intv_sym, m_int_decl, func_decl_info(m_family_id, OP_NUM, 2, p)));
                    m_manager->inc_ref(r);
                    m_small_ints.setx(u_val, r, 0);

                    if (log_constant_meaning_prelude(r)) {
                        m_manager->trace_stream() << u_val << "\n";
                    }
                }
                return r;
            }
            else {
                app * r = m_small_reals.get(u_val, 0);
                if (r == nullptr) {
                    parameter p[2] = { parameter(val), parameter(0) };
                    r = m_manager->mk_const(m_manager->mk_const_decl(m_realv_sym, m_real_decl, func_decl_info(m_family_id, OP_NUM, 2, p)));
                    m_manager->inc_ref(r);
                    m_small_reals.setx(u_val, r, 0);

                    if (log_constant_meaning_prelude(r)) {
                        m_manager->trace_stream() << u_val << "\n";
                    }
                }
                return r;
            }
        }
    }
    parameter p[2] = { parameter(val), parameter(static_cast<int>(is_int)) };
    func_decl * decl;

    if (is_int && !m_convert_int_numerals_to_real)
        decl = m_manager->mk_const_decl(m_intv_sym, m_int_decl, func_decl_info(m_family_id, OP_NUM, 2, p));
    else
        decl = m_manager->mk_const_decl(m_realv_sym, m_real_decl, func_decl_info(m_family_id, OP_NUM, 2, p));
    app * r = m_manager->mk_const(decl);

    if (log_constant_meaning_prelude(r)) {
        val.display_smt2(m_manager->trace_stream());
        m_manager->trace_stream() << "\n";
    }

    return r;
}

func_decl * arith_decl_plugin::mk_num_decl(unsigned num_parameters, parameter const * parameters, unsigned arity) {
    if (!(num_parameters == 2 && arity == 0 && parameters[0].is_rational() && parameters[1].is_int())) {
        m_manager->raise_exception("invalid numeral declaration");
        return nullptr;
    }
    if (parameters[1].get_int() != 0)
        return m_manager->mk_const_decl(m_intv_sym, m_int_decl, func_decl_info(m_family_id, OP_NUM, num_parameters, parameters));
    else
        return m_manager->mk_const_decl(m_realv_sym, m_real_decl, func_decl_info(m_family_id, OP_NUM, num_parameters, parameters));
}

static bool use_coercion(decl_kind k) {
    return k == OP_ADD || k == OP_SUB || k == OP_MUL || k == OP_POWER || k == OP_LE || k == OP_GE || k == OP_LT || k == OP_GT || k == OP_UMINUS;
}

static bool has_real_arg(unsigned arity, sort * const * domain, sort * real_sort) {
    for (unsigned i = 0; i < arity; i++)
        if (domain[i] == real_sort)
            return true;
    return false;
}

static bool has_real_arg(ast_manager * m, unsigned num_args, expr * const * args, sort * real_sort) {
    for (unsigned i = 0; i < num_args; i++)
        if (m->get_sort(args[i]) == real_sort)
            return true;
    return false;
}

static bool is_const_op(decl_kind k) {
    return
        k == OP_PI ||
        k == OP_E;
        //k == OP_0_PW_0_INT ||
        //k == OP_0_PW_0_REAL;
}

func_decl * arith_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                          unsigned arity, sort * const * domain, sort * range) {
    if (k == OP_NUM)
        return mk_num_decl(num_parameters, parameters, arity);
    if (arity == 0 && !is_const_op(k)) {
        m_manager->raise_exception("no arguments supplied to arithmetical operator");
        return nullptr;
    }
    if (k == OP_IDIVIDES) {
        if (arity != 1 || domain[0] != m_int_decl || num_parameters != 1 || !parameters[0].is_int()) {
            m_manager->raise_exception("invalid divides application. Expects integer parameter and one argument of sort integer");
        }
        return m_manager->mk_func_decl(symbol("divisible"), 1, &m_int_decl, m_manager->mk_bool_sort(), 
                                       func_decl_info(m_family_id, k, num_parameters, parameters));
    }

    if (m_manager->int_real_coercions() && use_coercion(k)) {
        return mk_func_decl(fix_kind(k, arity), has_real_arg(arity, domain, m_real_decl));
    }
    else {
        bool is_real = arity > 0 && domain[0] == m_real_decl;
        return mk_func_decl(fix_kind(k, arity), is_real);
    }
}

func_decl * arith_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                          unsigned num_args, expr * const * args, sort * range) {
    if (k == OP_NUM)
        return mk_num_decl(num_parameters, parameters, num_args);
    if (num_args == 0 && !is_const_op(k)) {
        m_manager->raise_exception("no arguments supplied to arithmetical operator");
        return nullptr;
    }
    if (k == OP_IDIVIDES) {
        if (num_args != 1 || m_manager->get_sort(args[0]) != m_int_decl || num_parameters != 1 || !parameters[0].is_int()) {
            m_manager->raise_exception("invalid divides application. Expects integer parameter and one argument of sort integer");
        }
        return m_manager->mk_func_decl(symbol("divisible"), 1, &m_int_decl, m_manager->mk_bool_sort(), 
                                       func_decl_info(m_family_id, k, num_parameters, parameters));
    }
    if (m_manager->int_real_coercions() && use_coercion(k)) {
        return mk_func_decl(fix_kind(k, num_args), has_real_arg(m_manager, num_args, args, m_real_decl));
    }
    else {
        bool is_real = num_args > 0 && m_manager->get_sort(args[0]) == m_real_decl;
        return mk_func_decl(fix_kind(k, num_args), is_real);
    }
}

void arith_decl_plugin::get_sort_names(svector<builtin_name>& sort_names, symbol const & logic) {
    if (logic == "NRA" ||
        logic == "QF_NRA" ||
        logic == "QF_UFNRA") {
        m_convert_int_numerals_to_real = true;
        sort_names.push_back(builtin_name("Real", REAL_SORT));
    }
    else {
        // TODO: only define Int and Real in the right logics
        sort_names.push_back(builtin_name("Int", INT_SORT));
        sort_names.push_back(builtin_name("Real", REAL_SORT));
    }
}

void arith_decl_plugin::get_op_names(svector<builtin_name>& op_names, symbol const & logic) {
    op_names.push_back(builtin_name("<=",OP_LE));
    op_names.push_back(builtin_name(">=",OP_GE));
    op_names.push_back(builtin_name("<",OP_LT));
    op_names.push_back(builtin_name(">",OP_GT));
    op_names.push_back(builtin_name("+",OP_ADD));
    op_names.push_back(builtin_name("-",OP_SUB));
    op_names.push_back(builtin_name("~",OP_UMINUS));
    op_names.push_back(builtin_name("*",OP_MUL));
    op_names.push_back(builtin_name("/",OP_DIV));
    op_names.push_back(builtin_name("div",OP_IDIV));
    if (gparams::get_value("smtlib2_compliant") == "true") {
        op_names.push_back(builtin_name("divisible",OP_IDIVIDES));
    }
    op_names.push_back(builtin_name("rem",OP_REM));
    op_names.push_back(builtin_name("mod",OP_MOD));
    op_names.push_back(builtin_name("to_real",OP_TO_REAL));
    op_names.push_back(builtin_name("to_int",OP_TO_INT));
    op_names.push_back(builtin_name("is_int",OP_IS_INT));
    op_names.push_back(builtin_name("abs", OP_ABS));
    if (logic == symbol::null || logic == symbol("ALL")) {
        op_names.push_back(builtin_name("^", OP_POWER));
        op_names.push_back(builtin_name("sin", OP_SIN));
        op_names.push_back(builtin_name("cos", OP_COS));
        op_names.push_back(builtin_name("tan", OP_TAN));
        op_names.push_back(builtin_name("asin", OP_ASIN));
        op_names.push_back(builtin_name("acos", OP_ACOS));
        op_names.push_back(builtin_name("atan", OP_ATAN));
        op_names.push_back(builtin_name("sinh", OP_SINH));
        op_names.push_back(builtin_name("cosh", OP_COSH));
        op_names.push_back(builtin_name("tanh", OP_TANH));
        op_names.push_back(builtin_name("asinh", OP_ASINH));
        op_names.push_back(builtin_name("acosh", OP_ACOSH));
        op_names.push_back(builtin_name("atanh", OP_ATANH));
        op_names.push_back(builtin_name("pi", OP_PI));
        op_names.push_back(builtin_name("euler", OP_E));
    }
}

bool arith_decl_plugin::is_value(app * e) const {
    return
        is_app_of(e, m_family_id, OP_NUM) ||
        is_app_of(e, m_family_id, OP_IRRATIONAL_ALGEBRAIC_NUM) ||
        is_app_of(e, m_family_id, OP_PI) ||
        is_app_of(e, m_family_id, OP_E);
}

bool arith_decl_plugin::is_unique_value(app * e) const {
    return
        is_app_of(e, m_family_id, OP_NUM) ||
        is_app_of(e, m_family_id, OP_PI) ||
        is_app_of(e, m_family_id, OP_E);
}

bool arith_decl_plugin::are_equal(app * a, app * b) const {
    if (decl_plugin::are_equal(a, b)) {
        return true;
    }

    if (is_app_of(a, m_family_id, OP_IRRATIONAL_ALGEBRAIC_NUM) && is_app_of(b, m_family_id, OP_IRRATIONAL_ALGEBRAIC_NUM)) {
        return am().eq(aw().to_anum(a->get_decl()), aw().to_anum(b->get_decl()));
    }

    return false;
}

bool arith_decl_plugin::are_distinct(app * a, app * b) const {
    TRACE("are_distinct_bug", tout << mk_ismt2_pp(a, *m_manager) << "\n" << mk_ismt2_pp(b, *m_manager) << "\n";);
    if (decl_plugin::are_distinct(a,b)) {
        return true;
    }

    if (is_app_of(a, m_family_id, OP_IRRATIONAL_ALGEBRAIC_NUM) && is_app_of(b, m_family_id, OP_IRRATIONAL_ALGEBRAIC_NUM)) {
        return am().neq(aw().to_anum(a->get_decl()), aw().to_anum(b->get_decl()));
    }

#define is_non_zero(e) is_app_of(e,m_family_id, OP_NUM) && !to_app(e)->get_decl()->get_parameter(0).get_rational().is_zero()

    if (is_app_of(a, m_family_id, OP_ADD) &&
        a->get_num_args() == 2 &&
        to_app(a)->get_arg(0) == b &&
        is_non_zero(to_app(a)->get_arg(1))) {
        return true;
    }
    if (is_app_of(a, m_family_id, OP_ADD) &&
        a->get_num_args() == 2 &&
        to_app(a)->get_arg(1) == b &&
        is_non_zero(to_app(a)->get_arg(0))) {
        return true;
    }
    if (is_app_of(b, m_family_id, OP_ADD) &&
        b->get_num_args() == 2 &&
        to_app(b)->get_arg(1) == a &&
        is_non_zero(to_app(b)->get_arg(0))) {
        return true;
    }
    if (is_app_of(b, m_family_id, OP_ADD) &&
        b->get_num_args() == 2 &&
        to_app(b)->get_arg(0) == a &&
        is_non_zero(to_app(b)->get_arg(1))) {
        return true;
    }
    return false;
}

expr * arith_decl_plugin::get_some_value(sort * s) {
    SASSERT(s == m_int_decl || s == m_real_decl);
    return mk_numeral(rational(0), s == m_int_decl);
}

bool arith_recognizers::is_numeral(expr const * n, rational & val, bool & is_int) const {
    if (!is_app_of(n, m_afid, OP_NUM))
        return false;
    func_decl * decl = to_app(n)->get_decl();
    val    = decl->get_parameter(0).get_rational();
    is_int = decl->get_parameter(1).get_int() != 0;
    return true;
}

bool arith_recognizers::is_irrational_algebraic_numeral(expr const * n) const { 
    return is_app(n) && to_app(n)->is_app_of(m_afid, OP_IRRATIONAL_ALGEBRAIC_NUM); 
}


#define IS_INT_EXPR_DEPTH_LIMIT 100
bool arith_recognizers::is_int_expr(expr const *e) const {
    if (is_int(e)) return true;
    if (is_uninterp(e)) return false;
    ptr_buffer<const expr> todo;
    todo.push_back(e);
    rational r;
    unsigned i = 0;
    while (!todo.empty()) {
        ++i;
        if (i > IS_INT_EXPR_DEPTH_LIMIT) {return false;}
        e = todo.back();
        todo.pop_back();
        if (is_to_real(e)) {
            // pass
        }
        else if (is_numeral(e, r) && r.is_int()) {
            // pass
        }
        else if (is_add(e) || is_mul(e)) {
            todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
        }
        else {
            return false;
        }
    }
    return true;
}

arith_util::arith_util(ast_manager & m):
    arith_recognizers(m.mk_family_id("arith")),
    m_manager(m),
    m_plugin(nullptr) {
}

void arith_util::init_plugin() {
    SASSERT(m_plugin == 0);
    m_plugin = static_cast<arith_decl_plugin*>(m_manager.get_plugin(m_afid));
}

bool arith_util::is_irrational_algebraic_numeral2(expr const * n, algebraic_numbers::anum & val) {
    if (!is_app_of(n, m_afid, OP_IRRATIONAL_ALGEBRAIC_NUM))
        return false;
    am().set(val, to_irrational_algebraic_numeral(n));
    return true;
}

algebraic_numbers::anum const & arith_util::to_irrational_algebraic_numeral(expr const * n) {
    SASSERT(is_irrational_algebraic_numeral(n));
    return plugin().aw().to_anum(to_app(n)->get_decl());
}

expr_ref arith_util::mk_mul_simplify(expr_ref_vector const& args) {
    return mk_mul_simplify(args.size(), args.c_ptr());

}
expr_ref arith_util::mk_mul_simplify(unsigned sz, expr* const* args) {
    expr_ref result(m_manager);

    switch (sz) {
    case 0:
        result = mk_numeral(rational(1), true);
        break;
    case 1:
        result = args[0];
        break;
    default:
        result = mk_mul(sz, args);
        break;
    }
    return result;
}

expr_ref arith_util::mk_add_simplify(expr_ref_vector const& args) {
    return mk_add_simplify(args.size(), args.c_ptr());

}
expr_ref arith_util::mk_add_simplify(unsigned sz, expr* const* args) {
    expr_ref result(m_manager);

    switch (sz) {
    case 0:
        result = mk_numeral(rational(0), true);
        break;
    case 1:
        result = args[0];
        break;
    default:
        result = mk_add(sz, args);
        break;
    }
    return result;
}

bool arith_util::is_considered_uninterpreted(func_decl* f, unsigned n, expr* const* args, func_decl_ref& f_out) {
    rational r;
    if (is_decl_of(f, m_afid, OP_DIV) && is_numeral(args[1], r) && r.is_zero()) {
        f_out = mk_div0();
        return true;
    }
    if (is_decl_of(f, m_afid, OP_IDIV) && is_numeral(args[1], r) && r.is_zero()) {
        sort* rs[2] = { mk_real(), mk_real() };
        f_out = m_manager.mk_func_decl(m_afid, OP_IDIV0, 0, nullptr, 2, rs, mk_real());
        return true;
    }
    if (is_decl_of(f, m_afid, OP_MOD) && is_numeral(args[1], r) && r.is_zero()) {
        sort* rs[2] = { mk_real(), mk_real() };
        f_out = m_manager.mk_func_decl(m_afid, OP_MOD0, 0, nullptr, 2, rs, mk_real());
        return true;
    }
    if (is_decl_of(f, m_afid, OP_REM) && is_numeral(args[1], r) && r.is_zero()) {
        sort* rs[2] = { mk_real(), mk_real() };
        f_out = m_manager.mk_func_decl(m_afid, OP_REM0, 0, nullptr, 2, rs, mk_real());
        return true;
    }
    if (is_decl_of(f, m_afid, OP_POWER) && is_numeral(args[1], r) && r.is_zero() && is_numeral(args[0], r) && r.is_zero()) {
        sort* rs[2] = { mk_real(), mk_real() };
        f_out = m_manager.mk_func_decl(m_afid, OP_POWER0, 0, nullptr, 2, rs, mk_real());
        return true;
    }
    return plugin().is_considered_uninterpreted(f);
}

func_decl* arith_util::mk_div0() {
    sort* rs[2] = { mk_real(), mk_real() };
    return m_manager.mk_func_decl(m_afid, OP_DIV0, 0, nullptr, 2, rs, mk_real());
}
