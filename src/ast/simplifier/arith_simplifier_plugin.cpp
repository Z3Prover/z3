/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    arith_simplifier_plugin.cpp

Abstract:

    Simplifier for the arithmetic family.

Author:

    Leonardo (leonardo) 2008-01-08
    
--*/
#include"arith_simplifier_plugin.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"ast_smt2_pp.h"

arith_simplifier_plugin::~arith_simplifier_plugin() {
}

arith_simplifier_plugin::arith_simplifier_plugin(ast_manager & m, basic_simplifier_plugin & b, arith_simplifier_params & p):
    poly_simplifier_plugin(symbol("arith"), m, OP_ADD, OP_MUL, OP_UMINUS, OP_SUB, OP_NUM),
    m_params(p),
    m_util(m),
    m_bsimp(b),
    m_int_zero(m),
    m_real_zero(m) {
    m_int_zero  = m_util.mk_numeral(rational(0), true);
    m_real_zero = m_util.mk_numeral(rational(0), false);
}

/**
   \brief Return true if the first monomial of t is negative.
*/
bool arith_simplifier_plugin::is_neg_poly(expr * t) const {
    if (m_util.is_add(t)) {
        t = to_app(t)->get_arg(0);
    }
    if (m_util.is_mul(t)) {
        t = to_app(t)->get_arg(0);
        rational r;
        bool is_int;
        if (m_util.is_numeral(t, r, is_int))
            return r.is_neg();
    }
    return false;
}

void arith_simplifier_plugin::get_monomial_gcd(expr_ref_vector& monomials, numeral& g) {
    g = numeral::zero();
    numeral n;
    for (unsigned  i = 0; !g.is_one() && i < monomials.size(); ++i) {
        expr* e = monomials[i].get();
        if (is_numeral(e, n)) {
            g = gcd(abs(n), g);
        }
        else if (is_mul(e) && is_numeral(to_app(e)->get_arg(0), n)) {
            g = gcd(abs(n), g);        
        }
        else {
            g = numeral::one();
            return;
        }
    }
    if (g.is_zero()) {
        g = numeral::one();
    }
}

void arith_simplifier_plugin::div_monomial(expr_ref_vector& monomials, numeral const& g) {
    numeral n;
    for (unsigned  i = 0; i < monomials.size(); ++i) {
        expr* e = monomials[i].get();
        if (is_numeral(e, n)) {
            SASSERT((n/g).is_int());
            monomials[i] = mk_numeral(n/g);
        }
        else if (is_mul(e) && is_numeral(to_app(e)->get_arg(0), n)) {
            SASSERT((n/g).is_int());
            monomials[i] = mk_mul(n/g, to_app(e)->get_arg(1));
        }
        else {
            UNREACHABLE();
        }
    }
}

void arith_simplifier_plugin::gcd_reduce_monomial(expr_ref_vector& monomials, numeral& k) {
    numeral g, n;

    get_monomial_gcd(monomials, g);
    g = gcd(abs(k), g);

    if (g.is_one()) {
        return;
    }
    SASSERT(g.is_pos());

    k = k / g;
    div_monomial(monomials, g);
    
}

template<arith_simplifier_plugin::op_kind Kind>
void arith_simplifier_plugin::mk_le_ge_eq_core(expr * arg1, expr * arg2, expr_ref & result) {
    set_curr_sort(arg1);
    bool is_int = m_curr_sort->get_decl_kind() == INT_SORT;
    expr_ref_vector monomials(m_manager);
    rational k;
    TRACE("arith_eq_bug", tout << mk_ismt2_pp(arg1, m_manager) << "\n" << mk_ismt2_pp(arg2, m_manager) << "\n";);
    process_sum_of_monomials(false, arg1, monomials, k);
    process_sum_of_monomials(true,  arg2, monomials, k);
    k.neg();
    if (is_int) {
        numeral g;
        get_monomial_gcd(monomials, g);
        if (!g.is_one()) {
            div_monomial(monomials, g);
            switch(Kind) {
            case LE:
                //
                //   g*monmials' <= k
                // <=> 
                //   monomials' <= floor(k/g)
                //
                k = floor(k/g);
                break;
            case GE:
                //
                //   g*monmials' >= k
                // <=> 
                //   monomials' >= ceil(k/g)
                //
                k = ceil(k/g);
                break;
            case EQ:
                k = k/g;
                if (!k.is_int()) {
                    result = m_manager.mk_false();
                    return;
                }
                break;
            }
        }
    }
    expr_ref lhs(m_manager);
    mk_sum_of_monomials(monomials, lhs);
    if (m_util.is_numeral(lhs)) {
        SASSERT(lhs == mk_zero());
        if (( Kind == LE && numeral::zero() <= k) ||
            ( Kind == GE && numeral::zero() >= k) ||
            ( Kind == EQ && numeral::zero() == k))
            result = m_manager.mk_true();
        else
            result = m_manager.mk_false();
    }
    else {
        
        if (is_neg_poly(lhs)) {
            expr_ref neg_lhs(m_manager);
            mk_uminus(lhs, neg_lhs);
            lhs = neg_lhs;
            k.neg();
            expr * rhs = m_util.mk_numeral(k, is_int);
            switch (Kind) {
            case LE:
                result = m_util.mk_ge(lhs, rhs); 
                break;
            case GE:
                result = m_util.mk_le(lhs, rhs);
                break;
            case EQ:
                result = m_manager.mk_eq(lhs, rhs);
                break;
            }
        }
        else {
            expr * rhs = m_util.mk_numeral(k, is_int);
            switch (Kind) {
            case LE:
                result = m_util.mk_le(lhs, rhs); 
                break;
            case GE:
                result = m_util.mk_ge(lhs, rhs);
                break;
            case EQ:
                result = m_manager.mk_eq(lhs, rhs);
                break;
            }
        }
    }
}

void arith_simplifier_plugin::mk_arith_eq(expr * arg1, expr * arg2, expr_ref & result) {
    mk_le_ge_eq_core<EQ>(arg1, arg2, result);
}

void arith_simplifier_plugin::mk_le(expr * arg1, expr * arg2, expr_ref & result) {
    mk_le_ge_eq_core<LE>(arg1, arg2, result);
}

void arith_simplifier_plugin::mk_ge(expr * arg1, expr * arg2, expr_ref & result) {
    mk_le_ge_eq_core<GE>(arg1, arg2, result);
}

void arith_simplifier_plugin::mk_lt(expr * arg1, expr * arg2, expr_ref & result) {
    expr_ref tmp(m_manager);
    mk_le(arg2, arg1, tmp);
    m_bsimp.mk_not(tmp, result);
}
 
void arith_simplifier_plugin::mk_gt(expr * arg1, expr * arg2, expr_ref & result) {
    expr_ref tmp(m_manager);
    mk_le(arg1, arg2, tmp);
    m_bsimp.mk_not(tmp, result);
}

void arith_simplifier_plugin::gcd_normalize(numeral & coeff, expr_ref& term) {
    if (!abs(coeff).is_one()) {
        set_curr_sort(term);
        SASSERT(m_curr_sort->get_decl_kind() == INT_SORT);
        expr_ref_vector monomials(m_manager);
        rational k;
        monomials.push_back(mk_numeral(numeral(coeff), true));
        process_sum_of_monomials(false, term, monomials, k);
        gcd_reduce_monomial(monomials, k);
        numeral coeff1;
        if (!is_numeral(monomials[0].get(), coeff1)) {
            UNREACHABLE();
        }
        if (coeff1 == coeff) {
            return;
        }
        monomials[0] = mk_numeral(k, true);
        coeff = coeff1;        
        mk_sum_of_monomials(monomials, term);        
    }
}


void arith_simplifier_plugin::mk_div(expr * arg1, expr * arg2, expr_ref & result) {
    set_curr_sort(arg1);
    numeral v1, v2;
    bool is_int;
    if (m_util.is_numeral(arg2, v2, is_int) && !v2.is_zero()) {
        SASSERT(!is_int);
        if (m_util.is_numeral(arg1, v1, is_int))
            result = m_util.mk_numeral(v1/v2, false);
        else {
            numeral k(1);
            k /= v2;
            
            expr_ref inv_arg2(m_util.mk_numeral(k, false), m_manager);
            mk_mul(inv_arg2, arg1, result);
        }
    }
    else
        result = m_util.mk_div(arg1, arg2);
}

void arith_simplifier_plugin::mk_idiv(expr * arg1, expr * arg2, expr_ref & result) {
    set_curr_sort(arg1);
    numeral v1, v2;
    bool is_int;
    if (m_util.is_numeral(arg1, v1, is_int) && m_util.is_numeral(arg2, v2, is_int) && !v2.is_zero())
        result = m_util.mk_numeral(div(v1, v2), is_int);
    else 
        result = m_util.mk_idiv(arg1, arg2);
}

void arith_simplifier_plugin::prop_mod_const(expr * e, unsigned depth, numeral const& k, expr_ref& result) {
    SASSERT(m_util.is_int(e));
    SASSERT(k.is_int() && k.is_pos());
    numeral n;
    bool is_int;

    if (depth == 0) {
        result = e;
    }
    else if (is_add(e) || is_mul(e)) {
        expr_ref_vector args(m_manager);
        expr_ref tmp(m_manager);
        app* a = to_app(e);
        for (unsigned i = 0; i < a->get_num_args(); ++i) {
            prop_mod_const(a->get_arg(i), depth - 1, k, tmp);
            args.push_back(tmp);
        }
        reduce(a->get_decl(), args.size(), args.c_ptr(), result);
    }
    else if (m_util.is_numeral(e, n, is_int) && is_int) {
        result = mk_numeral(mod(n, k), true);
    }
    else {
        result = e;
    }
}

void arith_simplifier_plugin::mk_mod(expr * arg1, expr * arg2, expr_ref & result) {
    set_curr_sort(arg1);
    numeral v1, v2;
    bool is_int;
    if (m_util.is_numeral(arg1, v1, is_int) && m_util.is_numeral(arg2, v2, is_int) && !v2.is_zero()) {
        result = m_util.mk_numeral(mod(v1, v2), is_int);
    }
    else if (m_util.is_numeral(arg2, v2, is_int) && is_int && v2.is_one()) {
        result = m_util.mk_numeral(numeral(0), true);
    }
    else if (m_util.is_numeral(arg2, v2, is_int) && is_int && v2.is_pos()) {
        expr_ref tmp(m_manager);
        prop_mod_const(arg1, 5, v2, tmp);
        result = m_util.mk_mod(tmp, arg2);
    }
    else {
        result = m_util.mk_mod(arg1, arg2);
    }
}

void arith_simplifier_plugin::mk_rem(expr * arg1, expr * arg2, expr_ref & result) {
    set_curr_sort(arg1);
    numeral v1, v2;
    bool is_int;
    if (m_util.is_numeral(arg1, v1, is_int) && m_util.is_numeral(arg2, v2, is_int) && !v2.is_zero()) {
        numeral m = mod(v1, v2);
        //
        // rem(v1,v2) = if v2 >= 0 then mod(v1,v2) else -mod(v1,v2)
        //
        if (v2.is_neg()) {
            m.neg();
        }
        result = m_util.mk_numeral(m, is_int);
    }
    else if (m_util.is_numeral(arg2, v2, is_int) && is_int && v2.is_one()) {
        result = m_util.mk_numeral(numeral(0), true);
    }
    else if (m_util.is_numeral(arg2, v2, is_int) && is_int && !v2.is_zero()) {
        expr_ref tmp(m_manager);
        prop_mod_const(arg1, 5, v2, tmp);
        result = m_util.mk_mod(tmp, arg2);
        if (v2.is_neg()) {
            result = m_util.mk_uminus(result);
        }
    }
    else {
        result = m_util.mk_rem(arg1, arg2);
    }
}

void arith_simplifier_plugin::mk_to_real(expr * arg, expr_ref & result) {
    numeral v;
    if (m_util.is_numeral(arg, v))
        result = m_util.mk_numeral(v, false);
    else
        result = m_util.mk_to_real(arg);
}

void arith_simplifier_plugin::mk_to_int(expr * arg, expr_ref & result) {
    numeral v;
    if (m_util.is_numeral(arg, v))
        result = m_util.mk_numeral(floor(v), true);
    else if (m_util.is_to_real(arg)) 
        result = to_app(arg)->get_arg(0);
    else 
        result = m_util.mk_to_int(arg);
}

void arith_simplifier_plugin::mk_is_int(expr * arg, expr_ref & result) {
    numeral v;
    if (m_util.is_numeral(arg, v))
        result = v.is_int()?m_manager.mk_true():m_manager.mk_false();
    else if (m_util.is_to_real(arg)) 
        result = m_manager.mk_true();
    else 
        result = m_util.mk_is_int(arg);
}

bool arith_simplifier_plugin::reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    set_reduce_invoked();
    SASSERT(f->get_family_id() == m_fid);
    TRACE("arith_simplifier_plugin", tout << mk_pp(f, m_manager) << "\n"; 
          for (unsigned i = 0; i < num_args; i++) tout << mk_pp(args[i], m_manager) << "\n";);
    arith_op_kind k = static_cast<arith_op_kind>(f->get_decl_kind());
    switch (k) {
    case OP_NUM:      return false;
    case OP_LE:       if (m_presimp) return false; SASSERT(num_args == 2); mk_le(args[0], args[1], result); break;
    case OP_GE:       if (m_presimp) return false; SASSERT(num_args == 2); mk_ge(args[0], args[1], result); break;
    case OP_LT:       if (m_presimp) return false; SASSERT(num_args == 2); mk_lt(args[0], args[1], result); break;
    case OP_GT:       if (m_presimp) return false; SASSERT(num_args == 2); mk_gt(args[0], args[1], result); break;
    case OP_ADD:      mk_add(num_args, args, result); break;
    case OP_SUB:      mk_sub(num_args, args, result); break;
    case OP_UMINUS:   SASSERT(num_args == 1); mk_uminus(args[0], result); break;
    case OP_MUL:      
        mk_mul(num_args, args, result); 
        TRACE("arith_simplifier_plugin", tout << mk_pp(result, m_manager) << "\n";); 
        break;
    case OP_DIV:      SASSERT(num_args == 2); mk_div(args[0], args[1], result); break;
    case OP_IDIV:     SASSERT(num_args == 2); mk_idiv(args[0], args[1], result); break;
    case OP_REM:      SASSERT(num_args == 2); mk_rem(args[0], args[1], result); break;
    case OP_MOD:      SASSERT(num_args == 2); mk_mod(args[0], args[1], result); break;
    case OP_TO_REAL:  SASSERT(num_args == 1); mk_to_real(args[0], result); break;
    case OP_TO_INT:   SASSERT(num_args == 1); mk_to_int(args[0], result); break;
    case OP_IS_INT:   SASSERT(num_args == 1); mk_is_int(args[0], result); break;
    case OP_POWER:                    return false;
    case OP_ABS:      SASSERT(num_args == 1); mk_abs(args[0], result); break;
    case OP_IRRATIONAL_ALGEBRAIC_NUM: return false;
    case OP_DIV_0: return false;
    case OP_IDIV_0: return false;
    default:
        return false;
    }
    TRACE("arith_simplifier_plugin", tout << mk_pp(result.get(), m_manager) << "\n";);
    return true;
}

void arith_simplifier_plugin::mk_abs(expr * arg, expr_ref & result) {
    expr_ref c(m_manager);
    expr_ref m_arg(m_manager);
    mk_uminus(arg, m_arg);
    mk_ge(arg, m_util.mk_numeral(rational(0), m_util.is_int(arg)), c);
    m_bsimp.mk_ite(c, arg, m_arg, result);
}

bool arith_simplifier_plugin::is_arith_term(expr * n) const {
    return n->get_kind() == AST_APP && to_app(n)->get_family_id() == m_fid;
}

bool arith_simplifier_plugin::reduce_eq(expr * lhs, expr * rhs, expr_ref & result) {
    TRACE("reduce_eq_bug", tout << mk_ismt2_pp(lhs, m_manager) << "\n" << mk_ismt2_pp(rhs, m_manager) << "\n";);
    set_reduce_invoked();
    if (m_presimp) {
        return false;
    }
    if (m_params.m_arith_expand_eqs) {
        expr_ref le(m_manager), ge(m_manager);
        mk_le_ge_eq_core<LE>(lhs, rhs, le);
        mk_le_ge_eq_core<GE>(lhs, rhs, ge);
        m_bsimp.mk_and(le, ge, result);
        return true;
    }

    if (m_params.m_arith_process_all_eqs || is_arith_term(lhs) || is_arith_term(rhs)) {
        mk_arith_eq(lhs, rhs, result); 
        return true;
    }
    return false;
}



