/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    factor_simplifier.cpp

Abstract:

    Polynomial factorization simplifier.
    Ported from factor_tactic.cpp by Leonardo de Moura (leonardo) 2012-02-03.

--*/

#include "ast/simplifiers/factor_simplifier.h"
#include "ast/expr2polynomial.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/rewriter_def.h"
#include "math/polynomial/polynomial.h"

struct factor_simplifier::rw_cfg : public default_rewriter_cfg {
    ast_manager &               m;
    arith_util                  m_util;
    unsynch_mpq_manager         m_qm;
    polynomial::manager         m_pm;
    default_expr2polynomial     m_expr2poly;
    polynomial::factor_params   m_fparams;
    bool                        m_split_factors;

    rw_cfg(ast_manager & _m, params_ref const & p):
        m(_m),
        m_util(_m),
        m_pm(m.limit(), m_qm),
        m_expr2poly(m, m_pm) {
        updt_params(p);
    }

    void updt_params(params_ref const & p) {
        m_split_factors = p.get_bool("split_factors", true);
        m_fparams.updt_params(p);
    }

    expr * mk_mul(unsigned sz, expr * const * args) {
        SASSERT(sz > 0);
        if (sz == 1)
            return args[0];
        return m_util.mk_mul(sz, args);
    }

    expr * mk_zero_for(expr * arg) {
        return m_util.mk_numeral(rational(0), m_util.is_int(arg));
    }

    // p1^k1 * p2^k2 = 0 --> p1*p2 = 0
    void mk_eq(polynomial::factors const & fs, expr_ref & result) {
        expr_ref_buffer args(m);
        expr_ref arg(m);
        for (unsigned i = 0; i < fs.distinct_factors(); ++i) {
            m_expr2poly.to_expr(fs[i], true, arg);
            args.push_back(arg);
        }
        result = m.mk_eq(mk_mul(args.size(), args.data()), mk_zero_for(arg));
    }

    // p1^k1 * p2^k2 = 0 --> p1 = 0 or p2 = 0
    void mk_split_eq(polynomial::factors const & fs, expr_ref & result) {
        expr_ref_buffer args(m);
        expr_ref arg(m);
        for (unsigned i = 0; i < fs.distinct_factors(); ++i) {
            m_expr2poly.to_expr(fs[i], true, arg);
            args.push_back(m.mk_eq(arg, mk_zero_for(arg)));
        }
        if (args.size() == 1)
            result = args[0];
        else
            result = m.mk_or(args);
    }

    decl_kind flip(decl_kind k) {
        SASSERT(k == OP_LT || k == OP_GT || k == OP_LE || k == OP_GE);
        switch (k) {
        case OP_LT: return OP_GT;
        case OP_LE: return OP_GE;
        case OP_GT: return OP_LT;
        case OP_GE: return OP_LE;
        default:
            UNREACHABLE();
            return k;
        }
    }

    // p1^{2*k1} * p2^{2*k2 + 1} >=< 0
    // -->
    // (p1^2)*p2 >=<0
    void mk_comp(decl_kind k, polynomial::factors const & fs, expr_ref & result) {
        SASSERT(k == OP_LT || k == OP_GT || k == OP_LE || k == OP_GE);
        expr_ref_buffer args(m);
        expr_ref arg(m);
        for (unsigned i = 0; i < fs.distinct_factors(); ++i) {
            m_expr2poly.to_expr(fs[i], true, arg);
            if (fs.get_degree(i) % 2 == 0)
                arg = m_util.mk_power(arg, m_util.mk_numeral(rational(2), m_util.is_int(arg)));
            args.push_back(arg);
        }
        expr * lhs = mk_mul(args.size(), args.data());
        result = m.mk_app(m_util.get_family_id(), k, lhs, mk_zero_for(lhs));
    }

    // See mk_split_strict_comp and mk_split_nonstrict_comp
    void split_even_odd(bool strict, polynomial::factors const & fs, expr_ref_buffer & even_eqs, expr_ref_buffer & odd_factors) {
        expr_ref arg(m);
        for (unsigned i = 0; i < fs.distinct_factors(); ++i) {
            m_expr2poly.to_expr(fs[i], true, arg);
            if (fs.get_degree(i) % 2 == 0) {
                expr * eq = m.mk_eq(arg, mk_zero_for(arg));
                if (strict)
                    even_eqs.push_back(m.mk_not(eq));
                else
                    even_eqs.push_back(eq);
            }
            else {
                odd_factors.push_back(arg);
            }
        }
    }

    // Strict case
    // p1^{2*k1} * p2^{2*k2 + 1} >< 0
    // -->
    // p1 != 0 and p2 >< 0
    //
    // Nonstrict
    // p1^{2*k1} * p2^{2*k2 + 1} >=< 0
    // -->
    // p1 = 0 or p2 >=< 0
    //
    void mk_split_comp(decl_kind k, polynomial::factors const & fs, expr_ref & result) {
        SASSERT(k == OP_LT || k == OP_GT || k == OP_LE || k == OP_GE);
        bool strict = (k == OP_LT) || (k == OP_GT);
        expr_ref_buffer args(m);
        expr_ref_buffer odd_factors(m);
        split_even_odd(strict, fs, args, odd_factors);
        if (odd_factors.empty()) {
            if (k == OP_LT) {
                result = m.mk_false();
                return;
            }
            if (k == OP_GE) {
                result = m.mk_true();
                return;
            }
        }
        else {
            args.push_back(m.mk_app(m_util.get_family_id(), k, mk_mul(odd_factors.size(), odd_factors.data()), mk_zero_for(odd_factors[0])));
        }
        SASSERT(!args.empty());
        if (args.size() == 1)
            result = args[0];
        else if (strict)
            result = m.mk_and(args);
        else
            result = m.mk_or(args);
    }

    br_status factor(func_decl * f, expr * lhs, expr * rhs, expr_ref & result) {
        polynomial_ref p1(m_pm);
        polynomial_ref p2(m_pm);
        scoped_mpz d1(m_qm);
        scoped_mpz d2(m_qm);
        m_expr2poly.to_polynomial(lhs, p1, d1);
        m_expr2poly.to_polynomial(rhs, p2, d2);
        TRACE(factor_tactic_bug,
              tout << "lhs: " << mk_ismt2_pp(lhs, m) << "\n";
              tout << "p1:  " << p1 << "\n";
              tout << "d1:  " << d1 << "\n";
              tout << "rhs: " << mk_ismt2_pp(rhs, m) << "\n";
              tout << "p2:  " << p2 << "\n";
              tout << "d2:  " << d2 << "\n";);
        scoped_mpz lcm(m_qm);
        m_qm.lcm(d1, d2, lcm);
        m_qm.div(lcm, d1, d1);
        m_qm.div(lcm, d2, d2);
        m_qm.neg(d2);
        polynomial_ref p(m_pm);
        p = m_pm.addmul(d1, m_pm.mk_unit(), p1, d2, m_pm.mk_unit(), p2);
        if (is_const(p))
            return BR_FAILED;
        polynomial::factors fs(m_pm);
        TRACE(factor_tactic_bug, tout << "p: " << p << "\n";);
        m_pm.factor(p, fs, m_fparams);
        SASSERT(fs.distinct_factors() > 0);
        TRACE(factor_tactic_bug, tout << "factors:\n"; fs.display(tout); tout << "\n";);
        if (fs.distinct_factors() == 1 && fs.get_degree(0) == 1)
            return BR_FAILED;
        if (m.is_eq(f)) {
            if (m_split_factors)
                mk_split_eq(fs, result);
            else
                mk_eq(fs, result);
        }
        else {
            decl_kind k = f->get_decl_kind();
            if (m_qm.is_neg(fs.get_constant()))
                k = flip(k);

            if (m_split_factors)
                mk_split_comp(k, fs, result);
            else
                mk_comp(k, fs, result);
        }
        return BR_DONE;
    }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        if (num != 2)
            return BR_FAILED;
        if (m.is_eq(f) && (m_util.is_arith_expr(args[0]) || m_util.is_arith_expr(args[1])) && (!m.is_bool(args[0])))
            return factor(f, args[0], args[1], result);
        if (f->get_family_id() != m_util.get_family_id())
            return BR_FAILED;
        switch (f->get_decl_kind()) {
        case OP_LT:
        case OP_GT:
        case OP_LE:
        case OP_GE:
            return factor(f, args[0], args[1], result);
        }
        return BR_FAILED;
    }
};

struct factor_simplifier::rw : public rewriter_tpl<factor_simplifier::rw_cfg> {
    rw_cfg m_cfg;
    rw(ast_manager & m, params_ref const & p):
        rewriter_tpl<rw_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, p) {
    }
};

factor_simplifier::factor_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s)
    : dependent_expr_simplifier(m, s), m_params(p), m_rw(alloc(rw, m, p)) {}

void factor_simplifier::updt_params(params_ref const& p) {
    m_params.append(p);
    m_rw->cfg().updt_params(m_params);
}

void factor_simplifier::collect_param_descrs(param_descrs& r) {
    r.insert("split_factors", CPK_BOOL,
             "apply simplifications such as (= (* p1 p2) 0) --> (or (= p1 0) (= p2 0)).", "true");
    polynomial::factor_params::get_param_descrs(r);
}

void factor_simplifier::reduce() {
    expr_ref  new_curr(m);
    proof_ref new_pr(m);
    for (unsigned idx : indices()) {
        auto const& d = m_fmls[idx];
        m_rw->operator()(d.fml(), new_curr, new_pr);
        if (new_curr != d.fml())
            m_fmls.update(idx, dependent_expr(m, new_curr, mp(d.pr(), new_pr), d.dep()));
    }
}

dependent_expr_simplifier* mk_factor_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s) {
    return alloc(factor_simplifier, m, p, s);
}
