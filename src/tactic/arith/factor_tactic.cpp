/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    factor_tactic.cpp

Abstract:

    Polynomial factorization tactic.

Author:

    Leonardo de Moura (leonardo) 2012-02-03

Revision History:

--*/
#include"tactical.h"
#include"expr2polynomial.h"
#include"rewriter_def.h"

class factor_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
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
            for (unsigned i = 0; i < fs.distinct_factors(); i++) {
                m_expr2poly.to_expr(fs[i], true, arg);
                args.push_back(arg);
            }
            result = m.mk_eq(mk_mul(args.size(), args.c_ptr()), mk_zero_for(arg));
        }

        // p1^k1 * p2^k2 = 0 --> p1 = 0 or p2 = 0
        void mk_split_eq(polynomial::factors const & fs, expr_ref & result) {
            expr_ref_buffer args(m);
            expr_ref arg(m);
            for (unsigned i = 0; i < fs.distinct_factors(); i++) {
                m_expr2poly.to_expr(fs[i], true, arg);
                args.push_back(m.mk_eq(arg, mk_zero_for(arg)));
            }
            if (args.size() == 1)
                result = args[0];
            else
                result = m.mk_or(args.size(), args.c_ptr());
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
            for (unsigned i = 0; i < fs.distinct_factors(); i++) {
                m_expr2poly.to_expr(fs[i], true, arg);
                if (fs.get_degree(i) % 2 == 0)
                    arg = m_util.mk_power(arg, m_util.mk_numeral(rational(2), m_util.is_int(arg)));
                args.push_back(arg);
            }
            expr * lhs = mk_mul(args.size(), args.c_ptr());
            result = m.mk_app(m_util.get_family_id(), k, lhs, mk_zero_for(lhs));
        }

        // See mk_split_strict_comp and mk_split_nonstrict_comp
        void split_even_odd(bool strict, polynomial::factors const & fs, expr_ref_buffer & even_eqs, expr_ref_buffer & odd_factors) {
            expr_ref arg(m);
            for (unsigned i = 0; i < fs.distinct_factors(); i++) {
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
                args.push_back(m.mk_app(m_util.get_family_id(), k, mk_mul(odd_factors.size(), odd_factors.c_ptr()), mk_zero_for(odd_factors[0])));
            }
            SASSERT(!args.empty());
            if (args.size() == 1)
                result = args[0];
            else if (strict)
                result = m.mk_and(args.size(), args.c_ptr());
            else
                result = m.mk_or(args.size(), args.c_ptr());
        }

        br_status factor(func_decl * f, expr * lhs, expr * rhs, expr_ref & result) {
            polynomial_ref p1(m_pm);
            polynomial_ref p2(m_pm);
            scoped_mpz d1(m_qm);
            scoped_mpz d2(m_qm);
            m_expr2poly.to_polynomial(lhs, p1, d1);
            m_expr2poly.to_polynomial(rhs, p2, d2);
            TRACE("factor_tactic_bug",
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
            TRACE("factor_tactic_bug", tout << "p: " << p << "\n";);
            m_pm.factor(p, fs, m_fparams);
            SASSERT(fs.distinct_factors() > 0);
            TRACE("factor_tactic_bug", tout << "factors:\n"; fs.display(tout); tout << "\n";);
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

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;

        rw(ast_manager & m, params_ref const & p):
            rewriter_tpl<rw_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(m, p) {
        }
    };

    struct imp {
        ast_manager & m;
        rw            m_rw;

        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            m_rw(m, p) {
        }


        void updt_params(params_ref const & p) {
            m_rw.cfg().updt_params(p);
        }

        void operator()(goal_ref const & g,
                        goal_ref_buffer & result,
                        model_converter_ref & mc,
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            mc = 0; pc = 0; core = 0;
            tactic_report report("factor", *g);
            bool produce_proofs = g->proofs_enabled();

            expr_ref   new_curr(m);
            proof_ref  new_pr(m);
            unsigned   size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                expr * curr = g->form(idx);
                m_rw(curr, new_curr, new_pr);
                if (produce_proofs) {
                    proof * pr = g->pr(idx);
                    new_pr     = m.mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));
            }
            g->inc_depth();
            result.push_back(g.get());
            TRACE("factor", g->display(tout););
            SASSERT(g->is_well_sorted());
        }
    };

    imp *      m_imp;
    params_ref m_params;
public:
    factor_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(factor_tactic, m, m_params);
    }

    virtual ~factor_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->m_rw.cfg().updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
        r.insert("split_factors", CPK_BOOL,
                 "(default: true) apply simplifications such as (= (* p1 p2) 0) --> (or (= p1 0) (= p2 0)).");
        polynomial::factor_params::get_param_descrs(r);
    }

    virtual void operator()(goal_ref const & in,
                            goal_ref_buffer & result,
                            model_converter_ref & mc,
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        try {
            (*m_imp)(in, result, mc, pc, core);
        }
        catch (z3_error & ex) {
            throw ex;
        }
        catch (z3_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }

    virtual void cleanup() {
        imp * d = alloc(imp, m_imp->m, m_params);
        std::swap(d, m_imp);        
        dealloc(d);
    }


};

tactic * mk_factor_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(factor_tactic, m, p));
}



