/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_diagnostics.cpp

Abstract:

    Theory plugin for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "ast/ast_util.h"
#include "ast/scoped_proof.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_solver.h"


namespace arith {

    
    std::ostream& solver::display(std::ostream& out) const { 
        lp().display(out);
        
        if (m_nla) {
            m_nla->display(out);
        }
        unsigned nv = get_num_vars();
        for (unsigned v = 0; v < nv; ++v) {
            auto t = get_tv(v);
            auto vi = lp().external_to_column_index(v);
            out << "v" << v << " ";
            if (is_bool(v)) {
                euf::enode* n = var2enode(v);
                api_bound* b = nullptr;
                if (m_bool_var2bound.find(n->bool_var(), b)) {
                    sat::literal lit = b->get_lit();
                    out << lit << " " << s().value(lit);
                }
            }
            else {
                if (t.is_null()) 
                    out << "null"; 
                else 
                    out << (t.is_term() ? "t" : "j") << vi;
                if (m_nla && m_nla->use_nra_model() && is_registered_var(v)) {
                    scoped_anum an(m_nla->am());
                    m_nla->am().display(out << " = ", nl_value(v, an));
                }
                else if (can_get_value(v) && !m_solver->has_changed_columns())  
                    out << " = " << get_value(v);
                if (is_int(v)) 
                    out << ", int";
                if (ctx.is_shared(var2enode(v))) 
                    out << ", shared";
            }
            expr* e = var2expr(v);
            out << " := ";
            if (e)
                out << "#" << e->get_id() << ": ";
            out << mk_bounded_pp(var2expr(v), m) << "\n";
        }
        return out; 
    }

    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const { 
        return euf::th_explain::from_index(idx).display(out);
    }

    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const { 
        return display_justification(out, idx);
    }

    void solver::collect_statistics(statistics& st) const {
        m_stats.collect_statistics(st);
        lp().settings().stats().collect_statistics(st);
        if (m_nla) m_nla->collect_statistics(st);
    }

    void solver::explain_assumptions() {
        unsigned i = 0;
        for (auto const & ev : m_explanation) {
            ++i;
            auto idx = ev.ci();
            if (UINT_MAX == idx)
                continue;
            switch (m_constraint_sources[idx]) {
            case inequality_source: {
                literal lit = m_inequalities[idx];
                m_arith_hint.add_lit(ev.coeff(), lit);
                break;                
            }
            case equality_source: {
                auto [u, v] = m_equalities[idx];
                m_arith_hint.add_eq(u, v);
                break;
            }
            default:
                break;
            }
        }
    }

    /**
     * It may be necessary to use the following assumption when checking Farkas claims
     * generated from bounds propagation:
     * A bound literal ax <= b is explained by a set of weighted literals
     * r1*(a1*x <= b1) + .... + r_k*(a_k*x <= b_k), where r_i > 0
     * such that there is a r >= 1
     * (r1*a1+..+r_k*a_k) = r*a, (r1*b1+..+r_k*b_k) <= r*b
     */
    arith_proof_hint const* solver::explain(hint_type ty, sat::literal lit) {
        if (!ctx.use_drat())
            return nullptr;
        m_arith_hint.set_type(ctx, ty);
        explain_assumptions();
        if (lit != sat::null_literal)
            m_arith_hint.add_lit(rational(1), ~lit);
        return m_arith_hint.mk(ctx);
    }

    arith_proof_hint const* solver::explain_implied_eq(euf::enode* a, euf::enode* b) {
        if (!ctx.use_drat())
            return nullptr;
        m_arith_hint.set_type(ctx, hint_type::implied_eq_h);
        explain_assumptions();
        m_arith_hint.add_diseq(a, b);
        return m_arith_hint.mk(ctx);
    }

    expr* arith_proof_hint::get_hint(euf::solver& s) const {
        ast_manager& m = s.get_manager();
        family_id fid = m.get_family_id("arith");
        arith_util arith(m);
        solver& a = dynamic_cast<solver&>(*s.fid2solver(fid));
        char const* name;
        switch (m_ty) {
        case hint_type::farkas_h:
            name = "farkas";
            break;
        case hint_type::bound_h:
            name = "bound";
            break;
        case hint_type::implied_eq_h:
            name = "implied-eq";
            break;
        }
        rational lc(1);
        for (unsigned i = m_lit_head; i < m_lit_tail; ++i) 
            lc = lcm(lc, denominator(a.m_arith_hint.lit(i).first));
            
        expr_ref_vector args(m);
        sort_ref_vector sorts(m);
        for (unsigned i = m_lit_head; i < m_lit_tail; ++i) {            
            auto const& [coeff, lit] = a.m_arith_hint.lit(i);
            args.push_back(arith.mk_int(abs(coeff*lc)));
            args.push_back(s.literal2expr(lit));
        }
        for (unsigned i = m_eq_head; i < m_eq_tail; ++i) {
            auto const& [x, y, is_eq] = a.m_arith_hint.eq(i);            
            expr_ref eq(m.mk_eq(x->get_expr(), y->get_expr()), m);
            if (!is_eq) eq = m.mk_not(eq);
            args.push_back(arith.mk_int(1));
            args.push_back(eq);
        }
        for (expr* arg : args)
            sorts.push_back(arg->get_sort());
        sort* range = m.mk_proof_sort();
        func_decl* d = m.mk_func_decl(symbol(name), args.size(), sorts.data(), range);
        expr* r = m.mk_app(d, args);
        return r;
    }
}
