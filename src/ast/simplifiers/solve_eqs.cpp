/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    solve_eqs.cpp

Abstract:

    simplifier for solving equations

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

--*/


#include "util/trace.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/simplifiers/solve_eqs.h"


namespace euf {

    class basic_extract_eq : public extract_eq {
        ast_manager& m;
    public:
        basic_extract_eq(ast_manager& m) : m(m) {}
        void get_eqs(dependent_expr const& e, dep_eq_vector& eqs) {
            auto [f, d] = e();
            expr* x, * y;
            if (m.is_eq(f, x, y)) {
                if (is_uninterp_const(x))
                    eqs.push_back(dependent_eq(to_app(x), expr_ref(y, m), d));
                if (is_uninterp_const(y))
                    eqs.push_back(dependent_eq(to_app(y), expr_ref(x, m), d));
            }
            expr* c, * th, * el, * x1, * y1, * x2, * y2;
            if (m.is_ite(f, c, th, el)) {
                if (m.is_eq(th, x1, y1) && m.is_eq(el, x2, y2)) {
                    if (x1 == y2 && is_uninterp_const(x1))
                        std::swap(x2, y2);
                    if (x2 == y2 && is_uninterp_const(x2))
                        std::swap(x2, y2), std::swap(x1, y1);
                    if (x2 == y1 && is_uninterp_const(x2))
                        std::swap(x1, y1);
                    if (x1 == x2 && is_uninterp_const(x1)) 
                        eqs.push_back(dependent_eq(to_app(x1), expr_ref(m.mk_ite(c, y1, y2), m), d));                    
                }
            }
            if (is_uninterp_const(f))
                eqs.push_back(dependent_eq(to_app(f), expr_ref(m.mk_true(), m), d));
            if (m.is_not(f, x) && is_uninterp_const(x))
                eqs.push_back(dependent_eq(to_app(x), expr_ref(m.mk_false(), m), d));
        }
    };

    class arith_extract_eq : public extract_eq {
        ast_manager& m;
        arith_util a;
#if 0
        void solve_eq(expr* f, expr_depedency* d) {

        }
#endif
    public:
        arith_extract_eq(ast_manager& m) : m(m), a(m) {}
        void get_eqs(dependent_expr const& e, dep_eq_vector& eqs) {
#if 0
            auto [f, d] = e();
            expr* x, * y;
            if (m.is_eq(f, x, y) && a.is_int_real(x))
                ;
#endif
        }
    };

    // initialize graph that maps variable ids to next ids
    void solve_eqs::extract_dep_graph(dep_eq_vector& eqs) {
        m_var2id.reset();
        m_id2var.reset();
        m_next.reset();
        unsigned sz = 0;
        for (auto const& [v, t, d] : eqs)
            sz = std::max(sz, v->get_id());
        m_var2id.resize(sz + 1, UINT_MAX);
        for (auto const& [v, t, d] : eqs) {
            if (is_var(v))
                continue;
            m_var2id[v->get_id()] = m_id2var.size();
            m_id2var.push_back(v);
        }
        m_next.resize(m_id2var.size());

        for (auto const& eq : eqs)
            m_next[var2id(eq.var)].push_back(eq);
    }

    /**
    * Build a substitution while assigning levels to terms.
    * The substitution is well-formed when variables are replaced with terms whose
    * Free variables have higher levels.
    */
    void solve_eqs::extract_subst() {
        m_id2level.reset();
        m_id2level.resize(m_id2var.size(), UINT_MAX);
        m_subst_ids.reset();
        m_subst = alloc(expr_substitution, m, false, false);

        auto is_explored = [&](unsigned id) {
            return m_id2level[id] != UINT_MAX;
        };

        auto is_safe = [&](unsigned lvl, expr* t) {
            for (auto* e : subterms::all(expr_ref(t, m)))
                if (is_var(e) && m_id2level[var2id(e)] < lvl)
                    return false;
            return true;
        };

        unsigned init_level = UINT_MAX;
        unsigned_vector todo;
        for (unsigned id = 0; id < m_id2var.size(); ++id) {
            if (is_explored(id))
                continue;
            // initialize current level to have enough room to assign different levels to all variables.
            if (init_level < m_id2var.size() + 1)
                return;
            init_level -= m_id2var.size() + 1;
            unsigned curr_level = init_level;
            todo.push_back(id);
            while (!todo.empty()) {
                unsigned j = todo.back();
                todo.pop_back();
                if (is_explored(j))
                    continue;
                m_id2level[id] = curr_level++;
                for (auto const& eq : m_next[j]) {
                    auto const& [v, t, d] = eq;
                    if (!is_safe(curr_level, t))
                        continue;
                    m_next[j][0] = eq;
                    m_subst_ids.push_back(id);                   
                    for (expr* e : subterms::all(expr_ref(t, m))) 
                        if (is_var(e) && !is_explored(var2id(e))) 
                            todo.push_back(var2id(e));   
                    break;
                }
            }            
        }
    }

    void solve_eqs::add_subst(dependent_eq const& eq) {
        m_subst->insert(eq.var, eq.term, nullptr, eq.dep);
    }

    void solve_eqs::normalize() {
        scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m, true);
        m_subst->reset();
        rp->set_substitution(m_subst.get());

        std::sort(m_subst_ids.begin(), m_subst_ids.end(), [&](unsigned u, unsigned v) { return m_id2level[u] > m_id2level[v]; });

        expr_dependency_ref new_dep(m);
        expr_ref new_def(m);
        proof_ref new_pr(m);

        for (unsigned id : m_subst_ids) {
            // checkpoint();
            auto const& [v, def, dep] = m_next[id][0];
            rp->operator()(def, new_def, new_pr, new_dep);
            // m_num_steps += rp->get_num_steps() + 1;
            new_dep = m.mk_join(dep, new_dep);
            m_subst->insert(v, new_def, new_pr, new_dep);
            // we updated the substitution, but we don't need to reset rp
            // because all cached values there do not depend on v.
        }

        TRACE("solve_eqs",
            tout << "after normalizing variables\n";
        for (unsigned id : m_subst_ids) {
            auto const& eq = m_next[id][0];
            expr* def = nullptr;
            proof* pr = nullptr;
            expr_dependency* dep = nullptr;
            m_subst->find(eq.var, def, pr, dep);
            tout << mk_pp(eq.var, m) << "\n----->\n" << mk_pp(def, m) << "\n\n";
        });
    }

    void solve_eqs::apply_subst() {
        scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m, true);
        rp->set_substitution(m_subst.get());
        expr_ref new_f(m);
        proof_ref new_pr(m);
        expr_dependency_ref new_dep(m);
        for (unsigned i = m_qhead; i < m_fmls.size() && !m_fmls.inconsistent(); ++i) {
            auto [f, d] = m_fmls[i]();
            rp->operator()(f, new_f, new_pr, new_dep);
            if (new_f == f)
                continue;
            new_dep = m.mk_join(d, new_dep);
            m_fmls.update(i, dependent_expr(m, new_f, new_dep));
        }
    }
    
    void solve_eqs::reduce() {
        dep_eq_vector eqs;
        get_eqs(eqs);
        extract_dep_graph(eqs);
        extract_subst();
        apply_subst();
        advance_qhead(m_fmls.size());
    }

}
