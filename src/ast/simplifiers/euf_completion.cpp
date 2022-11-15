/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    euf_completion.cpp

Abstract:

    Ground completion for equalities

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

Notes:

Create a congruence closure of E.
Select _simplest_ term in each equivalence class. A term is _simplest_
if it is smallest in a well-order, such as a ground Knuth-Bendix order.
A basic approach is terms that are of smallest depth, are values can be chosen as simplest.
Ties between equal-depth terms can be resolved arbitrarily.


Algorithm for extracting canonical form from an E-graph:

* Compute function canon(t) that maps every term in E to a canonical, least with respect to well-order relative to the congruence closure.
  That is, terms that are equal modulo the congruence closure have the same canonical representative.

* Each f(t) = g(s) in E:
  * add f(canon(t)) = canon(f(t)), g(canon(s)) = canon(g(s)) where canon(f(t)) = canon(g(s)) by construction.
  
* Each other g(t) in E:
  * add g(canon(t)) to E.
  * Note that canon(g(t)) = true because g(t) = true is added to congruence closure of E.
* We claim the new formula is equivalent.
* The dependencies for each rewrite can be computed by following the equality justification data-structure.


--*/

#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/euf/euf_egraph.h"
#include "ast/simplifiers/euf_completion.h"

namespace euf {

    completion::completion(ast_manager& m, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_egraph(m),
        m_canonical(m),
        m_eargs(m),
        m_deps(m),
        m_rewriter(m) {
        m_tt = m_egraph.mk(m.mk_true(), 0, 0, nullptr);
        m_ff = m_egraph.mk(m.mk_false(), 0, 0, nullptr);
    }

    void completion::reduce() {
        ++m_epoch;
        add_egraph();
        map_canonical();
        read_egraph();
    }

    void completion::add_egraph() {
        m_nodes.reset();
        unsigned sz = m_fmls.size();
        expr* x, *y;
        for (unsigned i = m_qhead; i < sz; ++i) {
            auto [f,d] = m_fmls[i]();
            auto* n = mk_enode(f);
            if (m.is_eq(f, x, y)) 
                m_egraph.merge(n->get_arg(0), n->get_arg(1), d);
            if (m.is_not(f, x)) 
                m_egraph.merge(n->get_arg(0), m_ff, d);
            else 
                m_egraph.merge(n, m_tt, d);
        }
        m_egraph.propagate();
    }

    void completion::read_egraph() {

        if (m_egraph.inconsistent()) {
            auto* d = explain_conflict();
            dependent_expr de(m, m.mk_false(), d);
            m_fmls.update(0, de);
            return;
        }

        unsigned sz = m_fmls.size();
        for (unsigned i = m_qhead; i < sz; ++i) {
            auto [f, d] = m_fmls[i]();
            
            expr_dependency_ref dep(d, m);
            expr_ref g = canonize_fml(f, dep);
            if (g != f) {
                m_fmls.update(i, dependent_expr(m, g, dep));
                m_stats.m_num_rewrites++;
                IF_VERBOSE(11, verbose_stream() << mk_bounded_pp(f, m, 3) << " -> " << mk_bounded_pp(g, m, 3) << "\n");
            }
            CTRACE("euf_completion", g != f, tout << mk_bounded_pp(f, m) << " -> " << mk_bounded_pp(g, m) << "\n");
        }
        advance_qhead(m_fmls.size());
    }

    enode* completion::mk_enode(expr* e) {
        m_todo.push_back(e);
        enode* n;
        while (!m_todo.empty()) {
            e = m_todo.back();
            if (m_egraph.find(e)) {
                m_todo.pop_back();
                continue;
            }
            if (!is_app(e)) {
                m_nodes.push_back(m_egraph.mk(e, 0, 0, nullptr));
                m_todo.pop_back();
                continue;
            }
            m_args.reset();
            unsigned sz = m_todo.size();
            for (expr* arg : *to_app(e)) {
                n = m_egraph.find(arg);
                if (n)
                    m_args.push_back(n);
                else 
                    m_todo.push_back(arg);
            }
            if (sz == m_todo.size()) {
                m_nodes.push_back(m_egraph.mk(e, 0, m_args.size(), m_args.data()));
                m_todo.pop_back();
            }
        }
        return m_egraph.find(e);
    }

    expr_ref completion::canonize_fml(expr* f, expr_dependency_ref& d) {

        expr* x, * y;
        if (m.is_eq(f, x, y)) {
            expr_ref x1 = canonize(x, d);
            expr_ref y1 = canonize(y, d);

            if (x == x1 && y == y1)
                return expr_ref(f, m);
            if (x1 == y1)
                return expr_ref(m.mk_true(), m);
            else {
                expr* c = get_canonical(x, d);
                if (c == x1)
                    return expr_ref(m.mk_eq(y1, c), m);
                else if (c == y1)
                    return expr_ref(m.mk_eq(x1, c), m);
                else
                    return expr_ref(m.mk_and(m.mk_eq(x1, c), m.mk_eq(y1, c)), m);
            }
        }

        if (m.is_not(f, x)) {
            expr_ref x1 = canonize(x, d);
            return expr_ref(mk_not(m, x1), m);
        }

        return canonize(f, d);
    }

    expr_ref completion::canonize(expr* f, expr_dependency_ref& d) {
        if (!is_app(f))
            return expr_ref(f, m); // todo could normalize ground expressions under quantifiers

        m_eargs.reset();
        bool change = false;
        for (expr* arg : *to_app(f)) {
            m_eargs.push_back(get_canonical(arg, d));
            change |= arg != m_eargs.back();
        }

        if (!change) 
            return expr_ref(f, m);        
        else
            return expr_ref(m_rewriter.mk_app(to_app(f)->get_decl(), m_eargs.size(), m_eargs.data()), m);
    }

    expr* completion::get_canonical(expr* f, expr_dependency_ref& d) {
        enode* n = m_egraph.find(f);
        enode* r = n->get_root();
        d = m.mk_join(d, explain_eq(n, r));
        d = m.mk_join(d, m_deps.get(r->get_id(), nullptr));        
        return m_canonical.get(r->get_id());
    }
    
    expr* completion::get_canonical(enode* n) {
        if (m_epochs.get(n->get_id(), 0) == m_epoch)
            return m_canonical.get(n->get_id());
        else
            return nullptr;
    }

    void completion::set_canonical(enode* n, expr* e) {
        class vtrail : public trail {
            expr_ref_vector& c;
            unsigned idx;
            expr_ref old_value;
        public:
            vtrail(expr_ref_vector& c, unsigned idx) : 
                c(c), idx(idx), old_value(c.get(idx), c.m()) {
            }
        
            void undo() override {
                c[idx] = old_value;
                old_value = nullptr;
            }
        };
        if (num_scopes() > 0)
            m_trail.push(vtrail(m_canonical, n->get_id()));
        m_canonical.setx(n->get_id(), e);
        m_epochs.setx(n->get_id(), m_epoch, 0);
    }

    expr_dependency* completion::explain_eq(enode* a, enode* b) {
        if (a == b)
            return nullptr;
        ptr_vector<expr_dependency> just;
        m_egraph.begin_explain();
        m_egraph.explain_eq(just, nullptr, a, b);
        m_egraph.end_explain();
        expr_dependency* d = nullptr;
        for (expr_dependency* d2 : just)
            d = m.mk_join(d, d2);
        return d;
    }

    expr_dependency* completion::explain_conflict() {
        ptr_vector<expr_dependency> just;
        m_egraph.begin_explain();
        m_egraph.explain(just, nullptr);
        m_egraph.end_explain();
        expr_dependency* d = nullptr;
        for (expr_dependency* d2 : just)
            d = m.mk_join(d, d2);
        return d;
    }

    void completion::collect_statistics(statistics& st) const {
        st.update("euf-completion-rewrites", m_stats.m_num_rewrites);        
    }

    void completion::map_canonical() {
        m_todo.reset();
        enode_vector roots;
        for (unsigned i = 0; i < m_nodes.size(); ++i) {
            enode* n = m_nodes[i]->get_root();
            if (n->is_marked1())
                continue;
            n->mark1();
            roots.push_back(n);
            enode* rep = nullptr;
            for (enode* k : enode_class(n)) 
                if (!rep || m.is_value(k->get_expr()) || get_depth(rep->get_expr()) > get_depth(k->get_expr()))
                    rep = k;
            m_reps.setx(n->get_id(), rep, nullptr);

            TRACE("euf_completion", tout << "rep " << m_egraph.bpp(n) << " -> " << m_egraph.bpp(rep) << "\n";
                         for (enode* k : enode_class(n)) tout << m_egraph.bpp(k) << "\n";);
            m_todo.push_back(n->get_expr());
            for (enode* arg : enode_args(n)) {
                arg = arg->get_root();
                if (!arg->is_marked1())
                    m_nodes.push_back(arg);
            }
        }
        for (enode* r : roots)
            r->unmark1();

        // explain dependencies when no nodes are marked.
        // explain_eq uses both mark1 and mark2 on e-nodes so 
        // we cannot call it inside the previous loop where mark1 is used
        // to track which roots have been processed.
        for (enode* r : roots) {
            enode* rep = m_reps[r->get_id()];
            auto* d = explain_eq(r, rep);
            m_deps.setx(r->get_id(), d);
        }
        expr_ref new_expr(m);
        while (!m_todo.empty()) {
            expr* e = m_todo.back();
            enode* n = m_egraph.find(e);
            SASSERT(n->is_root());
            enode* rep = m_reps[n->get_id()];
            if (get_canonical(n)) 
                m_todo.pop_back();
            else if (get_depth(rep->get_expr()) == 0 || !is_app(rep->get_expr())) {
                set_canonical(n, rep->get_expr());
                m_todo.pop_back();
            }
            else {
                m_eargs.reset();
                unsigned sz = m_todo.size();
                bool new_arg = false;
                expr_dependency* d = m_deps.get(n->get_id(), nullptr);
                for (enode* arg : enode_args(rep)) {
                    enode* rarg = arg->get_root();
                    expr* c = get_canonical(rarg);
                    if (c) {
                        m_eargs.push_back(c);
                        new_arg |= c != arg->get_expr();
                        d = m.mk_join(d, m_deps.get(rarg->get_id(), nullptr));
                    }
                    else
                        m_todo.push_back(rarg->get_expr());
                }
                if (sz == m_todo.size()) {
                    m_todo.pop_back();
                    if (new_arg) 
                        new_expr = m_rewriter.mk_app(to_app(rep->get_expr())->get_decl(), m_eargs.size(), m_eargs.data());                    
                    else
                        new_expr = rep->get_expr();                        
                    set_canonical(n, new_expr);
                    m_deps.setx(n->get_id(), d);
                }
            }
        }
    }        
}


