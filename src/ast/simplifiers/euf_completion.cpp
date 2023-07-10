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
#include "ast/shared_occs.h"

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
        m_rewriter.set_order_eq(true);
        m_rewriter.set_flat_and_or(false);
    }

    void completion::reduce() {
        m_has_new_eq = true;
        for (unsigned rounds = 0; m_has_new_eq && rounds <= 3 && !m_fmls.inconsistent(); ++rounds) {
            ++m_epoch;
            m_has_new_eq = false;
            add_egraph();
            map_canonical();
            read_egraph();
            IF_VERBOSE(11, verbose_stream() << "(euf.completion :rounds " << rounds << ")\n");
        }
    }

    void completion::add_egraph() {
        m_nodes_to_canonize.reset();
        unsigned sz = qtail();
        auto add_children = [&](enode* n) {                
            for (auto* ch : enode_args(n))
                m_nodes_to_canonize.push_back(ch);
        };

        for (unsigned i = qhead(); i < sz; ++i) {
            expr* x, * y;
            auto [f, p, d] = m_fmls[i]();
            if (m.is_eq(f, x, y)) {
                enode* a = mk_enode(x);
                enode* b = mk_enode(y);
                m_egraph.merge(a, b, d);
                add_children(a);
                add_children(b);
            }
            else if (m.is_not(f, f)) {
                enode* n = mk_enode(f);
                m_egraph.merge(n, m_ff, d);
                add_children(n);
            }
            else {
                enode* n = mk_enode(f);
                m_egraph.merge(n, m_tt, d);
                add_children(n);
            }
        }
        m_egraph.propagate();
    }

    void completion::read_egraph() {

        if (m_egraph.inconsistent()) {
            auto* d = explain_conflict();
            dependent_expr de(m, m.mk_false(), nullptr, d);
            m_fmls.update(0, de);
            return;
        }

        unsigned sz = qtail();
        for (unsigned i = qhead(); i < sz; ++i) {
            auto [f, p, d] = m_fmls[i]();
            
            expr_dependency_ref dep(d, m);
            expr_ref g = canonize_fml(f, dep);
            if (g != f) {
                m_fmls.update(i, dependent_expr(m, g, nullptr, dep));
                m_stats.m_num_rewrites++;
                IF_VERBOSE(11, verbose_stream() << mk_bounded_pp(f, m, 3) << " -> " << mk_bounded_pp(g, m, 3) << "\n");
                update_has_new_eq(g);
            }
            CTRACE("euf_completion", g != f, tout << mk_bounded_pp(f, m) << " -> " << mk_bounded_pp(g, m) << "\n");
        }
    }

    bool completion::is_new_eq(expr* a, expr* b) {
        enode* na = m_egraph.find(a);
        enode* nb = m_egraph.find(b);
        if (!na)
            IF_VERBOSE(11, verbose_stream() << "not internalied " << mk_bounded_pp(a, m) << "\n");
        if (!nb)
            IF_VERBOSE(11, verbose_stream() << "not internalied " << mk_bounded_pp(b, m) << "\n");
        if (na && nb && na->get_root() != nb->get_root())
            IF_VERBOSE(11, verbose_stream() << m_egraph.bpp(na) << " " << m_egraph.bpp(nb) << "\n");
        return !na || !nb || na->get_root() != nb->get_root();
    }

    void completion::update_has_new_eq(expr* g) {
        expr* x, * y;
        if (m_has_new_eq)
            return;
        else if (m.is_eq(g, x, y))
            m_has_new_eq |= is_new_eq(x, y);
        else if (m.is_and(g)) {
            for (expr* arg : *to_app(g))
                update_has_new_eq(arg);
        }
        else if (m.is_not(g, g))
            m_has_new_eq |= is_new_eq(g, m.mk_false());
        else
            m_has_new_eq |= is_new_eq(g, m.mk_true());
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
                m_nodes_to_canonize.push_back(m_egraph.mk(e, 0, 0, nullptr));
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
                m_nodes_to_canonize.push_back(m_egraph.mk(e, 0, m_args.size(), m_args.data()));
                m_todo.pop_back();
            }
        }
        return m_egraph.find(e);
    }

    expr_ref completion::canonize_fml(expr* f, expr_dependency_ref& d) {

        auto is_nullary = [&](expr* e) {
            return is_app(e) && to_app(e)->get_num_args() == 0;
        };
        expr* x, * y;
        if (m.is_eq(f, x, y)) {
            expr_ref x1 = canonize(x, d);
            expr_ref y1 = canonize(y, d);

            if (is_nullary(x)) {
                SASSERT(x1 == x);
                x1 = get_canonical(x, d);
            }
            if (is_nullary(y)) {
                SASSERT(y1 == y);
                y1 = get_canonical(y, d);
            }

            if (x == y)
                return expr_ref(m.mk_true(), m);

            if (x == x1 && y == y1) 
                return m_rewriter.mk_eq(x, y);

            if (is_nullary(x) && is_nullary(y)) 
                return mk_and(m_rewriter.mk_eq(x, x1), m_rewriter.mk_eq(y, x1));

            if (x == x1 && is_nullary(x))
                return m_rewriter.mk_eq(y1, x1);

            if (y == y1 && is_nullary(y))
                return m_rewriter.mk_eq(x1, y1);
            
            if (is_nullary(x))
                return mk_and(m_rewriter.mk_eq(x, x1), m_rewriter.mk_eq(y1, x1));
            
            if (is_nullary(y))
                return mk_and(m_rewriter.mk_eq(y, y1), m_rewriter.mk_eq(x1, y1));
            
            if (x1 == y1)
                return expr_ref(m.mk_true(), m);
            else {
                expr* c = get_canonical(x, d);
                if (c == x1)
                    return m_rewriter.mk_eq(y1, c);
                else if (c == y1)
                    return m_rewriter.mk_eq(x1, c);
                else
                    return mk_and(m_rewriter.mk_eq(x1, c), m_rewriter.mk_eq(y1, c));
            }
        }

        if (m.is_not(f, x)) {
            expr_ref x1 = canonize(x, d);
            return expr_ref(mk_not(m, x1), m);
        }

        return canonize(f, d);
    }

    expr_ref completion::mk_and(expr* a, expr* b) {
        if (m.is_true(a))
            return expr_ref(b, m);
        if (m.is_true(b))
            return expr_ref(a, m);
        return expr_ref(m.mk_and(a, b), m);
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
        if (m.is_eq(f))
            return m_rewriter.mk_eq(m_eargs.get(0), m_eargs.get(1));
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
        SASSERT(m_canonical.get(r->get_id()));
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
        SASSERT(e);
        if (num_scopes() > 0 && m_canonical.size() > n->get_id())
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
        if (m_nodes_to_canonize.empty())
            return;
        for (unsigned i = 0; i < m_nodes_to_canonize.size(); ++i) {
            enode* n = m_nodes_to_canonize[i]->get_root();
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
                    m_nodes_to_canonize.push_back(arg);
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


