/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sls_user_sort_plugin.cpp

Abstract:

    Theory plugin for user sort local search

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-06

--*/

#include "ast/sls/sls_user_sort_plugin.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"


namespace sls {
        
    user_sort_plugin::user_sort_plugin(context& ctx):
        plugin(ctx)
    {
        m_fid = user_sort_family_id;
    }

    void user_sort_plugin::start_propagation() {
        m_g = alloc(euf::egraph, m);
        init_egraph(*m_g);
    }

    void user_sort_plugin::propagate_literal(sat::literal lit) {
        SASSERT(ctx.is_true(lit));
        auto e = ctx.atom(lit.var());
        expr* x, * y;

        auto block = [&](euf::enode* a, euf::enode* b) {
            ptr_vector<size_t> explain;
            m_g->explain_eq<size_t>(explain, nullptr, a, b);
            m_g->end_explain();
            unsigned n = 1;
            sat::literal_vector lits;
            lits.push_back(~lit);
            sat::literal flit = lit;
            for (auto p : explain) {
                sat::literal l = to_literal(p);
                if (!ctx.is_true(l))
                    return sat::null_literal;
                if (ctx.is_unit(l)) 
                    continue;      
                lits.push_back(~l);
                if (ctx.rand(++n) == 0)
                    flit = l;
            }
            ctx.add_clause(lits);
            return flit;
        };   

        if (e && m.is_eq(e, x, y) && m.is_uninterp(x->get_sort())) {
            auto vx = get_value(x);
            auto vy = get_value(y);
            bool should_flip = lit.sign() ? vx == vy : vx != vy;
            if (should_flip) {
                sat::literal flit = lit;

                if (lit.sign()) {
                    auto a = m_g->find(x);
                    auto b = m_g->find(y);
                    flit = block(a, b);                    
                }                
                
                if (flit != sat::null_literal)
                    ctx.flip(flit.var());                    
            }
        }
        else if (e && m.is_distinct(e) && !lit.sign()) {
            auto n = to_app(e)->get_num_args();
            for (unsigned i = 0; i < n; ++i) {
                auto a = m_g->find(to_app(e)->get_arg(i));
                for (unsigned j = i + 1; j < n; ++j) {
                    auto b = m_g->find(to_app(e)->get_arg(j));
                    if (a->get_root() == b->get_root()) {
                        verbose_stream() << "block " << mk_bounded_pp(e, m) << "\n";
                        auto flit = block(a, b);
                        if (flit != sat::null_literal)
                            ctx.flip(flit.var());
                    }
                }
            }
        }
        else if (e && lit.sign()) {
            auto a = m_g->find(e);
            auto b = m_g->find(m.mk_true());

            if (a->get_root() == b->get_root()) {
                verbose_stream() << "block " << lit << "\n";
                auto flit = block(a, b);
                if (flit != sat::null_literal)
                    ctx.flip(flit.var());
            }                
        }
    }


    void user_sort_plugin::init_egraph(euf::egraph& g) {
        ptr_vector<euf::enode> args;
        for (auto t : ctx.subterms()) {
            args.reset();
            if (is_app(t)) 
                for (auto* arg : *to_app(t)) 
                    args.push_back(g.find(arg));                
            g.mk(t, 0, args.size(), args.data());
        }
        if (!g.find(m.mk_true()))
            g.mk(m.mk_true(), 0, 0, nullptr);
        if (!g.find(m.mk_false()))
            g.mk(m.mk_false(), 0, 0, nullptr);
        for (auto lit : ctx.root_literals()) {
            if (!ctx.is_true(lit))
                lit.neg();
            auto e = ctx.atom(lit.var());
            expr* x, * y;
            if (e && m.is_eq(e, x, y) && !lit.sign()) 
                g.merge(g.find(x), g.find(y), to_ptr(lit));
            else if (!lit.sign())
                g.merge(g.find(e), g.find(m.mk_true()), to_ptr(lit));
        }
        g.propagate();

        typedef obj_map<sort, unsigned> map1;
        typedef obj_map<euf::enode, expr*> map2;

        m_num_elems = alloc(map1);
        m_root2value = alloc(map2);
        m_pinned = alloc(expr_ref_vector, m);

        for (auto n : g.nodes()) {
            if (n->is_root() && is_user_sort(n->get_sort())) {
                // verbose_stream() << "init root " << g.pp(n) << "\n";
                unsigned num = 0;
                m_num_elems->find(n->get_sort(), num);
                expr* v = m.mk_model_value(num, n->get_sort());
                m_pinned->push_back(v);
                m_root2value->insert(n, v);
                m_num_elems->insert(n->get_sort(), num + 1);
            }
        }
    }


    expr_ref user_sort_plugin::get_value(expr* e) {
        if (m.is_model_value(e))
            return expr_ref(e, m);

        if (!m_g) {
            m_g = alloc(euf::egraph, m);
            init_egraph(*m_g);
        }
        auto n = m_g->find(e)->get_root();
        VERIFY(m_root2value->find(n, e));
        return expr_ref(e, m);
    }

    std::ostream& user_sort_plugin::display(std::ostream& out) const {
        if (m_g)
            m_g->display(out);
        return out;
    }

    bool user_sort_plugin::is_sat() {
        return true;
        bool flipped = false;
        ptr_vector<euf::enode> args;
        euf::egraph g(m);
        auto assert_lit = [&](auto lit) {
            auto e = ctx.atom(lit.var());
            expr* x, * y;
            if (e && m.is_eq(e, x, y) && !lit.sign())
                g.merge(g.find(x), g.find(y), nullptr);
            else if (e && m.is_eq(e) && lit.sign())
                g.merge(g.find(e), g.find(m.mk_false()), nullptr);
            else
                g.merge(g.find(e), g.find(m.mk_bool_val(!lit.sign())), nullptr);
            g.propagate();
        };
        g.mk(m.mk_false(), 0, 0, nullptr);
        g.mk(m.mk_true(), 0, 0, nullptr);
        for (auto t : ctx.subterms()) {
            if (g.find(t))
                continue;
            args.reset();
            if (is_app(t)) {
                for (auto* arg : *to_app(t)) {
                    args.push_back(g.find(arg));
                }
            }
            g.mk(t, 0, args.size(), args.data());
        }
        for (auto lit : ctx.root_literals()) {
            if (!ctx.is_true(lit))
                lit.neg();

            g.push();
            assert_lit(lit);
            bool is_unsat = g.inconsistent();
            g.pop(1);
            if (is_unsat) {
                ctx.flip(lit.var());
                lit.neg();
                flipped = true;
            }
            assert_lit(lit);

        }
        return !flipped;
    }
}
