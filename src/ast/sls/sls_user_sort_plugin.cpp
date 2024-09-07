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


    void user_sort_plugin::init_egraph(euf::egraph& g) {
        ptr_vector<euf::enode> args;
        for (auto t : ctx.subterms()) {
            args.reset();
            if (is_app(t)) {
                for (auto* arg : *to_app(t)) {
                    args.push_back(g.find(arg));
                }
            }
            g.mk(t, 0, args.size(), args.data());
        }
        for (auto lit : ctx.root_literals()) {
            if (!ctx.is_true(lit) || lit.sign())
                continue;
            auto e = ctx.atom(lit.var());
            expr* x, * y;
            if (e && m.is_eq(e, x, y))
                g.merge(g.find(x), g.find(y), nullptr);
        }
        display(verbose_stream());     


        typedef obj_map<sort, unsigned> map1;
        typedef obj_map<euf::enode, expr*> map2;

        m_num_elems = alloc(map1);
        m_root2value = alloc(map2);
        m_pinned = alloc(expr_ref_vector, m);

        for (auto n : g.nodes()) {
            if (n->is_root() && is_user_sort(n->get_sort())) {
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
}
