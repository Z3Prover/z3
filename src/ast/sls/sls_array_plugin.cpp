/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sls_array_plugin.cpp

Abstract:

    Theory plugin for arrays local search

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-06

--*/

#include "ast/sls/sls_array_plugin.h"


namespace sls {

        
    array_plugin::array_plugin(context& ctx):
        plugin(ctx),
        a(m)
    {
        m_fid = a.get_family_id();
    }


    bool array_plugin::is_sat() {
        euf::egraph g(m);
        init_egraph(g);

        return false;
    }

    void array_plugin::init_kv(euf::egraph& g, kv& kv) {
        for (auto n : g.nodes()) {
            if (!n->is_root() || !a.is_array(n->get_expr()))
                continue;
            kv.insert(n, obj_map<euf::enode, euf::enode*>());
            for (auto p : euf::enode_parents(n)) {
                if (!a.is_select(p->get_expr()))
                    continue;
                SASSERT(n->num_args() == 2);
                if (p->get_arg(0)->get_root() != n->get_root())
                    continue;
                auto idx = n->get_arg(1)->get_root();
                auto val = p->get_root();
                kv[n].insert(idx, val);
            }
        }
    }

    void array_plugin::saturate_store(euf::egraph& g, kv& kv) {
        for (auto n : g.nodes()) {
            if (!a.is_store(n->get_expr()))
                continue;
            SASSERT(n->num_args() == 3);
            auto idx = n->get_arg(1)->get_root();
            auto val = n->get_arg(2)->get_root();
            auto arr = n->get_arg(0)->get_root();
#if 0
            auto it = kv.find(arr);
            if (it == kv.end())
                continue;
            auto it2 = it->get_value().find(idx);
            if (it2 == nullptr)
                continue;
            g.merge(val, it2->get_value(), nullptr);
#endif
        }
    }

    void array_plugin::init_egraph(euf::egraph& g) {
        ptr_vector<euf::enode> args;
        for (auto t : ctx.subterms()) {
            args.reset();
            if (is_app(t)) {
                for (auto* arg : *to_app(t)) {
                    args.push_back(g.find(arg));
                }
            }
            auto n = g.mk(t, 0, args.size(), args.data());
            if (a.is_array(t))
                continue;
            auto v = ctx.get_value(t);
            auto n2 = g.mk(v, 0, 0, nullptr);
            g.merge(n, n2, nullptr);
        }
        for (auto lit : ctx.root_literals()) {
            if (!ctx.is_true(lit))
                continue;
            auto e = ctx.atom(lit.var());
            expr* x, * y;
            if (e && m.is_eq(e, x, y))
                g.merge(g.find(x), g.find(y), nullptr);
        }
    }


}
