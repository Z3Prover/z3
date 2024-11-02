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
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"


namespace sls {
        
    array_plugin::array_plugin(context& ctx):
        plugin(ctx),
        a(m)
    {
        m_fid = a.get_family_id();
    }

    bool array_plugin::is_sat() {
        if (!m_has_arrays)
            return true;
        m_g = alloc(euf::egraph, m);
        m_kv = nullptr;
        init_egraph(*m_g);
        saturate_store(*m_g);
        return true;
    }

    // b ~ a[i -> v]
    // ensure b[i] ~ v
    // ensure b[j] ~ a[j] for j != i

    void array_plugin::saturate_store(euf::egraph& g) {
        unsigned sz = 0;
        while (sz < g.nodes().size()) {
            sz = g.nodes().size();
            for (unsigned i = 0; i < sz; ++i) {
                auto n = g.nodes()[i];
                if (!a.is_store(n->get_expr()))
                    continue;

                force_store_axiom1(g, n);

                for (auto p : euf::enode_parents(n->get_root())) 
                    if (a.is_select(p->get_expr()))
                        force_store_axiom2_down(g, n, p);
                
                auto arr = n->get_arg(0);
                for (auto p : euf::enode_parents(arr->get_root())) 
                    if (a.is_select(p->get_expr()))
                        force_store_axiom2_up(g, n, p);                
            }
        }
        display(verbose_stream() << "saturated\n");
    }

    euf::enode* array_plugin::mk_select(euf::egraph& g, euf::enode* b, euf::enode* sel) {
        auto arity = get_array_arity(b->get_sort());
        ptr_buffer<expr> args;
        ptr_buffer<euf::enode> eargs;
        args.push_back(b->get_expr());
        eargs.push_back(b);
        for (unsigned i = 1; i <= arity; ++i) {
            auto idx = sel->get_arg(i);
            eargs.push_back(idx);
            args.push_back(idx->get_expr());
        }
        expr_ref esel(a.mk_select(args), m);
        auto n = g.find(esel);
        return n ? n : g.mk(esel, 0, eargs.size(), eargs.data());
    }

    // ensure a[i->v][i] = v exists in the e-graph
    void array_plugin::force_store_axiom1(euf::egraph& g, euf::enode* n) {
        SASSERT(a.is_store(n->get_expr()));
        auto val = n->get_arg(n->num_args() - 1);
        auto nsel = mk_select(g, n, n);
        if (are_distinct(nsel, val))
            add_store_axiom1(n->get_app());
        else {
            g.merge(nsel, val, nullptr);
            VERIFY(g.propagate());
        }
    }

    // i /~ j, b ~ a[i->v], b[j] occurs -> a[j] = b[j] 
    void array_plugin::force_store_axiom2_down(euf::egraph& g, euf::enode* sto, euf::enode* sel) {
        SASSERT(a.is_store(sto->get_expr()));
        SASSERT(a.is_select(sel->get_expr()));
        if (sel->get_arg(0)->get_root() != sto->get_root())
            return;
        if (eq_args(sto, sel))
            return; 
        auto nsel = mk_select(g, sto->get_arg(0), sel);
        if (are_distinct(nsel, sel))
            add_store_axiom2(sto->get_app(), sel->get_app());
        else {
            g.merge(nsel, sel, nullptr);
            VERIFY(g.propagate());
        }
    }

    // a ~ b, i /~ j, b[j] occurs -> a[i -> v][j] = b[j] 
    void array_plugin::force_store_axiom2_up(euf::egraph& g, euf::enode* sto, euf::enode* sel) {
        SASSERT(a.is_store(sto->get_expr()));
        SASSERT(a.is_select(sel->get_expr()));
        if (sel->get_arg(0)->get_root() != sto->get_arg(0)->get_root())
            return;
        if (eq_args(sto, sel))
            return;
        auto nsel = mk_select(g, sto, sel);
        if (are_distinct(nsel, sel))
            add_store_axiom2(sto->get_app(), sel->get_app());
        else {
            g.merge(nsel, sel, nullptr);
            VERIFY(g.propagate());
        }
    }

    bool array_plugin::are_distinct(euf::enode* a, euf::enode* b) {
        a = a->get_root();
        b = b->get_root();
        return a->interpreted() && b->interpreted() && a != b; // TODO work with nested arrays?
    }    

    bool array_plugin::eq_args(euf::enode* sto, euf::enode* sel) {
        SASSERT(a.is_store(sto->get_expr()));
        SASSERT(a.is_select(sel->get_expr()));
        unsigned arity = get_array_arity(sto->get_sort());
        for (unsigned i = 1; i < arity; ++i) {
            if (sto->get_arg(i)->get_root() != sel->get_arg(i)->get_root())
                return false;
        }
        return true;
    }

    void array_plugin::add_store_axiom1(app* sto) {
        if (!m_add_conflicts)
            return;
        ptr_vector<expr> args;
        args.push_back(sto);
        for (unsigned i = 1; i < sto->get_num_args() - 1; ++i)
            args.push_back(sto->get_arg(i));
        expr_ref sel(a.mk_select(args), m);
        expr_ref eq(m.mk_eq(sel, to_app(sto)->get_arg(sto->get_num_args() - 1)), m);
        verbose_stream() << "add store axiom 1 " << mk_bounded_pp(sto, m) << "\n";
        ctx.add_clause(eq);
    }
    
    void array_plugin::add_store_axiom2(app* sto, app* sel) {
        if (!m_add_conflicts)
            return;
        ptr_vector<expr> args1, args2;
        args1.push_back(sto);
        args2.push_back(sto->get_arg(0));
        for (unsigned i = 1; i < sel->get_num_args() - 1; ++i) {
            args1.push_back(sel->get_arg(i));
            args2.push_back(sel->get_arg(i));
        }
        expr_ref sel1(a.mk_select(args1), m);
        expr_ref sel2(a.mk_select(args2), m);
        expr_ref eq(m.mk_eq(sel1, sel2), m);
        expr_ref_vector ors(m);
        ors.push_back(eq);
        for (unsigned i = 1; i < sel->get_num_args() - 1; ++i) 
            ors.push_back(m.mk_eq(sel->get_arg(i), sto->get_arg(i)));     
        verbose_stream() << "add store axiom 2 " << mk_bounded_pp(sto, m) << " " << mk_bounded_pp(sel, m) << "\n";
        ctx.add_clause(m.mk_or(ors));
    }

    void array_plugin::init_egraph(euf::egraph& g) {
        ptr_vector<euf::enode> args;
        for (auto t : ctx.subterms()) {
            args.reset();
            if (is_app(t)) 
                for (auto* arg : *to_app(t)) 
                    args.push_back(g.find(arg));
                            
            euf::enode* n1, * n2;
            n1 = g.find(t);
            n1 = n1 ? n1 : g.mk(t, 0, args.size(), args.data());
            if (a.is_array(t))
                continue;
            auto v = ctx.get_value(t);
            verbose_stream() << "init " << mk_bounded_pp(t, m) << " := " << mk_bounded_pp(v, m) << "\n";
            n2 = g.find(v);
            n2 = n2 ? n2: g.mk(v, 0, 0, nullptr);
            g.merge(n1, n2, nullptr);
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
        
    }

    void array_plugin::init_kv(euf::egraph& g, kv& kv) {
        for (auto n : g.nodes()) {
            if (!n->is_root() || !a.is_array(n->get_expr()))
                continue;
            kv.insert(n, select2value());
            for (auto p : euf::enode_parents(n)) {
                if (!a.is_select(p->get_expr()))
                    continue;
                if (p->get_arg(0)->get_root() != n->get_root())
                    continue;
                auto val = p->get_root();
                kv[n].insert(select_args(p), val);
            }
        }
        display(verbose_stream());
    }

    expr_ref array_plugin::get_value(expr* e)  { 
        SASSERT(a.is_array(e));
        if (!m_g) {
            m_g = alloc(euf::egraph, m);
            init_egraph(*m_g);
            flet<bool> _strong(m_add_conflicts, false);
            saturate_store(*m_g);
        }
        if (!m_kv) {
            m_kv = alloc(kv);
            init_kv(*m_g, *m_kv);
        }
        auto& kv = *m_kv;
        auto n = m_g->find(e)->get_root();
        expr_ref r(n->get_expr(), m);
        for (auto [k, v] : kv[n]) {
            ptr_vector<expr> args;
            args.push_back(r);
            args.push_back(k.sel->get_arg(1)->get_expr());
            args.push_back(v->get_expr());
            r = a.mk_store(args);
        }
        return r;
    }

    std::ostream& array_plugin::display(std::ostream& out) const {
        if (m_g)
            m_g->display(out);
        if (m_kv) {
            for (auto& [n, kvs] : *m_kv) {
                out << m_g->pp(n) << " -> {";
                char const* sp = "";
                for (auto& [k, v] : kvs) {
                    out << sp;
                    for (unsigned i = 1; i < k.sel->num_args(); ++i)
                        out << m_g->pp(k.sel->get_arg(i)->get_root()) << " ";
                    out << "-> " << m_g->pp(v);
                    sp = " ";
                }
                out << "}\n";
            }
        }
        return out;
    }
}
