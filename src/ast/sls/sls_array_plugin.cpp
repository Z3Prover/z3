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
        euf(ctx.euf()),
        a(m)
    {
        m_fid = a.get_family_id();
    }

    bool array_plugin::is_sat() {
        if (!m_has_arrays)
            return true;
        m_kv = nullptr;
        m_g = alloc(euf::egraph, m);
        init_egraph(*m_g);
        saturate(*m_g);
        if (m_g->inconsistent()) {
            resolve_conflict();
            return false;
        }        
        if (saturate_extensionality(*m_g))
            return false;
        return !m_g->inconsistent();
    }


    void array_plugin::resolve_conflict() {
        ++m_stats.m_num_conflicts;
        auto& g = *m_g;
        SASSERT(g.inconsistent());
        ptr_vector<size_t> explain;
        g.begin_explain();
        g.explain<size_t>(explain, nullptr);
        g.end_explain();

        IF_VERBOSE(3, verbose_stream() << "array conflict\n");
        bool has_missing_axiom = false;
        for (auto p : explain) {
            if (is_index(p)) {
                has_missing_axiom = true;
                unsigned idx = to_index(p);
                auto [t, sto, sel] = m_delayed_axioms[idx];
                switch (t) {
                case store_axiom1:
                    add_store_axiom1(sto->get_app());
                    break;
                case store_axiom2_down:
                case store_axiom2_up:
                    add_store_axiom2(sto->get_app(), sel->get_app());
                    break;
                case map_axiom:            
                case const_axiom:
                    add_eq_axiom(sto, sel);
                    break;
                default:
                    UNREACHABLE();
                    break;
                }
            }
        }
        if (has_missing_axiom)
            return;

        sat::literal_vector lits;
        for (auto p : explain) {
            if (is_enode(p)) {
                auto n = to_enode(p);
                auto v = ctx.get_value(n->get_expr());
                lits.push_back(~ctx.mk_literal(m.mk_eq(n->get_expr(), v)));
                if (a.is_store(n->get_expr()))
                    add_store_axiom1(n->get_app());
            }
            else if (is_literal(p)) {
                sat::literal l = to_literal(p);
                lits.push_back(~l);
            }          
        }
        IF_VERBOSE(3, verbose_stream() << "add conflict clause\n");
        ctx.add_clause(lits);
    }

    // b ~ a[i -> v]
    // ensure b[i] ~ v
    // ensure b[j] ~ a[j] for j != i

    void array_plugin::saturate(euf::egraph& g) {
        unsigned sz = 0;
        while (sz < g.nodes().size() && !g.inconsistent()) {
            sz = g.nodes().size();
            for (unsigned i = 0; i < sz && !g.inconsistent(); ++i) {
                auto n = g.nodes()[i];
                if (a.is_store(n->get_expr()))
                    saturate_store(g, n);
                else if (a.is_const(n->get_expr()))
                    saturate_const(g, n);
                else if (a.is_map(n->get_expr()))
                    saturate_map(g, n);
                
            }
        }
        IF_VERBOSE(10, display(verbose_stream() << "saturated\n"));
    }

    bool array_plugin::saturate_extensionality(euf::egraph& g) {
        bool new_axiom = false;
        for (auto lit : ctx.root_literals()) {
            if (!lit.sign() || !ctx.is_true(lit))
                continue;
            auto e = ctx.atom(lit.var());
            expr* x, *y;
            if (m.is_eq(e, x, y) && a.is_array(x) && add_extensionality_axiom(x, y))
                new_axiom = true;            
        }

        euf::enode_vector shared;
        collect_shared(g, shared);
        for (unsigned i = shared.size(); i-- > 0; ) {
            auto x = shared[i];
            auto e1 = x->get_expr();
            for (unsigned j = i; j-- > 0; ) {
                auto y = shared[j];
                auto e2 = y->get_expr();
                if (e1->get_sort() != e2->get_sort())
                    continue;
                if (add_extensionality_axiom(e1, e2))
                    new_axiom = true;
            }
        }
        return new_axiom;
    }

    void array_plugin::collect_shared(euf::egraph& g, euf::enode_vector& shared) {
        ptr_buffer<euf::enode> to_unmark;
        for (auto n : g.nodes()) {
            expr* e = n->get_expr();
            if (!a.is_array(e))
                continue;
            if (!ctx.is_relevant(e))
                continue;
            euf::enode * r = n->get_root();
            if (r->is_marked1()) 
                continue;            
            if (is_shared_arg(r))
                shared.push_back(r);
            r->mark1();            
        }
        for (auto* r : to_unmark)
            r->unmark1();
    }

    bool array_plugin::is_shared_arg(euf::enode* r) {
        SASSERT(r->is_root());
        for (euf::enode* n : euf::enode_parents(r)) {
            expr* e = n->get_expr();
            if (a.is_select(e) || a.is_store(e)) {
                for (unsigned i = 1; i < n->num_args(); ++i)
                    if (r == n->get_arg(i)->get_root())
                        return true;
                continue;
            }
            if (m.is_eq(e))
                continue;
            return true;
        }            
        return false;
    }

    void array_plugin::saturate_store(euf::egraph& g, euf::enode* n) {
        force_store_axiom1(g, n);
        for (auto p : euf::enode_parents(n->get_root()))
            if (a.is_select(p->get_expr()))
                force_store_axiom2_down(g, n, p);
        auto arr = n->get_arg(0);
        for (auto p : euf::enode_parents(arr->get_root()))
            if (a.is_select(p->get_expr()))
                force_store_axiom2_up(g, n, p);
    }

    void array_plugin::saturate_const(euf::egraph& g, euf::enode* n) {
        for (auto p : euf::enode_parents(n->get_root()))
            if (a.is_select(p->get_expr()))
                force_const_axiom(g, n, p);
    }

    void array_plugin::saturate_map(euf::egraph& g, euf::enode* n) {
        for (auto p : euf::enode_parents(n->get_root()))
            if (a.is_select(p->get_expr()))
                add_map_axiom(g, n, p);       
        for (auto arg : euf::enode_args(n)) {
            SASSERT(a.is_array(arg->get_expr()));
            for (auto p : euf::enode_parents(arg->get_root()))
                if (a.is_select(p->get_expr()))
                    add_map_axiom(g, n, p);
        }
    }

    void array_plugin::add_map_axiom(euf::egraph& g, euf::enode * n, euf::enode* sel) {
        if (g.inconsistent())
            return;
        func_decl* f = nullptr;
        SASSERT(a.is_map(n->get_expr()));
        VERIFY(a.is_map(n->get_decl(), f));
        expr_ref apply_map(m);
        expr_ref_vector args(m);
        euf::enode_vector eargs;
        for (auto arg : euf::enode_args(n)) {
            auto nsel = mk_select(g, arg, sel);
            eargs.push_back(nsel);
            args.push_back(nsel->get_expr());
        }
        expr_ref f_map(m.mk_app(f, args), m);
        ctx.add_new_term(f_map);
        auto nsel = mk_select(g, n, sel);
        auto nmap = g.find(f_map);
        if (!nmap) 
            nmap = g.mk(f_map, 0, eargs.size(), eargs.data()); 
        if (nmap->get_root() == nsel->get_root())
            return;
        if (!are_distinct(nsel, nmap)) {
            g.merge(nmap, nsel, to_ptr(map_axiom_index(nmap, nsel)));
            g.propagate();
            if (!g.inconsistent())
                return;
        }
        add_eq_axiom(nmap, nsel);
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
        ctx.add_new_term(esel);
        auto n = g.find(esel);
        return n ? n : g.mk(esel, 0, eargs.size(), eargs.data());
    }

    // ensure a[i->v][i] = v exists in the e-graph
    void array_plugin::force_store_axiom1(euf::egraph& g, euf::enode* n) {
        if (g.inconsistent())
            return;
        SASSERT(a.is_store(n->get_expr()));
        auto val = n->get_arg(n->num_args() - 1);
        auto nsel = mk_select(g, n, n);
        VERIFY(!g.inconsistent());
        if (!are_distinct(nsel, val)) {
            g.merge(nsel, val, to_ptr(store_axiom1_index(n)));
            g.propagate();
            if (!g.inconsistent())
                return;            
        }
        add_store_axiom1(n->get_app());
    }

    // i /~ j, b ~ a[i->v], b[j] occurs -> a[j] = b[j] 
    void array_plugin::force_store_axiom2_down(euf::egraph& g, euf::enode* sto, euf::enode* sel) {
        if (g.inconsistent())
            return;
        SASSERT(a.is_store(sto->get_expr()));
        SASSERT(a.is_select(sel->get_expr()));
        if (sel->get_arg(0)->get_root() != sto->get_root())
            return;
        if (eq_args(sto, sel))
            return; 
        auto nsel = mk_select(g, sto->get_arg(0), sel);
        if (!are_distinct(nsel, sel)) {
            g.merge(nsel, sel, to_ptr(store_axiom2_down_index(sto, sel)));
            g.propagate();
            if (!g.inconsistent())
                return;
        }
        add_store_axiom2(sto->get_app(), sel->get_app());
    }

    // a ~ b, i /~ j, b[j] occurs -> a[i -> v][j] = b[j] 
    void array_plugin::force_store_axiom2_up(euf::egraph& g, euf::enode* sto, euf::enode* sel) {
        if (g.inconsistent())
            return;
        SASSERT(a.is_store(sto->get_expr()));
        SASSERT(a.is_select(sel->get_expr()));
        if (sel->get_arg(0)->get_root() != sto->get_arg(0)->get_root())
            return;
        if (eq_args(sto, sel))
            return;
        auto nsel = mk_select(g, sto, sel);
        if (!are_distinct(nsel, sel)) {
            g.merge(nsel, sel, to_ptr(store_axiom2_up_index(sto, sel)));
            g.propagate();
            if (!g.inconsistent())
                return;
        }
        add_store_axiom2(sto->get_app(), sel->get_app());
    }

    // const(v) ~ b, b[j] occurs -> v = (const v)[j]
    void array_plugin::force_const_axiom(euf::egraph& g, euf::enode* cn, euf::enode* sel) {
        if (g.inconsistent())
            return;
        SASSERT(a.is_const(cn->get_expr()));
        SASSERT(a.is_select(sel->get_expr()));
        if (sel->get_arg(0)->get_root() != cn->get_root())
            return;
        auto val = cn->get_arg(0);
        auto nsel = mk_select(g, cn, sel);
        if (!are_distinct(nsel, sel)) {
            g.merge(nsel, sel, to_ptr(const_axiom_index(val, nsel)));
            g.propagate();
            if (!g.inconsistent())
                return;
        }
        ++m_stats.m_num_axioms;
        add_eq_axiom(val, nsel);
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
        IF_VERBOSE(3, verbose_stream() << "add store axiom 1 " << mk_bounded_pp(sto, m) << "\n");
        ++m_stats.m_num_axioms;
        ctx.add_theory_axiom(eq);
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
        IF_VERBOSE(3, verbose_stream() << "add store axiom 2 " << mk_bounded_pp(sto, m) << " " << mk_bounded_pp(sel, m) << "\n");
        ++m_stats.m_num_axioms;
        ctx.add_theory_axiom(m.mk_or(ors));
    }

    bool array_plugin::add_extensionality_axiom(expr* x, expr* y) {
        SASSERT(a.is_array(x));
        SASSERT(x->get_sort() == y->get_sort());
        auto s = x->get_sort();
        auto dimension = get_array_arity(s);
        func_decl_ref_vector funcs(m);
        for (unsigned i = 0; i < dimension; ++i) 
            funcs.push_back(a.mk_array_ext(s, i));

        expr_ref_vector args1(m), args2(m);
        args1.push_back(x);
        args2.push_back(y);
        for (func_decl* f : funcs) {
            expr_ref k(m.mk_app(f, x, y), m);
            args1.push_back(k);
            args2.push_back(k);
        }
        expr_ref sel1(a.mk_select(args1), m);
        expr_ref sel2(a.mk_select(args2), m);
        bool r = ctx.add_constraint(m.mk_implies(m.mk_eq(sel1, sel2), m.mk_eq(x, y)));
        if (r)
            ++m_stats.m_num_axioms;        
        return r;
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
            if (m.is_bool(t))
                continue;
            auto v = ctx.get_value(t);
            IF_VERBOSE(3, verbose_stream() << "init " << mk_bounded_pp(t, m) << " := " << mk_bounded_pp(v, m) << " " << g.inconsistent() << "\n");
            n2 = g.find(v);
            n2 = n2 ? n2: g.mk(v, 0, 0, nullptr);
            g.merge(n1, n2, to_ptr(n1));            
        }
        for (auto lit : ctx.root_literals()) {
            if (!ctx.is_true(lit) || lit.sign())
                continue;
            auto e = ctx.atom(lit.var());
            expr* x = nullptr, * y = nullptr;
            if (e && m.is_eq(e, x, y))
                g.merge(g.find(x), g.find(y), nullptr);

        }
        g.propagate();

        IF_VERBOSE(3, display(verbose_stream()));
        
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
#if 1
                bool is_relevant = any_of(euf::enode_class(p), [&](euf::enode* k) { return ctx.is_relevant(k->get_expr()); });
                if (!is_relevant)
                    continue;
#endif
                auto val = p->get_root();
                kv[n].insert(select_args(p), val);
            }
        }
    }

    expr_ref array_plugin::get_value(expr* e)  { 
        SASSERT(a.is_array(e));
        if (!m_g) {
            m_kv = nullptr;
            m_g = alloc(euf::egraph, m);
            init_egraph(*m_g);
            flet<bool> _strong(m_add_conflicts, false);
            saturate(*m_g);
        }
        if (!m_kv) {
            m_kv = alloc(kv);
            init_kv(*m_g, *m_kv);
        }
        // TODO: adapt to handle "const" arrays and multi-dimensional arrays.
        auto& kv = *m_kv;
        auto n = m_g->find(e)->get_root();
        expr_ref r(n->get_expr(), m), key(m);
        expr_mark visited;  
        SASSERT(kv.contains(n));
        for (auto [k, v] : kv[n]) {
            ptr_vector<expr> args;
            key = ctx.get_value(k.sel->get_arg(1)->get_expr());
            if (visited.is_marked(key))
                continue;
            visited.mark(key);
            args.push_back(r);
            args.push_back(key);
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

    void array_plugin::collect_statistics(statistics& st) const {
        st.update("sls-array-conflicts", m_stats.m_num_conflicts);
        st.update("sls-array-axioms", m_stats.m_num_axioms);
    }
}
