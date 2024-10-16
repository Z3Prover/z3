/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_euf_plugin.cpp

Abstract:

    Congruence Closure for SLS
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-06-24

Todo:

- try incremental CC with backtracking for changing assignments
- try determining plateau moves.
- try generally a model rotation move.
    
--*/

#include "ast/sls/sls_euf_plugin.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "params/sls_params.hpp"


namespace sls {
    
    euf_plugin::euf_plugin(context& c): 
        plugin(c), 
        m_values(8U, value_hash(*this), value_eq(*this)) {
        m_fid = user_sort_family_id;
    }
    
    euf_plugin::~euf_plugin() {}

    void euf_plugin::initialize() {
        sls_params sp(ctx.get_params());
        m_incremental_mode = sp.euf_incremental();
        m_incremental = 1 == m_incremental_mode;
        IF_VERBOSE(2, verbose_stream() << "sls.euf: incremental " << m_incremental_mode << "\n");
    }

    void euf_plugin::start_propagation() {
        if (m_incremental_mode == 2)
            m_incremental = !m_incremental;
        m_g = alloc(euf::egraph, m);
        std::function<void(std::ostream&, void*)> dj = [&](std::ostream& out, void* j) {
            out << "lit " << to_literal(reinterpret_cast<size_t*>(j));
        };
        m_g->set_display_justification(dj);
        init_egraph(*m_g, !m_incremental);
    }
    
    void euf_plugin::register_term(expr* e) {
        if (!is_app(e))
            return;
        if (!is_uninterp(e))
            return;
        app* a = to_app(e);
        if (a->get_num_args() == 0)
            return;
        auto f = a->get_decl();
        if (!m_app.contains(f))
            m_app.insert(f, ptr_vector<app>());
        m_app[f].push_back(a);
    }

    unsigned euf_plugin::value_hash::operator()(app* t) const {
        unsigned r = 0;
        for (auto arg : *t)
            r *= 3, r += cc.ctx.get_value(arg)->hash();
        return r;
    }

    bool euf_plugin::value_eq::operator()(app* a, app* b) const {
        SASSERT(a->get_num_args() == b->get_num_args());
        for (unsigned i = a->get_num_args(); i-- > 0; )
            if (cc.ctx.get_value(a->get_arg(i)) != cc.ctx.get_value(b->get_arg(i)))
                return false;
        return true;
    }

    void euf_plugin::propagate_literal_incremental(sat::literal lit) {
        m_replay_stack.push_back(lit);
        replay();
    }
    void euf_plugin::resolve() {
        auto& g = *m_g;
        if (!g.inconsistent())
            return;

        ++m_stats.m_num_conflicts;
        unsigned n = 0;
        sat::literal_vector lits;
        sat::literal flit = sat::null_literal, slit;
        ptr_vector<size_t> explain;
        g.begin_explain();
        g.explain<size_t>(explain, nullptr);
        g.end_explain();
        double reward = -1;
        bool has_flipped = false;
        TRACE("enf",
            for (auto p : explain) {
                sat::literal l = to_literal(p);
                tout << l << " " << mk_pp(ctx.atom(l.var()), m) << " " << ctx.is_unit(l) << "\n";
            });
        for (auto p : explain) {
            sat::literal l = to_literal(p);
            CTRACE("euf", !ctx.is_true(l), tout << "not true " << l << "\n"; ctx.display(tout););            
            SASSERT(ctx.is_true(l));

            if (ctx.is_unit(l))
                continue;
            if (!lits.contains(~l))
                lits.push_back(~l);


            if (ctx.reward(l.var()) > reward)
                n = 0, reward = ctx.reward(l.var());

            if (ctx.rand(++n) == 0)
                flit = l;
        }

        if (flit == sat::null_literal)
            return;
        do {
            slit = m_stack.back();
            g.pop(1);
            m_replay_stack.push_back(slit);
            m_stack.pop_back();
        }
        while (slit != flit);
        // flip the last literal on the replay stack
        IF_VERBOSE(10, verbose_stream() << "sls.euf - flip " << flit << "\n");
        ctx.add_clause(lits);
        ctx.flip(flit.var());        
        m_replay_stack.back().neg();

    }

    void euf_plugin::replay() {
        while (!m_replay_stack.empty()) {
            auto l = m_replay_stack.back();
            m_replay_stack.pop_back();
            propagate_literal_incremental_step(l);
            if (m_g->inconsistent())
                resolve();
        }
    }


    void euf_plugin::propagate_literal_incremental_step(sat::literal lit) {
        SASSERT(ctx.is_true(lit));
        auto e = ctx.atom(lit.var());
        expr* x, * y;
        auto& g = *m_g;

        if (!e)
            return;

        TRACE("euf", tout << "propagate " << lit << "\n");
        m_stack.push_back(lit);
        g.push();
        if (m.is_eq(e, x, y)) {
            if (lit.sign())
                g.new_diseq(g.find(e), to_ptr(lit));
            else
                g.merge(g.find(x), g.find(y), to_ptr(lit));
            g.merge(g.find(e), g.find(m.mk_bool_val(!lit.sign())), to_ptr(lit));
        }
        else if (!lit.sign() && m.is_distinct(e)) {
            auto n = to_app(e)->get_num_args();
            for (unsigned i = 0; i < n; ++i) {
                expr* a = to_app(e)->get_arg(i);
                for (unsigned j = i + 1; j < n; ++j) {
                    auto b = to_app(e)->get_arg(j);
                    expr_ref eq(m.mk_eq(a, b), m);
                    auto c = g.find(eq);
                    if (!c) {
                        euf::enode* args[2] = { g.find(a), g.find(b) };
                        c = g.mk(eq, 0, 2, args);
                    }
                    g.new_diseq(c, to_ptr(lit));
                    g.merge(c, g.find(m.mk_false()), to_ptr(lit));
                }
            }
        }
//        else if (m.is_bool(e) && is_app(e) && to_app(e)->get_family_id() == basic_family_id)
//            ;
        else {
            auto a = g.find(e);
            auto b = g.find(m.mk_bool_val(!lit.sign()));
            g.merge(a, b, to_ptr(lit));
        }
        g.propagate();
    }

    void euf_plugin::propagate_literal(sat::literal lit) {
        if (m_incremental)
            propagate_literal_incremental(lit);
        else
            propagate_literal_non_incremental(lit);
    }

    void euf_plugin::propagate_literal_non_incremental(sat::literal lit) {
        SASSERT(ctx.is_true(lit));
        auto e = ctx.atom(lit.var());
        expr* x, * y;

        if (!e)
            return;

        auto block = [&](euf::enode* a, euf::enode* b) {
            TRACE("euf", tout << "block " << m_g->bpp(a) << " != " << m_g->bpp(b) << "\n");
            if (a->get_root() != b->get_root())
                return;
            ptr_vector<size_t> explain;
            m_g->explain_eq<size_t>(explain, nullptr, a, b);
            m_g->end_explain();
            unsigned n = 1;
            sat::literal_vector lits;            
            sat::literal flit = sat::null_literal;
            if (!ctx.is_unit(lit)) {
                flit = lit;
                lits.push_back(~lit);
            }
            for (auto p : explain) {
                sat::literal l = to_literal(p);
                if (!ctx.is_true(l))
                    return;
                if (ctx.is_unit(l)) 
                    continue;      
                lits.push_back(~l);
                if (ctx.rand(++n) == 0)
                    flit = l;
            }
            ctx.add_clause(lits);
            ++m_stats.m_num_conflicts;
            if (flit != sat::null_literal)
                ctx.flip(flit.var());
        };   

        if (lit.sign() && m.is_eq(e, x, y))
            block(m_g->find(x), m_g->find(y));   
        else if (!lit.sign() && m.is_distinct(e)) {
            auto n = to_app(e)->get_num_args();
            for (unsigned i = 0; i < n; ++i) {
                auto a = m_g->find(to_app(e)->get_arg(i));
                for (unsigned j = i + 1; j < n; ++j) {
                    auto b = m_g->find(to_app(e)->get_arg(j));
                    block(a, b);
                }
            }
        }
        else if (lit.sign()) {
            auto a = m_g->find(e);
            auto b = m_g->find(m.mk_true());
            block(a, b);          
        }
    }

    void euf_plugin::init_egraph(euf::egraph& g, bool merge_eqs) {
        ptr_vector<euf::enode> args;
        m_stack.reset();
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

        // merge all equalities
        // check for conflict with disequalities during propagation
        if (merge_eqs) {
            TRACE("euf", tout << "root literals " << ctx.root_literals() << "\n");
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
        }

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

    expr_ref euf_plugin::get_value(expr* e) {
        if (m.is_model_value(e))
            return expr_ref(e, m);

        if (!m_g) {
            m_g = alloc(euf::egraph, m);
            init_egraph(*m_g, true);
        }
        auto n = m_g->find(e)->get_root();
        VERIFY(m_root2value->find(n, e));
        return expr_ref(e, m);
    }


    bool euf_plugin::is_sat() {
        for (auto& [f, ts] : m_app) {
            if (ts.size() <= 1)
                continue;
            m_values.reset();
            for (auto* t : ts) {
                app* u;
                if (!ctx.is_relevant(t))
                    continue;
                if (m_values.find(t, u)) {
                    if (ctx.get_value(t) != ctx.get_value(u))
                        return false;
                }
                else
                    m_values.insert(t);
            }
        }
        // validate_model();
        return true;
    }

    void euf_plugin::validate_model() {
        auto& g = *m_g;
        for (auto lit : ctx.root_literals()) {
                euf::enode* a, * b;
                if (!ctx.is_true(lit))
                    continue;
                auto e = ctx.atom(lit.var());
                if (!e)
                    continue;
                if (!ctx.is_relevant(e))
                    continue;
                if (m.is_distinct(e))
                    continue;

                if (m.is_eq(e)) {
                    a = g.find(to_app(e)->get_arg(0));
                    b = g.find(to_app(e)->get_arg(1));
                }
                if (lit.sign() && m.is_eq(e)) {
                    if (a->get_root() == b->get_root()) {
                        IF_VERBOSE(0, verbose_stream() << "not disequal " << lit << " " << mk_pp(e, m) << "\n");
                        ctx.display(verbose_stream());
                        UNREACHABLE();
                    }
                }
                else if (!lit.sign() && m.is_eq(e)) {
                    if (a->get_root() != b->get_root()) {
                        IF_VERBOSE(0, verbose_stream() << "not equal " << lit << " " << mk_pp(e, m) << "\n");
                        //UNREACHABLE();
                    }
                }
                else if (to_app(e)->get_family_id() != basic_family_id && lit.sign() && g.find(e)->get_root() != g.find(m.mk_false())->get_root()) {
                    IF_VERBOSE(0, verbose_stream() << "not alse " << lit << " " << mk_pp(e, m) << "\n");
                    //UNREACHABLE();
                }
                else if (to_app(e)->get_family_id() != basic_family_id && !lit.sign() && g.find(e)->get_root() != g.find(m.mk_true())->get_root()) {
                    IF_VERBOSE(0, verbose_stream() << "not true " << lit << " " << mk_pp(e, m) << "\n");
                    //UNREACHABLE();
                }
            
        }
    }

    bool euf_plugin::propagate() {  
        bool new_constraint = false;
        for (auto & [f, ts] : m_app) {
            if (ts.size() <= 1)
                continue;
            m_values.reset();
            for (auto * t : ts) {
                app* u;
                if (!ctx.is_relevant(t))
                    continue;
                if (m_values.find(t, u)) {
                    if (ctx.get_value(t) == ctx.get_value(u))
                        continue;
                    expr_ref_vector ors(m);
                    for (unsigned i = t->get_num_args(); i-- > 0; )
                        ors.push_back(m.mk_not(m.mk_eq(t->get_arg(i), u->get_arg(i))));
                    ors.push_back(m.mk_eq(t, u));
#if 0
                    verbose_stream() << "conflict: " << mk_bounded_pp(t, m) << " != " << mk_bounded_pp(u, m) << "\n";
                    verbose_stream() << "value " << ctx.get_value(t) << " != " << ctx.get_value(u) << "\n";
                    for (unsigned i = t->get_num_args(); i-- > 0; )
                        verbose_stream() << ctx.get_value(t->get_arg(i)) << " == " << ctx.get_value(u->get_arg(i)) << "\n";
#endif
                    ctx.add_constraint(m.mk_or(ors));
                    new_constraint = true;
                }
                else
                    m_values.insert(t);
           }
        }

        for (auto lit : ctx.root_literals()) {
            if (!ctx.is_true(lit))
                lit.neg();
            auto e = ctx.atom(lit.var());
            if (lit.sign() && e && m.is_distinct(e)) {
                auto n = to_app(e)->get_num_args();
                expr_ref_vector eqs(m);
                for (unsigned i = 0; i < n; ++i) {
                    auto arg = to_app(e)->get_arg(i);
                    auto a = ctx.get_value(arg);
                    for (unsigned j = i + 1; j < n; ++j) {
                        auto argb = to_app(e)->get_arg(j);
                        auto b = ctx.get_value(argb);
                        if (a == b)
                            goto done_distinct;
                        eqs.push_back(m.mk_eq(arg, argb));
                    }
                }
                // distinct(a, b, c) or a = b or a = c or b = c
                eqs.push_back(e);
                ctx.add_constraint(m.mk_or(eqs));
                new_constraint = true;
            done_distinct:
                ;
            }
        }
        
        return new_constraint;
    }

    std::ostream& euf_plugin::display(std::ostream& out) const {
        if (m_g)
            m_g->display(out);

        for (auto& [f, ts] : m_app) {
            for (auto* t : ts)
                out << mk_bounded_pp(t, m) << "\n";
            out << "\n";
        }
        return out;
    }

    void euf_plugin::mk_model(model& mdl) {
        expr_ref_vector args(m);
        for (auto& [f, ts] : m_app) {
            func_interp* fi = alloc(func_interp, m, f->get_arity());
            mdl.register_decl(f, fi);
            m_values.reset();
            for (auto* t : ts) {
                if (m_values.contains(t))
                    continue;
                args.reset();
                expr_ref val = ctx.get_value(t);
                for (auto arg : *t) 
                    args.push_back(ctx.get_value(arg));
                fi->insert_new_entry(args.data(), val);
                m_values.insert(t);
            }
        }
    }

    void euf_plugin::collect_statistics(statistics& st) const {
        st.update("sls-euf-conflict", m_stats.m_num_conflicts);
    }

    void euf_plugin::reset_statistics() {
        m_stats.reset();
    }
}
