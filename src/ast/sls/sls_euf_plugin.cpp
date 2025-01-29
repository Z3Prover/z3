/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_euf_plugin.cpp

Abstract:

    Congruence Closure for SLS
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-06-24

Todo:

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
    }

    void euf_plugin::start_propagation() {

        m_g = alloc(euf::egraph, m);
        std::function<void(std::ostream&, void*)> dj = [&](std::ostream& out, void* j) {
            out << "lit " << to_literal(reinterpret_cast<size_t*>(j));
        };
        m_g->set_display_justification(dj);
        init_egraph(*m_g, true);
    }
    
    void euf_plugin::register_term(expr* e) {
        if (!is_app(e))
            return;
        app* a = to_app(e);
        if (!ctx.check_ackerman(a)) 
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

    sat::literal euf_plugin::resolve_conflict() {
        auto& g = *m_g;
        SASSERT(g.inconsistent());
        ++m_stats.m_num_conflicts;
        unsigned n = 0;
        sat::literal_vector lits;
        sat::literal flit = sat::null_literal;
        ptr_vector<size_t> explain;
        g.begin_explain();
        g.explain<size_t>(explain, nullptr);
        g.end_explain();
        double reward = -1;
        TRACE("euf",
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
        // flip the last literal on the replay stack
        IF_VERBOSE(10, verbose_stream() << "sls.euf - flip " << flit << "\n");
        log_clause(lits);
        ctx.add_clause(lits);
        return flit;
    }

    void euf_plugin::log_clause(sat::literal_vector const& lits) {
        IF_VERBOSE(3, verbose_stream() << "block " << lits << "\n";
        for (auto lit : lits)
            verbose_stream() << (lit.sign() ? "~" : "") << mk_bounded_pp(ctx.atom(lit.var()), m) << "\n";
        verbose_stream() << "\n";
            );
    }

    void euf_plugin::propagate_literal(sat::literal lit) {
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
            log_clause(lits);
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

            if (g.inconsistent()) 
                resolve_conflict();
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

    bool euf_plugin::include_func_interp(func_decl* f) const {
        return is_uninterp(f) && f->get_arity() > 0;
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
                euf::enode* a = nullptr, * b = nullptr;
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
                    expr_ref fml(m.mk_or(ors), m);
                    if (ctx.add_constraint(fml))
                        new_constraint = true;
                    
                }
                else
                    m_values.insert(t);
           }
        }

        for (auto lit : ctx.root_literals()) {
            if (!ctx.is_true(lit))
                continue;
            auto e = ctx.atom(lit.var());
            if (lit.sign() && e && m.is_distinct(e)) {
                auto n = to_app(e)->get_num_args();
                expr_ref_vector eqs(m);
                for (unsigned i = 0; i < n; ++i) {
                    auto a = m_g->find(to_app(e)->get_arg(i));
                    for (unsigned j = i + 1; j < n; ++j) {
                        auto b = m_g->find(to_app(e)->get_arg(j));
                        if (a->get_root() == b->get_root())
                            goto done_distinct;
                        eqs.push_back(m.mk_eq(a->get_expr(), b->get_expr()));
                    }
                }
                // distinct(a, b, c) or a = b or a = c or b = c
                eqs.push_back(e);
                if (ctx.add_constraint(m.mk_or(eqs)))
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

    void euf_plugin::collect_statistics(statistics& st) const {
        st.update("sls-euf-conflict", m_stats.m_num_conflicts);
    }

    void euf_plugin::reset_statistics() {
        m_stats.reset();
    }
}
