/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_cc.cpp

Abstract:

    Congruence Closure for SLS
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-06-24
    
--*/

#include "ast/sls/sls_cc.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"


namespace sls {
    
    cc_plugin::cc_plugin(context& c): 
        plugin(c), 
        m_values(8U, value_hash(*this), value_eq(*this)) {
        m_fid = m.mk_family_id("cc");
    }
    
    cc_plugin::~cc_plugin() {}
    
    expr_ref cc_plugin::get_value(expr* e) {
        UNREACHABLE();
        return expr_ref(m);
    }

    void cc_plugin::register_term(expr* e) {
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

    unsigned cc_plugin::value_hash::operator()(app* t) const {
        unsigned r = 0;
        for (auto arg : *t)
            r *= 3, r += cc.ctx.get_value(arg)->hash();
        return r;
    }

    bool cc_plugin::value_eq::operator()(app* a, app* b) const {
        SASSERT(a->get_num_args() == b->get_num_args());
        for (unsigned i = a->get_num_args(); i-- > 0; )
            if (cc.ctx.get_value(a->get_arg(i)) != cc.ctx.get_value(b->get_arg(i)))
                return false;
        return true;
    }

    bool cc_plugin::is_sat() {
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
        return true;
    }

    bool cc_plugin::propagate() {        
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
                    ctx.add_constraint(m.mk_or(ors));
                    new_constraint = true;
                }
                else
                    m_values.insert(t);
            }
        }
        return new_constraint;
    }

    std::ostream& cc_plugin::display(std::ostream& out) const {
        for (auto& [f, ts] : m_app) {
            for (auto* t : ts)
                out << mk_bounded_pp(t, m) << "\n";
            out << "\n";
        }
        return out;
    }

    void cc_plugin::mk_model(model& mdl) {
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
}
