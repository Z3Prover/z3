/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    smt_sls.cpp

Abstract:

    A Stochastic Local Search (SLS) Context.

Author:

    Nikolaj Bjorner (nbjorner) 2024-06-24
    
--*/
#pragma once

#include "ast/sls/sls_smt.h"
#include "ast/sls/sls_cc.h"
#include "ast/sls/sls_arith_plugin.h"

namespace sls {

    plugin::plugin(context& c): 
        ctx(c), 
        m(c.get_manager()) {
        reset();
    }

    context::context(ast_manager& m, sat_solver_context& s) : 
        m(m), s(s), m_atoms(m), m_allterms(m) {
        reset();
    }

    void context::register_plugin(plugin* p) {
        m_plugins.reserve(p->fid() + 1);
        m_plugins.set(p->fid(), p);
    }

    void context::register_atom(sat::bool_var v, expr* e) { 
        m_atoms.setx(v, e); 
        m_atom2bool_var.setx(e->get_id(), v, sat::null_bool_var);
    }
    
    void context::reset() {
        m_plugins.reset();
        m_atoms.reset();
        m_atom2bool_var.reset();
        m_initialized = false;
        m_parents.reset();
        m_relevant.reset();
        m_visited.reset();
        m_allterms.reset();
        register_plugin(alloc(cc_plugin, *this));
        register_plugin(alloc(arith_plugin, *this));
    }
    
    lbool context::check() {
        //
        // initialize data-structures if not done before.
        // identify minimal feasible assignment to literals.
        // sub-expressions within assignment are relevant. 
        // Use timestamps to make it incremental.
        // 
        init();
        while (unsat().empty()) {
            reinit_relevant();
            for (auto p : m_plugins) {
                lbool r;
                if (p && (r = p->check()) != l_true)
                    return r;
            }
            if (m_new_constraint)
                return l_undef;
            if (all_of(m_plugins, [&](auto* p) { return !p || p->is_sat(); })) {
                model_ref mdl = alloc(model, m);
                for (auto p : m_plugins)
                    if (p)
                        p->mk_model(*mdl);
                s.on_model(mdl);
                verbose_stream() << *mdl << "\n";
                return l_true;
            }
        }
        return l_undef;
    }

    bool context::is_true(expr* e) {
        SASSERT(m.is_bool(e));
        auto v = m_atom2bool_var.get(e->get_id(), sat::null_bool_var);
        SASSERT(v != sat::null_bool_var);
        return is_true(sat::literal(v, false));
    }

    bool context::is_fixed(expr* e) {
        // is this a Boolean literal that is a unit?
        return false;
    }

    expr_ref context::get_value(expr* e) {
        if (m.is_bool(e)) {
            auto v = m_atom2bool_var[e->get_id()];
            return expr_ref(is_true(sat::literal(v, false)) ? m.mk_true() : m.mk_false(), m);
        }
        sort* s = e->get_sort();
        auto fid = s->get_family_id();
        auto p = m_plugins.get(fid, nullptr);
        if (p) 
            return p->get_value(e);      
        UNREACHABLE();
        return expr_ref(e, m);
    }
    
    void context::set_value(expr* e, expr* v) {
        for (auto p : m_plugins)
            if (p)
                p->set_value(e, v);       
    }
    
    bool context::is_relevant(expr* e) {
        unsigned id = e->get_id();
        if (m_relevant.contains(id))
            return true;
        if (m_visited.contains(id))
            return false;
        m_visited.insert(id);
        for (auto p : m_parents[id]) {
            if (is_relevant(p)) {
                m_relevant.insert(id);
                return true;
            }
        }
        return false;
    }

    void context::add_constraint(expr* e) {
        expr_ref _e(e, m);
        sat::literal_vector lits;
        auto add_literal = [&](expr* e) {
            bool is_neg = m.is_not(e, e);
            auto v = mk_atom(e);
            lits.push_back(sat::literal(v, is_neg));
        };
        if (m.is_or(e))
            for (auto arg : *to_app(e))
                add_literal(arg);
        else
            add_literal(e);
        TRACE("sls", tout << "new clause " << lits << "\n");
        s.add_clause(lits.size(), lits.data());  
        m_new_constraint = true;
    }

    sat::bool_var context::mk_atom(expr* e) {
        auto v = m_atom2bool_var.get(e->get_id(), sat::null_bool_var);
        if (v == sat::null_bool_var) {
            v = s.add_var();
            register_terms(e);
            register_atom(v, e);
            init_bool_var(v);
        }
        return v;
    }

    void context::init_bool_var(sat::bool_var v) {
        for (auto p : m_plugins)
            if (p)
                p->init_bool_var(v);
    }

    void context::init() {
        m_new_constraint = false;
        if (m_initialized)
            return;
        m_initialized = true;
        register_terms();
        for (sat::bool_var v = 0; v < num_bool_vars(); ++v)
            init_bool_var(v);
    }
  
    void context::register_terms() {
        for (auto a : m_atoms)
            if (a)
                register_terms(a);
    }

    void context::register_terms(expr* e) {
        auto is_visited = [&](expr* e) {
            return nullptr != m_allterms.get(e->get_id(), nullptr);
        };
        auto visit = [&](expr* e) {
            m_allterms.setx(e->get_id(), e);
        };
        if (is_visited(e))
            return;
        m_subterms.reset();
        m_todo.push_back(e);
        while (!m_todo.empty()) {
            expr* e = m_todo.back();
            if (is_visited(e)) 
                m_todo.pop_back();            
            else if (is_app(e)) {
                if (all_of(*to_app(e), [&](expr* arg) { return is_visited(arg); })) {
                    for (expr* arg : *to_app(e)) {
                        m_parents.reserve(arg->get_id() + 1);
                        m_parents[arg->get_id()].push_back(e);
                    }
                    register_term(e);
                    visit(e);
                    m_todo.pop_back();
                }
                else {
                    for (expr* arg : *to_app(e)) 
                        m_todo.push_back(arg);                    
                }
            }
            else {
                register_term(e);
                visit(e);
                m_todo.pop_back();
            }
        }
    }

    void context::register_term(expr* e) {
        for (auto p : m_plugins)
            if (p)
                p->register_term(e);
    }

    ptr_vector<expr> const& context::subterms() {
        if (!m_subterms.empty())
            return m_subterms;
        for (auto e : m_allterms)
            if (e)
                m_subterms.push_back(e);
        std::stable_sort(m_subterms.begin(), m_subterms.end(), 
            [](expr* a, expr* b) { return a->get_id() < b->get_id(); });
        return m_subterms;
    }

    void context::reinit_relevant() {
        m_relevant.reset();
        m_visited.reset();
        m_root_literals.reset();
        for (auto const& clause : s.clauses()) {
            bool has_relevant = false;
            unsigned n = 0;
            sat::literal selected_lit = sat::null_literal;
            for (auto lit : clause) {
                auto atm = m_atoms.get(lit.var(), nullptr);
                if (!atm)
                    continue;
                auto a = atm->get_id();
                if (!is_true(lit))
                    continue;
                if (m_relevant.contains(a)) {
                    has_relevant = true;
                    break;
                }
                if (m_rand() % ++n == 0)
                    selected_lit = lit;
            }               
            if (!has_relevant && selected_lit != sat::null_literal) {
                m_relevant.insert(m_atoms[selected_lit.var()]->get_id());
                m_root_literals.push_back(selected_lit);
            }
        }
        shuffle(m_root_literals.size(), m_root_literals.data(), m_rand);
    }

    std::ostream& context::display(std::ostream& out) const {
        for (auto p : m_plugins) {
            if (p)
                p->display(out);
        }
        return out;
    }
}
