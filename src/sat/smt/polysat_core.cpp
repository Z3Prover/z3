/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    polysat_core.cpp

Abstract:

    PolySAT core functionality

Author:

    Nikolaj Bjorner (nbjorner) 2022-01-26
    Jakob Rath 2021-04-06

Notes:

polysat::solver
- adds assignments
- calls propagation and check

polysat::core
- propagates literals 
- crates case splits by value assignment (equalities)
- detects conflicts based on Literal assignmets
- adds lemmas based on projections

--*/

#include "params/bv_rewriter_params.hpp"
#include "sat/smt/polysat_solver.h"
#include "sat/smt/euf_solver.h"

namespace polysat {

    class core::mk_assign_var : public trail {
        pvar m_var;
        core& c;
    public:
        mk_assign_var(pvar v, core& c) : m_var(v), c(c) {}
        void undo() {
            c.m_justification[m_var] = nullptr;
            c.m_assignment.pop();
        }
    };

    class core::mk_dqueue_var : public trail {
        pvar m_var;
        core& c;
    public:
        mk_dqueue_var(pvar v, core& c) : m_var(v), c(c) {}
        void undo() {
            c.m_var_queue.unassign_var_eh(m_var);
        }
    };

    class core::mk_add_var : public trail {
        core& c;
    public:
        mk_add_var(core& c) : c(c) {}
        void undo() override {
            c.del_var();
        }
    };

    class core::mk_add_watch : public trail {
        core& c;
        unsigned m_idx;
    public:
        mk_add_watch(core& c, unsigned idx) : c(c), m_idx(idx) {}
        void undo() override {
            auto& sc = c.m_prop_queue[m_idx].first;
            auto& vars = sc.vars();
            if (vars.size() > 0)
                c.m_watch[vars[0]].pop_back();
            if (vars.size() > 1)
                c.m_watch[vars[1]].pop_back();
        }
    };

    core::core(solver& s) :
        s(s),         
        m_viable(*this),
        m_constraints(s.get_trail_stack()),
        m_assignment(*this),
        m_dep(s.get_region()),
        m_var_queue(m_activity)
    {}

    pdd core::value(rational const& v, unsigned sz) {
        return sz2pdd(sz).mk_val(v);
    }

    dd::pdd_manager& core::sz2pdd(unsigned sz) const {
        m_pdd.reserve(sz + 1);
        if (!m_pdd[sz])
            m_pdd.set(sz, alloc(dd::pdd_manager, 1000, dd::pdd_manager::semantics::mod2N_e, sz));
        return *m_pdd[sz];
    }

    dd::pdd_manager& core::var2pdd(pvar v) const {
        return sz2pdd(size(v));
    }

    pvar core::add_var(unsigned sz) { 
        unsigned v = m_vars.size();
        m_vars.push_back(sz2pdd(sz).mk_var(v));
        m_activity.push_back({ sz, 0 });
        m_justification.push_back(nullptr);
        m_watch.push_back({});
        m_var_queue.mk_var_eh(v);
        s.ctx.push(mk_add_var(*this));
        return v;
    }

    void core::del_var() {
        unsigned v = m_vars.size() - 1;
        m_vars.pop_back();
        m_activity.pop_back();
        m_justification.pop_back();
        m_watch.pop_back();
        m_var_queue.del_var_eh(v);
    }

    // case split on unassigned variables until all are assigned values.
    // create equality literal for unassigned variable.
    // return new_eq if there is a new literal.
    
    sat::check_result core::check() { 
        if (m_var_queue.empty())
            return sat::check_result::CR_DONE;
        m_var = m_var_queue.next_var();       
        s.ctx.push(mk_dqueue_var(m_var, *this));
        switch (m_viable.find_viable(m_var, m_value)) {
        case find_t::empty:
            m_unsat_core = m_viable.explain();
            propagate_unsat_core();
            return sat::check_result::CR_CONTINUE;
        case find_t::singleton:
            s.propagate(m_constraints.eq(var2pdd(m_var), m_value), m_viable.explain());
            return sat::check_result::CR_CONTINUE;
        case find_t::multiple:  
            return sat::check_result::CR_CONTINUE;
        case find_t::resource_out:
            return sat::check_result::CR_GIVEUP;
        }
        UNREACHABLE();
        return sat::check_result::CR_GIVEUP;
    }

    // First propagate Boolean assignment, then propagate value assignment
    bool core::propagate() { 
        if (m_qhead == m_prop_queue.size() && m_vqhead == m_prop_queue.size())
            return false;
        s.ctx.push(value_trail(m_qhead));
        for (; m_qhead < m_prop_queue.size() && !s.ctx.inconsistent(); ++m_qhead)
            propagate_constraint(m_qhead, m_prop_queue[m_qhead]);        
        s.ctx.push(value_trail(m_vqhead));
        for (; m_vqhead < m_prop_queue.size() && !s.ctx.inconsistent(); ++m_vqhead) 
            propagate_value(m_vqhead, m_prop_queue[m_vqhead]);        
        return true;
    }

    void core::propagate_constraint(unsigned idx, dependent_constraint& dc) { 
        auto [sc, dep] = dc;
        if (sc.is_eq(m_var, m_value)) {
            propagate_assignment(m_var, m_value, dep);
            return;
        }
        add_watch(idx, sc);
    }

    void core::add_watch(unsigned idx, signed_constraint& sc) {        
        auto& vars = sc.vars();
        unsigned i = 0, j = 0, sz = vars.size();
        for (; i < sz && j < 2; ++i)
            if (!is_assigned(vars[i]))
                std::swap(vars[i], vars[j++]);
        if (vars.size() > 0)
            add_watch(idx, vars[0]);
        if (vars.size() > 1)
            add_watch(idx, vars[1]);
        s.ctx.push(mk_add_watch(*this, idx));
    }

    void core::add_watch(unsigned idx, unsigned var) {
        m_watch[var].push_back(idx);
    }

    void core::propagate_assignment(pvar v, rational const& value, stacked_dependency* dep) {
        if (is_assigned(v))
            return;
        if (m_var_queue.contains(v)) {
            m_var_queue.del_var_eh(v);
            s.ctx.push(mk_dqueue_var(v, *this));
        }
        m_values[v] = value;
        m_justification[v] = dep;   
        m_assignment.push(v , value);
        s.ctx.push(mk_assign_var(v, *this));

        // update the watch lists for pvars
        // remove constraints from m_watch[v] that have more than 2 free variables.
        // for entries where there is only one free variable left add to viable set 
        unsigned j = 0;
        for (auto idx : m_watch[v]) {
            auto [sc, dep] = m_prop_queue[idx];
            auto& vars = sc.vars();
            if (vars[0] != v)
                std::swap(vars[0], vars[1]);
            SASSERT(vars[0] == v);
            bool swapped = false;
            for (unsigned i = vars.size(); i-- > 2; ) {
                if (!is_assigned(vars[i])) {
                    add_watch(idx, vars[i]);
                    std::swap(vars[i], vars[0]);
                    swapped = true;
                    break;
                }
            }
            if (!swapped) {
                m_watch[v][j++] = idx;
            }

            // constraint is unitary, add to viable set 
            if (vars.size() >= 2 && is_assigned(vars[0]) && !is_assigned(vars[1])) {
                // m_viable.add_unitary(vars[1], idx);
            }
        }
        m_watch[v].shrink(j);
    }

    void core::propagate_value(unsigned idx, dependent_constraint const& dc) {
        auto [sc, dep] = dc;
        // check if sc evaluates to false
        switch (eval(sc)) {
        case l_true:
            return;
        case l_false:
            m_unsat_core = explain_eval(dc);
            propagate_unsat_core();
            return;
        default:
            break;
        }
        // if sc is v == value, then check the watch list for v if they evaluate to false.
        if (sc.is_eq(m_var, m_value)) {
            for (auto idx : m_watch[m_var]) {
                auto [sc, dep] = m_prop_queue[idx];
                if (eval(sc) == l_false) {
                    m_unsat_core = explain_eval({ sc, dep });
                    propagate_unsat_core();
                    return;
                }
            }
        }

        throw default_exception("nyi"); 
    }

    bool core::propagate_unsat_core() { 
        // default is to use unsat core:
        s.set_conflict(m_unsat_core);
        // if core is based on viable, use s.set_lemma();
        throw default_exception("nyi"); 
    }

    void core::assign_eh(signed_constraint const& sc, dependency const& dep) { 
        m_prop_queue.push_back({ sc, m_dep.mk_leaf(dep) });
        s.ctx.push(push_back_vector(m_prop_queue));
    }



}
