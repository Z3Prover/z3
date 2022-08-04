/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat boolean variables

Author:

    Jakob Rath 2021-04-6

--*/
#include "math/polysat/boolean.h"
#include "math/polysat/clause.h"
#include "math/polysat/log.h"

namespace polysat {

    sat::bool_var bool_var_manager::new_var() {
        sat::bool_var var;
        if (m_unused.empty()) {
            var = size();
            m_value.push_back(l_undef);
            m_value.push_back(l_undef);
            m_level.push_back(UINT_MAX);
            m_deps.push_back(null_dependency);
            m_kind.push_back(kind_t::unassigned);
            m_reason.push_back(nullptr);
            m_watch.push_back({});
            m_watch.push_back({});
        }
        else {
            var = m_unused.back();
            m_unused.pop_back();
            auto lit = sat::literal(var);
            SASSERT_EQ(m_value[lit.index()], l_undef);
            SASSERT_EQ(m_value[(~lit).index()], l_undef);
            SASSERT_EQ(m_level[var], UINT_MAX);
            SASSERT_EQ(m_deps[var], null_dependency);
            SASSERT_EQ(m_kind[var], kind_t::unassigned);
            SASSERT_EQ(m_reason[var], nullptr);
            SASSERT(m_watch[lit.index()].empty());
            SASSERT(m_watch[(~lit).index()].empty());
        }
        return var;
    }

    void bool_var_manager::del_var(sat::bool_var var) {
        SASSERT(std::count(m_unused.begin(), m_unused.end(), var) == 0);
        auto lit = sat::literal(var);
        m_value[lit.index()]    = l_undef;
        m_value[(~lit).index()] = l_undef;
        m_level[var] = UINT_MAX;
        m_kind[var] = kind_t::unassigned;
        m_reason[var] = nullptr;
        m_deps[var] = null_dependency;
        m_watch[lit.index()].reset();
        m_watch[(~lit).index()].reset();
        // TODO: this is disabled for now, since re-using variables for different constraints may be confusing during debugging. Should be enabled later.
        // m_unused.push_back(var);
    }

    void bool_var_manager::propagate(sat::literal lit, unsigned lvl, clause& reason) {
        LOG("Propagate literal " << lit << " @ " << lvl << " by " << reason);
        assign(kind_t::bool_propagation, lit, lvl, &reason);
        SASSERT(is_bool_propagation(lit));
    }

    void bool_var_manager::eval(sat::literal lit, unsigned lvl) {
        LOG("Eval literal " << lit << " @ " << lvl);
        assign(kind_t::value_propagation, lit, lvl, nullptr);
        SASSERT(is_value_propagation(lit));
    }

    void bool_var_manager::assumption(sat::literal lit, unsigned lvl, dependency dep) {
        LOG("Asserted " << lit << " @ " << lvl);
        assign(kind_t::assumption, lit, lvl, nullptr, dep);
        SASSERT(is_assumption(lit));
    }

    void bool_var_manager::assign(kind_t k, sat::literal lit, unsigned lvl, clause* reason, dependency dep) {
        SASSERT(!is_assigned(lit));
        SASSERT(k != kind_t::unassigned);
        m_value[lit.index()] = l_true;
        m_value[(~lit).index()] = l_false;
        m_level[lit.var()] = lvl;
        m_kind[lit.var()] = k;
        m_reason[lit.var()] = reason;
        m_deps[lit.var()] = dep;
    }

    void bool_var_manager::unassign(sat::literal lit) {
        SASSERT(is_assigned(lit));
        m_value[lit.index()] = l_undef;
        m_value[(~lit).index()] = l_undef;
        m_level[lit.var()] = UINT_MAX;
        m_kind[lit.var()] = kind_t::unassigned;
        m_reason[lit.var()] = nullptr;
        m_deps[lit.var()] = null_dependency;
    }

    std::ostream& bool_var_manager::display(std::ostream& out) const {
        for (sat::bool_var v = 0; v < size(); ++v) {
            sat::literal lit(v);
            if (value(lit) == l_true)
                out << " " << lit;
            else if (value(lit) == l_false)
                out << " " << ~lit;
        }
        return out;
    }

    std::ostream& bool_var_manager::display_justification(sat::literal lit, std::ostream& out) const {
        out << m_kind[lit.var()];
        if (is_assigned(lit))
            out << " @ " << level(lit);
        if (is_bool_propagation(lit))
            out << " by " << show_deref(reason(lit));
        return out;
    }
}
