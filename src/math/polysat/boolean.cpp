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
            m_reason.push_back(nullptr);
            m_lemma.push_back(nullptr);
            m_watch.push_back({});
            m_watch.push_back({});
            m_activity.push_back(0);
        }
        else {
            var = m_unused.back();
            m_unused.pop_back();
            SASSERT_EQ(m_level[var], UINT_MAX);
            SASSERT_EQ(m_value[2*var], l_undef);
            SASSERT_EQ(m_value[2*var+1], l_undef);
            SASSERT_EQ(m_reason[var], nullptr);
            SASSERT_EQ(m_lemma[var], nullptr);
            SASSERT_EQ(m_deps[var], null_dependency);
        }
        m_free_vars.mk_var_eh(var);
        return var;
    }

    void bool_var_manager::del_var(sat::bool_var var) {
        SASSERT(std::count(m_unused.begin(), m_unused.end(), var) == 0);
        auto lit = sat::literal(var);
        m_value[lit.index()]    = l_undef;
        m_value[(~lit).index()] = l_undef;
        m_level[var] = UINT_MAX;
        m_reason[var] = nullptr;
        m_lemma[var] = nullptr;
        m_deps[var] = null_dependency;
        m_watch[lit.index()].reset();
        m_watch[(~lit).index()].reset();
        m_free_vars.del_var_eh(var);
        // TODO: this is disabled for now, since re-using variables for different constraints may be confusing during debugging. Should be enabled later.
        // m_unused.push_back(var);
    }

    void bool_var_manager::propagate(sat::literal lit, unsigned lvl, clause& reason) {
        LOG("Propagate literal " << lit << " @ " << lvl << " by " << reason);
        assign(lit, lvl, &reason, nullptr, null_dependency);
    }

    void bool_var_manager::decide(sat::literal lit, unsigned lvl, clause* lemma) {
        LOG("Decide literal " << lit << " @ " << lvl);
        assign(lit, lvl, nullptr, lemma);
    }

    void bool_var_manager::eval(sat::literal lit, unsigned lvl) {
        LOG("Eval literal " << lit << " @ " << lvl);
        assign(lit, lvl, nullptr, nullptr);
    }

    void bool_var_manager::asserted(sat::literal lit, unsigned lvl, unsigned dep) {
        LOG("Asserted " << lit << " @ " << lvl);
        assign(lit, lvl, nullptr, nullptr, dep);
    }

    void bool_var_manager::assign(sat::literal lit, unsigned lvl, clause* reason, clause* lemma, unsigned dep) {
        SASSERT(!is_assigned(lit));
        m_value[lit.index()] = l_true;
        m_value[(~lit).index()] = l_false;
        m_level[lit.var()] = lvl;
        m_reason[lit.var()] = reason;
        m_lemma[lit.var()] = lemma;
        m_deps[lit.var()] = dep;
        m_free_vars.del_var_eh(lit.var());
    }

    void bool_var_manager::unassign(sat::literal lit) {
        SASSERT(is_assigned(lit));
        m_value[lit.index()] = l_undef;
        m_value[(~lit).index()] = l_undef;
        m_level[lit.var()] = UINT_MAX;
        m_reason[lit.var()] = nullptr;
        m_lemma[lit.var()] = nullptr;
        m_deps[lit.var()] = null_dependency;
        m_free_vars.unassign_var_eh(lit.var());
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
}
