/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat boolean variables

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#include "math/polysat/boolean.h"
#include "math/polysat/log.h"

namespace polysat {

    sat::bool_var bool_var_manager::new_var() {
        if (m_unused.empty()) {
            sat::bool_var var = size();
            m_value.push_back(l_undef);
            m_value.push_back(l_undef);
            m_level.push_back(UINT_MAX);
            m_reason.push_back(nullptr);
            m_lemma.push_back(nullptr);
            return var;
        } else {
            sat::bool_var var = m_unused.back();
            m_unused.pop_back();
            SASSERT_EQ(m_level[var], UINT_MAX);
            return var;
        }
    }

    void bool_var_manager::del_var(sat::bool_var var) {
        SASSERT(std::all_of(m_unused.begin(), m_unused.end(), [var](unsigned unused_var) { return var != unused_var; }));
        auto lit = sat::literal(var);
        m_value[lit.index()]    = l_undef;
        m_value[(~lit).index()] = l_undef;
        m_level[var] = UINT_MAX;
        m_reason[var] = nullptr;
        m_lemma[var] = nullptr;
        m_unused.push_back(var);
    }

    void bool_var_manager::assign(sat::literal lit, unsigned lvl, clause* reason, clause* lemma) {
        SASSERT(!is_assigned(lit));
        m_value[lit.index()] = l_true;
        m_value[(~lit).index()] = l_false;
        m_level[lit.var()] = lvl;
        m_reason[lit.var()] = reason;
        m_lemma[lit.var()] = lemma;
    }

    void bool_var_manager::unassign(sat::literal lit) {
        SASSERT(is_assigned(lit));
        m_value[lit.index()] = l_undef;
        m_value[(~lit).index()] = l_undef;
        m_level[lit.var()] = UINT_MAX;
        m_reason[lit.var()] = nullptr;
        m_lemma[lit.var()] = nullptr;
    }

    void bool_var_manager::reset_marks() {
        LOG_V("-------------------------- (reset boolean marks)");
        m_marks.reserve(size());
        m_clock++;
        if (m_clock != 0)
            return;
        m_clock++;
        m_marks.fill(0);
    }

    void bool_var_manager::set_mark(sat::bool_var var) {
        LOG_V("Marking: b" << var);
        SASSERT(var != sat::null_bool_var);
        m_marks[var] = m_clock;
    }

    std::ostream& bool_var_manager::display(std::ostream& out) const {
        for (sat::bool_var v = 0; v < size(); ++v) {
            sat::literal lit{v};
            if (value(lit) == l_true)
                out << " " << lit;
            if (value(lit) == l_false)
                out << " " << ~lit;
        }
        return out;
    }
}
