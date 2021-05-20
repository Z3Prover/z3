/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat boolean variables

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/boolean.h"
#include "math/polysat/log.h"

namespace polysat {

    bool_var bool_var_manager::new_var() {
        if (m_unused.empty()) {
            bool_var var = size();
            m_value.push_back(l_undef);
            m_value.push_back(l_undef);
            m_level.push_back(UINT_MAX);
            m_reason.push_back(nullptr);
            m_lemma.push_back(nullptr);
            return var;
        } else {
            bool_var var = m_unused.back();
            m_unused.pop_back();
            SASSERT_EQ(m_level[var], UINT_MAX);
            return var;
        }
    }

    void bool_var_manager::del_var(bool_var var) {
        SASSERT(std::all_of(m_unused.begin(), m_unused.end(), [var](unsigned unused_var) { return var != unused_var; }));
        auto lit = bool_lit::positive(var);
        m_value[lit.index()]    = l_undef;
        m_value[(~lit).index()] = l_undef;
        m_level[var] = UINT_MAX;
        m_reason[var] = nullptr;
        m_lemma[var] = nullptr;
        m_unused.push_back(var);
    }

    void bool_var_manager::assign(bool_lit lit, unsigned lvl, clause* reason, clause* lemma) {
        SASSERT(!is_assigned(lit));
        m_value[lit.index()] = l_true;
        m_value[(~lit).index()] = l_false;
        m_level[lit.var()] = lvl;
        m_reason[lit.var()] = reason;
        m_lemma[lit.var()] = lemma;
    }

    void bool_var_manager::unassign(bool_lit lit) {
        SASSERT(is_assigned(lit));
        m_value[lit.index()] = l_undef;
        m_value[(~lit).index()] = l_undef;
        m_level[lit.var()] = UINT_MAX;
        m_reason[lit.var()] = nullptr;
        m_lemma[lit.var()] = nullptr;
    }

    void bool_var_manager::reset_marks() {
        m_marks.reserve(size());
        m_clock++;
        if (m_clock != 0)
            return;
        m_clock++;
        m_marks.fill(0);
    }

    void bool_var_manager::set_mark(bool_var var) {
        SASSERT(var != null_bool_var);
        m_marks[var] = m_clock;
    }

    std::ostream& operator<<(std::ostream& out, bool_lit const& lit) {
        if (lit.is_negative())
            out << "~";
        return out << lit.var();
    }
}
