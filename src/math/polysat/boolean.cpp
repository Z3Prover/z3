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

namespace polysat {

        // svector<bool_var>   m_unused;  // previously deleted variables that can be reused by new_var();
        // svector<lbool>      m_value;   // current value (indexed by literal)
        // svector<unsigned>   m_level;   // level of assignment (indexed by variable)
        // svector<clause*>    m_reason;  // propagation reason, NULL for decisions (indexed by variable)

        // // For enumerative backtracking we store the lemma we're handling with a certain decision
        // svector<clause*>    m_lemma;

        // unsigned_vector     m_marks;
        // unsigned            m_clock { 0 };

    bool_var bool_var_manager::new_var() {
        if (m_unused.empty()) {
            bool_var var = size();
            m_value.push_back(l_undef);
            m_value.push_back(l_undef);
            m_level.push_back(UINT_MAX);
            m_reason.push_back(nullptr);
            return var;
        } else {
            bool_var var = m_unused.back();
            m_unused.pop_back();
            SASSERT_EQ(m_level[var], UINT_MAX);
            return var;
        }
    }

    void bool_var_manager::del_var(bool_var var) {
        auto lit = bool_lit::positive(var);
        m_value[lit.index()]    = l_undef;
        m_value[(~lit).index()] = l_undef;
        m_level[var] = UINT_MAX;
        m_reason[var] = nullptr;
        m_unused.push_back(var);
    }

    void bool_var_manager::assign(bool_lit lit, unsigned lvl, clause* reason) {
        m_value[lit.index()] = l_true;
        m_value[(~lit).index()] = l_false;
        m_level[lit.var()] = lvl;
        m_reason[lit.var()] = reason;
    }

    void bool_var_manager::reset_marks() {
        m_marks.reserve(size());
        m_clock++;
        if (m_clock != 0)
            return;
        m_clock++;
        m_marks.fill(0);
    }

    std::ostream& operator<<(std::ostream& out, bool_lit const& lit) {
        if (lit.is_negative())
            out << "~";
        return out << lit.var();
    }
}
