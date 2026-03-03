/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nseq_state.h

Abstract:

    Constraint store bridging the SMT context to the Nielsen graph.
    Holds word equations and regex membership constraints with
    push/pop support for backtracking.

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#pragma once

#include "util/vector.h"
#include "ast/euf/euf_sgraph.h"
#include "smt/seq/seq_nielsen.h"

namespace smt {

    class nseq_state {
        euf::sgraph&            m_sg;
        vector<seq::str_eq>     m_str_eqs;
        vector<seq::str_mem>    m_str_mems;
        unsigned_vector         m_str_eq_lim;
        unsigned_vector         m_str_mem_lim;
        unsigned                m_next_mem_id = 0;

    public:
        nseq_state(euf::sgraph& sg) : m_sg(sg) {}

        void push() {
            m_str_eq_lim.push_back(m_str_eqs.size());
            m_str_mem_lim.push_back(m_str_mems.size());
        }

        void pop(unsigned n) {
            for (unsigned i = 0; i < n; ++i) {
                m_str_eqs.shrink(m_str_eq_lim.back());
                m_str_eq_lim.pop_back();
                m_str_mems.shrink(m_str_mem_lim.back());
                m_str_mem_lim.pop_back();
            }
        }

        void add_str_eq(euf::snode* lhs, euf::snode* rhs) {
            seq::dep_tracker dep;
            m_str_eqs.push_back(seq::str_eq(lhs, rhs, dep));
        }

        void add_str_mem(euf::snode* str, euf::snode* regex) {
            seq::dep_tracker dep;
            m_str_mems.push_back(seq::str_mem(str, regex, nullptr, m_next_mem_id++, dep));
        }

        vector<seq::str_eq> const&  str_eqs()  const { return m_str_eqs; }
        vector<seq::str_mem> const& str_mems() const { return m_str_mems; }

        bool empty() const { return m_str_eqs.empty() && m_str_mems.empty(); }

        void reset() {
            m_str_eqs.reset();
            m_str_mems.reset();
            m_str_eq_lim.reset();
            m_str_mem_lim.reset();
        }
    };

}
