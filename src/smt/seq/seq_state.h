/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_state.h

Abstract:

    Constraint store bridging the SMT context to the Nielsen graph.
    Holds word equations and regex membership constraints with
    push/pop support for backtracking.

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#pragma once

#include "util/vector.h"
#include "smt/seq/seq_nielsen.h"
#include "util/sat_literal.h"

namespace smt {

    class enode;

    struct tracked_str_eq : public seq::str_eq {
        enode *m_l, *m_r;
        tracked_str_eq(euf::snode *lhs, euf::snode *rhs, smt::enode *l, smt::enode *r, seq::dep_tracker const &dep)
            : seq::str_eq(lhs, rhs, dep), m_l(l), m_r(r) {}
    };

    struct tracked_str_mem : public seq::str_mem {
        sat::literal lit;
        tracked_str_mem(euf::snode *str, euf::snode *regex, sat::literal lit, euf::snode *history, unsigned id, seq::dep_tracker const &dep)
            : seq::str_mem(str, regex, history, id, dep), lit(lit) {}
    };

    // source info for a string disequality
    struct diseq_source {
        enode* m_n1;
        enode* m_n2;
    };

    class seq_state {
        vector<tracked_str_eq>     m_str_eqs;
        vector<tracked_str_mem>    m_str_mems;
        vector<diseq_source>    m_diseqs;
        unsigned_vector         m_str_eq_lim;
        unsigned_vector         m_str_mem_lim;
        unsigned_vector         m_diseq_lim;
        unsigned                m_next_mem_id = 0;

    public:
        seq_state() = default;

        void push() {
            m_str_eq_lim.push_back(m_str_eqs.size());
            m_str_mem_lim.push_back(m_str_mems.size());
            m_diseq_lim.push_back(m_diseqs.size());
        }

        void pop(unsigned n) {
            for (unsigned i = 0; i < n; ++i) {
                m_str_eqs.shrink(m_str_eq_lim.back());
                m_str_eq_lim.pop_back();
                m_str_mems.shrink(m_str_mem_lim.back());
                m_str_mem_lim.pop_back();
                m_diseqs.shrink(m_diseq_lim.back());
                m_diseq_lim.pop_back();
            }
        }

        void add_str_eq(euf::snode* lhs, euf::snode* rhs, enode* n1, enode* n2) {
            seq::dep_tracker dep = nullptr;
            m_str_eqs.push_back(tracked_str_eq(lhs, rhs, n1, n2, dep));
        }

        void add_str_mem(euf::snode* str, euf::snode* regex, sat::literal lit) {
            seq::dep_tracker dep = nullptr;
            m_str_mems.push_back(tracked_str_mem(str, regex, lit, nullptr, m_next_mem_id++, dep));
        }

        void add_diseq(enode* n1, enode* n2) {
            m_diseqs.push_back({n1, n2});
        }

        vector<tracked_str_eq> const&  str_eqs()  const { return m_str_eqs; }
        vector<tracked_str_mem> const& str_mems() const { return m_str_mems; }
        vector<diseq_source> const& diseqs()   const { return m_diseqs; }

        diseq_source const& get_diseq(unsigned i) const { return m_diseqs[i]; }

        bool empty() const { return m_str_eqs.empty() && m_str_mems.empty() && m_diseqs.empty(); }

        void reset() {
            m_str_eqs.reset();
            m_str_mems.reset();
            m_diseqs.reset();
            m_str_eq_lim.reset();
            m_str_mem_lim.reset();
            m_diseq_lim.reset();
        }
    };

}
