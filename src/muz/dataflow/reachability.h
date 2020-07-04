/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    reachability.h

Abstract:

    Abstract domain for tracking rule reachability.

Author:
    Henning Guenther (t-hennig)

--*/

#pragma once

#include "muz/dataflow/dataflow.h"

namespace datalog {
    class reachability_info {
        bool m_reachable;
        reachability_info(bool r) : m_reachable(r) {}
    public:
        typedef ast_manager ctx_t;
        static const reachability_info null_fact;
        reachability_info() : m_reachable(false) {}

        void init_down(const ctx_t& m, const rule* r) {
            m_reachable = true;
        }

        bool init_up(const ctx_t& m, const rule* r) {
            if (m_reachable) 
                return false;
            else {
                m_reachable = true;
                return true;
            }
        }

        void propagate_down(const ctx_t& manager, const rule* r, fact_writer<reachability_info>& tail_facts) const {
            SASSERT(m_reachable);
            for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
                reachability_info& tail_fact = tail_facts.get(i);
                if (!tail_fact.m_reachable) {
                    tail_fact.m_reachable = true;
                    tail_facts.set_changed(i);
                }
            }
        }

        bool propagate_up(const ctx_t& manager, const rule* r, const fact_reader<reachability_info>& tail_facts) {
            if (m_reachable)
                return false;

            for (unsigned i = 0; i < r->get_positive_tail_size(); ++i) {
                if (!tail_facts.get(i).m_reachable) {
                    return false;
                }
            }
            m_reachable = true;
            return true;
        }

        void join(const ctx_t& manager, const reachability_info& oth) {
            m_reachable |= oth.m_reachable;
        }

        void dump(const ctx_t& manager, std::ostream& outp) const {
            outp << (m_reachable ? "reachable" : "unreachable");
        }

        bool is_reachable() const { return m_reachable; }
    };

    typedef dataflow_engine<reachability_info> reachability;
}

