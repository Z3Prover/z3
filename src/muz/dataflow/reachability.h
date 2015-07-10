/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    reachability.h

Abstract:

    Abstract domain for tracking rule reachability.

Author:
    Henning Guenther (t-hennig)

--*/

#ifndef REACHABILITY_H_
#define REACHABILITY_H_

#include "dataflow.h"

namespace datalog {
    class reachability_info {
        bool m_reachable;
        reachability_info(bool r) : m_reachable(r) {}
    public:
        typedef ast_manager ctx_t;
        static const reachability_info null_fact;
        reachability_info() : m_reachable(false) {}
        reachability_info(func_decl* sym) : m_reachable(false) {}

        static void init_down(ctx_t& m, const rule_set& rules, fact_setter<reachability_info>& setter) {
            const func_decl_set& outputs = rules.get_output_predicates();
            for (func_decl_set::iterator I = outputs.begin(),
                E = outputs.end(); I != E; ++I) {
                reachability_info& fact = setter.get(*I);
                fact.m_reachable = true;
                setter.set_changed(*I);
            }
        }

        bool init_up(const ctx_t& m, const rule* r) {
            if (!m_reachable && r->get_uninterpreted_tail_size() == 0) {
                m_reachable = true;
                return true;
            } else
                return false;
        }

        void propagate_down(const ctx_t& manager, const rule* r, fact_writer<reachability_info>& tail_facts) const {
            if (m_reachable) {
                for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
                    reachability_info& tail_fact = tail_facts.get(i);
                    if (!tail_fact.m_reachable) {
                        tail_fact.m_reachable = true;
                        tail_facts.set_changed(i);
                    }
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

#endif
