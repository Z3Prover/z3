/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    sat_activity_queue.h

Abstract:

    Case-split queue of the SAT solver over one of two activity vectors:
    the unsigned activities (sat.activity.truncate=true, the default) or
    the double activities (sat.activity.truncate=false). Only the queue
    of the active representation holds variables.

--*/
#pragma once

#include "util/var_queue.h"

namespace sat {

    class activity_queue {
        typedef unsigned var;
        var_queue<svector<unsigned>> m_unsigned_queue;
        var_queue<svector<double>>   m_double_queue;
        bool                         m_double = false;

    public:
        activity_queue(svector<unsigned>& act, svector<double>& dact):
            m_unsigned_queue(act), m_double_queue(dact) {}

        bool uses_double() const { return m_double; }

        // Switches to the other activity vector; the caller has set its
        // activities for all variables.
        void switch_activities(unsigned num_vars);

        // The unsigned queue is used inline, as before the double
        // activities were added; the double queue out of line
        // (sat_activity.cpp), so that the default path stays small enough
        // to be inlined into the solver.
        void activity_increased_eh(var v) {
            if (m_double)
                double_activity_increased_eh(v);
            else
                m_unsigned_queue.activity_increased_eh(v);
        }

        void activity_changed_eh(var v, bool up) {
            if (m_double)
                double_activity_changed_eh(v, up);
            else
                m_unsigned_queue.activity_changed_eh(v, up);
        }

        void mk_var_eh(var v) {
            if (m_double)
                double_mk_var_eh(v);
            else
                m_unsigned_queue.mk_var_eh(v);
        }

        void del_var_eh(var v) {
            if (m_double)
                double_del_var_eh(v);
            else
                m_unsigned_queue.del_var_eh(v);
        }

        void unassign_var_eh(var v) {
            if (m_double)
                double_unassign_var_eh(v);
            else
                m_unsigned_queue.unassign_var_eh(v);
        }

        void reset() {
            m_unsigned_queue.reset();
            m_double_queue.reset();
        }

        bool empty() const {
            return m_double ? m_double_queue.empty() : m_unsigned_queue.empty();
        }

        var next_var() {
            return m_double ? double_next_var() : m_unsigned_queue.next_var();
        }

        var min_var() {
            return m_double ? m_double_queue.min_var() : m_unsigned_queue.min_var();
        }

        bool more_active(var v1, var v2) const {
            return m_double ? double_more_active(v1, v2) : m_unsigned_queue.more_active(v1, v2);
        }

        std::ostream& display(std::ostream& out) const {
            return m_double ? m_double_queue.display(out) : m_unsigned_queue.display(out);
        }

    private:
        void double_activity_increased_eh(var v);
        void double_activity_changed_eh(var v, bool up);
        void double_mk_var_eh(var v);
        void double_del_var_eh(var v);
        void double_unassign_var_eh(var v);
        var double_next_var();
        bool double_more_active(var v1, var v2) const;
    };
}
