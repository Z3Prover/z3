/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    sat_activity.cpp

Abstract:

    Double variable activities of the SAT solver, used with
    sat.activity.truncate=false. They are kept out of sat_solver.cpp so
    that the inline code of the default (unsigned) activities stays as
    small as before.

--*/

#include "sat/sat_solver.h"

namespace sat {

    void activity_queue::double_activity_increased_eh(var v) {
        m_double_queue.activity_increased_eh(v);
    }

    void activity_queue::double_activity_changed_eh(var v, bool up) {
        m_double_queue.activity_changed_eh(v, up);
    }

    void activity_queue::double_mk_var_eh(var v) {
        m_double_queue.mk_var_eh(v);
    }

    void activity_queue::double_del_var_eh(var v) {
        m_double_queue.del_var_eh(v);
    }

    void activity_queue::double_unassign_var_eh(var v) {
        m_double_queue.unassign_var_eh(v);
    }

    activity_queue::var activity_queue::double_next_var() {
        return m_double_queue.next_var();
    }

    bool activity_queue::double_more_active(var v1, var v2) const {
        return m_double_queue.more_active(v1, v2);
    }

    // Moves the variables of from to to, in the order of the heap of from.
    // If the activities of to order the variables as those of from do, up
    // to ties, the heap of from is a valid heap for to, and the insertions
    // reproduce it.
    template<typename From, typename To>
    static void move_queue(From& from, To& to, unsigned num_vars) {
        to.reset();
        to.reserve(num_vars);
        for (unsigned v : from)
            to.unassign_var_eh(v);
        from.reset();
    }

    void activity_queue::switch_activities(unsigned num_vars) {
        if (m_double)
            move_queue(m_double_queue, m_unsigned_queue, num_vars);
        else
            move_queue(m_unsigned_queue, m_double_queue, num_vars);
        m_double = !m_double;
    }

    void solver::set_double_activity(bool_var v, double new_act) {
        double old_act = m_double_activity[v];
        m_double_activity[v] = new_act;
        if (!was_eliminated(v) && value(v) == l_undef && new_act != old_act) {
            m_case_split_queue.activity_changed_eh(v, new_act > old_act);
        }
    }

    void solver::inc_double_activity(bool_var v) {
        double & act = m_double_activity[v];
        act += m_double_activity_inc;
        m_case_split_queue.activity_increased_eh(v);
        if (act > 1e100)
            rescale_double_activity();
    }

    void solver::decay_double_activity() {
        m_double_activity_inc *= m_config.m_variable_decay;
        m_double_activity_inc /= 100;
    }

    void solver::rescale_double_activity() {
        SASSERT(m_config.m_branching_heuristic == BH_VSIDS);
        // Scaling all activities and the increment by the same factor
        // preserves the order of the variables. An activity underflows to
        // zero only when it is below about 1e-300 of the largest one, that
        // is, after several rescales without a bump.
        for (double& act : m_double_activity)
            act *= 1e-100;
        m_double_activity_inc *= 1e-100;
    }

    // Factor that maps the largest double activity (or the increment) to
    // 2^24, the bound of the unsigned activities. It only scales down:
    // small activities are kept as they are.
    double solver::unsigned_activity_scale() const {
        double max_act = m_double_activity_inc;
        for (double act : m_double_activity)
            max_act = std::max(max_act, act);
        return max_act > 0 ? std::min(1.0, (1 << 24) / max_act) : 1.0;
    }

    // Converts the activities when sat.activity.truncate changed. Unsigned
    // activities convert to doubles exactly; doubles are scaled into the
    // unsigned range and truncated, which preserves their order up to ties.
    void solver::updt_activity_representation() {
        bool use_double = !m_config.m_activity_truncate;
        if (use_double == double_activity())
            return;
        if (use_double) {
            for (unsigned v = 0; v < m_activity.size(); ++v)
                m_double_activity[v] = m_activity[v];
            m_double_activity_inc = m_activity_inc;
        }
        else {
            double scale = unsigned_activity_scale();
            for (unsigned v = 0; v < m_double_activity.size(); ++v)
                m_activity[v] = static_cast<unsigned>(std::floor(m_double_activity[v] * scale));
            m_activity_inc = std::max(1u, static_cast<unsigned>(std::floor(m_double_activity_inc * scale)));
        }
        m_case_split_queue.switch_activities(num_vars());
    }
}
