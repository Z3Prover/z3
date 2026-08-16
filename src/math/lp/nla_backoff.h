/*++
  Copyright (c) 2026 Microsoft Corporation

  Module Name:

  nla_backoff.h

  Abstract:

  Scheduling policies for expensive nonlinear engines.

  Author:
    Lev Nachmanson (levnach)

  --*/
#pragma once
#include <algorithm>

namespace nla {

// Exponential backoff: on success re-engage, otherwise double the delay
// until the next run.
class backoff {
    unsigned m_delay = 0;
    unsigned m_delay_bound = 0;
public:
    void set_delay_bound(unsigned b) { m_delay_bound = b; }
    // counts the delay down; the engine runs when it is exhausted
    bool should_run() {
        if (m_delay > 0)
            --m_delay;
        return m_delay < 2;
    }
    void update(bool success) {
        if (success)
            m_delay_bound /= 2;
        else if (m_delay_bound < (1u << 20))
            m_delay_bound = std::max(2 * m_delay_bound, 1u);
        m_delay = m_delay_bound;
    }
};

// Schedules the eager bound squeeze: eager while it improves bounds,
// disabled after too many squeezes without check() finding nothing to refine.
class squeeze_schedule {
    unsigned m_fail_streak = 0;             // consecutive fruitless squeezes
    unsigned m_squeezes_since_sat_check = 0; // squeezes since check() last found nothing to refine
public:
    bool enabled() const { return m_squeezes_since_sat_check < 50; }
    bool eager() const { return m_fail_streak < 3; }
    void on_squeeze(bool improved_bounds) {
        ++m_squeezes_since_sat_check;
        if (improved_bounds)
            m_fail_streak = 0;
        else
            ++m_fail_streak;
    }
    void on_nothing_to_refine() { m_squeezes_since_sat_check /= 2; }
};

}
