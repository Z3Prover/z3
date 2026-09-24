/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_geometric.h

Abstract:

    Step-size bookkeeping shared by geometric optimization searches.

--*/
#pragma once

#include "util/debug.h"
#include "util/rational.h"

namespace opt {

    class geometric_step {
        unsigned m_steps = 0;
        unsigned m_step_incs = 0;
        rational m_value{1};

        void check_value() const {
            SASSERT(m_value.is_int());
            SASSERT(m_value.is_pos());
        }

    public:
        geometric_step() { check_value(); }

        rational const& value() const { return m_value; }

        void update(bool can_increase) {
            // A round that cannot grow uses step one but keeps both counters.
            // Only reset() restarts the doubling schedule.
            if (!can_increase)
                m_value = 1;
            else if (m_steps > m_step_incs) {
                m_value *= rational(2);
                ++m_step_incs;
                m_steps = 0;
            }
            else
                ++m_steps;
            check_value();
        }

        void reset() {
            m_steps = 0;
            m_step_incs = 0;
            m_value = 1;
            check_value();
        }
    };
}
