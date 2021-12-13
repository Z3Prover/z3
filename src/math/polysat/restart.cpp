/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Restart

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-12

  
--*/
#include "math/polysat/solver.h"
#include "math/polysat/restart.h"
#include "util/luby.h"

namespace polysat {

    restart::restart(solver& s):
        s(s)
    {}

    /*
    * Basic restart functionality.
    * restarts make more sense when the order of variable 
    * assignments and the values assigned to variables can be diversified.
    */
    bool restart::should_apply() const {
        if (s.m_stats.m_num_conflicts - m_conflicts_at_restart < m_restart_threshold)
            return false;
        if (s.base_level() + 2 > s.m_level)
            return false;
        return true;        
    }

    void restart::operator()() {
        ++s.m_stats.m_num_restarts;
        s.pop_levels(s.m_level - s.base_level());
        m_conflicts_at_restart = s.m_stats.m_num_conflicts;
        m_restart_threshold = m_restart_init * get_luby(++m_luby_idx);
    }

}
