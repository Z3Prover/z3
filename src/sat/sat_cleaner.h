/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_cleaner.h

Abstract:

    Eliminate satisfied clauses, and literals assigned to false.

Author:

    Leonardo de Moura (leonardo) 2011-05-24.

Revision History:

--*/
#ifndef SAT_CLEANER_H_
#define SAT_CLEANER_H_

#include "sat/sat_types.h"
#include "util/statistics.h"

namespace sat {

    class cleaner {
        struct report;

        solver & s;
        unsigned m_last_num_units;
        int      m_cleanup_counter;

        // stats
        unsigned m_elim_clauses;
        unsigned m_elim_literals;

        void cleanup_watches();
        void cleanup_clauses(clause_vector & cs);
    public:
        cleaner(solver & s);

        bool is_clean() const;
        bool operator()(bool force = false);

        void collect_statistics(statistics & st) const;
        void reset_statistics();

        void dec() { m_cleanup_counter--; }
    };

};

#endif
