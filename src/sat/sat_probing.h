/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_probing.h

Abstract:

    Probing (aka failed literal detection).


Author:

    Leonardo de Moura (leonardo) 2011-06-04.

Revision History:

--*/
#ifndef _SAT_PROBING_H_
#define _SAT_PROBING_H_

#include"sat_types.h"
#include"params.h"
#include"statistics.h"

namespace sat {

    class probing {
        solver &        s;
        unsigned        m_stopped_at;  // where did it stop
        literal_set     m_assigned;    // literals assigned in the first branch
        literal_vector  m_to_assert;

        // counters
        int             m_counter;       // track cost

        // config
        bool               m_probing;             // enabled/disabled
        unsigned           m_probing_limit;       // max cost per round
        bool               m_probing_cache;       // cache implicit binary clauses
        bool               m_probing_binary;      // try l1 and l2 for binary clauses l1 \/ l2
        unsigned long long m_probing_cache_limit; // memory limit for enabling caching.

        // stats
        unsigned           m_num_assigned;
        
        struct cache_entry {
            bool           m_available;
            literal_vector m_lits; 
            cache_entry():m_available(false) {}
        };

        vector<cache_entry> m_cached_bins;  

        struct report;

        void reset_cache(literal l);
        void cache_bins(literal l, unsigned old_tr_sz);
        bool try_lit(literal l, bool updt_cache);
        void process(bool_var v);
        void process_core(bool_var v);

    public:
        probing(solver & s, params_ref const & p);
        
        bool operator()(bool force = false);

        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);

        void free_memory();

        void collect_statistics(statistics & st) const;
        void reset_statistics();

        // return the literals implied by l.
        // return 0, if the cache is not available
        literal_vector * cached_implied_lits(literal l) {
            if (!m_probing_cache) return 0;
            if (l.index() >= m_cached_bins.size()) return 0;
            cache_entry & e = m_cached_bins[l.index()];
            if (!e.m_available) return 0;
            return &(e.m_lits);
        }

        void dec(unsigned c) { m_counter -= c; }
    };

};

#endif
