/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

    sat_ddfw_wrapper.cpp

*/

#include "sat/sat_ddfw_wrapper.h"
#include "sat/sat_solver.h"
#include "sat/sat_parallel.h"

namespace sat {

    lbool ddfw_wrapper::check(unsigned sz, literal const* assumptions, parallel* p) { 
        flet<parallel*> _p(m_par, p);
        m_ddfw.m_parallel_sync = nullptr;
        if (m_par) {
            m_ddfw.m_parallel_sync = [&]() -> bool {
                if (should_parallel_sync()) {
                    do_parallel_sync();
                    return true;
                }
                else
                    return false;
                };
        }
        return m_ddfw.check(sz, assumptions); 
    }

    bool ddfw_wrapper::should_parallel_sync() {
        return m_par != nullptr && m_ddfw.m_flips >= m_parsync_next;
    }

    void ddfw_wrapper::do_parallel_sync() {
        if (m_par->from_solver(*this))
            m_par->to_solver(*this);

        ++m_parsync_count;
        m_parsync_next *= 3;
        m_parsync_next /= 2;
    }


    void ddfw_wrapper::reinit(solver& s, bool_vector const& phase) {
        add(s);
        m_ddfw.add_assumptions();
        for (unsigned v = 0; v < phase.size(); ++v) {
            m_ddfw.value(v) = phase[v];
            m_ddfw.set_reward(v, 0);
            m_ddfw.make_count(v) = 0;
        }
        m_ddfw.init_clause_data();
        m_ddfw.flatten_use_list();
    }

    void ddfw_wrapper::add(solver const& s) {
        m_ddfw.set_seed(s.get_config().m_random_seed);
        m_ddfw.m_clauses.reset(); 
        m_ddfw.m_use_list.reset();
        m_ddfw.m_num_non_binary_clauses = 0;

        unsigned trail_sz = s.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            m_ddfw.add(1, s.m_trail.data() + i);
        }
        unsigned sz = s.m_watches.size();
        for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
            literal l1 = ~to_literal(l_idx);
            watch_list const & wlist = s.m_watches[l_idx];
            for (watched const& w : wlist) {
                if (!w.is_binary_non_learned_clause())
                    continue;
                literal l2 = w.get_literal();
                if (l1.index() > l2.index()) 
                    continue;
                literal ls[2] = { l1, l2 };
                m_ddfw.add(2, ls);
            }
        }
        for (clause* c : s.m_clauses) 
            m_ddfw.add(c->size(), c->begin());        
    }    
}
