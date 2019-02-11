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
#include "sat/sat_cleaner.h"
#include "sat/sat_solver.h"
#include "util/trace.h"
#include "util/stopwatch.h"

namespace sat {

    cleaner::cleaner(solver & _s):
        s(_s),
        m_last_num_units(0), 
        m_cleanup_counter(0) {
        reset_statistics();
    }
    
    /**
       - Delete watch lists of assigned literals.
       - Delete satisfied binary watched binary clauses
       - Delete watched clauses (they will be reinserted after they are cleaned).
    */
    void cleaner::cleanup_watches() {
        vector<watch_list>::iterator it  = s.m_watches.begin();
        vector<watch_list>::iterator end = s.m_watches.end();
        unsigned l_idx = 0;
        for (; it != end; ++it, ++l_idx) {
            if (s.value(to_literal(l_idx)) != l_undef) {
                it->finalize();
                SASSERT(it->empty());
                continue;
            }
            TRACE("cleanup_bug", tout << "processing wlist of " << to_literal(l_idx) << "\n";);
            watch_list & wlist = *it;
            watch_list::iterator it2      = wlist.begin();
            watch_list::iterator it_prev  = it2;
            watch_list::iterator end2     = wlist.end();
            for (; it2 != end2; ++it2) {
                switch (it2->get_kind()) {
                case watched::BINARY:
                    SASSERT(s.value(it2->get_literal()) == l_true || s.value(it2->get_literal()) == l_undef);
                    if (s.value(it2->get_literal()) == l_undef) {
                        *it_prev = *it2;
                        ++it_prev;
                    }
                    TRACE("cleanup_bug", tout << "keeping: " << ~to_literal(l_idx) << " " << it2->get_literal() << "\n";);
                    break;
                case watched::TERNARY:
                case watched::CLAUSE:
                    // skip
                    break;
                case watched::EXT_CONSTRAINT:
                    *it_prev = *it2;
                    ++it_prev;
                    break;
                default:
                    UNREACHABLE();
                    break;
                }
            }
            wlist.set_end(it_prev);
        }
    }

    void cleaner::cleanup_clauses(clause_vector & cs) {
        clause_vector::iterator it  = cs.begin();
        clause_vector::iterator it2 = it;
        clause_vector::iterator end = cs.end();
        for (; it != end; ++it) {
            clause & c = *(*it);
            TRACE("sat_cleaner_bug", tout << "cleaning: " << c << "\n";
                  for (unsigned i = 0; i < c.size(); i++) tout << c[i] << ": " << s.value(c[i]) << "\n";);
            CTRACE("sat_cleaner_frozen", c.frozen(), tout << c << "\n";);
            unsigned sz = c.size();
            unsigned i = 0, j = 0;
            m_cleanup_counter += sz;
            for (; i < sz; i++) {
                switch (s.value(c[i])) {
                case l_true:
                    goto end_loop;
                case l_false:
                    m_elim_literals++;
                    break;
                case l_undef:
                    if (i != j) {
                        std::swap(c[j], c[i]);
                    }
                    j++;
                    break;
                }
            }
        end_loop:
            CTRACE("sat_cleaner_frozen", c.frozen(),
                   tout << "sat: " << (i < sz) << ", new_size: " << j << "\n";
                   tout << mk_lits_pp(j, c.begin()) << "\n";);
            if (i < sz) {
                m_elim_clauses++;
                s.del_clause(c);
            }
            else {
                unsigned new_sz = j;
                CTRACE("sat_cleaner_bug", new_sz < 2, tout << "new_sz: " << new_sz << "\n";
                       if (c.size() > 0) tout << "unit: " << c[0] << "\n";
                       s.display_watches(tout););
                switch (new_sz) {
                case 0:
                    s.set_conflict();
                    s.del_clause(c);
                    break;
                case 1:
                    s.assign_unit(c[0]);
                    s.del_clause(c);
                    break;
                case 2:
                    SASSERT(s.value(c[0]) == l_undef && s.value(c[1]) == l_undef);
                    TRACE("cleanup_bug", tout << "clause became binary: " << c[0] << " " << c[1] << "\n";);
                    s.mk_bin_clause(c[0], c[1], c.is_learned());
                    s.del_clause(c);
                    break;
                default:
                    c.shrink(new_sz);
                    *it2 = *it;
                    it2++;
                    if (!c.frozen()) {                            
                        s.attach_clause(c);
                    }
                    if (s.m_config.m_drat && new_sz < sz) {
                        s.m_drat.add(c, true);
                        c.restore(sz);
                        s.m_drat.del(c);
                        c.shrink(new_sz);
                    }
                    break;
                }
            }
        }
        cs.set_end(it2);
    }

    struct cleaner::report {
        cleaner & m_cleaner;
        stopwatch m_watch;
        unsigned  m_elim_clauses;
        unsigned  m_elim_literals;
        report(cleaner & c):
            m_cleaner(c),
            m_elim_clauses(c.m_elim_clauses),
            m_elim_literals(c.m_elim_literals) {
            m_watch.start();
        }
        ~report() {
            m_watch.stop();
            IF_VERBOSE(2,
                       verbose_stream() << " (sat-cleaner";
                       verbose_stream() << " :elim-literals " << (m_cleaner.m_elim_literals - m_elim_literals);
                       verbose_stream() << " :elim-clauses " << (m_cleaner.m_elim_clauses - m_elim_clauses);
                       verbose_stream() << " :cost " << m_cleaner.m_cleanup_counter << m_watch << ")\n";);
        }
    };

    /**
       \brief Return true if cleaner executed.
    */
    bool cleaner::operator()(bool force) {
        CASSERT("cleaner_bug", s.check_invariant());
        unsigned trail_sz = s.m_trail.size();
        s.propagate(false); // make sure that everything was propagated.
        TRACE("sat_cleaner_bug", s.display(tout); s.display_watches(tout););
        if (s.m_inconsistent)
            return false;
        if (m_last_num_units == trail_sz)
            return false; // there are no new assigned literals since last time... nothing to be done
        if (!force && m_cleanup_counter > 0)
            return false; // prevent simplifier from being executed over and over again.
        report rpt(*this);
        m_last_num_units = trail_sz;
        m_cleanup_counter = 0;
        do {
            trail_sz = s.m_trail.size();
            cleanup_watches();
            cleanup_clauses(s.m_clauses);
            cleanup_clauses(s.m_learned);
            s.propagate(false);
        }
        while (trail_sz < s.m_trail.size());
        CASSERT("cleaner_bug", s.check_invariant());
        return true;
    }
    
    void cleaner::reset_statistics() {
        m_elim_clauses = 0;
        m_elim_literals = 0;
    }
    
    void cleaner::collect_statistics(statistics & st) const {
        st.update("sat elim clauses", m_elim_clauses);
        st.update("sat elim literals", m_elim_literals);
    }

};
