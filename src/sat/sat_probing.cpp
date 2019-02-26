/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_probing.cpp

Abstract:

    Probing (aka failed literal detection).


Author:

    Leonardo de Moura (leonardo) 2011-06-04.

Revision History:

--*/
#include "sat/sat_probing.h"
#include "sat/sat_solver.h"
#include "sat/sat_simplifier_params.hpp"

namespace sat {
    probing::probing(solver & _s, params_ref const & p):
        s(_s) {
        updt_params(p);
        reset_statistics();
        m_stopped_at = 0;
        m_counter    = 0;
    }

    // reset the cache for the given literal
    void probing::reset_cache(literal l) {
        if (l.index() < m_cached_bins.size()) {
            m_cached_bins[l.index()].m_available = false;
            m_cached_bins[l.index()].m_lits.finalize();
        }
    }

    // l implied the literals on the trail stack starting at position old_tr_sz
    // Thus, ~l \/ l2 is a binary clause for every l2 on this fragment of the trail stack.
    void probing::cache_bins(literal l, unsigned old_tr_sz) {
        if (!m_probing_cache)
            return;
        if (memory::get_allocation_size() > m_probing_cache_limit)
            return; // not enough memory to spare
        m_cached_bins.reserve(l.index() + 1);
        cache_entry & entry = m_cached_bins[l.index()];
        entry.m_available = true;
        entry.m_lits.reset();
        unsigned tr_sz = s.m_trail.size();
        for (unsigned i = old_tr_sz; i < tr_sz; i++) {
            entry.m_lits.push_back(s.m_trail[i]);
            if (s.m_config.m_drat) {
                s.m_drat.add(~l, s.m_trail[i], true);
            }
        }
    }

    // Return true if should keep going.
    // It will assert literals implied by l that are already marked
    // as assigned.
    bool probing::try_lit(literal l, bool updt_cache) {
        SASSERT(s.m_qhead == s.m_trail.size());
        SASSERT(s.value(l.var()) == l_undef);
        literal_vector * implied_lits = updt_cache ? nullptr : cached_implied_lits(l);
        if (implied_lits) {
            for (literal lit : *implied_lits) {
                if (m_assigned.contains(lit)) {
                    if (s.m_config.m_drat) {
                        s.m_drat.add(l, lit, true);
                        s.m_drat.add(~l, lit, true);
                    }
                    s.assign_scoped(lit);
                    m_num_assigned++;
                }
            }
        }
        else {
            m_to_assert.reset();
            s.push();
            s.assign_scoped(l);
            m_counter--;
            unsigned old_tr_sz = s.m_trail.size();
            s.propagate(false);
            if (s.inconsistent()) {
                // ~l must be true
                s.pop(1);
                s.assign_scoped(~l);
                s.propagate(false);
                return false;
            }
            // collect literals that were assigned after assigning l
            unsigned tr_sz = s.m_trail.size();
            for (unsigned i = old_tr_sz; i < tr_sz; i++) {
                if (m_assigned.contains(s.m_trail[i])) {
                    m_to_assert.push_back(s.m_trail[i]);
                }
            }
            if (updt_cache)
                cache_bins(l, old_tr_sz);
            s.pop(1);

            for (literal lit : m_to_assert) {
                if (s.m_config.m_drat) {
                    s.m_drat.add(l, lit, true);
                    s.m_drat.add(~l, lit, true);
                }
                s.assign_scoped(lit);
                m_num_assigned++;
            }
        }
        s.propagate(false);
        return !s.inconsistent();
    }

    void probing::process_core(bool_var v) {
        TRACE("probing", tout << "processing: " << v << " counter: " << -m_counter << "\n";);
        SASSERT(s.m_qhead == s.m_trail.size());
        SASSERT(s.value(v) == l_undef);
        m_counter--;
        s.push();
        literal l(v, false);
        s.assign_scoped(l);
        unsigned old_tr_sz = s.m_trail.size();
        s.propagate(false);
        if (s.inconsistent()) {
            // ~l must be true
            s.pop(1);
            s.assign_scoped(~l);
            s.propagate(false);
            m_num_assigned++;
            return;
        }
        // collect literals that were assigned after assigning l
        m_assigned.reset();
        unsigned tr_sz = s.m_trail.size();
        for (unsigned i = old_tr_sz; i < tr_sz; i++) {
            m_assigned.insert(s.m_trail[i]);
        }
        cache_bins(l, old_tr_sz);
        s.pop(1);

        if (!try_lit(~l, true))
            return;

        if (m_probing_binary) {
            watch_list & wlist = s.get_wlist(~l);
            for (watched & w : wlist) {
                if (!w.is_binary_clause())
                    continue;
                literal l2 = w.get_literal();
                if (l.index() > l2.index())
                    continue;
                if (s.value(l2) != l_undef)
                    continue;
                // verbose_stream() << "probing " << l << " " << l2 << " " << m_counter << "\n";
                // Note: that try_lit calls propagate, which may update the watch lists.
                if (!try_lit(l2, false))
                    return;
                if (s.inconsistent())
                    return;
            }
        }
    }

    void probing::process(bool_var v) {
        int old_counter = m_counter;
        unsigned old_num_assigned = m_num_assigned;
        process_core(v);
        if (m_num_assigned > old_num_assigned) {
            // if new variables were assigned when probing x,
            // then assume the cost is 0.
            m_counter = old_counter;
        }
    }

    struct probing::report {
        probing    & m_probing;
        stopwatch    m_watch;
        unsigned     m_num_assigned;        
        report(probing & p):
            m_probing(p),
            m_num_assigned(p.m_num_assigned) {
            m_watch.start();
        }

        ~report() {
            m_watch.stop();
            unsigned units = (m_probing.m_num_assigned - m_num_assigned);
            IF_VERBOSE(2,
                       verbose_stream() << " (sat-probing";
                       if (units > 0) verbose_stream() << " :probing-assigned " << units;
                       verbose_stream() << " :cost " << m_probing.m_counter;
                       if (m_probing.m_stopped_at != 0) verbose_stream() << " :stopped-at " << m_probing.m_stopped_at;
                       verbose_stream() << mem_stat() << m_watch << ")\n";);
        }
    };

    bool probing::operator()(bool force) {
        if (!m_probing)
            return true;
        s.propagate(false); // make sure propagation queue is empty
        if (s.inconsistent())
            return true;
        SASSERT(s.m_qhead == s.m_trail.size());
        CASSERT("probing", s.check_invariant());
        if (!force && m_counter > 0)
            return true;

        if (m_probing_cache && memory::get_allocation_size() > m_probing_cache_limit)
            m_cached_bins.finalize();

        report rpt(*this);
        bool r    = true;
        m_counter = 0;
        int limit = -static_cast<int>(m_probing_limit);
        unsigned i;
        unsigned num = s.num_vars();
        for (i = 0; i < num; i++) {
            bool_var v = (m_stopped_at + i) % num;
            if (m_counter < limit) {
                m_stopped_at = v;
                r = false;
                break;
            }
            if (s.inconsistent()) {
                break;
            }
            if (s.value(v) != l_undef || s.was_eliminated(v)) {
                if (m_probing_cache) {
                    // cache for v literals is not needed anymore.
                    reset_cache(literal(v, false));
                    reset_cache(literal(v, true));
                }
                continue;
            }
            s.checkpoint();
            process(v);
        }
        if (r)
            m_stopped_at = 0;
        m_counter = -m_counter;
        if (rpt.m_num_assigned == m_num_assigned) {
            // penalize
            m_counter *= 2;
        }
        CASSERT("probing", s.check_invariant());
        finalize();
        return r;
    }

    void probing::updt_params(params_ref const & _p) {
        sat_simplifier_params p(_p);
        m_probing             = p.probing();
        m_probing_limit       = p.probing_limit();
        m_probing_cache       = p.probing_cache();
        m_probing_binary      = p.probing_binary();
        m_probing_cache_limit = p.probing_cache_limit();
    }

    void probing::collect_param_descrs(param_descrs & d) {
        // TODO
    }

    void probing::finalize() {
        m_assigned.finalize();
        m_to_assert.finalize();
        m_cached_bins.finalize();
    }

    void probing::collect_statistics(statistics & st) const {
        st.update("sat probing assigned", m_num_assigned);
    }

    void probing::reset_statistics() {
        m_num_assigned = 0;
    }
};
