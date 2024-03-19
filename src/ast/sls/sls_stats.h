#pragma once
#include "util/statistics.h"
#include "util/stopwatch.h"


namespace bv {
    class sls_stats {
    public:
        unsigned        m_restarts;
        stopwatch       m_stopwatch;
        unsigned        m_full_evals;
        unsigned        m_incr_evals;
        unsigned        m_moves, m_flips, m_incs, m_decs, m_invs;
        
        sls_stats() :
            m_restarts(0),
            m_full_evals(0),
            m_incr_evals(0),
            m_moves(0),
            m_flips(0),
            m_incs(0),
            m_decs(0),
            m_invs(0) {
            m_stopwatch.reset();
            m_stopwatch.start();
        }
        void reset() {
            m_full_evals = m_flips = m_incr_evals = 0;
            m_stopwatch.reset();
            m_stopwatch.start();
        }

        void collect_statistics(statistics& st) const {            
            double seconds = m_stopwatch.get_current_seconds();            
            st.update("sls restarts", m_restarts);
            st.update("sls full evals", m_full_evals);
            st.update("sls incr evals", m_incr_evals);
            if (seconds > 0 && m_incr_evals > 0)
                st.update("sls incr evals/sec", m_incr_evals / seconds);
            if (seconds > 0 && m_moves > 0)
                st.update("sls moves/sec", m_moves / seconds);
            st.update("sls FLIP moves", m_flips);
            st.update("sls INC moves", m_incs);
            st.update("sls DEC moves", m_decs);
            st.update("sls INV moves", m_invs);
            st.update("sls moves", m_moves);

        }
        
    };
}
