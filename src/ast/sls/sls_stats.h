#pragma once
#include "util/statistics.h"
#include "util/stopwatch.h"


namespace bv {
    class sls_stats {
    public:
        unsigned        m_restarts = 0;
        unsigned        m_full_evals = 0;
        unsigned        m_incr_evals = 0;
        unsigned        m_moves = 0; 
        unsigned        m_flips = 0;
        unsigned        m_incs = 0;
        unsigned        m_decs = 0;
        unsigned        m_invs = 0;
        stopwatch       m_stopwatch;
        
        sls_stats() {
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
