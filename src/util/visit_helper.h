#pragma once
#include "sat_literal.h"

class visit_helper {
    
    unsigned_vector         m_visited;
    unsigned                m_visited_ts = 0;
    unsigned                m_visited_end = 0;
    
    void init_ts(unsigned n, unsigned lim = 1) {
        SASSERT(lim > 0);
        if (m_visited_end >= m_visited_end + lim) { // overflow
            m_visited_ts = 0;
            m_visited_end = lim;
            m_visited.reset();
        }
        else {
            m_visited_ts = m_visited_end;
            m_visited_end = m_visited_end + lim;
        }
        while (m_visited.size() < n) 
            m_visited.push_back(0);        
    }
    
public:
    
    void init_visited(unsigned num_vars, unsigned lim = 1) {
        init_ts(2 * num_vars, lim);
    }
    void mark_visited(sat::literal l) { m_visited[l.index()] = m_visited_ts; }
    void mark_visited(sat::bool_var v) { mark_visited(sat::literal(v, false)); }
    void inc_visited(sat::literal l) {
        m_visited[l.index()] = std::max(m_visited_ts, std::min(m_visited_end, m_visited[l.index()] + 1));
    }
    void inc_visited(sat::bool_var v) { inc_visited(sat::literal(v, false)); }
    bool is_visited(sat::bool_var v) const { return is_visited(sat::literal(v, false)); }
    bool is_visited(sat::literal l) const { return m_visited[l.index()] >= m_visited_ts; }
    unsigned num_visited(unsigned i) { return std::max(m_visited_ts, m_visited[i]) - m_visited_ts; }
};