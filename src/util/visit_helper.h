/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    visit_helper.h

Abstract:

    Routine for marking and counting visited occurrences

Author:

    Clemens Eisenhofer 2022-11-03

--*/
#pragma once


class visit_helper {
    
    unsigned_vector         m_visited;
    unsigned                m_visited_begin = 0;
    unsigned                m_visited_end = 0;
    
public:
    
    void init_visited(unsigned n, unsigned lim = 1) {
        SASSERT(lim > 0);
        if (m_visited_end >= m_visited_end + lim) { // overflow
            m_visited_begin = 0;
            m_visited_end = lim;
            m_visited.reset();
        }
        else {
            m_visited_begin = m_visited_end;
            m_visited_end = m_visited_end + lim;
        }
        while (m_visited.size() < n)
            m_visited.push_back(0);
    }
    
    void mark_visited(unsigned v) { m_visited[v] = m_visited_begin + 1; }
    void inc_visited(unsigned v) {
        m_visited[v] = std::min(m_visited_end, std::max(m_visited_begin, m_visited[v]) + 1);
    }
    bool is_visited(unsigned v) const { return m_visited[v] > m_visited_begin; }
    unsigned num_visited(unsigned v) { return std::max(m_visited_begin, m_visited[v]) - m_visited_begin; }
};