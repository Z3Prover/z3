/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    stopwatch.h

Abstract:

    High resolution time keeping

Author:

    Christoph Wintersteiger (t-cwinte) 2008-12-24

Revision History:

--*/

#ifndef STOPWATCH_H_
#define STOPWATCH_H_

#include "util/debug.h"
#include <chrono>

class stopwatch
{
    typedef decltype(std::chrono::steady_clock::now()) clock_t;
    typedef decltype(std::chrono::steady_clock::now() - std::chrono::steady_clock::now()) duration_t;

    clock_t m_start;
    duration_t m_elapsed;
#if Z3DEBUG
    bool m_running = false;
#endif
    
    // FIXME: just use auto with VS 2015+
    static clock_t get() {
        return std::chrono::steady_clock::now();
    }

public:
    stopwatch() {
        reset();
    }

    void add(const stopwatch &s) {
        m_elapsed += s.m_elapsed;
    }

    void reset() {
        m_elapsed = duration_t::zero();
        DEBUG_CODE(m_running = false;);
    }
    
    void start() {
        SASSERT(!m_running);
        DEBUG_CODE(m_running = true;);
        m_start = get();
    }

    void stop() {
        // SASSERT(m_running);
        DEBUG_CODE(m_running = false;);
        m_elapsed += get() - m_start;
    }

    double get_seconds() const {
        return std::chrono::duration_cast<std::chrono::milliseconds>(m_elapsed).count() / 1000.0;
    }

    double get_current_seconds() const {
        return std::chrono::duration_cast<std::chrono::milliseconds>(get() - m_start).count() / 1000.0;
    }
};


struct scoped_watch {
    stopwatch &m_sw;
    scoped_watch (stopwatch &sw, bool reset=false): m_sw(sw) {
        if (reset) m_sw.reset(); 
        m_sw.start();
    }
    ~scoped_watch() {
        m_sw.stop ();
    }
};

#endif
