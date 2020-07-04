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

#pragma once

#include "util/debug.h"
#include <chrono>
#include <iostream>
#include<iomanip>


class stopwatch
{
    typedef decltype(std::chrono::steady_clock::now()) clock_t;
    typedef decltype(std::chrono::steady_clock::now() - std::chrono::steady_clock::now()) duration_t;

    clock_t m_start;
    duration_t m_elapsed;
    bool m_running = false;

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
    }
    
    void start() {
        if (!m_running) {
            m_start = get();
            m_running = true;
        }
    }

    void stop() {
        if (m_running) {
            m_elapsed += get() - m_start;
            m_running = false;
        }
    }

    double get_seconds() const {
        if (m_running) {
            const_cast<stopwatch*>(this)->stop();
            const_cast<stopwatch*>(this)->start();
        }
        return std::chrono::duration_cast<std::chrono::milliseconds>(m_elapsed).count() / 1000.0;
    }

    double get_current_seconds() const {
        return get_seconds();
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

inline std::ostream& operator<<(std::ostream& out, stopwatch const& sw) {
    return out << " :time " << std::fixed << std::setprecision(2) << sw.get_seconds();
}


