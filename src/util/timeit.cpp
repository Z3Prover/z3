/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    timeit.h

Abstract:

    Support for timers.

Author:

    Nikolaj Bjorner (nbjorner) 2006-09-22

Revision History:

--*/
#include<iostream>
#include "util/timeit.h"
#include "util/memory_manager.h"
#include "util/stopwatch.h"
#include<iomanip>

struct timeit::imp {
    stopwatch      m_watch;
    char const *   m_msg;
    std::ostream & m_out;
    double         m_start_memory;
    
    imp(char const * msg, std::ostream & out):
        m_msg(msg), 
        m_out(out),
        m_start_memory(static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024)) {
        m_watch.start();
    }

    ~imp() {
        m_watch.stop();
        double end_memory = static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024);
        m_out << "(" << m_msg << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds() 
              << " :before-memory " << std::fixed << std::setprecision(2) << m_start_memory 
              << " :after-memory " << std::fixed << std::setprecision(2) << end_memory << ")" 
              << std::endl;
    }
};

timeit::timeit(bool enable, char const * msg, std::ostream & out) {
    if (enable)
        m_imp = alloc(imp, msg, out);
    else
        m_imp = nullptr;
}
   
timeit::~timeit() {
    if (m_imp)
        dealloc(m_imp);
}
