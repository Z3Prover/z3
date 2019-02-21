/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    scoped_timer.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2011-04-26.

Revision History:

--*/

#include "util/scoped_timer.h"
#include "util/util.h"
#include <chrono>
#include <climits>
#include <mutex>
#include <thread>


struct scoped_timer::imp {
private:
    std::thread      m_thread;
    std::timed_mutex m_mutex;

    static void thread_func(unsigned ms, event_handler * eh, std::timed_mutex * mutex) {
        auto end = std::chrono::steady_clock::now() + std::chrono::milliseconds(ms);

        while (!mutex->try_lock_until(end)) {
            if (std::chrono::steady_clock::now() >= end) {
                eh->operator()(TIMEOUT_EH_CALLER);
                return;
            }
        }

        mutex->unlock();
    }

public:
    imp(unsigned ms, event_handler * eh) {
        m_mutex.lock();
        m_thread = std::thread(thread_func, ms, eh, &m_mutex);
    }

    ~imp() {
        m_mutex.unlock();
        m_thread.join();
    }
};

scoped_timer::scoped_timer(unsigned ms, event_handler * eh) {
    if (ms != UINT_MAX && ms != 0)
        m_imp = alloc(imp, ms, eh);
    else
        m_imp = nullptr;
}
    
scoped_timer::~scoped_timer() {
    dealloc(m_imp);
}
