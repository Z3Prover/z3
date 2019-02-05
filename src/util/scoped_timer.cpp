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
    event_handler *  m_eh;
    std::thread      m_thread;
    std::timed_mutex m_mutex;
    unsigned         m_ms;

    static void* thread_func(imp * st) {
        auto end = std::chrono::steady_clock::now() + std::chrono::milliseconds(st->m_ms);

        while (!st->m_mutex.try_lock_until(end)) {
          if (std::chrono::steady_clock::now() > end) {
            st->m_eh->operator()(TIMEOUT_EH_CALLER);
            return nullptr;
          }
        }

        st->m_mutex.unlock();
        return nullptr;
    }

    imp(unsigned ms, event_handler * eh):
        m_eh(eh), m_ms(ms) {
        m_mutex.lock();
        m_thread = std::thread(thread_func, this);
    }

    ~imp() {
        m_mutex.unlock();
        while (!m_thread.joinable()) {
            std::this_thread::yield();
        }
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
    if (m_imp)
        dealloc(m_imp);
}
