/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    scoped_timer.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2011-04-26.

Revision History:

    Nuno Lopes (nlopes) 2019-02-04  - use C++11 goodies

--*/

#include "util/scoped_timer.h"
#include "util/util.h"
#include <chrono>
#include <climits>
#include <condition_variable>
#include <mutex>
#include <thread>
#include <vector>

struct state {
    std::thread * m_thread = nullptr;
    std::timed_mutex m_mutex;
    unsigned ms;
    event_handler * eh;
    int work = 0;
    std::condition_variable_any cv;
};

/*
 * NOTE: this implementation deliberately leaks threads when Z3
 * exits. this is preferable to deallocating on exit, because
 * destructing threads blocked on condition variables leads to
 * deadlock.
 */
static std::vector<state *> available_workers;
static std::mutex workers;

static void thread_func(state *s) {
    workers.lock();
    while (true) {
        s->cv.wait(workers, [=]{ return s->work > 0; });
        workers.unlock();

        auto end = std::chrono::steady_clock::now() + std::chrono::milliseconds(s->ms);

        while (!s->m_mutex.try_lock_until(end)) {
            if (std::chrono::steady_clock::now() >= end) {
                s->eh->operator()(TIMEOUT_EH_CALLER);
                goto next;
            }
        }

        s->m_mutex.unlock();

    next:
        s->work = 0;
        workers.lock();
        available_workers.push_back(s);
    }
}

struct scoped_timer::imp {
private:
    state *s;

public:
    imp(unsigned ms, event_handler * eh) {
        workers.lock();
        if (available_workers.empty()) {
            workers.unlock();
            s = new state;
        } else {
            s = available_workers.back();
            available_workers.pop_back();
            workers.unlock();
        }
        s->ms = ms;
        s->eh = eh;
        s->m_mutex.lock();
        s->work = 1;
        if (!s->m_thread) {
            s->m_thread = new std::thread(thread_func, s);
            s->m_thread->detach();
        } else {
            s->cv.notify_one();
        }
    }

    ~imp() {
        s->m_mutex.unlock();
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
