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
#include "util/vector.h"
#include <atomic>
#include <chrono>
#include <climits>
#include <condition_variable>
#include <mutex>
#include <thread>
#include <vector>

struct state {
    std::thread * m_thread { nullptr };
    std::timed_mutex m_mutex;
    unsigned ms { 0 };
    event_handler * eh { nullptr };
    bool working { false };
    std::condition_variable_any cv;
};

static ptr_vector<state> available_workers;
static ptr_vector<state> all_workers;
static std::mutex workers;
static std::atomic<int> thread_count;
static std::atomic<bool> terminating;

static void thread_func(state *s) {
    workers.lock();
    while (true) {
        s->cv.wait(workers, [=]{ return terminating || s->working; });
        workers.unlock();

        if (terminating) {
            thread_count--;
            return;
        }

        auto end = std::chrono::steady_clock::now() + std::chrono::milliseconds(s->ms);

        while (!s->m_mutex.try_lock_until(end)) {
            if (std::chrono::steady_clock::now() >= end) {
                s->eh->operator()(TIMEOUT_EH_CALLER);
                goto next;
            }
        }

        s->m_mutex.unlock();

    next:
        s->working = false;
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
        } 
        else {
            s = available_workers.back();
            available_workers.pop_back();
            workers.unlock();
        }
        s->ms = ms;
        s->eh = eh;
        s->m_mutex.lock();
        s->working = true;
        if (!s->m_thread) {
            s->m_thread = new std::thread(thread_func, s);
            s->m_thread->detach();
            workers.lock();
            all_workers.push_back(s);
            workers.unlock();
            thread_count++;
        } 
        else {
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

void finalize_scoped_timer() {
    terminating = true;
    // the outer loop is because a thread that is not blocked on its
    // condition variable will miss our notification. we do not have
    // the option of leaking these threads since they will end up
    // deadlocking finalization.
    while (thread_count > 0) {
        for (auto t : all_workers)
            t->cv.notify_one();
        std::this_thread::yield();
    }
    available_workers.clear();
    all_workers.clear();
    terminating = false;
}
