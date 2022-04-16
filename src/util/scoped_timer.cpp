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
#include "util/mutex.h"
#include "util/util.h"
#include <atomic>
#include <chrono>
#include <climits>
#include <condition_variable>
#include <mutex>
#include <thread>
#include <vector>
#ifndef _WINDOWS
#include <pthread.h>
#endif

enum scoped_timer_work_state { IDLE = 0, WORKING = 1, EXITING = 2 };

struct scoped_timer_state {
    std::thread m_thread;
    std::timed_mutex m_mutex;
    event_handler * eh;
    unsigned ms;
    std::atomic<scoped_timer_work_state> work;
    std::condition_variable_any cv;
};

static std::vector<scoped_timer_state*> available_workers;
static std::mutex workers;
static atomic<unsigned> num_workers(0);

static void thread_func(scoped_timer_state *s) {
    workers.lock();
    while (true) {
        s->cv.wait(workers, [=]{ return s->work > IDLE; });
        workers.unlock();

        // exiting..
        if (s->work == EXITING)
            return;

        auto end = std::chrono::steady_clock::now() + std::chrono::milliseconds(s->ms);

        while (!s->m_mutex.try_lock_until(end)) {
            if (std::chrono::steady_clock::now() >= end) {
                s->eh->operator()(TIMEOUT_EH_CALLER);
                goto next;
            }
        }

        s->m_mutex.unlock();

    next:
        s->work = IDLE;
        workers.lock();
    }
}


scoped_timer::scoped_timer(unsigned ms, event_handler * eh) {
    if (ms == 0 || ms == UINT_MAX)
        return;

    workers.lock();
    bool new_worker = false;
    if (available_workers.empty()) {
        workers.unlock();
        s = new scoped_timer_state;
        new_worker = true;
        ++num_workers;
    }
    else {
        s = available_workers.back();
        available_workers.pop_back();
        workers.unlock();
    }
    s->ms = ms;
    s->eh = eh;
    s->m_mutex.lock();
    s->work = WORKING;
    if (new_worker) {
        s->m_thread = std::thread(thread_func, s);
    }
    else {
        s->cv.notify_one();
    }
}
    
scoped_timer::~scoped_timer() {
    if (!s)
        return;

    s->m_mutex.unlock();
    while (s->work == WORKING)
        std::this_thread::yield();
    workers.lock();
    available_workers.push_back(s);
    workers.unlock();
}

void scoped_timer::initialize() {
#ifndef _WINDOWS
    static bool pthread_atfork_set = false;
    if (!pthread_atfork_set) {
        pthread_atfork(finalize, nullptr, nullptr);
        pthread_atfork_set = true;
    }
#endif
}

void scoped_timer::finalize() {
    unsigned deleted = 0;
    while (deleted < num_workers) {
        workers.lock();
        for (auto w : available_workers) {
            w->work = EXITING;
            w->cv.notify_one();
        }
        decltype(available_workers) cleanup_workers;
        std::swap(available_workers, cleanup_workers);
        workers.unlock();

        for (auto w : cleanup_workers) {
            ++deleted;
            w->m_thread.join();
            delete w;
        }
    }
    num_workers = 0;
    available_workers.clear();
}
