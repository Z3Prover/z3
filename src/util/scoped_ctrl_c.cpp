/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    scoped_ctrl_c.cpp

Abstract:

    Scoped control-c handler.

Author:

    Leonardo de Moura (leonardo) 2011-04-27.
    Mikulas Patocka 2025-04-05. (rewritten to be thread safe)

Revision History:

--*/
#include <signal.h>
#include <cstring>
#include <mutex>
#include "util/scoped_ctrl_c.h"

#ifdef _WINDOWS
#define USE_SIGNAL
#endif

static std::mutex context_lock;
static std::vector<scoped_ctrl_c *> active_contexts;
#ifdef USE_SIGNAL
static void (*old_handler)(int);
#else
static sigset_t context_old_set;
static struct sigaction old_sigaction;
#endif
static bool signal_handled = false;

static void signal_lock(void) {
#ifdef USE_SIGNAL
    context_lock.lock();
#else
    sigset_t set, old_set;
    sigemptyset(&set);
    sigaddset(&set, SIGINT);
    if (sigprocmask(SIG_BLOCK, &set, &old_set))
        abort();
    context_lock.lock();
    context_old_set = old_set;
#endif
}

static void signal_unlock(void) {
#ifdef USE_SIGNAL
    context_lock.unlock();
#else
    sigset_t old_set = context_old_set;
    context_lock.unlock();
    if (sigprocmask(SIG_SETMASK, &old_set, NULL))
        abort();
#endif
}

static void test_and_unhandle(void) {
    if (!signal_handled)
        return;
    for (auto a : active_contexts) {
        if (a->m_first)
            return;
    }
#ifdef USE_SIGNAL
    signal(SIGINT, old_handler);
#else
    if (sigaction(SIGINT, &old_sigaction, NULL))
        abort();
#endif
    signal_handled = false;
}

static void on_sigint(int) {
    signal_lock();
#ifdef USE_SIGNAL
    if (signal_handled)
        signal(SIGINT, on_sigint);
#endif
    for (auto a : active_contexts) {
        if (a->m_first)
            a->m_cancel_eh(CTRL_C_EH_CALLER);
        if (a->m_once)
            a->m_first = false;
    }
    test_and_unhandle();
    signal_unlock();
}

scoped_ctrl_c::scoped_ctrl_c(event_handler & eh, bool once, bool enabled):
    m_cancel_eh(eh),
    m_first(true),
    m_once(once),
    m_enabled(enabled) {
    if (m_enabled) {
        signal_lock();
        active_contexts.push_back(this);
        if (!signal_handled) {
#ifdef USE_SIGNAL
            old_handler = signal(SIGINT, on_sigint);
#else
            struct sigaction sa;
            memset(&sa, 0, sizeof(struct sigaction));
            sa.sa_handler = on_sigint;
            sigemptyset(&sa.sa_mask);
            sa.sa_flags = SA_RESTART;
            if (sigaction(SIGINT, &sa, &old_sigaction))
                abort();
#endif
            signal_handled = true;
        }
        signal_unlock();
    }
}

scoped_ctrl_c::~scoped_ctrl_c() {
    if (m_enabled) {
        signal_lock();
        for (auto it = active_contexts.begin(); it != active_contexts.end(); it++) {
            if (*it == this) {
                active_contexts.erase(it);
                goto found;
            }
        }
        abort();
found:
        test_and_unhandle();
        signal_unlock();
    }
}
