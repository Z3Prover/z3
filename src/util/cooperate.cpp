/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    cooperate.cpp

Abstract:

    Cooperation support

Author:

    Leonardo (leonardo) 2011-05-17

Notes:

--*/

#include "util/cooperate.h"
#include "util/trace.h"
#include "util/debug.h"
#include <thread>
#include <mutex>

struct cooperation_lock {
    std::recursive_mutex m_lock;
    char const *     m_task;
    std::thread::id   m_owner_thread;
    cooperation_lock() {
        m_task = nullptr;
    }
    ~cooperation_lock() {
    }
};

static cooperation_lock g_lock;

bool cooperation_ctx::g_cooperate = false;

void cooperation_ctx::checkpoint(char const * task) {
    SASSERT(cooperation_ctx::enabled());

    std::thread::id tid = std::this_thread::get_id();
    if (g_lock.m_owner_thread == tid) {
        g_lock.m_owner_thread = std::thread::id();
        g_lock.m_lock.unlock();
    }

    // this critical section is used to force the owner thread to give a chance to
    // another thread to get the lock
    std::this_thread::yield();
    g_lock.m_lock.lock();
    TRACE("cooperate_detail", tout << task << ", tid: " << tid << "\n";);
    CTRACE("cooperate", g_lock.m_task != task, tout << "moving to task: " << task << "\n";);
    g_lock.m_owner_thread = tid;    
}

