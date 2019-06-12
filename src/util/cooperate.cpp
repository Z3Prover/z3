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

#ifndef SINGLE_THREAD

#include "util/cooperate.h"
#include "util/trace.h"
#include "util/debug.h"
#include <atomic>
#include <mutex>
#include <thread>

static std::mutex* s_mux = nullptr;

void initialize_cooperate() {
    s_mux = new std::mutex();
}
void finalize_cooperate() {
    delete s_mux;
}

static std::atomic<std::thread::id> owner_thread;

bool cooperation_ctx::g_cooperate = false;

void cooperation_ctx::checkpoint(char const * task) {
    SASSERT(cooperation_ctx::enabled());

    std::thread::id tid = std::this_thread::get_id();
    if (owner_thread == tid) {
        owner_thread = std::thread::id();
        s_mux->unlock();
    }

    // this critical section is used to force the owner thread to give a chance to
    // another thread to get the lock
    std::this_thread::yield();
    s_mux->lock();
    TRACE("cooperate_detail", tout << task << ", tid: " << tid << "\n";);
    owner_thread = tid;
}

#endif
