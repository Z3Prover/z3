/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    timeout.cpp

Abstract:

    Timeout support

Author:

    Leonardo de Moura (leonardo) 2006-10-02.

Revision History:

    Christoph (cwinter) 2012-02-14: Switch to scoped_timer for timeout support on all platforms.

--*/
#include<iostream>
#include<signal.h>
#include "util/util.h"
#include "util/timeout.h"
#include "util/error_codes.h"

#include "util/event_handler.h"
#include "util/scoped_timer.h"

static scoped_timer * g_timeout = nullptr;
static void (* g_on_timeout)() = nullptr;

static void do_timeout() {
    std::cout << "timeout\n";
    std::cout.flush();
    if (g_on_timeout)
        g_on_timeout();
}

#ifdef SIGXCPU
// React to SIGXCPU (an external CPU limit, e.g. ulimit -t) like a -T timeout.
static void STD_CALL on_sigxcpu(int) {
    signal(SIGXCPU, SIG_DFL);
    do_timeout();
    raise(SIGXCPU);
}
#endif

namespace {
class g_timeout_eh : public event_handler {
public:
    void operator()(event_handler_caller_t caller_id) override {
        m_caller_id = caller_id;
        do_timeout();
        throw z3_error(ERR_TIMEOUT);
    }
};
}

static g_timeout_eh eh;

void set_timeout(long ms) {
    SASSERT(!g_timeout);
    g_timeout = new scoped_timer(ms, &eh);
}

void disable_timeout() {
    delete g_timeout;
}

void register_on_timeout_proc(void (*proc)()) {
    g_on_timeout = proc;
#ifdef SIGXCPU
    // Handle external CPU limits (SIGXCPU) like our own timeouts.
    signal(SIGXCPU, on_sigxcpu);
#endif
}
