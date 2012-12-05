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
#include"z3_omp.h"
#include"util.h"
#include"timeout.h"
#include"error_codes.h"

#include"event_handler.h"
#include"scoped_timer.h"

scoped_timer * g_timeout = 0;
void (* g_on_timeout)() = 0;

class g_timeout_eh : public event_handler {
public:
    void operator()() {
        #pragma omp critical (g_timeout_cs) 
        {
            std::cout << "timeout\n";
            if (g_on_timeout)
                g_on_timeout();
            if (g_timeout) 
                delete g_timeout;
            g_timeout = 0;
            throw z3_error(ERR_TIMEOUT);
        }
    }
};

void set_timeout(long ms) {
    if (g_timeout) 
        delete g_timeout;

    g_timeout = new scoped_timer(ms, new g_timeout_eh());
}

void register_on_timeout_proc(void (*proc)()) {
    g_on_timeout = proc;
}
