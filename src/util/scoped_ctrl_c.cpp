/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    scoped_ctrl_c.cpp

Abstract:

    Scoped control-c handler.

Author:

    Leonardo de Moura (leonardo) 2011-04-27.

Revision History:

--*/
#include<signal.h>
#include "util/scoped_ctrl_c.h"

static scoped_ctrl_c * g_obj = nullptr;

static void on_ctrl_c(int) {
    if (g_obj->m_first) {
        g_obj->m_cancel_eh(CTRL_C_EH_CALLER);
        if (g_obj->m_once) {
            g_obj->m_first = false;
        }
    }
    else {
        sigaction(SIGINT, &g_obj->m_old_action, nullptr);
        raise(SIGINT);
    }
}

scoped_ctrl_c::scoped_ctrl_c(event_handler & eh, bool once, bool enabled):
    m_cancel_eh(eh), 
    m_first(true),
    m_once(once),
    m_enabled(enabled),
    m_old_scoped_ctrl_c(g_obj) {
    if (m_enabled) {
        g_obj = this;
        struct sigaction sa;
        sa.sa_handler = on_ctrl_c;
        sa.sa_flags = SA_ONSTACK;
        sigemptyset(&sa.sa_mask);
        sigaction(SIGINT, &sa, &m_old_action);
    }
}

scoped_ctrl_c::~scoped_ctrl_c() { 
    if (m_enabled) {
        g_obj = m_old_scoped_ctrl_c;
        sigaction(SIGINT, &m_old_action, nullptr);
    }
}
