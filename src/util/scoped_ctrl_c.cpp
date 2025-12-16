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
#include <mutex>
#include <vector>
#include <signal.h>
#include "util/scoped_ctrl_c.h"
#include "util/gparams.h"

static std::vector<scoped_ctrl_c*> g_list;
static std::mutex g_list_mutex;
static void (*g_old_handler)(int);

static void on_ctrl_c(int) {
    std::lock_guard lock(g_list_mutex);
    for (auto handler : g_list) {
        if (handler->m_enabled) {
            handler->m_cancel_eh(CTRL_C_EH_CALLER);
        }
    }
    signal(SIGINT, g_old_handler);
}

scoped_ctrl_c::scoped_ctrl_c(event_handler & eh, bool enabled):
    m_cancel_eh(eh),
    m_enabled(enabled) {
    if (enabled && gparams::get_value("ctrl_c") == "false")
        m_enabled = false;

    if (m_enabled) {
        std::lock_guard lock(g_list_mutex);
        if (g_list.empty()) {
            g_old_handler = signal(SIGINT, on_ctrl_c);
        }
        g_list.push_back(this);
    }
}

scoped_ctrl_c::~scoped_ctrl_c() { 
    if (m_enabled) {
        std::lock_guard lock(g_list_mutex);
        auto it = std::find(g_list.begin(), g_list.end(), this);
        SASSERT(it != g_list.end());
        g_list.erase(it);
        if (g_list.empty()) {
            signal(SIGINT, g_old_handler);
        }
    }
}
