/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_log.cpp

Abstract:
    API for creating logs

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include<fstream>
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "util/util.h"
#include "util/z3_version.h"
#include "util/mutex.h"

std::ostream * g_z3_log = nullptr;
std::atomic<bool> g_z3_log_enabled;

#ifdef Z3_LOG_SYNC
static mutex g_log_mux;
#define SCOPED_LOCK() lock_guard lock(g_log_mux)
#else
#define SCOPED_LOCK() {}
#endif

static void Z3_close_log_unsafe(void) {
    if (g_z3_log != nullptr) {
        g_z3_log_enabled = false;
        dealloc(g_z3_log);
        g_z3_log = nullptr;
    }
}

extern "C" {
    bool Z3_API Z3_open_log(Z3_string filename) {
        bool res = true;

        SCOPED_LOCK();
        if (g_z3_log != nullptr)
            Z3_close_log_unsafe();
        g_z3_log = alloc(std::ofstream, filename);
        if (g_z3_log->bad() || g_z3_log->fail()) {
            dealloc(g_z3_log);
            g_z3_log = nullptr;
            res = false;
        }
        else {
            *g_z3_log << "V \"" << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER << "." << Z3_REVISION_NUMBER << "\"\n";
            g_z3_log->flush();
            g_z3_log_enabled = true;
        }

        return res;
    }

    void Z3_API Z3_append_log(Z3_string str) {
        if (g_z3_log == nullptr)
            return;
        SCOPED_LOCK();
        if (g_z3_log != nullptr)
            _Z3_append_log(static_cast<char const *>(str));
    }

    void Z3_API Z3_close_log(void) {
        if (g_z3_log != nullptr) {
            SCOPED_LOCK();
            Z3_close_log_unsafe();
        }
    }
}
