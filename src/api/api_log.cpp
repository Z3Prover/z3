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

std::ostream * g_z3_log = nullptr;
bool g_z3_log_enabled   = false;

extern "C" {
    void Z3_close_log_unsafe(void) {
        if (g_z3_log != nullptr) {
            dealloc(g_z3_log);
            g_z3_log_enabled = false;
            g_z3_log = nullptr;
        }
    }

    Z3_bool Z3_API Z3_open_log(Z3_string filename) {
        Z3_bool res = Z3_TRUE;

#ifdef Z3_LOG_SYNC
        #pragma omp critical (z3_log)
        {
#endif
            if (g_z3_log != nullptr)
                Z3_close_log_unsafe();
            g_z3_log = alloc(std::ofstream, filename);
            if (g_z3_log->bad() || g_z3_log->fail()) {
                dealloc(g_z3_log);
                g_z3_log = nullptr;
                res = Z3_FALSE;
            }
            else {
                *g_z3_log << "V \"" << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER << "." << Z3_REVISION_NUMBER << " " << __DATE__ << "\"\n";
                g_z3_log->flush();
                g_z3_log_enabled = true;
            }
#ifdef Z3_LOG_SYNC
        }
#endif

        return res;
    }

    void Z3_API Z3_append_log(Z3_string str) {
        if (g_z3_log == nullptr)
            return;
#ifdef Z3_LOG_SYNC
        #pragma omp critical (z3_log)
        {
#endif
            if (g_z3_log != nullptr)
                _Z3_append_log(static_cast<char const *>(str));
#ifdef Z3_LOG_SYNC
        }
#endif
    }

    void Z3_API Z3_close_log(void) {
        if (g_z3_log != nullptr) {
#ifdef Z3_LOG_SYNC
            #pragma omp critical (z3_log)
            {
#endif
                Z3_close_log_unsafe();
#ifdef Z3_LOG_SYNC
            }
#endif
        }
    }
}
