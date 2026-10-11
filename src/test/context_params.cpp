/*++
Module Name:

    context_params.cpp

Abstract:

    Regression tests for unsigned context parameter parsing.

--*/
#include "params/context_params.h"
#include "util/debug.h"
#include "util/z3_exception.h"
#include <climits>
#include <cstring>
#include <string>

void tst_context_params() {
    for (char const* name : {"timeout", "rlimit"}) {
        context_params params;
        auto value = [&]() {
            return strcmp(name, "timeout") == 0 ? params.m_timeout : params.rlimit();
        };

        // Values above INT_MAX must survive even when long is only 32 bits.
        for (unsigned limit : {0u, static_cast<unsigned>(INT_MAX),
                               static_cast<unsigned>(INT_MAX) + 1, UINT_MAX}) {
            params.set(name, std::to_string(limit).c_str());
            ENSURE(value() == limit);
        }

        std::string overflow = std::to_string(static_cast<unsigned long long>(UINT_MAX) + 1);
        for (char const* invalid : {"", "abc", "12x", "-1", "+1", " 1", "1 ", "1.5",
                                    overflow.c_str(), "18446744073709551616"}) {
            params.set(name, "42");
            bool rejected = false;
            try {
                params.set(name, invalid);
            }
            catch (default_exception const&) {
                rejected = true;
            }
            ENSURE(rejected);
            ENSURE(value() == 42);
        }
    }
}
