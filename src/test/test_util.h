
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#pragma once

#include "stopwatch.h"

struct test_context {
    bool test_ok;
    unsigned test_fails;
    unsigned fails;
    double test_time;
    stopwatch test_timer;

    test_context() : fails(0) {}
};

#undef min
#undef max

#define TEST_CLASS(context, CLASS_NAME, TYPE, CALL_DESTRUCTORS)     \
    context.test_fails = 0;                                        \
    cout << "" << #CLASS_NAME << "<" << #TYPE << ">" << endl; \
    CLASS_NAME ## _test< TYPE, CALL_DESTRUCTORS >::run_tests(context);       \
    context.fails += context.test_fails;                                   

#define TEST_METHOD(context, METHOD)                       \
    cout << "\t" << #METHOD << "... ";                     \
    context.test_timer.reset();                            \
    context.test_ok = test_ ## METHOD;                     \
    context.test_time = context.test_timer.get_seconds();  \
    if (context.test_ok) {                                 \
        cout << "PASS";                                    \
        if (context.test_time > 0) {                       \
            cout << "(" << context.test_time << "s)";      \
        }                                                  \
        cout << endl;                                      \
    }                                                      \
    else {                                                 \
        cout << "FAIL";                                    \
        if (context.test_time > 0) {                       \
            cout << "(" << context.test_time << "s)";      \
        }                                                  \
        cout << endl;                                      \
        ++ context.test_fails;                             \
    }                                                      \

