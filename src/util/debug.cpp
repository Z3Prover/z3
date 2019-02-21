/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    debug.cpp

Abstract:

    Basic debugging support.

Author:

    Leonardo de Moura (leonardo) 2006-09-11.

Revision History:

--*/
#include<cstdio>
#ifndef _WINDOWS
#include<unistd.h>
#endif
#include<iostream>
#include "util/str_hashtable.h"
#include "util/z3_exception.h"

static volatile bool g_enable_assertions = true;

void enable_assertions(bool f) {
    g_enable_assertions = f;
}

bool assertions_enabled() {
    return g_enable_assertions;
}

void notify_assertion_violation(const char * fileName, int line, const char * condition) {
    std::cerr << "ASSERTION VIOLATION\n";
    std::cerr << "File: " << fileName << "\n";
    std::cerr << "Line: " << line << "\n";
    std::cerr << condition << "\n";
}

static str_hashtable* g_enabled_debug_tags = nullptr;

static void init_debug_table() {
    if (!g_enabled_debug_tags) {
        g_enabled_debug_tags = alloc(str_hashtable);
    }
}

void finalize_debug() {
    dealloc(g_enabled_debug_tags);
    g_enabled_debug_tags = nullptr;
}

void enable_debug(const char * tag) {
    init_debug_table();
    g_enabled_debug_tags->insert(tag);
}

void disable_debug(const char * tag) {
    init_debug_table();
    g_enabled_debug_tags->erase(tag);
}

bool is_debug_enabled(const char * tag) {
    init_debug_table();
    return g_enabled_debug_tags->contains(tag);
}

#if !defined(_WINDOWS) && !defined(NO_Z3_DEBUGGER)
void invoke_gdb() {
    char buffer[1024];
    int * x = nullptr;
    for (;;) {
        std::cerr << "(C)ontinue, (A)bort, (S)top, (T)hrow exception, Invoke (G)DB\n";
        char result;
        bool ok = bool(std::cin >> result);
        if (!ok) exit(ERR_INTERNAL_FATAL); // happens if std::cin is eof or unattached.
        switch(result) {
        case 'C':
        case 'c':
            return;
        case 'A':
        case 'a':
            exit(1);
        case 'S':
        case 's':
            // force seg fault...
            *x = 0;
            return;
        case 't':
        case 'T':
            throw default_exception("assertion violation");
        case 'G':
        case 'g':
            sprintf(buffer, "gdb -nw /proc/%d/exe %d", getpid(), getpid());
            std::cerr << "invoking GDB...\n";
            if (system(buffer) == 0) {
                std::cerr << "continuing the execution...\n";
            }
            else {
                std::cerr << "error starting GDB...\n";
                // forcing seg fault.
                int * x = nullptr;
                *x = 0;
            }
            return;
        default:
            std::cerr << "INVALID COMMAND\n";
        }
    }
}
#endif
