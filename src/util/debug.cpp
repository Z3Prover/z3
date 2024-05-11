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
#include "util/mutex.h"
#include "util/str_hashtable.h"
#include "util/z3_exception.h"
#include "util/z3_version.h"

static atomic<bool> g_enable_assertions(true);

void enable_assertions(bool f) {
    g_enable_assertions = f;
}

bool assertions_enabled() {
    return g_enable_assertions;
}

void notify_assertion_violation(const char * fileName, int line, const char * condition) {
    std::cerr << "ASSERTION VIOLATION\n"
                 "File: " << fileName << "\n"
                 "Line: " << line << '\n'
              << condition << '\n';
#ifndef Z3DEBUG
    std::cerr << Z3_FULL_VERSION "\n"
                 "Please file an issue with this message and more detail about how you encountered it at https://github.com/Z3Prover/z3/issues/new\n";
#endif
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

atomic<exit_action> g_default_exit_action(exit_action::exit);

exit_action get_default_exit_action() {
    return g_default_exit_action;
}

void set_default_exit_action(exit_action a) {
    g_default_exit_action = a;
}

void invoke_exit_action(unsigned int code) {
    exit_action a = get_default_exit_action();
    switch (a) {
    case exit_action::exit:
        exit(code);
    case exit_action::throw_exception:
        switch (code) {
            case ERR_INTERNAL_FATAL:
                throw default_exception("internal fatal");
            case ERR_UNREACHABLE:
                throw default_exception("unreachable");
            case ERR_NOT_IMPLEMENTED_YET:
                throw default_exception("not implemented yet");
            default:
                throw default_exception("unknown");
        }
    default:
        exit(code);
    }
}

atomic<debug_action> g_default_debug_action(debug_action::ask);

debug_action get_default_debug_action() {
    return g_default_debug_action;
}

void set_default_debug_action(debug_action a) {
    g_default_debug_action = a;
}

debug_action ask_debug_action(std::istream& in) {
    std::cerr << "(C)ontinue, (A)bort, (S)top, (T)hrow exception, Invoke (G)DB\n";
    char result;
    bool ok = bool(in >> result);
    if (!ok)
        exit(ERR_INTERNAL_FATAL); // happens if std::cin is eof or unattached.
    switch(result) {
    case 'C':
    case 'c':
        return debug_action::cont;
    case 'A':
    case 'a':
        return debug_action::abort;
    case 'S':
    case 's':
        return debug_action::stop;
    case 't':
    case 'T':
        return debug_action::throw_exception;
    case 'G':
    case 'g':
        return debug_action::invoke_debugger;
    default:
        std::cerr << "INVALID COMMAND\n";
        return debug_action::ask;
    }
}

#if !defined(_WINDOWS) && !defined(NO_Z3_DEBUGGER)
void invoke_gdb() {
    std::string buffer;
    int *x = nullptr;
    debug_action a = get_default_debug_action();
    for (;;) {
        switch (a) {
        case debug_action::cont:
            return;
        case debug_action::abort:
            exit(1);
        case debug_action::stop:
            // force seg fault...
            *x = 0;
            return;
        case debug_action::throw_exception:
            throw default_exception("assertion violation");
        case debug_action::invoke_debugger:
            buffer = "gdb -nw /proc/" + std::to_string(getpid()) + "/exe " + std::to_string(getpid());
            std::cerr << "invoking GDB...\n";
            if (system(buffer.c_str()) == 0) {
                std::cerr << "continuing the execution...\n";
            }
            else {
                std::cerr << "error starting GDB...\n";
                // forcing seg fault.
                int *x = nullptr;
                *x = 0;
            }
            return;
        case debug_action::ask:
        default:
            a = ask_debug_action(std::cin);
        }
    }
}
#endif
