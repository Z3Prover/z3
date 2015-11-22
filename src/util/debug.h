/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    debug.h

Abstract:

    Basic debugging support.

Author:

    Leonardo de Moura (leonardo) 2006-09-11.

Revision History:

--*/
#ifndef DEBUG_H_
#define DEBUG_H_

#include <stdlib.h>

void enable_assertions(bool f);
bool assertions_enabled();

#if 0
#define _CRTDBG_MAP_ALLOC
#include<stdlib.h>
#include<new>
#include<crtdbg.h>
#endif

#ifndef __has_builtin
# define __has_builtin(x) 0
#endif

#include"error_codes.h"
#include"warning.h"

#ifdef Z3DEBUG
#define DEBUG_CODE(CODE) { CODE } ((void) 0)
#else
#define DEBUG_CODE(CODE) ((void) 0)
#endif

#ifdef _WINDOWS
#define INVOKE_DEBUGGER() __debugbreak()
#else
void invoke_gdb();
#define INVOKE_DEBUGGER() invoke_gdb()
#endif

void notify_assertion_violation(const char * file_name, int line, const char * condition);
void enable_debug(const char * tag);
void disable_debug(const char * tag);
bool is_debug_enabled(const char * tag);

#define SASSERT(COND) DEBUG_CODE(if (assertions_enabled() && !(COND)) { notify_assertion_violation(__FILE__, __LINE__, #COND); INVOKE_DEBUGGER(); })
#define CASSERT(TAG, COND) DEBUG_CODE(if (assertions_enabled() && is_debug_enabled(TAG) && !(COND)) { notify_assertion_violation(__FILE__, __LINE__, #COND); INVOKE_DEBUGGER(); })
#define XASSERT(COND, EXTRA_CODE) DEBUG_CODE(if (assertions_enabled() && !(COND)) { notify_assertion_violation(__FILE__, __LINE__, #COND); { EXTRA_CODE } INVOKE_DEBUGGER(); })

#ifdef Z3DEBUG
# define UNREACHABLE() DEBUG_CODE(notify_assertion_violation(__FILE__, __LINE__, "UNREACHABLE CODE WAS REACHED."); INVOKE_DEBUGGER();)
#else
#if (defined(__GNUC__) && ((__GNUC__ * 100 + __GNUC_MINOR__) >= 405)) || __has_builtin(__builtin_unreachable)
// only available in gcc >= 4.5 and in newer versions of clang
# define UNREACHABLE() __builtin_unreachable()
#elif defined(_MSC_VER)
# define UNREACHABLE() __assume(0)
#else
#define UNREACHABLE() DEBUG_CODE(notify_assertion_violation(__FILE__, __LINE__, "UNREACHABLE CODE WAS REACHED."); INVOKE_DEBUGGER();)
#endif
#endif

#define NOT_IMPLEMENTED_YET() { std::cerr << "NOT IMPLEMENTED YET!\n"; UNREACHABLE(); exit(ERR_NOT_IMPLEMENTED_YET); } ((void) 0)

#ifdef Z3DEBUG
#define VERIFY(_x_) if (!(_x_)) {                               \
        std::cerr << "Failed to verify: " << #_x_ << "\n";      \
        UNREACHABLE();                                          \
    }                                                           
#else
#define VERIFY(_x_) (void)(_x_)
#endif

#define ENSURE(_x_)                                         \
    if (!(_x_)) {                                           \
        std::cerr << "Failed to verify: " << #_x_ << "\n";  \
        exit(-1);                                           \
    }

#define MAKE_NAME2(LINE) zofty_ ## LINE 
#define MAKE_NAME(LINE) MAKE_NAME2(LINE)
#define DBG_UNIQUE_NAME MAKE_NAME(__LINE__)
#ifdef __GNUC__
#define COMPILE_TIME_ASSERT(expr) extern __attribute__((unused)) char DBG_UNIQUE_NAME[expr]
#else
#define COMPILE_TIME_ASSERT(expr) extern char DBG_UNIQUE_NAME[expr]
#endif

void finalize_debug();
/*
  ADD_FINALIZER('finalize_debug();')
*/

#endif /* DEBUG_H_ */

