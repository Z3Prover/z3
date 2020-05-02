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

#include "util/error_codes.h"
#include "util/warning.h"

#ifdef Z3DEBUG
#define DEBUG_CODE(CODE) { CODE } ((void) 0)
#else
#define DEBUG_CODE(CODE) ((void) 0)
#endif

#ifdef __APPLE__
#include <TargetConditionals.h>
#if !TARGET_OS_OSX
#define NO_Z3_DEBUGGER
#endif
#endif

#ifdef __EMSCRIPTEN__
#define NO_Z3_DEBUGGER
#endif

#ifdef NO_Z3_DEBUGGER
#define INVOKE_DEBUGGER() exit(ERR_INTERNAL_FATAL)
#else
#ifdef _WINDOWS
#define INVOKE_DEBUGGER() __debugbreak()
#else
void invoke_gdb();
#define INVOKE_DEBUGGER() invoke_gdb()
#endif
#endif

void notify_assertion_violation(const char * file_name, int line, const char * condition);
void enable_debug(const char * tag);
void disable_debug(const char * tag);
bool is_debug_enabled(const char * tag);

#define SASSERT(COND) DEBUG_CODE(if (assertions_enabled() && !(COND)) { notify_assertion_violation(__FILE__, __LINE__, #COND); INVOKE_DEBUGGER(); })
#define CASSERT(TAG, COND) DEBUG_CODE(if (assertions_enabled() && is_debug_enabled(TAG) && !(COND)) { notify_assertion_violation(__FILE__, __LINE__, #COND); INVOKE_DEBUGGER(); })
#define XASSERT(COND, EXTRA_CODE) DEBUG_CODE(if (assertions_enabled() && !(COND)) { notify_assertion_violation(__FILE__, __LINE__, #COND); { EXTRA_CODE } INVOKE_DEBUGGER(); })

/**
  We use __builtin_unreachable where possible to suppress control flow compilation warnings, but it should
  not be called because its behavior is undefined, so we do need to exit before "calling" it.
*/
#if (defined(__GNUC__) && ((__GNUC__ * 100 + __GNUC_MINOR__) >= 405)) || __has_builtin(__builtin_unreachable)
# define EXIT_WITH(ERR_CODE) { exit(ERR_CODE); __builtin_unreachable(); } ((void) 0)
#else
# define EXIT_WITH(ERR_CODE) { exit(ERR_CODE); } ((void) 0)
#endif

#ifdef Z3DEBUG
# define UNREACHABLE() DEBUG_CODE(notify_assertion_violation(__FILE__, __LINE__, "UNREACHABLE CODE WAS REACHED."); INVOKE_DEBUGGER();)
#else
# define UNREACHABLE() { notify_assertion_violation(__FILE__, __LINE__, "UNREACHABLE CODE WAS REACHED."); EXIT_WITH(ERR_UNREACHABLE); } ((void) 0)
#endif

#ifdef Z3DEBUG
# define NOT_IMPLEMENTED_YET() DEBUG_CODE(notify_assertion_violation(__FILE__, __LINE__, "NOT IMPLEMENTED YET!"); INVOKE_DEBUGGER();)
#else
# define NOT_IMPLEMENTED_YET() { notify_assertion_violation(__FILE__, __LINE__, "NOT IMPLEMENTED YET!"); EXIT_WITH(ERR_NOT_IMPLEMENTED_YET); } ((void) 0)
#endif

#define VERIFY(_x_) if (!(_x_)) {                               \
        std::cerr << "Failed to verify: " << #_x_ << "\n";      \
        UNREACHABLE();                                          \
    }                                                           

#define ENSURE(_x_)                                         \
    if (!(_x_)) {                                           \
        std::cerr << "Failed to verify: " << #_x_ << "\n";  \
        exit(-1);                                           \
    }


void finalize_debug();
/*
  ADD_FINALIZER('finalize_debug();')
*/

#endif /* DEBUG_H_ */

