/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    trace.h

Abstract:

    Trace message support.

Author:

    Leonardo de Moura (leonardo) 2006-09-13.

Revision History:

--*/

#pragma once

#include<fstream>

#ifdef SINGLE_THREAD
# define is_threaded() false
#else
bool is_threaded();
#endif

#ifdef SINGLE_THREAD
#define LOCK_CODE(CODE) CODE;
#define THREAD_LOCK(CODE) CODE

#else
void verbose_lock();
void verbose_unlock();

#define LOCK_CODE(CODE)                                         \
    {                                                           \
        verbose_lock();                                         \
        CODE;                                                   \
        verbose_unlock();                                       \
    }

#define THREAD_LOCK(CODE) if (is_threaded()) { LOCK_CODE(CODE); } else { CODE; }

#endif



#ifdef _TRACE
extern std::ofstream tout; 
#define TRACE_CODE(CODE) { CODE } ((void) 0 )

void enable_trace(const char * tag);
void enable_all_trace(bool flag);
void disable_trace(const char * tag);
bool is_trace_enabled(const char * tag);
void close_trace();
void open_trace();
void finalize_trace();
/*
  ADD_FINALIZER('finalize_trace();')
*/

#else
#define TRACE_CODE(CODE) ((void) 0)

static inline void enable_trace(const char * tag) {}
static inline void enable_all_trace(bool flag) {}
static inline void disable_trace(const char * tag) {}
static inline bool is_trace_enabled(const char * tag) { return false; }
static inline void close_trace() {}
static inline void open_trace() {}
static inline void finalize_trace() {}
#endif

#define TRACEH(TAG)  tout << "-------- [" << TAG << "] " << __FUNCTION__ << " " << __FILE__ << ":" << __LINE__ << " ---------\n"
#define TRACEEND tout << "------------------------------------------------\n"
#define TRACEBODY(TAG, CODE) TRACEH(TAG); CODE; TRACEEND; tout.flush()
#define STRACEBODY(CODE) CODE; tout.flush()

#define TRACE(TAG, CODE) TRACE_CODE(if (is_trace_enabled(TAG)) { THREAD_LOCK(TRACEBODY(TAG, CODE)); })

#define STRACE(TAG, CODE) TRACE_CODE(if (is_trace_enabled(TAG)) { THREAD_LOCK(STRACEBODY(CODE)); })

#define SCTRACE(TAG, COND, CODE) TRACE_CODE(if (is_trace_enabled(TAG) && (COND)) { THREAD_LOCK(STRACEBODY(CODE)); })

#define CTRACE(TAG, COND, CODE) TRACE_CODE(if (is_trace_enabled(TAG) && (COND)) { THREAD_LOCK(TRACEBODY(TAG, CODE)); })
