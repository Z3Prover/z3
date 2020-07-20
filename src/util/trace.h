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

#define TRACE(TAG, CODE) TRACE_CODE(if (is_trace_enabled(TAG)) { tout << "-------- [" << TAG << "] " << __FUNCTION__ << " " << __FILE__ << ":" << __LINE__ << " ---------\n"; CODE tout << "------------------------------------------------\n"; tout.flush(); })

#define STRACE(TAG, CODE) TRACE_CODE(if (is_trace_enabled(TAG)) { CODE tout.flush(); })

#define SCTRACE(TAG, COND, CODE) TRACE_CODE(if (is_trace_enabled(TAG) && (COND)) { CODE tout.flush(); })

#define CTRACE(TAG, COND, CODE) TRACE_CODE(if (is_trace_enabled(TAG) && (COND)) { tout << "-------- [" << TAG << "] " << __FUNCTION__ << " " << __FILE__ << ":" << __LINE__ << " ---------\n"; CODE tout << "------------------------------------------------\n"; tout.flush(); })
