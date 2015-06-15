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

#ifndef _TRACE_H_
#define _TRACE_H_

#ifdef _CYGWIN
#undef max
#undef min
#endif
#ifdef __APPLE__
#undef max
#undef min
#endif
#include<fstream>

#ifdef _TRACE
extern std::ofstream tout; 
#define TRACE_CODE(CODE) { CODE } ((void) 0 )
#else
#define TRACE_CODE(CODE) ((void) 0)
#endif

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

#define TRACE(TAG, CODE) TRACE_CODE(if (is_trace_enabled(TAG)) { tout << "-------- [" << TAG << "] " << __FUNCTION__ << " " << __FILE__ << ":" << __LINE__ << " ---------\n"; CODE tout << "------------------------------------------------\n"; tout.flush(); })

#define STRACE(TAG, CODE) TRACE_CODE(if (is_trace_enabled(TAG)) { CODE tout.flush(); })

#define CTRACE(TAG, COND, CODE) TRACE_CODE(if (is_trace_enabled(TAG) && (COND)) { tout << "-------- [" << TAG << "] " << __FUNCTION__ << " " << __FILE__ << ":" << __LINE__ << " ---------\n"; CODE tout << "------------------------------------------------\n"; tout.flush(); })

#endif /* _TRACE_H_ */

