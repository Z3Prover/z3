/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    trace.cpp

Abstract:

    Trace message support.

Author:

    Leonardo de Moura (leonardo) 2006-09-13.

Revision History:

--*/
#include"trace.h"
#include"str_hashtable.h"

#ifdef _TRACE
std::ofstream tout(".z3-trace"); 
#endif

bool g_enable_all_trace_tags = false;
str_hashtable* g_enabled_trace_tags = 0;

static str_hashtable& get_enabled_trace_tags() {
    if (!g_enabled_trace_tags) {
        g_enabled_trace_tags = alloc(str_hashtable);
    }
    return *g_enabled_trace_tags;
}

void finalize_trace() {
    dealloc(g_enabled_trace_tags);
    g_enabled_trace_tags = 0;
}

void enable_trace(const char * tag) {
    get_enabled_trace_tags().insert(const_cast<char *>(tag));
}

void enable_all_trace(bool flag) {
    g_enable_all_trace_tags = flag;
}

void disable_trace(const char * tag) {
    get_enabled_trace_tags().erase(const_cast<char *>(tag));
}

bool is_trace_enabled(const char * tag) {
    return g_enable_all_trace_tags || 
		(g_enabled_trace_tags && get_enabled_trace_tags().contains(const_cast<char *>(tag)));
}

void close_trace() {
#ifdef _TRACE
    tout.close();
#endif
}

void open_trace() {
#ifdef _TRACE
    tout.open(".z3-trace");
#endif
}
