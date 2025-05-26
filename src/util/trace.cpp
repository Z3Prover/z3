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
#include "util/trace.h"
#include "util/str_hashtable.h"

#ifndef SINGLE_THREAD
#include <mutex>
#include <thread>

static std::mutex g_verbose_mux;
void verbose_lock() { g_verbose_mux.lock(); }
void verbose_unlock() { g_verbose_mux.unlock(); }

static std::thread::id g_thread_id = std::this_thread::get_id();
static bool g_is_threaded = false;

bool is_threaded() {
    if (g_is_threaded) return true;
    g_is_threaded = std::this_thread::get_id() != g_thread_id;
    return g_is_threaded;
}

#endif

#ifdef _TRACE

std::ofstream tout(".z3-trace"); 

static bool g_enable_all_trace_tags = false;
static str_hashtable* g_enabled_trace_tags = nullptr;

static str_hashtable& get_enabled_trace_tags() {
    if (!g_enabled_trace_tags) {
        g_enabled_trace_tags = alloc(str_hashtable);
    }
    return *g_enabled_trace_tags;
}

void finalize_trace() {
    dealloc(g_enabled_trace_tags);
    g_enabled_trace_tags = nullptr;
}

void enable_trace(const char * tag) {
    get_enabled_trace_tags().insert(tag);
    int count = 0;
    TraceTag tag_str = find_trace_tag_by_string(tag);
    if(tag_str == TraceTag::Count) {
        return;
    }
    const TraceTag* tags = get_tags_by_class(tag_str, count);
    for (int i = 0; i < count; ++i) {
        const char* tag_str = tracetag_to_string(tags[i]);
        if (!get_enabled_trace_tags().contains(tag_str)) {
            get_enabled_trace_tags().insert(tag_str);
        }
    }
}

void enable_all_trace(bool flag) {
    g_enable_all_trace_tags = flag;
}

void disable_trace(const char * tag) {
    get_enabled_trace_tags().erase(tag);
}

bool is_trace_enabled(TraceTag tag) {
    return g_enable_all_trace_tags || 
        (g_enabled_trace_tags && get_enabled_trace_tags().contains(tracetag_to_string(tag)));
}

void close_trace() {
    tout.close();
}

void open_trace() {
    tout.open(".z3-trace");
}

#endif
