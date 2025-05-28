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

static const TraceTag* get_tag_classes() {
   static bool tag_class_init = false; // ignore thread safety assuming TRACE is already under a lock.
   if (!tag_class_init) {
       // Arrays to track first and last tag in each class
       TraceTag first[static_cast<unsigned>(TraceTag::Count)];
       TraceTag last[static_cast<unsigned>(TraceTag::Count)];
       for (unsigned i = 0; i < static_cast<unsigned>(TraceTag::Count); ++i)
           first[i] = last[i] = TraceTag::Count;

       // Link tags in each class
       for (unsigned i = 0; i < static_cast<unsigned>(TraceTag::Count); ++i) {
           TraceTag tag = static_cast<TraceTag>(i);
           TraceTag tag_class = get_trace_tag_class(tag);
           unsigned cls = static_cast<unsigned>(tag_class);
           if (first[cls] == TraceTag::Count) 
               first[cls] = tag;           
           else 
               tag_classes[static_cast<unsigned>(last[cls])] = tag;           
           last[cls] = tag;
       }
       // Close the circular list for each class
       for (unsigned cls = 0; cls < static_cast<unsigned>(TraceTag::Count); ++cls) 
           if (last[cls] != TraceTag::Count && first[cls] != TraceTag::Count) 
               tag_classes[static_cast<unsigned>(last[cls])] = first[cls];
                 
       tag_class_init = true;
   }
   return tag_classes;
}


void enable_trace(const char * tag) {
    get_enabled_trace_tags().insert(tag);
    
    TraceTag tag_str = find_trace_tag_by_string(tag);
    if (tag_str == TraceTag::Count) 
        return;

    auto tag_class = get_trace_tag_class(tag_str);
    if (tag_class != tag_str)
        return; // Only enable the tag if it is a class tag.
    auto const& next_tag = get_tag_classes();

    auto t = next_tag[static_cast<unsigned>(tag_str)];
    while (t != tag_str) {
        get_enabled_trace_tags().insert(tracetag_to_string(t));
        t = next_tag[static_cast<unsigned>(t)];
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
