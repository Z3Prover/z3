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

inline unsigned tag2u(TraceTag tag) { return static_cast<unsigned>(tag); }

struct tag_info {
    bool is_enabled;
    bool is_class;
    TraceTag next;
};

static tag_info s_tag_infos[] = {
    #define X(tag_class, tag, desc) { false, false, TraceTag::tag },
#include "util/trace_tags.def"
#undef  X
};


bool tag_enabled(TraceTag tag) {
    return tag < TraceTag::Count && s_tag_infos[tag2u(tag)].is_enabled;
}

static void enable_tag(TraceTag tag) {
    if (tag < TraceTag::Count)
        s_tag_infos[tag2u(tag)].is_enabled = true;
}

static void disable_tag(TraceTag tag) {
    if (tag < TraceTag::Count)
        s_tag_infos[tag2u(tag)].is_enabled = false;
}

static const tag_info* get_tag_infos() {
   static bool tag_class_init = false; // ignore thread safety assuming TRACE is already under a lock.
   if (!tag_class_init) {
       // Arrays to track first and last tag in each class
       TraceTag first[static_cast<unsigned>(TraceTag::Count)];
       TraceTag last[static_cast<unsigned>(TraceTag::Count)];
       for (unsigned i = 0; i < tag2u(TraceTag::Count); ++i)
           first[i] = last[i] = TraceTag::Count;

       // Link tags in each class
       for (unsigned i = 0; i < tag2u(TraceTag::Count); ++i) {
           TraceTag tag = static_cast<TraceTag>(i);
           TraceTag tag_class = get_trace_tag_class(tag);
           s_tag_infos[tag2u(tag_class)].is_class = true;
           unsigned cls = tag2u(tag_class);
           if (first[cls] == TraceTag::Count) 
               first[cls] = tag;           
           else 
               s_tag_infos[tag2u(last[cls])].next = tag;           
           last[cls] = tag;
       }
       // Close the circular list for each class
       for (unsigned cls = 0; cls < tag2u(TraceTag::Count); ++cls) 
           if (last[cls] != TraceTag::Count && first[cls] != TraceTag::Count) 
               s_tag_infos[tag2u(last[cls])].next = first[cls];
                 
       tag_class_init = true;
   }
   return s_tag_infos;
}


static size_t levenshtein_distance(std::string_view s, std::string_view t) {
    size_t len_s = s.length();
    size_t len_t = t.length();
    std::vector<size_t> prev(len_t + 1), curr(len_t + 1);

    for (size_t j = 0; j <= len_t; ++j)
        prev[j] = j;

    for (size_t i = 1; i <= len_s; ++i) {
        curr[0] = i;
        for (size_t j = 1; j <= len_t; ++j) {
            size_t cost = s[i - 1] == t[j - 1] ? 0 : 1;
            curr[j] = std::min({ prev[j] + 1, curr[j - 1] + 1, prev[j - 1] + cost });
        }
        prev.swap(curr);
    }
    return prev[len_t];
}

static bool has_overlap(std::string_view s, std::string_view t, size_t k) {
    // Consider overlap if Levenshtein distance is <= k
    return levenshtein_distance(s, t) <= k;
}

void enable_trace(std::string_view tag_str) {
    std::string tag_string(tag_str); // Convert to std::string for null-termination
    TraceTag tag = find_trace_tag_by_string(tag_string.c_str());
    size_t k = tag_str.length();

  
    if (tag == TraceTag::Count) {
        warning_msg("trace tag '%s' does not exist", tag_string.c_str());
#define X(tag_class, tag, desc) k = std::min(levenshtein_distance(#tag, tag_str), k);
#include "util/trace_tags.def"
#undef X
#define X(tag_class, tag, desc) if (has_overlap(#tag, tag_str, k + 2)) warning_msg("did you mean '%s'?", #tag);
#include "util/trace_tags.def"
#undef X           
        return;
    }

    enable_tag(tag);
  
    auto const& tag_infos = get_tag_infos();
    if (!tag_infos[tag2u(tag)].is_class)
        return;

    auto t = tag_infos[tag2u(tag)].next;
    while (t != tag) {
        enable_tag(t);
        t = tag_infos[tag2u(t)].next;
    }
}

void enable_all_trace(bool flag) {
    g_enable_all_trace_tags = flag;
}

void disable_trace(std::string_view tag) {
    std::string tag_string(tag); // Convert to std::string for null-termination
    TraceTag tag_str = find_trace_tag_by_string(tag_string.c_str());
    disable_tag(tag_str);
}

bool is_trace_enabled(TraceTag tag) {
    return g_enable_all_trace_tags || tag_enabled(tag);
}

void close_trace() {
    tout.close();
}

void open_trace() {
    tout.open(".z3-trace");
}

#endif
