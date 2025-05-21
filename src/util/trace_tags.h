#pragma once

enum class TraceTag {
#define X(tag, desc) tag,
#include "trace_tags.def"
#undef X
    Count
};

// Convert TraceTag to string
inline const char* to_string(TraceTag tag) {
    switch (tag) {
#define X(tag, desc) case TraceTag::tag: return #tag;
#include "trace_tags.def"
#undef X
    default: return "Unknown";
    }
}

// Return description of TraceTag
inline const char* get_trace_tag_doc(TraceTag tag) {
    switch (tag) {
#define X(tag, desc) case TraceTag::tag: return desc;
#include "trace_tags.def"
#undef X
    default: return "Unknown tag";
    }
}

// Return the number of TraceTags
inline constexpr int trace_tag_count() {
    return static_cast<int>(TraceTag::Count);
}

// Return all TraceTags as an array
inline const TraceTag* all_trace_tags() {
    static TraceTag tags[] = {
#define X(tag, desc) TraceTag::tag,
#include "trace_tags.def"
#undef X
    };
    return tags;
}