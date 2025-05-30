#pragma once

#include <cstring>

enum class TraceTag {
#define X(tag, tag_class, desc) tag,
#include "util/trace_tags.def"
#undef X
    Count
};

// Convert TraceTag to string
inline const char* tracetag_to_string(TraceTag tag) {
    switch (tag) {
#define X(tag, tag_class, desc) case TraceTag::tag: return #tag;
#include "util/trace_tags.def"
#undef X
    default: return "Unknown";
    }
}

// Return description of TraceTag
inline const char* get_trace_tag_doc(TraceTag tag) {
    switch (tag) {
#define X(tag, tag_class, desc) case TraceTag::tag: return desc;
#include "util/trace_tags.def"
#undef X
    default: return "Unknown tag";
    }
}

inline TraceTag get_trace_tag_class(TraceTag tag) {
    switch (tag) {
#define X(tag, tag_class, desc) case TraceTag::tag: return TraceTag::tag_class;
#include "util/trace_tags.def"
#undef X
    default: return TraceTag::Count;
    }
}



// Find TraceTag by string
inline TraceTag find_trace_tag_by_string(const char* tag_str) {
#define X(tag, tag_class, desc) if (strcmp(#tag, tag_str) == 0) return TraceTag::tag;
#include "util/trace_tags.def"
#undef X
    return TraceTag::Count;
}