#pragma once

#include <cstring>

enum class TraceTag {
#define X(tag, tag_class, desc) tag,
#include "trace_tags.def"
#undef X
    Count
};

// Convert TraceTag to string
inline const char* tracetag_to_string(TraceTag tag) {
    switch (tag) {
#define X(tag, tag_class, desc) case TraceTag::tag: return #tag;
#include "trace_tags.def"
#undef X
    default: return "Unknown";
    }
}

// Return description of TraceTag
inline const char* get_trace_tag_doc(TraceTag tag) {
    switch (tag) {
#define X(tag, tag_class, desc) case TraceTag::tag: return desc;
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
#define X(tag, tag_class, desc) TraceTag::tag,
#include "trace_tags.def"
#undef X
    };
    return tags;
}

// Helper function to count tags in a class
inline constexpr int count_tags_in_class(TraceTag cls) {
    int count = 0;
    #define X(tag, tag_class, desc) if (TraceTag::tag_class == cls) count++;
    #include "trace_tags.def"
    #undef X
    return count;
}

// TODO(#7663): Implement tag_class activation of all associated tags
// TODO: Need to consider implementation approach and memory management
// Return all tags that belong to the given class
inline const TraceTag* get_tags_by_class(TraceTag cls, int& count) {
    count = count_tags_in_class(cls);
    static TraceTag* class_tags = nullptr;
    if (class_tags) delete[] class_tags;
    
    class_tags = new TraceTag[count];
    int idx = 0;
    
    #define X(tag, tag_class, desc) \
        if (TraceTag::tag_class == cls) { \
            class_tags[idx++] = TraceTag::tag; \
        }
    #include "trace_tags.def"
    #undef X
    
    return class_tags;
}

// Find TraceTag by string
inline TraceTag find_trace_tag_by_string(const char* tag_str) {
    #define X(tag, tag_class, desc) if (strncmp(#tag, tag_str, strlen(#tag)) == 0) return TraceTag::tag;
    #include "trace_tags.def"
    #undef X
    return TraceTag::Count;
}