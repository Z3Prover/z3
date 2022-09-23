/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Logging support

Abstract:

    Utilities for logging.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once

#include <iostream>
#include <sstream>
#include <utility>
#include "util/ref.h"
#include "util/util.h"

template <typename T>
struct show_deref_t {
    T const* ptr;
};

template <typename T>
std::ostream& operator<<(std::ostream& os, show_deref_t<T> s) {
    if (s.ptr)
        return os << *s.ptr;
    else
        return os << "<null>";
}

template <typename T>
show_deref_t<T> show_deref(T* ptr) {
    return show_deref_t<T>{ptr};
}

template <typename Ptr, typename T = typename std::remove_pointer<decltype(std::declval<Ptr>().get())>::type>
show_deref_t<T> show_deref(Ptr const& ptr) {
    return show_deref_t<T>{ptr.get()};
}


template <typename T>
struct repeat {
    unsigned count;
    T const& obj;
    repeat(unsigned count, T const& obj): count(count), obj(obj) {}
};

template <typename T>
std::ostream& operator<<(std::ostream& out, repeat<T> const& r) {
    for (unsigned i = r.count; i-- > 0; ) {
        out << r.obj;
    }
    return out;
}

enum class pad_direction {
    left,
    right,
};

template <typename T>
struct pad {
    pad_direction dir;
    unsigned width;
    T const& obj;
    pad(pad_direction dir, unsigned width, T const& obj): dir(dir), width(width), obj(obj) {}
};

template <typename T>
std::ostream& operator<<(std::ostream& out, pad<T> const& p) {
    std::stringstream tmp;
    tmp << p.obj;
    std::string s = tmp.str();
    unsigned n = (s.length() < p.width) ? (p.width - s.length()) : 0;
    switch (p.dir) {
    case pad_direction::left:
        out << repeat(n, ' ') << s;
        break;
    case pad_direction::right:
        out << s << repeat(n, ' ');
        break;
    }
    return out;
}

/// Fill with spaces to the right:
/// out << rpad(8, "hello")
/// writes "hello   ".
template <typename T>
pad<T> rpad(unsigned width, T const& obj) {
    return pad<T>(pad_direction::right, width, obj);
}

/// Fill with spaces to the left.
template <typename T>
pad<T> lpad(unsigned width, T const& obj) {
    return pad<T>(pad_direction::left, width, obj);
}
