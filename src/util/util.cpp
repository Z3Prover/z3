/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    util.cpp

Abstract:

    Useful functions & macros

Author:

    Leonardo de Moura (leonardo) 2006-10-10.

Revision History:

--*/

#include"util.h"

static unsigned g_verbosity_level = 0;

void set_verbosity_level(unsigned lvl) {
    g_verbosity_level = lvl;
}

unsigned get_verbosity_level() {
    return g_verbosity_level;
}

static std::ostream* g_verbose_stream = &std::cerr;

void set_verbose_stream(std::ostream& str) {
    g_verbose_stream = &str;
}

std::ostream& verbose_stream() {
    return *g_verbose_stream;
}


static void (*g_fatal_error_handler)(int) = 0;

void fatal_error(int error_code) {
    if (g_fatal_error_handler) {
        g_fatal_error_handler(error_code);
    }
    else {
        exit(error_code);
    }
}

void set_fatal_error_handler(void (*pfn)(int error_code)) {
    g_fatal_error_handler = pfn;
}

unsigned log2(unsigned v) {
    unsigned r = 0;
    if (v & 0xFFFF0000) {
        v >>= 16;
        r |=  16;
    }
    if (v & 0xFF00) {
        v >>= 8;
        r |=  8;
    }
    if (v & 0xF0) {
        v >>= 4;
        r |=  4;
    }
    if (v & 0xC) {
        v >>= 2;
        r |=  2;
    }
    if (v & 0x2) {
        v >>= 1;
        r |=  1;
    }
    return r;
}

unsigned uint64_log2(uint64 v) {
    unsigned r = 0;
    if (v & 0xFFFFFFFF00000000ull) {
        v >>= 32;
        r |=  32;
    }
    if (v & 0xFFFF0000) {
        v >>= 16;
        r |=  16;
    }
    if (v & 0xFF00) {
        v >>= 8;
        r |=  8;
    }
    if (v & 0xF0) {
        v >>= 4;
        r |=  4;
    }
    if (v & 0xC) {
        v >>= 2;
        r |=  2;
    }
    if (v & 0x2) {
        v >>= 1;
        r |=  1;
    }
    return r;
}

bool product_iterator_next(unsigned n, unsigned const * sz, unsigned * it) {
    for (unsigned i = 0; i < n; i++) {
        it[i]++;
        if (it[i] < sz[i])
            return true;
        it[i] = 0;
    }
    return false;
}

char const * escaped::end() const {
    if (m_str == 0) return 0;
    char const * it = m_str;
    char const * e  = m_str;
    while (*it) {
        if (!m_trim_nl || *it != '\n') {
            ++it;
            e = it;
        }
        else {
            ++it;
        }
    }
    return e;
}

void escaped::display(std::ostream & out) const {
    char const * it = m_str;
    char const * e  = end();
    for (; it != e; ++it) {
        char c = *it;
        if (c == '"') {
            out << '\\';
        }
        out << c;
        if (c == '\n') {
            for (unsigned i = 0; i < m_indent; i++)
                out << " ";
        }
    }
}

