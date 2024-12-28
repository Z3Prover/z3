/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_log.cpp

Abstract:
    API for creating logs

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include<fstream>
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/z3_logger.h"
#include "util/util.h"
#include "util/z3_version.h"
#include "util/mutex.h"

static std::ostream * g_z3_log = nullptr;
atomic<bool> g_z3_log_enabled;

#ifdef Z3_LOG_SYNC
static mutex g_log_mux;
#define SCOPED_LOCK() lock_guard lock(g_log_mux)
#else
#define SCOPED_LOCK() {}
#endif

// functions called from api_log_macros.*
void SetR(const void * obj) {
    *g_z3_log << "= " << obj << '\n';
}

void SetO(void * obj, unsigned pos) {
    *g_z3_log << "* " << obj << ' ' << pos << '\n';
}

void SetAO(void * obj, unsigned pos, unsigned idx) {
    *g_z3_log << "@ " << obj << ' ' << pos << ' ' << idx << '\n';
}

namespace {
struct ll_escaped { char const * m_str; };
std::ostream & operator<<(std::ostream & out, ll_escaped const & d) {
    char const * s = d.m_str;
    while (*s) {
        unsigned char c = *s;
        if (('0' <= c && c <= '9') || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') ||
            c == '~' || c == '!' || c == '@' || c == '#' || c == '$' || c == '%' || c == '^' || c == '&' ||
            c == '*' || c == '-' || c == '_' || c == '+' || c == '.' || c == '?' || c == '/' || c == ' ' ||
            c == '<' || c == '>') {
            out << c;
        }
        else {
            unsigned char str[4] = {'0', '0', '0', 0};
            str[2] = '0' + (c % 10);
            c /= 10;
            str[1] = '0' + (c % 10);
            c /= 10;
            str[0] = '0' + c;
            out << '\\' << str;
        }
        s++;
    }
    return out;
}
}

void R()              { *g_z3_log << 'R' << std::endl; }
void P(void * obj)    { *g_z3_log << "P " << obj <<std::endl; }
void I(int64_t i)     { *g_z3_log << "I " << i << std::endl; }
void U(uint64_t u)    { *g_z3_log << "U " << u << std::endl; }
void D(double d)      { *g_z3_log << "D " << d << std::endl; }
void S(Z3_string str) { *g_z3_log << "S \"" << ll_escaped{str} << '"' << std::endl; }
void Sy(Z3_symbol sym) {
    symbol s = symbol::c_api_ext2symbol(sym);
    if (s.is_null()) {
        *g_z3_log << 'N';
    }
    else if (s.is_numerical()) {
        *g_z3_log << "# " << s.get_num();
    }
    else {
        *g_z3_log << "$ |" << ll_escaped{s.str().c_str()} << '|';
    }
    *g_z3_log << std::endl;
}
void Ap(unsigned sz)  { *g_z3_log << "p " << sz << std::endl; }
void Au(unsigned sz)  { *g_z3_log << "u " << sz << std::endl; }
void Ai(unsigned sz)  { *g_z3_log << "i " << sz << std::endl; }
void Asy(unsigned sz) { *g_z3_log << "s " << sz << std::endl; }
void C(unsigned id)   { *g_z3_log << "C " << id << std::endl; }
static void _Z3_append_log(char const * msg) { *g_z3_log << "M \"" << ll_escaped{msg} << '"' << std::endl; }

void ctx_enable_logging() {
    SCOPED_LOCK();
    if (g_z3_log != nullptr)
        g_z3_log_enabled = true;
}

static void Z3_close_log_unsafe(void) {
    if (g_z3_log != nullptr) {
        g_z3_log_enabled = false;
        dealloc(g_z3_log);
        g_z3_log = nullptr;
    }
}

extern "C" {
    bool Z3_API Z3_open_log(Z3_string filename) {
        bool res;

        SCOPED_LOCK();
        Z3_close_log_unsafe();

        g_z3_log = alloc(std::ofstream, filename);
        if (g_z3_log->bad() || g_z3_log->fail()) {
            dealloc(g_z3_log);
            g_z3_log = nullptr;
            res = false;
        }
        else {
            *g_z3_log << "V \"" << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER << "." << Z3_REVISION_NUMBER << '"' << std::endl;
            res = true;
        }

        g_z3_log_enabled = res;
        return res;
    }

    void Z3_API Z3_append_log(Z3_string str) {
        if (!g_z3_log_enabled)
            return;
        SCOPED_LOCK();
        if (g_z3_log != nullptr)
            _Z3_append_log(static_cast<char const *>(str));
    }

    void Z3_API Z3_close_log(void) {
        SCOPED_LOCK();
        Z3_close_log_unsafe();
    }
}
