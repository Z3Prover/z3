/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    z3_logger.h

Abstract:

    Goodies for log generation

Author:

    Leonardo de Moura (leonardo) 2011-09-22

Notes:
    
--*/
#include<iostream>
#include "util/symbol.h"
struct ll_escaped { char const * m_str; ll_escaped(char const * str):m_str(str) {} };
static std::ostream & operator<<(std::ostream & out, ll_escaped const & d);

static void __declspec(noinline) R()  { *g_z3_log << "R\n"; g_z3_log->flush(); }
static void __declspec(noinline) P(void * obj)  { *g_z3_log << "P " << obj << "\n"; g_z3_log->flush(); }
static void __declspec(noinline) I(int64_t i)   { *g_z3_log << "I " << i << "\n"; g_z3_log->flush(); }
static void __declspec(noinline) U(uint64_t u)   { *g_z3_log << "U " << u << "\n"; g_z3_log->flush(); }
static void __declspec(noinline) D(double d)   { *g_z3_log << "D " << d << "\n"; g_z3_log->flush(); }
static void __declspec(noinline) S(Z3_string str) { *g_z3_log << "S \"" << ll_escaped(str) << "\"\n"; g_z3_log->flush(); }
static void __declspec(noinline) Sy(Z3_symbol sym) { 
    symbol s = symbol::mk_symbol_from_c_ptr(reinterpret_cast<void *>(sym));
    if (s == symbol::null) {
        *g_z3_log << "N\n";
    }
    else if (s.is_numerical()) {
        *g_z3_log << "# " << s.get_num() << "\n";
    }
    else {
        *g_z3_log << "$ |" << ll_escaped(s.bare_str()) << "|\n";
    }
    g_z3_log->flush();
}
static void __declspec(noinline) Ap(unsigned sz) { *g_z3_log << "p " << sz << "\n"; g_z3_log->flush(); }
static void __declspec(noinline) Au(unsigned sz) { *g_z3_log << "u " << sz << "\n"; g_z3_log->flush(); }
static void __declspec(noinline) Asy(unsigned sz) { *g_z3_log << "s " << sz << "\n"; g_z3_log->flush(); }
static void __declspec(noinline) C(unsigned id)   { *g_z3_log << "C " << id << "\n"; g_z3_log->flush(); }
void __declspec(noinline) _Z3_append_log(char const * msg) { *g_z3_log << "M \"" << ll_escaped(msg) << "\"\n"; g_z3_log->flush(); }

static std::ostream & operator<<(std::ostream & out, ll_escaped const & d) {
    char const * s = d.m_str;
    while (*s) {
        char c = *s;
        if (('0' <= c && c <= '9') || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') ||
            c == '~' || c == '!' || c == '@' || c == '#' || c == '$' || c == '%' || c == '^' || c == '&' ||
            c == '*' || c == '-' || c == '_' || c == '+' || c == '.' || c == '?' || c == '/' || c == ' ' ||
            c == '<' || c == '>') {
            out << c;
        }
        else {
            char str[4] = {'0', '0', '0', 0};
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
