/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt2_util.cpp

Abstract:

    Goodies for SMT2 standard

Author:

    Leonardo (leonardo) 2012-10-20

Notes:

--*/
#include "util/smt2_util.h"

bool is_smt2_simple_symbol_char(char s) {
    return 
        ('0' <= s && s <= '9') ||
        ('a' <= s && s <= 'z') ||
        ('A' <= s && s <= 'Z') ||
        s == '~' || s == '!' || s == '@' || s == '$' || s == '%' || s == '^' || s == '&' ||
        s == '*' || s == '_' || s == '-' || s == '+' || s == '=' || s == '<' || s == '>' ||
        s == '.' || s == '?' || s == '/';
}

bool is_smt2_quoted_symbol(char const * s) {
    if (s == nullptr)
        return false;
    if ('0' <= s[0] && s[0] <= '9')
        return true;
    unsigned len = static_cast<unsigned>(strlen(s));
    if (len >= 2 && s[0] == '|' && s[len-1] == '|') {
        for (unsigned i = 1; i + 1 < len; i++) {
            if (s[i] == '\\' && i + 2 < len && (s[i+1] == '\\' || s[i+1] == '|')) {
                i++;
            }
            else if (s[i] == '\\' || s[i] == '|') 
                return true;
        }
        return false;
    }
    for (unsigned i = 0; i < len; i++)
        if (!is_smt2_simple_symbol_char(s[i]))
            return true;
    return false;
}

bool is_smt2_quoted_symbol(symbol const & s) {
    if (s.is_numerical())
        return false;
    return is_smt2_quoted_symbol(s.bare_str());
}

std::string mk_smt2_quoted_symbol(symbol const & s) {
    SASSERT(is_smt2_quoted_symbol(s));
    string_buffer<> buffer;
    buffer.append('|');
    char const * str = s.bare_str();
    while (*str) {
        if (*str == '|' || *str == '\\')
            buffer.append('\\');
        buffer.append(*str);
        str++;
    }
    buffer.append('|');
    return std::string(buffer.c_str());
}
