/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    zstring.cpp

Abstract:

    String wrapper for unicode/ascii internal strings as vectors

Author:

    Nikolaj Bjorner (nbjorner) 2021-01-26

--*/
#include "util/gparams.h"
#include "util/zstring.h"

static bool is_hex_digit(char ch, unsigned& d) {
    if ('0' <= ch && ch <= '9') {
        d = ch - '0';
        return true;
    }
    if ('A' <= ch && ch <= 'F') {
        d = 10 + ch - 'A';
        return true;
    }
    if ('a' <= ch && ch <= 'f') {
        d = 10 + ch - 'a';
        return true;
    }
    return false;
}

bool zstring::is_escape_char(char const *& s, unsigned& result) {
    unsigned d;
    if (*s == '\\' && s[1] == 'u' && s[2] == '{' && s[3] != '}') {
        result = 0;
        for (unsigned i = 0; i < 6; ++i) {
            if (is_hex_digit(*(s+3+i), d)) {
                result = 16*result + d;
            }
            else if (*(s+3+i) == '}') {
                if (result > 255 && !uses_unicode())
                    throw default_exception("unicode characters outside of byte range are not supported");
                if (result > unicode_max_char()) 
                    throw default_exception("unicode characters outside of byte range are not supported");
                s += 4 + i;
                return true;                
            }
            else {
                break;
            }
        }
        return false;
    }
    unsigned d1, d2, d3, d4;
    if (*s == '\\' && s[1] == 'u' && 
        is_hex_digit(s[2], d1) &&
        is_hex_digit(s[3], d2) &&
        is_hex_digit(s[4], d3) &&
        is_hex_digit(s[5], d4)) {
        result = d1;
        result = 16*result + d2;
        result = 16*result + d3;
        result = 16*result + d4;
        if (result > unicode_max_char()) 
            throw default_exception("unicode characters outside of byte range are not supported");
        s += 6;
        return true;
    }
    return false;
}

zstring::zstring(char const* s) {
    while (*s) {
        unsigned ch = 0;
        if (is_escape_char(s, ch)) {
            m_buffer.push_back(ch);
        }
        else {
            m_buffer.push_back(*s);
            ++s;
        }
    }
    SASSERT(well_formed());
}


bool zstring::uses_unicode() const {
    return gparams::get_value("unicode") != "false";
}

bool zstring::well_formed() const {
    for (unsigned ch : m_buffer) {
        if (ch > unicode_max_char()) {
            IF_VERBOSE(0, verbose_stream() << "large character: " << ch << "\n";);
            return false;
        }
    }
    return true;
}

zstring::zstring(unsigned ch) {
    m_buffer.push_back(ch);
}

zstring zstring::reverse() const {
    zstring result;
    for (unsigned i = length(); i-- > 0; ) {
        result.m_buffer.push_back(m_buffer[i]);
    }
    return result;
}

zstring zstring::replace(zstring const& src, zstring const& dst) const {
    zstring result;
    if (length() < src.length()) {
        return zstring(*this);
    }
    if (src.length() == 0) {
        return dst + zstring(*this);
    }
    bool found = false;
    for (unsigned i = 0; i < length(); ++i) {
        bool eq = !found && i + src.length() <= length();
        for (unsigned j = 0; eq && j < src.length(); ++j) {
            eq = m_buffer[i+j] == src[j];
        }
        if (eq) {
            result.m_buffer.append(dst.m_buffer);
            found = true;
            i += src.length() - 1;
        }
        else {
            result.m_buffer.push_back(m_buffer[i]);
        }
    }
    return result;
}

std::string zstring::encode() const {
    std::ostringstream strm;
    char buffer[100];
    unsigned offset = 0;
#define _flush() if (offset > 0) { buffer[offset] = 0; strm << buffer; offset = 0; }
    for (unsigned i = 0; i < m_buffer.size(); ++i) {
        unsigned ch = m_buffer[i];
        if (ch < 32 || ch >= 128) {
            _flush();
            strm << "\\u{" << std::hex << ch << std::dec << "}";
        }
        else {
            if (offset == 99)  
                _flush();
            buffer[offset++] = (char)ch;
        }
    }
    _flush();
    return strm.str();
}

bool zstring::suffixof(zstring const& other) const {
    if (length() > other.length()) return false;
    bool suffix = true;
    for (unsigned i = 0; suffix && i < length(); ++i) {
        suffix = m_buffer[length()-i-1] == other[other.length()-i-1];
    }
    return suffix;
}

bool zstring::prefixof(zstring const& other) const {
    if (length() > other.length()) return false;
    bool prefix = true;
    for (unsigned i = 0; prefix && i < length(); ++i) {
        prefix = m_buffer[i] == other[i];
    }
    return prefix;
}

bool zstring::contains(zstring const& other) const {
    if (other.length() > length()) return false;
    unsigned last = length() - other.length();
    bool cont = false;
    for (unsigned i = 0; !cont && i <= last; ++i) {
        cont = true;
        for (unsigned j = 0; cont && j < other.length(); ++j) {
            cont = other[j] == m_buffer[j+i];
        }
    }
    return cont;
}

int zstring::indexofu(zstring const& other, unsigned offset) const {
    if (offset <= length() && other.length() == 0) return offset;
    if (offset == length()) return -1;
    if (offset > other.length() + offset) return -1;
    if (other.length() + offset > length()) return -1;
    unsigned last = length() - other.length();
    for (unsigned i = offset; i <= last; ++i) {
        bool prefix = true;
        for (unsigned j = 0; prefix && j < other.length(); ++j) {
            prefix = m_buffer[i + j] == other[j];
        }
        if (prefix) {
            return static_cast<int>(i);
        }
    }
    return -1;
}

int zstring::last_indexof(zstring const& other) const {
    if (other.length() == 0) return length();
    if (other.length() > length()) return -1;
    for (unsigned last = length() - other.length(); last-- > 0; ) {
        bool suffix = true;
        for (unsigned j = 0; suffix && j < other.length(); ++j) {
            suffix = m_buffer[last + j] == other[j];
        }
        if (suffix) {
            return static_cast<int>(last);
        }
    }
    return -1;
}

zstring zstring::extract(unsigned offset, unsigned len) const {
    zstring result;
    if (offset + len < offset) return result;
    int last = std::min(offset+len, length());
    for (int i = offset; i < last; ++i) {
        result.m_buffer.push_back(m_buffer[i]);
    }
    return result;
}

unsigned zstring::hash() const {
    return unsigned_ptr_hash(m_buffer.data(), m_buffer.size(), 23);
}

zstring zstring::operator+(zstring const& other) const {
    zstring result(*this);
    result.m_buffer.append(other.m_buffer);
    return result;
}


bool zstring::operator==(const zstring& other) const {
    // two strings are equal iff they have the same length and characters
    if (length() != other.length()) {
        return false;
    }
    for (unsigned i = 0; i < length(); ++i) {
        if (m_buffer[i] != other[i]) {
            return false;
        }
    }
    return true;
}

bool zstring::operator!=(const zstring& other) const {
    return !(*this == other);
}

std::ostream& operator<<(std::ostream &os, const zstring &str) {
    return os << str.encode();
}

bool operator<(const zstring& lhs, const zstring& rhs) {
    // This has the same semantics as strcmp()
    unsigned len = lhs.length();
    if (rhs.length() < len) {
        len = rhs.length();
    }
    for (unsigned i = 0; i < len; ++i) {
        unsigned Li = lhs[i];
        unsigned Ri = rhs[i];
        if (Li != Ri)
            return Li < Ri;
    }
    // at this point, all compared characters are equal,
    // so decide based on the relative lengths
    return lhs.length() < rhs.length();
}
