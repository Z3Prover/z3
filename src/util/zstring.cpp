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

static bool is_octal_digit(char ch, unsigned& d) {
    if ('0' <= ch && ch <= '7') {
        d = ch - '0';
        return true;
    }
    return false;
}

bool zstring::is_escape_char(char const *& s, unsigned& result) {
    unsigned d1, d2, d3;
    if (*s != '\\' || *(s + 1) == 0) {
        return false;
    }
    if (*(s + 1) == 'x' &&
        is_hex_digit(*(s + 2), d1) && is_hex_digit(*(s + 3), d2)) {
        result = d1*16 + d2;
        s += 4;
        return true;
    }
    /* C-standard octal escapes: either 1, 2, or 3 octal digits,
     * stopping either at 3 digits or at the first non-digit character.
     */
    /* 1 octal digit */
    if (is_octal_digit(*(s + 1), d1) && !is_octal_digit(*(s + 2), d2)) {
        result = d1;
        s += 2;
        return true;
    }
    /* 2 octal digits */
    if (is_octal_digit(*(s + 1), d1) && is_octal_digit(*(s + 2), d2) &&
        !is_octal_digit(*(s + 3), d3)) {
        result = d1 * 8 + d2;
        s += 3;
        return true;
    }
    /* 3 octal digits */
    if (is_octal_digit(*(s + 1), d1) && is_octal_digit(*(s + 2), d2) &&
        is_octal_digit(*(s + 3), d3)) {
        result = d1*64 + d2*8 + d3;
        s += 4;
        return true;
    }

    if (*(s+1) == 'u' && *(s+2) == '{') {
        result = 0;
        for (unsigned i = 0; i < 5; ++i) {
            if (is_hex_digit(*(s+3+i), d1)) {
                result = 16*result + d1;
            }
            else if (*(s+3+i) == '}') {
                if (result > 255 && !uses_unicode())
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
    if (*(s+1) == 'u' && is_hex_digit(*(s+2), d1)) {
        result = d1;
        unsigned i = 0;
        for (; i < 4; ++i) {
            if (is_hex_digit(*(s+3+i), d1)) {
                result = 16*result + d1;
            }
            else {
                break;
            }
        }
        if (result > 255 && !uses_unicode())
            throw default_exception("unicode characters outside of byte range are not supported");
        s += 3 + i;
        return true;
    }
    switch (*(s + 1)) {
    case 'a':
        result = '\a';
        s += 2;
        return true;
    case 'b':
        result = '\b';
        s += 2;
        return true;
#if 0
    case 'e':
        result = '\e';
        s += 2;
        return true;
#endif
    case 'f':
        result = '\f';
        s += 2;
        return true;
    case 'n':
        result = '\n';
        s += 2;
        return true;
    case 'r':
        result = '\r';
        s += 2;
        return true;
    case 't':
        result = '\t';
        s += 2;
        return true;
    case 'v':
        result = '\v';
        s += 2;
        return true;
    default:
        result = *(s + 1);
        s += 2;
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
    return gparams::get_value("unicode") == "true";
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

static const char esc_table[32][6] =
    { "\\x00", "\\x01", "\\x02", "\\x03", "\\x04", "\\x05", "\\x06", "\\x07", "\\x08", "\\x09", "\\n",   "\\v",   "\\f",   "\\r",   "\\x0E", "\\x0F",
      "\\x10", "\\x11", "\\x12", "\\x13", "\\x14", "\\x15", "\\x16", "\\x17", "\\x18", "\\x19", "\\x1A", "\\x1B", "\\x1C", "\\x1D", "\\x1E", "\\x1F"
};

std::string zstring::encode() const {
    std::ostringstream strm;
    char buffer[100];
    unsigned offset = 0;
#define _flush() if (offset > 0) { buffer[offset] = 0; strm << buffer; offset = 0; }
    for (unsigned i = 0; i < m_buffer.size(); ++i) {
        unsigned ch = m_buffer[i];
        if (0 <= ch && ch < 32) {
            _flush();
            strm << esc_table[ch];
        }
        else if (ch == '\\') {
            _flush();
            strm << "\\\\";
        }
        else if (ch >= 256) {
            _flush();
            strm << "\\u{" << std::hex << ch << std::dec << "}";
        }
        else if (ch >= 128) {
            _flush();
            strm << "\\x" << std::hex << ch << std::dec; 
        }
        else {
            if (offset == 99) { 
                _flush();
            }
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
        if (Li < Ri) {
            return true;
        } 
        else if (Li > Ri) {
            return false;
        } 
    }
    // at this point, all compared characters are equal,
    // so decide based on the relative lengths
    return lhs.length() < rhs.length();
}


