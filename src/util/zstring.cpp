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
                if (result > max_char())
                    return false;
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
        if (result > max_char())
            return false;
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
            m_buffer.push_back((unsigned char)*s);
            ++s;
        }
    }
    SASSERT(well_formed());
}

string_encoding zstring::get_encoding() {
    if (gparams::get_value("encoding") == "unicode") 
        return string_encoding::unicode;
    if (gparams::get_value("encoding") == "bmp") 
        return string_encoding::bmp;
    if (gparams::get_value("encoding") == "ascii") 
        return string_encoding::ascii;
    return string_encoding::unicode;
}

bool zstring::well_formed() const {
    for (unsigned ch : m_buffer) {
        if (ch > max_char()) {
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
        if (ch < 32 || ch >= 127 || ('\\' == ch && i + 1 < m_buffer.size() && 'u' == m_buffer[i+1])) {
            _flush();
            strm << "\\u{" << std::hex << ch << std::dec << '}';
        }
        else {
            if (offset == 99)  
                _flush();
            buffer[offset++] = (char)ch;
        }
    }
    _flush();
    return std::move(strm).str();
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
    for (unsigned last = length() - other.length() + 1; last-- > 0; ) {
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

// -----------------------------------------------
// char_set
// -----------------------------------------------

unsigned char_set::char_count() const {
    unsigned count = 0;
    for (auto const& r : m_ranges)
        count += r.length();
    return count;
}

bool char_set::contains(unsigned c) const {
    // binary search over sorted non-overlapping ranges
    int lo = 0, hi = static_cast<int>(m_ranges.size()) - 1;
    while (lo <= hi) {
        int mid = lo + (hi - lo) / 2;
        if (c < m_ranges[mid].m_lo)
            hi = mid - 1;
        else if (c >= m_ranges[mid].m_hi)
            lo = mid + 1;
        else
            return true;
    }
    return false;
}

void char_set::add(unsigned c) {
    if (m_ranges.empty()) {
        m_ranges.push_back(char_range(c));
        return;
    }
    // binary search for insertion point
    int lo = 0, hi = static_cast<int>(m_ranges.size()) - 1;
    while (lo <= hi) {
        int mid = lo + (hi - lo) / 2;
        if (c < m_ranges[mid].m_lo)
            hi = mid - 1;
        else if (c >= m_ranges[mid].m_hi)
            lo = mid + 1;
        else
            return; // already contained
    }
    // lo is the insertion point
    unsigned idx = static_cast<unsigned>(lo);
    bool merge_left  = idx > 0 && m_ranges[idx - 1].m_hi == c;
    bool merge_right = idx < m_ranges.size() && m_ranges[idx].m_lo == c + 1;
    if (merge_left && merge_right) {
        m_ranges[idx - 1].m_hi = m_ranges[idx].m_hi;
        m_ranges.erase(m_ranges.begin() + idx);
    } else if (merge_left) {
        m_ranges[idx - 1].m_hi = c + 1;
    } else if (merge_right) {
        m_ranges[idx].m_lo = c;
    } else {
        // positional insert: shift elements right and place new element
        m_ranges.push_back(char_range());
        for (unsigned k = m_ranges.size() - 1; k > idx; --k)
            m_ranges[k] = m_ranges[k - 1];
        m_ranges[idx] = char_range(c);
    }
}

void char_set::add(char_set const& other) {
    for (auto const& r : other.m_ranges) {
        for (unsigned c = r.m_lo; c < r.m_hi; ++c)
            add(c);
    }
}

char_set char_set::intersect_with(char_set const& other) const {
    char_set result;
    unsigned i = 0, j = 0;
    while (i < m_ranges.size() && j < other.m_ranges.size()) {
        unsigned lo = std::max(m_ranges[i].m_lo, other.m_ranges[j].m_lo);
        unsigned hi = std::min(m_ranges[i].m_hi, other.m_ranges[j].m_hi);
        if (lo < hi)
            result.m_ranges.push_back(char_range(lo, hi));
        if (m_ranges[i].m_hi < other.m_ranges[j].m_hi)
            ++i;
        else
            ++j;
    }
    return result;
}

char_set char_set::complement(unsigned max_char) const {
    char_set result;
    if (m_ranges.empty()) {
        result.m_ranges.push_back(char_range(0, max_char + 1));
        return result;
    }
    unsigned from = 0;
    for (auto const& r : m_ranges) {
        if (from < r.m_lo)
            result.m_ranges.push_back(char_range(from, r.m_lo));
        from = r.m_hi;
    }
    if (from <= max_char)
        result.m_ranges.push_back(char_range(from, max_char + 1));
    return result;
}

bool char_set::is_disjoint(char_set const& other) const {
    unsigned i = 0, j = 0;
    while (i < m_ranges.size() && j < other.m_ranges.size()) {
        if (m_ranges[i].m_hi <= other.m_ranges[j].m_lo)
            ++i;
        else if (other.m_ranges[j].m_hi <= m_ranges[i].m_lo)
            ++j;
        else
            return false;
    }
    return true;
}

bool char_set::is_subset(char_set const& other) const {
    // Every range in *this must be fully covered by ranges in other.
    // Both are sorted, non-overlapping.
    if (m_ranges.empty())
        return true;
    unsigned j = 0;
    for (unsigned i = 0; i < m_ranges.size(); ++i) {
        unsigned lo = m_ranges[i].m_lo;
        unsigned hi = m_ranges[i].m_hi;
        // Advance j to find covering range in other
        while (j < other.m_ranges.size() && other.m_ranges[j].m_hi <= lo)
            ++j;
        if (j >= other.m_ranges.size())
            return false;
        // other.m_ranges[j] must fully contain [lo, hi)
        if (other.m_ranges[j].m_lo > lo || other.m_ranges[j].m_hi < hi)
            return false;
    }
    return true;
}

std::ostream& char_set::display(std::ostream& out) const {
    if (m_ranges.empty()) {
        out << "{}";
        return out;
    }
    out << "{ ";
    bool first = true;
    for (auto const& r : m_ranges) {
        if (!first) out << ", ";
        first = false;
        if (r.is_unit()) {
            unsigned c = r.m_lo;
            if (c >= 'a' && c <= 'z')
                out << (char)c;
            else if (c >= 'A' && c <= 'Z')
                out << (char)c;
            else if (c >= '0' && c <= '9')
                out << (char)c;
            else
                out << "#[" << c << "]";
        } else {
            out << "[" << r.m_lo << "-" << (r.m_hi - 1) << "]";
        }
    }
    out << " }";
    return out;
}
