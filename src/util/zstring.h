/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    zstring.h

Abstract:

    String wrapper for unicode/ascii internal strings as vectors

Author:

    Nikolaj Bjorner (nbjorner) 2021-01-26

--*/
#pragma once

#include <cstdint>
#include <string>
#include "util/buffer.h"
#include "util/rational.h"

enum class string_encoding {
  ascii, // exactly 8 bits
  unicode,
  bmp // basic multilingual plane; exactly 16 bits
};

class zstring {
private:
    buffer<uint32_t> m_buffer;
    bool well_formed() const;
    bool is_escape_char(char const *& s, unsigned& result);
public:
    static unsigned unicode_max_char() { return 196607; }
    static unsigned unicode_num_bits() { return 18; }
    static unsigned bmp_max_char() { return 65535; }
    static unsigned bmp_num_bits() { return 16; }
    static unsigned ascii_max_char() { return 255; }
    static unsigned ascii_num_bits() { return 8; }
    static unsigned max_char() {
      switch (get_encoding()) {
      case string_encoding::unicode:
          return unicode_max_char();
      case string_encoding::bmp:
          return bmp_max_char();
      case string_encoding::ascii:
          return ascii_max_char();
      }
      return unicode_max_char();
    }
    static unsigned num_bits() {
      switch (get_encoding()) {
      case string_encoding::unicode:
          return unicode_num_bits();
      case string_encoding::bmp:
          return bmp_num_bits();
      case string_encoding::ascii:
          return ascii_num_bits();
      }
      return unicode_num_bits();
    }
    static string_encoding get_encoding();
    zstring() = default;
    zstring(char const* s);
    zstring(const std::string &str) : zstring(str.c_str()) {}
    zstring(rational const& r): zstring(r.to_string()) {}
    zstring(unsigned sz, unsigned const* s) { m_buffer.append(sz, s); SASSERT(well_formed()); }
    zstring(unsigned ch);
    zstring replace(zstring const& src, zstring const& dst) const;
    zstring reverse() const;
    std::string encode() const;
    unsigned length() const { return m_buffer.size(); }
    unsigned operator[](unsigned i) const { return m_buffer[i]; }
    bool empty() const { return m_buffer.empty(); }
    bool suffixof(zstring const& other) const;
    bool prefixof(zstring const& other) const;
    bool contains(zstring const& other) const;
    int  indexofu(zstring const& other, unsigned offset) const;
    int  last_indexof(zstring const& other) const;
    zstring extract(unsigned offset, unsigned length) const;
    zstring operator+(zstring const& other) const;
    bool operator==(const zstring& other) const;
    bool operator!=(const zstring& other) const;
    unsigned hash() const;

    void reset() { m_buffer.reset(); }
    zstring& operator+=(zstring const& other) { m_buffer.append(other.m_buffer); return *this; }
    uint32_t const* begin() const { return m_buffer.begin(); }
    uint32_t const* end() const { return m_buffer.end(); }

    friend std::ostream& operator<<(std::ostream &os, const zstring &str);
    friend bool operator<(const zstring& lhs, const zstring& rhs);
};
