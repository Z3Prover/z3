/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    symbol.h

Abstract:

    Lisp-like symbols.

Author:

    Leonardo de Moura (leonardo) 2006-09-11.

Revision History:

    Use sz (= 8) bytes per symbol.

    The last byte is 0 when the string is directly encoded in m_data.
    Otherwise, the last byte contains a code, whether it is an unsigned (could now be uint64_t), 
    or a pointer to a string allocated in a shared region.

    Most string symbols are going to have length 8 or less, so allocating 11 characters for short string
    symbols covers a very large set of uses.
 
    The use of 8 bytes is very crude. Symbols are exposed over the API and it is convenient that they fit in a single uint64.
    Otherwise the API has to be rewritten to pass structure data for symbols.

--*/
#ifndef SYMBOL_H_
#define SYMBOL_H_
#include<ostream>
#include<climits>

#include "util/util.h"
#include "util/tptr.h"
#include "util/string_buffer.h"
#include "util/hash.h"

template<typename T>
class symbol_table;

class symbol {
    static const unsigned sz = 8;    // the upper 3 bits are used for tagging.
    union {
        unsigned char m_data[sz];
        uint64_t m_raw;
    };

    template<typename T>
    friend class symbol_table;
    struct dummy_t {};

    static const unsigned char tag_mask = 128 + 64;
    static const unsigned char mark_mask = 32;
    static const unsigned char istring_tag = 0;
    static const unsigned char estring_tag = 64;
    static const unsigned char num_tag = 128;

    explicit symbol(void const * data) { SASSERT(data); memcpy(m_data, data, sz); }
    explicit symbol(dummy_t) { memset(m_data, 0, sz); m_data[sz-1] = num_tag + 1; }
    
    static symbol mark(symbol s) { SASSERT(!s.is_marked()); symbol r(s.m_data); r.m_data[sz-1] |= mark_mask; return r; }
    static symbol unmark(symbol s) { SASSERT(s.is_marked()); symbol r(s.m_data); r.m_data[sz-1] &= ~mark_mask; return r; }

    bool is_marked() const { return mark_mask == (mark_mask & m_data[sz-1]); }
    bool is_internal_string() const { return (tag_mask & m_data[sz-1]) == istring_tag; }
    bool is_num() const             { return (tag_mask & m_data[sz-1]) == num_tag; }
    bool is_external_string() const { return (tag_mask & m_data[sz-1]) == estring_tag; }
    char const* get_internal() const { SASSERT(is_internal_string()); return reinterpret_cast<char const*>(m_data); }
    char const* get_external() const { SASSERT(is_external_string()); 
        uint64_t u = m_raw;
        u &= ~(3ull << 62ull);  
        return reinterpret_cast<char const*>(u); 
    }

    static symbol m_dummy;
    static symbol dummy() { return m_dummy; }

public:

    symbol() { memset(m_data, 0, sz); m_data[sz-1] = 3; }
    explicit symbol(char const * d);
    explicit symbol(unsigned idx) {
        m_raw = idx;
        m_data[sz-1] = 1;
    }

    static const symbol null;
    symbol & operator=(char const * d);
    symbol & operator=(symbol const& s) { memcpy(m_data, s.m_data, sz); return *this; }
    friend bool operator==(symbol const & s1, symbol const & s2) { return s1.m_raw == s2.m_raw; }
    friend bool operator!=(symbol const & s1, symbol const & s2) { return s1.m_raw != s2.m_raw; }

    inline bool is_null() const { return (0x3 & m_data[sz-1]) == 3; }
    inline bool is_numerical() const { return is_num(); }
    unsigned get_num() const { SASSERT(is_numerical()); return *reinterpret_cast<unsigned const*>(m_data); }
    std::string str() const;
    friend bool operator==(symbol const & s1, char const * s2) {
        if (s1.is_null() && s2 == nullptr)
            return true;
        if (s1.is_null() || s2 == nullptr)
            return false;
        if (!s1.is_numerical())
            return strcmp(s1.bare_str(), s2) == 0;
        return s1.str() == s2;
    }
    friend bool operator!=(symbol const & s1, char const * s2) { return !operator==(s1, s2); }

    // Low level functions.
    // It was made public to simplify the implementation of the C API.
    uint64_t c_api_symbol2ext() const { return m_raw; }

    static symbol c_api_ext2symbol(uint64_t r) { symbol s; s.m_raw = r; return s; }

    unsigned hash() const;
    bool contains(char c) const;
    unsigned display_size() const;
    char const * bare_str() const { 
        if (is_internal_string()) return get_internal();
        if (is_external_string()) return get_external();
        if (is_null()) return nullptr;
        UNREACHABLE();
        return nullptr;
    }
    friend std::ostream & operator<<(std::ostream & target, symbol const& s) {
        SASSERT(!s.is_marked());
        if (s.is_numerical()) {
            target << "k!" << s.get_num();
        }
        else if (s.is_null()) {
            target << "null";
        }
        else {
            target << s.bare_str();
        }
        return target;
    }

    template<unsigned SZ>
    friend string_buffer<SZ> & operator<<(string_buffer<SZ> & target, symbol const& s) {
        SASSERT(!s.is_marked());
        if (s.is_numerical()) {
            target << "k!" << s.get_num();
        }
        else if (s.is_null()) {
            target << "null";
        }
        else {
            target << s.bare_str();
        }
        return target;
    }
};

struct symbol_hash_proc {
    unsigned operator()(symbol const & s) const { 
        return s.hash();
    }
};

struct symbol_eq_proc {
    bool operator()(symbol const & s1, symbol const & s2) const {
        return s1 == s2;
    }
};

void initialize_symbols();
void finalize_symbols();
/*
  ADD_INITIALIZER('initialize_symbols();')
  ADD_FINALIZER('finalize_symbols();')
*/

// total order on symbols... I did not overloaded '<' to avoid misunderstandings.
// numerical symbols are smaller than non numerical symbols.
// two numerical symbols are compared using get_num.
// two non-numerical symbols are compared using string comparison.
bool lt(symbol const & s1, symbol const & s2);

#endif /* SYMBOL_H_ */

