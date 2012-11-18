/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    symbol.h

Abstract:

    Lisp-like symbols.

Author:

    Leonardo de Moura (leonardo) 2006-09-11.

Revision History:

--*/
#ifndef _SYMBOL_H_
#define _SYMBOL_H_
#include<ostream>
#include<limits.h>

#include"util.h"
#include"tptr.h"
#include"string_buffer.h"

template<typename T>
class symbol_table;

class symbol {
    char const * m_data;

    template<typename T>
    friend class symbol_table;

    explicit symbol(void const * data):
        m_data(reinterpret_cast<char const *>(data)) {
    }
    bool is_marked() const {
        return GET_TAG(m_data) > 1;
    }
    static symbol mark(symbol s) {
        SASSERT(!s.is_marked());
        return symbol(TAG(void *, UNTAG(void *, s.m_data), GET_TAG(s.m_data) + 2));
    }
    static symbol unmark(symbol s) {
        SASSERT(s.is_marked());
        return symbol(TAG(void *, UNTAG(void *, s.m_data), GET_TAG(s.m_data) - 2));
    }
    static symbol m_dummy;
public:
    symbol():
        m_data(0) {
    }
    explicit symbol(char const * d);
    explicit symbol(unsigned idx):
        m_data(BOXTAGINT(char const *, idx, 1)) {
#ifndef _AMD64_
        SASSERT(idx < (SIZE_MAX >> PTR_ALIGNMENT));
#endif
    }
    static symbol dummy() { return m_dummy; }
    static const symbol null;
    symbol & operator=(char const * d);
    friend bool operator==(symbol const & s1, symbol const & s2) { return s1.m_data == s2.m_data; }
    friend bool operator!=(symbol const & s1, symbol const & s2) { return s1.m_data != s2.m_data; }
    bool is_numerical() const { return GET_TAG(m_data) == 1; }
    unsigned int get_num() const { SASSERT(is_numerical()); return UNBOXINT(m_data); }
    std::string str() const;
    friend bool operator==(symbol const & s1, char const * s2) {
        if (s1.m_data == 0 && s2 == 0)
            return true;
        if (s1.m_data == 0 || s2 == 0)
            return false;
        if (!s1.is_numerical())
            return strcmp(s1.bare_str(), s2) == 0;
        return s1.str() == s2;
    }
    friend bool operator!=(symbol const & s1, char const * s2) { return !operator==(s1, s2); }
    void const * c_ptr() const { return m_data; }
    // Low level function.
    // It is the inverse of c_ptr().
    // It was made public to simplify the implementation of the C API.
    static symbol mk_symbol_from_c_ptr(void const * ptr) { 
        symbol s(ptr); 
        return s;
    }
    unsigned hash() const { 
        if (m_data == 0) return 0x9e3779d9;
        else if (is_numerical()) return get_num(); 
        else return static_cast<unsigned>(reinterpret_cast<size_t const *>(m_data)[-1]);
    }
    bool contains(char c) const;
    unsigned size() const;
    char const * bare_str() const { SASSERT(!is_numerical()); return is_numerical() ? "" : m_data; }
    friend std::ostream & operator<<(std::ostream & target, symbol s) {
        SASSERT(!s.is_marked());
        if (GET_TAG(s.m_data) == 0) {
            if (s.m_data) {
                target << s.m_data;
            }
            else {
                target << "null";
            }
        }
        else {
            target << "k!" << UNBOXINT(s.m_data);
        }
        return target;
    }
    template<unsigned SZ>
    friend string_buffer<SZ> & operator<<(string_buffer<SZ> & target, symbol s) {
        SASSERT(!s.is_marked());
        if (GET_TAG(s.m_data) == 0) {
            if (s.m_data) {
                target << s.m_data;
            }
            else {
                target << "null";
            }
        }
        else {
            target << "k!" << UNBOXINT(s.m_data);
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

#endif /* _SYMBOL_H_ */

