/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    symbol.cpp

Abstract:
 
    Lisp-like symbols.

Author:

    Leonardo de Moura (leonardo) 2006-09-11.

Revision History:

--*/
#include "util/symbol.h"
#include "util/mutex.h"
#include "util/str_hashtable.h"
#include "util/region.h"
#include "util/string_buffer.h"
#include "util/map.h"
#include <cstring>
#include <thread>


symbol symbol::m_dummy = symbol(dummy_t());
const symbol symbol::null;


/**
   \brief Symbol table manager. It stores the symbol strings created at runtime.
*/
class internal_symbol_table {
    region        m_region; //!< Region used to store symbol strings.
    str_hashtable m_table;  //!< Table of created symbol strings.
    DECLARE_MUTEX(lock);
    
public:

    internal_symbol_table() {
        ALLOC_MUTEX(lock);
    }

    ~internal_symbol_table() {
        DEALLOC_MUTEX(lock);
    }

    char const * get_str(char const * d) {
        const char * result;
        lock_guard _lock(*lock);

        str_hashtable::entry * e;
        if (m_table.insert_if_not_there_core(d, e)) {
            // new entry
            size_t l   = strlen(d);
            // store the hash-code before the string
            size_t * mem = static_cast<size_t*>(m_region.allocate(l + 1 + sizeof(size_t)));
            *mem = e->get_hash();
            mem++;
            result = reinterpret_cast<const char*>(mem);
            memcpy(mem, d, l+1);
            // update the entry with the new ptr.
            e->set_data(result);
        }
        else {
            result = e->get_data();
        }
        SASSERT(m_table.contains(result));
        return result;
    }
};

struct internal_symbol_tables {
    unsigned sz;
    internal_symbol_table** tables;

    internal_symbol_tables(unsigned sz): sz(sz), tables(alloc_vect<internal_symbol_table*>(sz)) {
        for (unsigned i = 0; i < sz; ++i) {
            tables[i] = alloc(internal_symbol_table);
        }
    }
    ~internal_symbol_tables() {
        for (unsigned i = 0; i < sz; ++i) {
            dealloc(tables[i]);
        }
        dealloc_vect<internal_symbol_table*>(tables, sz);
    }

    char const * get_str(char const * d) {
        auto* table = tables[string_hash(d, static_cast<unsigned>(strlen(d)), 251) % sz];
        return table->get_str(d);
    }
};


static internal_symbol_tables* g_symbol_tables = nullptr;

void initialize_symbols() {
    if (!g_symbol_tables) {
        unsigned num_tables = 2 * std::min((unsigned) std::thread::hardware_concurrency(), 64u);
        g_symbol_tables = alloc(internal_symbol_tables, num_tables);        
    }
}

void finalize_symbols() {
    dealloc(g_symbol_tables);
    g_symbol_tables = nullptr;
}

symbol::symbol(char const * d) {
    memset(m_data, 0, sz);
    if (d == nullptr) {
        m_data[sz-1] = 3;
        return;
    }
    // std::cout << "create " << d << "\n";
    size_t l = strlen(d);
    if (l < sz) {
        memcpy(m_data, d, l);
        SASSERT(!m_data[sz-1]); 
        return;
    }
    char const* ptr = g_symbol_tables->get_str(d);
    *reinterpret_cast<uintptr_t*>(m_data) = reinterpret_cast<uintptr_t>(ptr);
    SASSERT(!(m_data[sz-1] & tag_mask));
    m_data[sz-1] &= ~tag_mask;
    m_data[sz-1] |= estring_tag;
}

symbol & symbol::operator=(char const * d) {
    symbol s(d);
    *this = s;
    return *this;
}

std::string symbol::str() const {
    SASSERT(!is_marked());
    if (is_numerical()) {
        string_buffer<128> buffer;
        buffer << "k!" << get_num();
        return buffer.c_str();
    }
    else if (is_null()) {
        return "<null>";
    }
    else {
        return bare_str();
    }
}

bool symbol::contains(char ch) const {
    SASSERT(!is_marked());
    return !is_null() && !is_numerical() && strchr(bare_str(), ch) != nullptr;
}
 
unsigned symbol::display_size() const {
    SASSERT(!is_marked());
    if (is_numerical()) {
        unsigned v = get_num();
        unsigned sz = 4;
        v = v >> 1;
        while (v > 0) {
            sz++;
            v = v >> 1;
        }
        return sz;
    }
    if (is_null()) {
        return 0;
    }
    return static_cast<unsigned>(strlen(bare_str()));
}

bool lt(symbol const & s1, symbol const & s2) { 
    if (s1 == s2)
        return false;
    if (s1.is_numerical()) {
        if (!s2.is_numerical())
            return true; // numeral symbols are smaller than non-numerical ones.
        return s1.get_num() < s2.get_num();
    }
    if (s2.is_numerical()) {
        SASSERT(!s1.is_numerical());
        return false;
    }
    if (!s1.bare_str())
        return true;
    if (!s2.bare_str())
        return false;
    SASSERT(!s1.is_numerical() && !s2.is_numerical());
    auto cmp = strcmp(s1.bare_str(), s2.bare_str());
    SASSERT(cmp != 0);
    return cmp < 0;
}

unsigned symbol::hash() const {
    if (is_null()) 
        return 0;
    if (is_internal_string()) 
        return hash_u_u(*reinterpret_cast<unsigned const*>(m_data), 
                        *reinterpret_cast<unsigned const*>(m_data + 4));
    if (is_numerical()) 
        return hash_u(get_num()); 
    return static_cast<unsigned>(reinterpret_cast<size_t const *>(get_external())[-1]);
}
