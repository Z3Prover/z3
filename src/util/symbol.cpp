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
#if 0

 // include "util/new_symbol.cpp"
#else

#include "util/symbol.h"
#include "util/mutex.h"
#include "util/str_hashtable.h"
#include "util/region.h"
#include "util/string_buffer.h"
#include <cstring>
#include <thread>



symbol symbol::m_dummy(TAG(void*, nullptr, 2));
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
    if (d == nullptr)
        m_data = nullptr;
    else
        m_data = g_symbol_tables->get_str(d);
}

symbol & symbol::operator=(char const * d) {
    m_data = d ? g_symbol_tables->get_str(d) : nullptr;
    return *this;
}

std::string symbol::str() const {
    SASSERT(!is_marked());
    if (GET_TAG(m_data) == 0) { 
        if (m_data)
            return m_data;
        else
            return "<null>";
    }
    else {
        string_buffer<128> buffer;
        buffer << "k!" << UNBOXINT(m_data);
        return buffer.c_str();
    }
}

bool symbol::contains(char ch) const {
    SASSERT(!is_marked());
    if (GET_TAG(m_data) == 0) {
        return strchr(m_data, ch) != nullptr;
    }
    else {
        return false;
    }
}
 
unsigned symbol::display_size() const {
    SASSERT(!is_marked());
    if (GET_TAG(m_data) == 0) {
        return static_cast<unsigned>(strlen(m_data));
    }
    else {
        unsigned v = UNBOXINT(m_data);
        unsigned sz = 4;
        v = v >> 1;
        while (v > 0) {
            sz++;
            v = v >> 1;
        }
        return sz;
    }
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

#endif
