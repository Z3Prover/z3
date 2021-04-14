/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    statistics.h

Abstract:

    Wrapper for reporting statistics

Author:

    Leonardo (leonardo) 2011-05-17

Notes:

--*/
#include "util/statistics.h"
#include "util/map.h"
#include "util/str_hashtable.h"
#include "util/buffer.h"
#include "util/smt2_util.h"
#include<iomanip>

void statistics::update(char const * key, unsigned inc) {
    if (inc != 0)
        m_stats.push_back(key_val_pair(key, inc));
}

void statistics::update(char const * key, double inc) {
    if (inc != 0.0)
        m_d_stats.push_back(key_d_val_pair(key, inc));
}

void statistics::copy(statistics const & st) {
    m_stats.append(st.m_stats);
    m_d_stats.append(st.m_d_stats);
}

void statistics::reset() {
    m_stats.reset();
    m_d_stats.reset();
}

template<typename V, typename M>
static void mk_map(V const & v, M & m) {
    for (auto const& p : v) {
        typename V::data_t::second_type val;
        if (m.find(p.first, val)) 
            m.insert(p.first, p.second + val);
        else
            m.insert(p.first, p.second);
    }
}

template<typename M>
static void get_keys(M const & m, ptr_buffer<char> & keys) {
    for (auto const& kv : m)
        keys.push_back(const_cast<char*>(kv.m_key));    
}

static void display_smt2_key(std::ostream & out, char const * key) {
    SASSERT(key != 0);
    out << ":";
    if (*key == ':')
        key++;
    while (*key) {
        if (is_smt2_simple_symbol_char(*key))
            out << *key;
        else
            out << "-";
        key++;
    }
}

struct str_lt {
    bool operator()(char const * s1, char const * s2) const { return strcmp(s1, s2) < 0; }
};

typedef map<char const *, unsigned, str_hash_proc, str_eq_proc> key2val;
typedef map<char const *, double, str_hash_proc, str_eq_proc> key2dval;

unsigned get_max_len(ptr_buffer<char> & keys) {
    unsigned max = 0;
    for (unsigned i = 0; i < static_cast<unsigned>(keys.size()); i++) {
        char * k = keys.get(i);
        if (*k == ':')
            k++;
        unsigned curr = static_cast<unsigned>(strlen(k));
        if (curr > max)
            max = curr;
    }
    return max;
}

std::ostream& statistics::display_smt2(std::ostream & out) const {   
#define INIT_DISPLAY()                                  \
    key2val m_u;                                        \
    key2dval m_d;                                       \
    mk_map(m_stats, m_u);                               \
    mk_map(m_d_stats, m_d);                             \
    ptr_buffer<char> keys;                              \
    get_keys(m_u, keys);                                \
    get_keys(m_d, keys);                                \
    std::sort(keys.begin(), keys.end(), str_lt());      \
    unsigned max = get_max_len(keys);                   

    INIT_DISPLAY();
    bool first = true;

#define DISPLAY_KEY() {                                         \
        if (!first)                                             \
            out << "\n ";                                       \
        display_smt2_key(out, k);                               \
        unsigned len = static_cast<unsigned>(strlen(k));        \
        for (unsigned j = len; j < max; j++)                    \
            out << " ";                                         \
        first = false;                                          \
    }
    
    out << "(";
    for (unsigned i = 0; i < keys.size(); i++) {
        char * k = keys.get(i);
        unsigned val; 
        if (m_u.find(k, val)) {
            DISPLAY_KEY();
            out << " " << val;
        }
        else {
            double d_val = 0.0;
            m_d.find(k, d_val);
            DISPLAY_KEY();
            out << " " << std::fixed << std::setprecision(2) << d_val;
        }
    }
    out << ")\n";
    return out;
}

std::ostream& statistics::display(std::ostream & out) const {
    INIT_DISPLAY();

#undef DISPLAY_KEY
#define DISPLAY_KEY() {                                         \
        if (*k == ':')                                          \
            k++;                                                \
        out << k << ":";                                        \
        unsigned len = static_cast<unsigned>(strlen(k));        \
        for (unsigned j = len; j < max; j++)                    \
            out << " ";                                         \
    }

    for (unsigned i = 0; i < keys.size(); i++) {
        char * k = keys.get(i);
        unsigned val; 
        if (m_u.find(k, val)) {
            DISPLAY_KEY();
            out << " " << val << "\n";
        }
        else {
            double d_val = 0.0;
            m_d.find(k, d_val);
            DISPLAY_KEY();
            out << " " << std::fixed << std::setprecision(2) << d_val << "\n";
        }
    }
    return out;
}

template<typename M>
static void display_internal(std::ostream & out, M const & m) {
    for (auto const& kv : m) {
        char const * key = kv.m_key;
        if (*key == ':') key++;
        while (*key) {
            if ('a' <= *key && *key <= 'z')
                out << ('A' + (*key - 'a'));
            else if (*key == ' ')
                out << "_";
            else
                out << *key;
        }
        out << " " << kv.m_value << "\n";
    }
}

void statistics::display_internal(std::ostream & out) const {
    key2val m_u;                                                
    key2dval m_d;                                               
    mk_map(m_stats, m_u);                                       
    mk_map(m_d_stats, m_d);            

    ::display_internal(out, m_u);
    ::display_internal(out, m_d);
}

unsigned statistics::size() const {
    return m_stats.size() + m_d_stats.size();
}

bool statistics::is_uint(unsigned idx) const {
    return idx < m_stats.size();
}

char const * statistics::get_key(unsigned idx) const {
    if (is_uint(idx))
        return m_stats[idx].first;
    else
        return m_d_stats[idx - m_stats.size()].first;
}

unsigned statistics::get_uint_value(unsigned idx) const {
    SASSERT(idx < size());
    SASSERT(is_uint(idx));
    return m_stats[idx].second;
}

double statistics::get_double_value(unsigned idx) const {
    SASSERT(idx < size());
    SASSERT(!is_uint(idx));
    return m_d_stats[idx - m_stats.size()].second;
}

static void get_uint64_stats(statistics& st, char const* name, unsigned long long value) {
    if (value <= UINT_MAX) {
        st.update(name, static_cast<unsigned>(value));
    }
    else {
        st.update(name, static_cast<double>(value));
    }
}

void get_memory_statistics(statistics& st) {
    unsigned long long max_mem = memory::get_max_used_memory();
    unsigned long long mem = memory::get_allocation_size();
    max_mem = (100*max_mem)/(1024*1024);
    mem = (100*mem)/(1024*1024);
    st.update("max memory", static_cast<double>(max_mem)/100.0);    
    st.update("memory", static_cast<double>(mem)/100.0);
    get_uint64_stats(st, "num allocs",  memory::get_allocation_count());
}

void get_rlimit_statistics(reslimit& l, statistics& st) {
    get_uint64_stats(st, "rlimit count", l.count());
}
