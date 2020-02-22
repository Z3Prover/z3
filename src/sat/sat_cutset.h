/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_cutset.cpp

  Author:

    Nikolaj Bjorner 2020-01-02

  --*/

#pragma once
#include "util/region.h"
#include "util/debug.h"
#include "util/util.h"
#include "util/lbool.h"
#include "util/vector.h"
#include <algorithm>
#include <cstring>
#include <functional>

namespace sat {

    struct cut_val {
        cut_val():m_t(0ull), m_f(0ull) {}
        cut_val(uint64_t t, uint64_t f): m_t(t), m_f(f) {}
        uint64_t m_t, m_f;
    };
    
    typedef svector<cut_val> cut_eval;

    class cut {
        unsigned m_filter;
        unsigned m_size;
        unsigned m_elems[5];
        uint64_t m_table;
        mutable uint64_t m_dont_care;

        uint64_t table_mask() const { return (1ull << (1ull << m_size)) - 1ull; }

    public:
        cut(): m_filter(0), m_size(0), m_table(0), m_dont_care(0) {}

        cut(unsigned id): m_filter(1u << (id & 0x1F)), m_size(1), m_table(2), m_dont_care(0) { 
            m_elems[0] = id; 
        }

        cut(cut const& other) {
            *this = other;
        }

        cut& operator=(cut const& other) { 
            m_filter = other.m_filter;
            m_size = other.m_size;
            m_table = other.m_table;
            m_dont_care = other.m_dont_care;
            for (unsigned i = 0; i < m_size; ++i) m_elems[i] = other.m_elems[i];
            return *this;
        }

        cut_val eval(cut_eval const& env) const;

        unsigned size() const { return m_size; }

        unsigned filter() const { return m_filter; }

        static unsigned max_cut_size() { return 5; }

        unsigned const* begin() const { return m_elems; }
        unsigned const* end() const  { return m_elems + m_size; }

        bool add(unsigned i) {
            if (m_size >= max_cut_size()) {
                return false;
            }
            else {
                m_elems[m_size++] = i;
                m_filter |= (1u << (i & 0x1F));
                return true;
            }
        }
        void negate() { set_table(~m_table); }
        void set_table(uint64_t t) { m_table = t & table_mask(); }
        uint64_t table() const { return (m_table | m_dont_care) & table_mask(); }
        uint64_t ntable() const { return (~m_table | m_dont_care) & table_mask(); }

        uint64_t dont_care() const { return m_dont_care; }
        void add_dont_care(uint64_t t) const { m_dont_care |= t; }

        bool is_true()  const { return 0 == (table_mask() & ~table()); }
        bool is_false() const { return 0 == (table_mask() & ~m_dont_care & m_table); }

        bool operator==(cut const& other) const;
        bool operator!=(cut const& other) const { return !(*this == other); }
        unsigned hash() const;
        unsigned dom_hash() const;
        bool dom_eq(cut const& other) const;
        struct eq_proc { 
            bool operator()(cut const& a, cut const& b) const { return a == b; }
            bool operator()(cut const* a, cut const* b) const { return *a == *b; }
        };
        struct hash_proc {
            unsigned operator()(cut const& a) const { return a.hash(); }
            unsigned operator()(cut const* a) const { return a->hash(); }
        };

        struct dom_eq_proc {
            bool operator()(cut const& a, cut const& b) const { return a.dom_eq(b); }
            bool operator()(cut const* a, cut const* b) const { return a->dom_eq(*b); }
        };

        struct dom_hash_proc {
            unsigned operator()(cut const& a) const { return a.dom_hash(); }
            unsigned operator()(cut const* a) const { return a->dom_hash(); }
        };

        unsigned operator[](unsigned idx) const {
            return (idx >= m_size) ? UINT_MAX : m_elems[idx];
        }

        uint64_t shift_table(cut const& other) const;

        bool merge(cut const& a, cut const& b) {
            unsigned i = 0, j = 0;
            unsigned x = a[i];
            unsigned y = b[j];
            while (x != UINT_MAX || y != UINT_MAX) {
                if (!add(std::min(x, y))) {                    
                    return false;
                }
                if (x < y) {
                    x = a[++i];
                }
                else if (y < x) {
                    y = b[++j];
                }
                else {
                    x = a[++i];
                    y = b[++j];
                }
            }
            return true;
        }

        bool subset_of(cut const& other) const {
            if (other.m_filter != (m_filter | other.m_filter)) {
                return false;
            }
            unsigned i = 0;
            unsigned other_id = other[i];
            for (unsigned id : *this) {
                while (id > other_id) {
                    other_id = other[++i];
                }
                if (id != other_id) return false;
                other_id = other[++i];
            }
            return true;
        }

        void remove_elem(unsigned i);

        static uint64_t effect_mask(unsigned i);

        std::ostream& display(std::ostream& out) const;

        static std::ostream& display_table(std::ostream& out, unsigned num_input, uint64_t table);

        static std::string table2string(unsigned num_input, uint64_t table);
    };

    class cut_set {
        unsigned m_var;
        region*  m_region;
        unsigned m_size;
        unsigned m_max_size;
        cut *    m_cuts;
    public:
        typedef std::function<void(unsigned v, cut const& c)> on_update_t;

        cut_set(): m_var(UINT_MAX), m_region(nullptr), m_size(0), m_max_size(0), m_cuts(nullptr) {}
        void init(region& r, unsigned max_sz, unsigned v);
        bool insert(on_update_t& on_add, on_update_t& on_del, cut const& c);
        bool no_duplicates() const;
        unsigned var() const { return m_var; }
        unsigned size() const { return m_size; }
        cut const * begin() const { return m_cuts; }
        cut const * end() const { return m_cuts + m_size; }
        cut const & back() { return m_cuts[m_size-1]; }
        void push_back(on_update_t& on_add, cut const& c);
        void reset(on_update_t& on_del) { shrink(on_del, 0); }
        cut const & operator[](unsigned idx) const { return m_cuts[idx]; }
        void shrink(on_update_t& on_del, unsigned j); 
        void swap(cut_set& other) { 
            std::swap(m_var, other.m_var);
            std::swap(m_size, other.m_size); 
            std::swap(m_max_size, other.m_max_size); 
            std::swap(m_cuts, other.m_cuts); 
        }
        void evict(on_update_t& on_del, unsigned idx);
        void evict(on_update_t& on_del, cut const& c);

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, cut const& c) { return c.display(out); }
    inline std::ostream& operator<<(std::ostream& out, cut_set const& cs) { return cs.display(out); }

}
