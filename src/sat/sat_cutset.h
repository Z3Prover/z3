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
#include <algorithm>
#include <cstring>

namespace sat {

    struct cut {
        unsigned max_cut_size;
        unsigned m_filter;
        unsigned m_size;
        unsigned m_elems[6];
        uint64_t m_table;
        cut(): max_cut_size(6), m_filter(0), m_size(0), m_table(0) {}

        cut(unsigned id): m_filter(1u << (id & 0x1F)), m_size(1), m_table(2) { m_elems[0] = id; }

        cut(cut const& other): m_filter(other.m_filter), m_size(other.m_size), m_table(other.m_table) {
            for (unsigned i = 0; i < m_size; ++i) m_elems[i] = other.m_elems[i];
        }

        unsigned const* begin() const { return m_elems; }
        unsigned const* end() const  { return m_elems + m_size; }

        bool add(unsigned i, unsigned max_sz) {
            SASSERT(max_sz <= max_cut_size);
            if (m_size >= max_sz) {
                return false;
            }
            else {
                m_elems[m_size++] = i;
                m_filter |= (1u << (i & 0x1F));
                return true;
            }
        }
        void sort();
        void negate() { set_table(~m_table); }
        uint64_t table_mask() const { return (1ull << (1ull << m_size)) - 1ull; }
        void set_table(uint64_t t) { m_table = t & table_mask(); }

        bool is_true()  const { return 0 == (table_mask() & ~m_table); }
        bool is_false() const { return 0 == (table_mask() &  m_table); }

        bool operator==(cut const& other) const;
        unsigned hash() const;
        struct eq_proc { 
            bool operator()(cut const& a, cut const& b) const { return a == b; }
            bool operator()(cut const* a, cut const* b) const { return *a == *b; }
        };
        struct hash_proc {
            unsigned operator()(cut const& a) const { return a.hash(); }
            unsigned operator()(cut const* a) const { return a->hash(); }
        };

        unsigned operator[](unsigned idx) const {
            return (idx >= m_size) ? UINT_MAX : m_elems[idx];
        }

        uint64_t shift_table(cut const& other) const;

        bool merge(cut const& a, cut const& b, unsigned max_sz) {
            unsigned i = 0, j = 0;
            unsigned x = a[i];
            unsigned y = b[j];
            while (x != UINT_MAX || y != UINT_MAX) {
                if (!add(std::min(x, y), max_sz)) {
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

        std::ostream& display(std::ostream& out) const;
    };

    class cut_set {
        region*  m_region;
        unsigned m_size;
        unsigned m_max_size;
        cut *    m_cuts;
    public:
        cut_set(): m_region(nullptr), m_size(0), m_max_size(0), m_cuts(nullptr) {}
        void init(region& r, unsigned sz) { 
            m_max_size = sz;
            SASSERT(!m_region || m_cuts);
            if (m_region) return;
            m_region = &r; 
            m_cuts = new (r) cut[sz]; 
        }
        bool insert(cut const& c);
        bool no_duplicates() const;
        unsigned size() const { return m_size; }
        cut * begin() const { return m_cuts; }
        cut * end() const { return m_cuts + m_size; }
        cut & back() { return m_cuts[m_size-1]; }
        void push_back(cut const& c) {
            SASSERT(c.m_size > 0);
            if (m_size == m_max_size) {
                m_max_size *= 2;
                cut* new_cuts = new (*m_region) cut[m_max_size]; 
                memcpy(new_cuts, m_cuts, sizeof(cut)*m_size);
                m_cuts = new_cuts;
            }
            m_cuts[m_size++] = c; 
        }
        void reset() { m_size = 0; }
        cut & operator[](unsigned idx) { return m_cuts[idx]; }
        void shrink(unsigned j) { m_size = j; }
        void swap(cut_set& other) { std::swap(m_size, other.m_size); std::swap(m_cuts, other.m_cuts); std::swap(m_max_size, other.m_max_size); }
        void evict(unsigned idx) {  m_cuts[idx] = m_cuts[--m_size]; }
        std::ostream& display(std::ostream& out) const;
    };

}
