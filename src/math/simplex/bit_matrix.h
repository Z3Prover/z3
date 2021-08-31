/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bit_matrix.h

Abstract:

    Dense bit-matrix utilities.    
    
Author:

    Nikolaj Bjorner (nbjorner) 2020-01-1

Notes:

    Exposes Gauss-Jordan simplification.
    Uses extremely basic implementation, can be tuned by 4R method.

--*/

#pragma once

#include "util/region.h"
#include "util/vector.h"

class bit_matrix {

    region               m_region;
    unsigned             m_num_columns;
    unsigned             m_num_chunks;
    ptr_vector<uint64_t> m_rows;

    struct report;

public:

    class col_iterator;
    class row_iterator;
    class row {
        friend row_iterator;
        friend bit_matrix;
        bit_matrix& m;
        uint64_t*   r;
        row(bit_matrix& m, uint64_t* r):m(m), r(r) {}        
    public:
        col_iterator begin() const;
        col_iterator end() const;
        bool operator[](unsigned i) const;
        void set(unsigned i, bool b) { if (b) set(i); else unset(i); }
        void set(unsigned i) { SASSERT((i >> 6) < m.m_num_chunks); r[i >> 6] |= (1ull << (i & 63)); }
        void unset(unsigned i) { SASSERT((i >> 6) < m.m_num_chunks); r[i >> 6] &= ~(1ull << (i & 63)); }
        row& operator+=(row const& other);

        // using pointer equality:
        bool operator==(row const& other) const { return r == other.r; }
        bool operator!=(row const& other) const { return r != other.r; }
        std::ostream& display(std::ostream& out) const;
    };

    class col_iterator {
        friend row;
        friend bit_matrix;
        row r;
        unsigned m_column;        
        void next();
        col_iterator(row const& r, bool at_first): r(r), m_column(at_first?0:r.m.m_num_columns) { if (at_first && !r[m_column]) next(); }
    public:
        unsigned const& operator*() const { return m_column; }
        unsigned const* operator->() const { return &m_column; }
        col_iterator& operator++() { next(); return *this; }
        col_iterator operator++(int) { auto tmp = *this; next(); return tmp; }
        bool operator==(col_iterator const& other) const { return m_column == other.m_column; }
        bool operator!=(col_iterator const& other) const { return m_column != other.m_column; }  
    };

    class row_iterator {
        friend class bit_matrix;
        row m_row;
        unsigned m_index;
        row_iterator(bit_matrix& m, bool at_first): m_row(m, at_first ? m.m_rows[0] : nullptr), m_index(at_first ? 0 : m.m_rows.size()) {}
        void next() { m_index++; if (m_index < m_row.m.m_rows.size()) m_row.r = m_row.m.m_rows[m_index]; }
    public:
        row const& operator*() const { return m_row; }
        row const* operator->() const { return &m_row; }
        row& operator*() { return m_row; }
        row* operator->() { return &m_row; }
        row_iterator& operator++() { next(); return *this; }
        row_iterator operator++(int) { auto tmp = *this; next(); return tmp; }
        bool operator==(row_iterator const& other) const { return m_index == other.m_index; }
        bool operator!=(row_iterator const& other) const { return m_index != other.m_index; }  
    };

    void reset(unsigned num_columns);
    
    row_iterator begin() { return row_iterator(*this, true); }
    row_iterator end() { return row_iterator(*this, false); }
                
    row add_row();
    void solve();
    std::ostream& display(std::ostream& out);

private:
    void basic_solve();
    unsigned_vector gray(unsigned n);
};

inline std::ostream& operator<<(std::ostream& out, bit_matrix& m) { return m.display(out); }
inline std::ostream& operator<<(std::ostream& out, bit_matrix::row const& r) { return r.display(out); }

