/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bit_matrix.cpp    
    
Author:

    Nikolaj Bjorner (nbjorner) 2020-01-1

Notes:

--*/

#include "math/simplex/bit_matrix.h"
#include "util/stopwatch.h"


bit_matrix::col_iterator bit_matrix::row::begin() const { 
    return bit_matrix::col_iterator(*this, true); 
}

bit_matrix::col_iterator bit_matrix::row::end() const { 
    return bit_matrix::col_iterator(*this, false); 
}

void bit_matrix::col_iterator::next() {
    ++m_column;
    while (m_column < r.m.m_num_columns && !r[m_column]) {
        while ((m_column % 64) == 0 && m_column + 64 < r.m.m_num_columns && !r.r[m_column >> 6]) {
            m_column += 64;
        }
        ++m_column;
    }
}

bool bit_matrix::row::operator[](unsigned i) const {
    SASSERT((i >> 6) < m.m_num_chunks);
    return (r[i >> 6] & (1ull << static_cast<uint64_t>(i & 63))) != 0;
}


std::ostream& bit_matrix::row::display(std::ostream& out) const {
    for (unsigned i = 0; i < m.m_num_columns; ++i) {
        out << ((*this)[i]?"1":"0");
    }
    return out << "\n";
}

void bit_matrix::reset(unsigned num_columns) {
    m_region.reset();
    m_rows.reset();
    m_num_columns = num_columns;
    m_num_chunks = (num_columns + 63)/64;
}
                
bit_matrix::row bit_matrix::add_row() {
    uint64_t* r = new (m_region) uint64_t[m_num_chunks];
    m_rows.push_back(r);
    memset(r, 0, sizeof(uint64_t)*m_num_chunks);
    return row(*this, r);
}

bit_matrix::row& bit_matrix::row::operator+=(row const& other) {
    for (unsigned i = 0; i < m.m_num_chunks; ++i) {
        r[i] ^= other.r[i];
    }
    return *this;
}

struct bit_matrix::report {
    bit_matrix& b;
    stopwatch   m_watch;
    report(bit_matrix& b) : b(b) { m_watch.start(); }
    ~report() {
        m_watch.stop();
        IF_VERBOSE(10, verbose_stream() << "solve " << b.m_rows.size() << " " << b.m_num_columns << " " << m_watch << "\n");
    }
};

void bit_matrix::solve() {
    basic_solve();
}

void bit_matrix::basic_solve() {
    report _report(*this);
    for (row& r : *this) {
        auto ci = r.begin();
        if (ci != r.end()) {
            unsigned c = *ci;
            for (row& r2 : *this) {
                if (r2 != r && r2[c]) r2 += r;
            }
        }        
    }
}

std::ostream& bit_matrix::display(std::ostream& out) {
    for (row& r : *this) {
        out << r;
    }
    return out;
}

/*
  produce a sequence of bits forming a Gray code.
  - All 2^n bit-sequences are covered.
  - The Hamming distance between two entries it one.
 */
unsigned_vector bit_matrix::gray(unsigned n) {
    SASSERT(n < 32);
    if (n == 0) {
        return unsigned_vector();
    }
    else if (n == 1) {
        unsigned_vector v;
        v.push_back(0);
        v.push_back(1);
        return v;
    }
    else {
        auto v = gray(n-1);
        auto w = v;
        w.reverse();
        for (auto & u : v) u |= (1 << (n-1));
        v.append(w);
        return v;
    }
}
