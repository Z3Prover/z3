/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_cutset.cpp

  Author:

    Nikolaj Bjorner 2020-01-02

  --*/


#include "util/hashtable.h"
#include "sat/sat_cutset.h"
#include "sat/sat_cutset_compute_shift.h"


namespace sat {


    /**
       \brief
       if c is subsumed by a member in cut_set, then c is not inserted.
       otherwise, remove members that c subsumes.
       Note that the cut_set maintains invariant that elements don't subsume each-other.
       
       TBD: this is a bottleneck.
       Ideas:
       - add Bloom filter to is_subset_of operation.
       - pre-allocate fixed array instead of vector for cut_set to avoid overhead for memory allocation.
    */
    
    bool cut_set::insert(cut const& c) {
        SASSERT(c.m_size > 0);
        unsigned i = 0, j = 0;
        for (; i < size(); ++i) {
            cut const& a = (*this)[i];
            if (a.subset_of(c)) {
                return false;
            }
            if (c.subset_of(a)) {
                continue;
            }
            else if (j < i) {
                (*this)[j] = a;
            }
            SASSERT(!(a == c));
            ++j;
        }
        shrink(j);    
        push_back(c);
        return true;
    }
    
    bool cut_set::no_duplicates() const {
        hashtable<cut const*, cut::hash_proc, cut::eq_proc> table;
        for (auto const& cut : *this) {
            VERIFY(!table.contains(&cut));
            table.insert(&cut);
        }
        return true;
    }

    std::ostream& cut_set::display(std::ostream& out) const {
        for (auto const& cut : *this) {
            cut.display(out) << "\n";
        }
        return out;
    }

    /**
       \brief shift table 'a' by adding elements from 'c'.
       a.shift_table(c)
       
       \pre 'a' is a subset of 'c'.
       
       Let 't' be the table for 'a'.
       
       i'th bit in t  is function of indices x0*2^0 + x2*2^1 = i
       i'th bit in t' is function of indices x0*2^0 + x1*2^1 + x2*2^2 = i
       
       i -> assignment to coefficients in c, 
       -> assignment to coefficients in a
       -> compute j, 
       -> t'[i] <- t[j]
       
       This is still time consuming:
       Ideas: 
       - pre-compute some shift operations.
       - use strides on some common cases.
       - what ABC does?
    */       
    uint64_t cut::shift_table(cut const& c) const {
        SASSERT(subset_of(c));
        unsigned index = 0;
        for (unsigned i = 0, j = 0, x = (*this)[i], y = c[j]; x != UINT_MAX; ) {
            if (x == y) {
                index |= (1 << j);
                x = (*this)[++i];
            }
            y = c[++j];
        }
        index |= (1 << c.m_size);
        return compute_shift(m_table, index);
    }
    
    bool cut::operator==(cut const& other) const {
        if (m_size != other.m_size) return false;
        if (m_table != other.m_table) return false;
        for (unsigned i = 0; i < m_size; ++i) {
            if ((*this)[i] != other[i]) return false;
        }
        return true;
    }
    
    unsigned cut::hash() const {
        return get_composite_hash(*this, m_size, 
                                  [](cut const& c) { return (unsigned)c.m_table; }, 
                                  [](cut const& c, unsigned i) { return c[i]; });
    }
    
    std::ostream& cut::display(std::ostream& out) const {
        out << "{";
        for (unsigned i = 0; i < m_size; ++i) {
            out << (*this)[i];
            if (i + 1 < m_size) out << " ";
        }        
        out << "} t: ";
        for (unsigned i = 0; i < (1u << m_size); ++i) {
            if (0 != (m_table & (1ull << i))) out << "1"; else out << "0";
        }    
        return out;
    }

    void cut::sort() {
        std::sort(m_elems, m_elems + m_size);
    }

}
