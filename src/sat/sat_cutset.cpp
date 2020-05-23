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
#include <memory>
#include <sstream>


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
    
    bool cut_set::insert(on_update_t& on_add, on_update_t& on_del, cut const& c) {
        unsigned i = 0, k = m_size;
        for (; i < k; ++i) {
            cut const& a = (*this)[i];
            if (a.subset_of(c)) {
                return false;
            }
            if (c.subset_of(a)) {
                std::swap(m_cuts[i--], m_cuts[--k]);
            }
        }
        // for DRAT make sure to add new element before removing old cuts
        // the new cut may need to be justified relative to the old cut
        push_back(on_add, c);
        std::swap(m_cuts[i++], m_cuts[m_size-1]);
        shrink(on_del, i);    
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


    void cut_set::shrink(on_update_t& on_del, unsigned j) { 
        if (m_var != UINT_MAX && on_del) {
            for (unsigned i = j; i < m_size; ++i) {
                on_del(m_var, m_cuts[i]);
            }
        }
        m_size = j; 
    }

    void cut_set::push_back(on_update_t& on_add, cut const& c) {
        SASSERT(m_max_size > 0);
        if (!m_cuts) {
            m_cuts = new (*m_region) cut[m_max_size];
        }
        if (m_size == m_max_size) {
            m_max_size *= 2;
            cut* new_cuts = new (*m_region) cut[m_max_size];
            std::uninitialized_copy(m_cuts, m_cuts + m_size, new_cuts);
            m_cuts = new_cuts;
        }
        if (m_var != UINT_MAX && on_add) on_add(m_var, c);
        m_cuts[m_size++] = c; 
    }

    void cut_set::evict(on_update_t& on_del, cut const& c) {
        for (unsigned i = 0; i < m_size; ++i) {
            if (m_cuts[i] == c) {
                evict(on_del, i);
                break;
            }
        }
    }

    void cut_set::evict(on_update_t& on_del, unsigned idx) {
        if (m_var != UINT_MAX && on_del) on_del(m_var, m_cuts[idx]); 
        m_cuts[idx] = m_cuts[--m_size]; 
    }

    void cut_set::init(region& r, unsigned max_sz, unsigned v) { 
        m_var = v;
        m_size = 0;
        SASSERT(!m_region || m_cuts);
        VERIFY(!m_region || m_max_size > 0);
        if (!m_region) {
            m_max_size = 2; // max_sz;
            m_region = &r;
            m_cuts = nullptr;
        }
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
        return compute_shift(table(), index);
    }
    
    bool cut::operator==(cut const& other) const {
        return table() == other.table() && dom_eq(other);
    }
    
    unsigned cut::hash() const {
        return get_composite_hash(*this, m_size, 
                                  [](cut const& c) { return (unsigned)c.table(); }, 
                                  [](cut const& c, unsigned i) { return c[i]; });
    }

    unsigned cut::dom_hash() const {
        return get_composite_hash(*this, m_size, 
                                  [](cut const& c) { return 3; }, 
                                  [](cut const& c, unsigned i) { return c[i]; });
    }

    bool cut::dom_eq(cut const& other) const {
        if (m_size != other.m_size) return false;
        for (unsigned i = 0; i < m_size; ++i) {
            if ((*this)[i] != other[i]) return false;
        }
        return true;
    }

    /**
     * \brief create the masks
     * i = 0: 101010101010101
     * i = 1: 1100110011001100
     * i = 2: 1111000011110000
     * i = 3: 111111110000000011111111
     */

    uint64_t cut::effect_mask(unsigned i) {
        SASSERT(i <= 6);
        uint64_t m = 0;
        if (i == 6) {
            m = ~((uint64_t)0);
        }
        else {
            m = (1ull << (1u << i)) - 1;   // i = 0: m = 1
            unsigned w = 1u << (i + 1);    // i = 0: w = 2
            while (w < 64) {
                m |= (m << w);             // i = 0: m = 1 + 4
                w *= 2;
            }
        }
        return m;
    }

    /**
       remove element from cut as it is deemed a don't care
     */
    void cut::remove_elem(unsigned i) {
        for (unsigned j = i + 1; j < m_size; ++j) {
            m_elems[j-1] = m_elems[j]; 
        }
        --m_size;
        uint64_t m = effect_mask(i);
        uint64_t t = 0;
        for (unsigned j = 0, offset = 0; j < 64; ++j) {
            if (0 != (m & (1ull << j))) {
                t |= ((m_table >> j) & 1u) << offset;
                ++offset;
            }
        }
        m_table = t;
        m_dont_care = 0;
        unsigned f = 0;
        for (unsigned e : *this) {
            f |= (1u << (e & 0x1F));
        }
        m_filter = f;
    }

    /**
       sat-sweep evaluation. Given 64 bits worth of possible values per variable, 
       find possible values for function table encoded by cut.
    */
    cut_val cut::eval(cut_eval const& env) const {
        cut_val v;
        uint64_t t = table();
        uint64_t n = table();
        unsigned sz = size();
        if (sz == 1 && t == 2) {
            return env[m_elems[0]];
        }
        for (unsigned i = 0; i < 64; ++i) {
            unsigned offset = 0;
            for (unsigned j = 0; j < sz; ++j) {
                offset |= (((env[m_elems[j]].m_t >> i) & 0x1) << j);
            }
            v.m_t |= ((t >> offset) & 0x1) << i;
            v.m_f |= ((n >> offset) & 0x1) << i;
        }
        return v;
    }
    
    std::ostream& cut::display(std::ostream& out) const {
        out << "{";
        for (unsigned i = 0; i < m_size; ++i) {
            out << (*this)[i];
            if (i + 1 < m_size) out << " ";
        }        
        out << "} ";
        display_table(out, m_size, table());
        return out;
    }

    std::ostream& cut::display_table(std::ostream& out, unsigned num_input, uint64_t table) {
        for (unsigned i = 0; i < (1u << num_input); ++i) {
            if (0 != (table & (1ull << i))) out << "1"; else out << "0";
        }    
        return out;
    }

    std::string cut::table2string(unsigned num_input, uint64_t table) {
        std::ostringstream strm;
        display_table(strm, num_input, table);
        return strm.str();
    }


}
