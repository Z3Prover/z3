/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    uint_set.h

Abstract:

    Sets of unsigned integers.
    
Author:

    Leonardo de Moura (leonardo) 2006-12-07.

Revision History:

--*/
#ifndef UINT_SET_H_
#define UINT_SET_H_

#include"util.h"
#include"vector.h"

COMPILE_TIME_ASSERT(sizeof(unsigned) == 4);

class uint_set : unsigned_vector {

public:

    typedef unsigned data;

    uint_set() {}

    uint_set(const uint_set & source) {
        for (unsigned i = 0; i < source.size(); ++i) {
            push_back(source[i]);
        }
    }

    ~uint_set() {}

    void swap(uint_set & other) {
        unsigned_vector::swap(other);
    }

    // return the maximum value that can be stored in the set. 
    unsigned get_max_elem() const {
        return 32 * size();
    }

    void reset() {
        unsigned_vector::reset();
    }

    bool empty() const {
        for (unsigned i = 0; i < size(); i++) {
            if ((*this)[i] != 0) {
                return false;
            }
        }
        return true;
    }

    void insert(unsigned val) {
        unsigned idx = val >> 5;
        if (idx >= size()) {
            resize(idx+1);
        }
        (*this)[idx] |= 1 << (val & 31);
    }

    void remove(unsigned val) {
        unsigned idx = val >> 5;
        if (idx < size()) {
            (*this)[val >> 5] &= ~(1 << (val & 31));
        }
    }

    bool contains(unsigned val) const {
        unsigned idx = val >> 5;        
        return idx < size() && ((*this)[idx] & (1 << (val & 31))) != 0;
    }

    unsigned num_elems() const {
        unsigned r = 0;
        for (unsigned i = 0; i < size(); i++) {
            r += get_num_1bits((*this)[i]);
        }
        return r;
    }

    // Insert in the this object the elements in the set source.
    uint_set & operator |=(const uint_set & source) {
        unsigned source_size = source.size();
        if (source_size > size()) {
            resize(source_size + 1);
        }
        for (unsigned i = 0; i < source_size; i++) {
            (*this)[i] |= source[i];
        }
        return *this;
    }

    uint_set& operator &=(const uint_set& source) {
        unsigned source_size = source.size();
        if (source_size < size()) {
            resize(source_size);
        }
        for (unsigned i = 0; i < size(); i++) {
            (*this)[i] &= source[i];
        }
        return *this;
    }

    bool operator==(const uint_set & source) const {
        unsigned min_size = size();
        if (source.size() < min_size) {
            min_size = source.size();
        }
        for (unsigned i = 0; i < min_size; i++) {
            if ((*this)[i] != source[i]) {
                return false;
            }
        }
        for (unsigned i = min_size; i < size(); ++i) {
            if ((*this)[i]) {
                return false;
            }
        }
        for (unsigned i = min_size; i < source.size(); ++i) {
            if (source[i]) {
                return false;
            }
        }

        return true;
    }

    bool operator!=(const uint_set & source) const {
        return !operator==(source);
    }

    // Return true if the this set is a subset of source.
    bool subset_of(const uint_set & source) const {
        unsigned min_size = size();
        if (source.size() < min_size) {
            min_size = source.size();
        }
        for (unsigned i = 0; i < min_size; i++) {
            if (((*this)[i] & ~source[i]) != 0) {
                return false;
            }
        }
        for (unsigned i = min_size; i < size(); ++i) {
            if ((*this)[i]) {
                return false;
            }
        }
        return true;
    }

    class iterator {
        uint_set const* m_set;
        unsigned  m_index;
        unsigned  m_last;

        bool invariant() const { return m_index <= m_last; }

        bool at_end() const { return m_index == m_last; }

        void scan_idx() {
            SASSERT(invariant());
            while (!at_end() && !m_set->contains(m_index) && 0 != (m_index & 31)) {
                ++m_index;
            }
            SASSERT(invariant());
        }
        void scan_word() {
            SASSERT((m_index & 31) == 0);
            SASSERT(invariant());
            unsigned idx = m_index >> 5;
            while (!at_end() && !(*m_set)[idx]) {
                ++idx;
                m_index += 32;
            }
            SASSERT(invariant());
        }
        bool contains() const { return m_set->contains(m_index); }
        void scan() {     
            scan_idx();
            if (contains() || at_end()) {
                return;
            }
            scan_word();
            if (!at_end() && !contains()) {
                ++m_index;
            }
            scan_idx();
            SASSERT(invariant());
        }
    public:
        iterator(uint_set const& s, bool at_end): 
            m_set(&s), m_index(at_end?s.get_max_elem():0), m_last(s.get_max_elem()) {
            scan();
            SASSERT(invariant());
          }
        unsigned operator*() const { return m_index; }
        bool operator==(iterator const& it) const { return m_index == it.m_index; }
        bool operator!=(iterator const& it) const { return m_index != it.m_index; }
        iterator & operator++() { ++m_index; scan(); return *this; }
        iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
        iterator & operator=(iterator const& other) { 
            m_set = other.m_set;
            m_index = other.m_index;
            m_last = other.m_last;
            return *this;
        }
    };

    iterator const begin() const { return iterator(*this, false); }
    iterator const end() const { return iterator(*this, true); }

    unsigned get_hash() const {
        unsigned h = 0;
        for (unsigned i = 0; i < size(); ++i) {
            h += (i+1)*((*this)[i]);
        }
        return h;
    }

    struct eq { bool operator()(uint_set const& s1, uint_set const& s2) const { return s1 == s2; } };
    struct hash { unsigned operator()(uint_set const& s) const { return s.get_hash(); } };
        
};

inline std::ostream & operator<<(std::ostream & target, const uint_set & s) {
    unsigned n = s.get_max_elem() + 1;
    target << "{";
    bool first = true;
    for (unsigned i = 0; i < n; i++) {
        if (s.contains(i)) {
            if (first) {
                first = false;
            }
            else {
                target << ", ";
            }
            target << i;
        }
    }
    target << "}";
    return target;
}

#endif /* UINT_SET_H_ */

