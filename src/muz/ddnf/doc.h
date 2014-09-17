/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    doc.h

Abstract:

    difference of cubes.

Author:

    Nuno Lopes (a-nlopes) 2013-03-01
    Nikolaj Bjorner (nbjorner) 2014-09-15

Revision History:

    Based on ternary_diff_bitvector by Nuno Lopes.

--*/

#ifndef _DOC_H_
#define _DOC_H_

#include "tbv.h"
#include "union_find.h"


class doc;
template<typename M, typename T> class union_bvec;

class doc_manager {
    tbv_manager m;
public:
    doc_manager(unsigned n): m(n) {}
    tbv_manager& tbv() { return m; }
    void reset();
    doc* allocate();
    doc* allocate1();
    doc* allocate0();
    doc* allocateX();
    doc* allocate(doc const& src);
    doc* allocate(uint64 n);
    doc* allocate(rational const& r);
    doc* allocate(uint64 n, unsigned hi, unsigned lo);
    doc* allocate(doc, unsigned const* permutation);
    void deallocate(doc* src);        
    void copy(doc& dst, doc const& src) const;
    doc& reset(doc& src) const { return fill0(src); }
    doc& fill0(doc& src) const;
    doc& fill1(doc& src) const;
    doc& fillX(doc& src) const;
    bool is_full(doc const& src) const;
    bool set_and(doc& dst, doc const& src) const;
    bool intersect(doc const& A, doc const& B, doc& result) const;
    void complement(doc const& src, ptr_vector<doc>& result);
    void subtract(doc const& A, doc const& B, ptr_vector<doc>& result);
    bool equals(doc const& a, doc const& b) const;
    unsigned hash(doc const& src) const;
    bool contains(doc const& a, doc const& b) const;
    std::ostream& display(std::ostream& out, doc const& b) const;
    unsigned num_tbits() const { return m.num_tbits(); }
};

typedef union_find<> subset_ints;

// union of tbv*, union of doc*
template<typename M, typename T>
class union_bvec { 
    ptr_vector<T> m_elems; // TBD: reuse allocator of M

    enum fix_bit_result_t {
        e_row_removed, // = 1
        e_duplicate_row, // = 2
        e_fixed
    };


public:
    unsigned size() const { return m_elems.size(); }
    T& operator[](unsigned idx) const { return *m_elems[idx]; }
    bool empty() const { return m_elems.empty(); }    
    bool is_full(M& m) const { return size() == 1 && m.is_full(*m_elems[0]); }
    bool contains(M& m, T& t) const {
        for (unsigned i = 0; i < m_elems.size(); ++i) {
            if (m.contains(*m_elems[i], t)) return true;
        }
        return false;
    }
    void push_back(T* t) {
        m_elems.push_back(t);
    }
    void reset(M& m) {
        for (unsigned i = 0; i < m_elems.size(); ++i) {
            m.deallocate(m_elems[i]);
        }
        m_elems.reset(); 
    }    
    bool insert(M& m, T* t) {
        unsigned sz = size(), j = 0;
        bool found = false;
        for (unsigned i = 0; i < sz; ++i, ++j) {
            if (!found && m.contains(*t, *m_elems[i])) {
                m.deallocate(m_elems[i]);
                --j;
            }
            else if (m.contains(*m_elems[i], *t)) {
                found = true;
            }
            else if (i != j) {                
                m_elems[j] = m_elems[i];
            }                
        }
        if (j != sz) m_elems.resize(j);
        if (found) {
            m.deallocate(t);
        }
        else {
            m_elems.push_back(t);
        }
        return !found;
    }
    void intersect(M& m, T& t) {
        unsigned sz = size();
        unsigned j = 0;
        for (unsigned i = 0; i < sz; ++i, ++j) {
            if (!m.set_and(*m_elems[i], t)) {
                m.deallocate(m_elems[i]);
                --j;
            }
            else if (i != j) {
                m_elems[i] = m_elems[j];
            }
        }
        if (j != sz) m_elems.resize(j);
    }
    void insert(M& m, union_bvec const& other) {
        for (unsigned i = 0; i < other.size(); ++i) {
            insert(m, other[i]);
        }
    }
    void intersect(M& m, union_bvec const& other) {
        union_bvec result;
        unsigned sz1 = size();
        unsigned sz2 = other.size();
        T* inter = m.allocate();
        for (unsigned i = 0; i < sz1; ++i) {
            for (unsigned j = 0; j < sz2; ++j) {
                if (m.intersect(*m_elems[i], other[j], *inter)) {
                    result.push_back(inter);
                    inter = m.allocate();
                }
            }
        }
        m.deallocate(inter);
        std::swap(result, *this);
        result.reset(m);
    }
    void complement(M& m, union_bvec& result) {     
        union_bvec negated;
        result.reset(m);
        result.push_back(m.allocateX());
        unsigned sz = size();
        for (unsigned i = 0; !empty() && i < sz; ++i) {
            m.complement(*m_elems[i], negated.m_elems);
            result.intersect(m, negated);
            negated.reset(m);
        }
    }
    void fix_eq_bits(unsigned idx1, tbv* BV, unsigned idx2, unsigned length,
                     subset_ints& equalities, const bit_vector& discard_cols) {
        for (unsigned i = 0; i < length; ++i) {
            unsigned k = 0;
            for (unsigned j = 0; j < size(); ++j, ++k) {
                NOT_IMPLEMENTED_YET();

#if 0
                T *eqBV = BV ? const_cast<T*>(BV) : &*I;
                bool discard_col = discard_cols.get(idx1+i) || (!BV && discard_cols.get(idx2+i));
                
                switch (fix_single_bit(*I, idx1+i, eqBV, idx2+i, equalities, discard_col)) {
                case 1:
                    // remove row
                    I = m_bitvectors.erase(I);
                    break;
                    
                case 2: {
                    // don't care column equality. try subtraction first.
                    union_ternary_bitvector diff(I->size()), result(I->size());
                    T BV(I->size(), true);
                    BV.set(idx1+i, BIT_0);
                    BV.set(idx2+i, BIT_1);
                    diff.add_new_fact(BV);
                    
                    BV.set(idx1+i, BIT_1);
                    BV.set(idx2+i, BIT_0);
                    diff.add_new_fact(BV);
                    
                    I->subtract(diff, result);
                    *I = *result.begin();
                    ++I;
                    break;
                }

                default:
                    if (I->is_empty()) {
                        I = m_bitvectors.erase(I);
                    } else {
                        // bits fixed
                        ++I;
                    }
                }
#endif
            }
        }
    }

private:

    fix_bit_result_t fix_single_bit(tbv& bv, unsigned idx, unsigned value, const subset_ints& equalities) {
        unsigned root = equalities.find(idx);
        idx = root;
        do {
            unsigned bitval = bv.get(idx);
            if (bitval == tbv::BIT_x) {
                bv.set(idx, value);
            } 
            else if (bitval != value) {
                return e_row_removed;
            }
            idx = equalities.next(idx);
        } 
        while (idx != root);
        return e_fixed;
    }

    fix_bit_result_t fix_single_bit(tbv & BV1, unsigned idx1, tbv & BV2, unsigned idx2,
                                  subset_ints& equalities, bool discard_col) {
        unsigned A = BV1.get(idx1);
        unsigned B = BV2.get(idx2);
        
        if (A == tbv::BIT_x) {
            if (B == tbv::BIT_x) {
                // Both are don't cares.
                if (!discard_col)
                    return e_duplicate_row;
                equalities.merge(idx1, idx2);
                return e_fixed;
            } else {
                // only A is don't care.
                return fix_single_bit(BV1, idx1, B, equalities);
            }
        } else if (B == tbv::BIT_x) {
            // Only B is don't care.
            return fix_single_bit(BV2, idx2, A, equalities);
        } else if (A == B) {
            return e_fixed;
        } else {
            return e_row_removed;
        }
    }

};

typedef union_bvec<tbv_manager, tbv> utbv;

class doc {
    // pos \ (neg_0 \/ ... \/ neg_n)
    friend class doc_manager;
    tbv*                         m_pos;
    utbv                         m_neg;
public:

    struct eq {
        doc_manager& m;
        eq(doc_manager& m):m(m) {}
        bool operator()(doc const& d1, doc const& d2) const {
            return m.equals(d1, d2);
        }
    };

    struct hash {
        doc_manager& m;
        hash(doc_manager& m):m(m) {}
        unsigned operator()(doc const& d) const {
            return m.hash(d);
        }
    };

    tbv& pos() { return *m_pos; }
    utbv& neg() { return m_neg; }
    tbv const& pos() const { return *m_pos; }
    utbv const& neg() const { return m_neg; }
        
};

typedef union_bvec<doc_manager, doc> udoc;

class doc_ref {
    doc_manager& dm;
    doc* d;
public:
    doc_ref(doc_manager& dm):dm(dm),d(0) {}
    doc_ref(doc_manager& dm, doc* d):dm(dm),d(d) {}
    ~doc_ref() {
        if (d) dm.deallocate(d);
    }
    doc_ref& operator=(doc* d2) {
        if (d) dm.deallocate(d);
        d = d2;
    }
    doc& operator*() { return *d; }
};

#endif /* _DOC_H_ */

