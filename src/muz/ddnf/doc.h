/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    doc.h

Abstract:

    difference of cubes.

Author:

    Nikolaj Bjorner (nbjorner) 2014-09-15

Revision History:

    Based on ternary_diff_bitvector by Nuno Lopes.

--*/

#ifndef _DOC_H_
#define _DOC_H_

#if 0

#include "tbv.h"

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
    void deallocate(doc* src);        
    void copy(doc& dst, doc const& src) const;
    doc& reset(doc& src) const { return fill0(src); }
    doc& fill0(doc& src) const;
    doc& fill1(doc& src) const;
    doc& fillX(doc& src) const;
    bool set_and(doc& dst, doc const& src) const;
    //  doc& set_or(doc& dst,  doc const& src) const;
    void neg(doc const& src, union_bvec<doc_mananger, doc>& result) const;
    bool equals(doc const& a, doc const& b) const;
    unsigned hash(doc const& src) const;
    bool contains(doc const& a, doc const& b) const;
    std::ostream& display(std::ostream& out, doc const& b) const;
};

// union of tbv*, union of doc*
template<typename M, typename T>
class union_bvec {
    ptr_vector<T> m_elems; // TBD: reuse allocator of M
public:
    unsigned size() const { return m_elems.size(); }
    T& operator[](unsigned idx) const { return *m_elems[idx]; }
    void reset(M& m) {
        for (unsigned i = 0; i < m_elems.size(); ++i) {
            m.deallocate(m_elems[i]);
        }
        m_elems.reset(); 
    }
    void insert(M& m, T* t) {
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
    }
    bool intersect(M& m, T& t) {
        unsigned sz = size();
        for (unsigned i = 0; i < sz; ++i) {
            if (!m.set_and(m_elems[i], t)) 
                return false;
        }
        return true;
    }
    void insert(M& m, union_set const& other) {
        for (unsigned i = 0; i < other.size(); ++i) {
            insert(m, other[i]);
        }
    }
    void intersect(M& m, union_set const& other, union_set& result) {
        result.reset(m);
        unsigned sz1 = size();
        unsigned sz2 = other.size();
        T* inter = m.allocate();
        for (unsigned i = 0; i < sz1; ++i) {
            for (unsigned j = 0; j < sz2; ++j) {
                if (m.intesect(*m_elems[i], other[j], *inter)) {
                    result.push_back(inter);
                    inter = m.allocate();
                }
            }
        }
        m.deallocate(inter);
    }
    void neg(M& m, union_set& result) {     
        union_set negated;
        result.reset(m);
        result.push_back(m.allocateX());
        unsigned sz = size();
        for (unsigned i = 0; !result.empty() && i < sz; ++i) {
            // m.set_neg(*m_elems[i]);
            // result.intersect(m, negated);
        }
    }

    void subtract(M& m, union_set const& other, union_set& result) {
        result.reset(m);
        
    }
};

class doc {
    // pos \ (neg_0 \/ ... \/ neg_n)
    friend class doc_manager;
    tbv*                         m_pos;
    union_bvec<tbv_manager, tbv> m_neg;
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
        
};

#endif

#endif /* _DOC_H_ */

#if 0

    class utbv {
        friend class ternary_bitvector;

        ternary_bitvector m_pos;
        union_ternary_bitvector<ternary_bitvector> m_neg;

    public:
        utbv() : m_pos(), m_neg(0) {}
        utbv(unsigned size) : m_pos(size), m_neg(size) {}
        utbv(unsigned size, bool full);
        utbv(const rational& n, unsigned num_bits);
        explicit utbv(const ternary_bitvector & tbv);

        bool contains(const utbv & other) const;
        bool contains(const ternary_bitvector & other) const;
        bool contains(unsigned offset, const utbv& other,
                      unsigned other_offset, unsigned length) const;
        bool is_empty() const;

        utbv band(const utbv& other) const;
        void neg(union_ternary_bitvector<utbv>& result) const;

        static bool has_subtract() { return true; }
        void subtract(const union_ternary_bitvector<utbv>& other,
            union_ternary_bitvector<utbv>& result) const;


        unsigned get(unsigned idx);
        void set(unsigned idx, unsigned val);

        void swap(utbv & other);
        void reset();


        void display(std::ostream & out) const;

    private:
        void add_negated(const ternary_bitvector& neg);
        void add_negated(const union_ternary_bitvector<ternary_bitvector>& neg);
        bool fold_neg();
    };

#endif
