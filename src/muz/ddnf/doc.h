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
typedef union_find<> subset_ints;

class doc_manager {
    tbv_manager m;
    tbv*        m_full;
    small_object_allocator m_alloc;
public:
    doc_manager(unsigned num_bits);
    ~doc_manager();
    tbv_manager& tbvm() { return m; }
    doc* allocate();
    doc* allocate1();
    doc* allocate0();
    doc* allocateX();
    doc* allocate(doc const& src);
    doc* allocate(tbv const& src);
    doc* allocate(tbv * src);
    doc* allocate(uint64 n);
    doc* allocate(rational const& r);
    doc* allocate(uint64 n, unsigned hi, unsigned lo);
    doc* allocate(doc const& src, unsigned const* permutation);
    void deallocate(doc* src);        
    void copy(doc& dst, doc const& src);
    doc& reset(doc& src) { return fill0(src); }
    doc& fill0(doc& src);
    doc& fill1(doc& src);
    doc& fillX(doc& src);
    bool is_full(doc const& src) const;
    bool set_and(doc& dst, doc const& src);
    bool fold_neg(doc& dst);
    bool intersect(doc const& A, doc const& B, doc& result) const;
    void complement(doc const& src, ptr_vector<doc>& result);
    void subtract(doc const& A, doc const& B, ptr_vector<doc>& result);
    bool equals(doc const& a, doc const& b) const;
    unsigned hash(doc const& src) const;
    bool contains(doc const& a, doc const& b) const;
    std::ostream& display(std::ostream& out, doc const& b) const;
    unsigned num_tbits() const { return m.num_tbits(); }
    doc* project(doc_manager& dstm, unsigned n, bool const* to_delete, doc const& src);
    bool well_formed(doc const& d) const;
    bool merge(doc& d, unsigned lo, unsigned length, subset_ints& equalities, bit_vector const& discard_cols);
    void set(doc& d, unsigned idx, tbit value);
private:
    unsigned diff_by_012(tbv const& pos, tbv const& neg, unsigned& index);
    bool merge(doc& d, unsigned idx, subset_ints& equalities, bit_vector const& discard_cols);
    bool can_project_neg(tbv const& pos, unsigned n, bool const* to_delete, tbv const& neg);
};


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
    bool is_empty() const { return m_elems.empty(); }    
    bool is_full(M& m) const { return size() == 1 && m.is_full(*m_elems[0]); }
    bool contains(M& m, T& t) const {
        for (unsigned i = 0; i < m_elems.size(); ++i) {
            if (m.contains(*m_elems[i], t)) return true;
        }
        return false;
    }
    std::ostream& display(M& m, std::ostream& out) const {
        for (unsigned i = 0; i < size(); ++i) {
            m.display(out, *m_elems[i]);
            if (i + 1 < size()) out << ", ";
        }
        return out << "\n";
    }

    void push_back(T* t) {
        m_elems.push_back(t);
    }
    void erase(M& m, unsigned idx) {
        T* t = m_elems[idx];
        m_elems.erase(t);
        m.deallocate(t);
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
            else {
                if (m.contains(*m_elems[i], *t)) {
                    found = true;
                }
                if (i != j) {                
                    m_elems[j] = m_elems[i];
                }       
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
    void subtract(M& m, union_bvec const& other) {
        unsigned sz = other.size();
        for (unsigned i = 0; !is_empty() && i < sz; ++i) {
            subtract(m, other[i]);
        }
        // TBD compress?
    }
    void subtract(M& m, T& t) {
        unsigned sz = size();
        bool found = false;
        union_bvec result;
        for (unsigned i = 0; i < sz; ++i) {
            m.subtract(*m_elems[i], t, result.m_elems);
        }
        std::swap(m_elems, result.m_elems);
        result.reset(m);
    }
    void complement(M& m, union_bvec& result) const {     
        union_bvec negated;
        result.reset(m);
        result.push_back(m.allocateX());
        unsigned sz = size();
        for (unsigned i = 0; !is_empty() && i < sz; ++i) {
            m.complement(*m_elems[i], negated.m_elems);
            result.intersect(m, negated);
            negated.reset(m);
        }
    }
    void copy(M& m, union_bvec const& other) {
        reset(m);
        for (unsigned i = 0; i < other.size(); ++i) {
            push_back(m.allocate(other[i]));
        }
    }

    void merge(M& m, unsigned lo, unsigned length, subset_ints & equalities, bit_vector const& discard_cols) {
        for (unsigned i = 0; i < size(); ++i) {
            if (!m.merge(*m_elems[i], lo, length, equalities, discard_cols)) {
                erase(m, i);
                --i;
            }
        }
    }

    void merge(M& m, unsigned lo1, unsigned lo2, unsigned length, bit_vector const& discard_cols) {
        union_find_default_ctx union_ctx;
        subset_ints equalities(union_ctx);
        for (unsigned i = 0; i < discard_cols.size(); ++i) {
            equalities.mk_var();
        }
        for (unsigned j = 0; j < length; ++j) {
            equalities.merge(lo1 + j, lo2 + j);
        }
        merge(m, lo1, length, equalities, discard_cols);
    }


private:


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

    doc(tbv* t): m_pos(t) {}
    tbv& pos() { return *m_pos; }
    utbv& neg() { return m_neg; }
    tbv const& pos() const { return *m_pos; }
    utbv const& neg() const { return m_neg; }
    tbit operator[](unsigned idx) const { return pos()[idx]; }        
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
        return *this;
    }
    doc& operator*() { return *d; }
    doc* operator->() { return d; }
    doc* detach() { doc* r = d; d = 0; return r; }
};

#endif /* _DOC_H_ */

