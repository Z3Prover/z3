/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    hilbert_basis.h

Abstract:

    Basic Hilbert Basis computation.

    hilbert_basis computes a Hilbert basis for linear
    homogeneous inequalities over naturals.
    hilbert_sl_basis  computes a semi-linear set over naturals.
    hilbert_isl_basis computes semi-linear sets over integers.

Author:

    Nikolaj Bjorner (nbjorner) 2013-02-09.

Revision History:

--*/

#ifndef _HILBERT_BASIS_H_
#define _HILBERT_BASIS_H_

#include "rational.h"
#include "lbool.h"
#include "statistics.h"

class hilbert_basis {
public:
    typedef rational numeral;
    typedef vector<numeral> num_vector;
private:
    class rational_heap;
    class index;
    class passive;
    class weight_map;
    struct offset_t { 
        unsigned m_offset; 
        offset_t(unsigned o) : m_offset(o) {} 
        offset_t(): m_offset(0) {}
        bool operator<(offset_t const& other) const {
            return m_offset < other.m_offset;
        }        
    };
    enum sign_t { pos, neg, zero };
    struct stats {
        unsigned m_num_subsumptions;
        unsigned m_num_resolves;
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };
    typedef numeral const* values;
    typedef numeral* values_ref;

    vector<num_vector> m_ineqs;
    num_vector         m_store;
    num_vector         m_eval;
    svector<offset_t>  m_basis;
    svector<offset_t>  m_free_list;
    svector<offset_t>  m_active;
    svector<offset_t>  m_zero;
    volatile bool      m_cancel;
    stats              m_stats;
    index*             m_index;
    passive*           m_passive;
    class iterator {
        hilbert_basis const& hb;
        unsigned   m_idx;
    public:
        iterator(hilbert_basis const& hb, unsigned idx): hb(hb), m_idx(idx) {}
        offset_t operator*() const { return hb.m_basis[m_idx]; }
        iterator& operator++() { ++m_idx; return *this; }
        iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
        bool operator==(iterator const& it) const {return m_idx == it.m_idx; }
        bool operator!=(iterator const& it) const {return m_idx != it.m_idx; }
    };

    static offset_t mk_invalid_offset();
    static bool     is_invalid_offset(offset_t offs);
    lbool saturate(num_vector const& ineq);
    void init_basis();
    unsigned get_num_vars() const;
    numeral eval(values val, num_vector const& ineq) const;
    bool is_subsumed(offset_t idx);
    bool is_subsumed(offset_t i, offset_t j) const;
    bool is_geq(values v, values w) const;
    void recycle(offset_t idx);
    sign_t hilbert_basis::get_sign(offset_t idx) const;
    void add_goal(offset_t idx);
    offset_t alloc_vector();
    void resolve(offset_t i, offset_t j, offset_t r);
    iterator begin() const { return iterator(*this,0); }
    iterator end() const { return iterator(*this, m_basis.size()); }

    values vec(offset_t offs) const;
    values_ref vec(offset_t offs);
    numeral const& eval(offset_t o) const { 
        return m_eval[o.m_offset/get_num_vars()]; 
    }
    numeral& eval(offset_t o) { 
        return m_eval[o.m_offset/get_num_vars()]; 
    }
    
    void set_value(offset_t offs, values v);

    void display(std::ostream& out, offset_t o) const;
    void display(std::ostream& out, values v) const;
    void display_ineq(std::ostream& out, num_vector const& v) const;

public:
        
    hilbert_basis();
    ~hilbert_basis();

    void reset();

    // add inequality v*x <= 0
    // add inequality v*x >= 0
    // add equality   v*x = 0

    void add_le(num_vector const& v);
    void add_ge(num_vector const& v);
    void add_eq(num_vector const& v);

    lbool saturate();

    void set_cancel(bool f) { m_cancel = f; }

    void display(std::ostream& out) const;

    void collect_statistics(statistics& st) const;
    void reset_statistics(); 
    
};

class hilbert_sl_basis {
public:
    typedef rational        numeral;
    typedef vector<numeral> num_vector;
private:
    hilbert_basis m_basis;    
public:
    hilbert_sl_basis() {}    
    void reset() { m_basis.reset(); }

    // add inequality v*x >= bound, x ranges over naturals
    void add_le(num_vector const& v, numeral bound);
    lbool saturate() { return m_basis.saturate(); }
    void set_cancel(bool f) { m_basis.set_cancel(f); }
    void display(std::ostream& out) const { m_basis.display(out); }    

    void collect_statistics(statistics& st) const { m_basis.collect_statistics(st); }
    void reset_statistics() { m_basis.reset_statistics(); }
};

class hilbert_isl_basis {
public:
    typedef rational        numeral;
    typedef vector<numeral> num_vector;
private:
    hilbert_basis m_basis;    
public:
    hilbert_isl_basis() {}    
    void reset() { m_basis.reset(); }

    // add inequality v*x >= bound, x ranges over integers
    void add_le(num_vector const& v, numeral bound);
    lbool saturate() { return m_basis.saturate(); }
    void set_cancel(bool f) { m_basis.set_cancel(f); }
    void display(std::ostream& out) const { m_basis.display(out); }    
};

#endif 
