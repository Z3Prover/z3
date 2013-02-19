/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    hilbert_basis.h

Abstract:

    Basic Hilbert Basis computation.

    hilbert_basis computes a Hilbert basis for linear
    homogeneous inequalities over naturals.

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
    class value_index1;
    class value_index2;
    class index;
    class passive;
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
        unsigned m_num_saturations;
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };
    class values {
        numeral* m_values;
    public:
        values(numeral* v):m_values(v) {}
        numeral& weight() { return m_values[0]; } // value of a*x 
        numeral& operator[](unsigned i) { return m_values[i+1]; } // value of x_i
        numeral const& weight() const { return m_values[0]; } // value of a*x 
        numeral const& operator[](unsigned i) const { return m_values[i+1]; } // value of x_i
        numeral const* operator()() const { return m_values + 1; }
    };

    vector<num_vector> m_ineqs;      // set of asserted inequalities
    svector<bool>      m_iseq;       // inequalities that are equalities
    num_vector         m_store;      // store of vectors
    svector<offset_t>  m_basis;      // vector of current basis
    svector<offset_t>  m_free_list;  // free list of unused storage
    svector<offset_t>  m_active;     // active set
    svector<offset_t>  m_zero;       // zeros
    passive*           m_passive;    // passive set
    volatile bool      m_cancel;     
    stats              m_stats;
    index*             m_index;      // index of generated vectors
    unsigned_vector    m_ints;       // indices that can be both positive and negative
    unsigned           m_current_ineq;
    class iterator {
        hilbert_basis const& hb;
        unsigned             m_idx;
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
    lbool saturate(num_vector const& ineq, bool is_eq);
    void init_basis();
    void select_inequality();
    unsigned get_num_nonzeros(num_vector const& ineq);
    unsigned get_ineq_product(num_vector const& ineq);

    void add_unit_vector(unsigned i, numeral const& e);
    unsigned get_num_vars() const;
    numeral get_weight(values const & val, num_vector const& ineq) const;
    bool is_geq(values const& v, values const& w) const;
    static bool is_abs_geq(numeral const& v, numeral const& w);
    bool is_subsumed(offset_t idx);
    bool is_subsumed(offset_t i, offset_t j) const;
    void recycle(offset_t idx);
    bool can_resolve(offset_t i, offset_t j) const;
    sign_t get_sign(offset_t idx) const;
    void add_goal(offset_t idx);
    offset_t alloc_vector();
    void resolve(offset_t i, offset_t j, offset_t r);
    iterator begin() const { return iterator(*this,0); }
    iterator end() const { return iterator(*this, m_basis.size()); }

    values vec(offset_t offs) const;
    
    void display(std::ostream& out, offset_t o) const;
    void display(std::ostream& out, values const & v) const;
    void display_ineq(std::ostream& out, num_vector const& v, bool is_eq) const;

public:
        
    hilbert_basis();
    ~hilbert_basis();

    void reset();

    // add inequality v*x >= 0
    // add inequality v*x <= 0
    // add equality   v*x = 0
    void add_ge(num_vector const& v);
    void add_le(num_vector const& v);
    void add_eq(num_vector const& v);

    // add inequality v*x >= b
    // add inequality v*x <= b
    // add equality   v*x = b
    void add_ge(num_vector const& v, numeral const& b);
    void add_le(num_vector const& v, numeral const& b);
    void add_eq(num_vector const& v, numeral const& b);

    void set_is_int(unsigned var_index);
    bool get_is_int(unsigned var_index) const;

    lbool saturate();

    unsigned get_basis_size() const { return m_basis.size(); }
    void get_basis_solution(unsigned i, num_vector& v, bool& is_initial);

    unsigned get_num_ineqs() const { return m_ineqs.size(); }
    void get_ge(unsigned i, num_vector& v, numeral& b, bool& is_eq);    

    void set_cancel(bool f) { m_cancel = f; }

    void display(std::ostream& out) const;

    void collect_statistics(statistics& st) const;
    void reset_statistics();     

};


#endif 
