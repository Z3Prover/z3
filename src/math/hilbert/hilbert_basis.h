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

    Hilbert basis can be templatized 
    based on traits that define numeral:
    as rational, mpz, checked_int64 
    (checked or unchecked).

--*/

#ifndef HILBERT_BASIS_H_
#define HILBERT_BASIS_H_

#include "rational.h"
#include "lbool.h"
#include "statistics.h"
#include "checked_int64.h"
#include "rlimit.h"

typedef vector<rational> rational_vector;

class hilbert_basis {

    static const bool check = true;
    typedef checked_int64<check> numeral;
    typedef vector<numeral> num_vector;
    static checked_int64<check> to_numeral(rational const& r) {
        if (!r.is_int64()) {
            throw checked_int64<check>::overflow_exception();
        }
        return checked_int64<check>(r.get_int64());
    }
    static rational to_rational(checked_int64<check> const& i) {
        return rational(i.get_int64(), rational::i64());
    }

    class value_index1;
    class value_index2;
    class value_index3;
    class index;
    class passive;
    class passive2;
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
        values(unsigned offset, numeral* v): m_values(v+offset) { }
        numeral& weight()             { return m_values[-1]; } // value of a*x 
        numeral const& weight() const { return m_values[-1]; } // value of a*x 
        numeral& weight(int i)   { return m_values[-2-i]; } // value of b_i*x for 0 <= i < current inequality. 
        numeral const& weight(int i) const { return m_values[-2-i]; } // value of b_i*x 
        numeral& operator[](unsigned i) { return m_values[i]; } // value of x_i
        numeral const& operator[](unsigned i) const { return m_values[i]; } // value of x_i
        numeral const* operator()() const { return m_values; }
    };

    reslimit&          m_limit;
    vector<num_vector> m_ineqs;      // set of asserted inequalities
    svector<bool>      m_iseq;       // inequalities that are equalities
    num_vector         m_store;      // store of vectors
    svector<offset_t>  m_basis;      // vector of current basis
    svector<offset_t>  m_free_list;  // free list of unused storage
    svector<offset_t>  m_active;     // active set
    svector<offset_t>  m_sos;        // set of support
    svector<offset_t>  m_zero;       // zeros
    passive*           m_passive;    // passive set
    passive2*          m_passive2;   // passive set
    stats              m_stats;
    index*             m_index;      // index of generated vectors
    unsigned_vector    m_ints;       // indices that can be both positive and negative
    unsigned           m_current_ineq;
    
    bool               m_use_support;             // parameter: (associativity) resolve only against vectors that are initially in basis.
    bool               m_use_ordered_support;     // parameter: (commutativity) resolve in order
    bool               m_use_ordered_subsumption; // parameter


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
    lbool saturate_orig(num_vector const& ineq, bool is_eq);
    void init_basis();
    void select_inequality();
    unsigned get_num_nonzeros(num_vector const& ineq);
    unsigned get_ineq_product(num_vector const& ineq);
    numeral   get_ineq_diff(num_vector const& ineq);

    void add_unit_vector(unsigned i, numeral const& e);
    unsigned get_num_vars() const;
    numeral get_weight(values const & val, num_vector const& ineq) const;
    bool is_geq(values const& v, values const& w) const;
    bool is_abs_geq(numeral const& v, numeral const& w) const;
    bool is_subsumed(offset_t idx);
    bool is_subsumed(offset_t i, offset_t j) const;
    void recycle(offset_t idx);
    bool can_resolve(offset_t i, offset_t j, bool check_sign) const;
    sign_t get_sign(offset_t idx) const;
    bool add_goal(offset_t idx);
    bool checkpoint();

    offset_t alloc_vector();
    void resolve(offset_t i, offset_t j, offset_t r);
    iterator begin() const { return iterator(*this,0); }
    iterator end() const { return iterator(*this, m_basis.size()); }

    class vector_lt_t;
    bool vector_lt(offset_t i, offset_t j) const;

    values vec(offset_t offs) const;
    
    void display(std::ostream& out, offset_t o) const;
    void display(std::ostream& out, values const & v) const;
    void display_ineq(std::ostream& out, num_vector const& v, bool is_eq) const;

public:
        
    hilbert_basis(reslimit& rl);
    ~hilbert_basis();

    void reset();

    void set_use_support(bool b) { m_use_support = b; }
    void set_use_ordered_support(bool b) { m_use_ordered_support = b; }
    void set_use_ordered_subsumption(bool b) { m_use_ordered_subsumption = b; }

    // add inequality v*x >= 0
    // add inequality v*x <= 0
    // add equality   v*x = 0
    void add_ge(rational_vector const& v);
    void add_le(rational_vector const& v);
    void add_eq(rational_vector const& v);

    // add inequality v*x >= b
    // add inequality v*x <= b
    // add equality   v*x = b
    void add_ge(rational_vector const& v, rational const& b);
    void add_le(rational_vector const& v, rational const& b);
    void add_eq(rational_vector const& v, rational const& b);

    void set_is_int(unsigned var_index);
    bool get_is_int(unsigned var_index) const;

    lbool saturate();

    unsigned get_basis_size() const { return m_basis.size(); }
    void get_basis_solution(unsigned i, rational_vector& v, bool& is_initial);

    unsigned get_num_ineqs() const { return m_ineqs.size(); }
    void get_ge(unsigned i, rational_vector& v, rational& b, bool& is_eq);    

    void display(std::ostream& out) const;

    void collect_statistics(statistics& st) const;
    void reset_statistics();     

};


#endif 
