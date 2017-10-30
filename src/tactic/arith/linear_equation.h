/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    linear_equation.h

Abstract:

    Basic infrastructure for managing linear equations of the form:
    
    a_1 * x_1 + ... + a_n * x_n = 0

Author:

    Leonardo de Moura (leonardo) 2011-06-28

Revision History:

--*/
#ifndef LINEAR_EQUATION_H_
#define LINEAR_EQUATION_H_

#include "util/mpq.h"
#include "util/small_object_allocator.h"
#include "util/numeral_buffer.h"
#include "util/double_manager.h"

class linear_equation {
public:
    typedef unsigned var;
private:
    static unsigned get_obj_size(unsigned sz) { return sizeof(linear_equation) + sz * (sizeof(mpz) + sizeof(double) + sizeof(var)); }
    friend class linear_equation_manager;
    unsigned   m_size;
    mpz *      m_as;        // precise coefficients
    double *   m_approx_as; // approximated coefficients
    var *      m_xs;        // var ids
    linear_equation() {}
public:
    unsigned size() const { return m_size; }
    mpz const & a(unsigned idx) const { SASSERT(idx < m_size); return m_as[idx]; }
    double approx_a(unsigned idx) const { SASSERT(idx < m_size); return m_approx_as[idx]; }
    var x(unsigned idx) const { SASSERT(idx < m_size); return m_xs[idx]; }
    unsigned pos(unsigned x_i) const;
    void get_a(double_manager & m, unsigned idx, double & r) const { r = m_approx_as[idx]; }
    template<typename NumManager>
    void get_a(NumManager & m, unsigned idx, mpq & r) const { m.set(r, m_as[idx]); }
    template<typename NumManager>
    void get_a(NumManager & m, unsigned idx, mpz & r) const { m.set(r, m_as[idx]); }
};

class linear_equation_manager {
public:
    typedef unsynch_mpq_manager numeral_manager;
    typedef linear_equation::var var;
    typedef numeral_buffer<mpz, numeral_manager> mpz_buffer;
private:
    typedef svector<var>      var_buffer;

    small_object_allocator &  m_allocator;
    numeral_manager &         m;
    mpz_buffer                m_int_buffer;
    mpz_buffer                m_val_buffer;
    char_vector               m_mark;
    var_buffer                m_var_buffer;

    linear_equation * mk_core(unsigned sz, mpz * as, var * xs);

public:
    linear_equation_manager(numeral_manager & _m, small_object_allocator & a):m_allocator(a), m(_m), m_int_buffer(m), m_val_buffer(m) {}
    ~linear_equation_manager() {}

    linear_equation * mk(unsigned sz, mpq * as, var * xs, bool normalized = false);
    linear_equation * mk(unsigned sz, mpz * as, var * xs, bool normalized = false);
    void del(linear_equation * eq);

    // Return b1 * eq1 + b2 * eq2
    // return 0 if the b1 * eq1 + b2 * eq2 == 0
    linear_equation * mk(mpz const & b1, linear_equation const & eq1, mpz const & b2, linear_equation const & eq2);
    
    void display(std::ostream & out, linear_equation const & eq) const;
};

#endif
