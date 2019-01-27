/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    linear_equation.cpp

Abstract:

    Basic infrastructure for managing linear equations of the form:
    
    a_1 * x_1 + ... + a_n * x_n = 0

Author:

    Leonardo de Moura (leonardo) 2011-06-28

Revision History:

--*/
#include "tactic/arith/linear_equation.h"

/**
   \brief Return the position of variable x_i in the linear equation.
   Return UINT_MAX, if the variable is not in the linear_equation.
*/
unsigned linear_equation::pos(unsigned x_i) const {
    int low  = 0;
    int high = m_size - 1;
    while (true) {
        int mid   = low + ((high - low) / 2);
        var x_mid = m_xs[mid];
        if (x_i > x_mid) {
            low = mid + 1;
            if (low > high)
                return UINT_MAX;
        }
        else if (x_i < x_mid) {
            high = mid - 1;
            if (low > high)
                return UINT_MAX;
        }
        else {
            return mid;
        }
    }
}

void linear_equation_manager::display(std::ostream & out, linear_equation const & eq) const {
    unsigned sz = eq.m_size;
    for (unsigned i = 0; i < sz; i++) {
        if (i > 0)
            out << " + ";
        out << m.to_string(eq.m_as[i]) << "*x" << eq.m_xs[i];
    }
    out << " = 0";
}

linear_equation * linear_equation_manager::mk(unsigned sz, mpq * as, var * xs, bool normalized) {
    SASSERT(sz > 1);
    
    // compute lcm of the denominators
    mpz l;
    mpz r;
    m.set(l, as[0].denominator());
    for (unsigned i = 1; i < sz; i++) {
        m.set(r, as[i].denominator());
        m.lcm(r, l, l);
    }
    
    TRACE("linear_equation_mk", tout << "lcm: " << m.to_string(l) << "\n";);
    
    // copy l * as to m_int_buffer.
    m_int_buffer.reset();
    for (unsigned i = 0; i < sz; i++) {
        TRACE("linear_equation_mk", tout << "before as[" << i << "]: " << m.to_string(as[i]) << "\n";);
        m.mul(l, as[i], as[i]);
        TRACE("linear_equation_mk", tout << "after as[" << i << "]: " << m.to_string(as[i]) << "\n";);
        SASSERT(m.is_int(as[i]));
        m_int_buffer.push_back(as[i].numerator());
    }

    linear_equation * new_eq = mk(sz, m_int_buffer.c_ptr(), xs, normalized);
    
    m.del(r);
    m.del(l);

    return new_eq;
}

linear_equation * linear_equation_manager::mk_core(unsigned sz, mpz * as, var * xs) {
    SASSERT(sz > 0);
    DEBUG_CODE({
        for (unsigned i = 1; i < sz; i++) {
            SASSERT(xs[i-1] < xs[i]);
        }
    });

    TRACE("linear_equation_bug", for (unsigned i = 0; i < sz; i++) tout << m.to_string(as[i]) << "*x" << xs[i] << " "; tout << "\n";);
    
    mpz g;
    m.set(g, as[0]);
    for (unsigned i = 1; i < sz; i++) {
        if (m.is_one(g))
            break;
        if (m.is_neg(as[i])) {
            m.neg(as[i]);
            m.gcd(g, as[i], g);
            m.neg(as[i]);
        }
        else {
            m.gcd(g, as[i], g);
        }
    }
    if (!m.is_one(g)) {
        for (unsigned i = 0; i < sz; i++) {
            m.div(as[i], g, as[i]);
        }
    }

    TRACE("linear_equation_bug", 
          tout << "g: " << m.to_string(g) << "\n";
          for (unsigned i = 0; i < sz; i++) tout << m.to_string(as[i]) << "*x" << xs[i] << " "; tout << "\n";);

    m.del(g);

    unsigned obj_sz          = linear_equation::get_obj_size(sz);
    void * mem               = m_allocator.allocate(obj_sz);
    linear_equation * new_eq = new (mem) linear_equation();
    mpz * new_as             = reinterpret_cast<mpz*>(reinterpret_cast<char*>(new_eq) + sizeof(linear_equation));
    double * new_app_as      = reinterpret_cast<double*>(reinterpret_cast<char*>(new_as) + sz * sizeof(mpz));
    var * new_xs             = reinterpret_cast<var *>(reinterpret_cast<char*>(new_app_as) + sz * sizeof(double));
    for (unsigned i = 0; i < sz; i++) {
        new (new_as + i) mpz();
        m.set(new_as[i], as[i]);
        new_app_as[i] = m.get_double(as[i]);
        var x_i   = xs[i];
        new_xs[i] = x_i;
    }
    new_eq->m_size        = sz;
    new_eq->m_as          = new_as;
    new_eq->m_approx_as   = new_app_as;
    new_eq->m_xs          = new_xs;
    return new_eq;
}

linear_equation * linear_equation_manager::mk(unsigned sz, mpz * as, var * xs, bool normalized) {
    if (!normalized) {
        for (unsigned i = 0; i < sz; i++) {
            var x = xs[i];
            m_mark.reserve(x+1, false);
            m_val_buffer.reserve(x+1);
            
            if (m_mark[x]) {
                m.add(m_val_buffer[x], as[i], m_val_buffer[x]);
            }
            else {
                m.set(m_val_buffer[x], as[i]);
                m_mark[x] = true;
            }
        }
        
        unsigned j = 0;
        for (unsigned i = 0; i < sz; i++) {
            var x = xs[i];
            if (m_mark[x]) {
                if (!m.is_zero(m_val_buffer[x])) {
                    xs[j] = xs[i];
                    m.set(as[j], m_val_buffer[x]);
                    j++;
                }
                m_mark[x] = false;
            }
        }
        sz = j;
        if (sz <= 1)
            return nullptr;
    }
    else {
        DEBUG_CODE({
            for (unsigned i = 0; i < sz; i++) {
                var x = xs[i];
                m_mark.reserve(x+1, false);
                SASSERT(!m_mark[x]);
                m_mark[x] = true;
            }
            for (unsigned i = 0; i < sz; i++) {
                var x = xs[i];
                m_mark[x] = false;
            }
        });
    }
    
    for (unsigned i = 0; i < sz; i++) {
        var x = xs[i];
        m_val_buffer.reserve(x+1);
        m.swap(m_val_buffer[x], as[i]);
    }
    std::sort(xs, xs+sz);
    for (unsigned i = 0; i < sz; i++) {
        var x = xs[i];
        m.swap(as[i], m_val_buffer[x]);
    }
    
    return mk_core(sz, as, xs);
}

linear_equation * linear_equation_manager::mk(mpz const & b1, linear_equation const & eq1, mpz const & b2, linear_equation const & eq2) {
    SASSERT(!m.is_zero(b1));
    SASSERT(!m.is_zero(b2));
    mpz tmp, new_a;
    m_int_buffer.reset();
    m_var_buffer.reset();
    unsigned sz1 = eq1.size();
    unsigned sz2 = eq2.size();
    unsigned i1  = 0;
    unsigned i2  = 0;
    while (true) {
        if (i1 == sz1) {
            // copy remaining entries from eq2
            while (i2 < sz2) {
                m_int_buffer.push_back(eq2.a(i2));
                m.mul(m_int_buffer.back(), b2, m_int_buffer.back());
                m_var_buffer.push_back(eq2.x(i2));
                i2++;
            }
            break;
        }
        if (i2 == sz2) {
            // copy remaining entries from eq1
            while (i1 < sz1) {
                m_int_buffer.push_back(eq1.a(i1));
                m.mul(m_int_buffer.back(), b1, m_int_buffer.back());
                m_var_buffer.push_back(eq1.x(i1));
                i1++;
            }
            break;
        }
        var x1 = eq1.x(i1);
        var x2 = eq2.x(i2);
        if (x1 < x2) {
            m_int_buffer.push_back(eq1.a(i1));
            m.mul(m_int_buffer.back(), b1, m_int_buffer.back());
            m_var_buffer.push_back(eq1.x(i1));
            i1++;
        }
        else if (x1 > x2) {
            m_int_buffer.push_back(eq2.a(i2));
            m.mul(m_int_buffer.back(), b2, m_int_buffer.back());
            m_var_buffer.push_back(eq2.x(i2));
            i2++;
        }
        else {
            m.mul(eq1.a(i1), b1, tmp);
            m.addmul(tmp, b2, eq2.a(i2), new_a);
            if (!m.is_zero(new_a)) {
                m_int_buffer.push_back(new_a);
                m_var_buffer.push_back(eq1.x(i1));
            }
            i1++;
            i2++;
        }
    }
    m.del(tmp);
    m.del(new_a);
    SASSERT(m_int_buffer.size() == m_var_buffer.size());
    if (m_int_buffer.empty())
        return nullptr;
    return mk_core(m_int_buffer.size(), m_int_buffer.c_ptr(), m_var_buffer.c_ptr());
}

void linear_equation_manager::del(linear_equation * eq) {
    for (unsigned i = 0; i < eq->m_size; i++) {
        m.del(eq->m_as[i]);
    }
    unsigned obj_sz = linear_equation::get_obj_size(eq->m_size);
    m_allocator.deallocate(obj_sz, eq);
}

