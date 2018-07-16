/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    mpq_inf.h

Abstract:

    MPQ numbers with infinitesimals

Author:

    Leonardo de Moura (leonardo) 2011-06-28

Revision History:

--*/
#ifndef MPQ_INF_H_
#define MPQ_INF_H_

#include "util/mpq.h"
#include "util/hash.h"

typedef std::pair<mpq, mpq> mpq_inf;

template<bool SYNCH = true>
class mpq_inf_manager {
    mpq_manager<SYNCH>   m;
    double               m_inf;
public:
    typedef mpq_inf numeral;

    mpq_inf_manager(double inf = 0.0001) {
        set_inf(inf);
    }

    void set_inf(double inf) {
        m_inf = inf;
    }

    enum inf_kind { NEG=-1, ZERO, POS };
    
    void reset(mpq_inf & a) {
        m.reset(a.first);
        m.reset(a.second);
    }
    
    unsigned hash(mpq_inf const & a) const { return hash_u_u(m.hash(a.first), m.hash(a.second)); }
    
    void del(mpq_inf & a) {
        m.del(a.first);
        m.del(a.second);
    }

    void swap(mpq_inf & a, mpq_inf & b) {
        m.swap(a.first, b.first);
        m.swap(a.second, b.second);
    }

    void set(mpq_inf & a, mpq_inf const & b) {
        m.set(a.first, b.first);
        m.set(a.second, b.second);
    }

    void set(mpq_inf & a, mpq const & r) {
        m.set(a.first, r);
        m.reset(a.second);
    }

    void set(mpq_inf & a, mpq const & r, inf_kind k) {
        m.set(a.first, r);
        switch (k) {
        case NEG:  m.set(a.second, -1); break;
        case ZERO: m.reset(a.second); break;
        case POS:  m.set(a.second, 1); break;
        }
    }

    void set(mpq_inf & a, mpq const & r, mpq const & i) {
        m.set(a.first, r);
        m.set(a.second, i);
    }

    bool is_int(mpq_inf const & a) const { return m.is_int(a.first) && m.is_zero(a.second); }

    bool is_pos(mpq_inf const & a) const { 
        return m.is_pos(a.first) || (m.is_zero(a.first) && m.is_pos(a.second)); 
    }

    bool is_neg(mpq_inf const & a) const { 
        return m.is_neg(a.first) || (m.is_zero(a.first) && m.is_neg(a.second)); 
    }
    
    bool is_rational(mpq_inf const & a) const { return m.is_zero(a.second); }

    void get_rational(mpq_inf const & a, mpq & r) { m.set(r, a.first); }

    void get_infinitesimal(mpq_inf const & a, mpq & r) { m.set(r, a.second); }

    double get_double(mpq_inf const & a) {
        double r = m.get_double(a.first);
        if (m.is_pos(a.second))
            return r + m_inf;
        else if (m.is_neg(a.second))
            return r - m_inf;
        else
            return r;
    }

    bool is_zero(mpq_inf const & a) const {
        return m.is_zero(a.first) && m.is_zero(a.second);
    }

    bool eq(mpq_inf const & a, mpq_inf const & b) {
        return m.eq(a.first, b.first) && m.eq(a.second, b.second);
    }

    bool eq(mpq_inf const & a, mpq const & b) {
        return m.eq(a.first, b) && m.is_zero(a.second);
    }
        
    bool eq(mpq_inf const & a, mpq const & b, inf_kind k) {
        if (!m.eq(a.first, b))
            return false;
        switch (k) {
        case NEG: return m.is_minus_one(a.second); 
        case ZERO: return m.is_zero(a.second);
        case POS: return m.is_one(a.second);
        }
        UNREACHABLE();
        return false;
    }
    
    bool lt(mpq_inf const & a, mpq_inf const & b) {
        return m.lt(a.first, b.first) || (m.lt(a.second, b.second) && m.eq(a.first, b.first));
    }

    bool lt(mpq_inf const & a, mpq const & b) {
        return m.lt(a.first, b) || (m.is_neg(a.second) && m.eq(a.first, b));
    }

    bool lt(mpq_inf const & a, mpq const & b, inf_kind k) {
        if (m.lt(a.first, b))
            return true;
        if (m.eq(a.first, b)) {
            switch (k) {
            case NEG:  return m.lt(a.second, mpq(-1));
            case ZERO: return m.is_neg(a.second);
            case POS:  return m.lt(a.second, mpq(1));
            }
            UNREACHABLE();
        }
        return false;
    }

    bool gt(mpq_inf const & a, mpq_inf const & b) { return lt(b, a); }
    
    bool gt(mpq_inf const & a, mpq const & b) {
        return m.gt(a.first, b) || (m.is_pos(a.second) && m.eq(a.first, b));
    }

    bool gt(mpq_inf const & a, mpq const & b, inf_kind k) {
        if (m.gt(a.first, b))
            return true;
        if (m.eq(a.first, b)) {
            switch (k) {
            case NEG:  return m.gt(a.second, mpq(-1));
            case ZERO: return m.is_pos(a.second);
            case POS:  return m.gt(a.second, mpq(1));
            }
            UNREACHABLE();
        }
        return false;
    }

    bool le(mpq_inf const & a, mpq_inf const & b) { return !gt(a, b); }

    bool le(mpq_inf const & a, mpq const & b) { return !gt(a, b); }

    bool le(mpq_inf const & a, mpq const & b, inf_kind k) { return !gt(a, b, k); }

    bool ge(mpq_inf const & a, mpq_inf const & b) { return !lt(a, b); }

    bool ge(mpq_inf const & a, mpq const & b) { return !lt(a, b); }

    bool ge(mpq_inf const & a, mpq const & b, inf_kind k) { return !lt(a, b, k); }

    void add(mpq_inf const & a, mpq_inf const & b, mpq_inf & c) {
        m.add(a.first, b.first, c.first);
        m.add(a.second, b.second, c.second);
    }

    void sub(mpq_inf const & a, mpq_inf const & b, mpq_inf & c) {
        m.sub(a.first, b.first, c.first);
        m.sub(a.second, b.second, c.second);
    }

    void add(mpq_inf const & a, mpq const & b, mpq_inf & c) {
        m.add(a.first, b, c.first);
        m.set(c.second, a.second);
    }

    void sub(mpq_inf const & a, mpq const & b, mpq_inf & c) {
        m.sub(a.first, b, c.first);
        m.set(c.second, a.second);
    }

    void mul(mpq_inf const & a, mpq const & b, mpq_inf & c) {
        m.mul(a.first, b, c.first);
        m.mul(a.second, b, c.second);
    }

    void mul(mpq_inf const & a, mpz const & b, mpq_inf & c) {
        m.mul(b, a.first, c.first);
        m.mul(b, a.second, c.second);
    }

    void div(mpq_inf const & a, mpq const & b, mpq_inf & c) {
        m.div(a.first, b, c.first);
        m.div(a.second, b, c.second);
    }

    void div(mpq_inf const & a, mpz const & b, mpq_inf & c) {
        m.div(a.first, b,  c.first);
        m.div(a.second, b, c.second);
    }

    void inc(mpq_inf & a) {
        m.inc(a.first);
    }

    void dec(mpq_inf & a) {
        m.dec(a.first);
    }

    void neg(mpq_inf & a) {
        m.neg(a.first);
        m.neg(a.second);
    }

    void abs(mpq_inf & a) {
        if (is_neg(a)) {
            neg(a);
        }
    }

    void ceil(mpq_inf const & a, mpq & b) {
        if (m.is_int(a.first)) {
            // special cases for  k - delta*epsilon where k is an integer
            if (m.is_pos(a.second))
                m.add(a.first, mpq(1), b); // ceil(k + delta*epsilon) --> k+1
            else
                m.set(b, a.first);
        }
        else {
            m.ceil(a.first, b);
        }
    }

    void floor(mpq_inf const & a, mpq & b) {
        if (m.is_int(a.first)) {
            if (m.is_neg(a.first))
                m.sub(a.first, mpq(1), b); // floor(k - delta*epsilon) --> k-1
            else
                m.set(b, a.first);
        }
        else {
            m.floor(a.first, b);
        }
    }

    std::string to_string(mpq_inf const & a);

    void display(std::ostream & out, mpq_inf const & a) {
        out << to_string(a);
    }

    mpq_manager<SYNCH>& get_mpq_manager() { return m; }
};

#ifndef _NO_OMP_
typedef mpq_inf_manager<true>  synch_mpq_inf_manager;
#else
typedef mpq_inf_manager<false> synch_mpq_inf_manager;
#endif
typedef mpq_inf_manager<false> unsynch_mpq_inf_manager;

#endif
