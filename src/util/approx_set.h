/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    approx_set.h

Abstract:

    Approximated sets.

Author:

    Leonardo de Moura (leonardo) 2007-03-02.

Revision History:

--*/
#ifndef APPROX_SET_H_
#define APPROX_SET_H_
#include<iostream>
#include "util/debug.h"

template<typename T> class approx_set_traits;

template <> class approx_set_traits<unsigned long long> {
public:
    static const unsigned capacity = 64;
    static const unsigned long long zero = 0ull;
    static const unsigned long long one  = 1ull;
};
static_assert(sizeof(unsigned long long) == 8, "");

template <> class approx_set_traits<unsigned> {
public:
    static const unsigned capacity = 32;
    static const unsigned zero = 0;
    static const unsigned one  = 1;
};
static_assert(sizeof(unsigned) == 4, "unsigned are 4 bytes");

template<typename T, typename T2U_Proc, typename R=unsigned long long>
class approx_set_tpl : private T2U_Proc {
protected:
    R m_set;

    unsigned e2u(T const & e) const { return T2U_Proc::operator()(e); }

    R u2s(unsigned u) const { return (approx_set_traits<R>::one << (u & (approx_set_traits<R>::capacity - 1))); }

    R e2s(T const & e) const { return u2s(e2u(e)); }
    
    static approx_set_tpl r2s(R const & s) { approx_set_tpl r; r.m_set = s; return r; }

public:
    approx_set_tpl():
        m_set(approx_set_traits<R>::zero) {
    }

    explicit approx_set_tpl(T const & e):
        m_set(e2s(e)) {
    }

    approx_set_tpl(unsigned sz, T const * es):
        m_set(approx_set_traits<R>::zero) {
        for (unsigned i = 0; i < sz; i++)
            insert(es[i]);
    }

    approx_set_tpl(approx_set_tpl const & s):
        m_set(s.m_set) {
    }

    void insert(T const & e) {
        m_set |= e2s(e);
    }

    bool may_contain(T const & e) const {
        return (m_set & e2s(e)) != approx_set_traits<R>::zero;
    }
    
    bool must_not_contain(T const & e) const {
        return !may_contain(e); 
    }

    friend inline approx_set_tpl mk_union(approx_set_tpl const & s1, approx_set_tpl const & s2) { 
        return r2s(s1.m_set | s2.m_set); 
    }
    
    friend inline approx_set_tpl mk_intersection(approx_set_tpl const & s1, approx_set_tpl const & s2) { 
        return r2s(s1.m_set & s2.m_set); 
    }

    void operator|=(approx_set_tpl const & other) {
        m_set |= other.m_set;
    }

    void operator&=(approx_set_tpl const & other) {
        m_set &= other.m_set;
    }

    void operator-=(approx_set_tpl const & other) {
        m_set &= ~(other.m_set);
    }

    bool empty() const {
        return m_set == approx_set_traits<R>::zero;
    }

    friend inline bool empty(approx_set_tpl const & s) {
        return s.empty();
    }

    bool must_not_subset(approx_set_tpl const & s2) const {
        return (m_set & ~(s2.m_set)) != approx_set_traits<R>::zero;
    }

    friend inline bool must_not_subset(approx_set_tpl const & s1, approx_set_tpl const & s2) {
        return s1.must_not_subset(s2);
    }

    bool must_not_subsume(approx_set_tpl const & s2) const {
        return must_not_subset(s2);
    }

    friend inline bool must_not_subsume(approx_set_tpl const & s1, approx_set_tpl const & s2) {
        return s1.must_not_subset(s2);
    }

    friend inline bool must_not_eq(approx_set_tpl const & s1, approx_set_tpl const & s2) { return s1.m_set != s2.m_set; }
    
    friend inline bool may_eq(approx_set_tpl const & s1, approx_set_tpl const & s2) { return s1.m_set == s2.m_set; }
    
    /**
       \brief Return if s1 and s2 are the same approximated set.
    */
    bool equiv(approx_set_tpl const & s2) const { return m_set == s2.m_set; }
    friend inline bool equiv(approx_set_tpl const & s1, approx_set_tpl const & s2) { return s1.m_set == s2.m_set; }

    /**
       \brief Return true if the approximation of s1 is a subset of the approximation of s2.
    */
    friend inline bool approx_subset(approx_set_tpl const & s1, approx_set_tpl const & s2) {
        return s2.equiv(mk_union(s1, s2));
    }
    
    void reset() {
        m_set = approx_set_traits<R>::zero;
    }

    bool empty_intersection(approx_set_tpl const & other) const {
        return mk_intersection(*this, other).empty();
    }
};

struct u2u { unsigned operator()(unsigned u) const { return u; } };

typedef approx_set_tpl<unsigned, u2u> u_approx_set;

#define APPROX_SET_CAPACITY (approx_set_traits<unsigned long long>::capacity)

class approx_set : public u_approx_set {
public:
    approx_set():u_approx_set() {}
    approx_set(unsigned e):u_approx_set(e) {}

    class iterator {
        unsigned long long m_set;
        unsigned           m_val;
        void move_to_next() {
            // TODO: this code can be optimized in platforms with special
            // instructions to count leading (trailing) zeros in a word.
            while (m_set > 0) {
                if ((m_set & 1ull) != 0) {
                    return;
                }
                m_val ++;
                m_set = m_set >> 1;
            }
        }
    public:
        iterator(unsigned long long s):
            m_set(s),
            m_val(0) {
            move_to_next();
        }

        unsigned operator*() const {
            return m_val;
        }

        iterator & operator++() {
            m_val++;
            m_set = m_set >> 1;
            move_to_next(); 
            return *this;
        }

        iterator operator++(int) { 
            iterator tmp = *this; 
            ++*this; 
            return tmp; 
        }

        bool operator==(iterator const & it) const { 
            return m_set == it.m_set;
        }
        
        bool operator!=(iterator const & it) const { 
            return m_set != it.m_set; 
        }
    };

    iterator begin() const {
        return iterator(m_set);
    }

    static iterator end() {
        return iterator(0);
    }

    void display(std::ostream & out) const;

    unsigned size() const;
    
    // for backward compatibility
    friend inline bool operator==(approx_set const & s1, approx_set const & s2) { return may_eq(s1, s2); }
};

inline std::ostream & operator<<(std::ostream & out, approx_set const & s) {
    s.display(out);
    return out;
}

#endif /* APPROX_SET_H_ */

