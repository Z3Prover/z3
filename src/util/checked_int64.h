/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    checked_int64.h

Abstract:

    A class for wrapping checked (and unchecked) int64 operations.
    Note: the mpfx class defines a more general class of fixed-point operations.
    A tradeoff is that it relies on a manager.
    This class several of the most common operations from rational, so
    it can be swapped for rational.

Author:

    Nikolaj Bjorner (nbjorner) 2013-03-25.

Revision History:

--*/

#ifndef CHECKED_INT64_H_
#define CHECKED_INT64_H_

#include"z3_exception.h"
#include"rational.h"

template<bool CHECK>
class checked_int64 {
    int64 m_value;
    typedef checked_int64 ci;
    
    rational r64(int64 i) { return rational(i, rational::i64()); }

public:

    checked_int64(): m_value(0) {}
    checked_int64(int64 v): m_value(v) {}
    checked_int64(checked_int64 const& other) { m_value = other.m_value; }

    class overflow_exception : public z3_exception {
        virtual char const * msg() const { return "checked_int64 overflow/underflow";}
    };

    bool is_zero() const { return m_value == 0; }
    bool is_pos() const { return m_value > 0; }
    bool is_neg() const { return m_value < 0; }
    bool is_one() const { return m_value == 1; }
    bool is_minus_one() const { return m_value == -1; }
    bool is_nonneg() const { return m_value >= 0; }
    bool is_nonpos() const { return m_value <= 0; }
    bool is_even() const { return 0 == (m_value ^ 0x1); }
    
    static checked_int64 zero() { return ci(0); }
    static checked_int64 one() { return ci(1); }
    static checked_int64 minus_one() { return ci(-1);}

    int64 get_int64() const { return m_value; }

    checked_int64 abs() const { 
        if (m_value >= 0) {
            return *this; 
        }
        if (CHECK && m_value == INT64_MIN) {
            throw overflow_exception();
        }                    
        return ci(-m_value);
    } 

    checked_int64& neg() { 
        if (CHECK && m_value == INT64_MIN) {
            throw overflow_exception();
        }                    
        m_value = -m_value; 
        return *this; 
    } 

    unsigned hash() const { return static_cast<unsigned>(m_value); } 

    struct hash_proc {  unsigned operator()(checked_int64 const& r) const { return r.hash(); }  };

    struct eq_proc { bool operator()(checked_int64 const& r1, checked_int64 const& r2) const { return r1 == r2; } };

    friend inline std::ostream& operator<<(std::ostream& out, checked_int64 const& i) {
        return out << i.m_value;
    }

    friend inline bool operator==(checked_int64 const& a, checked_int64 const& b) {
        return a.m_value == b.m_value;
    }

    friend inline bool operator<(checked_int64 const& a, checked_int64 const& b) {
        return a.m_value < b.m_value;
    }
    
    checked_int64 & operator++() {
        if (CHECK && INT64_MAX == m_value) {
            throw overflow_exception();
        }
        ++m_value;
        return *this;
    }

    const checked_int64 operator++(int) { checked_int64 tmp(*this); ++(*this); return tmp; }
    
    checked_int64 & operator--() {
        if (CHECK && m_value == INT64_MIN) {
            throw overflow_exception();
        }                    
        --m_value;
        return *this;
    }
    
    const checked_int64 operator--(int) { checked_int64 tmp(*this); --(*this); return tmp; }

    checked_int64& operator+=(checked_int64 const& other) { 
        if (CHECK && m_value > 0 && other.m_value > 0 &&
            (m_value > INT_MAX || other.m_value > INT_MAX)) {
            rational r(r64(m_value) + r64(other.m_value));
            if (!r.is_int64()) {
                throw overflow_exception();
            }
            m_value = r.get_int64();
            return *this;
        }
        if (CHECK && m_value < 0 && other.m_value < 0 &&
            (m_value < INT_MIN || other.m_value < INT_MIN)) {
            rational r(r64(m_value) + r64(other.m_value));
            if (!r.is_int64()) {
                throw overflow_exception();
            }
            m_value = r.get_int64();
            return *this;
        }
        m_value += other.m_value; 
        return *this;
    }

    checked_int64& operator-=(checked_int64 const& other) {
        if (CHECK && m_value > 0 && other.m_value < 0 &&
            (m_value > INT_MAX || other.m_value < INT_MIN)) {
            rational r(r64(m_value) - r64(other.m_value));
            if (!r.is_int64()) {
                throw overflow_exception();
            }
            m_value = r.get_int64();
            return *this;
        }
        if (CHECK && m_value < 0 && other.m_value > 0 &&
            (m_value < INT_MIN || other.m_value > INT_MAX)) {
            rational r(r64(m_value) - r64(other.m_value));
            if (!r.is_int64()) {
                throw overflow_exception();
            }
            m_value = r.get_int64();
            return *this;
        }
        m_value -= other.m_value;
        return *this;
    }

    checked_int64& operator*=(checked_int64 const& other) {
        if (CHECK) {
            rational r(r64(m_value) * r64(other.m_value));
            if (!r.is_int64()) {
                throw overflow_exception();
            }
            m_value = r.get_int64();
        }
        else {
            m_value *= other.m_value; 
        }
        return *this;
    }

    friend inline checked_int64 abs(checked_int64 const& i) {
        return i.abs();
    }
        
};

template<bool CHECK>
inline bool operator!=(checked_int64<CHECK> const & i1, checked_int64<CHECK> const & i2) { 
    return !operator==(i1, i2); 
}

template<bool CHECK>
inline bool operator>(checked_int64<CHECK> const & i1, checked_int64<CHECK> const & i2) { 
    return operator<(i2, i1); 
}

template<bool CHECK>
inline bool operator<=(checked_int64<CHECK> const & i1, checked_int64<CHECK> const & i2) { 
    return !operator>(i1, i2); 
}

template<bool CHECK>
inline bool operator>=(checked_int64<CHECK> const & i1, checked_int64<CHECK> const & i2) { 
    return !operator<(i1, i2); 
}

template<bool CHECK>
inline checked_int64<CHECK> operator-(checked_int64<CHECK> const& i) {
    checked_int64<CHECK> result(i);
    return result.neg();
}

template<bool CHECK>
inline checked_int64<CHECK> operator+(checked_int64<CHECK> const& a, checked_int64<CHECK> const& b) {
    checked_int64<CHECK> result(a);
    result += b;
    return result;
}

template<bool CHECK>
inline checked_int64<CHECK> operator-(checked_int64<CHECK> const& a, checked_int64<CHECK> const& b) {
    checked_int64<CHECK> result(a);
    result -= b;
    return result;
}

template<bool CHECK>
inline checked_int64<CHECK> operator*(checked_int64<CHECK> const& a, checked_int64<CHECK> const& b) {
    checked_int64<CHECK> result(a);
    result *= b;
    return result;
}

#endif
