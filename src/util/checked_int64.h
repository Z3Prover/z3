/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    checked_int64.h

Abstract:

    A class for wrapping checked (and unchecked) int64_t operations.
    Note: the mpfx class defines a more general class of fixed-point operations.
    A tradeoff is that it relies on a manager.
    This class several of the most common operations from rational, so
    it can be swapped for rational.

Author:

    Nikolaj Bjorner (nbjorner) 2013-03-25.

Revision History:

--*/

#pragma once

#include "util/z3_exception.h"
#include "util/rational.h"
#include "util/mpn.h"


class overflow_exception : public z3_exception {
    char const* what() const noexcept override { return "checked_int64 overflow/underflow"; }
};

template<bool CHECK>
class checked_int64 {
    int64_t m_value;
    typedef checked_int64 ci;
    
    rational r64(int64_t i) const { return rational(i, rational::i64()); }

public:

    checked_int64(): m_value(0) {}
    checked_int64(int64_t v): m_value(v) {}

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

    int64_t get_int64() const { return m_value; }
    double get_double() const { return (double)m_value; }
    rational to_rational() const { return r64(m_value); }

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
        if (CHECK) {
            uint64_t x = static_cast<uint64_t>(m_value);
            uint64_t y = static_cast<uint64_t>(other.m_value);
            int64_t r = static_cast<int64_t>(x + y);
            if (m_value > 0 && other.m_value > 0 && r <= 0) 
                throw overflow_exception();
            if (m_value < 0 && other.m_value < 0 && r >= 0) 
                throw overflow_exception();
            m_value = r;
        }
        else {
            m_value += other.m_value; 
        }
        return *this;
    }

    checked_int64& operator-=(checked_int64 const& other) {
        if (CHECK) {
            uint64_t x = static_cast<uint64_t>(m_value);
            uint64_t y = static_cast<uint64_t>(other.m_value);
            int64_t r = static_cast<int64_t>(x - y);
            if (m_value > 0 && other.m_value < 0 && r <= 0) 
                throw overflow_exception();
            if (m_value < 0 && other.m_value > 0 && r >= 0) 
                throw overflow_exception();
            m_value = r;            
        }
        else {
            m_value -= other.m_value;
        }
        return *this;
    }

    checked_int64& operator*=(checked_int64 const& other) {
        if (CHECK) {
            if (INT_MIN < m_value && m_value <= INT_MAX && INT_MIN < other.m_value && other.m_value <= INT_MAX) {
                m_value *= other.m_value;
            }
            else if (m_value == 0 || other.m_value == 0 || m_value == 1 || other.m_value == 1) {
                m_value *= other.m_value;
            }
            else if (m_value == INT64_MIN || other.m_value == INT64_MIN)
                throw overflow_exception();
            else {
                uint64_t x = m_value < 0 ? -m_value : m_value;
                uint64_t y = other.m_value < 0 ? -other.m_value : other.m_value;
                uint64_t r = x * y;
                if ((y != 0 && r / y != x) || r > INT64_MAX)
                    throw overflow_exception();
                int64_t old_value = m_value;
                m_value = r;
                if (old_value < 0 && other.m_value > 0)
                    m_value = -m_value;
                else if (old_value > 0 && other.m_value < 0)
                    m_value = -m_value;
            }
        }
        else {
            m_value *= other.m_value; 
        }
        return *this;
    }

    checked_int64& operator/=(checked_int64 const& other) {
        m_value /= other.m_value;
        return *this;
    }

    checked_int64& operator%=(checked_int64 const& other) {
        m_value %= other.m_value;
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
inline bool operator!=(checked_int64<CHECK> const& i1, int64_t const& i2) {
    return !operator==(i1, i2);
}

template<bool CHECK>
inline bool operator>(checked_int64<CHECK> const & i1, checked_int64<CHECK> const & i2) { 
    return operator<(i2, i1); 
}

template<bool CHECK>
inline bool operator>(checked_int64<CHECK> const& i1, int64_t i2) {
    return operator<(i2, i1);
}

template<bool CHECK>
inline bool operator<=(checked_int64<CHECK> const & i1, checked_int64<CHECK> const & i2) { 
    return !operator>(i1, i2); 
}

template<bool CHECK>
inline bool operator<=(checked_int64<CHECK> const& i1, int64_t const& i2) {
    return !operator>(i1, i2);
}

template<bool CHECK>
inline bool operator>=(checked_int64<CHECK> const & i1, checked_int64<CHECK> const & i2) { 
    return !operator<(i1, i2); 
}


template<bool CHECK>
inline bool operator>=(checked_int64<CHECK> const& i1, int64_t const& i2) {
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
inline checked_int64<CHECK> operator+(checked_int64<CHECK> const& a, int64_t const& b) {
    checked_int64<CHECK> result(a);
    checked_int64<CHECK> _b(b);
    result += _b;
    return result;
}

template<bool CHECK>
inline checked_int64<CHECK> operator-(checked_int64<CHECK> const& a, checked_int64<CHECK> const& b) {
    checked_int64<CHECK> result(a);
    result -= b;
    return result;
}

template<bool CHECK>
inline checked_int64<CHECK> operator-(checked_int64<CHECK> const& a, int64_t const& b) {
    checked_int64<CHECK> result(a);
    checked_int64<CHECK> _b(b);
    result -= _b;
    return result;
}

template<bool CHECK>
inline checked_int64<CHECK> operator*(checked_int64<CHECK> const& a, checked_int64<CHECK> const& b) {
    checked_int64<CHECK> result(a);
    result *= b;
    return result;
}

template<bool CHECK>
inline checked_int64<CHECK> operator*(int64_t const& a, checked_int64<CHECK> const& b) {
    checked_int64<CHECK> result(a);
    result *= b;
    return result;
}

template<bool CHECK>
inline checked_int64<CHECK> operator*(checked_int64<CHECK> const& a, int64_t const& b) {
    checked_int64<CHECK> result(a);
    checked_int64<CHECK> _b(b);
    result *= _b;
    return result;
}

template<bool CHECK>
inline checked_int64<CHECK> div(checked_int64<CHECK> const& a, checked_int64<CHECK> const& b) {
    checked_int64<CHECK> result(a);
    result /= b;
    if (a < 0) {
        checked_int64<CHECK> r(a);
        r %= b;
        if (r != 0) {
            if (b < 0)
                result += 1;
            else
                result -= 1;
        }
    }
    return result;
}

template<bool CHECK>
inline checked_int64<CHECK> operator/(checked_int64<CHECK> const& a, checked_int64<CHECK> const& b) {
    checked_int64<CHECK> result(a);
    result /= b;
    return result;
}

template<bool CHECK>
inline checked_int64<CHECK> mod(checked_int64<CHECK> const& a, checked_int64<CHECK> const& b) {
    checked_int64<CHECK> result(a);
    result %= b;
    if (result < 0) {
        if (b > 0)
            result += b;
        else
            result -= b;
    }
    return result;
}

template<bool CHECK>
inline bool divides(checked_int64<CHECK> const& a, checked_int64<CHECK> const& b) {
    return mod(b, a) == 0;
}

template <bool CHECK>
inline checked_int64<CHECK> gcd(checked_int64<CHECK> const& a, checked_int64<CHECK> const& b) {
    checked_int64<CHECK> _a = abs(a);
    checked_int64<CHECK> _b = abs(b);
    if (_a == 0) 
        return _b;
    while (_b != 0) {
        checked_int64<CHECK> r = mod(_a, _b);
        _a = _b;
        _b = r;
    }
    return _a;
}

// Compute the extended GCD such that ax + by = gcd(a,b)
template <bool CHECK>
inline checked_int64<CHECK> gcd(checked_int64<CHECK> const& a, checked_int64<CHECK> const& b,
    checked_int64<CHECK>& x, checked_int64<CHECK>& y) {
    checked_int64<CHECK> _a = a;
    checked_int64<CHECK> _b = b;
    x = 0;
    y = 0;
    checked_int64<CHECK> lastx = 1;
    checked_int64<CHECK> lasty = 0;
    while (_b != 0) {
        checked_int64<CHECK> q = div(_a, _b);
        checked_int64<CHECK> r = mod(_a, _b);
        _a = _b;
        _b = r;
        checked_int64<CHECK> temp = x;
        x = lastx - q * x;
        lastx = temp;
        temp = y;
        y = lasty - q * y;
        lasty = temp;
    }
    return _a;
}
