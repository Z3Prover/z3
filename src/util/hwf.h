/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    hwf.h

Abstract:

    Hardware Floating Point Numbers

Author:

    Christoph Wintersteiger (cwinter) 2012-07-30.

Revision History:

--*/
#ifndef HWF_H_
#define HWF_H_

#include<string>
#include"mpz.h"
#include"mpq.h"
#include"mpf.h" // we use the same rounding modes as mpf's

class hwf {
    friend class hwf_manager;
    double value;
    hwf & operator=(hwf const & other) { UNREACHABLE(); return *this; }
    uint64 get_raw() const {
      uint64 n;
      SASSERT(sizeof(n) == sizeof(value));
      memcpy(&n, &value, sizeof(value));
      return n;
    }

public:    
    hwf() {}
    hwf(hwf const & other) { this->value = other.value; }
    ~hwf() {}   
    void swap(hwf & other) { double t = value; value = other.value; other.value = t; }
};


class hwf_manager {
    unsynch_mpq_manager m_mpq_manager;
    unsynch_mpz_manager & m_mpz_manager; // A mpq_manager is a mpz_manager, reusing it.

public:
    typedef hwf numeral;
    hwf_manager();
    ~hwf_manager();

    void reset(hwf & o) { set(o, 0); }
    void set(hwf & o, int value);
    void set(hwf & o, mpf_rounding_mode rm, int n, int d);
    void set(hwf & o, float value);
    void set(hwf & o, double value);
    void set(hwf & o, mpf_rounding_mode rm, mpq const & value);
    void set(hwf & o, mpf_rounding_mode rm, char const * value);
    void set(hwf & o, mpf_rounding_mode rm, mpq const & significand, mpz const & exponent);
    void set(hwf & o, bool sign, uint64 significand, int exponent);
    void set(hwf & o, hwf const & x);
    
    // auxiliary methods to make the interface compatible with mpf
    void reset(hwf & o, unsigned ebits, unsigned sbits) { set(o, 0); }
    void set(hwf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, mpq const & value) { set(o, rm, value); }
    void set(hwf & o, unsigned ebits, unsigned sbits, int value) { set(o, value); }
    void set(hwf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, int n, int d) { set(o, rm, n, d); }
    void set(hwf & o, unsigned ebits, unsigned sbits, float value) { set(o, value); }
    void set(hwf & o, unsigned ebits, unsigned sbits, double value) { set(o, value); }
    

    void del(hwf & x) {}

    void abs(hwf & o);
    void abs(hwf const & x, hwf & o);

    void neg(hwf & o);
    void neg(hwf const & x, hwf & o);

    bool is_zero(hwf const & x);
    bool is_neg(hwf const & x);
    bool is_pos(hwf const & x);

    bool is_nzero(hwf const & x);
    bool is_pzero(hwf const & x);

    bool is_one(hwf const & x);

    bool eq(hwf const & x, hwf const & y);
    bool lt(hwf const & x, hwf const & y);
    bool lte(hwf const & x, hwf const & y);
    bool le(hwf const & x, hwf const & y) { return lte(x, y); }
    bool gt(hwf const & x, hwf const & y);
    bool gte(hwf const & x, hwf const & y);
    bool ge(hwf const & x, hwf const & y) { return gte(x, y); }

    void add(mpf_rounding_mode rm, hwf const & x, hwf const & y, hwf & o);
    void sub(mpf_rounding_mode rm, hwf const & x, hwf const & y, hwf & o);
    void mul(mpf_rounding_mode rm, hwf const & x, hwf const & y, hwf & o);
    void div(mpf_rounding_mode rm, hwf const & x, hwf const & y, hwf & o);    

    void fma(mpf_rounding_mode rm, hwf const & x, hwf const & y, hwf const &z, hwf & o);

    void sqrt(mpf_rounding_mode rm, hwf const & x, hwf & o);

    void round_to_integral(mpf_rounding_mode rm, hwf const & x, hwf & o);

    void rem(hwf const & x, hwf const & y, hwf & o);

    void maximum(hwf const & x, hwf const & y, hwf & o);
    void minimum(hwf const & x, hwf const & y, hwf & o);

    std::string to_string(hwf const & a);
    std::string to_rational_string(hwf const & a);
    void display_decimal(std::ostream & out, hwf const & a, unsigned k);
    void display_smt2(std::ostream & out, hwf const & a, bool decimal);
    
    double to_double(hwf const & x) { return x.value; }
    float to_float(hwf const & x) { return (float) x.value; }
    void to_rational(hwf const & x, unsynch_mpq_manager & qm, mpq & o);
    void to_rational(hwf const & x, scoped_mpq & o) { to_rational(x, o.m(), o); }
    
    
    bool sgn(hwf const & x) const {
        return (x.get_raw() & 0x8000000000000000ull) != 0; 
    }

    uint64 sig(hwf const & x) const {
        return x.get_raw() & 0x000FFFFFFFFFFFFFull;
    }

    int exp(hwf const & x) const {
        return ((x.get_raw() & 0x7FF0000000000000ull) >> 52) - 1023;
    }

    bool is_nan(hwf const & x);
    bool is_inf(hwf const & x);
    bool is_pinf(hwf const & x);
    bool is_ninf(hwf const & x);
    bool is_normal(hwf const & x);
    bool is_denormal(hwf const & x);
    bool is_regular(hwf const & x);
    bool is_int(hwf const & x);

    void mk_zero(bool sign, hwf & o);
    void mk_nzero(hwf & o);
    void mk_pzero(hwf & o);
    void mk_nan(hwf & o);
    void mk_inf(bool sign, hwf & o);
    void mk_pinf(hwf & o);
    void mk_ninf(hwf & o);
    
    unsigned hash(hwf const & a) { return hash_ull(a.get_raw()); }

    inline void set_rounding_mode(mpf_rounding_mode rm);

    /**
       \brief Return the biggest k s.t. 2^k <= a.
       
       \remark Return 0 if a is not positive.
    */
    unsigned prev_power_of_two(hwf const & a);

protected:
#ifdef _WINDOWS
    unsigned x86_state, sse2_state;
#endif
};

typedef _scoped_numeral<hwf_manager> scoped_hwf;
typedef _scoped_numeral_vector<hwf_manager> scoped_hwf_vector;

#endif
