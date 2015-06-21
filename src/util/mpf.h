/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    mpf.h

Abstract:

    Multi Precision Floating Point Numbers

Author:

    Christoph Wintersteiger (cwinter) 2011-12-01.

Revision History:

--*/
#ifndef _MPF_H_
#define _MPF_H_

#include<string>
#include"mpz.h"
#include"mpq.h"
#include"map.h"
#include"scoped_numeral.h"
#include"scoped_numeral_vector.h"
#include"hash.h"

typedef enum {
    MPF_ROUND_NEAREST_TEVEN,
    MPF_ROUND_NEAREST_TAWAY,
    MPF_ROUND_TOWARD_POSITIVE,
    MPF_ROUND_TOWARD_NEGATIVE,
    MPF_ROUND_TOWARD_ZERO
} mpf_rounding_mode;

typedef int64 mpf_exp_t;

class mpf {    
    friend class mpf_manager;
    friend class scoped_mpf;
    unsigned ebits:15;
    unsigned sbits:16;
    unsigned sign:1; // counts as one sbit.
    mpz significand;
    mpf_exp_t exponent;
    mpf & operator=(mpf const & other) { UNREACHABLE(); return *this; }
    void set(unsigned _ebits, unsigned _sbits);
public:    
    mpf();
    mpf(unsigned ebits, unsigned sbits);
    mpf(mpf const & other);
    ~mpf();    
    unsigned get_ebits() const { return ebits; }
    unsigned get_sbits() const { return sbits; }
    void swap(mpf & other);
};

class mpf_manager {
    unsynch_mpq_manager m_mpq_manager;
    unsynch_mpz_manager & m_mpz_manager; // A mpq_manager is a mpz_manager, reusing it.

public:
    typedef mpf numeral;

    mpf_manager();
    ~mpf_manager();

    void reset(mpf & o, unsigned ebits, unsigned sbits) { set(o, ebits, sbits, 0); }
    void set(mpf & o, unsigned ebits, unsigned sbits, int value);
    void set(mpf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, int n, int d);
    void set(mpf & o, unsigned ebits, unsigned sbits, float value);
    void set(mpf & o, unsigned ebits, unsigned sbits, double value);
    void set(mpf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, mpq const & value);
    void set(mpf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, char const * value);
    void set(mpf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, mpq const & significand, mpz const & exponent);
    void set(mpf & o, unsigned ebits, unsigned sbits, bool sign, uint64 significand, mpf_exp_t exponent);
    void set(mpf & o, unsigned ebits, unsigned sbits, bool sign, mpz const & significand, mpf_exp_t exponent);	
    void set(mpf & o, mpf const & x);
    void set(mpf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, mpf const & x);

    void del(mpf & x) {
        m_mpz_manager.del(x.significand);        
    }

    void abs(mpf & o);
    void abs(mpf const & x, mpf & o);

    void neg(mpf & o);
    void neg(mpf const & x, mpf & o);

    bool is_zero(mpf const & x);
    bool is_neg(mpf const & x);
    bool is_pos(mpf const & x);
    bool is_one(mpf const & x);

    bool is_nzero(mpf const & x);
    bool is_pzero(mpf const & x);
    
    // structural eq
    bool eq_core(mpf const & x, mpf const & y) {
        return 
            x.ebits == y.ebits && 
            x.sbits == y.sbits && 
            x.sign == y.sign && 
            m_mpz_manager.eq(x.significand, y.significand) && 
            x.exponent == y.exponent;
    }

    bool eq(mpf const & x, mpf const & y);
    bool lt(mpf const & x, mpf const & y);
    bool lte(mpf const & x, mpf const & y);
    bool le(mpf const & x, mpf const & y) { return lte(x, y); }
    bool gt(mpf const & x, mpf const & y);
    bool gte(mpf const & x, mpf const & y);
    bool ge(mpf const & x, mpf const & y) { return gte(x, y); }

    void add(mpf_rounding_mode rm, mpf const & x, mpf const & y, mpf & o);
    void sub(mpf_rounding_mode rm, mpf const & x, mpf const & y, mpf & o);
    void mul(mpf_rounding_mode rm, mpf const & x, mpf const & y, mpf & o);
    void div(mpf_rounding_mode rm, mpf const & x, mpf const & y, mpf & o);    

    void fused_mul_add(mpf_rounding_mode rm, mpf const & x, mpf const & y, mpf const &z, mpf & o);

    void sqrt(mpf_rounding_mode rm, mpf const & x, mpf & o);

    void round_to_integral(mpf_rounding_mode rm, mpf const & x, mpf & o);

    void rem(mpf const & x, mpf const & y, mpf & o);

    void maximum(mpf const & x, mpf const & y, mpf & o);
    void minimum(mpf const & x, mpf const & y, mpf & o);

    std::string to_string(mpf const & a);
    std::string to_rational_string(mpf const & a);
    void display_decimal(std::ostream & out, mpf const & a, unsigned k);
    void display_smt2(std::ostream & out, mpf const & a, bool decimal);

    // Convert x into a mpq numeral. zm is the manager that owns o.
    void to_rational(mpf const & x, unsynch_mpq_manager & qm, mpq & o);
    void to_rational(mpf const & x, scoped_mpq & o) { to_rational(x, o.m(), o); }

    double to_double(mpf const & x);
    float to_float(mpf const & x);
    
    bool sgn(mpf const & x) const { return x.sign; }
    const mpz & sig(mpf const & x) const { return x.significand; }
    void sig_normalized(mpf const & x, mpz & res) { 
        mpf t;
        set(t, x);
        unpack(t, true);
        mpz_manager().set(res, t.significand);
        del(t);
    }
    const mpf_exp_t & exp(mpf const & x) const { return x.exponent; }
    mpf_exp_t exp_normalized(mpf const & x) { 
        mpf t;
        set(t, x);
        unpack(t, true);
        mpf_exp_t r = t.exponent;
        del(t);
        return r;
    }

    bool is_nan(mpf const & x);
    bool is_inf(mpf const & x);
    bool is_pinf(mpf const & x);
    bool is_ninf(mpf const & x);
    bool is_normal(mpf const & x);
    bool is_denormal(mpf const & x);
    bool is_regular(mpf const & x) { return x.sbits == 0 || is_zero(x) || is_normal(x) || is_denormal(x); }

    bool is_int(mpf const & x);

    void mk_zero(unsigned ebits, unsigned sbits, bool sign, mpf & o);
    void mk_nzero(unsigned ebits, unsigned sbits, mpf & o);
    void mk_pzero(unsigned ebits, unsigned sbits, mpf & o);
    void mk_nan(unsigned ebits, unsigned sbits, mpf & o);
    void mk_inf(unsigned ebits, unsigned sbits, bool sign, mpf & o);
    void mk_pinf(unsigned ebits, unsigned sbits, mpf & o);
    void mk_ninf(unsigned ebits, unsigned sbits, mpf & o);

    std::string to_string_raw(mpf const & a);

    unsynch_mpz_manager & mpz_manager(void) { return m_mpz_manager; }
    unsynch_mpq_manager & mpq_manager(void) { return m_mpq_manager; }

    unsigned hash(mpf const & a) { 
        return hash_u_u(m_mpz_manager.hash(a.significand), 
                        m_mpz_manager.hash(hash_ull(a.exponent))); 
    }

    void mk_max_value(unsigned ebits, unsigned sbits, bool sign, mpf & o);
    mpf_exp_t mk_bot_exp(unsigned ebits);
    mpf_exp_t mk_top_exp(unsigned ebits);
    mpf_exp_t mk_max_exp(unsigned ebits);
    mpf_exp_t mk_min_exp(unsigned ebits);

    mpf_exp_t unbias_exp(unsigned ebits, mpf_exp_t biased_exponent);

    /**
       \brief Return the biggest k s.t. 2^k <= a.
       
       \remark Return 0 if a is not positive.
    */
    unsigned prev_power_of_two(mpf const & a);

    void to_sbv_mpq(mpf_rounding_mode rm, const mpf & x, scoped_mpq & o);

protected:
    void mk_one(unsigned ebits, unsigned sbits, bool sign, mpf & o) const;

    bool has_bot_exp(mpf const & x);
    bool has_top_exp(mpf const & x);

    void unpack(mpf & o, bool normalize);    
    void add_sub(mpf_rounding_mode rm, mpf const & x, mpf const & y, mpf & o, bool sub);
    void round(mpf_rounding_mode rm, mpf & o);
    void round_sqrt(mpf_rounding_mode rm, mpf & o);    

    void mk_round_inf(mpf_rounding_mode rm, mpf & o);    

    // Convert x into a mpz numeral. zm is the manager that owns o.
    void to_mpz(mpf const & x, unsynch_mpz_manager & zm, mpz & o);
    void to_mpz(mpf const & x, scoped_mpz & o) { to_mpz(x, o.m(), o); }    

    class powers2 {
        unsynch_mpz_manager & m;
        u_map<mpz*> m_p;
        u_map<mpz*> m_pn;
        u_map<mpz*> m_pm1;
        u_map<mpz*> m_pm1n;
    public:
        powers2(unsynch_mpz_manager & m) : m(m) {}
        ~powers2() {
            dispose(m_p);
            dispose(m_pn);
            dispose(m_pm1);
            dispose(m_pm1n);            
        }

        void dispose(u_map<mpz*> & map) {
            for (u_map<mpz*>::iterator it = map.begin(); it != map.end(); it++) {
                m.del(*it->m_value);
                dealloc(it->m_value);
            }
        }

        const mpz & operator()(unsigned n, bool negated = false) {
            u_map<mpz*> & map = (negated) ? m_pn : m_p;
            u_map<mpz*>::iterator it = map.find_iterator(n);
            if (it != map.end())
                return *it->m_value;
            else {
                mpz * new_obj = alloc(mpz);
                map.insert(n, new_obj);
                m.power(unsynch_mpz_manager::mk_z(2), n, *new_obj);
                if (negated) m.neg(*new_obj);
                return *new_obj;
            }
        }

        const mpz & m1(unsigned n, bool negated=false) { // (2 ^ n) - 1
            u_map<mpz*> & map = (negated) ? m_pm1n : m_pm1;
            u_map<mpz*>::iterator it = map.find_iterator(n);
            if (it != map.end())
                return *it->m_value;
            else {
                mpz * new_obj = alloc(mpz);
                map.insert(n, new_obj);
                m.power(unsynch_mpz_manager::mk_z(2), n, *new_obj);
                m.dec(*new_obj);
                if (negated) m.neg(*new_obj);
                return *new_obj;
            }            
        }
    };

public:
    powers2 m_powers2;
};

class scoped_mpf : public _scoped_numeral<mpf_manager> {
    friend class mpf_manager;
    mpz & significand() { return get().significand; }
    bool sign() const { return get().sign; }
    mpf_exp_t exponent() const { return get().exponent; }
    unsigned sbits() const { return get().sbits; }
    void set(unsigned ebits, unsigned sbits) { get().set(ebits, sbits); }
public:
    scoped_mpf(mpf_manager & m):_scoped_numeral<mpf_manager>(m) {}
    scoped_mpf(scoped_mpf const & n):_scoped_numeral<mpf_manager>(n) {}
    scoped_mpf(mpf_manager & m, unsigned ebits, unsigned sbits):_scoped_numeral<mpf_manager>(m) { set(ebits, sbits); }
};

typedef _scoped_numeral_vector<mpf_manager> scoped_mpf_vector;

#endif
