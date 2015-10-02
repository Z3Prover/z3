/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    mpq.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-06-21.

Revision History:

--*/
#ifndef MPQ_H_
#define MPQ_H_

#include"mpz.h"
#include"trace.h"

class mpq {
    mpz m_num;
    mpz m_den;
    friend class mpq_manager<true>;
    friend class mpq_manager<false>;
    mpq & operator=(mpq const & other) { UNREACHABLE(); return *this; }
public:
    mpq(int v):m_num(v), m_den(1) {}
    mpq():m_den(1) {}
    void swap(mpq & other) { m_num.swap(other.m_num); m_den.swap(other.m_den); }
    mpz const & numerator() const { return m_num; }
    mpz const & denominator() const { return m_den; }
};

inline void swap(mpq & m1, mpq & m2) { m1.swap(m2); }

template<bool SYNCH = true>
class mpq_manager : public mpz_manager<SYNCH> {
    mpz m_n_tmp;
    mpz m_add_tmp1;
    mpz m_add_tmp2;
    mpq m_addmul_tmp;
    mpq m_lt_tmp1;
    mpq m_lt_tmp2;

    void reset_denominator(mpq & a) {
        del(a.m_den);
        a.m_den.m_val = 1;
    }

    void normalize(mpq & a) {
        if (SYNCH) {
            mpz tmp;
            gcd(a.m_num, a.m_den, tmp);
            if (is_one(tmp)) {
                del(tmp);
                return;
            }
            div(a.m_num, tmp, a.m_num);
            div(a.m_den, tmp, a.m_den);
            del(tmp);
        }
        else {
            gcd(a.m_num, a.m_den, m_n_tmp);
            if (is_one(m_n_tmp))
                return;
            div(a.m_num, m_n_tmp, a.m_num);
            div(a.m_den, m_n_tmp, a.m_den);
        }
    }

    void rat_add(mpq const & a, mpq const & b, mpq & c) {
        STRACE("rat_mpq", tout << "[mpq] " << to_string(a) << " + " << to_string(b) << " == ";); 
        if (SYNCH) {
            mpz tmp1, tmp2;
            mul(a.m_num, b.m_den, tmp1);
            mul(b.m_num, a.m_den, tmp2);
            mul(a.m_den, b.m_den, c.m_den);
            add(tmp1, tmp2, c.m_num);
            normalize(c);
            del(tmp1);
            del(tmp2);
        }
        else {
            mul(a.m_num, b.m_den, m_add_tmp1);
            mul(b.m_num, a.m_den, m_add_tmp2);
            mul(a.m_den, b.m_den, c.m_den);
            add(m_add_tmp1, m_add_tmp2, c.m_num);
            normalize(c);
        }
        STRACE("rat_mpq", tout << to_string(c) << "\n";);
    }

    void rat_add(mpq const & a, mpz const & b, mpq & c) {
        STRACE("rat_mpq", tout << "[mpq] " << to_string(a) << " + " << to_string(b) << " == ";); 
        if (SYNCH) {
            mpz tmp1;
            mul(b, a.m_den, tmp1);
            set(c.m_den, a.m_den);
            add(a.m_num, tmp1, c.m_num);
            normalize(c);
            del(tmp1);
        }
        else {
            mul(b, a.m_den, m_add_tmp1);
            set(c.m_den, a.m_den);
            add(a.m_num, m_add_tmp1, c.m_num);
            normalize(c);
        }
        STRACE("rat_mpq", tout << to_string(c) << "\n";);
    }

    void rat_sub(mpq const & a, mpq const & b, mpq & c) {
        STRACE("rat_mpq", tout << "[mpq] " << to_string(a) << " - " << to_string(b) << " == ";); 
        if (SYNCH) {
            mpz tmp1, tmp2;
            mul(a.m_num, b.m_den, tmp1);
            mul(b.m_num, a.m_den, tmp2);
            mul(a.m_den, b.m_den, c.m_den);
            sub(tmp1, tmp2, c.m_num);
            normalize(c);
            del(tmp1);
            del(tmp2);
        }
        else {
            mul(a.m_num, b.m_den, m_add_tmp1);
            mul(b.m_num, a.m_den, m_add_tmp2);
            mul(a.m_den, b.m_den, c.m_den);
            sub(m_add_tmp1, m_add_tmp2, c.m_num);
            normalize(c);
        }
        STRACE("rat_mpq", tout << to_string(c) << "\n";);
    }

    void rat_mul(mpq const & a, mpq const & b, mpq & c) {
        STRACE("rat_mpq", tout << "[mpq] " << to_string(a) << " * " << to_string(b) << " == ";); 
        mul(a.m_num, b.m_num, c.m_num);
        mul(a.m_den, b.m_den, c.m_den);
        normalize(c);
        STRACE("rat_mpq", tout << to_string(c) << "\n";);
    }

    void rat_mul(mpz const & a, mpq const & b, mpq & c) {
        STRACE("rat_mpq", tout << "[mpq] " << to_string(a) << " * " << to_string(b) << " == ";); 
        mul(a, b.m_num, c.m_num);
        set(c.m_den, b.m_den);
        normalize(c);
        STRACE("rat_mpq", tout << to_string(c) << "\n";);
    }

    bool rat_lt(mpq const & a, mpq const & b);

public:
    typedef mpq numeral;
    typedef mpq rational;
    typedef mpz integer;
    static bool precise() { return true; }
    static bool field() { return true; }

    mpq_manager();

    ~mpq_manager();

    void reset(mpz & a) { mpz_manager<SYNCH>::reset(a); }

    void reset(mpq & a) {
        reset(a.m_num);
        reset_denominator(a);
    }

    static bool is_small(mpz const & a) { return mpz_manager<SYNCH>::is_small(a); }

    static bool is_small(mpq const & a) { return is_small(a.m_num) && is_small(a.m_den); }

    static mpq mk_q(int v) { return mpq(v); }

    mpq mk_q(int n, int d) { mpq r; set(r, n, d); return r; }

    void del(mpz & a) { mpz_manager<SYNCH>::del(a); }

    void del(mpq & a) {
        del(a.m_num);
        del(a.m_den);
    }
    
    void get_numerator(mpq const & a, mpz & n) { set(n, a.m_num); }

    void get_denominator(mpq const & a, mpz & d) { set(d, a.m_den); }

    void get_numerator(mpq const & a, mpq & n) { get_numerator(a, n.m_num); reset_denominator(n); }

    void get_denominator(mpq const & a, mpq & d) { get_denominator(a, d.m_num); reset_denominator(d); }

    void neg(mpz & a) { mpz_manager<SYNCH>::neg(a); }
    
    void neg(mpq & a) { mpz_manager<SYNCH>::neg(a.m_num); }

    void abs(mpz & a) { mpz_manager<SYNCH>::abs(a); }

    void abs(mpq & a) { mpz_manager<SYNCH>::abs(a.m_num); }

    static int sign(mpz const & a) { return mpz_manager<SYNCH>::sign(a); }

    static int sign(mpq const & a) { return mpz_manager<SYNCH>::sign(a.m_num); }

    static bool is_pos(mpz const & a) { return mpz_manager<SYNCH>::is_pos(a); }

    static bool is_neg(mpz const & a) { return mpz_manager<SYNCH>::is_neg(a); }

    static bool is_zero(mpz const & a) { return mpz_manager<SYNCH>::is_zero(a); }

    static bool is_nonpos(mpz const & a) { return mpz_manager<SYNCH>::is_nonpos(a); }

    static bool is_nonneg(mpz const & a) { return mpz_manager<SYNCH>::is_nonneg(a); }

    static bool is_pos(mpq const & a) { return is_pos(a.m_num); }

    static bool is_neg(mpq const & a) { return is_neg(a.m_num); }

    static bool is_zero(mpq const & a) { return is_zero(a.m_num); }

    static bool is_nonpos(mpq const & a) { return is_nonpos(a.m_num); }

    static bool is_nonneg(mpq const & a) { return is_nonneg(a.m_num); }

    static bool is_one(mpz const & a) { return mpz_manager<SYNCH>::is_one(a); }
    
    static bool is_one(mpq const & a) { return is_one(a.m_num) && is_one(a.m_den); }

    static bool is_minus_one(mpz const & a) { return mpz_manager<SYNCH>::is_minus_one(a); }
    
    static bool is_minus_one(mpq const & a) { return is_minus_one(a.m_num) && is_one(a.m_den); }

    void floor(mpq const & a, mpz & f);

    void floor(mpq const & a, mpq & f) {
        floor(a, f.m_num);
        reset_denominator(f);
    }

    void ceil(mpq const & a, mpz & f);

    void ceil(mpq const & a, mpq & f) {
        ceil(a, f.m_num);
        reset_denominator(f);
    }
    
    static bool is_int(mpq const & a) { return is_one(a.m_den); }
    
    std::string to_string(mpq const & a) const;
    std::string to_rational_string(numeral const & a) { return to_string(a); }

    std::string to_string(mpz const & a) const { return mpz_manager<SYNCH>::to_string(a); }

    void display(std::ostream & out, mpz const & a) const { return mpz_manager<SYNCH>::display(out, a); }

    void display(std::ostream & out, mpq const & a) const;
    void display_pp(std::ostream & out, mpq const & a) const { display(out, a); }

    void display_smt2(std::ostream & out, mpz const & a, bool decimal) const { return mpz_manager<SYNCH>::display_smt2(out, a, decimal); }

    void display_smt2(std::ostream & out, mpq const & a, bool decimal) const;

    void display_decimal(std::ostream & out, mpq const & a, unsigned prec);

    void add(mpz const & a, mpz const & b, mpz & c) { mpz_manager<SYNCH>::add(a, b, c); }
    
    void add(mpq const & a, mpq const & b, mpq & c) {
        STRACE("mpq", tout << "[mpq] " << to_string(a) << " + " << to_string(b) << " == ";); 
        if (is_int(a) && is_int(b)) {
            mpz_manager<SYNCH>::add(a.m_num, b.m_num, c.m_num);
            reset_denominator(c);
        }
        else
            rat_add(a, b, c);
        STRACE("mpq", tout << to_string(c) << "\n";);
    }

    void add(mpq const & a, mpz const & b, mpq & c) {
        STRACE("mpq", tout << "[mpq] " << to_string(a) << " + " << to_string(b) << " == ";); 
        if (is_int(a)) {
            mpz_manager<SYNCH>::add(a.m_num, b, c.m_num);
            reset_denominator(c);
        }
        else {
            rat_add(a, b, c);
        }
        STRACE("mpq", tout << to_string(c) << "\n";);
    }

    void sub(mpz const & a, mpz const & b, mpz & c) { mpz_manager<SYNCH>::sub(a, b, c); }

    void sub(mpq const & a, mpq const & b, mpq & c) {
        STRACE("mpq", tout << "[mpq] " << to_string(a) << " - " << to_string(b) << " == ";); 
        if (is_int(a) && is_int(b)) {
            mpz_manager<SYNCH>::sub(a.m_num, b.m_num, c.m_num);
            reset_denominator(c);
        }
        else
            rat_sub(a, b, c);
        STRACE("mpq", tout << to_string(c) << "\n";);
    }

    void inc(mpz & a) { mpz_manager<SYNCH>::inc(a); }

    void dec(mpz & a) { mpz_manager<SYNCH>::dec(a); }

    void inc(mpq & a) { add(a, mpz(1), a); }

    void dec(mpq & a) { add(a, mpz(-1), a); }

    void mul(mpz const & a, mpz const & b, mpz & c) { mpz_manager<SYNCH>::mul(a, b, c); }

    void mul(mpz const & a, mpz const & b, mpq & c) { 
        mpz_manager<SYNCH>::mul(a, b, c.m_num);
        reset_denominator(c);
    }

    void mul(mpq const & a, mpq const & b, mpq & c) {
        STRACE("mpq", tout << "[mpq] " << to_string(a) << " * " << to_string(b) << " == ";); 
        if (is_int(a) && is_int(b)) {
            mpz_manager<SYNCH>::mul(a.m_num, b.m_num, c.m_num);
            reset_denominator(c);
        }
        else
            rat_mul(a, b, c);
        STRACE("mpq", tout << to_string(c) << "\n";);
    }

    void mul(mpz const & a, mpq const & b, mpq & c) {
        STRACE("mpq", tout << "[mpq] " << to_string(a) << " * " << to_string(b) << " == ";); 
        if (is_int(b)) {
            mpz_manager<SYNCH>::mul(a, b.m_num, c.m_num);
            reset_denominator(c);
        }
        else
            rat_mul(a, b, c);
        STRACE("mpq", tout << to_string(c) << "\n";);
    }

    void addmul(mpz const & a, mpz const & b, mpz const & c, mpz & d) {
        return mpz_manager<SYNCH>::addmul(a, b, c, d);
    }

    void submul(mpz const & a, mpz const & b, mpz const & c, mpz & d) {
        return mpz_manager<SYNCH>::submul(a, b, c, d);
    }

    // d <- a + b*c
    void addmul(mpq const & a, mpq const & b, mpq const & c, mpq & d) {
        if (is_one(b)) {
            add(a, c, d);
        }
        else if (is_minus_one(b)) {
            sub(a, c, d);
        }
        else {
            if (SYNCH) {
                mpq tmp;
                mul(b,c,tmp);
                add(a,tmp,d);
                del(tmp);
            }
            else {
                mul(b,c,m_addmul_tmp);
                add(a, m_addmul_tmp, d);
            }
        }
    }

    // d <- a + b*c
    void addmul(mpq const & a, mpz const & b, mpq const & c, mpq & d) {
        if (is_one(b)) {
            add(a, c, d);
        }
        else if (is_minus_one(b)) {
            sub(a, c, d);
        }
        else {
            if (SYNCH) {
                mpq tmp;
                mul(b,c,tmp);
                add(a,tmp,d);
                del(tmp);
            }
            else {
                mul(b,c,m_addmul_tmp);
                add(a, m_addmul_tmp, d);
            }
        }
    }


    // d <- a - b*c
    void submul(mpq const & a, mpq const & b, mpq const & c, mpq & d) {
        if (is_one(b)) {
            sub(a, c, d);
        }
        else if (is_minus_one(b)) {
            add(a, c, d);
        }
        else {
            if (SYNCH) {
                mpq tmp;
                mul(b,c,tmp);
                sub(a,tmp,d);
                del(tmp);
            }
            else {
                mul(b,c,m_addmul_tmp);
                sub(a, m_addmul_tmp, d);
            }
        }
    }

    // d <- a - b*c
    void submul(mpq const & a, mpz const & b, mpq const & c, mpq & d) {
        if (is_one(b)) {
            sub(a, c, d);
        }
        else if (is_minus_one(b)) {
            add(a, c, d);
        }
        else {
            if (SYNCH) {
                mpq tmp;
                mul(b,c,tmp);
                sub(a,tmp,d);
                del(tmp);
            }
            else {
                mul(b,c,m_addmul_tmp);
                sub(a, m_addmul_tmp, d);
            }
        }
    }

    void inv(mpq & a) {
        SASSERT(!is_zero(a));
        if (is_neg(a)) {
            neg(a.m_num);
            neg(a.m_den);
        }
        mpz_manager<SYNCH>::swap(a.m_num, a.m_den);
    }

    void inv(mpq const & a, mpq & b) {
        set(b, a);
        inv(b);
    }

    void div(mpq const & a, mpq const & b, mpq & c) {
        STRACE("mpq", tout << "[mpq] " << to_string(a) << " / " << to_string(b) << " == ";); 
        if (&b == &c) {
            mpz tmp; // it is not safe to use c.m_num at this point.
            mul(a.m_num, b.m_den, tmp);
            mul(a.m_den, b.m_num, c.m_den);
            set(c.m_num, tmp);
            del(tmp);
        }
        else {
            mul(a.m_num, b.m_den, c.m_num);
            mul(a.m_den, b.m_num, c.m_den);
        }

        if (mpz_manager<SYNCH>::is_neg(c.m_den)) {
            neg(c.m_num);
            neg(c.m_den);
        }
        normalize(c);
        STRACE("mpq", tout << to_string(c) << "\n";);
    }

    void div(mpq const & a, mpz const & b, mpq & c) {
        STRACE("mpq", tout << "[mpq] " << to_string(a) << " / " << to_string(b) << " == ";); 
        set(c.m_num, a.m_num);
        mul(a.m_den, b, c.m_den);
        if (mpz_manager<SYNCH>::is_neg(b)) {
            neg(c.m_num);
            neg(c.m_den);
        }
        normalize(c);
        STRACE("mpq", tout << to_string(c) << "\n";);
    }

    void acc_div(mpq & a, mpz const & b) {
        STRACE("mpq", tout << "[mpq] " << to_string(a) << " / " << to_string(b) << " == ";); 
        mul(a.m_den, b, a.m_den);
        if (mpz_manager<SYNCH>::is_neg(b)) {
            neg(a.m_num);
            neg(a.m_den);
        }
        normalize(a);
        STRACE("mpq", tout << to_string(a) << "\n";);
    }

    void machine_div(mpz const & a, mpz const & b, mpz & c) { mpz_manager<SYNCH>::machine_div(a, b, c); }

    void div(mpz const & a, mpz const & b, mpz & c) { mpz_manager<SYNCH>::div(a, b, c); }
    
    void rat_div(mpz const & a, mpz const & b, mpq & c) {
        set(c.m_num, a);
        set(c.m_den, b);
        normalize(c);
    }

    void machine_idiv(mpq const & a, mpq const & b, mpq & c) {
        SASSERT(is_int(a) && is_int(b));
        machine_div(a.m_num, b.m_num, c.m_num);
        reset_denominator(c);
    }

    void machine_idiv(mpq const & a, mpq const & b, mpz & c) {
        SASSERT(is_int(a) && is_int(b));
        machine_div(a.m_num, b.m_num, c);
    }

    void idiv(mpq const & a, mpq const & b, mpq & c) {
        SASSERT(is_int(a) && is_int(b));
        div(a.m_num, b.m_num, c.m_num);
        reset_denominator(c);
    }

    void idiv(mpq const & a, mpq const & b, mpz & c) {
        SASSERT(is_int(a) && is_int(b));
        div(a.m_num, b.m_num, c);
    }

    void rem(mpz const & a, mpz const & b, mpz & c) { mpz_manager<SYNCH>::rem(a, b, c); }

    void rem(mpq const & a, mpq const & b, mpq & c) { 
        SASSERT(is_int(a) && is_int(b));
        rem(a.m_num, b.m_num, c.m_num);
        reset_denominator(c);
    }

    void rem(mpq const & a, mpq const & b, mpz & c) { 
        SASSERT(is_int(a) && is_int(b));
        rem(a.m_num, b.m_num, c);
    }

    void mod(mpz const & a, mpz const & b, mpz & c) { mpz_manager<SYNCH>::mod(a, b, c); }

    void mod(mpq const & a, mpq const & b, mpq & c) {
        SASSERT(is_int(a) && is_int(b));
        mod(a.m_num, b.m_num, c.m_num);
        reset_denominator(c);
    }

    void mod(mpq const & a, mpq const & b, mpz & c) {
        SASSERT(is_int(a) && is_int(b));
        mod(a.m_num, b.m_num, c);
    }

    static unsigned hash(mpz const & a) { return mpz_manager<SYNCH>::hash(a); }

    static unsigned hash(mpq const & a) { return hash(a.m_num); }

    bool eq(mpz const & a, mpz const & b) { return mpz_manager<SYNCH>::eq(a, b); }
    
    bool eq(mpq const & a, mpq const & b) {
        return eq(a.m_num, b.m_num) && eq(a.m_den, b.m_den);
    }

    bool lt(mpz const & a, mpz const & b) { return mpz_manager<SYNCH>::lt(a, b); }

    bool lt(mpq const & a, mpq const & b) {
        if (is_int(a) && is_int(b))
            return lt(a.m_num, b.m_num);
        else
            return rat_lt(a, b);
    }

    bool neq(mpz const & a, mpz const & b) { return mpz_manager<SYNCH>::neq(a, b); }

    bool gt(mpz const & a, mpz const & b) { return mpz_manager<SYNCH>::gt(a, b); }

    bool ge(mpz const & a, mpz const & b) { return mpz_manager<SYNCH>::ge(a, b); }

    bool le(mpz const & a, mpz const & b) { return mpz_manager<SYNCH>::le(a, b); }

    bool neq(mpq const & a, mpq const & b) { return !eq(a, b); }

    bool gt(mpq const & a, mpq const & b) { return lt(b, a); }

    bool ge(mpq const & a, mpq const & b) { return !lt(a, b); }

    bool le(mpq const & a, mpq const & b) { return !lt(b, a); }

    void gcd(mpz const & a, mpz const & b, mpz & c) { mpz_manager<SYNCH>::gcd(a, b, c); }

    void gcd(unsigned sz, mpz const * as, mpz & g) { mpz_manager<SYNCH>::gcd(sz, as, g); }

    void gcd(unsigned sz, mpq const * as, mpq & g);
    
    void gcd(mpq const & a, mpq const & b, mpq & c) {
        SASSERT(is_int(a) && is_int(b));
        gcd(a.m_num, b.m_num, c.m_num);
        reset_denominator(c);
    }

    void gcd(mpz const & r1, mpz const & r2, mpz & a, mpz & b, mpz & g) { mpz_manager<SYNCH>::gcd(r1, r2, a, b, g); }

    void gcd(mpq const & r1, mpq const & r2, mpq & a, mpq & b, mpq & g) { 
        SASSERT(is_int(r1) && is_int(r2));
        reset_denominator(a);
        reset_denominator(b);
        reset_denominator(g);
        gcd(r1.m_num, r2.m_num, a.m_num, b.m_num, g.m_num);
    }

    void lcm(mpz const & a, mpz const & b, mpz & c) { mpz_manager<SYNCH>::lcm(a, b, c); }
    
    void lcm(mpq const & a, mpq const & b, mpq & c) {
        SASSERT(is_int(a) && is_int(b));
        lcm(a.m_num, b.m_num, c.m_num);
        reset_denominator(c);
    }
    
    bool divides(mpz const & a, mpz const & b) { return mpz_manager<SYNCH>::divides(a, b); }

    bool divides(mpq const & a, mpq const & b) { 
        SASSERT(is_int(a) && is_int(b));
        return divides(a.m_num, b.m_num);
    }

    void bitwise_or(mpz const & a, mpz const & b, mpz & c) { return mpz_manager<SYNCH>::bitwise_or(a, b, c); }

    void bitwise_or(mpq const & a, mpq const & b, mpq & c) { 
        SASSERT(is_int(a) && is_int(b));
        bitwise_or(a.m_num, b.m_num, c.m_num);
        reset_denominator(c);
    }

    void bitwise_and(mpz const & a, mpz const & b, mpz & c) { return mpz_manager<SYNCH>::bitwise_and(a, b, c); }

    void bitwise_and(mpq const & a, mpq const & b, mpq & c) { 
        SASSERT(is_int(a) && is_int(b));
        bitwise_and(a.m_num, b.m_num, c.m_num);
        reset_denominator(c);
    }

    void bitwise_xor(mpz const & a, mpz const & b, mpz & c) { return mpz_manager<SYNCH>::bitwise_xor(a, b, c); }

    void bitwise_xor(mpq const & a, mpq const & b, mpq & c) { 
        SASSERT(is_int(a) && is_int(b));
        bitwise_xor(a.m_num, b.m_num, c.m_num);
        reset_denominator(c);
    }

    void bitwise_not(unsigned sz, mpz const & a, mpz & c) { return mpz_manager<SYNCH>::bitwise_not(sz, a, c); }

    void bitwise_not(unsigned sz, mpq const & a, mpq & c) { 
        SASSERT(is_int(a));
        bitwise_not(sz, a.m_num, c.m_num);
        reset_denominator(c);
    }

    void set(mpz & target, mpz const & source) { mpz_manager<SYNCH>::set(target, source); }

    void set(mpq & target, mpq const & source) {
        set(target.m_num, source.m_num);
        set(target.m_den, source.m_den);
    }

    void set(mpz & a, int val) { mpz_manager<SYNCH>::set(a, val); }

    void set(mpq & a, int val) {
        set(a.m_num, val);
        reset_denominator(a);
    }

    void set(mpq & a, int n, int d) {
        SASSERT(d != 0);
        if (d < 0) {
            n = -n;
            d = -d;
        }
        set(a.m_num, n);
        set(a.m_den, d);
        normalize(a);
    }

    void set(mpq & a, int64 n, uint64 d) {
        SASSERT(d != 0);
        set(a.m_num, n);
        set(a.m_den, d);
        normalize(a);
    }
    
    void set(mpq & a, mpz const & n, mpz const & d) {
        if (is_neg(d)) {
            set(a.m_num, n);
            set(a.m_den, d);
            neg(a.m_num);
            neg(a.m_den);
        }
        else {
            set(a.m_num, n);
            set(a.m_den, d);
        }
        normalize(a);
    }

    void set(mpz & a, unsigned val) { mpz_manager<SYNCH>::set(a, val); }

    void set(mpq & a, unsigned val) { 
        set(a.m_num, val);
        reset_denominator(a);
    }

    void set(mpz & a, char const * val) { mpz_manager<SYNCH>::set(a, val); }

    void set(mpq & a, char const * val);

    void set(mpz & a, int64 val) { mpz_manager<SYNCH>::set(a, val); }

    void set(mpq & a, int64 val) {
        set(a.m_num, val);
        reset_denominator(a);
    }

    void set(mpz & a, uint64 val) { mpz_manager<SYNCH>::set(a, val); }
    
    void set(mpq & a, uint64 val) { 
        set(a.m_num, val);
        reset_denominator(a);
    }
    
    void set(mpq & a, mpz const & val) {
        mpz_manager<SYNCH>::set(a.m_num, val);
        reset_denominator(a);
    }

    void set(mpz & a, unsigned sz, digit_t const * digits) { mpz_manager<SYNCH>::set(a, sz, digits); }

    void set(mpq & a, unsigned sz, digit_t const * digits) { 
        mpz_manager<SYNCH>::set(a.m_num, sz, digits); 
        reset_denominator(a); 
    }

    void swap(mpz & a, mpz & b) { mpz_manager<SYNCH>::swap(a, b); }

    void swap(mpq & a, mpq & b) {
        swap(a.m_num, b.m_num);
        swap(a.m_den, b.m_den);
    }

    void swap_numerator(mpz & a, mpq & b) {
        swap(a, b.m_num);
    }

    bool is_uint64(mpz const & a) const { return mpz_manager<SYNCH>::is_uint64(a); }

    bool is_int64(mpz const & a) const { return mpz_manager<SYNCH>::is_int64(a); }

    uint64 get_uint64(mpz const & a) const { return mpz_manager<SYNCH>::get_uint64(a); }

    int64 get_int64(mpz const & a) const { return mpz_manager<SYNCH>::get_int64(a); }

    bool is_uint64(mpq const & a) const { return is_int(a) && is_uint64(a.m_num); }

    bool is_int64(mpq const & a) const { return is_int(a) && is_int64(a.m_num); }

    uint64 get_uint64(mpq const & a) const { SASSERT(is_uint64(a)); return get_uint64(a.m_num); }

    int64 get_int64(mpq const & a) const { SASSERT(is_int64(a)); return get_int64(a.m_num); }

    double get_double(mpz const & a) const { return mpz_manager<SYNCH>::get_double(a); }

    double get_double(mpq const & a) const;

    void power(mpz const & a, unsigned p, mpz & b) { mpz_manager<SYNCH>::power(a, p, b); }

    void power(mpq const & a, unsigned p, mpq & b);

    bool is_power_of_two(mpz const & a, unsigned & shift) { return mpz_manager<SYNCH>::is_power_of_two(a, shift); }

    bool is_power_of_two(mpq const & a, unsigned & shift) { return is_int(a) && is_power_of_two(a.m_num, shift); }

    unsigned bitsize(mpz const & a) { return mpz_manager<SYNCH>::bitsize(a); }
    unsigned bitsize(mpq const & a) { return is_int(a) ? bitsize(a.m_num) : bitsize(a.m_num) + bitsize(a.m_den); }

    /**
       \brief Return true if the number is a perfect square, and 
       store the square root in 'root'.
       If the number n is positive and the result is false, then
       root will contain the smallest integer r such that r*r > n.
    */
    bool is_perfect_square(mpz const & a, mpz & r) { return mpz_manager<SYNCH>::is_perfect_square(a, r); }

    /**
       \brief Return true if the numerator and denominators are perfect squares.
       Store the square root in root.
       If the result is false, then the value of root should be ignored.
    */
    bool is_perfect_square(mpq const & a, mpq & r) {
        if (is_int(a)) {
            reset_denominator(r);
            return is_perfect_square(a.m_num, r.m_num);
        }
        if (is_perfect_square(a.m_num, r.m_num) && is_perfect_square(a.m_den, r.m_den)) {
            normalize(r);
            return true;
        }
        return false;
    }

    bool root(mpz & a, unsigned n) { return mpz_manager<SYNCH>::root(a, n); }
    bool root(mpz const & a, unsigned n, mpz & r) { return mpz_manager<SYNCH>::root(a, n, r); }

    /**
       \brief Return true if n-th root of a is rational, and store result in r.
    */
    bool root(mpq const & a, unsigned n, mpq & r);

    /**
       \brief Return the biggest k s.t. 2^k <= a.
       
       \remark Return 0 if a is not positive.
    */
    unsigned prev_power_of_two(mpz const & a) { return mpz_manager<SYNCH>::prev_power_of_two(a); }
    unsigned prev_power_of_two(mpq const & a);

    bool is_int_perfect_square(mpq const & a, mpq & r) {
        SASSERT(is_int(a));
        reset_denominator(r);
        return is_perfect_square(a.m_num, r.m_num);
    }

    bool is_even(mpz const & a) { return mpz_manager<SYNCH>::is_even(a); }

    bool is_even(mpq const & a) { return is_int(a) && is_even(a.m_num); }

};

typedef mpq_manager<true> synch_mpq_manager;
typedef mpq_manager<false> unsynch_mpq_manager;

typedef _scoped_numeral<unsynch_mpq_manager> scoped_mpq;
typedef _scoped_numeral<synch_mpq_manager> scoped_synch_mpq;
typedef _scoped_numeral_vector<unsynch_mpq_manager> scoped_mpq_vector;

#endif /* MPQ_H_ */

