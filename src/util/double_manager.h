/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    double_manager.h

Abstract:

    Simulates mpq interface using doubles

Author:

    Leonardo de Moura (leonardo) 2011-06-09.

Revision History:

--*/
#ifndef DOUBLE_MANAGER_H_
#define DOUBLE_MANAGER_H_

#include<cmath>
#include<string>
#include<sstream>
#include<iomanip>
#include "util/util.h"
#include "util/debug.h"
#include "util/hash.h"
#include "util/params.h"

/**
   \brief Create an interface for manipulating double numbers compatible with the one for mpq.
*/
class double_manager {
    double m_zero_tolerance;
public:
    typedef double numeral;
    static bool precise() { return false; }
    
    double_manager(params_ref const & p = params_ref()) { updt_params(p); }

    void updt_params(params_ref const & p) {
        m_zero_tolerance = p.get_double("zero_tolerance", 0.00000001);
    }

    static void reset(double & a) { a = 0.0; }

    static void del(double & a) { /* do nothing */ }
    static void add(double a, double b, double & c) { c = a + b; }
    // d <- a + b*c
    static void addmul(double a, double b, double c, double & d) { d = a + b*c; }
    // d <- a - b*c
    static void submul(double a, double b, double c, double & d) { d = a - b*c; }
    static void sub(double a, double b, double & c) { c = a - b; }
    static void mul(double a, double b, double & c) { c = a * b; }
    static void div(double a, double b, double & c) { c = a / b; }
    static void inv(double a, double & b) { b = 1 / a; }
    static void inv(double & a) { a = 1 / a; }
    static void neg(double & a) { a = -a; }
    static void abs(double & a) { if (a < 0.0) neg(a); }
    static void power(double a, unsigned p, double & b) { 
        SASSERT(p <= INT_MAX);
        b = ::pow(a, static_cast<int>(p)); 
    }
    static void floor(double a, double & b) { b = ::floor(a); }
    static void ceil(double a, double & b) { b = ::ceil(a); }
    bool eq(double a, double b) const { return is_zero(a - b); }
    bool neq(double a, double b) const { return !eq(a, b); }
    static bool lt(double a, double b) { return a < b; }
    static bool le(double a, double b) { return a <= b; }
    static bool gt(double a, double b) { return a > b; }
    static bool ge(double a, double b) { return a >= b; }
    static void set(double & a, int n, int d) { a = static_cast<double>(n)/static_cast<double>(d); }
    static void set(double & a, double val) { a = val; }
    static void set(double & a, char const * val) { a = atof(val); }
    static void set(double & a, int val) { a = static_cast<double>(val); }
    static void set(double & a, unsigned val) { a = static_cast<double>(val); }
    static void set(double & a, int64_t val) { a = static_cast<double>(val); }
    static void set(double & a, uint64_t val) { a = static_cast<double>(val); }
    static void swap(double & a, double & b) { std::swap(a, b); }
    bool is_pos(double a) const { return a > m_zero_tolerance; }
    bool is_neg(double a) const { return a < m_zero_tolerance; }
    bool is_zero(double a) const { return  -m_zero_tolerance <= a && a <= m_zero_tolerance; }
    bool is_nonpos(double a) const { return !is_pos(a); }
    bool is_nonneg(double a) const { return !is_neg(a); }
    static bool is_one(double a) { return a == 1.0; }
    static bool is_minus_one(double a) { return a == -1.0; }
    static bool is_int(double a) { return a == ::floor(a); }
    static std::string to_string(double a) { 
        std::ostringstream sstream;
        sstream << std::setprecision(12) << a;
        return sstream.str();
    }

    static unsigned hash(double a) { 
        return hash_ull(static_cast<uint64_t>(a));
    }
};

static_assert(sizeof(uint64_t) == sizeof(double), "");

#endif /* DOUBLE_MANAGER_H_ */

