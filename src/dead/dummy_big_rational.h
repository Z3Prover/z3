/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dummy_big_rational.h

Abstract:

    Dummy big rational

Author:

    Leonardo de Moura (leonardo) 2006-09-26.

Revision History:

--*/

#ifndef _DUMMY_BIG_RATIONAL_H_
#define _DUMMY_BIG_RATIONAL_H_

#include<string>
#include"debug.h"

class big_rational {
public:
    big_rational() { }
    big_rational(int n) {}
    ~big_rational() {}
    void reset() {}
    unsigned hash() const { return 0; }
    void set(int num, int den) { UNREACHABLE(); }
    void set(const char * str) { UNREACHABLE(); }
    bool is_int() const { UNREACHABLE(); return false; }
    long get_int() const { UNREACHABLE(); return 0; }
    void neg() { UNREACHABLE(); }
    big_rational & operator=(const big_rational & r) { UNREACHABLE(); return *this; }
    bool operator==(const big_rational & r) const { UNREACHABLE(); return false; }
    bool operator<(const big_rational & r) const { UNREACHABLE(); return false; }
    big_rational & operator+=(const big_rational & r) { UNREACHABLE(); return *this; }
    big_rational & operator-=(const big_rational & r) { UNREACHABLE(); return *this; }
    big_rational & operator*=(const big_rational & r) { UNREACHABLE(); return *this; }
    big_rational & operator/=(const big_rational & r) { UNREACHABLE(); return *this; }
    big_rational & operator%=(const big_rational & r) { UNREACHABLE(); return *this; }
    friend void div(const big_rational & r1, const big_rational & r2, big_rational & result) { UNREACHABLE(); }
    void get_numerator(big_rational & result) { UNREACHABLE(); }
    void get_denominator(big_rational & result) { UNREACHABLE(); }
    void get_floor(big_rational & result) { UNREACHABLE(); }
    std::string to_string() const { UNREACHABLE(); return std::string(""); }
};

#endif /* _DUMMY_BIG_RATIONAL_H_ */

