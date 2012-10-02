/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mpbqi.h

Abstract:

    Binary Rational Number Intervals

Author:

    Leonardo de Moura (leonardo) 2012-01-04

Revision History:

--*/
#ifndef _MPBQI_H_
#define _MPBQI_H_

#include"mpbq.h"
#include"basic_interval.h"

class mpbqi_manager : public basic_interval_manager<mpbq_manager, false> {
    typedef basic_interval_manager<mpbq_manager, false> super;
public:
    mpbqi_manager(mpbq_manager & m):super(m) {}

    void set(interval & a, interval const & b) { super::set(a, b); }
    void set(interval & a, bound const & lower, bound const & upper) { super::set(a, lower, upper); }
    void set(interval & a, bound const & n) { super::set(a, n); }
    void set(interval & a, mpz const & n) {
        m().set(a.lower(), n);
        m().set(a.upper(), n);
    }

    void add(interval const & a, interval const & b, interval & c) { super::add(a, b, c); }
    void add(interval const & a, mpz const & b, interval & c) { 
        m().add(a.lower(), b, c.lower());
        m().add(a.upper(), b, c.upper());
    }
    

};

typedef mpbqi_manager::interval mpbqi;
typedef mpbqi_manager::scoped_interval scoped_mpbqi;

#endif
