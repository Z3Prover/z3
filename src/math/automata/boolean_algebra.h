/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    boolean_algebra.h

Abstract:

    Boolean Algebra, a la Margus Veanes Automata library.

Author:

    Nikolaj Bjorner (nbjorner) 2016-2-27

Revision History:


--*/

#ifndef BOOLEAN_ALGEBRA_H_
#define BOOLEAN_ALGEBRA_H_

#include "util.h"

template<class T>
class positive_boolean_algebra {
public:
    virtual T mk_false() = 0;
    virtual T mk_true() = 0;
    virtual T mk_and(T x, T y) = 0;
    virtual T mk_or(T x, T y) = 0;
    virtual T mk_and(unsigned sz, T const* ts) = 0;
    virtual T mk_or(unsigned sz, T const* ts) = 0;
    virtual lbool is_sat(T x) = 0;
};

template<class T>
class boolean_algebra : public positive_boolean_algebra<T> {
public:
    virtual T mk_not(T x) = 0;	
    //virtual lbool are_equivalent(T x, T y) = 0;
    //virtual T simplify(T x) = 0;    
};

#endif
