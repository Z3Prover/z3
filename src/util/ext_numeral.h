/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ext_numeral.h

Abstract:

    Goodies for handling extended numerals such as R union { -oo, +oo }.
    We can have extended sets of mpq, mpz, mpbq, mpf, etc.
    
Author:

    Leonardo de Moura (leonardo) 2011-12-04.

Revision History:

--*/
#pragma once

#include<iostream>
#include "util/debug.h"
    
enum ext_numeral_kind { EN_MINUS_INFINITY, EN_NUMERAL, EN_PLUS_INFINITY };

template<typename numeral_manager>
bool is_zero(numeral_manager & m, 
             typename numeral_manager::numeral const & a,
             ext_numeral_kind ak) {
    return ak == EN_NUMERAL && m.is_zero(a);
}

template<typename numeral_manager>
bool is_pos(numeral_manager & m, 
            typename numeral_manager::numeral const & a,
            ext_numeral_kind ak) {
    return ak == EN_PLUS_INFINITY || (ak == EN_NUMERAL && m.is_pos(a));
}

template<typename numeral_manager>
bool is_neg(numeral_manager & m, 
            typename numeral_manager::numeral const & a,
            ext_numeral_kind ak) {
    return ak == EN_MINUS_INFINITY || (ak == EN_NUMERAL && m.is_neg(a));
}

inline bool is_infinite(ext_numeral_kind ak) { return ak != EN_NUMERAL; }

template<typename numeral_manager>
void set(numeral_manager & m, 
         typename numeral_manager::numeral & a,
         ext_numeral_kind & ak,
         typename numeral_manager::numeral const & b,
         ext_numeral_kind bk) {
    m.set(a, b);
    ak = bk;
}

template<typename numeral_manager>
void reset(numeral_manager & m, 
           typename numeral_manager::numeral & a,
           ext_numeral_kind & ak) {
    m.reset(a);
    ak = EN_NUMERAL;
}

template<typename numeral_manager>
void neg(numeral_manager & m, 
         typename numeral_manager::numeral & a,
         ext_numeral_kind & ak) {
    switch (ak) {
    case EN_MINUS_INFINITY:
        ak = EN_PLUS_INFINITY;
        break;
    case EN_NUMERAL:
        m.neg(a);
        break;
    case EN_PLUS_INFINITY:
        ak = EN_MINUS_INFINITY;
        break;
    }
}

template<typename numeral_manager>
void inv(numeral_manager & m, 
         typename numeral_manager::numeral & a,
         ext_numeral_kind & ak) {
    SASSERT(numeral_manager::field());
    switch (ak) {
    case EN_MINUS_INFINITY:
        ak = EN_NUMERAL;
        m.reset(a);
        break;
    case EN_NUMERAL:
        SASSERT(!m.is_zero(a));
        m.inv(a);
        break;
    case EN_PLUS_INFINITY:
        ak = EN_NUMERAL;
        m.reset(a);
        break;
    }
}

template<typename numeral_manager>
void add(numeral_manager & m, 
         typename numeral_manager::numeral const & a,
         ext_numeral_kind ak,
         typename numeral_manager::numeral const & b,
         ext_numeral_kind bk,
         typename numeral_manager::numeral & c,
         ext_numeral_kind & ck) {
    SASSERT(!(ak == EN_MINUS_INFINITY && bk == EN_PLUS_INFINITY));  // result is undefined
    SASSERT(!(ak == EN_PLUS_INFINITY  && bk == EN_MINUS_INFINITY)); // result is undefined
    if (ak != EN_NUMERAL) {
        m.reset(c);
        ck = ak;
    }
    else if (bk != EN_NUMERAL) {
        m.reset(c);
        ck = bk;
    }
    else {
        m.add(a, b, c);
        ck = EN_NUMERAL;
    }
}

template<typename numeral_manager>
void sub(numeral_manager & m, 
         typename numeral_manager::numeral const & a,
         ext_numeral_kind ak,
         typename numeral_manager::numeral const & b,
         ext_numeral_kind bk,
         typename numeral_manager::numeral & c,
         ext_numeral_kind & ck) {
    SASSERT(!(ak == EN_MINUS_INFINITY && bk == EN_MINUS_INFINITY));  // result is undefined
    SASSERT(!(ak == EN_PLUS_INFINITY  && bk == EN_PLUS_INFINITY));   // result is undefined
    if (ak != EN_NUMERAL) {
        SASSERT(bk != ak);
        m.reset(c);
        ck = ak;
    }
    else {
        switch (bk) {
        case EN_MINUS_INFINITY:
            m.reset(c);
            ck = EN_PLUS_INFINITY;
            break;
        case EN_NUMERAL:
            m.sub(a, b, c);
            ck = EN_NUMERAL;
            break;
        case EN_PLUS_INFINITY:
            m.reset(c);
            ck = EN_MINUS_INFINITY;
            break;
        }
    }
}

template<typename numeral_manager>
void mul(numeral_manager & m, 
         typename numeral_manager::numeral const & a,
         ext_numeral_kind ak,
         typename numeral_manager::numeral const & b,
         ext_numeral_kind bk,
         typename numeral_manager::numeral & c,
         ext_numeral_kind & ck) {
    if (is_zero(m, a, ak) || is_zero(m, b, bk)) {
        m.reset(c);
        ck = EN_NUMERAL;
    }
    else if (is_infinite(ak) || is_infinite(bk)) {
        if (is_pos(m, a, ak) == is_pos(m, b, bk))
            ck = EN_PLUS_INFINITY;
        else
            ck = EN_MINUS_INFINITY;
        m.reset(c);
    }
    else {
        ck = EN_NUMERAL;
        m.mul(a, b, c);
    }
}

template<typename numeral_manager>
void div(numeral_manager & m, 
         typename numeral_manager::numeral const & a,
         ext_numeral_kind ak,
         typename numeral_manager::numeral const & b,
         ext_numeral_kind bk,
         typename numeral_manager::numeral & c,
         ext_numeral_kind & ck) {
    SASSERT(!is_zero(m, b, bk));
    if (is_zero(m, a, ak)) {
        SASSERT(!is_zero(m, b, bk));
        m.reset(c);
        ck = EN_NUMERAL;
    }
    else if (is_infinite(ak)) {
        SASSERT(!is_infinite(bk));
        if (is_pos(m, a, ak) == is_pos(m, b, bk))
            ck = EN_PLUS_INFINITY;
        else
            ck = EN_MINUS_INFINITY;
        m.reset(c);
    }
    else if (is_infinite(bk)) {
        SASSERT(!is_infinite(ak));
        m.reset(c);
        ck = EN_NUMERAL;
    }
    else {
        ck = EN_NUMERAL;
        m.div(a, b, c);
    }
}


template<typename numeral_manager>
void power(numeral_manager & m, 
           typename numeral_manager::numeral & a,
           ext_numeral_kind & ak,
           unsigned n) {
    switch (ak) {
    case EN_MINUS_INFINITY:
        if (n % 2 == 0)
            ak = EN_PLUS_INFINITY;
        break;
    case EN_NUMERAL:
        m.power(a, n, a);
        break;
    case EN_PLUS_INFINITY:
        break; // do nothing
    }
}

/**
   \brief Return true if (a,ak) == (b,bk).
*/
template<typename numeral_manager>
bool eq(numeral_manager & m, 
        typename numeral_manager::numeral const & a,
        ext_numeral_kind ak,
        typename numeral_manager::numeral const & b,
        ext_numeral_kind bk) {
    if (ak == EN_NUMERAL) {
        return bk == EN_NUMERAL && m.eq(a, b);
    }
    else {
        return ak == bk;
    }
}

template<typename numeral_manager>
bool neq(numeral_manager & m, 
         typename numeral_manager::numeral const & a,
         ext_numeral_kind ak,
         typename numeral_manager::numeral const & b,
         ext_numeral_kind bk) {
    return !eq(m, a, ak, b, bk);
}

template<typename numeral_manager>
bool lt(numeral_manager & m, 
        typename numeral_manager::numeral const & a,
        ext_numeral_kind ak,
        typename numeral_manager::numeral const & b,
        ext_numeral_kind bk) {
    switch (ak) {
    case EN_MINUS_INFINITY:
        return bk != EN_MINUS_INFINITY;
    case EN_NUMERAL:
        switch (bk) {
        case EN_MINUS_INFINITY:
            return false;
        case EN_NUMERAL:
            return m.lt(a, b);
        case EN_PLUS_INFINITY:
            return true;
        default:
            UNREACHABLE();
            return false;
        }
    case EN_PLUS_INFINITY:
        return false;
    default:
        UNREACHABLE();
        return false;
    }
}

template<typename numeral_manager>
bool gt(numeral_manager & m, 
        typename numeral_manager::numeral const & a,
        ext_numeral_kind ak,
        typename numeral_manager::numeral const & b,
        ext_numeral_kind bk) {
    return lt(m, b, bk, a, ak);
}

template<typename numeral_manager>
bool le(numeral_manager & m, 
        typename numeral_manager::numeral const & a,
        ext_numeral_kind ak,
        typename numeral_manager::numeral const & b,
        ext_numeral_kind bk) {
    return !gt(m, a, ak, b, bk);
}

template<typename numeral_manager>
bool ge(numeral_manager & m, 
        typename numeral_manager::numeral const & a,
        ext_numeral_kind ak,
        typename numeral_manager::numeral const & b,
        ext_numeral_kind bk) {
    return !lt(m, a, ak, b, bk);
}

template<typename numeral_manager>
void display(std::ostream & out,
             numeral_manager & m, 
             typename numeral_manager::numeral const & a,
             ext_numeral_kind ak) {
    switch (ak) {
    case EN_MINUS_INFINITY: out << "-oo"; break;
    case EN_NUMERAL: m.display(out, a); break;
    case EN_PLUS_INFINITY: out << "+oo"; break;
    }
}

template<typename numeral_manager>
void display_pp(std::ostream & out,
                numeral_manager & m, 
                typename numeral_manager::numeral const & a,
                ext_numeral_kind ak) {
    switch (ak) {
    case EN_MINUS_INFINITY: out << "-&infin;"; break;
    case EN_NUMERAL: m.display_pp(out, a); break;
    case EN_PLUS_INFINITY: out << "+&infin;"; break;
    }
}

