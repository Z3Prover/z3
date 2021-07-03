/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    mod_interval_def.h

Abstract:

    Intervals over fixed precision modular arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#pragma once

#include "math/interval/mod_interval.h"

template<typename Numeral>
bool mod_interval<Numeral>::contains(Numeral const& n) const {
    if (is_empty())
        return false;
    if (is_free())
        return true;
    if (lo < hi)
        return lo <= n && n < hi;
    else
        return lo <= n || n < hi;
}

template<typename Numeral>
mod_interval<Numeral> mod_interval<Numeral>::operator+(mod_interval<Numeral> const& other) const {
    if (is_empty())
        return *this;
    if (other.is_empty())
        return other;
    if (is_free())
        return *this;
    if (other.is_free())
        return other;
    Numeral sz = (hi - lo) + (other.hi - other.lo);
    if (sz < (hi - lo))
        return mod_interval::free();
    return mod_interval(lo + other.lo, hi + other.hi);
}

template<typename Numeral>
mod_interval<Numeral> mod_interval<Numeral>::operator-(mod_interval<Numeral> const& other) const {
    return *this + (-other);
}

template<typename Numeral>
mod_interval<Numeral> mod_interval<Numeral>::operator-() const {
    if (is_empty())
        return *this;
    if (is_free())
        return *this;
    return mod_interval(1 - hi, 1 - lo);
}

template<typename Numeral>
mod_interval<Numeral> mod_interval<Numeral>::operator*(Numeral const& n) const {
    if (is_empty())
        return *this;
    if (n == 0)
        return mod_interval(0, 1);
    if (n == 1)
        return *this;
    if (is_free())
        return *this;
    Numeral sz = hi - lo;
    if (0 - n < n) {
        Numeral mn = 0 - n;
        Numeral mz = mn * sz;            
        if (mz / mn != sz)
            return mod_interval::free();
        return mod_interval((hi - 1) * n, n * lo + 1);
    }
    else {
        Numeral mz = n * sz;
        if (mz / n != sz)
            return mod_interval::free();
        return mod_interval(n * lo, n * (hi - 1) + 1);
    }
}

template<typename Numeral>
mod_interval<Numeral> mod_interval<Numeral>::operator&(mod_interval const& other) const {
    Numeral l, h;
    if (is_free() || other.is_empty())
        return other;
    if (other.is_free() || is_empty())
        return *this;
    if (contains(other.lo))
        l = other.lo;
    else if (other.contains(lo))
        l = lo;
    else 
        return mod_interval::empty();
    if (contains(other.hi - 1))
        h = other.hi;
    else if (other.contains(hi - 1))
        h = hi;
    else
        return mod_interval::empty();
    return mod_interval(l, h);
}

template<typename Numeral>
Numeral mod_interval<Numeral>::closest_value(Numeral const& n) const {
    if (contains(n))
        return n;
    if (is_empty())
        return n;
    if (lo - n < n - hi)
        return lo;
    return hi - 1;
}

// TBD: correctness and completeness for wrap-around semantics needs to be checked/fixed

template<typename Numeral>
mod_interval<Numeral>& mod_interval<Numeral>::intersect_ule(Numeral const& h) {
    if (is_empty())
        return *this;
    if (is_max(h))
        return *this;
    else if (is_free())
        lo = 0, hi = h + 1;
    else if (hi > lo && lo > h)
        set_empty();
    else if (hi != 0 || h + 1 < hi)
        hi = h + 1; 
    return *this;
}

template<typename Numeral>
mod_interval<Numeral>& mod_interval<Numeral>::intersect_uge(Numeral const& l) {
    if (is_empty())
        return *this;
    if (lo < hi && hi <= l)
        set_empty();
    else if (is_free())
        lo = l, hi = 0;
    else if (lo < hi && lo < l)
        lo = l;     
    return *this;
}

template<typename Numeral>
mod_interval<Numeral>& mod_interval<Numeral>::intersect_ult(Numeral const& h) {
    if (is_empty())
        return *this;
    if (h == 0)
        set_empty();
    else if (is_free())
        lo = 0, hi = h;
    else if (hi > lo && lo >= h)
        set_empty();
    else if (hi > lo && h < hi)
        hi = h;
    return *this;
}

template<typename Numeral>
mod_interval<Numeral>& mod_interval<Numeral>::intersect_ugt(Numeral const& l) {
    if (is_empty())
        return *this;
    if (is_max(l))
        set_empty();
    else if (is_free())
        lo = l + 1, hi = 0;
    else if (lo > l)
        return;
    else if (lo < hi && hi <= l)
        set_empty();
    else if (lo < hi) 
        lo = l + 1;
    return *this;
}

template<typename Numeral>
mod_interval<Numeral>& mod_interval<Numeral>::intersect_fixed(Numeral const& a) {
    if (is_empty())
        return *this;
    if (!contains(a))
        set_empty();
    else if (is_max(a))
        lo = a, hi = 0;
    else
        lo = a, hi = a + 1;
    return *this;
}

template<typename Numeral>
mod_interval<Numeral>& mod_interval<Numeral>::intersect_diff(Numeral const& a) {
    if (!contains(a) || is_empty())
        return *this;
    if (a == lo && a + 1 == hi)
        set_empty();
    else if (a == lo && hi == 0 && is_max(a))
        set_empty();
    else if (a == lo && !is_max(a))
        lo = a + 1;
    else if (a + 1 == hi)
        hi = a;
    else if (hi == 0 && is_max(a))
        hi = a;
    return *this;
}
