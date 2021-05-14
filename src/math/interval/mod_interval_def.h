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
