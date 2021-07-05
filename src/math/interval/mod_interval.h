/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    mod_interval.h

Abstract:

    Intervals over fixed precision modular arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#pragma once

#include "util/rational.h"


template<typename Numeral>
struct pp {
    Numeral n;
    pp(Numeral const& n):n(n) {}
};

template<typename Numeral>
inline std::ostream& operator<<(std::ostream& out, pp<Numeral> const& p) {
    if ((0 - p.n) < p.n)
        return out << "-" << (0 - p.n);
    return out << p.n;
}

inline std::ostream& operator<<(std::ostream& out, pp<rational> const& p) {
    return out << p.n;
}

template<typename Numeral>
class mod_interval {
    bool emp { false };
public:
    Numeral lo { 0 };
    Numeral hi { 0 };
    mod_interval() {}
    mod_interval(Numeral const& l, Numeral const& h): lo(l), hi(h) {}
    virtual ~mod_interval() {}
    static mod_interval free() { return mod_interval(0, 0); }
    static mod_interval empty() { mod_interval i(0, 0); i.emp = true; return i; }

    bool is_free() const { return !emp && lo == hi; }
    bool is_empty() const { return emp; }
    bool is_singleton() const { return !is_empty() && (lo + 1 == hi || (hi == 0 && is_max(lo))); }
    bool contains(Numeral const& n) const;
    virtual bool is_max(Numeral const& n) const { return n + 1 == 0; }

    void set_free() { lo = hi = 0; emp = false; }
    void set_bounds(Numeral const& l, Numeral const& h) { lo = l; hi = h; }
    void set_empty() { emp = true; }

    mod_interval& intersect_ule(Numeral const& h);
    mod_interval& intersect_uge(Numeral const& l);
    mod_interval& intersect_ult(Numeral const& h);
    mod_interval& intersect_ugt(Numeral const& l);
    mod_interval& intersect_fixed(Numeral const& n);
    mod_interval& intersect_diff(Numeral const& n);
    mod_interval& update_lo(Numeral const& new_lo);
    mod_interval& update_hi(Numeral const& new_hi);

    mod_interval operator&(mod_interval const& other) const;
    mod_interval operator+(mod_interval const& other) const;
    mod_interval operator-(mod_interval const& other) const;
    mod_interval operator*(mod_interval const& other) const;
    mod_interval operator-() const;
    mod_interval operator*(Numeral const& n) const;
    mod_interval operator+(Numeral const& n) const { return mod_interval(lo + n, hi + n); }
    mod_interval operator-(Numeral const& n) const { return mod_interval(lo - n, hi - n); }
    mod_interval& operator+=(mod_interval const& other) { *this = *this + other; return *this; }
    std::ostream& display(std::ostream& out) const { 
        if (is_empty()) return out << "empty"; 
        if (is_free()) return out << "free";
        return out << "[" << pp(lo) << ", " << pp(hi) << "["; 
    }
    Numeral closest_value(Numeral const& n) const;
};

template<typename Numeral>
inline std::ostream& operator<<(std::ostream& out, mod_interval<Numeral> const& i) {
    return i.display(out);
}

