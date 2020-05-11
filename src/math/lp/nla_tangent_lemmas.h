/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)
  --*/
#pragma once
#include "util/rational.h"
#include "math/lp/factorization.h"
#include "math/lp/nla_common.h"

namespace nla {
class core;

struct point {
    rational x;
    rational y;
    point(const rational& a, const rational& b): x(a), y(b) {}
    point() {}
    inline point& operator*=(rational a) {
        x *= a;
        y *= a;
        return *this;
    } 
    inline point& operator/=(rational a) {
        x /= a;
        y /= a;
        return *this;
    } 
    inline point operator+(const point& b) const {
        return point(x + b.x, y + b.y);
    } 

    inline point operator-(const point& b) const {
        return point(x - b.x, y - b.y);
    }
};

inline std::ostream& operator<<(std::ostream& out, point const& a) { return out << "(" << a.x <<  ", " << a.y << ")"; }


struct tangents : common {
    tangents(core *core);
    void tangent_lemma();    
}; // end of tangents
} // end of namespace
