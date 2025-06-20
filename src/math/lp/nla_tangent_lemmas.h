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
#include "util/hashtable.h"
#include "util/hash.h"

namespace nla {
class core;

// Key for throttling tangent plane generation: (var, below)
struct tangent_key {
    unsigned var;
    bool below;
    
    tangent_key(unsigned v, bool b) : var(v), below(b) {}
    tangent_key() : var(0), below(false) {}
    
    bool operator==(const tangent_key& other) const {
        return var == other.var && below == other.below;
    }
};

struct tangent_key_hash {
    unsigned operator()(const tangent_key& k) const {
        return hash_u(k.var) ^ (k.below ? 1 : 0);
    }
};

struct tangent_key_eq {
    bool operator()(const tangent_key& a, const tangent_key& b) const {
        return a == b;
    }
};

// Key for throttling tangent line generation: (var1, var2)
struct line_key {
    unsigned var1;
    unsigned var2;
    
    line_key(unsigned v1, unsigned v2) : var1(v1), var2(v2) {}
    line_key() : var1(0), var2(0) {}
    
    bool operator==(const line_key& other) const {
        return var1 == other.var1 && var2 == other.var2;
    }
};

struct line_key_hash {
    unsigned operator()(const line_key& k) const {
        return hash_u(k.var1) ^ hash_u(k.var2);
    }
};

struct line_key_eq {
    bool operator()(const line_key& a, const line_key& b) const {
        return a == b;
    }
};

struct point {
    rational x;
    rational y;
    point(const rational& a, const rational& b): x(a), y(b) {}
    point() = default;
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
    // Hashtable to throttle tangent plane generation
    hashtable<tangent_key, tangent_key_hash, tangent_key_eq> m_processed_planes;
    
    // Hashtable to throttle tangent line generation
    hashtable<line_key, line_key_hash, line_key_eq> m_processed_lines;
    
    tangents(core *core);
    void tangent_lemma();
    
    // Throttling function similar to order::throttle_monic
    bool throttle_plane(unsigned var, bool below, std::string const & debug_location);
    
    // Throttling function for line generation
    bool throttle_line(unsigned var1, unsigned var2, std::string const & debug_location);
}; // end of tangents
} // end of namespace
