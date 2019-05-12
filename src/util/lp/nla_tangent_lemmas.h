/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/
#pragma once
#include "util/rational.h"
#include "util/lp/factorization.h"
#include "util/lp/nla_common.h"

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
        inline point operator+(const point& b) const {
            return point(x + b.x, y + b.y);
        } 

        inline point operator-(const point& b) const {
            return point(x - b.x, y - b.y);
        }
    };

    inline std::ostream& operator<<(std::ostream& out, point const& a) { return out << "(" << a.x <<  ", " << a.y << ")"; }


class tangents : common {   
public:
    tangents(core *core);
    void tangent_lemma();
private:    
    lpvar find_binomial_to_refine();
    void generate_explanations_of_tang_lemma(const monomial& m, const factorization& bf, lp::explanation& exp);
    
    void tangent_lemma_bf(const monomial& m,const factorization& bf);
    void generate_tang_plane(const rational & a, const rational& b, const factor& x, const factor& y, bool below, lpvar j);
    
    void generate_two_tang_lines(const factorization & bf, const point& xy, lpvar j);
    // Get two planes tangent to surface z = xy, one at point a,  and another at point b.
    // One can show that these planes still create a cut.
    void get_initial_tang_points(point &a, point &b, const point& xy, bool below) const;

    void push_tang_point(point &a, const point& xy, bool below, const rational& correct_val, const rational& val) const;
    
    void push_tang_points(point &a, point &b, const point& xy, bool below, const rational& correct_val, const rational& val) const;

    rational tang_plane(const point& a, const point& x) const;
    void get_tang_points(point &a, point &b, bool below, const rational& val, const point& xy) const;
    std::ostream& print_point(const point &a, std::ostream& out) const;
    std::ostream& print_tangent_domain(const point &a, const point &b, std::ostream& out) const;
    // "below" means that the val is below the surface xy 
    bool  plane_is_correct_cut(const point& plane,
                               const point& xy,
                               const rational & correct_val,                             
                               const rational & val,
                               bool below) const;
    template <typename T> rational val(T const& t) const;
    template <typename T> lpvar var(T const& t) const { return t.var(); }
}; // end of tangents
}
