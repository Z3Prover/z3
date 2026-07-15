/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

  --*/
#include "math/lp/nla_tangent_lemmas.h"
#include "math/lp/nla_core.h"

namespace nla {

class tangent_imp {
    point         m_a;
    point         m_b;
    point         m_xy;
    rational      m_correct_v;
    // "below" means that the incorrect value is less than the correct one, that is m_v < m_correct_v
    bool          m_below;
    // pl is in the strict interior of the bound box (model-driven points
    // get_initial_points + push_point); McCormick at the box corners
    // requires non-strict inequality because the tangent meets the surface
    // along the box's edges (xy = pl.y*x + pl.x*y - pl.x*pl.y at x = pl.x
    // or y = pl.y).
    bool          m_pl_strict_interior = true;
    rational      m_v; // the monomial value 
    lpvar         m_j; // the monic variable
    const monic&  m_m;
    const factor& m_x;
    const factor& m_y;
    lpvar         m_jx;
    lpvar         m_jy;
    tangents&     m_tang;
    bool          m_is_mon;

public:
    tangent_imp(point xy,        
        const rational& v,
        const monic& m,
        const factorization& f,
        tangents& tang) : m_xy(xy),
                          m_correct_v(xy.x * xy.y),
                          m_below(v < m_correct_v),
                          m_v(v),
                          m_j(m.var()),
                          m_m(m),
                          m_x(f[0]),
                          m_y(f[1]),
                          m_jx(m_x.var()),
                          m_jy(m_y.var()),
                          m_tang(tang),
                          m_is_mon(f.is_mon()) {
        SASSERT(f.size() == 2);
    }
       
    void operator()() {    
        get_points();
        TRACE(nla_solver, print_tangent_domain(tout << "tang domain = ") << std::endl;);
        generate_line1();
        generate_line2();
        generate_plane(m_a);
        generate_plane(m_b);
    }

private:

    core & c() { return m_tang.c(); }

    void explain(lemma_builder& lemma) {
        if (!m_is_mon) {
            lemma &= m_m;
            lemma &= m_x;
            lemma &= m_y;
        }
    }

    void generate_plane(const point & pl) {
        if (c().throttle().insert_new(nla_throttle::TANGENT_LEMMA, m_j, m_jx, m_jy, m_below))
            return;
            
        lemma_builder lemma(c(), "generate tangent plane");
        c().negate_relation(lemma, m_jx, m_x.rat_sign()*pl.x);
        c().negate_relation(lemma, m_jy, m_y.rat_sign()*pl.y);
#if Z3DEBUG
        SASSERT(c().val(m_x) == m_xy.x && c().val(m_y) == m_xy.y);
        // int mult_sign = nla::rat_sign(pl.x - m_xy.x)*nla::rat_sign(pl.y - m_xy.y);
        SASSERT((nla::rat_sign(pl.x - m_xy.x)*nla::rat_sign(pl.y - m_xy.y) == 1) == m_below);
        // If "mult_sign is 1"  then (a - x)(b-y) > 0 and ab - bx - ay + xy > 0
        // or -ab + bx + ay < xy or -ay - bx + xy > -ab
        // val(j) stands for xy. So, finally we have  -ay - bx + j > - ab
#endif
            
        lp::lar_term t;
        t.add_monomial(- m_y.rat_sign()*pl.x, m_jy);
        t.add_monomial(- m_x.rat_sign()*pl.y, m_jx);
        t.add_var(m_j);
        llc cmp = m_below
            ? (m_pl_strict_interior ? llc::GT : llc::GE)
            : (m_pl_strict_interior ? llc::LT : llc::LE);
        lemma |= ineq(t, cmp, - pl.x*pl.y);
        explain(lemma);
    }

    void generate_line1() {
        // Use plane_type 1 to distinguish line1 from other tangent lemmas
        if (c().throttle().insert_new(nla_throttle::TANGENT_LEMMA, m_j, m_jx, m_jy, m_below, 1))
            return;
            
        lemma_builder lemma(c(), "tangent line 1");
        // Should be  v = val(m_x)*val(m_y), and val(factor) = factor.rat_sign()*var(factor.var())
        lemma |= ineq(m_jx, llc::NE, c().val(m_jx));
        lemma |= ineq(lp::lar_term(m_j,  - m_y.rat_sign() * m_xy.x,  m_jy), llc::EQ, 0);
        explain(lemma);
    }

    void generate_line2() {
        // Use plane_type 2 to distinguish line2 from other tangent lemmas
        if (c().throttle().insert_new(nla_throttle::TANGENT_LEMMA, m_j, m_jx, m_jy, m_below, 2))
            return;
            
        lemma_builder lemma(c(), "tangent line 2");
        lemma |= ineq(m_jy, llc::NE, c().val(m_jy));
        lemma |= ineq(lp::lar_term(m_j, - m_x.rat_sign() * m_xy.y, m_jx), llc::EQ, 0);
        explain(lemma);
    }

    // Get two planes tangent to surface z = xy, one at point a,  and another at point b, creating a cut
    void get_initial_points() {
        const rational& x = m_xy.x;
        const rational& y = m_xy.y;
        bool all_ints = m_v.is_int() && x.is_int() && y.is_int();
        rational delta = rational(1);
        if (!all_ints )
            delta = std::min(delta, abs(m_correct_v - m_v));
        TRACE(nla_solver, tout << "delta = " << delta << "\n";);
        if (!m_below){
            m_a = point(x - delta, y + delta);
            m_b = point(x + delta, y - delta);
        }
        else {
            // denote x = xy.x and y = xy.y, and vx, vy - the values of x and y.
            // we have val(xy) <  vx*y + vy*x - vx*vy = pl(x, y);
            // The plane with delta (1, 1) is  (vx + 1)y + (vy + 1)x - (vx + 1)(vy + 1) =
            // vx*y + vy*x - vx*vy + y + x - xv*vy - vx - vy - 1 = pl(x, y) - 1
            // For integers the last expression is greater than or equal to val(xy) when x = vx and y = vy.
            // If x <= vx+1 and y <= vy+1 then (vx+1-x)*(vy+1-y) > 0, that creates a cut
            // - (vx + 1)y - (vy + 1)x + xy > - (vx+1)*(vx+1).
            // If all_ints is false then we use the fact that
            // tang_plane() will not change more than on delta*delta
            m_a = point(x - delta, y - delta);
            m_b = point(x + delta, y + delta);
        }
    }

    void push_point(point & a) {
        SASSERT(plane_is_correct_cut(a));
        int steps = 10;
        point del = a - m_xy;
        while (steps-- && !c().done()) {
            del *= rational(2);
            point na = m_xy + del;
            TRACE(nla_solver_tp, tout << "del = " << del << std::endl;);
            if (!plane_is_correct_cut(na)) {
                TRACE(nla_solver_tp, tout << "exit\n";);
                return;
            }
            a = na;
        }
    }

    rational tang_plane(const point& a) const {
        return a.x * m_xy.y + a.y * m_xy.x - a.x * a.y;
    }

    // McCormick at box corners: choose m_a, m_b at the corners of
    // [x_lo, x_hi] x [y_lo, y_hi] that bound xy from the side dictated by
    // m_below. Returns false if either factor has an unbounded side, the
    // box is degenerate, or the current LP value of a factor coincides with
    // a chosen corner — generate_plane's negate_relation requires
    // val(j) != corner_coord (SASSERT in debug; trivially-true literal in
    // release). The caller falls back to the model-driven point selection in
    // these cases.
    bool set_box_corners() {
        if (!c().has_lower_bound(m_jx) || !c().has_upper_bound(m_jx))
            return false;
        if (!c().has_lower_bound(m_jy) || !c().has_upper_bound(m_jy))
            return false;
        rational const& x_lo = c().get_lower_bound(m_jx);
        rational const& x_hi = c().get_upper_bound(m_jx);
        rational const& y_lo = c().get_lower_bound(m_jy);
        rational const& y_hi = c().get_upper_bound(m_jy);
        if (x_lo == x_hi || y_lo == y_hi)
            return false;
        // negate_relation requires the model value to be strictly separated
        // from the corner coordinate it's compared to. If LP currently sits
        // exactly at a box edge, fall back.
        rational const& vx = c().val(m_jx);
        rational const& vy = c().val(m_jy);
        if (vx == x_lo || vx == x_hi || vy == y_lo || vy == y_hi)
            return false;
        if (m_below) {
            // Under-approximation: tangents at (x_lo, y_lo) and (x_hi, y_hi)
            // bound xy from below across the box.
            m_a = point(x_lo, y_lo);
            m_b = point(x_hi, y_hi);
        } else {
            // Over-approximation: anti-diagonal corners.
            m_a = point(x_lo, y_hi);
            m_b = point(x_hi, y_lo);
        }
        m_pl_strict_interior = false;
        return true;
    }

    void get_points() {
        if (c().params().arith_nl_tangents_box_corners() && set_box_corners()) {
            // Box corners are extremes; pushing further moves out of the box
            // and would invalidate the McCormick property.
            TRACE(nla_solver, tout << "xy = " << m_xy << ", box-corner points: ";
                  print_tangent_domain(tout) << std::endl;);
            return;
        }
        get_initial_points();
        TRACE(nla_solver, tout << "xy = " << m_xy << ", correct val = " << m_correct_v;
              print_tangent_domain(tout << "\ntang points:") << std::endl;);
        push_point(m_a);
        push_point(m_b);
        TRACE(nla_solver,
              tout << "pushed a = " << m_a << std::endl
              << "pushed b = " << m_b << std::endl
              << "tang_plane(a) = " << tang_plane(m_a) << " , val = " << m_a << ", "
              << "tang_plane(b) = " << tang_plane(m_b) << " , val = " << m_b << std::endl;);
    }

    std::ostream& print_tangent_domain(std::ostream& out) {
        return out << "(" << m_a <<  ", " << m_b << ")";
    }

    bool plane_is_correct_cut(const point& plane) const {
        TRACE(nla_solver, tout << "plane = " << plane << "\n";
              tout << "tang_plane() = " << tang_plane(plane) << ", v = " << m_v << ", correct_v = " << m_correct_v << "\n";);
        SASSERT((m_below && m_v < m_correct_v) ||
                ((!m_below) && m_v > m_correct_v));
        rational sign = rational(m_below ? 1 : -1);
        rational px = tang_plane(plane);
        return ((m_correct_v - px)*sign).is_pos() && !((px - m_v)*sign).is_neg();        
    }    
};

tangents::tangents(core * c) : common(c) {}
    
void tangents::tangent_lemma() {
    factorization bf(nullptr);
    const monic* m = nullptr;
    if (c().params().arith_nl_tangents() && c().find_bfc_to_refine(m, bf)) {
        lpvar j = m->var();
        tangent_imp tangent(point(val(bf[0]), val(bf[1])), c().val(j), *m, bf, *this);
        tangent();
    }
}


}
