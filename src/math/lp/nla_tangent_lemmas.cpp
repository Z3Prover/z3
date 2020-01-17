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
#include "math/lp/nla_tangent_lemmas.h"
#include "math/lp/nla_core.h"

namespace nla {

struct imp {
    point m_a;
    point m_b;
    point m_xy;
    rational m_correct_v;
    // "below" means that the incorrect value is less than the correct one, that is m_v < m_correct_v
    bool  m_below;
    rational m_v; // the monomial value 
    lpvar    m_j; // the monic variable
    const monic& m_m;
    const factor& m_x;
    const factor& m_y;
    lpvar m_jx;
    lpvar m_jy;
    tangents& m_tang;
    imp(point xy,        
        const rational& v,
        lpvar j, // the monic variable
        const monic& m,
        const factor& x,
        const factor& y,
        tangents& tang) : m_xy(xy),
                          m_correct_v(xy.x * xy.y),
                          m_below(v < m_correct_v),
                          m_v(v),
                          m_j(tang.var(m)),
                          m_m(m),
                          m_x(x),
                          m_y(y),
                          m_jx(tang.var(x)),
                          m_jy(tang.var(y)),
                          m_tang(tang) {}

    
    core & c() { return m_tang.c(); }
    
    void generate_explanations_of_tang_lemma(lp::explanation& exp) {    
    // here we repeat the same explanation for each lemma
        c().explain(m_m, exp);
        c().explain(m_x, exp);
        c().explain(m_y, exp);
    }
    void generate_simple_tangent_lemma(const monic& m, const factorization&);    
    void tangent_lemma_on_bf() {    
        get_tang_points();
        TRACE("nla_solver", tout << "tang domain = "; print_tangent_domain(tout) << std::endl;);
        generate_two_tang_lines();
        generate_tang_plane(m_a);
        generate_tang_plane(m_b);
    }


    void generate_tang_plane(const point & pl) {
        c().add_empty_lemma();
        c().negate_relation(m_jx, pl.x);
        c().negate_relation(m_jy, pl.y);
#if Z3DEBUG
        int mult_sign = nla::rat_sign(pl.x - c().val(m_jx))*nla::rat_sign(pl.y - c().val(m_jy));
        SASSERT((mult_sign == 1) == m_below);
        // If "mult_sign is 1"  then (a - x)(b-y) > 0 and ab - bx - ay + xy > 0
        // or -ab + bx + ay < xy or -ay - bx + xy > -ab
        // val(j) stands for xy. So, finally we have  -ay - bx + j > - ab
#endif
            
        lp::lar_term t;
        t.add_monomial(- pl.x, m_jy);
        t.add_monomial(- pl.y, m_jx);
        t.add_var(m_j);
        c().mk_ineq(t, m_below? llc::GT : llc::LT, - pl.x*pl.y);            
    }
    
    void generate_two_tang_lines() {
        m_tang.add_empty_lemma();
        c().mk_ineq(m_jx, llc::NE, m_xy.x);
        c().mk_ineq(m_j, - m_xy.x, m_jy, llc::EQ);
        
        m_tang.add_empty_lemma();
        c().mk_ineq(m_jy, llc::NE, m_xy.y);
        c().mk_ineq(m_j, - m_xy.y, m_jx, llc::EQ);
    }
    // Get two planes tangent to surface z = xy, one at point a,  and another at point b, creating a cut
    void get_initial_tang_points() {
        const rational& x = m_xy.x;
        const rational& y = m_xy.y;
        bool all_ints = m_v.is_int() && x.is_int() && y.is_int();
        rational delta = rational(1);
        if (!all_ints )
            delta = std::min(delta, abs(m_correct_v - m_v));
        TRACE("nla_solver", tout << "delta = " << delta << "\n";);
        if (!m_below){
            m_a = point(x - delta, y + delta);
            m_b = point(x + delta, y - delta);
        }
        else {
            // denote x = xy.x and y = xy.y, and vx, vy - the value of x and y.
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

    void push_tang_point(point & a) {
        SASSERT(plane_is_correct_cut(a));
        int steps = 10;
        point del = a - m_xy;
        while (steps--) {
            del *= rational(2);
            point na = m_xy + del;
            TRACE("nla_solver_tp", tout << "del = " << del << std::endl;);
            if (!plane_is_correct_cut(na)) {
                TRACE("nla_solver_tp", tout << "exit";tout << std::endl;);
                return;
            }
            a = na;
        }
    }

    rational tang_plane(const point& a) const {
        return  a.x * m_xy.y + a.y * m_xy.x - a.x * a.y;
    }

    void get_tang_points() {
        get_initial_tang_points();
        TRACE("nla_solver", tout << "xy = " << m_xy << ", correct val = " << m_correct_v;
              tout << "\ntang points:"; print_tangent_domain(tout);tout << std::endl;);
        push_tang_point(m_a);
        TRACE("nla_solver", tout << "pushed a = " << m_a << std::endl;);
        
        push_tang_point(m_b);
        TRACE("nla_solver", tout << "pushed b = " << m_b << std::endl;);
        TRACE("nla_solver",
              tout << "tang_plane(a) = " << tang_plane(m_a) << " , val = " << m_v <<  ", tang_plane(b) = " << tang_plane(m_b) << " , val = " << std::endl;);
    }

    std::ostream& print_tangent_domain(std::ostream& out) {
        out << "(" << m_a <<  ", " << m_b << ")";
        return out;
    }

    bool  plane_is_correct_cut(const point& plane) const {
        TRACE("nla_solver", tout << "plane = " << plane << "\n";
              tout << "tang_plane() = " << tang_plane(plane) << ", v = " << m_v << ", correct_v = " << m_correct_v << "\n";);
        SASSERT((m_below && m_v < m_correct_v) ||
                ((!m_below) && m_v > m_correct_v));
        rational sign = m_below? rational(1) : rational(-1);
        rational px = tang_plane(plane);
        return ((m_correct_v - px)*sign).is_pos() && !((px - m_v)*sign).is_neg();        
    }    
};

tangents::tangents(core * c) : common(c, nullptr) {}
    
void tangents::tangent_lemma() {
    if (!c().m_nla_settings.run_tangents()) {
        TRACE("nla_solver", tout << "not generating tangent lemmas\n";);
        return;
    }
    factorization bf(nullptr);
    const monic* m;
    if (c().find_bfc_to_refine(m, bf)) {
        unsigned lemmas_size_was = c().m_lemma_vec->size();
        unsigned j = m->var();
        imp i(point(val(bf[0]), val(bf[1])),
              c().val(j),
              j,
              *m,
              bf[0],
              bf[1],
              *this);
        i.tangent_lemma_on_bf();
        if (!bf.is_mon()) { 
            lp::explanation expl;
            generate_explanations_of_tang_lemma(*m, bf, expl);
            for (unsigned i = lemmas_size_was; i < c().m_lemma_vec->size(); i++) {
                auto &l = ((*c().m_lemma_vec)[i]);
                l.expl().add(expl);
            }
        }
        TRACE("nla_solver",
              for (unsigned i = lemmas_size_was; i < c().m_lemma_vec->size(); i++) 
                  c().print_specific_lemma((*c().m_lemma_vec)[i], tout); );

    }
}

void tangents::generate_explanations_of_tang_lemma(const monic& rm, const factorization& bf, lp::explanation& exp) {
    // here we repeat the same explanation for each lemma
    c().explain(rm, exp);
    c().explain(bf[0], exp);
    c().explain(bf[1], exp);
}

}
