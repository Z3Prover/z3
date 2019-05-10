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
#include "util/lp/nla_tangent_lemmas.h"
#include "util/lp/nla_core.h"

namespace nla {
template <typename T> rational tangents::val(T const& t) const { return m_core->val(t); }

tangents::tangents(core * c) : common(c) {}

    
std::ostream& tangents::print_tangent_domain(const point &a, const point &b, std::ostream& out) const {
    return out << "(" << a <<  ", " << b << ")";
}
void tangents::tangent_lemma() {
    if (!c().m_settings.run_tangents()) {
        TRACE("nla_solver", tout << "not generating tangent lemmas\n";);
        return;
    }
    factorization bf(nullptr);
    const monomial* m;
    if (c().find_bfc_to_refine(m, bf)) {
        tangent_lemma_bf(*m, bf);
    }
}

void tangents::generate_explanations_of_tang_lemma(const monomial& rm, const factorization& bf, lp::explanation& exp) {
    // here we repeat the same explanation for each lemma
    c().explain(rm, exp);
    c().explain(bf[0], exp);
    c().explain(bf[1], exp);
}

void tangents::generate_tang_plane(const rational & a, const rational& b, const factor& x, const factor& y, bool below, lpvar j) {
    lpvar jx = var(x);
    lpvar jy = var(y);
    add_empty_lemma();
    c().negate_relation(jx, a);
    c().negate_relation(jy, b);
#if Z3DEBUG
    int mult_sign = nla::rat_sign(a - val(jx))*nla::rat_sign(b - val(jy));
    SASSERT((mult_sign == 1) == below);
    // If "mult_sign is 1"  then (a - x)(b-y) > 0 and ab - bx - ay + xy > 0
    // or -ab + bx + ay < xy or -ay - bx + xy > -ab
    // val(j) stands for xy. So, finally we have  -ay - bx + j > - ab
#endif

    lp::lar_term t;
    t.add_coeff_var(-a, jy);
    t.add_coeff_var(-b, jx);
    t.add_var(j);
    c().mk_ineq(t, below? llc::GT : llc::LT, - a*b);
}

void tangents::tangent_lemma_bf(const monomial& m, const factorization& bf){
    point a, b;
    point xy (val(bf[0]), val(bf[1]));
    rational correct_mult_val =  xy.x * xy.y;
    lpvar j =m.var();
    // We have canonize_sign(m)*m.vars() = m.rvars()
    // Let s = canonize_sign(bf). Then we have bf[1]*bf[1] = s*m.rvars()
    // s*canonize_sign(m)*val(m).
    // Therefore sign*val(m) = val((bf[0])*val(bf[1]), where sign = canonize_sign(bf)*canonize_sign(m)
    
    SASSERT(canonize_sign(bf) == canonize_sign(m));
    rational v = val(j);    
    bool below = v < correct_mult_val;
    TRACE("nla_solver", tout << "below = " << below << std::endl; );
    get_tang_points(a, b, below, v, xy);
    TRACE("nla_solver", tout << "tang domain = "; print_tangent_domain(a, b, tout); tout << std::endl;);
    unsigned lemmas_size_was = c().m_lemma_vec->size();
    rational sign(1);
    generate_two_tang_lines(bf, xy, j);
    generate_tang_plane(a.x, a.y, bf[0], bf[1], below, j);
    generate_tang_plane(b.x, b.y, bf[0], bf[1], below, j);

    if (!bf.is_mon()) { 
        lp::explanation expl;
        generate_explanations_of_tang_lemma(m, bf, expl);
        for (unsigned i = lemmas_size_was; i < c().m_lemma_vec->size(); i++) {
            auto &l = ((*c().m_lemma_vec)[i]);
            l.expl().add(expl);
        }
    }
    TRACE("nla_solver",
          for (unsigned i = lemmas_size_was; i < c().m_lemma_vec->size(); i++) 
              c().print_specific_lemma((*c().m_lemma_vec)[i], tout); );
}
/*
  void tangents::generate_simple_tangent_lemma(const monomial& m) {
    if (m.size() != 2)
        return;
    TRACE("nla_solver", tout << "m:" << pp_mon(c(), m) << std::endl;);
    c().add_empty_lemma();
    const rational v = c().product_value(m.vars());
    const rational mv = val(m);
    SASSERT(mv != v);
    SASSERT(!mv.is_zero() && !v.is_zero());
    rational sign = rational(nla::rat_sign(mv));
    if (sign != nla::rat_sign(v)) {
        c().generate_simple_sign_lemma(-sign, m);
        return;
    }
    bool gt = abs(mv) > abs(v);
    if (gt) {
        for (lpvar j : m.vars()) {
            const rational jv = val(j);
            rational js = rational(nla::rat_sign(jv));
            c().mk_ineq(js, j, llc::LT);
            c().mk_ineq(js, j, llc::GT, jv);
        }
        c().mk_ineq(sign, m.var(), llc::LE, std::max(v, rational(-1)));
    } else {
        for (lpvar j : m.vars()) {
            const rational jv = val(j);
            rational js = rational(nla::rat_sign(jv));
            c().mk_ineq(js, j, llc::LT, std::max(jv, rational(0)));
        }
        c().mk_ineq(sign, m.var(), llc::LT);
        c().mk_ineq(sign, m.var(), llc::GE, v);
    }
    TRACE("nla_solver", c().print_lemma(tout););
}
// todo : consider using generate_simple_tangent_lemma on each factorization
 */
void tangents::generate_two_tang_lines(const factorization & bf, const point& xy, lpvar j) {
    add_empty_lemma();
    c().mk_ineq(var(bf[0]), llc::NE, xy.x);
    c().mk_ineq(j, - xy.x, var(bf[1]), llc::EQ);
        
    add_empty_lemma();
    c().mk_ineq(var(bf[1]), llc::NE, xy.y);
    c().mk_ineq(j, - xy.y, var(bf[0]), llc::EQ);
}

// Get two planes tangent to surface z = xy, one at point a,  and another at point b.
// One can show that these planes still create a cut.
void tangents::get_initial_tang_points(point &a, point &b, const point& xy,
                                   bool below) const {
    const rational& x = xy.x;
    const rational& y = xy.y;
    if (!below){
        a = point(x - rational(1), y + rational(1));
        b = point(x + rational(1), y - rational(1));
    }
    else {
        a = point(x - rational(1), y - rational(1));
        b = point(x + rational(1), y + rational(1));
    }
}

void tangents::push_tang_point(point &a, const point& xy, bool below, const rational& correct_val, const rational& val) const {
    SASSERT(correct_val ==  xy.x * xy.y);
    int steps = 10;
    point del = a - xy;
    while (steps--) {
        del *= rational(2);
        point na = xy + del;
        TRACE("nla_solver_tp", tout << "del = " << del << std::endl;);
        if (!plane_is_correct_cut(na, xy, correct_val, val, below)) {
            TRACE("nla_solver_tp", tout << "exit";tout << std::endl;);
            return;
        }
        a = na;
    }
}
    
void tangents::push_tang_points(point &a, point &b, const point& xy, bool below, const rational& correct_val, const rational& val) const {
    push_tang_point(a, xy, below, correct_val, val);
    push_tang_point(b, xy, below, correct_val, val);
}

rational tangents::tang_plane(const point& a, const point& x) const {
    return  a.x * x.y + a.y * x.x - a.x * a.y;
}

bool tangents:: plane_is_correct_cut(const point& plane,
                                 const point& xy,
                                 const rational & correct_val,                             
                                 const rational & val,
                                 bool below) const {
    SASSERT(correct_val ==  xy.x * xy.y);
    if (below && val > correct_val) return false;
    rational sign = below? rational(1) : rational(-1);
    rational px = tang_plane(plane, xy);
    return ((correct_val - px)*sign).is_pos() && !((px - val)*sign).is_neg();
        
}

// "below" means that the val is below the surface xy 
void tangents::get_tang_points(point &a, point &b, bool below, const rational& val,
                           const point& xy) const {
    get_initial_tang_points(a, b, xy, below);
    auto correct_val = xy.x * xy.y;
    TRACE("nla_solver", tout << "xy = " << xy << ", correct val = " << xy.x * xy.y;
          tout << "\ntang points:"; print_tangent_domain(a, b, tout);tout << std::endl;);
    TRACE("nla_solver", tout << "tang_plane(a, xy) = " << tang_plane(a, xy) << " , val = " << val;
          tout << "\ntang_plane(b, xy) = " << tang_plane(b, xy); tout << std::endl;);
    SASSERT(plane_is_correct_cut(a, xy, correct_val, val, below));
    SASSERT(plane_is_correct_cut(b, xy, correct_val, val, below));
    push_tang_points(a, b, xy, below, correct_val, val);
    TRACE("nla_solver", tout << "pushed a = " << a << "\npushed b = " << b << std::endl;);
}
}
