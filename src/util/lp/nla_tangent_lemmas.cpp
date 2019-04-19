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
template <typename T> rational tangents::vvr(T const& t) const { return m_core->vvr(t); }

tangents::tangents(core * c) : common(c) {}
std::ostream& tangents::print_point(const point &a, std::ostream& out) const {
    out << "(" << a.x <<  ", " << a.y << ")";
    return out;
}
    
std::ostream& tangents::print_tangent_domain(const point &a, const point &b, std::ostream& out) const {
    out << "("; print_point(a, out);  out <<  ", "; print_point(b, out); out <<  ")";
    return out;
}
void tangents::generate_simple_tangent_lemma(const smon* rm) {
    if (rm->size() != 2)
        return;
    TRACE("nla_solver", tout << "rm:" << *rm << std::endl;);
    m_core->add_empty_lemma();
    const monomial & m = c().m_emons[rm->var()];
    const rational v = c().product_value(m);
    const rational& mv = vvr(m);
    SASSERT(mv != v);
    SASSERT(!mv.is_zero() && !v.is_zero());
    rational sign = rational(nla::rat_sign(mv));
    if (sign != nla::rat_sign(v)) {
        c().generate_simple_sign_lemma(-sign, m);
        return;
    }
    bool gt = abs(mv) > abs(v);
    if (gt) {
        for (lpvar j : m) {
            const rational & jv = vvr(j);
            rational js = rational(nla::rat_sign(jv));
            c().mk_ineq(js, j, llc::LT);
            c().mk_ineq(js, j, llc::GT, jv);
        }
        c().mk_ineq(sign, rm->var(), llc::LE, std::max(v, rational(-1)));
    } else {
        for (lpvar j : m) {
            const rational & jv = vvr(j);
            rational js = rational(nla::rat_sign(jv));
            c().mk_ineq(js, j, llc::LT, std::max(jv, rational(0)));
        }
        c().mk_ineq(sign, m.var(), llc::LT);
        c().mk_ineq(sign, m.var(), llc::GE, v);
    }
    TRACE("nla_solver", c().print_lemma(tout););
}
    
void tangents::tangent_lemma() {
    bfc bf;
    lpvar j;
    rational sign;
    const smon* rm = nullptr;
        
    if (c().find_bfc_to_refine(bf, j, sign, rm)) {
        tangent_lemma_bf(bf, j, sign, rm);
    } else {
        TRACE("nla_solver", tout << "cannot find a bfc to refine\n"; );
        if (rm != nullptr)
            generate_simple_tangent_lemma(rm);
    }
}

void tangents::generate_explanations_of_tang_lemma(const smon& rm, const bfc& bf, lp::explanation& exp) {
    // here we repeat the same explanation for each lemma
    c().explain(rm, exp);
    c().explain(bf.m_x, exp);
    c().explain(bf.m_y, exp);
}

void tangents::generate_tang_plane(const rational & a, const rational& b, const factor& x, const factor& y, bool below, lpvar j, const rational& j_sign) {
    lpvar jx = var(x);
    lpvar jy = var(y);
    add_empty_lemma();
    c().negate_relation(jx, a);
    c().negate_relation(jy, b);
    bool sbelow = j_sign.is_pos()? below: !below;
#if Z3DEBUG
    int mult_sign = nla::rat_sign(a - vvr(jx))*nla::rat_sign(b - vvr(jy));
    SASSERT((mult_sign == 1) == sbelow);
    // If "mult_sign is 1"  then (a - x)(b-y) > 0 and ab - bx - ay + xy > 0
    // or -ab + bx + ay < xy or -ay - bx + xy > -ab
    // j_sign*vvr(j) stands for xy. So, finally we have  -ay - bx + j_sign*j > - ab
#endif

    lp::lar_term t;
    t.add_coeff_var(-a, jy);
    t.add_coeff_var(-b, jx);
    t.add_coeff_var( j_sign, j);
    c().mk_ineq(t, sbelow? llc::GT : llc::LT, - a*b);
}  
void tangents::tangent_lemma_bf(const bfc& bf, lpvar j, const rational& sign, const smon* rm){
    point a, b;
    point xy (vvr(bf.m_x), vvr(bf.m_y));
    rational correct_mult_val =  xy.x * xy.y;
    rational val = vvr(j) * sign;
    bool below = val < correct_mult_val;
    TRACE("nla_solver", tout << "rm = " << rm << ", below = " << below << std::endl; );
    get_tang_points(a, b, below, val, xy);
    TRACE("nla_solver", tout << "sign = " << sign << ", tang domain = "; print_tangent_domain(a, b, tout); tout << std::endl;);
    unsigned lemmas_size_was = c().m_lemma_vec->size();
    generate_two_tang_lines(bf, xy, sign, j);
    generate_tang_plane(a.x, a.y, bf.m_x, bf.m_y, below, j, sign);
    generate_tang_plane(b.x, b.y, bf.m_x, bf.m_y, below, j, sign);
    // if rm == nullptr there is no need to explain equivs since we work on a monomial and not on a rooted monomial
    if (rm != nullptr) { 
        lp::explanation expl;
        generate_explanations_of_tang_lemma(*rm, bf, expl);
        for (unsigned i = lemmas_size_was; i < c().m_lemma_vec->size(); i++) {
            auto &l = ((*c().m_lemma_vec)[i]);
            l.expl().add(expl);
        }
    }
    TRACE("nla_solver",
          for (unsigned i = lemmas_size_was; i < c().m_lemma_vec->size(); i++) 
              c().print_specific_lemma((*c().m_lemma_vec)[i], tout); );
}
    
void tangents::generate_two_tang_lines(const bfc & bf, const point& xy, const rational& sign, lpvar j) {
    add_empty_lemma();
    c().mk_ineq(var(bf.m_x), llc::NE, xy.x);
    c().mk_ineq(sign, j, - xy.x, var(bf.m_y), llc::EQ);
        
    add_empty_lemma();
    c().mk_ineq(var(bf.m_y), llc::NE, xy.y);
    c().mk_ineq(sign, j, - xy.y, var(bf.m_x), llc::EQ);
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
        TRACE("nla_solver", tout << "del = "; print_point(del, tout); tout << std::endl;);
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
    TRACE("nla_solver", tout << "xy = "; print_point(xy, tout); tout << ", correct val = " << xy.x * xy.y;
          tout << "\ntang points:"; print_tangent_domain(a, b, tout);tout << std::endl;);
    TRACE("nla_solver", tout << "tang_plane(a, xy) = " << tang_plane(a, xy) << " , val = " << val;
          tout << "\ntang_plane(b, xy) = " << tang_plane(b, xy); tout << std::endl;);
    SASSERT(plane_is_correct_cut(a, xy, correct_val, val, below));
    SASSERT(plane_is_correct_cut(b, xy, correct_val, val, below));
    push_tang_points(a, b, xy, below, correct_val, val);
    TRACE("nla_solver", tout << "pushed a = "; print_point(a, tout); tout << "\npushed b = "; print_point(b, tout); tout << std::endl;);
}
}

