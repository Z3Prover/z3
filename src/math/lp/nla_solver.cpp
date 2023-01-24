/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)
  --*/
#include "math/lp/nla_solver.h"
#include <map>
#include "math/lp/monic.h"
#include "math/lp/lp_utils.h"
#include "math/lp/var_eqs.h"
#include "math/lp/factorization.h"
#include "math/lp/nla_solver.h"
#include "math/lp/nla_core.h"
#include "math/polynomial/algebraic_numbers.h"

namespace nla {

    nla_settings& solver::settings() { return m_core->m_nla_settings; }

    void solver::add_monic(lpvar v, unsigned sz, lpvar const* vs) {
        m_core->add_monic(v, sz, vs);
    }
    
    bool solver::is_monic_var(lpvar v) const {
        return m_core->is_monic_var(v);
    }
    
    bool solver::need_check() { return true; }
    
    lbool solver::check(vector<lemma>& l) {
        return m_core->check(l);
    }
    
    void solver::push(){
        m_core->push();
    }
    
    void solver::pop(unsigned n) {
        m_core->pop(n);
    }
    
    solver::solver(lp::lar_solver& s, reslimit& limit): 
        m_core(alloc(core, s, limit)) {
    }
    
    bool solver::influences_nl_var(lpvar j) const {    
        return m_core->influences_nl_var(j);
    }
    
    solver::~solver() {
        dealloc(m_core);
    }
    
    std::ostream& solver::display(std::ostream& out) const {    
        m_core->print_monics(out);
        if (use_nra_model()) 
            m_core->m_nra.display(out);
        return out;
    }
    
    bool solver::use_nra_model() const { return m_core->use_nra_model(); }

    core& solver::get_core() { return *m_core; }

    nlsat::anum_manager& solver::am() { return m_core->m_nra.am(); }

    nlsat::anum const& solver::am_value(lp::var_index v) const {
        SASSERT(use_nra_model());
        return m_core->m_nra.value(v);
    }
    
    void solver::collect_statistics(::statistics & st) {
        m_core->collect_statistics(st);
    }

    // ensure r = x^y, add abstraction/refinement lemmas
    lbool solver::check_power(lpvar r, lpvar x, lpvar y, vector<lemma>& lemmas) {
        if (x == null_lpvar || y == null_lpvar || r == null_lpvar)
            return l_undef;
        
        if (use_nra_model()) 
            return l_undef;

        auto xval = m_core->val(x);
        auto yval = m_core->val(y);
        auto rval = m_core->val(r);

        core& c = get_core();
        c.set_lemma_vec(lemmas);
        lemmas.reset();

        // x >= x0 > 0, y >= y0 > 0 => r >= x0^y0
        // x >= x0 > 0, y <= y0 => r <= x0^y0
        // x != 0, y = 0 => r = 1
        // x = 0, y != 0 => r = 0
        // 
        // for x fixed, it is exponentiation
        // => use tangent lemmas and error tolerance.

        if (xval > 0 && yval.is_unsigned()) {
            auto r2val = power(xval, yval.get_unsigned());
            if (rval == r2val)
                return l_true;
            if (xval != 0 && yval == 0) {
                new_lemma lemma(c, "x != 0 => x^0 = 1");
                lemma |= ineq(x, llc::EQ, rational::zero());
                lemma |= ineq(y, llc::NE, rational::zero());
                lemma |= ineq(r, llc::EQ, rational::one());
                return l_false;
            }
            if (xval == 0 && yval > 0) {
                new_lemma lemma(c, "y != 0 => 0^y = 0");
                lemma |= ineq(x, llc::NE, rational::zero());
                lemma |= ineq(y, llc::EQ, rational::zero());
                lemma |= ineq(r, llc::EQ, rational::zero());
                return l_false;
            }
            if (xval > 0 && r2val < rval) {
                SASSERT(yval > 0);
                new_lemma lemma(c, "x >= x0 > 0, y >= y0 > 0 => r >= x0^y0");
                lemma |= ineq(x, llc::LT, xval);
                lemma |= ineq(y, llc::LT, yval);
                lemma |= ineq(r, llc::GE, r2val);
                return l_false;
            }
            if (xval > 0 && r2val < rval) {
                new_lemma lemma(c, "x >= x0 > 0, y <= y0 => r <= x0^y0");
                lemma |= ineq(x, llc::LT, xval);
                lemma |= ineq(y, llc::GT, yval);
                lemma |= ineq(r, llc::LE, r2val);
                return l_false;
            }
        }
        if (xval > 0 && yval > 0 && !yval.is_int()) {
            auto ynum = numerator(yval);
            auto yden = denominator(yval);
            if (!ynum.is_unsigned())
                return l_undef;
            if (!yden.is_unsigned())
                return l_undef;
            //   r = x^{yn/yd}
            // <=>
            //   r^yd = x^yn
            auto ryd = power(rval, yden.get_unsigned());
            auto xyn = power(xval, ynum.get_unsigned());
            if (ryd == xyn)
                return l_true;
#if 0
            // try some root approximation instead?
            if (ryd > xyn) {
                // todo
            }
            if (ryd < xyn) {
                // todo
            }
#endif

        }


        return l_undef;

        // anum isn't initialized unless nra_solver is invoked.
        // there is no proviso for using algebraic numbers outside of the nra solver.
        // so either we have a rational refinement version _and_ an algebraic numeral refinement
        // loop or we introduce algebraic numerals outside of the nra_solver

#if 0
        scoped_anum xval(am()), yval(am()), rval(am());

        am().set(xval, am_value(x));
        am().set(yval, am_value(y));
        am().set(rval, am_value(r));
#endif

    }

}
