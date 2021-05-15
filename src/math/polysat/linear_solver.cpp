/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    linear_solver.cpp
    
Author:

    Nikolaj Bjorner (nbjorner) 2021-05-14
    Jakob Rath 2021-05-14

--*/

#include "math/polysat/linear_solver.h"
#include "math/polysat/solver.h"

namespace polysat {

    void linear_solver::push() {
        m_trail.push_back(trail_i::inc_level_i);
    }

    void linear_solver::pop(unsigned n) {
        while (n > 0) {
            switch (m_trail.back()) {
            case trail_i::inc_level_i:
                --n;
                break;
            case trail_i::add_var_i:
                NOT_IMPLEMENTED_YET();
                break;
            case trail_i::set_bound_i: {
                auto [v, sz] = m_rows.back();
                sz2fixplex(sz).restore_bound();
                m_rows.pop_back();
                break;
            }
            case trail_i::set_value_i:
                break;
            case trail_i::add_row_i: {
                auto [v, sz] = m_rows.back();
                sz2fixplex(sz).del_row(v);
                m_rows.pop_back();
                break;
            }
            case trail_i::activate_constraint_i:
                // not needed?
                NOT_IMPLEMENTED_YET();
                break;
            default:
                UNREACHABLE();
            }
            m_trail.pop_back();
        }
    }

    fixplex_base& linear_solver::sz2fixplex(unsigned sz) { 
        fixplex_base* b = m_fix.get(sz, nullptr);
        if (!b) {
            switch (sz) {
            case 64:
                b = alloc(fixplex<uint64_ext>, s.m_lim);
                break;
            case 8:
            case 16:
            case 32:
            case 128:
            case 256:
            default:
                NOT_IMPLEMENTED_YET();
                break;
            }
            m_fix.set(sz, b);
        }
        return *b;
    }        

    void linear_solver::new_constraint(constraint& c) {
        switch (c.kind()) {
        case ckind_t::eq_t: {
            //
            // create the row c.p() - v == 0
            // when equality is asserted, set range on v as v == 0 or v > 0.
            //
            pdd p = c.to_eq().p();
            unsigned sz = p.power_of_2();
            linearize(p);
            var_t v = fresh_var(sz);
            m_vars.push_back(v);
            m_coeffs.push_back(rational::power_of_two(sz) - 1);
            sz2fixplex(sz).add_row(v, m_vars.size(), m_vars.data(), m_coeffs.data());
            m_rows.push_back(std::make_pair(v, sz));
            m_trail.push_back(trail_i::add_row_i);
            m_bool_var2row.setx(c.bvar(), v, UINT_MAX);
            break;
        }
        case ckind_t::ule_t:
        case ckind_t::bit_t:
            break;
        }
    }

    void linear_solver::activate_constraint(constraint& c) {
        switch (c.kind()) {
        case ckind_t::eq_t: {
            var_t v = m_bool_var2row[c.bvar()];
            pdd p = c.to_eq().p();
            unsigned sz = p.power_of_2();
            auto& fp = sz2fixplex(sz);
            
            m_trail.push_back(trail_i::set_bound_i);
            m_rows.push_back(std::make_pair(v, sz));
            if (c.is_positive()) 
                fp.set_bounds(v, rational::zero(), rational::zero());
            else 
                fp.set_bounds(v, rational::one(), rational::power_of_two(sz) - 1);
            break;
        }
        case ckind_t::ule_t:
        case ckind_t::bit_t:
            break;
        }
    }

    void linear_solver::linearize(pdd const& p) {
        unsigned sz = p.power_of_2();
        m_vars.reset();
        m_coeffs.reset();
        for (auto const& m : p) {
            m_vars.push_back(mono2var(sz, m.vars));
            m_coeffs.push_back(m.coeff);
        }        
    }

    var_t linear_solver::mono2var(unsigned sz, unsigned_vector const& var) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }

    var_t linear_solver::fresh_var(unsigned sz) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }

    void linear_solver::set_value(pvar v, rational const& value) {
    }

    void linear_solver::set_bound(pvar v, rational const& lo, rational const& hi) {
        unsigned sz = s.size(v);
        auto& fp = sz2fixplex(sz);
        m_trail.push_back(trail_i::set_bound_i);
        m_rows.push_back(std::make_pair(v, sz));
        fp.set_bounds(v, lo, hi);        
    }
    
    // check integer modular feasibility under current bounds.
    lbool linear_solver::check() { 
        return l_undef; 
    }

    void linear_solver::unsat_core(unsigned_vector& deps) {
    }

    // current value assigned to (linear) variable according to tableau.
    rational linear_solver::value(pvar v) { 
        return rational(0); 
    }
    
};

