/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    linear_solver.cpp
    
Author:

    Nikolaj Bjorner (nbjorner) 2021-05-14
    Jakob Rath 2021-05-14

--*/

#include "math/polysat/linear_solver.h"
#include "math/polysat/fixplex_def.h"
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
            case trail_i::add_var_i: {
                auto [v, sz] = m_rows.back();
                --m_sz2num_vars[sz];
                m_rows.pop_back();
                break;
            }
            case trail_i::add_mono_i: {
                auto m = m_monomials.back();
                m_mono2var.erase(m);
                m_alloc.deallocate(m.num_vars*sizeof(unsigned), m.vars);
                m_monomials.pop_back();
                break;
            }
            case trail_i::set_bound_i: {
                auto [v, sz] = m_rows.back();
                sz2fixplex(sz).restore_bound();
                m_rows.pop_back();
                break;
            }
            case trail_i::add_row_i: {
                auto [v, sz] = m_rows.back();
                sz2fixplex(sz).del_row(v);
                m_rows.pop_back();
                break;
            }
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


    var_t linear_solver::internalize_pdd(pdd const& p) {
        unsigned sz = p.power_of_2();
        linearize(p);
        if (m_vars.size() == 1 && m_coeffs.back() == 1) 
            return m_vars.back();
        var_t v = fresh_var(sz);
        m_vars.push_back(v);
        m_coeffs.push_back(rational::power_of_two(sz) - 1);
        sz2fixplex(sz).add_row(v, m_vars.size(), m_vars.data(), m_coeffs.data());
        m_rows.push_back(std::make_pair(v, sz));
        m_trail.push_back(trail_i::add_row_i);
        return v;
    }
    
    /**
     * create the row c.p() - v == 0
     * when equality is asserted, set range on v as v == 0 or v > 0.
     */
        
    void linear_solver::new_eq(eq_constraint& c) {
        var_t v = internalize_pdd(c.p());
        auto pr = std::make_pair(v, v);
        m_bool_var2row.setx(c.bvar(), pr, pr);
    }
    
    void linear_solver::assert_eq(eq_constraint& c) {
        var_t v = m_bool_var2row[c.bvar()].first;
        unsigned sz = c.p().power_of_2();
        auto& fp = sz2fixplex(sz);            
        m_trail.push_back(trail_i::set_bound_i);
        m_rows.push_back(std::make_pair(v, sz));
        rational z(0), o(1);
        if (c.is_positive()) 
            fp.set_bounds(v, z, z);
        else 
            fp.set_bounds(v, o, z);
}

    void linear_solver::new_le(ule_constraint& c) {
        var_t v = internalize_pdd(c.lhs());
        var_t w = internalize_pdd(c.rhs());
        auto pr = std::make_pair(v, w);
        m_bool_var2row.setx(c.bvar(), pr, pr);
    }

    void linear_solver::assert_le(ule_constraint& c) {
        auto [v, w] = m_bool_var2row[c.bvar()];
        // v <= w:
        // static constraints:
        // - lo(v) <= lo(w)
        // - hi(v) <= hi(w)
        //
        // special case for inequalities with constant bounds
        // bounds propagation on fp, then bounds strengthening
        // based on static constraints
        // internal backtrack search over bounds
        // inequality graph (with offsets)
        // 
    }

    void linear_solver::new_bit(var_constraint& c) {
    }

    void linear_solver::assert_bit(var_constraint& c) {

    }


    void linear_solver::new_constraint(constraint& c) {
        switch (c.kind()) {
        case ckind_t::eq_t: 
            new_eq(c.to_eq());
            break;        
        case ckind_t::ule_t:
            new_le(c.to_ule());
            break;
        case ckind_t::bit_t:
            new_bit(c.to_bit());
            break;
        default:
            UNREACHABLE();
            break;
        }
    }

    void linear_solver::activate_constraint(constraint& c) {
        switch (c.kind()) {
        case ckind_t::eq_t: 
            assert_eq(c.to_eq());
            break;        
        case ckind_t::ule_t:
            assert_le(c.to_ule());
            break;
        case ckind_t::bit_t:
            assert_bit(c.to_bit());            
            break;
        default:
            UNREACHABLE();
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
        mono_info m(sz, var.size(), var.data()), m1;
        if (m_mono2var.find(m, m1))
            return m1.var;
        m.vars = static_cast<unsigned*>(m_alloc.allocate(var.size()*sizeof(unsigned)));
        for (unsigned i = 0; i < var.size(); var.data()) 
            m.vars[i] = var[i];
        m.var = fresh_var(sz);
        m_mono2var.insert(m);
        m_monomials.push_back(m);
        m_trail.push_back(trail_i::add_mono_i);
        return m.var;
    }

    var_t linear_solver::pvar2var(unsigned sz, pvar v) {
        unsigned_vector vars;
        vars.push_back(v);
        return mono2var(sz, vars);
    }

    var_t linear_solver::fresh_var(unsigned sz) {
        m_sz2num_vars.reserve(sz + 1);
        m_trail.push_back(trail_i::add_var_i);
        m_rows.push_back(std::make_pair(0, sz));
        return m_sz2num_vars[sz]++;
    }

    void linear_solver::set_value(pvar v, rational const& value) {
        unsigned sz = s.size(v);
        auto& fp = sz2fixplex(sz);
        var_t w = pvar2var(sz, v);
        m_trail.push_back(trail_i::set_bound_i);
        m_rows.push_back(std::make_pair(w, sz));
        fp.set_value(w, value);        
    }

    void linear_solver::set_bound(pvar v, rational const& lo, rational const& hi) {
        unsigned sz = s.size(v);
        auto& fp = sz2fixplex(sz);
        var_t w = pvar2var(sz, v);
        m_trail.push_back(trail_i::set_bound_i);
        m_rows.push_back(std::make_pair(w, sz));
        fp.set_bounds(w, lo, hi);        
    }
    
    // check integer modular feasibility under current bounds.
    // and inequalities
    lbool linear_solver::check() { 
        lbool res = l_true;
        for (auto* f : m_fix) {
            if (!f)
                continue;
            lbool r = f->make_feasible();
            if (r == l_false) {
                // m_unsat_f = f;
                return r;
            }
            if (r == l_undef)
                res = l_undef;
        }
        return res; 
    }

    void linear_solver::unsat_core(unsigned_vector& deps) {
        NOT_IMPLEMENTED_YET();
    }

    // current value assigned to (linear) variable according to tableau.
    rational linear_solver::value(pvar v) { 
        return rational(0); 
    }
    
};

