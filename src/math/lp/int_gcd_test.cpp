/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    int_gcd_test.cpp

Abstract:

    Gcd_Test heuristic

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Notes:

Basic:
    For each row a*x + b = 0, where fixed variables are replaced by b, 
    check if gcd(a) divides b 

Extended:
    For each row a*x + b*y + c = 0, where 
    - the coefficients in a are all the same and smaller than the coefficients in b
    - the variables x are bounded
    Let l := a*lb(x), u := a*ub(x)
    - that is the lower and upper bounds for a*x based on the bounds for x.
    let ll := ceil  (l / gcd(b,c))
        uu := floor (u / gcd(b,c))
    If uu > ll, there is no space to find solutions for x within the bounds

Accumulative:
    For each row a*x + b*y - c = 0, where |a| = 1 < |b|, and x is a single variable,
    (it could also be a group of variables) accumulate constraint x = c mod b

    If there are row gcd constraints, such that 
    - x = c1 mod b1, from rows R1
    - x = c2 mod b2, from rows R2
    
    - If c1 mod gcd(b1,b2) != c2 mod gcd(b1,b2) report conflict for the rows involved.
   
    - Otherwise accumulate x = (c1 * lcm(b1,b2) / b2) + (c2 * lcm(b1,b2) / b1) mod lcm(b,b2)
      and accumulate the rows from R1, R2

 

--*/

#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/int_gcd_test.h"

namespace lp {

    int_gcd_test::int_gcd_test(int_solver& lia): lia(lia), lra(lia.lra), m_next_gcd(0), m_delay(0) {}

    bool int_gcd_test::should_apply() {
        return lia.settings().int_run_gcd_test();
    }

    lia_move int_gcd_test::operator()() {              
        lia.settings().stats().m_gcd_calls++;
        TRACE("int_solver", tout << "gcd-test " << lia.settings().stats().m_gcd_calls << "\n";);
        if (gcd_test()) {
            m_delay = m_next_gcd++;
            return lia_move::undef;
        }
        else {
            m_next_gcd = 0;
            m_delay = 0;
            lia.settings().stats().m_gcd_conflicts++;
            TRACE("gcd_test", tout << "gcd conflict\n";);
            return lia_move::conflict;
        }
    }

    bool int_gcd_test::gcd_test() {
        reset_test();
        const auto & A = lra.A_r(); // getting the matrix
        for (unsigned i = 0; i < A.row_count(); i++) {
            unsigned basic_var = lra.r_basis()[i];
            if (!lia.column_is_int(basic_var))
                continue;
            if (lia.get_value(basic_var).is_int())
                continue;
            if (!gcd_test_for_row(A, i)) 
                return false;        
            mark_visited(i);
        }
        for (unsigned i = m_inserted_vars.size(); i-- > 0; ) {
            unsigned j = m_inserted_vars[i];
            for (const auto & c : lra.get_column(j)) {
                unsigned r = c.var();
                if (is_visited(r))
                    continue;
                mark_visited(r);
                if (!gcd_test_for_row(A, r))
                    return false;
            }
        }
        return true;
    }
    
    static mpq get_denominators_lcm(const row_strip<mpq> & row) {
        mpq r(1);
        for (auto & c : row) 
            r = lcm(r, denominator(c.coeff()));
        return r;
    }
    
    bool int_gcd_test::gcd_test_for_row(const static_matrix<mpq, numeric_pair<mpq>> & A, unsigned i) {
        auto const& row = A.m_rows[i];
        unsigned basic_var = lra.r_basis()[i];
        
        if (!lia.column_is_int(basic_var))
            return true;
        m_lcm_den = get_denominators_lcm(row);
        m_consts = 0;
        mpq gcds(0);
        m_least_coeff = 0;
        bool least_coeff_is_bounded = false;
        bool least_coeff_is_unique = false;
        unsigned least_coeff_index = 0;
        for (auto &c : A.m_rows[i]) {
            unsigned j = c.var();
            const mpq& a = c.coeff();
            if (lra.column_is_fixed(j)) {
                mpq aux = m_lcm_den * a;
                m_consts += aux * lra.column_lower_bound(j).x;
            }
            else if (lra.column_is_real(j)) {
                return true;
            }
            else if (gcds.is_zero()) {
                gcds = abs(m_lcm_den * a);
                m_least_coeff = gcds;
                least_coeff_is_bounded = lra.column_is_bounded(j);
                least_coeff_is_unique = true;
                least_coeff_index = j;
            }
            else {
                mpq aux = abs(m_lcm_den * a);
                gcds = gcd(gcds, aux);
                if (aux < m_least_coeff) {
                    m_least_coeff = aux;
                    least_coeff_is_bounded = lra.column_is_bounded(j);
                    least_coeff_is_unique = true;
                    least_coeff_index = j;
                }
                else if (aux == m_least_coeff) {
                    least_coeff_is_bounded &= lra.column_is_bounded(j);
                    least_coeff_is_unique = false;
                }
            }
            SASSERT(gcds.is_int());
            SASSERT(m_least_coeff.is_int());
            TRACE("gcd_test_bug", tout << "coeff: " << a << ", gcds: " << gcds 
                  << " least_coeff: " << m_least_coeff << " consts: " << m_consts << "\n";);
            
        }
        
        if (gcds.is_zero()) {
            // All variables are fixed.
            // This theory guarantees that the assignment satisfies each row, and
            // fixed integer variables are assigned to integer values.
            return true;
        }
        
        if (!(m_consts / gcds).is_int()) {
            TRACE("gcd_test", tout << "row failed the GCD test:\n"; lia.display_row_info(tout, i););
            fill_explanation_from_fixed_columns(A.m_rows[i]);
            return false;
        }
                
        if (least_coeff_is_bounded && 
            !m_least_coeff.is_one() && 
            !lia.get_value(basic_var).is_int() && 
            !ext_gcd_test(A.m_rows[i]))
            return false;    

        if (!least_coeff_is_unique)
            return true;
    
        return accumulate_parity(row, least_coeff_index);
    }
    
    bool int_gcd_test::ext_gcd_test(const row_strip<mpq> & row) {
        TRACE("ext_gcd_test", tout << "row = "; lra.print_row(row, tout););
        mpq gcds(0);
        mpq l(m_consts);
        mpq u(m_consts);
        
        mpq a;
        unsigned j;
        for (const auto & c : row) {
            j = c.var();
            TRACE("ext_gcd_test", tout << "col = "; lra.print_column_info(j, tout););
            const mpq & a = c.coeff();
            if (lra.column_is_fixed(j))
                continue;
            SASSERT(!lra.column_is_real(j));
            mpq ncoeff = m_lcm_den * a;
            SASSERT(ncoeff.is_int());
            mpq abs_ncoeff = abs(ncoeff);
            if (abs_ncoeff == m_least_coeff) {
                SASSERT(lra.column_is_bounded(j));
                if (ncoeff.is_pos()) {
                    // l += ncoeff * lra.column_lower_bound(j).x;
                    l.addmul(ncoeff, lra.column_lower_bound(j).x);
                    // u += ncoeff * lra.column_upper_bound(j).x;
                    u.addmul(ncoeff, lra.column_upper_bound(j).x);
                }
                else {
                    // l += ncoeff * upper_bound(j).get_rational();
                    l.addmul(ncoeff, lra.column_upper_bound(j).x);
                    // u += ncoeff * lower_bound(j).get_rational();
                    u.addmul(ncoeff, lra.column_lower_bound(j).x);
                }
                add_to_explanation_from_fixed_or_boxed_column(j);
            }
            else if (gcds.is_zero()) {
                gcds = abs_ncoeff; 
            }
            else {
                gcds = gcd(gcds, abs_ncoeff);
            }
            SASSERT(gcds.is_int());
        }
        
        if (gcds.is_zero()) {
            return true;
        }
        
        mpq l1 = ceil(l/gcds);
        mpq u1 = floor(u/gcds);
        
        if (u1 < l1) {
            fill_explanation_from_fixed_columns(row);
            TRACE("gcd_test", tout << "row failed the GCD test:\n"; lia.display_row(tout, row););
            return false;
        }        
        return true;
    }

    void int_gcd_test::fill_explanation_from_fixed_columns(const row_strip<mpq> & row) {
        for (const auto & c : row) {
            if (lra.column_is_fixed(c.var()))
                add_to_explanation_from_fixed_or_boxed_column(c.var());
        }
    }

    void int_gcd_test::add_to_explanation_from_fixed_or_boxed_column(unsigned j) {
        constraint_index lc, uc;
        lra.get_bound_constraint_witnesses_for_column(j, lc, uc);
        lia.m_ex->push_back(lc);
        lia.m_ex->push_back(uc);
    }

    bool int_gcd_test::accumulate_parity(const row_strip<mpq> & row, unsigned least_idx) {

        // remove this line to enable new functionality.
        // return true;

        mpq modulus(0);
        bool least_sign = false;
        for (const auto & c : row) {
            unsigned j = c.var();
            const mpq& a = c.coeff();
            if (j == least_idx) 
                least_sign = a.is_neg();
            else if (!lra.column_is_fixed(j)) {
                mpq aux = abs(m_lcm_den * a);
                if (gcd(m_least_coeff, aux) != m_least_coeff)
                    return true;
                modulus = modulus == 0 ? aux : gcd(modulus, aux);
                if (modulus.is_one())
                    return true;
            }
        }
        modulus /= m_least_coeff;
        if (modulus == 0)
            return true;
        SASSERT(modulus.is_int());
        mpq offset = m_consts / m_least_coeff;
        if (!offset.is_int())
            return true;
        offset = mod(offset, modulus);
        if (!least_sign && offset != 0)
            offset = modulus - offset;
        TRACE("gcd_test", tout << least_idx << " modulus: " << modulus << " consts: " << m_consts << " sign " << least_sign << " offset: " << offset << "\n";);

        SASSERT(0 <= offset && offset < modulus);
        return insert_parity(least_idx, row, offset, modulus);
    }

    void int_gcd_test::reset_test() {
        for (auto j : m_inserted_vars)
            m_parities[j].pop_back();
        m_inserted_vars.reset();
        m_visited_ts++;
        if (m_visited_ts == 0) {
            m_visited.reset();
            m_visited_ts++;
        }
    }

    bool int_gcd_test::insert_parity(unsigned j, row_strip<mpq> const& r, mpq const& offset, mpq const& modulo) {
        m_parities.reserve(j + 1);

        // incomplete parity check.
        for (auto const& p : m_parities[j]) {            
            if (p.m_modulo != modulo)
                continue;
            if (p.m_offset == offset) 
                return true;
            else {
                fill_explanation_from_fixed_columns(r);
                fill_explanation_from_fixed_columns(*p.m_row);
                return false;
            }
        }
        m_inserted_vars.push_back(j);        
        m_parities[j].push_back(parity(offset, modulo, r));
        return true;
    }

}
