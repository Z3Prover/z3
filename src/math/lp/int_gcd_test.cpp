/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    int_gcd_test.cpp

Abstract:

    Gcd_Test heuristic

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:
--*/

#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/int_gcd_test.h"

namespace lp {

    int_gcd_test::int_gcd_test(int_solver& lia): lia(lia), lra(lia.lra), m_next_gcd(0), m_delay(0) {}

    bool int_gcd_test::should_apply() {

        if (!lia.settings().m_int_run_gcd_test)
            return false;
#if 1
        return true;
#else
        if (m_delay == 0) {
            return true;
        }
        --m_delay;
        return false;
#endif
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
        auto & A = lra.A_r(); // getting the matrix
        for (unsigned i = 0; i < A.row_count(); i++)
            if (!gcd_test_for_row(A, i)) 
                return false;        
        return true;
    }
    
    static mpq get_denominators_lcm(const row_strip<mpq> & row) {
        mpq r(1);
        for  (auto & c : row) {
            r = lcm(r, denominator(c.coeff()));
        }
        return r;
    }
    
    bool int_gcd_test::gcd_test_for_row(static_matrix<mpq, numeric_pair<mpq>> & A, unsigned i) {
        auto const& row = A.m_rows[i];
        auto & lcs = lra.m_mpq_lar_core_solver;
        unsigned basic_var = lcs.m_r_basis[i];
        
        if (!lia.column_is_int(basic_var) || lia.get_value(basic_var).is_int())
            return true;
        mpq lcm_den = get_denominators_lcm(row);
        mpq consts(0);
        mpq gcds(0);
        mpq least_coeff(0);
        bool    least_coeff_is_bounded = false;
        unsigned j;
        for (auto &c : A.m_rows[i]) {
            j = c.var();
            const mpq& a = c.coeff();
            if (lra.column_is_fixed(j)) {
                mpq aux = lcm_den * a;
                consts += aux * lra.column_lower_bound(j).x;
            }
            else if (lra.column_is_real(j)) {
                return true;
            }
            else if (gcds.is_zero()) {
                gcds = abs(lcm_den * a);
                least_coeff = gcds;
                least_coeff_is_bounded = lra.column_is_bounded(j);
            }
            else {
                mpq aux = abs(lcm_den * a);
                gcds = gcd(gcds, aux);
                if (aux < least_coeff) {
                    least_coeff = aux;
                    least_coeff_is_bounded = lra.column_is_bounded(j);
                }
                else if (least_coeff_is_bounded && aux == least_coeff) {
                    least_coeff_is_bounded = lra.column_is_bounded(j);
                }
            }
            SASSERT(gcds.is_int());
            SASSERT(least_coeff.is_int());
            TRACE("gcd_test_bug", tout << "coeff: " << a << ", gcds: " << gcds 
                  << " least_coeff: " << least_coeff << " consts: " << consts << "\n";);
            
        }
        
        if (gcds.is_zero()) {
            // All variables are fixed.
            // This theory guarantees that the assignment satisfies each row, and
            // fixed integer variables are assigned to integer values.
            return true;
        }
        
        if (!(consts / gcds).is_int()) {
            TRACE("gcd_test", tout << "row failed the GCD test:\n"; lia.display_row_info(tout, i););
            fill_explanation_from_fixed_columns(A.m_rows[i]);
            return false;
        }
        
        if (least_coeff.is_one() && !least_coeff_is_bounded) {
            SASSERT(gcds.is_one());
            return true;
        }
        
        if (least_coeff_is_bounded) {
            return ext_gcd_test(A.m_rows[i], least_coeff, lcm_den, consts);
        }
        return true;
    }
    
    bool int_gcd_test::ext_gcd_test(const row_strip<mpq> & row,
                                  mpq const & least_coeff, 
                                  mpq const & lcm_den,
                                  mpq const & consts) {
        TRACE("ext_gcd_test", tout << "row = "; lra.print_row(row, tout););
        mpq gcds(0);
        mpq l(consts);
        mpq u(consts);
        
        mpq a;
        unsigned j;
        for (const auto & c : row) {
            j = c.var();
            TRACE("ext_gcd_test", tout << "col = "; lra.m_mpq_lar_core_solver.m_r_solver.print_column_bound_info(j, tout););
            const mpq & a = c.coeff();
            if (lra.column_is_fixed(j))
                continue;
            SASSERT(!lra.column_is_real(j));
            mpq ncoeff = lcm_den * a;
            SASSERT(ncoeff.is_int());
            mpq abs_ncoeff = abs(ncoeff);
            if (abs_ncoeff == least_coeff) {
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
        lia.m_ex->push_justification(lc);
        lia.m_ex->push_justification(uc);
    }

}
