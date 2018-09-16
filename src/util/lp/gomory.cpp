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
#include "util/lp/gomory.h"
#include "util/lp/int_solver.h"
#include "util/lp/lar_solver.h"
namespace lp {

class gomory::imp {
    lar_term   &          m_t; // the term to return in the cut
    mpq        &          m_k; // the right side of the cut
    explanation&          m_ex; // the conflict explanation
    unsigned              m_inf_col; // a basis column which has to be an integer but has a not integral value
    const row_strip<mpq>& m_row;
    const int_solver&           m_int_solver;


    const impq & get_value(unsigned j) const { return m_int_solver.get_value(j); }
    bool is_real(unsigned j) const { return m_int_solver.is_real(j); }
    bool at_lower(unsigned j) const { return m_int_solver.at_lower(j); }
    bool at_upper(unsigned j) const { return m_int_solver.at_upper(j); }
    const impq & lower_bound(unsigned j) const { return m_int_solver.lower_bound(j); }
    const impq & upper_bound(unsigned j) const  { return m_int_solver.upper_bound(j); }
    constraint_index column_lower_bound_constraint(unsigned j) const { return m_int_solver.column_lower_bound_constraint(j); }
    constraint_index column_upper_bound_constraint(unsigned j) const { return m_int_solver.column_upper_bound_constraint(j); }
    bool column_is_fixed(unsigned j) const { return m_int_solver.m_lar_solver->column_is_fixed(j); }
    void int_case_in_gomory_cut(const mpq & a, unsigned j,
                                            mpq & lcm_den, const mpq& f0, const mpq& one_minus_f0) {
        lp_assert(is_int(j) && !a.is_int());
        mpq fj =  int_solver::fractional_part(a);
        lp_assert(fj.is_pos());
        TRACE("gomory_cut_detail", 
              tout << a << " j=" << j << " k = " << m_k;
              tout << ", fj: " << fj << ", ";
              tout << "f0: " << f0 << ", ";
              tout << "1 - f0: " << 1 - f0 << ", ";
              tout << (at_lower(j)?"at_lower":"at_upper")<< std::endl;
              );
        mpq new_a;
        mpq one_minus_fj = 1 - fj;
        if (at_lower(j)) {
            mpq fj_over_one_min_f0 = fj / one_minus_f0;
            mpq one_minus_fj_over_f0 = one_minus_fj / f0;
            new_a = fj_over_one_min_f0 < one_minus_fj_over_f0? fj_over_one_min_f0 : one_minus_fj_over_f0;
            m_k.addmul(new_a, lower_bound(j).x);
            m_ex.push_justification(column_lower_bound_constraint(j), new_a);
        }
        else {
            mpq fj_over_f0 = fj / f0;
            mpq one_minus_fj_over_one_minus_f0 = one_minus_fj / one_minus_f0;
            lp_assert(at_upper(j));
            // the upper terms are inverted - therefore we have -
            new_a = - (fj_over_f0 < one_minus_fj_over_one_minus_f0? fj_over_f0 : one_minus_fj_over_one_minus_f0);
            m_k.addmul(new_a, upper_bound(j).x);
            m_ex.push_justification(column_upper_bound_constraint(j), new_a);
        }
        TRACE("gomory_cut_detail", tout << "new_a: " << new_a << " k: " << m_k << "\n";);
        m_t.add_monomial(new_a, j);
        lcm_den = lcm(lcm_den, denominator(new_a));
    }

    void real_case_in_gomory_cut(const mpq & a, unsigned x_j, const mpq& f0, const mpq& one_minus_f0) {
        TRACE("gomory_cut_detail_real", tout << "real\n";);
        mpq new_a;
        if (at_lower(x_j)) {
            if (a.is_pos()) {
                new_a  =  a / one_minus_f0;
            }
            else {
                new_a  =  a / f0;
                new_a.neg();
            }
            m_k.addmul(new_a, lower_bound(x_j).x); // is it a faster operation than
            // k += lower_bound(x_j).x * new_a;  
            m_ex.push_justification(column_lower_bound_constraint(x_j), new_a);
        }
        else {
            lp_assert(at_upper(x_j));
            if (a.is_pos()) {
                new_a =   a / f0; 
                new_a.neg(); // the upper terms are inverted.
            }
            else {
                new_a =   a / one_minus_f0; 
            }
            m_k.addmul(new_a, upper_bound(x_j).x); //  k += upper_bound(x_j).x * new_a; 
            m_ex.push_justification(column_upper_bound_constraint(x_j), new_a);
        }
        TRACE("gomory_cut_detail_real", tout << a << "*v" << x_j << " k: " << m_k << "\n";);
        m_t.add_monomial(new_a, x_j);
    }

    lia_move report_conflict_from_gomory_cut() {
        lp_assert(m_k.is_pos());
        // conflict 0 >= k where k is positive
        m_k.neg(); // returning 0 <= -k
        return lia_move::conflict;
    }

    void adjust_term_and_k_for_some_ints_case_gomory(mpq &lcm_den) {
        lp_assert(!m_t.is_empty());
        auto pol = m_t.coeffs_as_vector();
        m_t.clear();
        if (pol.size() == 1) {
            TRACE("gomory_cut_detail", tout << "pol.size() is 1" << std::endl;);
            unsigned v = pol[0].second;
            lp_assert(is_int(v));
            const mpq& a = pol[0].first;
            m_k /= a;
            if (a.is_pos()) { // we have av >= k
                if (!m_k.is_int())
                    m_k = ceil(m_k);
                // switch size
                m_t.add_monomial(- mpq(1), v);
                m_k.neg();
            } else {
                if (!m_k.is_int())
                    m_k = floor(m_k);
                m_t.add_monomial(mpq(1), v);
            }
        } else {
            TRACE("gomory_cut_detail", tout << "pol.size() > 1" << std::endl;);
            lcm_den = lcm(lcm_den, denominator(m_k));
            lp_assert(lcm_den.is_pos());
            if (!lcm_den.is_one()) {
                // normalize coefficients of integer parameters to be integers.
                for (auto & pi: pol) {
                    pi.first *= lcm_den;
                    SASSERT(!is_int(pi.second) || pi.first.is_int());
                }
                m_k *= lcm_den;
            }
            // negate everything to return -pol <= -m_k
            for (const auto & pi: pol)
                m_t.add_monomial(-pi.first, pi.second);
            m_k.neg();
        }
        TRACE("gomory_cut_detail", tout << "k = " << m_k << std::endl;);
        lp_assert(m_k.is_int());
    }
public:
    lia_move create_cut() {
        TRACE("gomory_cut",
              tout << "applying cut at:\n"; m_int_solver.m_lar_solver->print_row(m_row, tout); tout << std::endl;
              for (auto & p : m_row) {
                  m_int_solver.m_lar_solver->m_mpq_lar_core_solver.m_r_solver.print_column_info(p.var(), tout);
              }
              tout << "inf_col = " << m_inf_col << std::endl;
              );
        
        // gomory will be   t <= k and the current solution has a property t > k
        m_k = 1;
        mpq lcm_den(1);
        bool some_int_columns = false;
        mpq f0  = int_solver::fractional_part(get_value(m_inf_col));
        mpq one_min_f0 = 1 - f0;
        for (const auto & p : m_row) {
            unsigned j = p.var();
            if (column_is_fixed(j)) {
                m_ex.push_justification(column_lower_bound_constraint(j));
                m_ex.push_justification(column_upper_bound_constraint(j));
                continue;
            }
            if (j == m_inf_col) {
                lp_assert(p.coeff() == one_of_type<mpq>());
                TRACE("gomory_cut_detail", tout << "seeing basic var";);
                continue;
            }
            // make the format compatible with the format used in: Integrating Simplex with DPLL(T)
            mpq a = - p.coeff();
            if (is_real(j)) 
                real_case_in_gomory_cut(a, j, f0, one_min_f0);
            else if (!a.is_int()) { // fj will be zero and no monomial will be added
                some_int_columns = true;
                int_case_in_gomory_cut(a, j, lcm_den, f0, one_min_f0);
            }
        }

        if (m_t.is_empty())
            return report_conflict_from_gomory_cut();
        if (some_int_columns)
            adjust_term_and_k_for_some_ints_case_gomory(lcm_den);
        lp_assert(m_int_solver.current_solution_is_inf_on_cut());
        m_int_solver.m_lar_solver->subs_term_columns(m_t, m_k);
        TRACE("gomory_cut", tout<<"gomory cut:"; m_int_solver.m_lar_solver->print_term(m_t, tout); tout << " <= " << m_k << std::endl;);
        return lia_move::cut;
    }
    imp(lar_term & t, mpq & k, explanation& ex, unsigned basic_inf_int_j, const row_strip<mpq>& row, const int_solver& int_slv ) :
        m_t(t),
        m_k(k),
        m_ex(ex),
        m_inf_col(basic_inf_int_j),
        m_row(row),
        m_int_solver(int_slv)
    {
    }
    
};

lia_move gomory::create_cut() {
    return m_imp->create_cut();
}

gomory::gomory(lar_term & t, mpq & k, explanation& ex, unsigned basic_inf_int_j, const row_strip<mpq>& row, const int_solver& s) {
    m_imp = alloc(imp, t, k, ex, basic_inf_int_j, row, s);
}

gomory::~gomory() { dealloc(m_imp); }

}
