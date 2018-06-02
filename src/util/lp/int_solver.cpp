/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#include "util/lp/int_solver.h"
#include "util/lp/lar_solver.h"
#include "util/lp/lp_utils.h"
#include <utility>
#include "util/lp/monomial.h"
namespace lp {


void int_solver::trace_inf_rows() const {
    TRACE("arith_int_rows",
          unsigned num = m_lar_solver->A_r().column_count();
          for (unsigned v = 0; v < num; v++) {
              if (is_int(v) && !get_value(v).is_int()) {
                  display_column(tout, v);
              }
          }
    
          num = 0;
          for (unsigned i = 0; i < m_lar_solver->A_r().row_count(); i++) {
              unsigned j = m_lar_solver->m_mpq_lar_core_solver.m_r_basis[i];
              if (column_is_int_inf(j)) {
                  num++;
                  m_lar_solver->print_row(m_lar_solver->A_r().m_rows[i], tout);
                  tout << "\n";
              }
          }
          tout << "num of int infeasible: " << num << "\n";
          );
}

bool int_solver::has_inf_int() const {
    return m_lar_solver->has_inf_int();
}

int int_solver::find_inf_int_base_column() {
    unsigned inf_int_count = 0;
    int j = find_inf_int_boxed_base_column_with_smallest_range(inf_int_count);
    if (j != -1)
        return j;
    if (inf_int_count == 0)
        return -1;
    unsigned k = random() % inf_int_count;
    return get_kth_inf_int(k);
}

int int_solver::get_kth_inf_int(unsigned k) const {
    for (unsigned j : m_lar_solver->r_basis()) 
        if (column_is_int_inf(j) && k-- == 0)
            return j;
    lp_assert(false);
    return -1;
}

int int_solver::find_inf_int_nbasis_column() const {
    for (unsigned j : m_lar_solver->r_nbasis())
        if (!column_is_int_inf(j))
            return j;    
    return -1; 
}

int int_solver::find_inf_int_boxed_base_column_with_smallest_range(unsigned & inf_int_count) {
    inf_int_count = 0;
    int result = -1;
    mpq range;
    mpq new_range;
    mpq small_range_thresold(1024);
    unsigned n = 0;
    lar_core_solver & lcs = m_lar_solver->m_mpq_lar_core_solver;

    for (unsigned j : m_lar_solver->r_basis()) {
        if (!column_is_int_inf(j))
            continue;
        inf_int_count++;
        if (!is_boxed(j))
            continue;
        lp_assert(!is_fixed(j));
        new_range  = lcs.m_r_upper_bounds()[j].x - lcs.m_r_lower_bounds()[j].x;
        if (new_range > small_range_thresold) 
            continue;
        if (result == -1 || new_range < range) {
            result = j;
            range  = new_range;
            n      = 1;
        }
        else if (new_range == range && settings().random_next() % (++n) == 0) {
            lp_assert(n > 1);
            result = j;
        }
    }
    return result;
    
}

bool int_solver::is_gomory_cut_target(const row_strip<mpq>& row) {
    // All non base variables must be at their bounds and assigned to rationals (that is, infinitesimals are not allowed).
    unsigned j;
    for (const auto & p : row) {
        j = p.var();
        if (is_base(j)) continue;
        if (!at_bound(j))
            return false;
        if (!is_zero(get_value(j).y)) {
            TRACE("gomory_cut", tout << "row is not gomory cut target:\n";
                  display_column(tout, j);
                  tout << "infinitesimal: " << !is_zero(get_value(j).y) << "\n";);
            return false;
        }
    }
    return true;
}


void int_solver::real_case_in_gomory_cut(const mpq & a, unsigned x_j, const mpq& f_0, const mpq& one_minus_f_0) {
    TRACE("gomory_cut_detail_real", tout << "real\n";);
    mpq new_a;
    if (at_low(x_j)) {
        if (a.is_pos()) {
            new_a  =  a / one_minus_f_0;
        }
        else {
            new_a  =  a / f_0;
            new_a.neg();
        }
        m_k->addmul(new_a, lower_bound(x_j).x); // is it a faster operation than
        // k += lower_bound(x_j).x * new_a;  
        m_ex->push_justification(column_lower_bound_constraint(x_j), new_a);
    }
    else {
        lp_assert(at_upper(x_j));
        if (a.is_pos()) {
            new_a =   a / f_0; 
            new_a.neg(); // the upper terms are inverted.
        }
        else {
            new_a =   a / one_minus_f_0; 
        }
        m_k->addmul(new_a, upper_bound(x_j).x); //  k += upper_bound(x_j).x * new_a; 
        m_ex->push_justification(column_upper_bound_constraint(x_j), new_a);
    }
    TRACE("gomory_cut_detail_real", tout << a << "*v" << x_j << " k: " << *m_k << "\n";);
    m_t->add_monomial(new_a, x_j);
}

constraint_index int_solver::column_upper_bound_constraint(unsigned j) const {
    return m_lar_solver->get_column_upper_bound_witness(j);
}

constraint_index int_solver::column_lower_bound_constraint(unsigned j) const {
    return m_lar_solver->get_column_lower_bound_witness(j);
}


void int_solver::int_case_in_gomory_cut(const mpq & a, unsigned x_j,
                                        mpq & lcm_den, const mpq& f_0, const mpq& one_minus_f_0) {
    lp_assert(is_int(x_j));
    lp_assert(!a.is_int());
    mpq f_j =  fractional_part(a);
    TRACE("gomory_cut_detail", 
          tout << a << " x_j" << x_j << " k = " << *m_k << "\n";
          tout << "f_j: " << f_j << "\n";
          tout << "f_0: " << f_0 << "\n";
          tout << "1 - f_0: " << 1 - f_0 << "\n";
          tout << "at_low(" << x_j << ") = " << at_low(x_j) << std::endl;
          );
    lp_assert (!f_j.is_zero());
    mpq new_a;
    if (at_low(x_j)) {
        if (f_j <= one_minus_f_0) {
            new_a = f_j / one_minus_f_0;
        }
        else {
            new_a = (1 - f_j) / f_0;
        }
        m_k->addmul(new_a, lower_bound(x_j).x);
        m_ex->push_justification(column_lower_bound_constraint(x_j), new_a);
    }
    else {
        lp_assert(at_upper(x_j));
        if (f_j <= f_0) {
            new_a = f_j / f_0;
        }
        else {
            new_a = (mpq(1) - f_j) / one_minus_f_0;
        }
        new_a.neg(); // the upper terms are inverted
        m_k->addmul(new_a, upper_bound(x_j).x);
        m_ex->push_justification(column_upper_bound_constraint(x_j), new_a);
    }
    TRACE("gomory_cut_detail", tout << "new_a: " << new_a << " k: " << *m_k << "\n";);
    m_t->add_monomial(new_a, x_j);
    lcm_den = lcm(lcm_den, denominator(new_a));
}

lia_move int_solver::report_conflict_from_gomory_cut() {
    TRACE("empty_pol",);
    lp_assert(m_k->is_pos());
    // conflict 0 >= k where k is positive
    m_k->neg(); // returning 0 <= -k
    return lia_move::conflict;
}

void int_solver::gomory_cut_adjust_t_and_k(vector<std::pair<mpq, unsigned>> & pol,
                                           lar_term & t,
                                           mpq &k,
                                           bool some_ints,
                                           mpq & lcm_den) {
    if (!some_ints)
        return;
        
    t.clear();
    if (pol.size() == 1) {
        unsigned v = pol[0].second;
        lp_assert(is_int(v));
        bool k_is_int = k.is_int();
        const mpq& a = pol[0].first;
        k /= a;
        if (a.is_pos()) { // we have av >= k
            if (!k_is_int)
                k = ceil(k);
            // switch size
            t.add_monomial(- mpq(1), v);
            k.neg();
        } else {
            if (!k_is_int)
                k = floor(k);
            t.add_monomial(mpq(1), v);
        }
    } else if (some_ints) {
        lcm_den = lcm(lcm_den, denominator(k));
        lp_assert(lcm_den.is_pos());
        if (!lcm_den.is_one()) {
            // normalize coefficients of integer parameters to be integers.
            for (auto & pi: pol) {
                pi.first *= lcm_den;
                SASSERT(!is_int(pi.second) || pi.first.is_int());
            }
            k *= lcm_den;
        }
        // negate everything to return -pol <= -k
        for (const auto & pi: pol)
            t.add_monomial(-pi.first, pi.second);
        k.neg();
    }
}

bool int_solver::current_solution_is_inf_on_cut() const {
    const auto & x = m_lar_solver->m_mpq_lar_core_solver.m_r_x;
    impq v = m_t->apply(x);
    mpq sign = *m_upper ? one_of_type<mpq>()  : -one_of_type<mpq>();
    CTRACE("current_solution_is_inf_on_cut", v * sign <= (*m_k) * sign,
           tout << "m_upper = " << *m_upper << std::endl;
           tout << "v = " << v << ", k = " << (*m_k) << std::endl;
          );
    return v * sign > (*m_k) * sign;
}

void int_solver::adjust_term_and_k_for_some_ints_case_gomory(mpq &lcm_den) {
    lp_assert(!m_t->is_empty());
    auto pol = m_t->coeffs_as_vector();
    m_t->clear();
    if (pol.size() == 1) {
        TRACE("gomory_cut_detail", tout << "pol.size() is 1" << std::endl;);
        unsigned v = pol[0].second;
        lp_assert(is_int(v));
        const mpq& a = pol[0].first;
        (*m_k) /= a;
        if (a.is_pos()) { // we have av >= k
            if (!(*m_k).is_int())
                (*m_k) = ceil((*m_k));
            // switch size
            m_t->add_monomial(- mpq(1), v);
            (*m_k).neg();
        } else {
            if (!(*m_k).is_int())
                (*m_k) = floor((*m_k));
            m_t->add_monomial(mpq(1), v);
        }
    } else {
        TRACE("gomory_cut_detail", tout << "pol.size() > 1" << std::endl;);
        lcm_den = lcm(lcm_den, denominator((*m_k)));
        lp_assert(lcm_den.is_pos());
        if (!lcm_den.is_one()) {
            // normalize coefficients of integer parameters to be integers.
            for (auto & pi: pol) {
                pi.first *= lcm_den;
                SASSERT(!is_int(pi.second) || pi.first.is_int());
            }
            (*m_k) *= lcm_den;
        }
        // negate everything to return -pol <= -(*m_k)
        for (const auto & pi: pol)
            m_t->add_monomial(-pi.first, pi.second);
        (*m_k).neg();
    }
    TRACE("gomory_cut_detail", tout << "k = " << (*m_k) << std::endl;);
    lp_assert((*m_k).is_int());
}




lia_move int_solver::mk_gomory_cut( unsigned inf_col, const row_strip<mpq> & row) {

    lp_assert(column_is_int_inf(inf_col));

    TRACE("gomory_cut",
          tout << "applying cut at:\n"; m_lar_solver->print_row(row, tout); tout << std::endl;
          for (auto & p : row) {
              m_lar_solver->m_mpq_lar_core_solver.m_r_solver.print_column_info(p.var(), tout);
          }
          tout << "inf_col = " << inf_col << std::endl;
          );
        
    // gomory will be   t <= k and the current solution has a property t > k
    *m_k = 1;
    mpq lcm_den(1);
    unsigned x_j;
    mpq a;
    bool some_int_columns = false;
    mpq f_0  = int_solver::fractional_part(get_value(inf_col));
    mpq one_min_f_0 = 1 - f_0;
    for (auto & p : row) {
        x_j = p.var();
        if (x_j == inf_col)
            continue;
        // make the format compatible with the format used in: Integrating Simplex with DPLL(T)
        a = p.coeff();
        a.neg();  
        if (is_real(x_j)) 
            real_case_in_gomory_cut(a, x_j, f_0, one_min_f_0);
        else if (!a.is_int()) { // f_j will be zero and no monomial will be added
            some_int_columns = true;
            int_case_in_gomory_cut(a, x_j, lcm_den, f_0, one_min_f_0);
        }
    }

    if (m_t->is_empty())
        return report_conflict_from_gomory_cut();
    if (some_int_columns)
        adjust_term_and_k_for_some_ints_case_gomory(lcm_den);

    lp_assert(current_solution_is_inf_on_cut());
    m_lar_solver->subs_term_columns(*m_t);
    TRACE("gomory_cut", tout<<"precut:"; m_lar_solver->print_term(*m_t, tout); tout << " <= " << *m_k << std::endl;);
    return lia_move::cut;
    
}

int int_solver::find_free_var_in_gomory_row(const row_strip<mpq>& row) {
    unsigned j;
    for (const auto & p : row) {
        j = p.var();
        if (!is_base(j) && is_free(j))
            return static_cast<int>(j);
    }
    return -1;
}

lia_move int_solver::proceed_with_gomory_cut(unsigned j) {
    const row_strip<mpq>& row = m_lar_solver->get_row(row_of_basic_column(j));

    if (-1 != find_free_var_in_gomory_row(row))  
        return lia_move::undef;

    if (!is_gomory_cut_target(row)) 
        return lia_move::undef;

    *m_upper = true;
    return mk_gomory_cut(j, row);
}


unsigned int_solver::row_of_basic_column(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_r_heading[j];
}

// template <typename T>
// void int_solver::fill_cut_solver_for_constraint(constraint_index ci, cut_solver<T> & cs) {
//     const lar_base_constraint* c = m_lar_solver->constraints()[ci];
//     vector<std::pair<T, var_index>> coeffs;
//     T rs;
//     get_int_coeffs_from_constraint(c, coeffs, rs);
//     vector<constraint_index> explanation;
//     explanation.push_back(ci);
//     cs.add_ineq(coeffs, -rs, explanation);
// }


typedef monomial mono;


// this will allow to enable and disable tracking of the pivot rows
struct pivoted_rows_tracking_control {
    lar_solver * m_lar_solver;
    bool m_track_pivoted_rows;
    pivoted_rows_tracking_control(lar_solver* ls) :
        m_lar_solver(ls),
        m_track_pivoted_rows(ls->get_track_pivoted_rows())
    {
        TRACE("pivoted_rows", tout << "pivoted rows = " << ls->m_mpq_lar_core_solver.m_r_solver.m_pivoted_rows->size() << std::endl;);
        m_lar_solver->set_track_pivoted_rows(false);
    }
    ~pivoted_rows_tracking_control() {
        TRACE("pivoted_rows", tout << "pivoted rows = " << m_lar_solver->m_mpq_lar_core_solver.m_r_solver.m_pivoted_rows->size() << std::endl;);
        m_lar_solver->set_track_pivoted_rows(m_track_pivoted_rows);
    }
};



impq int_solver::get_cube_delta_for_term(const lar_term& t) const {
    if (t.size() == 2) {
        bool seen_minus = false;
        bool seen_plus = false;
        for(const auto & p : t) {
            const mpq & c = p.coeff();
            if (c == one_of_type<mpq>()) {
                seen_plus = true;
            } else if (c == -one_of_type<mpq>()) {
                seen_minus = true;
            } else {
                goto usual_delta;
            }
        }
        if (seen_minus && seen_plus)
            return zero_of_type<impq>();
        return impq(0, 1);
    }
 usual_delta:
    mpq delta = zero_of_type<mpq>();
    for (const auto & p : t) {
        delta += abs(p.coeff());
    }
    delta *= mpq(1, 2);
    return impq(delta);
}

bool int_solver::tighten_term_for_cube(unsigned i) {
    unsigned ti = i + m_lar_solver->terms_start_index();
    if (!m_lar_solver->term_is_used_as_row(ti))
        return true;
    const lar_term* t = m_lar_solver->terms()[i];
    
    impq delta = get_cube_delta_for_term(*t);
    TRACE("cube", m_lar_solver->print_term_as_indices(*t, tout); tout << ", delta = " << delta;);
    if (is_zero(delta))
        return true;
    return m_lar_solver->tighten_term_bounds_by_delta(i, delta);
}

bool int_solver::tighten_terms_for_cube() {
    for (unsigned i = 0; i < m_lar_solver->terms().size(); i++)
        if (!tighten_term_for_cube(i)) {
            TRACE("cube", tout << "cannot tighten";);
            return false;
        }
    return true;
}

lia_move int_solver::find_cube() {
    if (m_branch_cut_counter % settings().m_int_find_cube_period != 0)
        return lia_move::undef;
    
    settings().st().m_cube_calls++;
    TRACE("cube",
          for (unsigned j = 0; j < m_lar_solver->A_r().column_count(); j++)
              display_column(tout, j);
          m_lar_solver->print_terms(tout);
          );
    
    lar_solver::scoped_push _sp(*m_lar_solver);
    if (!tighten_terms_for_cube()) {
        return lia_move::undef;
    }

    lp_status st = m_lar_solver->find_feasible_solution();
    if (st != lp_status::FEASIBLE && st != lp_status::OPTIMAL) {
        TRACE("cube", tout << "cannot find a feasiblie solution";);
        _sp.pop();
        move_non_basic_columns_to_bounds();
        find_feasible_solution();
        // it can happen that we found an integer solution here
        return !m_lar_solver->r_basis_has_inf_int()? lia_move::sat: lia_move::undef;
    }
    _sp.pop();
    m_lar_solver->round_to_integer_solution();
    settings().st().m_cube_success++;
    return lia_move::sat;
}

void int_solver::find_feasible_solution() {
    m_lar_solver->find_feasible_solution();
    lp_assert(lp_status::OPTIMAL == m_lar_solver->get_status() || lp_status::FEASIBLE == m_lar_solver->get_status());
}

lia_move int_solver::run_gcd_test() {
    if (settings().m_int_run_gcd_test) {
        settings().st().m_gcd_calls++;
        if (!gcd_test()) {
            settings().st().m_gcd_conflicts++;
            return lia_move::conflict;
        }
    }
    return lia_move::undef;
}

lia_move int_solver::gomory_cut() {
    if ((m_branch_cut_counter) % settings().m_int_gomory_cut_period != 0)
        return lia_move::undef;

    if (move_non_basic_columns_to_bounds()) {
#if Z3DEBUG 
        lp_status st =
#endif
            m_lar_solver->find_feasible_solution();
#if Z3DEBUG
        lp_assert(st == lp_status::FEASIBLE || st == lp_status::OPTIMAL);
#endif
    }
        
    int j = find_inf_int_base_column(); 
    if (j == -1) {
        j = find_inf_int_nbasis_column();
        return j == -1? lia_move::sat : create_branch_on_column(j);
    }
    return proceed_with_gomory_cut(j);
}


bool int_solver::try_add_term_to_A_for_hnf(unsigned i, bool & have_non_integral_x) {
    mpq rs;
    const lar_term* t = m_lar_solver->terms()[i];
    bool local_have_non_integral_x = false;
    for (const auto & p : *t) {
        if (!is_int(p.var())) {
            lp_assert(false); 
            return false; // todo : the mix case!
        }
        if (!local_have_non_integral_x)
            local_have_non_integral_x = ! get_value(p.var()).is_int();
    }
    constraint_index ci;
    if (m_lar_solver->get_equality_and_right_side_for_term_on_current_x(i, rs, ci)) {
        m_hnf_cutter.add_term(t, rs, ci);
        if (!have_non_integral_x)
            have_non_integral_x = local_have_non_integral_x;
        return true;
    }
    return false;
}

bool int_solver::hnf_matrix_is_empty() const { return true; }

bool int_solver::init_terms_for_hnf_cut() {
    bool have_non_integral_x = false;
    m_hnf_cutter.clear();
    for (unsigned i = 0; i < m_lar_solver->terms().size(); i++) {
        try_add_term_to_A_for_hnf(i, have_non_integral_x);
    }
    return have_non_integral_x && m_hnf_cutter.row_count() < settings().limit_on_rows_for_hnf_cutter;
}

lia_move int_solver::make_hnf_cut() {
    if (!init_terms_for_hnf_cut()) {
        return lia_move::undef;
    }
    settings().st().m_hnf_cutter_calls++;
    TRACE("hnf_cut", tout << "settings().st().m_hnf_cutter_calls = " << settings().st().m_hnf_cutter_calls;);
#ifdef Z3DEBUG
    vector<mpq> x0 = m_hnf_cutter.transform_to_local_columns(m_lar_solver->m_mpq_lar_core_solver.m_r_x);
#endif
    lia_move r =  m_hnf_cutter.create_cut(*m_t, *m_k, *m_ex, *m_upper
#ifdef Z3DEBUG
                                          , x0
#endif
                                          );
    CTRACE("hnf_cut", r == lia_move::cut, tout<< "cut:"; m_lar_solver->print_term(*m_t, tout); tout << " <= " << *m_k << std::endl;);
    if (r == lia_move::cut) {        
        lp_assert(current_solution_is_inf_on_cut());
        settings().st().m_hnf_cuts++;
        for (unsigned i = 0; i < m_hnf_cutter.row_count(); i++) {
            m_ex->push_justification(m_hnf_cutter.constraints_for_explanation()[i]);
        }
    }
    return r;
}

lia_move int_solver::hnf_cut() {
    if ((m_branch_cut_counter) % settings().m_hnf_cut_period == 0) {
        return make_hnf_cut();
    }
    return lia_move::undef;
}

lia_move int_solver::check(lar_term& t, mpq& k, explanation& ex, bool & upper) {
    if (!has_inf_int()) return lia_move::sat;

    m_t = &t;  m_k = &k;  m_ex = &ex; m_upper = &upper;
    lia_move r = run_gcd_test();
    if (r != lia_move::undef) return r;

    pivoted_rows_tracking_control pc(m_lar_solver);

    if(settings().m_int_pivot_fixed_vars_from_basis)
        m_lar_solver->pivot_fixed_vars_from_basis();

    r = patch_nbasic_columns();
    if (r != lia_move::undef) return r;
    ++m_branch_cut_counter;

    r = find_cube();
    if (r != lia_move::undef) return r;
    
    r = hnf_cut();
    if (r != lia_move::undef) return r;
    
    r = gomory_cut();
    return (r == lia_move::undef)? branch_or_sat() : r;
}

lia_move int_solver::branch_or_sat() {
    int j = find_any_inf_int_column_basis_first();
    return j == -1? lia_move::sat : create_branch_on_column(j);
}

int int_solver::find_any_inf_int_column_basis_first() {
   int j = find_inf_int_base_column();
   if (j != -1)
       return j;
   return find_inf_int_nbasis_column();
}

bool int_solver::move_non_basic_column_to_bounds(unsigned j) {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    auto & val = lcs.m_r_x[j];
    switch (lcs.m_column_types()[j]) {
    case column_type::boxed:
        if (val != lcs.m_r_lower_bounds()[j] && val != lcs.m_r_upper_bounds()[j]) {
            if (random() % 2 == 0)
                set_value_for_nbasic_column(j, lcs.m_r_lower_bounds()[j]);
            else
                set_value_for_nbasic_column(j, lcs.m_r_upper_bounds()[j]);
            return true;
        }
        break;
    case column_type::lower_bound:
        if (val != lcs.m_r_lower_bounds()[j]) {
            set_value_for_nbasic_column(j, lcs.m_r_lower_bounds()[j]);
            return true;
        }
        break;
    case column_type::upper_bound:
        if (val != lcs.m_r_upper_bounds()[j]) {
            set_value_for_nbasic_column(j, lcs.m_r_upper_bounds()[j]);
            return true;
        }
        break;
    default:
        if (is_int(j) && !val.is_int()) {
            set_value_for_nbasic_column(j, impq(floor(val)));
            return true;
        }
        break;
    }
    return false;
}

bool int_solver::move_non_basic_columns_to_bounds() {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    bool change = false;
    for (unsigned j : lcs.m_r_nbasis) {
        if (move_non_basic_column_to_bounds(j))
            change = true;
    }

    if (settings().simplex_strategy() == simplex_strategy_enum::tableau_costs)
        m_lar_solver->update_x_and_inf_costs_for_columns_with_changed_bounds_tableau();
    return change;
}

void int_solver::set_value_for_nbasic_column_ignore_old_values(unsigned j, const impq & new_val) {
    lp_assert(!is_base(j));
    auto & x = m_lar_solver->m_mpq_lar_core_solver.m_r_x[j];
    auto delta = new_val - x;
    x = new_val;
    m_lar_solver->change_basic_columns_dependend_on_a_given_nb_column(j, delta);
}


void int_solver::set_value_for_nbasic_column(unsigned j, const impq & new_val) {
    lp_assert(!is_base(j));
    auto & x = m_lar_solver->m_mpq_lar_core_solver.m_r_x[j];
    auto delta = new_val - x;
    x = new_val;
    m_lar_solver->change_basic_columns_dependend_on_a_given_nb_column(j, delta);
}

void int_solver::patch_nbasic_column(unsigned j) {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver; 
    impq & val = lcs.m_r_x[j];
    bool val_is_int = val.is_int();
    if (settings().m_int_patch_only_integer_values) {
        if (!val_is_int)
            return;
    }
        
    bool inf_l, inf_u;
    impq l, u;
    mpq m;
    if (!get_freedom_interval_for_column(j, inf_l, l, inf_u, u, m)) {
        return;
    }
    bool m_is_one = m.is_one();
    if (m.is_one() && val_is_int)
        return;
    // check whether value of j is already a multiple of m.
    if (val_is_int && (val.x / m).is_int())
        return;
    TRACE("patch_int",
          tout << "TARGET j" << j << " -> [";
          if (inf_l) tout << "-oo"; else tout << l;
          tout << ", ";
          if (inf_u) tout << "oo"; else tout << u;
          tout << "]";
          tout << ", m: " << m << ", val: " << val << ", is_int: " << m_lar_solver->column_is_int(j) << "\n";);
    if (!inf_l) {
        l = m_is_one ? ceil(l) : m * ceil(l / m);
        if (inf_u || l <= u) {
            TRACE("patch_int",
                  tout << "patching with l: " << l << '\n';);
            set_value_for_nbasic_column(j, l);
        }
        else {
            TRACE("patch_int",
                  tout << "not patching " << l << "\n";);
        }
    }
    else if (!inf_u) {
        u = m_is_one ? floor(u) : m * floor(u / m);
        set_value_for_nbasic_column(j, u);
        TRACE("patch_int",
              tout << "patching with u: " << u << '\n';);
    }
    else {
        set_value_for_nbasic_column(j, impq(0));
        TRACE("patch_int",
              tout << "patching with 0\n";);
    }
}

lia_move int_solver::patch_nbasic_columns() {
    settings().st().m_patches++;
    lp_assert(is_feasible());
    for (unsigned j : m_lar_solver->m_mpq_lar_core_solver.m_r_nbasis) {
        patch_nbasic_column(j);
    }
    lp_assert(is_feasible());
    if (!has_inf_int()) {
        settings().st().m_patches_success++;
        return lia_move::sat;
    }
    return lia_move::undef;
}

mpq get_denominators_lcm(const row_strip<mpq> & row) {
    mpq r(1);
    for  (auto & c : row) {
        r = lcm(r, denominator(c.coeff()));
    }
    return r;
}
    
bool int_solver::gcd_test_for_row(static_matrix<mpq, numeric_pair<mpq>> & A, unsigned i) {
    mpq lcm_den = get_denominators_lcm(A.m_rows[i]);
    mpq consts(0);
    mpq gcds(0);
    mpq least_coeff(0);
    bool    least_coeff_is_bounded = false;
    unsigned j;
    for (auto &c : A.m_rows[i]) {
        j = c.var();
        const mpq& a = c.coeff();
        if (m_lar_solver->column_is_fixed(j)) {
            mpq aux = lcm_den * a;
            consts += aux * m_lar_solver->column_lower_bound(j).x;
        }
        else if (m_lar_solver->column_is_real(j)) {
            return true;
        }
        else if (gcds.is_zero()) {
            gcds = abs(lcm_den * a);
            least_coeff = gcds;
            least_coeff_is_bounded = m_lar_solver->column_is_bounded(j);
        }
        else {
            mpq aux = abs(lcm_den * a);
            gcds = gcd(gcds, aux);
            if (aux < least_coeff) {
                least_coeff = aux;
                least_coeff_is_bounded = m_lar_solver->column_is_bounded(j);
            }
            else if (least_coeff_is_bounded && aux == least_coeff) {
                least_coeff_is_bounded = m_lar_solver->column_is_bounded(j);
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
        TRACE("gcd_test", tout << "row failed the GCD test:\n"; display_row_info(tout, i););
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


void int_solver::add_to_explanation_from_fixed_or_boxed_column(unsigned j) {
    constraint_index lc, uc;
    m_lar_solver->get_bound_constraint_witnesses_for_column(j, lc, uc);
    m_ex->m_explanation.push_back(std::make_pair(mpq(1), lc));
    m_ex->m_explanation.push_back(std::make_pair(mpq(1), uc));
}
void int_solver::fill_explanation_from_fixed_columns(const row_strip<mpq> & row) {
    for (const auto & c : row) {
        if (!m_lar_solver->column_is_fixed(c.var()))
            continue;
        add_to_explanation_from_fixed_or_boxed_column(c.var());
    }
}
    
bool int_solver::gcd_test() {
    auto & A = m_lar_solver->A_r(); // getting the matrix
    for (unsigned i = 0; i < A.row_count(); i++)
        if (!gcd_test_for_row(A, i)) 
            return false;        
    return true;
}

bool int_solver::ext_gcd_test(const row_strip<mpq> & row,
                              mpq const & least_coeff, 
                              mpq const & lcm_den,
                              mpq const & consts) {
    mpq gcds(0);
    mpq l(consts);
    mpq u(consts);

    mpq a;
    unsigned j;
    for (const auto & c : row) {
        j = c.var();
        const mpq & a = c.coeff();
        if (m_lar_solver->column_is_fixed(j))
            continue;
        SASSERT(!m_lar_solver->column_is_real(j));
        mpq ncoeff = lcm_den * a;
        SASSERT(ncoeff.is_int());
        mpq abs_ncoeff = abs(ncoeff);
        if (abs_ncoeff == least_coeff) {
            SASSERT(m_lar_solver->column_is_bounded(j));
            if (ncoeff.is_pos()) {
                // l += ncoeff * m_lar_solver->column_lower_bound(j).x;
                l.addmul(ncoeff, m_lar_solver->column_lower_bound(j).x);
                // u += ncoeff * m_lar_solver->column_upper_bound(j).x;
                u.addmul(ncoeff, m_lar_solver->column_upper_bound(j).x);
            }
            else {
                // l += ncoeff * upper_bound(j).get_rational();
                l.addmul(ncoeff, m_lar_solver->column_upper_bound(j).x);
                // u += ncoeff * lower_bound(j).get_rational();
                u.addmul(ncoeff, m_lar_solver->column_lower_bound(j).x);
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
/*
linear_combination_iterator<mpq> * int_solver::get_column_iterator(unsigned j) {
    if (m_lar_solver->use_tableau())
        return new iterator_on_column<mpq, impq>(m_lar_solver->A_r().m_columns[j], m_lar_solver->A_r());
    return new iterator_on_indexed_vector<mpq>(m_lar_solver->get_column_in_lu_mode(j));
}
*/


int_solver::int_solver(lar_solver* lar_slv) :
    m_lar_solver(lar_slv),
    m_branch_cut_counter(0),
    m_hnf_cutter(settings()) {
    m_lar_solver->set_int_solver(this);
}


bool int_solver::has_low(unsigned j) const {
    switch (m_lar_solver->m_mpq_lar_core_solver.m_column_types()[j]) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::lower_bound:
        return true;
    default:
        return false;
    }
}

bool int_solver::has_upper(unsigned j) const {
    switch (m_lar_solver->m_mpq_lar_core_solver.m_column_types()[j]) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::upper_bound:
        return true;
    default:
        return false;
    }
}


void set_lower(impq & l,
               bool & inf_l,
               impq const & v ) {
    if (inf_l || v > l) {
        l = v;
        inf_l = false;
    }
}


void set_upper(impq & u,
               bool & inf_u,
               impq const & v) {
    if (inf_u || v < u) {
        u = v;
        inf_u = false;
    }
}

bool int_solver::get_freedom_interval_for_column(unsigned j, bool & inf_l, impq & l, bool & inf_u, impq & u, mpq & m) {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    if (lcs.m_r_heading[j] >= 0) // the basic var 
        return false;

    impq const & xj = get_value(j);
    
    inf_l = true;
    inf_u = true;
    l = u = zero_of_type<impq>();
    m = mpq(1);

    if (has_low(j)) {
        set_lower(l, inf_l, lower_bound(j));
    }
    if (has_upper(j)) {
        set_upper(u, inf_u, upper_bound(j));
    }

    mpq a; // the coefficient in the column
    unsigned row_index;
    lp_assert(settings().use_tableau());
    const auto & A = m_lar_solver->A_r();
    for (const auto &c : A.column(j)) {
        row_index = c.var();
        const mpq & a = c.coeff();
        
        unsigned i = lcs.m_r_basis[row_index];
        impq const & xi = get_value(i);
        if (is_int(i) && is_int(j) && !a.is_int())
            m = lcm(m, denominator(a));
        if (a.is_neg()) {
            if (has_low(i))
                set_lower(l, inf_l, xj + (xi - lcs.m_r_lower_bounds()[i]) / a);

            if (has_upper(i))
                set_upper(u, inf_u, xj + (xi - lcs.m_r_upper_bounds()[i]) / a);
        }
        else {
            if (has_upper(i))
                set_lower(l, inf_l, xj + (xi - lcs.m_r_upper_bounds()[i]) / a);
            if (has_low(i))
                set_upper(u, inf_u, xj + (xi - lcs.m_r_lower_bounds()[i]) / a);
        }
        if (!inf_l && !inf_u && l >= u) break;                
    }

    TRACE("freedom_interval",
          tout << "freedom variable for:\n";
          tout << m_lar_solver->get_column_name(j);
          tout << "[";
          if (inf_l) tout << "-oo"; else tout << l;
          tout << "; ";
          if (inf_u) tout << "oo";  else tout << u;
          tout << "]\n";
          tout << "val = " << get_value(j) << "\n";
          tout << "return " << (inf_l || inf_u || l <= u);
          );
    return (inf_l || inf_u || l <= u);
}

bool int_solver::is_int(unsigned j) const {
    return m_lar_solver->column_is_int(j);
}

bool int_solver::is_real(unsigned j) const {
    return !is_int(j);
}

bool int_solver::value_is_int(unsigned j) const {
    return m_lar_solver->column_value_is_int(j);
}

    

bool int_solver::is_feasible() const {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    lp_assert(
        lcs.m_r_solver.calc_current_x_is_feasible_include_non_basis() ==
        lcs.m_r_solver.current_x_is_feasible());
    return lcs.m_r_solver.current_x_is_feasible();
}
const impq & int_solver::get_value(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_r_x[j];
}

void int_solver::display_column(std::ostream & out, unsigned j) const {
    m_lar_solver->m_mpq_lar_core_solver.m_r_solver.print_column_info(j, out);
}

bool int_solver::column_is_int_inf(unsigned j) const {
    return is_int(j) && (!value_is_int(j));
}

bool int_solver::is_base(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_r_heading[j] >= 0;
}

bool int_solver::is_boxed(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_column_types[j] == column_type::boxed;
}

bool int_solver::is_fixed(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_column_types[j] == column_type::fixed;
}

bool int_solver::is_free(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_column_types[j] == column_type::free_column;
}

bool int_solver::at_bound(unsigned j) const {
    auto & mpq_solver = m_lar_solver->m_mpq_lar_core_solver.m_r_solver;
    switch (mpq_solver.m_column_types[j] ) {
    case column_type::fixed:
    case column_type::boxed:
        return
            mpq_solver.m_lower_bounds[j] == get_value(j) ||
            mpq_solver.m_upper_bounds[j] == get_value(j);
    case column_type::lower_bound:
        return mpq_solver.m_lower_bounds[j] == get_value(j);
    case column_type::upper_bound:
        return  mpq_solver.m_upper_bounds[j] == get_value(j);
    default:
        return false;
    }
}

bool int_solver::at_low(unsigned j) const {
    auto & mpq_solver = m_lar_solver->m_mpq_lar_core_solver.m_r_solver;
    switch (mpq_solver.m_column_types[j] ) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::lower_bound:
        return mpq_solver.m_lower_bounds[j] == get_value(j);
    default:
        return false;
    }
}

bool int_solver::at_upper(unsigned j) const {
    auto & mpq_solver = m_lar_solver->m_mpq_lar_core_solver.m_r_solver;
    switch (mpq_solver.m_column_types[j] ) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::upper_bound:
        return mpq_solver.m_upper_bounds[j] == get_value(j);
    default:
        return false;
    }
}



lp_settings& int_solver::settings() {
    return m_lar_solver->settings();
}

void int_solver::display_row_info(std::ostream & out, unsigned row_index) const  {
    auto & rslv = m_lar_solver->m_mpq_lar_core_solver.m_r_solver;
    for (auto &c: rslv.m_A.m_rows[row_index]) {
        if (numeric_traits<mpq>::is_pos(c.coeff()))
            out << "+";
        out << c.coeff() << rslv.column_name(c.var()) << " ";
    }

    for (auto& c: rslv.m_A.m_rows[row_index]) {
        rslv.print_column_bound_info(c.var(), out);
    }
    rslv.print_column_bound_info(rslv.m_basis[row_index], out);
}

unsigned int_solver::random() {
    return m_lar_solver->get_core_solver().settings().random_next();
}

bool int_solver::shift_var(unsigned j, unsigned range) {
    if (is_fixed(j) || is_base(j))
        return false;
       
    bool inf_l, inf_u;
    impq l, u;
    mpq m;
    get_freedom_interval_for_column(j, inf_l, l, inf_u, u, m);
    if (inf_l && inf_u) {
        impq new_val = impq(random() % (range + 1));
        set_value_for_nbasic_column_ignore_old_values(j, new_val);
        return true;
    }
    if (is_int(j)) {
        if (!inf_l) {
            l = ceil(l);
            if (!m.is_one())
                l = m*ceil(l/m);
        }
        if (!inf_u) {
            u = floor(u);
            if (!m.is_one())
                u = m*floor(u/m);
        }
    }
    if (!inf_l && !inf_u && l >= u)
        return false;
    if (inf_u) {
        SASSERT(!inf_l);
        impq delta   = impq(random() % (range + 1));
        impq new_val = l + m*delta;
        set_value_for_nbasic_column_ignore_old_values(j, new_val);
        return true;
    }
    if (inf_l) {
        SASSERT(!inf_u);
        impq delta   = impq(random() % (range + 1));
        impq new_val = u - m*delta;
        set_value_for_nbasic_column_ignore_old_values(j, new_val);
        return true;
    }
    if (!is_int(j)) {
        SASSERT(!inf_l && !inf_u);
        mpq delta       = mpq(random() % (range + 1));
        impq new_val = l + ((delta * (u - l)) / mpq(range)); 
        set_value_for_nbasic_column_ignore_old_values(j, new_val);
        return true;
    }
    else {
        mpq r = (u.x - l.x) / m;
        if (r < mpq(range))
            range = static_cast<unsigned>(r.get_uint64());
        impq new_val = l + m * (impq(random() % (range + 1)));
        set_value_for_nbasic_column_ignore_old_values(j, new_val);
        return true;
    }
}

bool int_solver::non_basic_columns_are_at_bounds() const {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    for (unsigned j :lcs.m_r_nbasis) {
        auto & val = lcs.m_r_x[j];
        switch (lcs.m_column_types()[j]) {
        case column_type::boxed:
            if (val != lcs.m_r_lower_bounds()[j] && val != lcs.m_r_upper_bounds()[j])
                return false;
            break;
        case column_type::lower_bound:
            if (val != lcs.m_r_lower_bounds()[j])
                return false;
            break;
        case column_type::upper_bound:
            if (val != lcs.m_r_upper_bounds()[j])
                return false;
            break;
        default:
            if (is_int(j) && !val.is_int()) {
                return false;
            }
        }
    }
    return true;
}

const impq& int_solver::lower_bound(unsigned j) const {
    return m_lar_solver->column_lower_bound(j);
}

lia_move int_solver::create_branch_on_column(int j) {
    TRACE("check_main_int", tout << "branching" << std::endl;);
    lp_assert(m_t->is_empty());
    lp_assert(j != -1);
    m_t->add_monomial(mpq(1), m_lar_solver->adjust_column_index_to_term_index(j));
    if (is_free(j)) {
        *m_upper = true;
        *m_k = mpq(0);
    } else {
        *m_upper = left_branch_is_more_narrow_than_right(j);
        *m_k = *m_upper? floor(get_value(j)) : ceil(get_value(j));        
    }

    TRACE("arith_int", tout << "branching v" << j << " = " << get_value(j) << "\n";
          display_column(tout, j);
          tout << "k = " << *m_k << std::endl;
          );
    return lia_move::branch;

}

bool int_solver::left_branch_is_more_narrow_than_right(unsigned j) {
    switch (m_lar_solver->m_mpq_lar_core_solver.m_r_solver.m_column_types[j] ) {
    case column_type::fixed:
        return false;
    case column_type::boxed:
        {
            auto k = floor(get_value(j));
            return k - lower_bound(j).x < upper_bound(j).x - (k + mpq(1));
        }
    case column_type::lower_bound: 
        return true;
    case column_type::upper_bound:
        return false;
    default:
        return false;
    }       
}
    
const impq& int_solver::upper_bound(unsigned j) const {
    return m_lar_solver->column_upper_bound(j);
}

bool int_solver::is_term(unsigned j) const {
    return m_lar_solver->column_corresponds_to_term(j);
}

unsigned int_solver::column_count() const  { return m_lar_solver->column_count(); }

}
