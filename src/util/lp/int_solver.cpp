/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#include "util/lp/int_solver.h"
#include "util/lp/lar_solver.h"
#include "util/lp/cut_solver.h"
#include "util/lp/lp_utils.h"
#include <utility>
namespace lp {

void int_solver::failed() {
    // auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    
    // for (unsigned j : m_old_values_set.m_index) {
    //     lcs.m_r_x[j] = m_old_values_data[j];
    //     lp_assert(lcs.m_r_solver.column_is_feasible(j));
    //     lcs.m_r_solver.remove_column_from_inf_set(j);
    // }
    // lp_assert(lcs.m_r_solver.calc_current_x_is_feasible_include_non_basis());
    // lp_assert(lcs.m_r_solver.current_x_is_feasible());
    // m_old_values_set.clear();
}

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

bool int_solver::all_columns_are_bounded() const {
    for (unsigned j = 0; j < m_lar_solver->column_count(); j++)
        if (m_lar_solver->column_is_bounded(j) == false)
            return false;
    return true;
}

bool int_solver::has_inf_int() const {
    return m_lar_solver->has_inf_int();
}

int int_solver::find_inf_int_base_column() {
    unsigned inf_int_count;
    int j = find_inf_int_boxed_base_column_with_smallest_range(inf_int_count);
	if (j != -1)
		return j;
    if (inf_int_count == 0)
        return -1;
    unsigned k = random() % inf_int_count;
    return get_kth_inf_int(k);
}

int int_solver::get_kth_inf_int(unsigned k) const {
    unsigned inf_int_count = 0;
    for (unsigned j : m_lar_solver->r_basis()) {
        if (! column_is_int_inf(j) )
            continue;
        if (inf_int_count++ == k)
            return j;
    }
    lp_assert(false);
    return -1;
}

int int_solver::find_inf_int_boxed_base_column_with_smallest_range(unsigned & inf_int_count) {
    inf_int_count = 0;
    int result = -1;
    mpq range;
    mpq new_range;
    mpq small_range_thresold(1024);
    unsigned n;
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
        if (result == -1) {
            result = j;
            range  = new_range;
            n      = 1;
            continue;
        }
        if (new_range < range) {
            n      = 1;
            result = j;
            range  = new_range;
            continue;
        }
        if (new_range == range) {
            lp_assert(n >= 1);
            if (settings().random_next() % (++n) == 0) {
                result = j;
                continue;
            }
        }
    }
    return result;
    
}

bool int_solver::is_gomory_cut_target(const row_strip<mpq>& row) {
    // All non base variables must be at their bounds and assigned to rationals (that is, infinitesimals are not allowed).
    unsigned j;
    for (auto p : row) {
        j = p.var();
        if (is_base(j)) continue;
        if (!is_zero(get_value(j).y)) {
            TRACE("gomory_cut", tout << "row is not gomory cut target:\n";
                  display_column(tout, j);
                  tout << "infinitesimal: " << !is_zero(get_value(j).y) << "\n";);
            return false;
        }
    }
    return true;
}


void int_solver::real_case_in_gomory_cut(const mpq & a, unsigned x_j, mpq & k, lar_term& pol, explanation & expl, const mpq& f_0, const mpq& one_minus_f_0) {
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
        k.addmul(new_a, lower_bound(x_j).x); // is it a faster operation than
        // k += lower_bound(x_j).x * new_a;  
        expl.push_justification(column_lower_bound_constraint(x_j), new_a);
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
        k.addmul(new_a, upper_bound(x_j).x); //  k += upper_bound(x_j).x * new_a; 
        expl.push_justification(column_upper_bound_constraint(x_j), new_a);
    }
    TRACE("gomory_cut_detail_real", tout << a << "*v" << x_j << " k: " << k << "\n";);
    pol.add_monomial(new_a, x_j);
}

constraint_index int_solver::column_upper_bound_constraint(unsigned j) const {
    return m_lar_solver->get_column_upper_bound_witness(j);
}

constraint_index int_solver::column_lower_bound_constraint(unsigned j) const {
    return m_lar_solver->get_column_lower_bound_witness(j);
}


void int_solver::int_case_in_gomory_cut(const mpq & a, unsigned x_j, mpq & k, lar_term & t, explanation& expl, mpq & lcm_den, const mpq& f_0, const mpq& one_minus_f_0) {
    lp_assert(is_int(x_j));
    lp_assert(!a.is_int());
    mpq f_j =  fractional_part(a);
    TRACE("gomory_cut_detail", 
          tout << a << " x_j" << x_j << " k = " << k << "\n";
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
        k.addmul(new_a, lower_bound(x_j).x);
        expl.push_justification(column_lower_bound_constraint(x_j), new_a);
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
        k.addmul(new_a, upper_bound(x_j).x);
        expl.push_justification(column_upper_bound_constraint(x_j), new_a);
    }
    TRACE("gomory_cut_detail", tout << "new_a: " << new_a << " k: " << k << "\n";);
    t.add_monomial(new_a, x_j);
    lcm_den = lcm(lcm_den, denominator(new_a));
}

lia_move int_solver::report_conflict_from_gomory_cut(mpq & k) {
    TRACE("empty_pol",);
    lp_assert(k.is_pos());
    // conflict 0 >= k where k is positive
    k.neg(); // returning 0 <= -k
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

bool int_solver::current_solution_is_inf_on_cut(const lar_term& t, const mpq& k) const {
    const auto & x = m_lar_solver->m_mpq_lar_core_solver.m_r_x;
    impq v = t.apply(x);
    TRACE(
        "current_solution_is_inf_on_cut", tout << "v = " << v << " k = " << k << std::endl;
        if (v <=k) {
            tout << "v <= k - it should not happen!\n";
        }
          );
    
    return v > k;
}

void int_solver::adjust_term_and_k_for_some_ints_case_gomory(lar_term& t, mpq& k, mpq &lcm_den) {
    lp_assert(!t.is_empty());
    auto pol = t.coeffs_as_vector();
    t.clear();
    if (pol.size() == 1) {
        TRACE("gomory_cut_detail", tout << "pol.size() is 1" << std::endl;);
        unsigned v = pol[0].second;
        lp_assert(is_int(v));
        const mpq& a = pol[0].first;
        k /= a;
        if (a.is_pos()) { // we have av >= k
            if (!k.is_int())
                k = ceil(k);
            // switch size
            t.add_monomial(- mpq(1), v);
            k.neg();
        } else {
            if (!k.is_int())
                k = floor(k);
            t.add_monomial(mpq(1), v);
        }
    } else {
        TRACE("gomory_cut_detail", tout << "pol.size() > 1" << std::endl;);
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
    TRACE("gomory_cut_detail", tout << "k = " << k << std::endl;);
    lp_assert(k.is_int());
}




lia_move int_solver::mk_gomory_cut(lar_term& t, mpq& k, explanation & expl, unsigned inf_col, const row_strip<mpq> & row) {

    lp_assert(column_is_int_inf(inf_col));

    TRACE("gomory_cut",
          tout << "applying cut at:\n"; m_lar_solver->print_row(row, tout); tout << std::endl;
          for (auto p : row) {
              m_lar_solver->m_mpq_lar_core_solver.m_r_solver.print_column_info(p.var(), tout);
          }
          tout << "inf_col = " << inf_col << std::endl;
          );
        
    // gomory will be   t <= k and the current solution has a property t > k
    k = 1;
    mpq lcm_den(1);
    unsigned x_j;
    mpq a;
    bool some_int_columns = false;
    mpq f_0  = int_solver::fractional_part(get_value(inf_col));
    mpq one_min_f_0 = 1 - f_0;
    for (auto p : row) {
        x_j = p.var();
        if (x_j == inf_col)
            continue;
        // make the format compatible with the format used in: Integrating Simplex with DPLL(T)
        a = p.coeff();
        a.neg();  
        if (is_real(x_j)) 
            real_case_in_gomory_cut(a, x_j, k, t, expl, f_0, one_min_f_0);
        else {
            if (a.is_int()) continue; // f_j will be zero and no monomial will be added
            some_int_columns = true;
            int_case_in_gomory_cut(a, x_j, k, t, expl, lcm_den, f_0, one_min_f_0);
        }
    }

    if (t.is_empty())
        return report_conflict_from_gomory_cut(k);
    if (some_int_columns)
        adjust_term_and_k_for_some_ints_case_gomory(t, k, lcm_den);

    lp_assert(current_solution_is_inf_on_cut(t, k));
    m_lar_solver->subs_term_columns(t);
    TRACE("gomory_cut", tout<<"precut:"; m_lar_solver->print_term(t, tout); tout << " <= " << k << std::endl;);
    return lia_move::cut;
    
}

void int_solver::init_check_data() {
    // unsigned n = m_lar_solver->A_r().column_count();
    // m_old_values_set.resize(n);
    // m_old_values_data.resize(n);
}

int int_solver::find_free_var_in_gomory_row(const row_strip<mpq>& row) {
    unsigned j;
    for (auto p : row) {
        j = p.var();
        if (!is_base(j) && is_free(j))
            return static_cast<int>(j);
    }
    return -1;
}

lia_move int_solver::proceed_with_gomory_cut(lar_term& t, mpq& k, explanation& ex, unsigned j, bool & upper) {
    lia_move ret;
    
    const row_strip<mpq>& row = m_lar_solver->get_row(row_of_basic_column(j));
    int free_j = find_free_var_in_gomory_row(row);
    if (free_j != -1) {
        ret = create_branch_on_column(j, t, k, true, upper);
    } else if (!is_gomory_cut_target(row)) {
        bool upper;
        ret = create_branch_on_column(j, t, k, false, upper);
    } else {
        upper = false;
        ret = mk_gomory_cut(t, k, ex, j, row);
    }
    return ret;
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


typedef cut_solver::monomial mono;

// it produces an inequality coeff*x <= rs
template <typename T>
void int_solver::get_int_coeffs_from_constraint(const lar_base_constraint* c,
                                                vector<mono>& coeffs, T & rs) {
    lp_assert(c->m_kind != EQ); // it is not implemented, we need to create two inequalities in this case
    int sign = ((int)c->m_kind > 0) ? -1 : 1;
    vector<std::pair<T, var_index>> lhs = c->get_left_side_coefficients();
    T den = denominator(c->m_right_side);
    for (auto & kv : lhs) {
        lp_assert(!is_term(kv.second));
        lp_assert(is_int(kv.second)); // not implemented for real vars!
        den = lcm(den, denominator(kv.first));
    }
    lp_assert(den > 0);
    for (auto& kv : lhs) {
        coeffs.push_back(mono(den * kv.first * sign, kv.second));
    }
    rs = den * c->m_right_side * sign;
    if (kind_is_strict(c->m_kind))
        rs--;
}


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

void int_solver::copy_explanations_from_cut_solver(explanation &ex) {
    TRACE("propagate_and_backjump_step_int",
          for (unsigned j: m_cut_solver.m_explanation)
              m_lar_solver->print_constraint(m_lar_solver->constraints()[j], tout););

    for (unsigned j : m_cut_solver.m_explanation) {
        ex.push_justification(j);
     }
    m_cut_solver.m_explanation.clear();
}

void int_solver::copy_values_from_cut_solver() {
    for (unsigned j = 0; j < m_lar_solver->A_r().column_count() && j < m_cut_solver.number_of_vars(); j++) {
        if (!m_cut_solver.var_is_active(j))
            continue;
        if (!is_int(j)) {
            continue;
        }
        m_lar_solver->m_mpq_lar_core_solver.m_r_x[j] = m_cut_solver.var_value(j);
        lp_assert(m_lar_solver->column_value_is_int(j));
    }
}

void int_solver::catch_up_in_adding_constraints_to_cut_solver() {
	lp_assert(m_cut_solver.number_of_asserts() <= m_lar_solver->constraints().size());
    for (unsigned j = m_cut_solver.number_of_asserts(); j < m_lar_solver->constraints().size(); j++) {
        add_constraint_to_cut_solver(j, m_lar_solver->constraints()[j]);
    }
}

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

bool int_solver::find_cube() {
	if (m_branch_cut_counter % settings().m_int_branch_find_cube != 0)
        return false;
    
    settings().st().m_cube_calls++;
    TRACE("cube",
          for (unsigned j = 0; j < m_lar_solver->A_r().column_count(); j++)
              display_column(tout, j);
          m_lar_solver->print_terms(tout);
          );
    m_lar_solver->push();
    if(!tighten_terms_for_cube()) {
        m_lar_solver->pop();
        return false;
    }

    lp_status st = m_lar_solver->find_feasible_solution();
    if (st != lp_status::FEASIBLE && st != lp_status::OPTIMAL) {
        TRACE("cube", tout << "cannot find a feasiblie solution";);
        m_lar_solver->pop();
        move_non_basic_columns_to_bounds();
        m_lar_solver->find_feasible_solution();
        lp_assert(m_lar_solver->get_status() == lp_status::OPTIMAL);
        // it can happen that we found an integer solution here
        return !m_lar_solver->r_basis_has_inf_int();
    }
    m_lar_solver->round_to_integer_solution();
    m_lar_solver->pop();
    return true;
}

lia_move int_solver::call_cut_solver(lar_term& t, mpq& k, explanation& ex) {
    TRACE("check_main_int", tout<<"cut_solver";);
    catch_up_in_adding_constraints_to_cut_solver();
    auto check_res = m_cut_solver.check();
    settings().st().m_cut_solver_calls++;
    switch (check_res) {
    case cut_solver::lbool::l_false:
        copy_explanations_from_cut_solver(ex); 
        settings().st().m_cut_solver_false++;
        return lia_move::conflict;
    case cut_solver::lbool::l_true:
        settings().st().m_cut_solver_true++;
        copy_values_from_cut_solver();
        lp_assert(m_lar_solver->all_constraints_hold());
        return lia_move::ok;
    case cut_solver::lbool::l_undef:
        settings().st().m_cut_solver_undef++;
        if (m_cut_solver.try_getting_cut(t, k, m_lar_solver->m_mpq_lar_core_solver.m_r_x)) {
            m_lar_solver->subs_term_columns(t);
            TRACE("cut_solver_cuts",
                  tout<<"precut from cut_solver:"; m_lar_solver->print_term(t, tout); tout << " <= " << k << std::endl;);


            return lia_move::cut;
        }
    default:
        return lia_move::give_up;
    }
 }


lia_move int_solver::check(lar_term& t, mpq& k, explanation& ex, bool & upper) {
    if (!has_inf_int()) 
        return lia_move::ok;
    init_check_data();
    if (!gcd_test(ex)) {
        settings().st().m_gcd_conflicts++;
        return lia_move::conflict;
    }

    pivoted_rows_tracking_control pc(m_lar_solver);
    if (patch_nbasic_columns())
        return lia_move::ok;
	

    ++m_branch_cut_counter;
    if (find_cube()){
        settings().st().m_cube_success++;
        return lia_move::ok;
    }

    if ((m_branch_cut_counter) % settings().m_int_branch_cut_solver == 0 && all_columns_are_bounded()) {
        auto r = call_cut_solver(t, k, ex);
        if (r != lia_move::give_up)
            return r;
    }

    if ((m_branch_cut_counter) % settings().m_int_branch_cut_gomory_threshold == 0) {
        return calc_gomory_cut(t, k, ex, upper);
    }
    return create_branch_on_column(find_inf_int_base_column(), t, k, false, upper);
}

lia_move int_solver::calc_gomory_cut(lar_term& t, mpq& k, explanation& ex, bool & upper) {
    if (move_non_basic_columns_to_bounds()) {
        lp_status st = m_lar_solver->find_feasible_solution();
        lp_assert(non_basic_columns_are_at_bounds());
        if (st != lp_status::FEASIBLE && st != lp_status::OPTIMAL) {
            return lia_move::give_up;
        }
    }

    int j = find_inf_int_base_column();
    if (j == -1)
        return lia_move::ok;
    return proceed_with_gomory_cut(t, k, ex, j, upper);
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
    // if (m_lar_solver->has_int_var() && !m_old_values_set.contains(j)) {
    //     m_old_values_set.insert(j);
    //     m_old_values_data[j] = x;
    // }
    auto delta = new_val - x;
    x = new_val;
    m_lar_solver->change_basic_columns_dependend_on_a_given_nb_column(j, delta);
}


// try to make aij*xj to be an integer for every i, but keep the cnange in xj small enough that basic vars remain feasible
void int_solver::patch_nbasic_column(unsigned j) {
    bool infinite_l, infinite_u;
    impq l, u;
    mpq m;
	if (!get_freedom_interval_for_column(j, infinite_l, l, infinite_u, u, m))
		return;
    if (m.is_one() && get_value(j).is_int())
        return;
	if ((get_value(j)/ m).is_int())
		return;
    if (!infinite_l)
        l = ceil(l);
    if (!infinite_u)
        u = floor(u);
    if (!m.is_one()) {
        if (!infinite_l)
            l = m * ceil(l / m);
        if (!infinite_u)
            u = m * floor(u / m);
    }
    if (!infinite_l && !infinite_u) {
        if (l > u) {
            return;
        }
        set_value_for_nbasic_column(j, flip_coin()? l : u);
    } 
    else if (!infinite_u) {
        set_value_for_nbasic_column(j, u);
    }
    else if (!infinite_l) {
        set_value_for_nbasic_column(j, l);
    }
    else {
        set_value_for_nbasic_column(j, impq(0));
    }
    return;
}

bool int_solver::patch_nbasic_columns() {
    settings().st().m_patches++;
    m_lar_solver->pivot_fixed_vars_from_basis();
    for (unsigned j : m_lar_solver->m_mpq_lar_core_solver.m_r_nbasis)
        patch_nbasic_column(j);

	for (unsigned j : m_lar_solver->m_mpq_lar_core_solver.m_r_nbasis) {
		if (!get_value(j).is_int())
			set_value_for_nbasic_column(j,
                                        flip_coin() ? floor(get_value(j)) : ceil(get_value(j))
                                        );
	}
    m_lar_solver->find_feasible_solution();
    lp_assert(m_lar_solver->get_status() == lp_status::FEASIBLE || m_lar_solver->get_status() == lp_status::OPTIMAL);
    if (!has_inf_int()) {
        settings().st().m_patches_success++;
        return true;
    }
    return false;
}

mpq get_denominators_lcm(const row_strip<mpq> & row) {
    mpq r(1);
    for  (auto c : row) {
        r = lcm(r, denominator(c.coeff()));
    }
    return r;
}
    
bool int_solver::gcd_test_for_row(static_matrix<mpq, numeric_pair<mpq>> & A, unsigned i, explanation & ex) {
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
        fill_explanation_from_fixed_columns(A.m_rows[i], ex);
        return false;
    }
        
    if (least_coeff.is_one() && !least_coeff_is_bounded) {
        SASSERT(gcds.is_one());
        return true;
    }
        
    if (least_coeff_is_bounded) {
        return ext_gcd_test(A.m_rows[i], least_coeff, lcm_den, consts, ex);
    }
    return true;
}

void int_solver::add_to_explanation_from_fixed_or_boxed_column(unsigned j, explanation & ex) {
    constraint_index lc, uc;
    m_lar_solver->get_bound_constraint_witnesses_for_column(j, lc, uc);
    ex.m_explanation.push_back(std::make_pair(mpq(1), lc));
    ex.m_explanation.push_back(std::make_pair(mpq(1), uc));
}
void int_solver::fill_explanation_from_fixed_columns(const row_strip<mpq> & row, explanation & ex) {
    for (const auto & c : row) {
        if (!m_lar_solver->column_is_fixed(c.var()))
            continue;
        add_to_explanation_from_fixed_or_boxed_column(c.var(), ex);
    }
}
    
bool int_solver::gcd_test(explanation & ex) {
    if (!settings().m_run_gcd_test)
        return true;
    settings().st().m_gcd_calls++;
    auto & A = m_lar_solver->A_r(); // getting the matrix
    for (unsigned i = 0; i < A.row_count(); i++)
        if (!gcd_test_for_row(A, i, ex)) {
            settings().st().m_gcd_conflicts++;
            return false;
        }
        
    return true;
}

bool int_solver::ext_gcd_test(const row_strip<mpq> & row,
                              mpq const & least_coeff, 
                              mpq const & lcm_den,
                              mpq const & consts, explanation& ex) {
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
            add_to_explanation_from_fixed_or_boxed_column(j, ex);
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
        fill_explanation_from_fixed_columns(row, ex);
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
    m_cut_solver([this](unsigned j) {return m_lar_solver->get_column_name(j);},
                 [this](unsigned j, std::ostream &o) {m_lar_solver->print_constraint(j, o);},
                 [this]() {return m_lar_solver->A_r().column_count();},
                 [this](unsigned j) {return get_value(j);},
                 settings()) {
    //    lp_assert(m_old_values_set.size() == 0);
    // m_old_values_set.resize(lar_slv->A_r().column_count());
    // m_old_values_data.resize(lar_slv->A_r().column_count(), zero_of_type<impq>());
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
               bool & infinite_l,
               impq const & v ) {
    if (infinite_l || v > l) {
        l = v;
        infinite_l = false;
    }
}

void set_upper(impq & u,
               bool & infinite_u,
               impq const & v) {
    if (infinite_u || v < u) {
        u = v;
        infinite_u = false;
    }
}

bool int_solver::get_freedom_interval_for_column(unsigned j, bool & infinite_l, impq & l, bool & infinite_u, impq & u, mpq & m) {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    if (lcs.m_r_heading[j] >= 0) // the basic var 
        return false;

    impq const & xj = get_value(j);
    
    infinite_l = infinite_u = true;
    m = mpq(1);

    if (has_low(j)) {
        set_lower(l, infinite_l, lower_bound(j));
    }
    if (has_upper(j)) {
        set_upper(u, infinite_u, upper_bound(j));
    }

    mpq a; // the coefficient in the column
    unsigned row_index;
    lp_assert(settings().use_tableau());
    const auto & A = m_lar_solver->A_r();
    for (const auto & c : A.column(j)) {
        row_index = c.var();
        const mpq & a = c.coeff();
        
        unsigned rj = lcs.m_r_basis[row_index];
        impq const & xrj = get_value(rj);
        if (is_int(rj) && is_int(j) && !a.is_int())
            m = lcm(m, denominator(a));
        if (a.is_neg()) {
            if (has_low(rj))
                set_lower(l, infinite_l, xj + (xrj - lcs.m_r_lower_bounds()[rj]) / a);

            if (has_upper(rj))
                set_upper(u, infinite_u, xj + (xrj - lcs.m_r_upper_bounds()[rj]) / a);
        }
        else {
            if (has_upper(rj))
                set_lower(l, infinite_l, xj + (xrj - lcs.m_r_upper_bounds()[rj]) / a);
            if (has_low(rj))
                set_upper(u, infinite_u, xj + (xrj - lcs.m_r_lower_bounds()[rj]) / a);
        }
        if (!infinite_l && !infinite_u && l >= u) {
            if (l > u)
                return false;
            return true;
        }
    }

    TRACE("freedom_interval",
          tout << "freedom variable for:\n";
          tout << m_lar_solver->get_column_name(j);
          tout << "[";
          if (infinite_l) tout << "-oo"; else tout << l;
          tout << "; ";
          if (infinite_u) tout << "oo";  else tout << u;
          tout << "]\n";
          tout << "val = " << get_value(j) << "\n";
          tout << "return " << (infinite_l || infinite_u || l <= u);
          );
    return true; //(infinite_l || infinite_u || l <= u);
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
       
    bool infinite_l, infinite_u;
    impq l, u;
    mpq m;
    if (!get_freedom_interval_for_column(j, infinite_l, l, infinite_u, u, m))
        return false;
    if (infinite_l && infinite_u) {
        impq new_val = impq(random() % (range + 1));
        set_value_for_nbasic_column_ignore_old_values(j, new_val);
        return true;
    }
    if (is_int(j)) {
        if (!infinite_l) {
            l = ceil(l);
            if (!m.is_one())
                l = m*ceil(l/m);
        }
        if (!infinite_u) {
            u = floor(u);
            if (!m.is_one())
                u = m*floor(u/m);
        }
    }
    if (!infinite_l && !infinite_u && l >= u)
        return false;
    if (infinite_u) {
        SASSERT(!infinite_l);
        impq delta   = impq(random() % (range + 1));
        impq new_val = l + m*delta;
        set_value_for_nbasic_column_ignore_old_values(j, new_val);
        return true;
    }
    if (infinite_l) {
        SASSERT(!infinite_u);
        impq delta   = impq(random() % (range + 1));
        impq new_val = u - m*delta;
        set_value_for_nbasic_column_ignore_old_values(j, new_val);
        return true;
    }
    if (!is_int(j)) {
        SASSERT(!infinite_l && !infinite_u);
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

lia_move int_solver::create_branch_on_column(int j, lar_term& t, mpq& k, bool free_column, bool & upper) {
    TRACE("check_main_int", tout << "branching" << std::endl;);
    lp_assert(t.is_empty());
	if (j == -1)
		return lia_move::ok;
    t.add_monomial(mpq(1), m_lar_solver->adjust_column_index_to_term_index(j));
    if (free_column) {
        upper = true;
        k = mpq(0);
    } else {
        upper = left_branch_is_more_narrow_than_right(j);
        k = upper? floor(get_value(j)) : ceil(get_value(j));        
    }

    TRACE("arith_int", tout << "branching v" << j << " = " << get_value(j) << "\n";
          display_column(tout, j);
          tout << "k = " << k << std::endl;
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

void int_solver::add_constraint_to_cut_solver(unsigned ci, const lar_base_constraint * c) {
    vector<mono> coeffs;
    mpq rs;
    get_int_coeffs_from_constraint<mpq>(c, coeffs, rs);
    m_cut_solver.add_ineq(coeffs, -rs, ci);
}

void int_solver::pop(unsigned k) {
    m_cut_solver.pop_trail(k);
    while (m_cut_solver.number_of_asserts() > m_lar_solver->constraints().size())
        m_cut_solver.pop_last_assert();
    m_cut_solver.pop_constraints();
}

void int_solver::push() { m_cut_solver.push(); }

unsigned int_solver::column_count() const  { return m_lar_solver->column_count(); }

}
