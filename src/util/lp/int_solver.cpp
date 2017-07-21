/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#include "util/lp/int_solver.h"
#include "util/lp/lar_solver.h"
namespace lp {

void int_solver::fix_non_base_columns() {
	lp_assert(is_feasible() && inf_int_set_is_correct());
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    bool change = false;
    for (unsigned j : lcs.m_r_nbasis) {
        if (column_is_int_inf(j)) {
            change = true;
            set_value_for_nbasic_column(j, floor(lcs.m_r_x[j].x));
        }
    }
    if (!change)
        return;
    if (m_lar_solver->find_feasible_solution() == lp_status::INFEASIBLE)
        failed();
    init_inf_int_set();
    lp_assert(is_feasible() && inf_int_set_is_correct());
}

void int_solver::failed() {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    
    for (unsigned j : m_old_values_set.m_index) {
        lcs.m_r_x[j] = m_old_values_data[j];
        lp_assert(lcs.m_r_solver.column_is_feasible(j));
        lcs.m_r_solver.remove_column_from_inf_set(j);
    }
    lp_assert(lcs.m_r_solver.calc_current_x_is_feasible_include_non_basis());
    lp_assert(lcs.m_r_solver.current_x_is_feasible());
    m_old_values_set.clear();
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
                  iterator_on_row<mpq> it(m_lar_solver->A_r().m_rows[i]);
                  m_lar_solver->print_linear_iterator(&it, tout);
                  tout << "\n";
              }
          }
          tout << "num of int infeasible: " << num << "\n";
          );
}

int int_solver::find_inf_int_base_column() {
    if (m_inf_int_set.is_empty())
        return -1;
    int j = find_inf_int_boxed_base_column_with_smallest_range();
    if (j != -1)
        return j;
    unsigned k = settings().random_next() % m_inf_int_set.m_index.size();
    return m_inf_int_set.m_index[k];
}

int int_solver::find_inf_int_boxed_base_column_with_smallest_range() {
    int result = -1;
    mpq range;
    mpq new_range;
    mpq small_range_thresold(1024);
    unsigned n = 0;
    lar_core_solver & lcs = m_lar_solver->m_mpq_lar_core_solver;

    for (int j : m_inf_int_set.m_index) {
        lp_assert(is_base(j) && column_is_int_inf(j));
        if (!is_boxed(j))
            continue;
        new_range  = lcs.m_r_upper_bounds()[j].x - lcs.m_r_low_bounds()[j].x;
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
            n++;
            if (settings().random_next() % n == 0) {
                result = j;
                continue;
            }
        }
    }
    return result;
    
}

bool int_solver::is_gomory_cut_target() {
    m_iter_on_gomory_row->reset();
    unsigned j;
    TRACE("gomory_cut", m_lar_solver->print_linear_iterator(m_iter_on_gomory_row, tout);
          m_iter_on_gomory_row->reset();
          );

    while (m_iter_on_gomory_row->next(j)) {
        // All non base variables must be at their bounds and assigned to rationals (that is, infinitesimals are not allowed).
        if (j != m_gomory_cut_inf_column && (!at_bound(j) || !is_zero(get_value(j).y))) {
            TRACE("gomory_cut", tout << "row is not gomory cut target:\n";
                  display_column(tout, j);
                  tout << "at_bound:      " << at_bound(j) << "\n";
                  tout << "infinitesimal: " << !is_zero(get_value(j).y) << "\n";);
            return false;
        }
    }
    m_iter_on_gomory_row->reset();
    return true;
}


void int_solver::real_case_in_gomory_cut(const mpq & a, unsigned x_j, mpq & k, lar_term& pol, explanation & expl) {
    mpq f_0  = fractional_part(get_value(m_gomory_cut_inf_column));
    mpq new_a;
    if (at_lower(x_j)) {
        if (a.is_pos()) {
            new_a  =  a / (1 - f_0);
        }
        else {
            new_a  =  a / f_0;
            new_a.neg();
        }
        k += lower_bound(x_j).x * k;  // k.addmul(new_a, lower_bound(x_j).x); // is it a faster operation
        
        expl.push_justification(column_low_bound_constraint(x_j), new_a);
    }
    else {
        lp_assert(at_upper(x_j));
        if (a.is_pos()) {
            new_a =   a / f_0; 
            new_a.neg(); // the upper terms are inverted.
        }
        else {
            new_a =   a / (mpq(1) - f_0); 
        }
        k += upper_bound(x_j).x * k; // k.addmul(new_a, upper_bound(x_j).get_rational());
        expl.push_justification(column_upper_bound_constraint(x_j), new_a);
    }
    TRACE("gomory_cut_detail", tout << a << "*v" << x_j << " k: " << k << "\n";);
    pol.add_monoid(new_a, x_j);
}

constraint_index int_solver::column_upper_bound_constraint(unsigned j) const {
    return m_lar_solver->get_column_upper_bound_witness(j);
}

constraint_index int_solver::column_low_bound_constraint(unsigned j) const {
    return m_lar_solver->get_column_low_bound_witness(j);
}


void int_solver::int_case_in_gomory_cut(const mpq & a, unsigned x_j, mpq & k, lar_term & pol, explanation& expl, mpq & lcm_den) {
    mpq f_0  = fractional_part(get_value(m_gomory_cut_inf_column));
    lp_assert(is_int(x_j));
    mpq f_j =  fractional_part(a);
    TRACE("gomory_cut_detail", 
          tout << a << "*v" << x_j << "\n";
          tout << "fractional_part: " << fractional_part(a) << "\n";
          tout << "f_j: " << f_j << "\n";
          tout << "f_0: " << f_0 << "\n";
          tout << "one_minus_f_0: " << 1 - f_0 << "\n";);
    if (!f_j.is_zero()) {
        mpq new_a;
        if (at_lower(x_j)) {
            auto one_minus_f_0 = 1 - f_0;
            if (f_j <= one_minus_f_0) {
                new_a = f_j / one_minus_f_0;
            }
            else {
                new_a = (1 - f_j) / f_0;
            }
            k.addmul(new_a, lower_bound(x_j).x);
            expl.push_justification(column_low_bound_constraint(x_j), new_a);
        }
        else {
            SASSERT(at_upper(x_j));
            if (f_j <= f_0) {
                new_a = f_j / f_0;
            }
            else {
                new_a = (mpq(1) - f_j) / 1 - f_0;
            }
            new_a.neg(); // the upper terms are inverted
            k.addmul(new_a, upper_bound(x_j).x);
            expl.push_justification(column_upper_bound_constraint(x_j), new_a);
        }
        TRACE("gomory_cut_detail", tout << "new_a: " << new_a << " k: " << k << "\n";);
        pol.add_monoid(new_a, x_j);
        lcm_den = lcm(lcm_den, denominator(new_a));
    }
}

lia_move int_solver::report_conflict_from_gomory_cut(mpq & k) {
    TRACE("empty_pol",
          display_row_info(tout,
                           m_lar_solver->m_mpq_lar_core_solver.m_r_heading[m_gomory_cut_inf_column]););
    lp_assert(k.is_pos());
    // conflict 0 >= k where k is positive
    k.neg(); // returning 0 <= -k
    return lia_move::conflict;
}

void int_solver::gomory_cut_adjust_t_and_k_for_size_gt_1(
                                                         vector<std::pair<mpq, unsigned>> & pol,
                                                         lar_term & t,
                                                         mpq &k,
                                                         unsigned num_ints,
                                                         mpq & lcm_den) {
        if (num_ints > 0) {
            lcm_den = lcm(lcm_den, denominator(k));
            TRACE("gomory_cut_detail", tout << "k: " << k << " lcm_den: " << lcm_den << "\n";
                  linear_combination_iterator_on_vector<mpq> pi(pol);
                  m_lar_solver->print_linear_iterator(&pi, tout);
                  tout << "\nk: " << k << "\n";);
            lp_assert(lcm_den.is_pos());
            if (!lcm_den.is_one()) {
                // normalize coefficients of integer parameters to be integers.
                for (auto & pi: pol) {
                    pi.first *= lcm_den;
                    SASSERT(!is_int(pi.second) || pi.first.is_int());
                }
                k *= lcm_den;
            }
            TRACE("gomory_cut_detail", tout << "after *lcm_den\n";
                  for (unsigned i = 0; i < pol.size(); i++) {
                      tout << pol[i].first << " * v" << pol[i].second << "\n";
                  }
                  tout << "k: " << k << "\n";);
        }
        t.clear();
        // negate everything to return -pol <= -k
        for (const auto & pi: pol)
            t.add_monoid(-pi.first, pi.second);
        k.neg();
}


void int_solver::gomory_cut_adjust_t_and_k_for_size_1(const vector<std::pair<mpq, unsigned>> & pol, lar_term& t, mpq &k) {
    lp_assert(pol.size() == 1);
    unsigned j = pol[0].second;
    k /= pol[0].first;
    bool is_lower = pol[0].first.is_pos();
    if (is_int(j) && !k.is_int()) {
        k = is_lower?ceil(k):floor(k);
    }
    if (is_lower) { // returning -t <= -k which is equivalent to t >= k
        k.neg();
        t.negate();
    }
}


bool int_solver::current_solution_is_inf_on_cut(const lar_term& t, const mpq& k) const {
    const auto & x = m_lar_solver->m_mpq_lar_core_solver.m_r_x;
    impq v = t.apply(x);
    TRACE("gomory_cut", tout << "v = " << v << " k = " << k << std::endl;);
    return v > k;
}

lia_move int_solver::report_gomory_cut(lar_term& t, mpq& k, mpq &lcm_den, unsigned num_ints) {
    lp_assert(!t.is_empty());
    auto pol = t.coeffs_as_vector();
    if (pol.size() == 1)
        gomory_cut_adjust_t_and_k_for_size_1(pol, t, k);
    else
        gomory_cut_adjust_t_and_k_for_size_gt_1(pol, t, k, num_ints, lcm_den);
    return lia_move::cut;
}




lia_move int_solver::mk_gomory_cut(lar_term& t, mpq& k, explanation & expl) {

    lp_assert(column_is_int_inf(m_gomory_cut_inf_column));

    TRACE("gomory_cut", tout << "applying cut at:\n"; m_lar_solver->print_linear_iterator(m_iter_on_gomory_row, tout); tout << std::endl; m_iter_on_gomory_row->reset(););
        
    // gomory will be   t >= k
    k = 1;
    mpq lcm_den(1);
    unsigned num_ints = 0;
    unsigned x_j;
    mpq a;
    while (m_iter_on_gomory_row->next(a, x_j)) {
        if (x_j == m_gomory_cut_inf_column)
            continue;
        // make the format compatible with the format used in: Integrating Simplex with DPLL(T)
        a.neg();  
        if (is_real(x_j)) 
            real_case_in_gomory_cut(a, x_j, k, t, expl);
        else {
            num_ints++;
            int_case_in_gomory_cut(a, x_j, k, t, expl, lcm_den);
        }
    }

    if (t.is_empty())
        return report_conflict_from_gomory_cut(k);

    auto ret = report_gomory_cut(t, k, lcm_den, num_ints);

        // remove this call later :todo
    m_lar_solver->subs_term_columns(t);
    lp_assert(current_solution_is_inf_on_cut(t, k));
    return ret;
    
}

void int_solver::init_check_data() {
	init_inf_int_set();
	unsigned n = m_lar_solver->A_r().column_count();
	m_old_values_set.resize(n);
	m_old_values_data.resize(n);
}

int int_solver::find_next_free_var_in_gomory_row() {
    lp_assert(m_iter_on_gomory_row != nullptr);
    unsigned j;
    while(m_iter_on_gomory_row->next(j)) {
        if (j != m_gomory_cut_inf_column && is_free(j))
            return static_cast<int>(j);
    }
    return -1;
}

lia_move int_solver::proceed_with_gomory_cut(lar_term& t, mpq& k, explanation& ex) {
    int j = find_next_free_var_in_gomory_row();
    if (j != -1) {
        m_found_free_var_in_gomory_row = true;
        lp_assert(t.is_empty());
        t.add_monoid(mpq(1), j);
        k = zero_of_type<mpq>();
        return lia_move::branch; // branch on a free column
    }
    if (m_found_free_var_in_gomory_row || !is_gomory_cut_target()) {
        m_found_free_var_in_gomory_row = false;
        delete m_iter_on_gomory_row;
        m_iter_on_gomory_row = nullptr;
        return lia_move::continue_with_check;
    }

    lia_move ret = mk_gomory_cut(t, k, ex);
    delete m_iter_on_gomory_row;
    m_iter_on_gomory_row = nullptr;
    return ret;
 }


lia_move int_solver::check(lar_term& t, mpq& k, explanation& ex) {
    if (m_iter_on_gomory_row != nullptr) {
        auto ret = proceed_with_gomory_cut(t, k, ex);
        TRACE("gomory_cut", tout << "term t = "; m_lar_solver->print_term_as_indices(t, tout););
        if (ret != lia_move::continue_with_check)
            return ret;
    }

	init_check_data();
    lp_assert(inf_int_set_is_correct());
    // currently it is a reimplementation of
    // final_check_status theory_arith<Ext>::check_int_feasibility()
    // from theory_arith_int.h
	if (m_lar_solver->model_is_int_feasible())
		return lia_move::ok;
    if (!gcd_test(ex))
        return lia_move::conflict;
    /*
      if (m_params.m_arith_euclidean_solver)
            apply_euclidean_solver();
        
    */
    m_lar_solver->pivot_fixed_vars_from_basis();
	patch_int_infeasible_columns();
	fix_non_base_columns();
	TRACE("arith_int_rows", trace_inf_rows(););
    
    if (find_inf_int_base_column() == -1)
        return lia_move::ok;
        

    if ((++m_branch_cut_counter) % settings().m_int_branch_cut_threshold == 0) {
        move_non_base_vars_to_bounds();
        lp_status st = m_lar_solver->find_feasible_solution();
        if (st != lp_status::FEASIBLE && st != lp_status::OPTIMAL) {
            return lia_move::give_up;
        }
        init_inf_int_set(); // todo - can we avoid this call?
        int j = find_inf_int_base_column();
        if (j != -1) {
            // setup the call for gomory cut
            TRACE("arith_int", tout << "j = " << j << " does not have an integer assignment: " << get_value(j) << "\n";);
            unsigned row_index = m_lar_solver->m_mpq_lar_core_solver.m_r_heading[j];
            m_iter_on_gomory_row = m_lar_solver->get_iterator_on_row(row_index);
            m_gomory_cut_inf_column = j;
            return check(t, k, ex);
        }
    }
    else {
        int j = find_inf_int_base_column();
        if (j != -1) {
            TRACE("arith_int", tout << "j" << j << " does not have an integer assignment: " << get_value(j) << "\n";);

            lp_assert(t.is_empty());
            t.add_monoid(mpq(1), j);
            k = floor(get_value(j));
            TRACE("arith_int", tout << "branching v" << j << " = " << get_value(j) << "\n";
              display_column(tout, j);
              tout << "k = " << k << std::endl;
              );
            // todo: remove this call later when theory_lra handles term indices
            m_lar_solver->subs_term_columns(t);
            lp_assert(current_solution_is_inf_on_cut(t, k));
            return lia_move::branch;
        }
    }

	lp_assert(m_lar_solver->m_mpq_lar_core_solver.r_basis_is_OK());
	//    return true;
    return lia_move::give_up;
}

void int_solver::move_non_base_vars_to_bounds() {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    for (unsigned j : lcs.m_r_nbasis) {
        auto & val = lcs.m_r_x[j];
        switch (lcs.m_column_types()[j]) {
        case column_type::boxed:
            if (val != lcs.m_r_low_bounds()[j] && val != lcs.m_r_upper_bounds()[j])
                set_value_for_nbasic_column(j, lcs.m_r_low_bounds()[j]);
            break;
        case column_type::low_bound:
            if (val != lcs.m_r_low_bounds()[j])
                set_value_for_nbasic_column(j, lcs.m_r_low_bounds()[j]);
            break;
        case column_type::upper_bound:
            if (val != lcs.m_r_upper_bounds()[j])
                set_value_for_nbasic_column(j, lcs.m_r_upper_bounds()[j]);
            break;
        default:
            if (is_int(j) && !val.is_int()) {
                set_value_for_nbasic_column(j, impq(floor(val)));
            }
        }
    }
}



void int_solver::set_value_for_nbasic_column(unsigned j, const impq & new_val) {
	lp_assert(!is_base(j));
    auto & x = m_lar_solver->m_mpq_lar_core_solver.m_r_x[j];
    if (!m_old_values_set.contains(j)) {
        m_old_values_set.insert(j);
        m_old_values_data[j] = x;
    }
    auto delta = new_val - x;
    x = new_val;
    m_lar_solver->change_basic_x_by_delta_on_column(j, delta);

	auto * it = get_column_iterator(j);
    update_column_in_int_inf_set(j);
	unsigned i;
	while (it->next(i))
		update_column_in_int_inf_set(m_lar_solver->m_mpq_lar_core_solver.m_r_basis[i]);
	delete it;
}

void int_solver::patch_int_infeasible_columns() {
    bool inf_l, inf_u;
    impq l, u;
    mpq m;
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    for (unsigned j : lcs.m_r_nbasis) {
        if (!is_int(j))
            continue;
        get_freedom_interval_for_column(j, inf_l, l, inf_u, u, m);
        impq & val = lcs.m_r_x[j];
        bool val_is_int = val.is_int();
        bool m_is_one = m.is_one();
        if (m.is_one() && val_is_int)
            continue;
        // check whether value of j is already a multiple of m.
        if (val_is_int && (val.x / m).is_int())
            continue;
        TRACE("patch_int",
              tout << "TARGET j" << j << " -> [";
              if (inf_l) tout << "-oo"; else tout << l;
              tout << ", ";
              if (inf_u) tout << "oo"; else tout << u;
              tout << "]";
              tout << ", m: " << m << ", val: " << val << ", is_int: " << m_lar_solver->column_is_int(j) << "\n";);
        if (!inf_l) {
            l = m_is_one? ceil(l) : m * ceil(l / m);
            if (inf_u || l <= u) {
                TRACE("patch_int",
                      tout << "patching with l: " << l << '\n';);
                
                set_value_for_nbasic_column(j, l);
            } else {
                TRACE("patch_int", 
                      tout << "not patching " << l << "\n";);
            }
        } else if (!inf_u) {
            u = m_is_one? floor(u) : m * floor(u / m);
            set_value_for_nbasic_column(j, u);
            TRACE("patch_int",
                  tout << "patching with u: " << u << '\n';);
        } else {
            set_value_for_nbasic_column(j, impq(0));
            TRACE("patch_int",
                  tout << "patching with 0\n";);
        }
		lp_assert(is_feasible() && inf_int_set_is_correct());
	}
}

mpq get_denominators_lcm(iterator_on_row<mpq> &it) {
    mpq r(1);
    mpq a;
    unsigned j;
    while (it.next(a, j)) {
        r = lcm(r, denominator(a));
    }
    return r;
}
    
bool int_solver::gcd_test_for_row(static_matrix<mpq, numeric_pair<mpq>> & A, unsigned i, explanation & ex) {
    iterator_on_row<mpq> it(A.m_rows[i]);
    mpq lcm_den = get_denominators_lcm(it);
    mpq consts(0);
    mpq gcds(0);
    mpq least_coeff(0);
    bool    least_coeff_is_bounded = false;
    mpq a;
    unsigned j;
    while (it.next(a, j)) {
            if (m_lar_solver->column_is_fixed(j)) {
                mpq aux = lcm_den * a;
                consts += aux * m_lar_solver->column_low_bound(j).x;
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
        
        if (!(consts / gcds).is_int())
            fill_explanation_from_fixed_columns(it, ex);
        
        if (least_coeff.is_one() && !least_coeff_is_bounded) {
            SASSERT(gcds.is_one());
            return true;
        }
        
        if (least_coeff_is_bounded) {
            return ext_gcd_test(it, least_coeff, lcm_den, consts, ex);
        }
        return true;
}

void int_solver::add_to_explanation_from_fixed_or_boxed_column(unsigned j, explanation & ex) {
    constraint_index lc, uc;
    m_lar_solver->get_bound_constraint_witnesses_for_column(j, lc, uc);
    ex.m_explanation.push_back(std::make_pair(mpq(1), lc));
    ex.m_explanation.push_back(std::make_pair(mpq(1), uc));
}
void int_solver::fill_explanation_from_fixed_columns(iterator_on_row<mpq> & it, explanation & ex) {
    it.reset();
    unsigned j;
    while (it.next(j)) {
        if (!m_lar_solver->column_is_fixed(j))
            continue;
        add_to_explanation_from_fixed_or_boxed_column(j, ex);
    }
}
    
bool int_solver::gcd_test(explanation & ex) {
	auto & A = m_lar_solver->A_r(); // getting the matrix
	for (unsigned i = 0; i < A.row_count(); i++)
        if (!gcd_test_for_row(A, i, ex)) {
            std::cout << "false from gcd_test\n" ;
            return false;
        }
        
	return true;
}

bool int_solver::ext_gcd_test(iterator_on_row<mpq> & it,
                              mpq const & least_coeff, 
                              mpq const & lcm_den,
                              mpq const & consts, explanation& ex) {
    mpq gcds(0);
    mpq l(consts);
    mpq u(consts);

    it.reset();
    mpq a;
    unsigned j;
    while (it.next(a, j)) {
        if (m_lar_solver->column_is_fixed(j))
            continue;
        SASSERT(!m_lar_solver->column_is_real(j));
        mpq ncoeff = lcm_den * a;
        SASSERT(ncoeff.is_int());
        mpq abs_ncoeff = abs(ncoeff);
        if (abs_ncoeff == least_coeff) {
            SASSERT(m_lar_solver->column_is_bounded(j));
            if (ncoeff.is_pos()) {
                // l += ncoeff * m_lar_solver->column_low_bound(j).x;
                l.addmul(ncoeff, m_lar_solver->column_low_bound(j).x);
                // u += ncoeff * m_lar_solver->column_upper_bound(j).x;
                u.addmul(ncoeff, m_lar_solver->column_upper_bound(j).x);
            }
            else {
                // l += ncoeff * upper_bound(j).get_rational();
                l.addmul(ncoeff, m_lar_solver->column_upper_bound(j).x);
                // u += ncoeff * lower_bound(j).get_rational();
                u.addmul(ncoeff, m_lar_solver->column_low_bound(j).x);
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
        fill_explanation_from_fixed_columns(it, ex);
        return false;
    }
        
    return true;

}

linear_combination_iterator<mpq> * int_solver::get_column_iterator(unsigned j) {
    if (m_lar_solver->use_tableau())
        return new iterator_on_column<mpq, impq>(m_lar_solver->A_r().m_columns[j], m_lar_solver->A_r());
   return new iterator_on_indexed_vector<mpq>(m_lar_solver->get_column_in_lu_mode(j));
}


int_solver::int_solver(lar_solver* lar_slv) :
    m_lar_solver(lar_slv),
    m_branch_cut_counter(0),
    m_iter_on_gomory_row(nullptr),
    m_found_free_var_in_gomory_row(false) {
    lp_assert(m_old_values_set.size() == 0);
    m_old_values_set.resize(lar_slv->A_r().column_count());
    m_old_values_data.resize(lar_slv->A_r().column_count(), zero_of_type<impq>());    
}

bool int_solver::lower(unsigned j) const {
    switch (m_lar_solver->m_mpq_lar_core_solver.m_column_types()[j]) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::low_bound:
        return true;
    default:
        return false;
    }
}

bool int_solver::upper(unsigned j) const {
    switch (m_lar_solver->m_mpq_lar_core_solver.m_column_types()[j]) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::upper_bound:
        return true;
    default:
        return false;
    }
}

const impq& int_solver::lower_bound(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_r_low_bounds()[j];
}

const impq& int_solver::upper_bound(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_r_upper_bounds()[j];
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

bool int_solver::get_freedom_interval_for_column(unsigned x_j, bool & inf_l, impq & l, bool & inf_u, impq & u, mpq & m) {
    auto & lcs = m_lar_solver->m_mpq_lar_core_solver;
    if (lcs.m_r_heading[x_j] >= 0) // the basic var 
        return false;

    impq const & x_j_val = lcs.m_r_x[x_j];
    linear_combination_iterator<mpq> *it = get_column_iterator(x_j);

    inf_l = true;
    inf_u = true;
    l = u = zero_of_type<impq>();
    m = mpq(1);

    if (lower(x_j)) {
        set_lower(l, inf_l, lower_bound(x_j));
    }
    if (upper(x_j)) {
        set_upper(u, inf_u, upper_bound(x_j));
    }

    mpq a_ij; unsigned i;
    while (it->next(a_ij, i)) {
        unsigned x_i = lcs.m_r_basis[i];
        impq const & x_i_val = lcs.m_r_x[x_i];
        if (is_int(x_i) && is_int(x_j) && !a_ij.is_int())
            m = lcm(m, denominator(a_ij));
        bool x_i_lower = lower(x_i);
        bool x_i_upper = upper(x_i);
        if (a_ij.is_neg()) {
            if (x_i_lower) {
                impq new_l = x_j_val + ((x_i_val - lcs.m_r_low_bounds()[x_i]) / a_ij);
                set_lower(l, inf_l, new_l);
                if (!inf_l && !inf_u && l == u) break;;                
            }
            if (x_i_upper) {
                impq new_u = x_j_val + ((x_i_val - lcs.m_r_upper_bounds()[x_i]) / a_ij);
                set_upper(u, inf_u, new_u);
                if (!inf_l && !inf_u && l == u) break;;                
            }
        }
        else {
            if (x_i_upper) {
                impq new_l = x_j_val + ((x_i_val - lcs.m_r_upper_bounds()[x_i]) / a_ij);
                set_lower(l, inf_l, new_l);
                if (!inf_l && !inf_u && l == u) break;;                
            }
            if (x_i_lower) {
                impq new_u = x_j_val + ((x_i_val - lcs.m_r_low_bounds()[x_i]) / a_ij);
                set_upper(u, inf_u, new_u);
                if (!inf_l && !inf_u && l == u) break;;                
            }
        }
    }

    delete it;
    TRACE("freedom_interval",
          tout << "freedom variable for:\n";
          tout << m_lar_solver->get_column_name(x_j);
          tout << "[";
          if (inf_l) tout << "-oo"; else tout << l;
          tout << "; ";
          if (inf_u) tout << "oo";  else tout << u;
          tout << "]\n";
          tout << "val = " << get_value(x_j) << "\n";
          );
    lp_assert(inf_l || l <= get_value(x_j));
    lp_assert(inf_u || u >= get_value(x_j));
    return true;

}

bool int_solver::is_int(unsigned j) const {
    return m_lar_solver->column_is_int(j);
}

bool int_solver::is_real(unsigned j) const {
    return !is_int(j);
}

bool int_solver::value_is_int(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_r_x[j].is_int();
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

bool int_solver::inf_int_set_is_correct() const {
    for (unsigned j = 0; j < m_lar_solver->A_r().column_count(); j++) {
        if (m_inf_int_set.contains(j) != (is_int(j) && (!value_is_int(j))))
            return false;
    }
    return true;
}

bool int_solver::column_is_int_inf(unsigned j) const {
    return is_int(j) && (!value_is_int(j));
}
    
void int_solver::init_inf_int_set() {
    m_inf_int_set.clear();
    m_inf_int_set.resize(m_lar_solver->A_r().column_count());
	for (unsigned j = 0; j < m_lar_solver->A_r().column_count(); j++) {
        if (column_is_int_inf(j))
            m_inf_int_set.insert(j);
    }
}

void int_solver::update_column_in_int_inf_set(unsigned j) {
    if (is_int(j) && (!value_is_int(j)))
        m_inf_int_set.insert(j);
    else
        m_inf_int_set.erase(j);
}

bool int_solver::is_base(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_r_heading[j] >= 0;
}

bool int_solver::is_boxed(unsigned j) const {
    return m_lar_solver->m_mpq_lar_core_solver.m_column_types[j] == column_type::boxed;
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
            mpq_solver.m_low_bounds[j] == get_value(j) ||
            mpq_solver.m_upper_bounds[j] == get_value(j);
    case column_type::low_bound:
        return mpq_solver.m_low_bounds[j] == get_value(j);
    case column_type::upper_bound:
        return  mpq_solver.m_upper_bounds[j] == get_value(j);
    default:
        return false;
    }
}

bool int_solver::at_lower(unsigned j) const {
    auto & mpq_solver = m_lar_solver->m_mpq_lar_core_solver.m_r_solver;
    switch (mpq_solver.m_column_types[j] ) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::low_bound:
        return mpq_solver.m_low_bounds[j] == get_value(j);
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
    auto it = m_lar_solver->get_iterator_on_row(row_index);
    mpq a;
    unsigned j;
    while (it->next(a, j)) {
        if (numeric_traits<mpq>::is_pos(a))
            out << "+";
        out << a << rslv.column_name(j) << " ";
    }

    it->reset();
    while(it->next(j)) {
        rslv.print_column_bound_info(j, out);
    }
    rslv.print_column_bound_info(rslv.m_basis[row_index], out);
    delete it;
}
}
