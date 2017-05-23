/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "util/lp/random_updater.h"
#include "util/lp/static_matrix.h"
#include "util/lp/lar_solver.h"
#include "util/vector.h"
namespace lean {



random_updater::random_updater(
                               lar_core_solver & lar_core_solver,
                               const vector<unsigned> & column_indices) :
    m_core_solver(lar_core_solver),
    range(100000) {
    for (unsigned j : column_indices)
        add_column_to_sets(j);
}

random_updater::interval random_updater::get_interval_of_non_basic_var(unsigned j) {
    interval ret;
    switch (m_core_solver.get_column_type(j)) {
    case column_type::free_column:
        break;
    case column_type::low_bound:
        ret.set_low_bound(m_core_solver.m_r_low_bounds[j]);
        break;
    case column_type::upper_bound:
        ret.set_upper_bound(m_core_solver.m_r_upper_bounds[j]);
        break;
    case column_type::boxed:
    case column_type::fixed:
        ret.set_low_bound(m_core_solver.m_r_low_bounds[j]);
        ret.set_upper_bound(m_core_solver.m_r_upper_bounds[j]);
        break;
    default:
        lean_assert(false);
    }
    return ret;
}

void random_updater::diminish_interval_for_basic_var(numeric_pair<mpq>& nb_x, unsigned j,
                                                     mpq & a,
                                                     interval & r) {
    lean_assert(m_core_solver.m_r_heading[j] >= 0);
    numeric_pair<mpq> delta;
    lean_assert(a != zero_of_type<mpq>());
    switch (m_core_solver.get_column_type(j)) {
    case column_type::free_column:
        break;
    case column_type::low_bound:
        delta = m_core_solver.m_r_x[j] - m_core_solver.m_r_low_bounds[j];
        lean_assert(delta >= zero_of_type<numeric_pair<mpq>>());
        if (a > 0) {
            r.set_upper_bound(nb_x + delta / a);
        } else {
            r.set_low_bound(nb_x + delta / a);
        }
        break;
    case column_type::upper_bound:
        delta = m_core_solver.m_r_upper_bounds()[j] - m_core_solver.m_r_x[j];
        lean_assert(delta >= zero_of_type<numeric_pair<mpq>>());
        if (a > 0) {
            r.set_low_bound(nb_x - delta / a);
        } else {
            r.set_upper_bound(nb_x - delta / a);
        }
        break;
    case column_type::boxed:
        if (a > 0) {
            delta = m_core_solver.m_r_x[j] - m_core_solver.m_r_low_bounds[j];
            lean_assert(delta >= zero_of_type<numeric_pair<mpq>>());
            r.set_upper_bound(nb_x + delta / a);
            delta = m_core_solver.m_r_upper_bounds()[j] - m_core_solver.m_r_x[j];
            lean_assert(delta >= zero_of_type<numeric_pair<mpq>>());
            r.set_low_bound(nb_x - delta / a);
        } else { // a < 0
            delta = m_core_solver.m_r_upper_bounds()[j] - m_core_solver.m_r_x[j];
            lean_assert(delta >= zero_of_type<numeric_pair<mpq>>());
            r.set_upper_bound(nb_x - delta / a);
            delta = m_core_solver.m_r_x[j] - m_core_solver.m_r_low_bounds[j];
            lean_assert(delta >= zero_of_type<numeric_pair<mpq>>());
            r.set_low_bound(nb_x + delta / a);
        }
        break;
    case column_type::fixed:
          r.set_low_bound(nb_x);
          r.set_upper_bound(nb_x);
          break;
    default:
        lean_assert(false);
    }
}


void random_updater::diminish_interval_to_leave_basic_vars_feasible(numeric_pair<mpq> &nb_x, interval & r) {
    m_column_j->reset();
    unsigned i;
    mpq a;
    while (m_column_j->next(a, i)) {
        diminish_interval_for_basic_var(nb_x, m_core_solver.m_r_basis[i], a, r);
        if (r.is_empty())
            break;
    }
}

random_updater::interval random_updater::find_shift_interval(unsigned j) {
    interval ret = get_interval_of_non_basic_var(j);
    diminish_interval_to_leave_basic_vars_feasible(m_core_solver.m_r_x[j], ret);
    return ret;
}

void random_updater::shift_var(unsigned j, interval & r) {
    lean_assert(r.contains(m_core_solver.m_r_x[j]));
    lean_assert(m_core_solver.m_r_solver.column_is_feasible(j));
    auto old_x = m_core_solver.m_r_x[j];
    remove_value(old_x);
    auto new_val = m_core_solver.m_r_x[j] = get_random_from_interval(r);
    add_value(new_val);

    lean_assert(r.contains(m_core_solver.m_r_x[j]));
    lean_assert(m_core_solver.m_r_solver.column_is_feasible(j));
    auto delta = m_core_solver.m_r_x[j] - old_x;
   
    unsigned i;
    m_column_j->reset();
    mpq a;
    while(m_column_j->next(a, i)) {
        unsigned bj = m_core_solver.m_r_basis[i];
        m_core_solver.m_r_x[bj] -= a * delta;
        lean_assert(m_core_solver.m_r_solver.column_is_feasible(bj));
    }
    lean_assert(m_core_solver.m_r_solver.A_mult_x_is_off() == false);
}

numeric_pair<mpq> random_updater::get_random_from_interval(interval & r) {
    unsigned rand = m_core_solver.settings().random_next();
    if ((!r.low_bound_is_set)  && (!r.upper_bound_is_set))
        return numeric_pair<mpq>(rand % range, 0);
    if (r.low_bound_is_set  && (!r.upper_bound_is_set))
        return r.low_bound + numeric_pair<mpq>(rand % range, 0);
    if ((!r.low_bound_is_set) && r.upper_bound_is_set)
        return r.upper_bound - numeric_pair<mpq>(rand % range, 0);
    lean_assert(r.low_bound_is_set && r.upper_bound_is_set);
    return r.low_bound + (rand % range) * (r.upper_bound - r.low_bound)/ range;
}

void random_updater::random_shift_var(unsigned j) {
    m_column_j = m_core_solver.get_column_iterator(j);
    if (m_column_j->size() >= 50) {
        delete m_column_j;
        return;
    }
    interval interv = find_shift_interval(j);
    if (interv.is_empty()) {
        delete m_column_j;
        return;
    }

    shift_var(j, interv);
    delete m_column_j;
}

void random_updater::update() {
    for (auto j : m_var_set) {
        if (m_var_set.size() <= m_values.size()) {
            break; // we are done
        }
        random_shift_var(j);
    }
}

void random_updater::add_value(numeric_pair<mpq>& v) {
    auto it = m_values.find(v);
    if (it == m_values.end()) {
        m_values[v] = 1;
    } else {
        it->second++;
    }
}

void random_updater::remove_value(numeric_pair<mpq>& v) {
    std::unordered_map<numeric_pair<mpq>, unsigned>::iterator it = m_values.find(v);
    lean_assert(it != m_values.end());
    it->second--;
    if (it->second == 0)
        m_values.erase((std::unordered_map<numeric_pair<mpq>, unsigned>::const_iterator)it);
}

void random_updater::add_column_to_sets(unsigned j) {
    if (m_core_solver.m_r_heading[j] < 0) {
        m_var_set.insert(j);
        add_value(m_core_solver.m_r_x[j]);
    } else {
        unsigned row = m_core_solver.m_r_heading[j];
        for (auto row_c : m_core_solver.m_r_A.m_rows[row]) {
            unsigned cj = row_c.m_j;
            if (m_core_solver.m_r_heading[cj] < 0) {
                m_var_set.insert(cj);
                add_value(m_core_solver.m_r_x[cj]);
            }
        }
    }
}
}
