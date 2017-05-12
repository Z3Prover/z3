/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

// here we are inside lean::lar_solver class

bool strategy_is_undecided() const {
    return m_settings.simplex_strategy() == simplex_strategy_enum::undecided;
}

var_index add_var(unsigned ext_j) {
    var_index i;
    lean_assert (ext_j < m_terms_start_index); 

    if (ext_j >= m_terms_start_index)
        throw 0; // todo : what is the right way to exit?
            
    if (try_get_val(m_ext_vars_to_columns, ext_j, i)) {
        return i;
    }
    lean_assert(m_vars_to_ul_pairs.size() == A_r().column_count());
    i = A_r().column_count();
    m_vars_to_ul_pairs.push_back (ul_pair(static_cast<unsigned>(-1)));
    add_non_basic_var_to_core_fields(ext_j);
    lean_assert(sizes_are_correct());
    return i;
}

void register_new_ext_var_index(unsigned ext_v) {
    lean_assert(!contains(m_ext_vars_to_columns, ext_v));
    unsigned j = static_cast<unsigned>(m_ext_vars_to_columns.size());
    m_ext_vars_to_columns[ext_v] = j;
    lean_assert(m_columns_to_ext_vars_or_term_indices.size() == j);
    m_columns_to_ext_vars_or_term_indices.push_back(ext_v);
}

void add_non_basic_var_to_core_fields(unsigned ext_j) {
    register_new_ext_var_index(ext_j);
    m_mpq_lar_core_solver.m_column_types.push_back(column_type::free_column);
    m_columns_with_changed_bound.increase_size_by_one();
    add_new_var_to_core_fields_for_mpq(false);
    if (use_lu())
        add_new_var_to_core_fields_for_doubles(false);
}

void add_new_var_to_core_fields_for_doubles(bool register_in_basis) {
    unsigned j = A_d().column_count();
    A_d().add_column();
    lean_assert(m_mpq_lar_core_solver.m_d_x.size() == j);
    //        lean_assert(m_mpq_lar_core_solver.m_d_low_bounds.size() == j && m_mpq_lar_core_solver.m_d_upper_bounds.size() == j);  // restore later
    m_mpq_lar_core_solver.m_d_x.resize(j + 1 ); 
    m_mpq_lar_core_solver.m_d_low_bounds.resize(j + 1);
    m_mpq_lar_core_solver.m_d_upper_bounds.resize(j + 1);
    lean_assert(m_mpq_lar_core_solver.m_d_heading.size() == j); // as A().column_count() on the entry to the method
    if (register_in_basis) {
        A_d().add_row();
        m_mpq_lar_core_solver.m_d_heading.push_back(m_mpq_lar_core_solver.m_d_basis.size());
        m_mpq_lar_core_solver.m_d_basis.push_back(j);
    }else {
        m_mpq_lar_core_solver.m_d_heading.push_back(- static_cast<int>(m_mpq_lar_core_solver.m_d_nbasis.size()) - 1);
        m_mpq_lar_core_solver.m_d_nbasis.push_back(j);
    }
}

void add_new_var_to_core_fields_for_mpq(bool register_in_basis) {
    unsigned j = A_r().column_count();
    A_r().add_column();
    lean_assert(m_mpq_lar_core_solver.m_r_x.size() == j);
    //        lean_assert(m_mpq_lar_core_solver.m_r_low_bounds.size() == j && m_mpq_lar_core_solver.m_r_upper_bounds.size() == j);  // restore later
    m_mpq_lar_core_solver.m_r_x.resize(j + 1);
    m_mpq_lar_core_solver.m_r_low_bounds.increase_size_by_one();
    m_mpq_lar_core_solver.m_r_upper_bounds.increase_size_by_one();
    m_mpq_lar_core_solver.m_r_solver.m_inf_set.increase_size_by_one();
    m_mpq_lar_core_solver.m_r_solver.m_costs.resize(j + 1);
    m_mpq_lar_core_solver.m_r_solver.m_d.resize(j + 1);
    lean_assert(m_mpq_lar_core_solver.m_r_heading.size() == j); // as A().column_count() on the entry to the method
    if (register_in_basis) {
        A_r().add_row();
        m_mpq_lar_core_solver.m_r_heading.push_back(m_mpq_lar_core_solver.m_r_basis.size());
        m_mpq_lar_core_solver.m_r_basis.push_back(j);
        if (m_settings.bound_propagation())
            m_rows_with_changed_bounds.insert(A_r().row_count() - 1);
    } else {
        m_mpq_lar_core_solver.m_r_heading.push_back(- static_cast<int>(m_mpq_lar_core_solver.m_r_nbasis.size()) - 1);
        m_mpq_lar_core_solver.m_r_nbasis.push_back(j);
    }
}


var_index add_term_undecided(const vector<std::pair<mpq, var_index>> & coeffs,
                             const mpq &m_v) {
    m_terms.push_back(new lar_term(coeffs, m_v));
    m_orig_terms.push_back(new lar_term(coeffs, m_v));
    return m_terms_start_index +  m_terms.size() - 1;
}

// terms
var_index add_term(const vector<std::pair<mpq, var_index>> & coeffs,
                   const mpq &m_v) {
    if (strategy_is_undecided())
        return add_term_undecided(coeffs, m_v);

    m_terms.push_back(new lar_term(coeffs, m_v));
    m_orig_terms.push_back(new lar_term(coeffs, m_v));
    unsigned adjusted_term_index = m_terms.size() - 1;
    var_index ret = m_terms_start_index + adjusted_term_index;
    if (use_tableau() && !coeffs.empty()) {
        add_row_for_term(m_orig_terms.back(), ret);
        if (m_settings.bound_propagation())
            m_rows_with_changed_bounds.insert(A_r().row_count() - 1);
    } 
    lean_assert(m_ext_vars_to_columns.size() == A_r().column_count());
    return ret;
}

void add_row_for_term(const lar_term * term, unsigned term_ext_index) {
    lean_assert(sizes_are_correct());
    add_row_from_term_no_constraint(term, term_ext_index);
    lean_assert(sizes_are_correct());
}

void add_row_from_term_no_constraint(const lar_term * term, unsigned term_ext_index) {
    register_new_ext_var_index(term_ext_index);
    // j will be a new variable
	unsigned j = A_r().column_count();
    ul_pair ul(j);
    m_vars_to_ul_pairs.push_back(ul);
    add_basic_var_to_core_fields();
    if (use_tableau()) {
        auto it = iterator_on_term_with_basis_var(*term, j);
        A_r().fill_last_row_with_pivoting(it,
                                          m_mpq_lar_core_solver.m_r_solver.m_basis_heading);
        m_mpq_lar_core_solver.m_r_solver.m_b.resize(A_r().column_count(), zero_of_type<mpq>());
    } else {
        fill_last_row_of_A_r(A_r(), term);
    }
    m_mpq_lar_core_solver.m_r_x[j] = get_basic_var_value_from_row_directly(A_r().row_count() - 1);
    if (use_lu())
        fill_last_row_of_A_d(A_d(), term);
}

void add_basic_var_to_core_fields() {
    bool use_lu = m_mpq_lar_core_solver.need_to_presolve_with_double_solver();
    lean_assert(!use_lu || A_r().column_count() == A_d().column_count());
    m_mpq_lar_core_solver.m_column_types.push_back(column_type::free_column);
    m_columns_with_changed_bound.increase_size_by_one();
    m_rows_with_changed_bounds.increase_size_by_one();
    add_new_var_to_core_fields_for_mpq(true);
    if (use_lu)
        add_new_var_to_core_fields_for_doubles(true);
}

constraint_index add_var_bound(var_index j, lconstraint_kind kind, const mpq & right_side)  {
	constraint_index ci = m_constraints.size();
    if (!is_term(j)) { // j is a var
        auto vc = new lar_var_constraint(j, kind, right_side);
        m_constraints.push_back(vc);
        update_column_type_and_bound(j, kind, right_side, ci);
    } else {
        add_var_bound_on_constraint_for_term(j, kind, right_side, ci);
    }
    lean_assert(sizes_are_correct());
    return ci;
}

void update_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index) {
    switch(m_mpq_lar_core_solver.m_column_types[j]) {
    case column_type::free_column:
        update_free_column_type_and_bound(j, kind, right_side, constr_index);
        break;
    case column_type::boxed:
        update_boxed_column_type_and_bound(j, kind, right_side, constr_index);
        break;
    case column_type::low_bound:
        update_low_bound_column_type_and_bound(j, kind, right_side, constr_index);
        break;
    case column_type::upper_bound:
        update_upper_bound_column_type_and_bound(j, kind, right_side, constr_index);
        break;
    case column_type::fixed:
        update_fixed_column_type_and_bound(j, kind, right_side, constr_index);
        break;
    default:
        lean_assert(false); // cannot be here
    }
}

void add_var_bound_on_constraint_for_term(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
    lean_assert(is_term(j));
    unsigned adjusted_term_index = adjust_term_index(j);
    unsigned term_j;
    if (try_get_val(m_ext_vars_to_columns, j, term_j)) {
        mpq rs = right_side - m_orig_terms[adjusted_term_index]->m_v;
        m_constraints.push_back(new lar_term_constraint(m_orig_terms[adjusted_term_index], kind, right_side));
        update_column_type_and_bound(term_j, kind, rs, ci);
    }
    else {
        add_constraint_from_term_and_create_new_column_row(j, m_orig_terms[adjusted_term_index], kind, right_side);
    }
}


void add_constraint_from_term_and_create_new_column_row(unsigned term_j, const lar_term* term,
                                                        lconstraint_kind kind, const mpq & right_side) {

    add_row_from_term_no_constraint(term, term_j);
    unsigned j = A_r().column_count() - 1;
    update_column_type_and_bound(j, kind, right_side - term->m_v, m_constraints.size());
    m_constraints.push_back(new lar_term_constraint(term, kind, right_side));
    lean_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_solver.m_costs.size());
}

void decide_on_strategy_and_adjust_initial_state() {
	lean_assert(strategy_is_undecided());
	if (m_vars_to_ul_pairs.size() > m_settings.column_number_threshold_for_using_lu_in_lar_solver) {
        m_settings.simplex_strategy() = simplex_strategy_enum::lu;
    } else {
        m_settings.simplex_strategy() = simplex_strategy_enum::tableau_rows; // todo: when to switch to tableau_costs?
    }
    adjust_initial_state();
}

void adjust_initial_state() {
    switch (m_settings.simplex_strategy()) {
    case simplex_strategy_enum::lu:
        adjust_initial_state_for_lu();
        break;
    case simplex_strategy_enum::tableau_rows:
        adjust_initial_state_for_tableau_rows();
        break;
    case simplex_strategy_enum::tableau_costs:
        lean_assert(false); // not implemented
    case simplex_strategy_enum::undecided:
        adjust_initial_state_for_tableau_rows();
        break;
    }
}

void adjust_initial_state_for_lu() {
    copy_from_mpq_matrix(A_d());
	unsigned n = A_d().column_count();
	m_mpq_lar_core_solver.m_d_x.resize(n);
	m_mpq_lar_core_solver.m_d_low_bounds.resize(n);
	m_mpq_lar_core_solver.m_d_upper_bounds.resize(n);
	m_mpq_lar_core_solver.m_d_heading = m_mpq_lar_core_solver.m_r_heading;
	m_mpq_lar_core_solver.m_d_basis = m_mpq_lar_core_solver.m_r_basis;

	/*
    unsigned j = A_d().column_count();
    A_d().add_column();
    lean_assert(m_mpq_lar_core_solver.m_d_x.size() == j);
    //        lean_assert(m_mpq_lar_core_solver.m_d_low_bounds.size() == j && m_mpq_lar_core_solver.m_d_upper_bounds.size() == j);  // restore later
    m_mpq_lar_core_solver.m_d_x.resize(j + 1 ); 
    m_mpq_lar_core_solver.m_d_low_bounds.resize(j + 1);
    m_mpq_lar_core_solver.m_d_upper_bounds.resize(j + 1);
    lean_assert(m_mpq_lar_core_solver.m_d_heading.size() == j); // as A().column_count() on the entry to the method
    if (register_in_basis) {
        A_d().add_row();
        m_mpq_lar_core_solver.m_d_heading.push_back(m_mpq_lar_core_solver.m_d_basis.size());
        m_mpq_lar_core_solver.m_d_basis.push_back(j);
    }else {
        m_mpq_lar_core_solver.m_d_heading.push_back(- static_cast<int>(m_mpq_lar_core_solver.m_d_nbasis.size()) - 1);
        m_mpq_lar_core_solver.m_d_nbasis.push_back(j);
        }*/
}

void adjust_initial_state_for_tableau_rows() {
    for (unsigned j = 0; j < m_terms.size(); j++) {
        if (contains(m_ext_vars_to_columns, j + m_terms_start_index))
            continue;
        add_row_from_term_no_constraint(m_terms[j], j + m_terms_start_index);
    }
}

// this fills the last row of A_d and sets the basis column: -1 in the last column of the row
void fill_last_row_of_A_d(static_matrix<double, double> & A, const lar_term* ls) {
    lean_assert(A.row_count() > 0);
    lean_assert(A.column_count() > 0);
    unsigned last_row = A.row_count() - 1;
    lean_assert(A.m_rows[last_row].empty());

    for (auto & t : ls->m_coeffs) {
        lean_assert(!is_zero(t.second));
        var_index j = t.first;
        A.set(last_row, j, - t.second.get_double());
    }

    unsigned basis_j = A.column_count() - 1;
    A.set(last_row, basis_j, - 1 );
}

void update_free_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_ind) {
    mpq y_of_bound(0);
    switch (kind) {
    case LT:
        y_of_bound = -1;
    case LE:
        m_mpq_lar_core_solver.m_column_types[j] = column_type::upper_bound;
        lean_assert(m_mpq_lar_core_solver.m_column_types()[j] == column_type::upper_bound);
        lean_assert(m_mpq_lar_core_solver.m_r_upper_bounds.size() > j);
        {
            auto up = numeric_pair<mpq>(right_side, y_of_bound);
            m_mpq_lar_core_solver.m_r_upper_bounds[j] = up;
        }
        set_upper_bound_witness(j, constr_ind);
        break;
    case GT:
        y_of_bound = 1;
    case GE:
        m_mpq_lar_core_solver.m_column_types[j] = column_type::low_bound;
        lean_assert(m_mpq_lar_core_solver.m_r_upper_bounds.size() > j);
        {
            auto low = numeric_pair<mpq>(right_side, y_of_bound);
            m_mpq_lar_core_solver.m_r_low_bounds[j] = low;
        }
        set_low_bound_witness(j, constr_ind);
        break;
    case EQ:
        m_mpq_lar_core_solver.m_column_types[j] = column_type::fixed;
        m_mpq_lar_core_solver.m_r_low_bounds[j] = m_mpq_lar_core_solver.m_r_upper_bounds[j] = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
        set_upper_bound_witness(j, constr_ind);
        set_low_bound_witness(j, constr_ind);
        break;

    default:
        lean_unreachable();
                
    }
    m_columns_with_changed_bound.insert(j);
}

void update_upper_bound_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
    lean_assert(m_mpq_lar_core_solver.m_column_types()[j] == column_type::upper_bound);
    mpq y_of_bound(0);
    switch (kind) {
    case LT:
        y_of_bound = -1;
    case LE:
        {
            auto up = numeric_pair<mpq>(right_side, y_of_bound);
            if (up < m_mpq_lar_core_solver.m_r_upper_bounds()[j]) {
                m_mpq_lar_core_solver.m_r_upper_bounds[j] = up;
                set_upper_bound_witness(j, ci);
                m_columns_with_changed_bound.insert(j);
            }
        }
        break;
    case GT:
        y_of_bound = 1;
    case GE:            
        m_mpq_lar_core_solver.m_column_types[j] = column_type::boxed;
        {
            auto low = numeric_pair<mpq>(right_side, y_of_bound);
            m_mpq_lar_core_solver.m_r_low_bounds[j] = low;
            set_low_bound_witness(j, ci);
            m_columns_with_changed_bound.insert(j);
            if (low > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_status = INFEASIBLE;
                m_infeasible_column_index = j;
            } else {
                m_mpq_lar_core_solver.m_column_types[j] = m_mpq_lar_core_solver.m_r_low_bounds()[j] < m_mpq_lar_core_solver.m_r_upper_bounds()[j]? column_type::boxed : column_type::fixed;
            }                     
        }
        break;
    case EQ:
        {
            auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
            if (v > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_status = INFEASIBLE;
                set_low_bound_witness(j, ci);
                m_infeasible_column_index = j;
            } else {
                m_mpq_lar_core_solver.m_r_low_bounds[j] = m_mpq_lar_core_solver.m_r_upper_bounds[j] = v;
                m_columns_with_changed_bound.insert(j);
                set_low_bound_witness(j, ci);
                set_upper_bound_witness(j, ci);
                m_mpq_lar_core_solver.m_column_types[j] = column_type::fixed;
            }
            break;
        }
        break;

    default:
        lean_unreachable();
                
    }
}
    
void update_boxed_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
    lean_assert(m_status == INFEASIBLE || (m_mpq_lar_core_solver.m_column_types()[j] == column_type::boxed && m_mpq_lar_core_solver.m_r_low_bounds()[j] < m_mpq_lar_core_solver.m_r_upper_bounds()[j]));
    mpq y_of_bound(0);
    switch (kind) {
    case LT:
        y_of_bound = -1;
    case LE:
        {
            auto up = numeric_pair<mpq>(right_side, y_of_bound);
            if (up < m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_mpq_lar_core_solver.m_r_upper_bounds[j] = up;
                set_upper_bound_witness(j, ci);
                m_columns_with_changed_bound.insert(j);
            }

            if (up < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                m_status = INFEASIBLE;
                lean_assert(false);
                m_infeasible_column_index = j;
            } else {
                if (m_mpq_lar_core_solver.m_r_low_bounds()[j] == m_mpq_lar_core_solver.m_r_upper_bounds()[j])
                    m_mpq_lar_core_solver.m_column_types[j] = column_type::fixed;
            }                    
        }
        break;
    case GT:
        y_of_bound = 1;
    case GE:            
        {
            auto low = numeric_pair<mpq>(right_side, y_of_bound);
            if (low > m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                m_mpq_lar_core_solver.m_r_low_bounds[j] = low;
                m_columns_with_changed_bound.insert(j);
                set_low_bound_witness(j, ci);
            }
            if (low > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_status = INFEASIBLE;
                m_infeasible_column_index = j;
            } else if ( low == m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_mpq_lar_core_solver.m_column_types[j] = column_type::fixed;
            }
        }
        break;
    case EQ:
        {
            auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
            if (v < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                m_status = INFEASIBLE;
                m_infeasible_column_index = j;
                set_upper_bound_witness(j, ci);                    
            } else if (v > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_status = INFEASIBLE;
                m_infeasible_column_index = j;
                set_low_bound_witness(j, ci);                    
            } else {
                m_mpq_lar_core_solver.m_r_low_bounds[j] = m_mpq_lar_core_solver.m_r_upper_bounds[j] = v;
                set_low_bound_witness(j, ci);
                set_upper_bound_witness(j, ci);
                m_mpq_lar_core_solver.m_column_types[j] = column_type::fixed;
                m_columns_with_changed_bound.insert(j);
            }
                
            break;
        }

    default:
        lean_unreachable();
                
    }
}
void update_low_bound_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
    lean_assert(m_mpq_lar_core_solver.m_column_types()[j] == column_type::low_bound);
    mpq y_of_bound(0);
    switch (kind) {
    case LT:
        y_of_bound = -1;
    case LE:
        {
            auto up = numeric_pair<mpq>(right_side, y_of_bound);
            m_mpq_lar_core_solver.m_r_upper_bounds[j] = up;
            set_upper_bound_witness(j, ci);
            m_columns_with_changed_bound.insert(j);

            if (up < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                m_status = INFEASIBLE;
                m_infeasible_column_index = j;
            } else {
                m_mpq_lar_core_solver.m_column_types[j] = m_mpq_lar_core_solver.m_r_low_bounds()[j] < m_mpq_lar_core_solver.m_r_upper_bounds()[j]? column_type::boxed : column_type::fixed;
            }                    
        }
        break;
    case GT:
        y_of_bound = 1;
    case GE:            
        {
            auto low = numeric_pair<mpq>(right_side, y_of_bound);
            if (low > m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                m_mpq_lar_core_solver.m_r_low_bounds[j] = low;
                m_columns_with_changed_bound.insert(j);
                set_low_bound_witness(j, ci);
            }
        }
        break;
    case EQ:
        {
            auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
            if (v < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                m_status = INFEASIBLE;
                m_infeasible_column_index = j;
                set_upper_bound_witness(j, ci);                    
            } else {
                m_mpq_lar_core_solver.m_r_low_bounds[j] = m_mpq_lar_core_solver.m_r_upper_bounds[j] = v;
                set_low_bound_witness(j, ci);
                set_upper_bound_witness(j, ci);
                m_mpq_lar_core_solver.m_column_types[j] = column_type::fixed;
            }
            m_columns_with_changed_bound.insert(j);
            break;
        }

    default:
        lean_unreachable();
                
    }
}

void update_fixed_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
    lean_assert(m_status == INFEASIBLE || (m_mpq_lar_core_solver.m_column_types()[j] == column_type::fixed && m_mpq_lar_core_solver.m_r_low_bounds()[j] == m_mpq_lar_core_solver.m_r_upper_bounds()[j]));
    lean_assert(m_status == INFEASIBLE || (m_mpq_lar_core_solver.m_r_low_bounds()[j].y.is_zero() && m_mpq_lar_core_solver.m_r_upper_bounds()[j].y.is_zero()));
    auto v = numeric_pair<mpq>(right_side, mpq(0));
        
    mpq y_of_bound(0);
    switch (kind) {
    case LT:
        if (v <= m_mpq_lar_core_solver.m_r_low_bounds[j]) {
            m_status = INFEASIBLE;
            m_infeasible_column_index = j;
            set_upper_bound_witness(j, ci);
        }                   
        break;
    case LE:
        {
            if (v < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                m_status = INFEASIBLE;
                m_infeasible_column_index = j;
                set_upper_bound_witness(j, ci);
            }                   
        }
        break;
    case GT:
        {
            if (v >= m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_status = INFEASIBLE;
                m_infeasible_column_index =j;
                set_low_bound_witness(j, ci);
            }
        }
        break;
    case GE:            
        {
            if (v > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_status = INFEASIBLE;
                m_infeasible_column_index = j;
                set_low_bound_witness(j, ci);
            }
        }
        break;
    case EQ:
        {
            if (v < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                m_status = INFEASIBLE;
                m_infeasible_column_index = j;
                set_upper_bound_witness(j, ci);                    
            } else if (v > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_status = INFEASIBLE;
                m_infeasible_column_index = j;
                set_low_bound_witness(j, ci);                    
            } 
            break;
        }

    default:
        lean_unreachable();
                
    }
}
    
