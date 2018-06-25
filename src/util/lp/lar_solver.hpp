#include "util/lp/lar_solver.h"
/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner, Lev Nachmanson
*/

namespace lp {

unsigned lar_solver::constraint_count() const {
    return m_constraints.size();
}
const lar_base_constraint& lar_solver::get_constraint(unsigned ci) const {
    return *(m_constraints[ci]);
}

////////////////// methods ////////////////////////////////
static_matrix<mpq, numeric_pair<mpq>> & lar_solver::A_r() { return m_mpq_lar_core_solver.m_r_A;}
static_matrix<mpq, numeric_pair<mpq>> const & lar_solver::A_r() const { return m_mpq_lar_core_solver.m_r_A;}
static_matrix<double, double> & lar_solver::A_d() { return m_mpq_lar_core_solver.m_d_A;}
static_matrix<double, double > const & lar_solver::A_d() const { return m_mpq_lar_core_solver.m_d_A;}
    
lp_settings & lar_solver::settings() { return m_settings;}

lp_settings const & lar_solver::settings() const { return m_settings;}

void clear() {lp_assert(false); // not implemented
}


lar_solver::lar_solver() : m_status(lp_status::OPTIMAL),
                           m_infeasible_column_index(-1),
                           m_terms_start_index(1000000),
                           m_mpq_lar_core_solver(m_settings, *this),
                           m_tracker_of_x_change([&](unsigned j) {
                                   call_assignment_tracker(j);
                               }
                               ),
                           m_int_solver(nullptr)
{}
    
void lar_solver::set_track_pivoted_rows(bool v) {
    m_mpq_lar_core_solver.m_r_solver.m_pivoted_rows = v? (& m_rows_with_changed_bounds) : nullptr;
}

bool lar_solver::get_track_pivoted_rows() const {
    return m_mpq_lar_core_solver.m_r_solver.m_pivoted_rows != nullptr;
}


lar_solver::~lar_solver(){
    for (auto c : m_constraints)
        delete c;
    for (auto t : m_terms)
        delete t;
}

bool lar_solver::is_term(var_index j) const {
    return j >= m_terms_start_index && j - m_terms_start_index < m_terms.size();
}

unsigned lar_solver::adjust_term_index(unsigned j) const {
    lp_assert(is_term(j));
    return j - m_terms_start_index;
}


bool lar_solver::use_lu() const { return m_settings.simplex_strategy() == simplex_strategy_enum::lu; }
    
bool lar_solver::sizes_are_correct() const {
    lp_assert(strategy_is_undecided() || !m_mpq_lar_core_solver.need_to_presolve_with_double_solver() || A_r().column_count() == A_d().column_count());
    lp_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_solver.m_column_types.size());
    lp_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_solver.m_costs.size());
    lp_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_x.size());
    return true;
}
    
 
void lar_solver::print_implied_bound(const implied_bound& be, std::ostream & out) const {
    out << "implied bound\n";
    unsigned v = be.m_j;
    if (is_term(v)) {
        out << "it is a term number " << be.m_j << std::endl;
        print_term(*m_terms[be.m_j - m_terms_start_index],  out);
    }
    else {
        out << get_column_name(v);
    }
    out << " " << lconstraint_kind_string(be.kind()) << " "  << be.m_bound << std::endl;
    out << "end of implied bound" << std::endl;
}
    
bool lar_solver::implied_bound_is_correctly_explained(implied_bound const & be, const vector<std::pair<mpq, unsigned>> & explanation) const {
    std::unordered_map<unsigned, mpq> coeff_map;
    auto rs_of_evidence = zero_of_type<mpq>();
    unsigned n_of_G = 0, n_of_L = 0;
    bool strict = false;
    for (auto & it : explanation) {
        mpq coeff = it.first;
        constraint_index con_ind = it.second;
        const auto & constr = *m_constraints[con_ind];
        lconstraint_kind kind = coeff.is_pos() ? constr.m_kind : flip_kind(constr.m_kind);
        register_in_map(coeff_map, constr, coeff);
        if (kind == GT || kind == LT)
            strict = true;
        if (kind == GE || kind == GT) n_of_G++;
        else if (kind == LE || kind == LT) n_of_L++;
        rs_of_evidence += coeff*constr.m_right_side;
    }
    lp_assert(n_of_G == 0 || n_of_L == 0);
    lconstraint_kind kind = n_of_G ? GE : (n_of_L ? LE : EQ);
    if (strict)
        kind = static_cast<lconstraint_kind>((static_cast<int>(kind) / 2));
      
    if (!is_term(be.m_j)) {
        if (coeff_map.size() != 1)
            return false;
        auto it = coeff_map.find(be.m_j);
        if (it == coeff_map.end()) return false;
        mpq ratio = it->second;
        if (ratio < zero_of_type<mpq>()) {
            kind = static_cast<lconstraint_kind>(-kind);
        }
        rs_of_evidence /= ratio;
    } else {
        const lar_term * t = m_terms[adjust_term_index(be.m_j)];
        const auto first_coeff = *t->m_coeffs.begin();
        unsigned j = first_coeff.first;
        auto it = coeff_map.find(j);
        if (it == coeff_map.end())
            return false;
        mpq ratio = it->second / first_coeff.second;
        for (auto & p : t->m_coeffs) {
            it = coeff_map.find(p.first);
            if (it == coeff_map.end())
                return false;
            if (p.second * ratio != it->second)
                return false;
        }
        if (ratio < zero_of_type<mpq>()) {
            kind = static_cast<lconstraint_kind>(-kind);
        }
        rs_of_evidence /= ratio;
        rs_of_evidence += t->m_v * ratio;
    }

    return kind == be.kind() && rs_of_evidence == be.m_bound;
}

    
void lar_solver::analyze_new_bounds_on_row(
    unsigned row_index,
    bound_propagator & bp) {
    lp_assert(!use_tableau());
    iterator_on_pivot_row<mpq> it(m_mpq_lar_core_solver.get_pivot_row(), m_mpq_lar_core_solver.m_r_basis[row_index]);
     
    bound_analyzer_on_row ra_pos(it,
                                 zero_of_type<numeric_pair<mpq>>(),
                                 row_index,
                                 bp
                                 );
    ra_pos.analyze();
}

void lar_solver::analyze_new_bounds_on_row_tableau(
    unsigned row_index,
    bound_propagator & bp
                                                   ) {

    if (A_r().m_rows[row_index].size() > settings().max_row_length_for_bound_propagation)
        return;
    iterator_on_row<mpq> it(A_r().m_rows[row_index]);
    lp_assert(use_tableau());
    bound_analyzer_on_row::analyze_row(it,
                                       zero_of_type<numeric_pair<mpq>>(),
                                       row_index,
                                       bp
                                       );
}

    
void lar_solver::substitute_basis_var_in_terms_for_row(unsigned i) {
    // todo : create a map from term basic vars to the rows where they are used
    unsigned basis_j = m_mpq_lar_core_solver.m_r_solver.m_basis[i];
    for (unsigned k = 0; k < m_terms.size(); k++) {
        if (term_is_used_as_row(k))
            continue;
        if (!m_terms[k]->contains(basis_j)) 
            continue;
        m_terms[k]->subst(basis_j, m_mpq_lar_core_solver.m_r_solver.m_pivot_row);
    }
}
    
void lar_solver::calculate_implied_bounds_for_row(unsigned i, bound_propagator & bp) {
    if(use_tableau()) {
        analyze_new_bounds_on_row_tableau(i, bp);
    } else {
        m_mpq_lar_core_solver.calculate_pivot_row(i);
        substitute_basis_var_in_terms_for_row(i);
        analyze_new_bounds_on_row(i, bp);
    }
}

  
linear_combination_iterator<mpq> * lar_solver::create_new_iter_from_term(unsigned term_index) const {
    lp_assert(false); // not implemented
    return nullptr;
    //        new linear_combination_iterator_on_vector<mpq>(m_terms[adjust_term_index(term_index)]->coeffs_as_vector());
}

unsigned lar_solver::adjust_column_index_to_term_index(unsigned j) const {
    unsigned ext_var_or_term = m_columns_to_ext_vars_or_term_indices[j];
    return ext_var_or_term < m_terms_start_index ? j : ext_var_or_term;
}
    
void lar_solver::propagate_bounds_on_a_term(const lar_term& t, bound_propagator & bp, unsigned term_offset) {
    lp_assert(false); // not implemented
}


void lar_solver::explain_implied_bound(implied_bound & ib, bound_propagator & bp) {
    unsigned i = ib.m_row_or_term_index;
    int bound_sign = ib.m_is_low_bound? 1: -1;
    int j_sign = (ib.m_coeff_before_j_is_pos ? 1 :-1) * bound_sign;
    unsigned m_j = ib.m_j;
    if (is_term(m_j)) {
        auto it = m_ext_vars_to_columns.find(m_j);
        lp_assert(it != m_ext_vars_to_columns.end());
        m_j = it->second.ext_j();
    }
    for (auto const& r : A_r().m_rows[i]) {
        unsigned j = r.m_j;
        mpq const& a = r.get_val();
        if (j == m_j) continue;
        if (is_term(j)) {
            auto it = m_ext_vars_to_columns.find(j);
            lp_assert(it != m_ext_vars_to_columns.end());
            j = it->second.ext_j();
        } 
        int a_sign = is_pos(a)? 1: -1;
        int sign = j_sign * a_sign;
        const ul_pair & ul =  m_columns_to_ul_pairs[j];
        auto witness = sign > 0? ul.upper_bound_witness(): ul.low_bound_witness();
        lp_assert(is_valid(witness));
        bp.consume(a, witness);
    }
    // lp_assert(implied_bound_is_correctly_explained(ib, explanation));
}


bool lar_solver::term_is_used_as_row(unsigned term) const {
    lp_assert(is_term(term));
    return contains(m_ext_vars_to_columns, term);
}
    
void lar_solver::propagate_bounds_on_terms(bound_propagator & bp) {
    for (unsigned i = 0; i < m_terms.size(); i++) {
        if (term_is_used_as_row(i + m_terms_start_index))
            continue; // this term is used a left side of a constraint,
        // it was processed as a touched row if needed
        propagate_bounds_on_a_term(*m_terms[i], bp, i);
    }
}


// goes over touched rows and tries to induce bounds
void lar_solver::propagate_bounds_for_touched_rows(bound_propagator & bp) {
    if (!use_tableau())
        return; // todo: consider to remove the restriction
    
    for (unsigned i : m_rows_with_changed_bounds.m_index) {
        calculate_implied_bounds_for_row(i, bp);
    }
    m_rows_with_changed_bounds.clear();
    if (!use_tableau()) {
        propagate_bounds_on_terms(bp);
    }
}

lp_status lar_solver::get_status() const { return m_status;}

void lar_solver::set_status(lp_status s) {m_status = s;}

bool lar_solver::has_int_var() const {
    return m_mpq_lar_core_solver.m_r_solver.m_tracker_of_x_change != nullptr;
}

lp_status lar_solver::find_feasible_solution() {
    lp_assert(inf_int_set_is_correct());
    m_settings.st().m_make_feasible++;
    if (A_r().column_count() > m_settings.st().m_max_cols)
        m_settings.st().m_max_cols = A_r().column_count();
    if (A_r().row_count() > m_settings.st().m_max_rows)
        m_settings.st().m_max_rows = A_r().row_count();
    if (strategy_is_undecided())
        decide_on_strategy_and_adjust_initial_state();

    if (has_int_var()) {
        m_inf_int_set.resize(A_r().column_count());
    }
    
    m_mpq_lar_core_solver.m_r_solver.m_look_for_feasible_solution_only = true;
    auto ret = solve();
    TRACE("intinf", m_int_solver->display_inf_or_int_inf_columns(tout););
    lp_assert(inf_int_set_is_correct());
    return ret;
}
    
lp_status lar_solver::solve() {
    lp_assert(inf_int_set_is_correct());
    if (m_status == lp_status::INFEASIBLE) {
        return m_status;
    }
    solve_with_core_solver();
    if (m_status != lp_status::INFEASIBLE) {
        if (m_settings.bound_propagation())
            detect_rows_with_changed_bounds();
    }
       
    m_columns_with_changed_bound.clear();
    lp_assert(inf_int_set_is_correct());
    return m_status;
}

void lar_solver::fill_explanation_from_infeasible_column(vector<std::pair<mpq, constraint_index>> & evidence) const{

    // this is the case when the lower bound is in conflict with the upper one
    const ul_pair & ul =  m_columns_to_ul_pairs[m_infeasible_column_index];
    evidence.push_back(std::make_pair(numeric_traits<mpq>::one(), ul.upper_bound_witness()));
    evidence.push_back(std::make_pair(-numeric_traits<mpq>::one(), ul.low_bound_witness()));
}

    
unsigned lar_solver::get_total_iterations() const { return m_mpq_lar_core_solver.m_r_solver.total_iterations(); }
vector<unsigned> lar_solver::get_list_of_all_var_indices() const {
    vector<unsigned> ret;
    for (unsigned j = 0; j < m_mpq_lar_core_solver.m_r_heading.size(); j++)
        ret.push_back(j);
    return ret;
}
void lar_solver::push() {
    m_simplex_strategy = m_settings.simplex_strategy();
    m_simplex_strategy.push();
    m_columns_to_ul_pairs.push();
    m_infeasible_column_index.push();
    m_mpq_lar_core_solver.push();
    m_term_count = m_terms.size();
    m_term_count.push();
    m_constraint_count = m_constraints.size();
    m_constraint_count.push();
}

void lar_solver::clean_popped_elements(unsigned n, int_set& set) {
    vector<int> to_remove;
    for (unsigned j: set.m_index)
        if (j >= n)
            to_remove.push_back(j);
    for (unsigned j : to_remove)
        set.erase(j);
}

void lar_solver::shrink_inf_set_after_pop(unsigned n, int_set & set) {
    clean_popped_elements(n, set);
    set.resize(n);
}

    
void lar_solver::pop(unsigned k) {
    TRACE("arith_int", tout << "pop" << std::endl;);
    lp_assert(inf_int_set_is_correct());
    TRACE("lar_solver", tout << "k = " << k << std::endl;);

    int n_was = static_cast<int>(m_ext_vars_to_columns.size());
    m_infeasible_column_index.pop(k);
    unsigned n = m_columns_to_ul_pairs.peek_size(k);
    for (unsigned j = n_was; j-- > n;)
        m_ext_vars_to_columns.erase(m_columns_to_ext_vars_or_term_indices[j]);
    m_columns_to_ext_vars_or_term_indices.resize(n);
    TRACE("arith_int", tout << "pop" << std::endl;);
    if (m_settings.use_tableau()) {
        pop_tableau();
    }
    lp_assert(A_r().column_count() == n);
    m_columns_to_ul_pairs.pop(k);

    m_mpq_lar_core_solver.pop(k);
    clean_popped_elements(n, m_columns_with_changed_bound);
    clean_popped_elements(n, m_inf_int_set);
    unsigned m = A_r().row_count();
    lp_assert(inf_int_set_is_correct());
    clean_popped_elements(m, m_rows_with_changed_bounds);
    lp_assert(inf_int_set_is_correct());
    clean_inf_set_of_r_solver_after_pop();
    lp_assert(m_settings.simplex_strategy() == simplex_strategy_enum::undecided ||
              (!use_tableau()) || m_mpq_lar_core_solver.m_r_solver.reduced_costs_are_correct_tableau());
        
        
    lp_assert(ax_is_correct());
    lp_assert(m_mpq_lar_core_solver.m_r_solver.inf_set_is_correct());
    m_constraint_count.pop(k);
    for (unsigned i = m_constraint_count; i < m_constraints.size(); i++)
        delete m_constraints[i];
        
    m_constraints.resize(m_constraint_count);
    m_term_count.pop(k);
    for (unsigned i = m_term_count; i < m_terms.size(); i++) {
        delete m_terms[i];
    }
    m_terms.resize(m_term_count);
    m_simplex_strategy.pop(k);
    m_settings.simplex_strategy() = m_simplex_strategy;
    lp_assert(sizes_are_correct());
    lp_assert((!m_settings.use_tableau()) || m_mpq_lar_core_solver.m_r_solver.reduced_costs_are_correct_tableau());
    m_status = m_mpq_lar_core_solver.m_r_solver.current_x_is_feasible()? lp_status::OPTIMAL: lp_status::UNKNOWN;

}
    
vector<constraint_index> lar_solver::get_all_constraint_indices() const {
    vector<constraint_index> ret;
    constraint_index i = 0;
    while ( i < m_constraints.size())
        ret.push_back(i++);
    return ret;
}

bool lar_solver::maximize_term_on_tableau(const vector<std::pair<mpq, var_index>> & term,
                                          impq &term_max) {
    if (settings().simplex_strategy() == simplex_strategy_enum::undecided)
        decide_on_strategy_and_adjust_initial_state();
 
    m_mpq_lar_core_solver.solve();
    if (m_mpq_lar_core_solver.m_r_solver.get_status() == lp_status::UNBOUNDED)
        return false;

    term_max = 0;
    for (auto & p : term)
        term_max += p.first * m_mpq_lar_core_solver.m_r_x[p.second];

    return true;
}

bool lar_solver::costs_are_zeros_for_r_solver() const {
    for (unsigned j = 0; j < m_mpq_lar_core_solver.m_r_solver.m_costs.size(); j++) {
        lp_assert(is_zero(m_mpq_lar_core_solver.m_r_solver.m_costs[j]));
    }
    return true;
}
bool lar_solver::reduced_costs_are_zeroes_for_r_solver() const {
    for (unsigned j = 0; j < m_mpq_lar_core_solver.m_r_solver.m_d.size(); j++) {
        lp_assert(is_zero(m_mpq_lar_core_solver.m_r_solver.m_d[j]));
    }
    return true;
}
    
void lar_solver::set_costs_to_zero(const vector<std::pair<mpq, var_index>> & term) {
    auto & rslv = m_mpq_lar_core_solver.m_r_solver;
    auto & jset = m_mpq_lar_core_solver.m_r_solver.m_inf_set; // hijack this set that should be empty right now
    lp_assert(jset.m_index.size()==0);
        
    for (auto & p : term) {
        unsigned j = p.second;
        rslv.m_costs[j] = zero_of_type<mpq>();
        int i = rslv.m_basis_heading[j];
        if (i < 0)
            jset.insert(j);
        else {
            for (auto & rc : A_r().m_rows[i])
                jset.insert(rc.m_j);
        }
    }

    for (unsigned j : jset.m_index)
        rslv.m_d[j] = zero_of_type<mpq>();

    jset.clear();
        
    lp_assert(reduced_costs_are_zeroes_for_r_solver());
    lp_assert(costs_are_zeros_for_r_solver());
}

void lar_solver::prepare_costs_for_r_solver(const vector<std::pair<mpq, var_index>> & term) {
        
    auto & rslv = m_mpq_lar_core_solver.m_r_solver;
    rslv.m_using_infeas_costs = false;
    lp_assert(costs_are_zeros_for_r_solver());
    lp_assert(reduced_costs_are_zeroes_for_r_solver());
    rslv.m_costs.resize(A_r().column_count(), zero_of_type<mpq>());
    for (auto & p : term) {
        unsigned j = p.second;
        rslv.m_costs[j] = p.first;
        if (rslv.m_basis_heading[j] < 0)
            rslv.m_d[j] += p.first;
        else
            rslv.update_reduced_cost_for_basic_column_cost_change(- p.first, j);
    }
    lp_assert(rslv.reduced_costs_are_correct_tableau());
}
    
bool lar_solver::maximize_term_on_corrected_r_solver(const vector<std::pair<mpq, var_index>> & term,
                                                     impq &term_max) {
    settings().backup_costs = false;
    switch (settings().simplex_strategy()) {
    case simplex_strategy_enum::tableau_rows:
        prepare_costs_for_r_solver(term);
        settings().simplex_strategy() = simplex_strategy_enum::tableau_costs;
        {
            bool ret = maximize_term_on_tableau(term, term_max);
            settings().simplex_strategy() = simplex_strategy_enum::tableau_rows;
            set_costs_to_zero(term);
            m_mpq_lar_core_solver.m_r_solver.set_status(lp_status::OPTIMAL);
            return ret;
        }
    case simplex_strategy_enum::tableau_costs:
        prepare_costs_for_r_solver(term);
        {
            bool ret = maximize_term_on_tableau(term, term_max);
            set_costs_to_zero(term);
            m_mpq_lar_core_solver.m_r_solver.set_status(lp_status::OPTIMAL);
            return ret;
        }
            
    case simplex_strategy_enum::lu:
        lp_assert(false); // not implemented
        return false;
    default:
        lp_unreachable(); // wrong mode
    }
    return false;
}    
// starting from a given feasible state look for the maximum of the term
// return true if found and false if unbounded
bool lar_solver::maximize_term(const vector<std::pair<mpq, var_index>> & term,
                               impq &term_max) {
    lp_assert(m_mpq_lar_core_solver.m_r_solver.current_x_is_feasible());
    m_mpq_lar_core_solver.m_r_solver.m_look_for_feasible_solution_only = false;
    return maximize_term_on_corrected_r_solver(term, term_max);
}
    

    
const lar_term &  lar_solver::get_term(unsigned j) const {
    lp_assert(j >= m_terms_start_index);
    return *m_terms[j - m_terms_start_index];
}

void lar_solver::pop_core_solver_params() {
    pop_core_solver_params(1);
}

void lar_solver::pop_core_solver_params(unsigned k) {
    A_r().pop(k);
    A_d().pop(k);
}


void lar_solver::set_upper_bound_witness(var_index j, constraint_index ci) {
    ul_pair ul = m_columns_to_ul_pairs[j];
    ul.upper_bound_witness() = ci;
    m_columns_to_ul_pairs[j] = ul;
}

void lar_solver::set_low_bound_witness(var_index j, constraint_index ci) {
    ul_pair ul = m_columns_to_ul_pairs[j];
    ul.low_bound_witness() = ci;
    m_columns_to_ul_pairs[j] = ul;
}

void lar_solver::register_monoid_in_map(std::unordered_map<var_index, mpq> & coeffs, const mpq & a, unsigned j) {
    auto it = coeffs.find(j);
    if (it == coeffs.end()) {
        coeffs[j] = a;
    } else {
        it->second += a;
    }
}


void lar_solver::substitute_terms_in_linear_expression(const vector<std::pair<mpq, var_index>>& left_side_with_terms,
                                                       vector<std::pair<mpq, var_index>> &left_side, mpq & free_coeff) const {
    std::unordered_map<var_index, mpq> coeffs;
    for (auto & t : left_side_with_terms) {
        unsigned j = t.second;
        if (!is_term(j)) {
            register_monoid_in_map(coeffs, t.first, j);
        } else {
            const lar_term & term = * m_terms[adjust_term_index(t.second)];
            for (auto & p : term.coeffs()){
                register_monoid_in_map(coeffs, t.first * p.second , p.first);
            }
            free_coeff += t.first * term.m_v;
        }
    }

    for (auto & p : coeffs)
        left_side.push_back(std::make_pair(p.second, p.first));
}


void lar_solver::detect_rows_of_bound_change_column_for_nbasic_column(unsigned j) {
    if (A_r().row_count() != m_column_buffer.data_size())
        m_column_buffer.resize(A_r().row_count());
    else
        m_column_buffer.clear();
    lp_assert(m_column_buffer.size() == 0 && m_column_buffer.is_OK());
        
    m_mpq_lar_core_solver.m_r_solver.solve_Bd(j, m_column_buffer);
    for (unsigned i : m_column_buffer.m_index)
        m_rows_with_changed_bounds.insert(i);
}


    
void lar_solver::detect_rows_of_bound_change_column_for_nbasic_column_tableau(unsigned j) {
    for (auto & rc : m_mpq_lar_core_solver.m_r_A.m_columns[j])
        m_rows_with_changed_bounds.insert(rc.m_i);
}

bool lar_solver::use_tableau() const { return m_settings.use_tableau(); }

bool lar_solver::use_tableau_costs() const {
    return m_settings.simplex_strategy() == simplex_strategy_enum::tableau_costs;
}
    
void lar_solver::detect_rows_of_column_with_bound_change(unsigned j) {
    if (m_mpq_lar_core_solver.m_r_heading[j] >= 0) { // it is a basic column
        // just mark the row at touched and exit
        m_rows_with_changed_bounds.insert(m_mpq_lar_core_solver.m_r_heading[j]);
        return;
    }

    if (use_tableau())
        detect_rows_of_bound_change_column_for_nbasic_column_tableau(j);
    else
        detect_rows_of_bound_change_column_for_nbasic_column(j);
}

void lar_solver::adjust_x_of_column(unsigned j) {
    lp_assert(false);
}

bool lar_solver::row_is_correct(unsigned i) const {
    numeric_pair<mpq> r = zero_of_type<numeric_pair<mpq>>();
    for (const auto & c : A_r().m_rows[i])
        r += c.m_value * m_mpq_lar_core_solver.m_r_x[c.m_j];
    return is_zero(r);
}
    
bool lar_solver::ax_is_correct() const {
    for (unsigned i = 0; i < A_r().row_count(); i++) {
        if (!row_is_correct(i))
            return false;
    }
    return true;
}

bool lar_solver::tableau_with_costs() const {
    return m_settings.simplex_strategy() == simplex_strategy_enum::tableau_costs;
}

bool lar_solver::costs_are_used() const {
    return m_settings.simplex_strategy() != simplex_strategy_enum::tableau_rows;
}
    
void lar_solver::change_basic_columns_dependend_on_a_given_nb_column(unsigned j, const numeric_pair<mpq> & delta) {
    lp_assert(inf_int_set_is_correct());
    if (use_tableau()) {
        for (const auto & c : A_r().m_columns[j]) {
            unsigned bj = m_mpq_lar_core_solver.m_r_basis[c.m_i];
            if (tableau_with_costs()) {
                m_basic_columns_with_changed_cost.insert(bj);
            }
            m_mpq_lar_core_solver.m_r_solver.update_x_with_delta_and_track_feasibility(bj, - A_r().get_val(c) * delta);
            TRACE("change_x_del",
                  tout << "changed basis column " << bj << ", it is " <<
                  ( m_mpq_lar_core_solver.m_r_solver.column_is_feasible(bj)?  "feas":"inf") << std::endl;);
                  
        }
    } else {
        m_column_buffer.clear();
        m_column_buffer.resize(A_r().row_count());
        m_mpq_lar_core_solver.m_r_solver.solve_Bd(j, m_column_buffer);
        for (unsigned i : m_column_buffer.m_index) {
            unsigned bj = m_mpq_lar_core_solver.m_r_basis[i];
            m_mpq_lar_core_solver.m_r_solver.update_x_with_delta_and_track_feasibility(bj, -m_column_buffer[i] * delta); 
        }
    }
    lp_assert(inf_int_set_is_correct());
}

void lar_solver::update_x_and_inf_costs_for_column_with_changed_bounds(unsigned j) {
    if (m_mpq_lar_core_solver.m_r_heading[j] >= 0) {
        if (costs_are_used()) {
            bool was_infeas = m_mpq_lar_core_solver.m_r_solver.m_inf_set.contains(j);
            m_mpq_lar_core_solver.m_r_solver.track_column_feasibility(j);
            if (was_infeas != m_mpq_lar_core_solver.m_r_solver.m_inf_set.contains(j))
                m_basic_columns_with_changed_cost.insert(j);
        } else {
            m_mpq_lar_core_solver.m_r_solver.track_column_feasibility(j);
        }
    } else {
        numeric_pair<mpq> delta;
        if (m_mpq_lar_core_solver.m_r_solver.make_column_feasible(j, delta))
            change_basic_columns_dependend_on_a_given_nb_column(j, delta);
    }
}

    
void lar_solver::detect_rows_with_changed_bounds_for_column(unsigned j) {
    if (m_mpq_lar_core_solver.m_r_heading[j] >= 0) {
        m_rows_with_changed_bounds.insert(m_mpq_lar_core_solver.m_r_heading[j]);
        return;
    }

    if (use_tableau())
        detect_rows_of_bound_change_column_for_nbasic_column_tableau(j);
    else 
        detect_rows_of_bound_change_column_for_nbasic_column(j);
}
    
void lar_solver::detect_rows_with_changed_bounds() {
    for (auto j : m_columns_with_changed_bound.m_index)
        detect_rows_with_changed_bounds_for_column(j);
}

void lar_solver::update_x_and_inf_costs_for_columns_with_changed_bounds() {
    for (auto j : m_columns_with_changed_bound.m_index)
        update_x_and_inf_costs_for_column_with_changed_bounds(j);
}

void lar_solver::update_x_and_inf_costs_for_columns_with_changed_bounds_tableau() {
    for (auto j : m_columns_with_changed_bound.m_index)
        update_x_and_inf_costs_for_column_with_changed_bounds(j);

    if (tableau_with_costs()) {
        for (unsigned j : m_basic_columns_with_changed_cost.m_index)
            m_mpq_lar_core_solver.m_r_solver.update_inf_cost_for_column_tableau(j);
        lp_assert(m_mpq_lar_core_solver.m_r_solver.reduced_costs_are_correct_tableau());
    }
}

    
void lar_solver::solve_with_core_solver() {
    if (!use_tableau())
        add_last_rows_to_lu(m_mpq_lar_core_solver.m_r_solver);
    if (m_mpq_lar_core_solver.need_to_presolve_with_double_solver()) {
        add_last_rows_to_lu(m_mpq_lar_core_solver.m_d_solver);
    }
    m_mpq_lar_core_solver.prefix_r();
    if (costs_are_used()) {
        m_basic_columns_with_changed_cost.clear();
        m_basic_columns_with_changed_cost.resize(m_mpq_lar_core_solver.m_r_x.size());
    }
    if (use_tableau())
        update_x_and_inf_costs_for_columns_with_changed_bounds_tableau();
    else 
        update_x_and_inf_costs_for_columns_with_changed_bounds();
    TRACE("intinf", m_int_solver->display_inf_or_int_inf_columns(tout););
    m_mpq_lar_core_solver.solve();
    set_status(m_mpq_lar_core_solver.m_r_solver.get_status());
    lp_assert(inf_int_set_is_correct());
    lp_assert(m_status != lp_status::OPTIMAL || all_constraints_hold());
}

    
numeric_pair<mpq> lar_solver::get_basic_var_value_from_row_directly(unsigned i) {
    numeric_pair<mpq> r = zero_of_type<numeric_pair<mpq>>();
        
    unsigned bj = m_mpq_lar_core_solver.m_r_solver.m_basis[i];
    for (const auto & c: A_r().m_rows[i]) {
        if (c.m_j == bj) continue;
        const auto & x = m_mpq_lar_core_solver.m_r_x[c.m_j];
        if (!is_zero(x)) 
            r -= c.m_value * x;
    }
    return r;
}
    
numeric_pair<mpq> lar_solver::get_basic_var_value_from_row(unsigned i) {
    if (settings().use_tableau()) {
        return get_basic_var_value_from_row_directly(i);
    }
        
    numeric_pair<mpq> r = zero_of_type<numeric_pair<mpq>>();
    m_mpq_lar_core_solver.calculate_pivot_row(i);
    for (unsigned j : m_mpq_lar_core_solver.m_r_solver.m_pivot_row.m_index) {
        lp_assert(m_mpq_lar_core_solver.m_r_solver.m_basis_heading[j] < 0);
        r -= m_mpq_lar_core_solver.m_r_solver.m_pivot_row.m_data[j] * m_mpq_lar_core_solver.m_r_x[j];
    }
    return r;
}

template <typename K, typename L>
void lar_solver::add_last_rows_to_lu(lp_primal_core_solver<K,L> & s) {
    auto & f = s.m_factorization;
    if (f != nullptr) {
        auto columns_to_replace = f->get_set_of_columns_to_replace_for_add_last_rows(s.m_basis_heading);
        if (f->m_refactor_counter + columns_to_replace.size() >= 200 || f->has_dense_submatrix()) {
            delete f;
            f = nullptr;
        } else {
            f->add_last_rows_to_B(s.m_basis_heading, columns_to_replace);
        }
    }
    if (f == nullptr) {
        init_factorization(f, s.m_A, s.m_basis, m_settings);
        if (f->get_status() != LU_status::OK) {
            delete f;
            f = nullptr;
        }
    }
        
}
    
bool lar_solver::x_is_correct() const {
    if (m_mpq_lar_core_solver.m_r_x.size() != A_r().column_count()) {
        //            std::cout << "the size is off " << m_r_solver.m_x.size() << ", " << A().column_count() << std::endl;
        return false;
    }
    for (unsigned i = 0; i < A_r().row_count(); i++) {
        numeric_pair<mpq> delta =  A_r().dot_product_with_row(i, m_mpq_lar_core_solver.m_r_x);
        if (!delta.is_zero()) {
            // std::cout << "x is off (";
            // std::cout << "m_b[" << i  << "] = " << m_b[i] << " ";
            // std::cout << "left side = " << A().dot_product_with_row(i, m_r_solver.m_x) << ' ';
            // std::cout << "delta = " << delta << ' ';
            // std::cout << "iters = " << total_iterations() << ")" << std::endl;
            // std::cout << "row " << i << " is off" << std::endl;
            return false;
        }
    }
    return true;;
    
}

bool lar_solver::var_is_registered(var_index vj) const {
    if (vj >= m_terms_start_index) {
        if (vj - m_terms_start_index >= m_terms.size())
            return false;
    } else if ( vj >= A_r().column_count()) {
        return false;
    }
    return true;
}

unsigned lar_solver::constraint_stack_size() const {
    return m_constraint_count.stack_size();
}

void lar_solver::fill_last_row_of_A_r(static_matrix<mpq, numeric_pair<mpq>> & A, const lar_term * ls) {    
    lp_assert(A.row_count() > 0);
    lp_assert(A.column_count() > 0);
    unsigned last_row = A.row_count() - 1;
    lp_assert(A.m_rows[last_row].size() == 0);
    for (auto & t : ls->m_coeffs) {
        lp_assert(!is_zero(t.second));
        var_index j = t.first;
        A.set(last_row, j, - t.second);
    }
    unsigned basis_j = A.column_count() - 1;
    A.set(last_row, basis_j, mpq(1));
}

template <typename U, typename V>
void lar_solver::create_matrix_A(static_matrix<U, V> & matr) {
    lp_assert(false); // not implemented
    /*
      unsigned m = number_or_nontrivial_left_sides();
      unsigned n = m_vec_of_canonic_left_sides.size();
      if (matr.row_count() == m && matr.column_count() == n)
      return;
      matr.init_empty_matrix(m, n);
      copy_from_mpq_matrix(matr);
    */
}

template <typename U, typename V>
void lar_solver::copy_from_mpq_matrix(static_matrix<U, V> & matr) {
    matr.m_rows.resize(A_r().row_count());
    matr.m_columns.resize(A_r().column_count());
    for (unsigned i = 0; i < matr.row_count(); i++) {
        for (auto & it : A_r().m_rows[i]) {
            matr.set(i, it.m_j,  convert_struct<U, mpq>::convert(it.get_val()));
        }
    }
}


bool lar_solver::try_to_set_fixed(column_info<mpq> & ci) {
    if (ci.upper_bound_is_set() && ci.low_bound_is_set() && ci.get_upper_bound() == ci.get_low_bound() && !ci.is_fixed()) {
        ci.set_fixed_value(ci.get_upper_bound());
        return true;
    }
    return false;
}

column_type lar_solver::get_column_type(const column_info<mpq> & ci) {
    auto ret = ci.get_column_type_no_flipping();
    if (ret == column_type::boxed) { // changing boxed to fixed because of the no span
        if (ci.get_low_bound() == ci.get_upper_bound())
            ret = column_type::fixed;
    }
    return ret;
}

std::string lar_solver::get_column_name(unsigned j) const {
    if (j >= m_terms_start_index) 
        return std::string("_t") + T_to_string(j);
    if (j >= m_columns_to_ext_vars_or_term_indices.size())
        return std::string("_s") + T_to_string(j);

    return std::string("v") + T_to_string(m_columns_to_ext_vars_or_term_indices[j]);
}

bool lar_solver::all_constrained_variables_are_registered(const vector<std::pair<mpq, var_index>>& left_side) {
    for (auto it : left_side) {
        if (! var_is_registered(it.second))
            return false;
    }
    return true;
}

bool lar_solver::all_constraints_hold() const {
    if (m_settings.get_cancel_flag())
        return true;
    std::unordered_map<var_index, mpq> var_map;
    get_model_do_not_care_about_diff_vars(var_map);
    
    for (unsigned i = 0; i < m_constraints.size(); i++) {
        if (!constraint_holds(*m_constraints[i], var_map)) {
            print_constraint(i, std::cout);
            return false;
        }
    }
    return true;
}

bool lar_solver::constraint_holds(const lar_base_constraint & constr, std::unordered_map<var_index, mpq> & var_map) const {
    return true;
    mpq left_side_val = get_left_side_val(constr, var_map);
    switch (constr.m_kind) {
    case LE: return left_side_val <= constr.m_right_side;
    case LT: return left_side_val < constr.m_right_side;
    case GE: return left_side_val >= constr.m_right_side;
    case GT: return left_side_val > constr.m_right_side;
    case EQ: return left_side_val == constr.m_right_side;
    default:
        lp_unreachable();
    }
    return false; // it is unreachable
}

bool lar_solver::the_relations_are_of_same_type(const vector<std::pair<mpq, unsigned>> & evidence, lconstraint_kind & the_kind_of_sum) const {
    unsigned n_of_G = 0, n_of_L = 0;
    bool strict = false;
    for (auto & it : evidence) {
        mpq coeff = it.first;
        constraint_index con_ind = it.second;
        lconstraint_kind kind = coeff.is_pos() ?
            m_constraints[con_ind]->m_kind :
            flip_kind(m_constraints[con_ind]->m_kind);
        if (kind == GT || kind == LT)
            strict = true;
        if (kind == GE || kind == GT) n_of_G++;
        else if (kind == LE || kind == LT) n_of_L++;
    }
    the_kind_of_sum = n_of_G ? GE : (n_of_L ? LE : EQ);
    if (strict)
        the_kind_of_sum = static_cast<lconstraint_kind>((static_cast<int>(the_kind_of_sum) / 2));

    return n_of_G == 0 || n_of_L == 0;
}

void lar_solver::register_in_map(std::unordered_map<var_index, mpq> & coeffs, const lar_base_constraint & cn, const mpq & a) {
    for (auto & it : cn.get_left_side_coefficients()) {
        unsigned j = it.second;
        auto p = coeffs.find(j);
        if (p == coeffs.end())
            coeffs[j] = it.first * a;
        else {
            p->second += it.first * a;
            if (p->second.is_zero())
                coeffs.erase(p);
        }
    }
}

bool lar_solver::the_left_sides_sum_to_zero(const vector<std::pair<mpq, unsigned>> & evidence) const {
    std::unordered_map<var_index, mpq> coeff_map;
    for (auto & it : evidence) {
        mpq coeff = it.first;
        constraint_index con_ind = it.second;
        lp_assert(con_ind < m_constraints.size());
        register_in_map(coeff_map, *m_constraints[con_ind], coeff);
    }

    if (!coeff_map.empty()) {
        std::cout << "left side = ";
        vector<std::pair<mpq, var_index>> t;
        for (auto & it : coeff_map) {
            t.push_back(std::make_pair(it.second, it.first));
        }
        print_linear_combination_of_column_indices(t, std::cout);
        std::cout << std::endl;
        return false;
    }

    return true;
}

bool lar_solver::the_right_sides_do_not_sum_to_zero(const vector<std::pair<mpq, unsigned>> & evidence) {
    mpq ret = numeric_traits<mpq>::zero();
    for (auto & it : evidence) {
        mpq coeff = it.first;
        constraint_index con_ind = it.second;
        lp_assert(con_ind < m_constraints.size());
        const lar_constraint & constr = *m_constraints[con_ind];
        ret += constr.m_right_side * coeff;
    }
    return !numeric_traits<mpq>::is_zero(ret);
}

bool lar_solver::explanation_is_correct(const vector<std::pair<mpq, unsigned>>& explanation) const {
#ifdef LEAN_DEBUG
    lconstraint_kind kind;
    lp_assert(the_relations_are_of_same_type(explanation, kind));
    lp_assert(the_left_sides_sum_to_zero(explanation));
    mpq rs = sum_of_right_sides_of_explanation(explanation);
    switch (kind) {
    case LE: lp_assert(rs < zero_of_type<mpq>());
        break;
    case LT: lp_assert(rs <= zero_of_type<mpq>());
        break;
    case GE: lp_assert(rs > zero_of_type<mpq>());
        break;
    case GT: lp_assert(rs >= zero_of_type<mpq>());
        break;
    case EQ: lp_assert(rs != zero_of_type<mpq>());
        break;
    default:
        lp_assert(false);
        return false;
    }
#endif
    return true;
}

bool lar_solver::inf_explanation_is_correct() const {
#ifdef LEAN_DEBUG
    vector<std::pair<mpq, unsigned>> explanation;
    get_infeasibility_explanation(explanation);
    return explanation_is_correct(explanation);
#endif
    return true;
}

mpq lar_solver::sum_of_right_sides_of_explanation(const vector<std::pair<mpq, unsigned>> & explanation) const {
    mpq ret = numeric_traits<mpq>::zero();
    for (auto & it : explanation) {
        mpq coeff = it.first;
        constraint_index con_ind = it.second;
        lp_assert(con_ind < m_constraints.size());
        ret += (m_constraints[con_ind]->m_right_side - m_constraints[con_ind]->get_free_coeff_of_left_side()) * coeff;
    }
    return ret;
}

bool lar_solver::has_lower_bound(var_index var, constraint_index& ci, mpq& value, bool& is_strict) {

    if (var >= m_columns_to_ul_pairs.size()) {
        // TBD: bounds on terms could also be used, caller may have to track these.
        return false;
    }
    const ul_pair & ul = m_columns_to_ul_pairs[var];
    ci = ul.low_bound_witness();
    if (ci != static_cast<constraint_index>(-1)) {
        auto& p = m_mpq_lar_core_solver.m_r_low_bounds()[var];
        value = p.x;
        is_strict = p.y.is_pos();
        return true;
    }
    else {
        return false;
    }
}
    
bool lar_solver::has_upper_bound(var_index var, constraint_index& ci, mpq& value, bool& is_strict) {

    if (var >= m_columns_to_ul_pairs.size()) {
        // TBD: bounds on terms could also be used, caller may have to track these.
        return false;
    }
    const ul_pair & ul = m_columns_to_ul_pairs[var];
    ci = ul.upper_bound_witness();
    if (ci != static_cast<constraint_index>(-1)) {
        auto& p = m_mpq_lar_core_solver.m_r_upper_bounds()[var];
        value = p.x;
        is_strict = p.y.is_neg();
        return true;
    }
    else {
        return false;
    }
}

void lar_solver::get_infeasibility_explanation(vector<std::pair<mpq, constraint_index>> & explanation) const {
    explanation.clear();
    if (m_infeasible_column_index != -1) {
        fill_explanation_from_infeasible_column(explanation);
        return;
    }
    if (m_mpq_lar_core_solver.get_infeasible_sum_sign() == 0) {
        return;
    }
    // the infeasibility sign
    int inf_sign;
    auto inf_row = m_mpq_lar_core_solver.get_infeasibility_info(inf_sign);
    get_infeasibility_explanation_for_inf_sign(explanation, inf_row, inf_sign);
    lp_assert(explanation_is_correct(explanation));
}



void lar_solver::get_infeasibility_explanation_for_inf_sign(
    vector<std::pair<mpq, constraint_index>> & explanation,
    const vector<std::pair<mpq, unsigned>> & inf_row,
    int inf_sign) const {

    for (auto & it : inf_row) {
        mpq coeff = it.first;
        unsigned j = it.second;

        int adj_sign = coeff.is_pos() ? inf_sign : -inf_sign;
        const ul_pair & ul = m_columns_to_ul_pairs[j];

        constraint_index bound_constr_i = adj_sign < 0 ? ul.upper_bound_witness() : ul.low_bound_witness();
        lp_assert(bound_constr_i < m_constraints.size());
        explanation.push_back(std::make_pair(coeff, bound_constr_i));
    } 
}

void lar_solver::get_model(std::unordered_map<var_index, mpq> & variable_values) const {
    mpq delta = mpq(1, 2); // start from 0.5 to have less clashes
    lp_assert(m_status == lp_status::OPTIMAL);
    unsigned i;
    do {
        // different pairs have to produce different singleton values
        std::unordered_set<impq> set_of_different_pairs; 
        std::unordered_set<mpq> set_of_different_singles;
        delta = m_mpq_lar_core_solver.find_delta_for_strict_bounds(delta);
        for (i = 0; i < m_mpq_lar_core_solver.m_r_x.size(); i++ ) {
            const numeric_pair<mpq> & rp = m_mpq_lar_core_solver.m_r_x[i];
            set_of_different_pairs.insert(rp);
            mpq x = rp.x + delta * rp.y;
            set_of_different_singles.insert(x);
            if (set_of_different_pairs.size()
                != set_of_different_singles.size()) {
                delta /= mpq(2);
                break;
            }
                    
            variable_values[i] = x;
        }
    } while (i != m_mpq_lar_core_solver.m_r_x.size());
}

void lar_solver::get_model_do_not_care_about_diff_vars(std::unordered_map<var_index, mpq> & variable_values) const {
    mpq delta = mpq(1);
    delta = m_mpq_lar_core_solver.find_delta_for_strict_bounds(delta);
    for (unsigned i = 0; i < m_mpq_lar_core_solver.m_r_x.size(); i++ ) {
        const impq & rp = m_mpq_lar_core_solver.m_r_x[i];
        variable_values[i] = rp.x + delta * rp.y;
    }
}


std::string lar_solver::get_variable_name(var_index vi) const {
    return get_column_name(vi);
}

// ********** print region start
void lar_solver::print_constraint(constraint_index ci, std::ostream & out) const {
    if (ci >= m_constraints.size()) {
        out << "constraint " << T_to_string(ci) << " is not found";
        out << std::endl;
        return;
    }

    print_constraint(m_constraints[ci], out);
}

void lar_solver::print_constraints(std::ostream& out) const  {
    for (auto c : m_constraints) {
        print_constraint(c, out);
    }
}

void lar_solver::print_terms(std::ostream& out) const  {
    for (auto it : m_terms) {
        print_term(*it, out);
        out << "\n";
    }
}

void lar_solver::print_left_side_of_constraint(const lar_base_constraint * c, std::ostream & out) const {
    print_linear_combination_of_column_indices(c->get_left_side_coefficients(), out);
    mpq free_coeff = c->get_free_coeff_of_left_side();
    if (!is_zero(free_coeff))
        out << " + " << free_coeff;
        
}

void lar_solver::print_term(lar_term const& term, std::ostream & out) const {
    if (!numeric_traits<mpq>::is_zero(term.m_v)) {
        out << term.m_v << " + ";
    }
    print_linear_combination_of_column_indices(term.coeffs_as_vector(), out);
}

void lar_solver::print_term_as_indices(lar_term const& term, std::ostream & out) const {
    if (!numeric_traits<mpq>::is_zero(term.m_v)) {
        out << term.m_v << " + ";
    }
    print_linear_combination_of_column_indices_only(term.coeffs_as_vector(), out);
}

mpq lar_solver::get_left_side_val(const lar_base_constraint &  cns, const std::unordered_map<var_index, mpq> & var_map) const {
    mpq ret = cns.get_free_coeff_of_left_side();
    for (auto & it : cns.get_left_side_coefficients()) {
        var_index j = it.second;
        auto vi = var_map.find(j);
        lp_assert(vi != var_map.end());
        ret += it.first * vi->second;
    }
    return ret;
}

void lar_solver::print_constraint(const lar_base_constraint * c, std::ostream & out) const {
    print_left_side_of_constraint(c, out);
    out << " " << lconstraint_kind_string(c->m_kind) << " " << c->m_right_side << std::endl;
}

void lar_solver::fill_var_set_for_random_update(unsigned sz, var_index const * vars, vector<unsigned>& column_list) {
    for (unsigned i = 0; i < sz; i++) {        
        var_index var = vars[i];
        if (var >= m_terms_start_index) { // handle the term
            for (auto & it : m_terms[var - m_terms_start_index]->m_coeffs) {
                column_list.push_back(it.first);
            }
        } else {
            column_list.push_back(var);
        }
    }
}

void lar_solver::random_update(unsigned sz, var_index const * vars) {
    vector<unsigned> column_list;
    fill_var_set_for_random_update(sz, vars, column_list);
    random_updater ru(*this, column_list);
    ru.update();
    lp_assert(inf_int_set_is_correct());
}


void lar_solver::pivot_fixed_vars_from_basis() {
    m_mpq_lar_core_solver.m_r_solver.pivot_fixed_vars_from_basis();
}

void lar_solver::pop() {
    pop(1);
}

bool lar_solver::column_represents_row_in_tableau(unsigned j) {
    return m_columns_to_ul_pairs()[j].m_i != static_cast<row_index>(-1);
}

void lar_solver::make_sure_that_the_bottom_right_elem_not_zero_in_tableau(unsigned i, unsigned j) {
    // i, j - is the indices of the bottom-right element of the tableau
    lp_assert(A_r().row_count() == i + 1 && A_r().column_count() == j + 1);
    auto & last_column = A_r().m_columns[j];
    int non_zero_column_cell_index = -1;
    for (unsigned k = last_column.size(); k-- > 0;){
        auto & cc = last_column[k];
        if (cc.m_i == i)
            return;
        non_zero_column_cell_index = k;
    }

    lp_assert(non_zero_column_cell_index != -1);
    lp_assert(static_cast<unsigned>(non_zero_column_cell_index) != i);
    m_mpq_lar_core_solver.m_r_solver.transpose_rows_tableau(last_column[non_zero_column_cell_index].m_i, i);
}

void lar_solver::remove_last_row_and_column_from_tableau(unsigned j) {
    lp_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_solver.m_costs.size());
    auto & slv = m_mpq_lar_core_solver.m_r_solver;
    unsigned i = A_r().row_count() - 1; //last row index
    make_sure_that_the_bottom_right_elem_not_zero_in_tableau(i, j);
    if (slv.m_basis_heading[j] < 0) {
        slv.pivot_column_tableau(j, i);
    }

    auto & last_row = A_r().m_rows[i];
    mpq &cost_j = m_mpq_lar_core_solver.m_r_solver.m_costs[j];
    bool cost_is_nz = !is_zero(cost_j);
    for (unsigned k = last_row.size(); k-- > 0;) {
        auto &rc = last_row[k];
        if (cost_is_nz) {
            m_mpq_lar_core_solver.m_r_solver.m_d[rc.m_j] += cost_j*rc.get_val();
        }
            
        A_r().remove_element(last_row, rc);
    }
    lp_assert(last_row.size() == 0);
    lp_assert(A_r().m_columns[j].size() == 0);
    A_r().m_rows.pop_back();
    A_r().m_columns.pop_back();
    slv.m_b.pop_back();
}

void lar_solver::remove_last_column_from_A() {
    // the last column has to be empty
    lp_assert(A_r().m_columns.back().size() == 0);
    A_r().m_columns.pop_back();
}

void lar_solver::remove_last_column_from_basis_tableau(unsigned j) {
    auto& rslv = m_mpq_lar_core_solver.m_r_solver;
    int i = rslv.m_basis_heading[j];
    if (i >= 0) { // j is a basic var
        int last_pos = static_cast<int>(rslv.m_basis.size()) - 1;
        lp_assert(last_pos >= 0);
        if (i != last_pos) {
            unsigned j_at_last_pos = rslv.m_basis[last_pos];
            rslv.m_basis[i] = j_at_last_pos;
            rslv.m_basis_heading[j_at_last_pos] = i;
        }
        rslv.m_basis.pop_back(); // remove j from the basis
    } else {
        int last_pos = static_cast<int>(rslv.m_nbasis.size()) - 1;
        lp_assert(last_pos >= 0);
        i = - 1 - i;
        if (i != last_pos) {
            unsigned j_at_last_pos = rslv.m_nbasis[last_pos];
            rslv.m_nbasis[i] = j_at_last_pos;
            rslv.m_basis_heading[j_at_last_pos] = - i - 1;
        }
        rslv.m_nbasis.pop_back(); // remove j from the basis
    }
    rslv.m_basis_heading.pop_back();
    lp_assert(rslv.m_basis.size() == A_r().row_count());
    lp_assert(rslv.basis_heading_is_correct());
}

void lar_solver::remove_last_column_from_tableau() {
    auto& rslv = m_mpq_lar_core_solver.m_r_solver;
    unsigned j = A_r().column_count() - 1;
    lp_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_solver.m_costs.size());
    if (column_represents_row_in_tableau(j)) {
        remove_last_row_and_column_from_tableau(j);
        if (rslv.m_basis_heading[j] < 0)
            rslv.change_basis_unconditionally(j, rslv.m_basis[A_r().row_count()]); // A_r().row_count() is the index of the last row in the basis still
    }
    else {
        remove_last_column_from_A();
    }
    rslv.m_x.pop_back();
    rslv.m_d.pop_back();
    rslv.m_costs.pop_back();

    remove_last_column_from_basis_tableau(j);
    lp_assert(m_mpq_lar_core_solver.r_basis_is_OK());
    lp_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_solver.m_costs.size());
}

void lar_solver::pop_tableau() {
    lp_assert(m_mpq_lar_core_solver.m_r_solver.m_costs.size() == A_r().column_count());

    lp_assert(m_mpq_lar_core_solver.m_r_solver.m_basis.size() == A_r().row_count());
    lp_assert(m_mpq_lar_core_solver.m_r_solver.basis_heading_is_correct());
    // We remove last variables starting from m_column_names.size() to m_vec_of_canonic_left_sides.size().    
    // At this moment m_column_names is already popped
    while (A_r().column_count() > m_columns_to_ext_vars_or_term_indices.size())
        remove_last_column_from_tableau();
    lp_assert(m_mpq_lar_core_solver.m_r_solver.m_costs.size() == A_r().column_count());
    lp_assert(m_mpq_lar_core_solver.m_r_solver.m_basis.size() == A_r().row_count());
    lp_assert(m_mpq_lar_core_solver.m_r_solver.basis_heading_is_correct());
}

void lar_solver::clean_inf_set_of_r_solver_after_pop() {
    lp_assert(inf_int_set_is_correct());
    vector<unsigned> became_feas;
    clean_popped_elements(A_r().column_count(), m_mpq_lar_core_solver.m_r_solver.m_inf_set);
    std::unordered_set<unsigned> basic_columns_with_changed_cost;
    auto inf_index_copy = m_mpq_lar_core_solver.m_r_solver.m_inf_set.m_index;
    for (auto j: inf_index_copy) {
        if (m_mpq_lar_core_solver.m_r_heading[j] >= 0) {
            continue;
        }
        // some basic columns might become non-basic - these columns need to be made feasible
        numeric_pair<mpq> delta;
        if (m_mpq_lar_core_solver.m_r_solver.make_column_feasible(j, delta)) {
            
            change_basic_columns_dependend_on_a_given_nb_column(j, delta);
        }
        became_feas.push_back(j);
    }

    for (unsigned j : became_feas) {
        lp_assert(m_mpq_lar_core_solver.m_r_solver.m_basis_heading[j] < 0);
        m_mpq_lar_core_solver.m_r_solver.m_d[j] -= m_mpq_lar_core_solver.m_r_solver.m_costs[j];
        m_mpq_lar_core_solver.m_r_solver.m_costs[j] = zero_of_type<mpq>();
        m_mpq_lar_core_solver.m_r_solver.m_inf_set.erase(j);
    }
    became_feas.clear();
    for (unsigned j : m_mpq_lar_core_solver.m_r_solver.m_inf_set.m_index) {
        lp_assert(m_mpq_lar_core_solver.m_r_heading[j] >= 0);
        if (m_mpq_lar_core_solver.m_r_solver.column_is_feasible(j))
            became_feas.push_back(j);
    }
    for (unsigned j : became_feas)
        m_mpq_lar_core_solver.m_r_solver.m_inf_set.erase(j);
    
    
    if (use_tableau_costs()) {
        for (unsigned j : became_feas)
            m_mpq_lar_core_solver.m_r_solver.update_inf_cost_for_column_tableau(j);
        for (unsigned j : basic_columns_with_changed_cost)
            m_mpq_lar_core_solver.m_r_solver.update_inf_cost_for_column_tableau(j);
        lp_assert(m_mpq_lar_core_solver.m_r_solver.reduced_costs_are_correct_tableau());
    }
}

void lar_solver::shrink_explanation_to_minimum(vector<std::pair<mpq, constraint_index>> & explanation) const {
    // implementing quickXplain
    quick_xplain::run(explanation, *this);
    lp_assert(this->explanation_is_correct(explanation));
}

bool lar_solver::model_is_int_feasible() const {
    unsigned n = A_r().column_count();
    for (unsigned j = 0; j < n; j++) {
        if (column_is_int(j) && !column_value_is_integer(j))
            return false;
    }
    return true;
}

bool lar_solver::term_is_int(const lar_term * t) const {
    for (auto const & p :  t->m_coeffs)
        if (! (column_is_int(p.first)  && p.second.is_int()))
            return false;
    return t->m_v.is_int();
}

bool lar_solver::var_is_int(var_index v) const {
    if (is_term(v)) {
        lar_term const& t = get_term(v);
        return term_is_int(&t);
    }
    else {
        return column_is_int(v);
    }
}

bool lar_solver::column_is_int(unsigned j) const {
    unsigned ext_var = m_columns_to_ext_vars_or_term_indices[j];
    lp_assert(contains(m_ext_vars_to_columns, ext_var));
    return m_ext_vars_to_columns.find(ext_var)->second.is_integer();
}

bool lar_solver::column_is_fixed(unsigned j) const {
    return m_mpq_lar_core_solver.column_is_fixed(j);
}

    
bool lar_solver::ext_var_is_int(var_index ext_var) const {
    auto it = m_ext_vars_to_columns.find(ext_var);
    lp_assert(it != m_ext_vars_to_columns.end());
    return it == m_ext_vars_to_columns.end() || it->second.is_integer();
}

// below is the initialization functionality of lar_solver

bool lar_solver::strategy_is_undecided() const {
    return m_settings.simplex_strategy() == simplex_strategy_enum::undecided;
}

var_index lar_solver::add_var(unsigned ext_j, bool is_int) {
    TRACE("add_var", tout << "adding var " << ext_j << (is_int? " int" : " nonint") << std::endl;);
    var_index i;
    lp_assert(ext_j < m_terms_start_index);

    if (ext_j >= m_terms_start_index)
        throw 0; // todo : what is the right way to exit?
    auto it = m_ext_vars_to_columns.find(ext_j);
    if (it != m_ext_vars_to_columns.end()) {
        return it->second.ext_j();
    }
    lp_assert(m_columns_to_ul_pairs.size() == A_r().column_count());
    i = A_r().column_count();
    m_columns_to_ul_pairs.push_back(ul_pair(static_cast<unsigned>(-1)));
    add_non_basic_var_to_core_fields(ext_j, is_int);
    lp_assert(sizes_are_correct());
    if (is_int) {
        m_mpq_lar_core_solver.m_r_solver.set_tracker_of_x(& m_tracker_of_x_change);
    }
    lp_assert(inf_int_set_is_correct());
    return i;
}

void lar_solver::register_new_ext_var_index(unsigned ext_v, bool is_int) {
    lp_assert(!contains(m_ext_vars_to_columns, ext_v));
    unsigned j = static_cast<unsigned>(m_ext_vars_to_columns.size());
    m_ext_vars_to_columns.insert(std::make_pair(ext_v, ext_var_info(j, is_int)));
    lp_assert(m_columns_to_ext_vars_or_term_indices.size() == j);
    m_columns_to_ext_vars_or_term_indices.push_back(ext_v);
}

void lar_solver::add_non_basic_var_to_core_fields(unsigned ext_j, bool is_int) {
    register_new_ext_var_index(ext_j, is_int);
    m_mpq_lar_core_solver.m_column_types.push_back(column_type::free_column);
    m_columns_with_changed_bound.increase_size_by_one();
    m_inf_int_set.increase_size_by_one();
    add_new_var_to_core_fields_for_mpq(false);
    if (use_lu())
        add_new_var_to_core_fields_for_doubles(false);
}

void lar_solver::add_new_var_to_core_fields_for_doubles(bool register_in_basis) {
    unsigned j = A_d().column_count();
    A_d().add_column();
    lp_assert(m_mpq_lar_core_solver.m_d_x.size() == j);
    //        lp_assert(m_mpq_lar_core_solver.m_d_low_bounds.size() == j && m_mpq_lar_core_solver.m_d_upper_bounds.size() == j);  // restore later
    m_mpq_lar_core_solver.m_d_x.resize(j + 1);
    m_mpq_lar_core_solver.m_d_low_bounds.resize(j + 1);
    m_mpq_lar_core_solver.m_d_upper_bounds.resize(j + 1);
    lp_assert(m_mpq_lar_core_solver.m_d_heading.size() == j); // as A().column_count() on the entry to the method
    if (register_in_basis) {
        A_d().add_row();
        m_mpq_lar_core_solver.m_d_heading.push_back(m_mpq_lar_core_solver.m_d_basis.size());
        m_mpq_lar_core_solver.m_d_basis.push_back(j);
    }
    else {
        m_mpq_lar_core_solver.m_d_heading.push_back(-static_cast<int>(m_mpq_lar_core_solver.m_d_nbasis.size()) - 1);
        m_mpq_lar_core_solver.m_d_nbasis.push_back(j);
    }
}

void lar_solver::add_new_var_to_core_fields_for_mpq(bool register_in_basis) {
    unsigned j = A_r().column_count();
    A_r().add_column();
    lp_assert(m_mpq_lar_core_solver.m_r_x.size() == j);
    //        lp_assert(m_mpq_lar_core_solver.m_r_low_bounds.size() == j && m_mpq_lar_core_solver.m_r_upper_bounds.size() == j);  // restore later
    m_mpq_lar_core_solver.m_r_x.resize(j + 1);
    m_mpq_lar_core_solver.m_r_low_bounds.increase_size_by_one();
    m_mpq_lar_core_solver.m_r_upper_bounds.increase_size_by_one();
    m_mpq_lar_core_solver.m_r_solver.m_inf_set.increase_size_by_one();
    m_mpq_lar_core_solver.m_r_solver.m_costs.resize(j + 1);
    m_mpq_lar_core_solver.m_r_solver.m_d.resize(j + 1);
    lp_assert(m_mpq_lar_core_solver.m_r_heading.size() == j); // as A().column_count() on the entry to the method
    if (register_in_basis) {
        A_r().add_row();
        m_mpq_lar_core_solver.m_r_heading.push_back(m_mpq_lar_core_solver.m_r_basis.size());
        m_mpq_lar_core_solver.m_r_basis.push_back(j);
        if (m_settings.bound_propagation())
            m_rows_with_changed_bounds.insert(A_r().row_count() - 1);
    }
    else {
        m_mpq_lar_core_solver.m_r_heading.push_back(-static_cast<int>(m_mpq_lar_core_solver.m_r_nbasis.size()) - 1);
        m_mpq_lar_core_solver.m_r_nbasis.push_back(j);
    }
}


var_index lar_solver::add_term_undecided(const vector<std::pair<mpq, var_index>> & coeffs,
                                         const mpq &m_v) {
    m_terms.push_back(new lar_term(coeffs, m_v));
    return m_terms_start_index + m_terms.size() - 1;
}

// terms
var_index lar_solver::add_term(const vector<std::pair<mpq, var_index>> & coeffs,
                               const mpq &m_v) {
    if (strategy_is_undecided())
        return add_term_undecided(coeffs, m_v);

    m_terms.push_back(new lar_term(coeffs, m_v));
    unsigned adjusted_term_index = m_terms.size() - 1;
    var_index ret = m_terms_start_index + adjusted_term_index;
    if (use_tableau() && !coeffs.empty()) {
        add_row_from_term_no_constraint(m_terms.back(), ret);
        if (m_settings.bound_propagation())
            m_rows_with_changed_bounds.insert(A_r().row_count() - 1);
    }
    lp_assert(m_ext_vars_to_columns.size() == A_r().column_count());
    return ret;
}

void lar_solver::add_row_from_term_no_constraint(const lar_term * term, unsigned term_ext_index) {
    register_new_ext_var_index(term_ext_index, term_is_int(term));
    // j will be a new variable
    unsigned j = A_r().column_count();
    ul_pair ul(j);
    m_columns_to_ul_pairs.push_back(ul);
    add_basic_var_to_core_fields();
    if (use_tableau()) {
        auto it = iterator_on_term_with_basis_var(*term, j);
        A_r().fill_last_row_with_pivoting(it,
                                          m_mpq_lar_core_solver.m_r_solver.m_basis_heading);
        m_mpq_lar_core_solver.m_r_solver.m_b.resize(A_r().column_count(), zero_of_type<mpq>());
    }
    else {
        fill_last_row_of_A_r(A_r(), term);
    }
    m_mpq_lar_core_solver.m_r_solver.update_x_and_call_tracker(j, get_basic_var_value_from_row_directly(A_r().row_count() - 1));
    if (use_lu())
        fill_last_row_of_A_d(A_d(), term);
    lp_assert(inf_int_set_is_correct());
}

void lar_solver::add_basic_var_to_core_fields() {
    bool use_lu = m_mpq_lar_core_solver.need_to_presolve_with_double_solver();
    lp_assert(!use_lu || A_r().column_count() == A_d().column_count());
    m_mpq_lar_core_solver.m_column_types.push_back(column_type::free_column);
    m_columns_with_changed_bound.increase_size_by_one();
    m_rows_with_changed_bounds.increase_size_by_one();
    m_inf_int_set.increase_size_by_one();
    add_new_var_to_core_fields_for_mpq(true);
    if (use_lu)
        add_new_var_to_core_fields_for_doubles(true);
}

bool lar_solver::bound_is_integer_if_needed(unsigned j, const mpq & right_side) const {
    if (!column_is_int(j))
        return true;
    return right_side.is_int();
}

constraint_index lar_solver::add_var_bound(var_index j, lconstraint_kind kind, const mpq & right_side) {
    TRACE("lar_solver", tout << "j = " << j << std::endl;);
    constraint_index ci = m_constraints.size();
    if (!is_term(j)) { // j is a var
        lp_assert(bound_is_integer_if_needed(j, right_side));
        auto vc = new lar_var_constraint(j, kind, right_side);
        m_constraints.push_back(vc);
        update_column_type_and_bound(j, kind, right_side, ci);
    }
    else {
        add_var_bound_on_constraint_for_term(j, kind, right_side, ci);
    }
    lp_assert(sizes_are_correct());
    lp_assert(inf_int_set_is_correct());
    return ci;
}

void lar_solver::update_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index) {
    switch (m_mpq_lar_core_solver.m_column_types[j]) {
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
        lp_assert(false); // cannot be here
    }
}

void lar_solver::add_var_bound_on_constraint_for_term(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
    lp_assert(is_term(j));
    unsigned adjusted_term_index = adjust_term_index(j);
    lp_assert(!term_is_int(m_terms[adjusted_term_index]) || right_side.is_int());
    auto it = m_ext_vars_to_columns.find(j);
    if (it != m_ext_vars_to_columns.end()) {
        unsigned term_j = it->second.ext_j();
        mpq rs = right_side - m_terms[adjusted_term_index]->m_v;
        m_constraints.push_back(new lar_term_constraint(m_terms[adjusted_term_index], kind, right_side));
        update_column_type_and_bound(term_j, kind, rs, ci);
    }
    else {
        add_constraint_from_term_and_create_new_column_row(j, m_terms[adjusted_term_index], kind, right_side);
    }
}

constraint_index lar_solver::add_constraint(const vector<std::pair<mpq, var_index>>& left_side_with_terms, lconstraint_kind kind_par, const mpq& right_side_parm) {
    vector<std::pair<mpq, var_index>> left_side;
    mpq rs = -right_side_parm;
    substitute_terms_in_linear_expression(left_side_with_terms, left_side, rs);
    unsigned term_index = add_term(left_side, zero_of_type<mpq>());
    constraint_index ci = m_constraints.size();
    add_var_bound_on_constraint_for_term(term_index, kind_par, -rs, ci);
    return ci;
}

void lar_solver::add_constraint_from_term_and_create_new_column_row(unsigned term_j, const lar_term* term,
                                                                    lconstraint_kind kind, const mpq & right_side) {

    add_row_from_term_no_constraint(term, term_j);
    unsigned j = A_r().column_count() - 1;
    update_column_type_and_bound(j, kind, right_side - term->m_v, m_constraints.size());
    m_constraints.push_back(new lar_term_constraint(term, kind, right_side));
    lp_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_solver.m_costs.size());
}

void lar_solver::decide_on_strategy_and_adjust_initial_state() {
    lp_assert(strategy_is_undecided());
    if (m_columns_to_ul_pairs.size() > m_settings.column_number_threshold_for_using_lu_in_lar_solver) {
        m_settings.simplex_strategy() = simplex_strategy_enum::lu;
    }
    else {
        m_settings.simplex_strategy() = simplex_strategy_enum::tableau_rows; // todo: when to switch to tableau_costs?
    }
    adjust_initial_state();
}

void lar_solver::adjust_initial_state() {
    switch (m_settings.simplex_strategy()) {
    case simplex_strategy_enum::lu:
        adjust_initial_state_for_lu();
        break;
    case simplex_strategy_enum::tableau_rows:
        adjust_initial_state_for_tableau_rows();
        break;
    case simplex_strategy_enum::tableau_costs:
        lp_assert(false); // not implemented
    case simplex_strategy_enum::undecided:
        adjust_initial_state_for_tableau_rows();
        break;
    }
}

void lar_solver::adjust_initial_state_for_lu() {
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
      lp_assert(m_mpq_lar_core_solver.m_d_x.size() == j);
      //        lp_assert(m_mpq_lar_core_solver.m_d_low_bounds.size() == j && m_mpq_lar_core_solver.m_d_upper_bounds.size() == j);  // restore later
      m_mpq_lar_core_solver.m_d_x.resize(j + 1 );
      m_mpq_lar_core_solver.m_d_low_bounds.resize(j + 1);
      m_mpq_lar_core_solver.m_d_upper_bounds.resize(j + 1);
      lp_assert(m_mpq_lar_core_solver.m_d_heading.size() == j); // as A().column_count() on the entry to the method
      if (register_in_basis) {
      A_d().add_row();
      m_mpq_lar_core_solver.m_d_heading.push_back(m_mpq_lar_core_solver.m_d_basis.size());
      m_mpq_lar_core_solver.m_d_basis.push_back(j);
      }else {
      m_mpq_lar_core_solver.m_d_heading.push_back(- static_cast<int>(m_mpq_lar_core_solver.m_d_nbasis.size()) - 1);
      m_mpq_lar_core_solver.m_d_nbasis.push_back(j);
      }*/
}

void lar_solver::adjust_initial_state_for_tableau_rows() {
    for (unsigned j = 0; j < m_terms.size(); j++) {
        if (contains(m_ext_vars_to_columns, j + m_terms_start_index))
            continue;
        add_row_from_term_no_constraint(m_terms[j], j + m_terms_start_index);
    }
}

// this fills the last row of A_d and sets the basis column: -1 in the last column of the row
void lar_solver::fill_last_row_of_A_d(static_matrix<double, double> & A, const lar_term* ls) {
    lp_assert(A.row_count() > 0);
    lp_assert(A.column_count() > 0);
    unsigned last_row = A.row_count() - 1;
    lp_assert(A.m_rows[last_row].empty());

    for (auto & t : ls->m_coeffs) {
        lp_assert(!is_zero(t.second));
        var_index j = t.first;
        A.set(last_row, j, -t.second.get_double());
    }

    unsigned basis_j = A.column_count() - 1;
    A.set(last_row, basis_j, -1);
}

void lar_solver::update_free_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_ind) {
    mpq y_of_bound(0);
    switch (kind) {
    case LT:
        y_of_bound = -1;
    case LE:
        m_mpq_lar_core_solver.m_column_types[j] = column_type::upper_bound;
        lp_assert(m_mpq_lar_core_solver.m_column_types()[j] == column_type::upper_bound);
        lp_assert(m_mpq_lar_core_solver.m_r_upper_bounds.size() > j);
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
        lp_assert(m_mpq_lar_core_solver.m_r_upper_bounds.size() > j);
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
        lp_unreachable();

    }
    m_columns_with_changed_bound.insert(j);
}

void lar_solver::update_upper_bound_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
    lp_assert(m_mpq_lar_core_solver.m_column_types()[j] == column_type::upper_bound);
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
                m_status = lp_status::INFEASIBLE;
                m_infeasible_column_index = j;
            }
            else {
                m_mpq_lar_core_solver.m_column_types[j] = m_mpq_lar_core_solver.m_r_low_bounds()[j] < m_mpq_lar_core_solver.m_r_upper_bounds()[j] ? column_type::boxed : column_type::fixed;
            }
        }
        break;
    case EQ:
	{
            auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
            if (v > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_status = lp_status::INFEASIBLE;
                set_low_bound_witness(j, ci);
                m_infeasible_column_index = j;
            }
            else {
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
        lp_unreachable();

    }
}

void lar_solver::update_boxed_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
    lp_assert(m_status == lp_status::INFEASIBLE || (m_mpq_lar_core_solver.m_column_types()[j] == column_type::boxed && m_mpq_lar_core_solver.m_r_low_bounds()[j] < m_mpq_lar_core_solver.m_r_upper_bounds()[j]));
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
                m_status = lp_status::INFEASIBLE;
                lp_assert(false);
                m_infeasible_column_index = j;
            }
            else {
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
                m_status = lp_status::INFEASIBLE;
                m_infeasible_column_index = j;
            }
            else if (low == m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_mpq_lar_core_solver.m_column_types[j] = column_type::fixed;
            }
	}
	break;
    case EQ:
	{
            auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
            if (v < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                m_status = lp_status::INFEASIBLE;
                m_infeasible_column_index = j;
                set_upper_bound_witness(j, ci);
            }
            else if (v > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_status = lp_status::INFEASIBLE;
                m_infeasible_column_index = j;
                set_low_bound_witness(j, ci);
            }
            else {
                m_mpq_lar_core_solver.m_r_low_bounds[j] = m_mpq_lar_core_solver.m_r_upper_bounds[j] = v;
                set_low_bound_witness(j, ci);
                set_upper_bound_witness(j, ci);
                m_mpq_lar_core_solver.m_column_types[j] = column_type::fixed;
                m_columns_with_changed_bound.insert(j);
            }

            break;
	}

    default:
        lp_unreachable();

    }
}
void lar_solver::update_low_bound_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
    lp_assert(m_mpq_lar_core_solver.m_column_types()[j] == column_type::low_bound);
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
                m_status = lp_status::INFEASIBLE;
                m_infeasible_column_index = j;
            }
            else {
                m_mpq_lar_core_solver.m_column_types[j] = m_mpq_lar_core_solver.m_r_low_bounds()[j] < m_mpq_lar_core_solver.m_r_upper_bounds()[j] ? column_type::boxed : column_type::fixed;
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
                m_status = lp_status::INFEASIBLE;
                m_infeasible_column_index = j;
                set_upper_bound_witness(j, ci);
            }
            else {
                m_mpq_lar_core_solver.m_r_low_bounds[j] = m_mpq_lar_core_solver.m_r_upper_bounds[j] = v;
                set_low_bound_witness(j, ci);
                set_upper_bound_witness(j, ci);
                m_mpq_lar_core_solver.m_column_types[j] = column_type::fixed;
            }
            m_columns_with_changed_bound.insert(j);
            break;
	}

    default:
        lp_unreachable();

    }
}

void lar_solver::update_fixed_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index ci) {
    lp_assert(m_status == lp_status::INFEASIBLE || (m_mpq_lar_core_solver.m_column_types()[j] == column_type::fixed && m_mpq_lar_core_solver.m_r_low_bounds()[j] == m_mpq_lar_core_solver.m_r_upper_bounds()[j]));
    lp_assert(m_status == lp_status::INFEASIBLE || (m_mpq_lar_core_solver.m_r_low_bounds()[j].y.is_zero() && m_mpq_lar_core_solver.m_r_upper_bounds()[j].y.is_zero()));
    auto v = numeric_pair<mpq>(right_side, mpq(0));

    mpq y_of_bound(0);
    switch (kind) {
    case LT:
        if (v <= m_mpq_lar_core_solver.m_r_low_bounds[j]) {
            m_status = lp_status::INFEASIBLE;
            m_infeasible_column_index = j;
            set_upper_bound_witness(j, ci);
        }
        break;
    case LE:
	{
            if (v < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                m_status = lp_status::INFEASIBLE;
                m_infeasible_column_index = j;
                set_upper_bound_witness(j, ci);
            }
	}
	break;
    case GT:
	{
            if (v >= m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_status = lp_status::INFEASIBLE;
                m_infeasible_column_index = j;
                set_low_bound_witness(j, ci);
            }
	}
	break;
    case GE:
	{
            if (v > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_status = lp_status::INFEASIBLE;
                m_infeasible_column_index = j;
                set_low_bound_witness(j, ci);
            }
	}
	break;
    case EQ:
	{
            if (v < m_mpq_lar_core_solver.m_r_low_bounds[j]) {
                m_status = lp_status::INFEASIBLE;
                m_infeasible_column_index = j;
                set_upper_bound_witness(j, ci);
            }
            else if (v > m_mpq_lar_core_solver.m_r_upper_bounds[j]) {
                m_status = lp_status::INFEASIBLE;
                m_infeasible_column_index = j;
                set_low_bound_witness(j, ci);
            }
            break;
	}

    default:
        lp_unreachable();

    }
}


} // namespace lp


