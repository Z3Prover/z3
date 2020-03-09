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
#pragma once
#include "util/vector.h"
#include <utility>
#include "util/debug.h"
#include "util/buffer.h"
#include <unordered_map>
#include <unordered_set>
#include <string>
#include <algorithm>
#include <stack>
#include <functional>
#include "math/lp/lar_constraints.h"
#include "math/lp/lar_core_solver.h"
#include "math/lp/numeric_pair.h"
#include "math/lp/scaler.h"
#include "math/lp/lp_primal_core_solver.h"
#include "math/lp/random_updater.h"
#include "math/lp/stacked_value.h"
#include "math/lp/stacked_vector.h"
#include "math/lp/implied_bound.h"
#include "math/lp/bound_analyzer_on_row.h"
#include "math/lp/conversion_helper.h"
#include "math/lp/int_solver.h"
#include "math/lp/nra_solver.h"
#include "math/lp/lp_bound_propagator.h"

namespace lp {

typedef unsigned lpvar;
const lpvar null_lpvar = UINT_MAX;

class lar_solver : public column_namer {
    struct term_hasher {
        std::size_t operator()(const lar_term &t) const
        {            
            using std::size_t;
            using std::hash;
            using std::string;
            size_t seed = 0;
            int i = 0;
            for (const auto p : t) {
                hash_combine(seed, p.var());
                hash_combine(seed, p.coeff());
                if (i++ > 10)
                    break;
            }
            return seed;
        }
    };

    struct term_comparer {
        bool operator()(const lar_term &a, const lar_term& b) const
        {
            return a == b;            
        }
    };



    
    //////////////////// fields //////////////////////////
    lp_settings                                         m_settings;
    lp_status                                           m_status;
    stacked_value<simplex_strategy_enum>                m_simplex_strategy;
    stacked_value<int>                                  m_infeasible_column; // such can be found at the initialization step
public:
    lar_core_solver                                     m_mpq_lar_core_solver;
private:
    int_solver *                                        m_int_solver;
public:
    const var_index                                     m_terms_start_index;
    var_register                                        m_var_register;
    var_register                                        m_term_register;
    stacked_vector<ul_pair>                             m_columns_to_ul_pairs;
    constraint_set                                      m_constraints;
    // the set of column indices j such that bounds have changed for j
    int_set                                             m_columns_with_changed_bound;
    int_set                                             m_rows_with_changed_bounds;
    int_set                                             m_basic_columns_with_changed_cost;
    // these are basic columns with the value changed, so the the corresponding row in the tableau
    // does not sum to zero anymore
    int_set                                             m_incorrect_columns;
    stacked_value<int>                                  m_infeasible_column_index; // such can be found at the initialization step
    stacked_value<unsigned>                             m_term_count;
    vector<lar_term*>                                   m_terms;
    indexed_vector<mpq>                                 m_column_buffer;
    bool                                                m_need_register_terms;
    std::unordered_map<lar_term, std::pair<mpq, unsigned>, term_hasher, term_comparer>
                                                        m_normalized_terms_to_columns;
    // end of fields

    unsigned terms_start_index() const { return m_terms_start_index; }
    const vector<lar_term*> & terms() const { return m_terms; }
    lar_term const& term(unsigned i) const { return *m_terms[i]; }
    constraint_set const& constraints() const { return m_constraints; }
    void set_int_solver(int_solver * int_slv) { m_int_solver = int_slv; }
    int_solver * get_int_solver() { return m_int_solver; }

    ////////////////// methods ////////////////////////////////
    static_matrix<mpq, numeric_pair<mpq>> & A_r();
    static_matrix<mpq, numeric_pair<mpq>> const & A_r() const;
    static_matrix<double, double> & A_d();
    static_matrix<double, double > const & A_d() const;
    
    static bool valid_index(unsigned j){ return static_cast<int>(j) >= 0;}

    bool column_is_int(unsigned j) const;
    bool column_value_is_int(unsigned j) const {
        return m_mpq_lar_core_solver.m_r_x[j].is_int();
    }

    const impq& get_column_value(unsigned j) const {
        return m_mpq_lar_core_solver.m_r_x[j];
    }

    void set_column_value(unsigned j, const impq& v) {
        m_mpq_lar_core_solver.m_r_x[j] = v;
    }
    
    const mpq& get_column_value_rational(unsigned j) const {
        return m_mpq_lar_core_solver.m_r_x[j].x;
    }

    bool is_term(var_index j) const;
    bool column_is_fixed(unsigned j) const;
    bool column_is_free(unsigned j) const;
public:

    // init region
    bool strategy_is_undecided() const;

    var_index add_var(unsigned ext_j, bool is_integer);

    var_index add_named_var(unsigned ext_j, bool is_integer, const std::string&);

    void register_new_ext_var_index(unsigned ext_v, bool is_int);

    bool external_is_used(unsigned) const;
    
    bool term_is_int(const lar_term * t) const;

    bool var_is_int(var_index v) const;

    void add_non_basic_var_to_core_fields(unsigned ext_j, bool is_int);

    void add_new_var_to_core_fields_for_doubles(bool register_in_basis);

    void add_new_var_to_core_fields_for_mpq(bool register_in_basis);



    // terms
    bool all_vars_are_registered(const vector<std::pair<mpq, var_index>> & coeffs);

    var_index add_term(const vector<std::pair<mpq, var_index>> & coeffs, unsigned ext_i);

    var_index add_term_undecided(const vector<std::pair<mpq, var_index>> & coeffs);

    bool term_coeffs_are_ok(const vector<std::pair<mpq, var_index>> & coeffs);
    void push_term(lar_term* t);
    void add_row_for_term(const lar_term * term, unsigned term_ext_index);

    void add_row_from_term_no_constraint(const lar_term * term, unsigned term_ext_index);

    void add_basic_var_to_core_fields();

    constraint_index mk_var_bound(var_index j, lconstraint_kind kind, const mpq & right_side);

    void activate(constraint_index ci);

    constraint_index add_var_bound(var_index j, lconstraint_kind kind, const mpq & right_side) ;

    bool compare_values(var_index j, lconstraint_kind kind, const mpq & right_side);

    bool compare_values(impq const& lhs, lconstraint_kind k, const mpq & rhs);

    void update_column_type_and_bound(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    void update_column_type_and_bound_with_ub(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    void update_column_type_and_bound_with_no_ub(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    void update_bound_with_ub_lb(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    void update_bound_with_no_ub_lb(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    void update_bound_with_ub_no_lb(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    void update_bound_with_no_ub_no_lb(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    
    constraint_index add_var_bound_on_constraint_for_term(var_index j, lconstraint_kind kind, const mpq & right_side);

    void set_infeasible_column(unsigned j) {
        set_status(lp_status::INFEASIBLE);
        m_infeasible_column = j;
    }

    constraint_index add_constraint_from_term_and_create_new_column_row(unsigned term_j, const lar_term* term,
                                                            lconstraint_kind kind, const mpq & right_side);

    unsigned row_of_basic_column(unsigned) const;
    
    void decide_on_strategy_and_adjust_initial_state();

    void adjust_initial_state();

    void adjust_initial_state_for_lu();

    void adjust_initial_state_for_tableau_rows();

    // this fills the last row of A_d and sets the basis column: -1 in the last column of the row
    void fill_last_row_of_A_d(static_matrix<double, double> & A, const lar_term* ls);

    //end of init region


    lp_settings & settings();

    lp_settings const & settings() const;

    void clear();
    lar_solver();

    void set_track_pivoted_rows(bool v);

    bool get_track_pivoted_rows() const;
    
    virtual ~lar_solver();

    unsigned adjust_term_index(unsigned j) const;


    bool use_lu() const;
    
    bool sizes_are_correct() const;
     
    bool implied_bound_is_correctly_explained(implied_bound const & be, const vector<std::pair<mpq, unsigned>> & explanation) const;
    
    void analyze_new_bounds_on_row(
        unsigned row_index,
        lp_bound_propagator & bp);

    void analyze_new_bounds_on_row_tableau(
        unsigned row_index,
        lp_bound_propagator & bp);

    
    void substitute_basis_var_in_terms_for_row(unsigned i);
    
    void calculate_implied_bounds_for_row(unsigned i, lp_bound_propagator & bp);

    unsigned adjust_column_index_to_term_index(unsigned j) const;

    unsigned map_term_index_to_column_index(unsigned j) const;
    
    var_index local_to_external(var_index idx) const { return is_term(idx)?
            m_term_register.local_to_external(idx) : m_var_register.local_to_external(idx); }

    unsigned number_of_vars() const { return m_var_register.size(); }
    
    var_index external_to_local(unsigned j) const {
        var_index local_j;
        if (
            m_var_register.external_is_used(j, local_j) ||
            m_term_register.external_is_used(j, local_j))
            {
                return local_j;
            }
        else
            return -1;
    }

    bool column_has_upper_bound(unsigned j) const {
        return m_mpq_lar_core_solver.m_r_solver.column_has_upper_bound(j);
    }

    bool column_has_lower_bound(unsigned j) const {
        return m_mpq_lar_core_solver.m_r_solver.column_has_lower_bound(j);
    }

    const impq& get_upper_bound(unsigned j) const {
        return m_mpq_lar_core_solver.m_r_solver.m_upper_bounds[j];
    }

    const impq& get_lower_bound(unsigned j) const {
        return m_mpq_lar_core_solver.m_r_solver.m_lower_bounds[j];
    }
    
    
    void propagate_bounds_on_a_term(const lar_term& t, lp_bound_propagator & bp, unsigned term_offset);


    void explain_implied_bound(implied_bound & ib, lp_bound_propagator & bp);


    bool term_is_used_as_row(unsigned term) const;
    
    void propagate_bounds_on_terms(lp_bound_propagator & bp);


    // goes over touched rows and tries to induce bounds
    void propagate_bounds_for_touched_rows(lp_bound_propagator & bp);

    lp_status get_status() const;

    void set_status(lp_status s);

    lp_status find_feasible_solution();   
    
    lp_status solve();

    void fill_explanation_from_infeasible_column(explanation & evidence) const;

    
    unsigned get_total_iterations() const;
    // see http://research.microsoft.com/projects/z3/smt07.pdf
    // This method searches for a feasible solution with as many different values of variables, reverenced in vars, as it can find
    // Attention, after a call to this method the non-basic variables don't necesserarly stick to their bounds anymore
    vector<unsigned> get_list_of_all_var_indices() const;
    void push();

    static void clean_popped_elements(unsigned n, int_set& set);

    static void shrink_inf_set_after_pop(unsigned n, int_set & set);
    
    void pop(unsigned k);

    bool maximize_term_on_tableau(const lar_term & term,
                                  impq &term_max);

    bool costs_are_zeros_for_r_solver() const;
    bool reduced_costs_are_zeroes_for_r_solver() const;
    
    void set_costs_to_zero(const lar_term & term);

    void prepare_costs_for_r_solver(const lar_term & term);
    
    bool maximize_term_on_corrected_r_solver(lar_term & term, impq &term_max);    
    // starting from a given feasible state look for the maximum of the term
    // return true if found and false if unbounded
    lp_status maximize_term(unsigned j_or_term, impq &term_max);
    

    
    const lar_term &  get_term(unsigned j) const;

    void pop_core_solver_params();

    void pop_core_solver_params(unsigned k);


    void set_upper_bound_witness(var_index j, constraint_index ci);

    void set_lower_bound_witness(var_index j, constraint_index ci);


    void substitute_terms_in_linear_expression( const vector<std::pair<mpq, var_index>>& left_side_with_terms,
                                                vector<std::pair<mpq, var_index>> &left_side) const;


    void detect_rows_of_bound_change_column_for_nbasic_column(unsigned j);

    void detect_rows_of_bound_change_column_for_nbasic_column_tableau(unsigned j);

    bool use_tableau() const;

    bool use_tableau_costs() const;
    
    void detect_rows_of_column_with_bound_change(unsigned j);

    void adjust_x_of_column(unsigned j);

    bool row_is_correct(unsigned i) const;
    
    bool ax_is_correct() const;

    bool tableau_with_costs() const;

    bool costs_are_used() const;
    
    void change_basic_columns_dependend_on_a_given_nb_column(unsigned j, const numeric_pair<mpq> & delta);

    void update_x_and_inf_costs_for_column_with_changed_bounds(unsigned j);

    
    unsigned num_changed_bounds() const { return m_rows_with_changed_bounds.size(); }

    void detect_rows_with_changed_bounds_for_column(unsigned j);
    
    void detect_rows_with_changed_bounds();
    inline bool is_base(unsigned j) const {
        return m_mpq_lar_core_solver.m_r_heading[j] >= 0;
    }

    bool move_non_basic_columns_to_bounds();

    bool move_non_basic_column_to_bounds(unsigned j);
    void set_value_for_nbasic_column(unsigned j, const impq & new_val);
    void update_x_and_inf_costs_for_columns_with_changed_bounds();

    void update_x_and_inf_costs_for_columns_with_changed_bounds_tableau();
    
    void solve_with_core_solver();

    numeric_pair<mpq> get_basic_var_value_from_row(unsigned i);

    template <typename K, typename L>
    void add_last_rows_to_lu(lp_primal_core_solver<K,L> & s);
    
    bool x_is_correct() const;

    bool var_is_registered(var_index vj) const;

    void fill_last_row_of_A_r(static_matrix<mpq, numeric_pair<mpq>> & A, const lar_term * ls);

    template <typename U, typename V>
    void create_matrix_A(static_matrix<U, V> & matr);

    template <typename U, typename V>
    void copy_from_mpq_matrix(static_matrix<U, V> & matr);


    bool try_to_set_fixed(column_info<mpq> & ci);

    column_type get_column_type(unsigned j) const;

    bool all_constrained_variables_are_registered(const vector<std::pair<mpq, var_index>>& left_side);

    bool all_constraints_hold() const;
    bool constraint_holds(const lar_base_constraint & constr, std::unordered_map<var_index, mpq> & var_map) const;
    bool the_relations_are_of_same_type(const vector<std::pair<mpq, unsigned>> & evidence, lconstraint_kind & the_kind_of_sum) const;

    static void register_in_map(std::unordered_map<var_index, mpq> & coeffs, const lar_base_constraint & cn, const mpq & a);
    static void register_monoid_in_map(std::unordered_map<var_index, mpq> & coeffs, const mpq & a, unsigned j);


    bool the_left_sides_sum_to_zero(const vector<std::pair<mpq, unsigned>> & evidence) const;

    bool the_right_sides_do_not_sum_to_zero(const vector<std::pair<mpq, unsigned>> & evidence);

    bool explanation_is_correct(explanation&) const;

    bool inf_explanation_is_correct() const;

    mpq sum_of_right_sides_of_explanation(explanation &) const;

    bool has_lower_bound(var_index var, constraint_index& ci, mpq& value, bool& is_strict) const;
    
    bool has_upper_bound(var_index var, constraint_index& ci, mpq& value, bool& is_strict) const;

    bool has_value(var_index var, mpq& value) const;

    void get_infeasibility_explanation(explanation &) const;

    void get_infeasibility_explanation_for_inf_sign(
        explanation & exp,
        const vector<std::pair<mpq, unsigned>> & inf_row,
        int inf_sign) const;

    void get_model(std::unordered_map<var_index, mpq> & variable_values) const;

    void get_rid_of_inf_eps();
    
    void get_model_do_not_care_about_diff_vars(std::unordered_map<var_index, mpq> & variable_values) const;

    std::string get_variable_name(var_index vi) const;

    void set_variable_name(var_index vi, std::string);

    // ********** print region start

    std::ostream& print_terms(std::ostream& out) const;

    std::ostream& print_term(lar_term const& term, std::ostream & out) const;

    static std::ostream& print_term_as_indices(lar_term const& term, std::ostream & out);

    std::ostream& print_constraint_indices_only(const lar_base_constraint * c, std::ostream & out) const;

    std::ostream& print_implied_bound(const implied_bound& be, std::ostream & out) const;

    std::ostream& print_values(std::ostream& out) const;

    mpq get_left_side_val(const lar_base_constraint &  cns, const std::unordered_map<var_index, mpq> & var_map) const;

    void fill_var_set_for_random_update(unsigned sz, var_index const * vars, vector<unsigned>& column_list);

    void random_update(unsigned sz, var_index const * vars);
    void pivot_fixed_vars_from_basis();
    void pop();
    bool column_represents_row_in_tableau(unsigned j);
    void make_sure_that_the_bottom_right_elem_not_zero_in_tableau(unsigned i, unsigned j);
    void remove_last_row_and_column_from_tableau(unsigned j);
    void remove_last_column_from_A();

    void remove_last_column_from_basis_tableau(unsigned j);
    void remove_last_column_from_tableau();
    void pop_tableau();
    void clean_inf_set_of_r_solver_after_pop();
    void shrink_explanation_to_minimum(vector<std::pair<mpq, constraint_index>> & explanation) const;

    
    
    bool column_value_is_integer(unsigned j) const {
        return get_column_value(j).is_int();
    }

    bool column_is_real(unsigned j) const {
        return !column_is_int(j);
    }	
	
    bool model_is_int_feasible() const;

    const impq & column_lower_bound(unsigned j) const {
        return m_mpq_lar_core_solver.lower_bound(j);
    }

    const impq & column_upper_bound(unsigned j) const {
        return m_mpq_lar_core_solver.upper_bound(j);
    }

    bool column_is_bounded(unsigned j) const {
        return m_mpq_lar_core_solver.column_is_bounded(j);
    }

    void get_bound_constraint_witnesses_for_column(unsigned j, constraint_index & lc, constraint_index & uc) const {
        const ul_pair & ul = m_columns_to_ul_pairs[j];
        lc = ul.lower_bound_witness();
        uc = ul.upper_bound_witness();
    }
    indexed_vector<mpq> & get_column_in_lu_mode(unsigned j) {
        m_column_buffer.clear();
        m_column_buffer.resize(A_r().row_count());
        m_mpq_lar_core_solver.m_r_solver.solve_Bd(j, m_column_buffer);
        return m_column_buffer;
    }
    
    bool bound_is_integer_for_integer_column(unsigned j, const mpq & right_side) const;
    
    const row_strip<mpq> &  get_row(unsigned i) {
        return A_r().m_rows[i];
    }
    
    unsigned get_base_column_in_row(unsigned row_index) const {
        return m_mpq_lar_core_solver.m_r_solver.get_base_column_in_row(row_index);
    }

    constraint_index get_column_upper_bound_witness(unsigned j) const {
        return m_columns_to_ul_pairs()[j].upper_bound_witness();
    }

    constraint_index get_column_lower_bound_witness(unsigned j) const {
        return m_columns_to_ul_pairs()[j].lower_bound_witness();
    }

    void subs_term_columns(lar_term& t) {
        vector<std::pair<unsigned,unsigned>> columns_to_subs;
        for (const auto & m : t) {
            unsigned tj = adjust_column_index_to_term_index(m.var());
            if (tj == m.var()) continue;
            columns_to_subs.push_back(std::make_pair(m.var(), tj));
        }
        for (const auto & p : columns_to_subs) {
            t.subst_index(p.first, p.second);            
        }
    }

    std::ostream& print_column_info(unsigned j, std::ostream& out) const {
        m_mpq_lar_core_solver.m_r_solver.print_column_info(j, out);
        if( !column_corresponds_to_term(j))
            return out;
        const lar_term& t = * m_terms[m_var_register.local_to_external(j) - m_terms_start_index];
        print_term_as_indices(t, out) << "\n";
        return out;
    }
    
    bool has_int_var() const;

    bool has_inf_int() const {
        for (unsigned j = 0; j < column_count(); j++) {
            if (column_is_int(j) && ! column_value_is_int(j))
                return true;
        }
        return false;
    }

    bool r_basis_has_inf_int() const {
        for (unsigned j : r_basis()) {
            if (column_is_int(j) && ! column_value_is_int(j))
                return true;
        }
        return false;
    }
    
    lar_core_solver & get_core_solver() { return m_mpq_lar_core_solver; }
    bool column_corresponds_to_term(unsigned) const;
    void catch_up_in_updating_int_solver();
    var_index to_column(unsigned ext_j) const;
    bool tighten_term_bounds_by_delta(unsigned, const impq&);
    void round_to_integer_solution();
    void fix_terms_with_rounded_columns();
    void update_delta_for_terms(const impq & delta, unsigned j, const vector<unsigned>&);
    void fill_vars_to_terms(vector<vector<unsigned>> & vars_to_terms);
    unsigned column_count() const { return A_r().column_count(); }
    unsigned row_count() const { return A_r().row_count(); }
    const vector<unsigned> & r_basis() const { return m_mpq_lar_core_solver.r_basis(); }
    const vector<unsigned> & r_nbasis() const { return m_mpq_lar_core_solver.r_nbasis(); }
    bool get_equality_and_right_side_for_term_on_current_x(unsigned i, mpq &rs, constraint_index& ci, bool &upper_bound) const;
    bool remove_from_basis(unsigned);
    lar_term get_term_to_maximize(unsigned ext_j) const;
    void set_cut_strategy(unsigned cut_frequency);
    bool sum_first_coords(const lar_term& t, mpq & val) const;
    void collect_rounded_rows_to_fix();
    void register_existing_terms();
    void register_normalized_term(const lar_term&, lpvar);
    void deregister_normalized_term(const lar_term&);
    bool fetch_normalized_term_column(const lar_term& t, std::pair<mpq, lpvar>& ) const;
};
}
