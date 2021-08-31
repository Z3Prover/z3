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
#include "util/stacked_value.h"
#include "math/lp/stacked_vector.h"
#include "math/lp/implied_bound.h"
#include "math/lp/bound_analyzer_on_row.h"
#include "math/lp/conversion_helper.h"
#include "math/lp/int_solver.h"
#include "math/lp/nra_solver.h"
#include "math/lp/lp_types.h"
#include "math/lp/lp_bound_propagator.h"

namespace lp {

class int_branch;
class int_solver;
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
                hash_combine(seed, (unsigned)p.column());
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
    // such can be found at the initialization step: u < l
    stacked_value<int>                                  m_crossed_bounds_column; 
    lar_core_solver                                     m_mpq_lar_core_solver;
    int_solver *                                        m_int_solver;
    bool                                                m_need_register_terms;
    var_register                                        m_var_register;
    var_register                                        m_term_register;
    stacked_vector<ul_pair>                             m_columns_to_ul_pairs;
    constraint_set                                      m_constraints;
    // the set of column indices j such that bounds have changed for j
    u_set                                               m_columns_with_changed_bounds;
    u_set                                               m_rows_with_changed_bounds;
    u_set                                               m_basic_columns_with_changed_cost;
    // these are basic columns with the value changed, so the the corresponding row in the tableau
    // does not sum to zero anymore
    u_set                                               m_incorrect_columns;
    // copy of m_r_solver.inf_set()
    unsigned_vector                                     m_inf_index_copy;
    stacked_value<unsigned>                             m_term_count;
    vector<lar_term*>                                   m_terms;
    indexed_vector<mpq>                                 m_column_buffer;
    std::unordered_map<lar_term, std::pair<mpq, unsigned>, term_hasher, term_comparer>
    m_normalized_terms_to_columns;
    vector<impq>                                        m_backup_x;
    stacked_vector<unsigned>                            m_usage_in_terms;
    // ((x[j], is_int(j))->j)  for fixed j, used in equalities propagation
    // maps values to integral fixed vars
    map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>>  m_fixed_var_table_int;
    // maps values to non-integral fixed vars
    map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>>  m_fixed_var_table_real;
    // end of fields

    ////////////////// methods ////////////////////////////////
    static_matrix<double, double> & A_d();
    static_matrix<double, double > const & A_d() const;
    
    static bool valid_index(unsigned j) { return static_cast<int>(j) >= 0;}
    const lar_term & get_term(unsigned j) const;
    bool row_has_a_big_num(unsigned i) const;
    // init region
    bool strategy_is_undecided() const;
    void register_new_ext_var_index(unsigned ext_v, bool is_int);
    bool term_is_int(const lar_term * t) const;
    bool term_is_int(const vector<std::pair<mpq, unsigned int>> & coeffs) const;
    void add_non_basic_var_to_core_fields(unsigned ext_j, bool is_int);
    void add_new_var_to_core_fields_for_doubles(bool register_in_basis);
    void add_new_var_to_core_fields_for_mpq(bool register_in_basis);
    mpq adjust_bound_for_int(lpvar j, lconstraint_kind&, const mpq&);

    // terms
    bool all_vars_are_registered(const vector<std::pair<mpq, var_index>> & coeffs);
    var_index add_term_undecided(const vector<std::pair<mpq, var_index>> & coeffs);
    bool term_coeffs_are_ok(const vector<std::pair<mpq, var_index>> & coeffs);
    void push_term(lar_term* t);
    void add_row_for_term(const lar_term * term, unsigned term_ext_index);
    void add_row_from_term_no_constraint(const lar_term * term, unsigned term_ext_index);
    void add_basic_var_to_core_fields();
    bool compare_values(impq const& lhs, lconstraint_kind k, const mpq & rhs);

    inline void clear_columns_with_changed_bounds() { m_columns_with_changed_bounds.clear(); }
    inline void increase_by_one_columns_with_changed_bounds() { m_columns_with_changed_bounds.increase_size_by_one(); }
    inline void insert_to_columns_with_changed_bounds(unsigned j) { m_columns_with_changed_bounds.insert(j); }
    
    void update_column_type_and_bound_check_on_equal(unsigned j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index, unsigned&);
    void update_column_type_and_bound(unsigned j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    void update_column_type_and_bound_with_ub(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    void update_column_type_and_bound_with_no_ub(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    void update_bound_with_ub_lb(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    void update_bound_with_no_ub_lb(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    void update_bound_with_ub_no_lb(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    void update_bound_with_no_ub_no_lb(var_index j, lconstraint_kind kind, const mpq & right_side, constraint_index constr_index);
    void register_in_fixed_var_table(unsigned, unsigned&);
    void remove_non_fixed_from_fixed_var_table();
    constraint_index add_var_bound_on_constraint_for_term(var_index j, lconstraint_kind kind, const mpq & right_side);
    inline void set_infeasible_column(unsigned j) {
        set_status(lp_status::INFEASIBLE);
        m_crossed_bounds_column = j;
    }
    constraint_index add_constraint_from_term_and_create_new_column_row(unsigned term_j, const lar_term* term,
                                                                        lconstraint_kind kind, const mpq & right_side);
    unsigned row_of_basic_column(unsigned) const;
    void decide_on_strategy_and_adjust_initial_state();
    void adjust_initial_state();
    void adjust_initial_state_for_lu();
    void adjust_initial_state_for_tableau_rows();
    void fill_last_row_of_A_d(static_matrix<double, double> & A, const lar_term* ls);
    void clear();
    bool use_lu() const;
    bool sizes_are_correct() const;
    bool implied_bound_is_correctly_explained(implied_bound const & be, const vector<std::pair<mpq, unsigned>> & explanation) const;
    
    template <typename T>
    void analyze_new_bounds_on_row_tableau(
        unsigned row_index,
        lp_bound_propagator<T> & bp ) {
        
        if (A_r().m_rows[row_index].size() > settings().max_row_length_for_bound_propagation
            || row_has_a_big_num(row_index))
            return;
        lp_assert(use_tableau());
        
        bound_analyzer_on_row<row_strip<mpq>, lp_bound_propagator<T>>::analyze_row(A_r().m_rows[row_index],
                                                                                   null_ci,
                                                                                   zero_of_type<numeric_pair<mpq>>(),
                                                                                   row_index,
                                                                                   bp
                                                                                   );
    }

    void substitute_basis_var_in_terms_for_row(unsigned i);
    template <typename T>
    void calculate_implied_bounds_for_row(unsigned i, lp_bound_propagator<T> & bp) {
        SASSERT(use_tableau());
        analyze_new_bounds_on_row_tableau(i, bp);
    }
    static void clean_popped_elements(unsigned n, u_set& set);
    static void shrink_inf_set_after_pop(unsigned n, u_set & set);
    bool maximize_term_on_tableau(const lar_term & term,
                                  impq &term_max);
    bool costs_are_zeros_for_r_solver() const;
    bool reduced_costs_are_zeroes_for_r_solver() const;
    void set_costs_to_zero(const lar_term & term);
    void prepare_costs_for_r_solver(const lar_term & term);
    bool maximize_term_on_corrected_r_solver(lar_term & term, impq &term_max);    
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
    bool tableau_with_costs() const;
    bool costs_are_used() const;
    void change_basic_columns_dependend_on_a_given_nb_column(unsigned j, const numeric_pair<mpq> & delta);
    void update_x_and_inf_costs_for_column_with_changed_bounds(unsigned j);
    unsigned num_changed_bounds() const { return m_rows_with_changed_bounds.size(); }
    void detect_rows_with_changed_bounds_for_column(unsigned j);
    void detect_rows_with_changed_bounds();
    void set_value_for_nbasic_column(unsigned j, const impq & new_val);
    void update_x_and_inf_costs_for_columns_with_changed_bounds();
    void update_x_and_inf_costs_for_columns_with_changed_bounds_tableau();
    void solve_with_core_solver();
    numeric_pair<mpq> get_basic_var_value_from_row(unsigned i);
    template <typename K, typename L>
    void add_last_rows_to_lu(lp_primal_core_solver<K,L> & s);
    bool x_is_correct() const;
    void fill_last_row_of_A_r(static_matrix<mpq, numeric_pair<mpq>> & A, const lar_term * ls);
    template <typename U, typename V>
    void create_matrix_A(static_matrix<U, V> & matr);
    template <typename U, typename V>
    void copy_from_mpq_matrix(static_matrix<U, V> & matr);
    bool try_to_set_fixed(column_info<mpq> & ci);
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
    void get_infeasibility_explanation_for_inf_sign(
        explanation & exp,
        const vector<std::pair<mpq, unsigned>> & inf_row,
        int inf_sign) const;
    mpq get_left_side_val(const lar_base_constraint &  cns, const std::unordered_map<var_index, mpq> & var_map) const;
    void fill_var_set_for_random_update(unsigned sz, var_index const * vars, vector<unsigned>& column_list);
    void pivot_fixed_vars_from_basis();
    bool column_represents_row_in_tableau(unsigned j);
    void make_sure_that_the_bottom_right_elem_not_zero_in_tableau(unsigned i, unsigned j);
    void remove_last_row_and_column_from_tableau(unsigned j);
    void remove_last_column_from_A();

    void remove_last_column_from_basis_tableau(unsigned j);
    void remove_last_column_from_tableau();
    void pop_tableau();
    void clean_inf_set_of_r_solver_after_pop();
    void shrink_explanation_to_minimum(vector<std::pair<mpq, constraint_index>> & explanation) const;
    inline bool column_value_is_integer(unsigned j) const { return get_column_value(j).is_int(); }
    bool model_is_int_feasible() const;
    inline
    indexed_vector<mpq> & get_column_in_lu_mode(unsigned j) {
        m_column_buffer.clear();
        m_column_buffer.resize(A_r().row_count());
        m_mpq_lar_core_solver.m_r_solver.solve_Bd(j, m_column_buffer);
        return m_column_buffer;
    }
    bool bound_is_integer_for_integer_column(unsigned j, const mpq & right_side) const;
    inline unsigned get_base_column_in_row(unsigned row_index) const {
        return m_mpq_lar_core_solver.m_r_solver.get_base_column_in_row(row_index);
    }
    inline lar_core_solver & get_core_solver() { return m_mpq_lar_core_solver; }
    void catch_up_in_updating_int_solver();
    var_index to_column(unsigned ext_j) const;
    void fix_terms_with_rounded_columns();
    void update_delta_for_terms(const impq & delta, unsigned j, const vector<unsigned>&);
    void fill_vars_to_terms(vector<vector<unsigned>> & vars_to_terms);
    bool remove_from_basis(unsigned);
    lar_term get_term_to_maximize(unsigned ext_j) const;
    bool sum_first_coords(const lar_term& t, mpq & val) const;
    void collect_rounded_rows_to_fix();
    void register_normalized_term(const lar_term&, lpvar);
    void deregister_normalized_term(const lar_term&);

    mutable std::unordered_set<impq> m_set_of_different_pairs;
    mutable std::unordered_set<mpq>  m_set_of_different_singles;
    mutable mpq m_delta;

public:
    const map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>>& fixed_var_table_int() const {
        return m_fixed_var_table_int;
    }
    map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>>& fixed_var_table_int() {
        return m_fixed_var_table_int;
    }
    const map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>>& fixed_var_table_real() const {
        return m_fixed_var_table_real;
    }
    map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>>& fixed_var_table_real() {
        return m_fixed_var_table_real;
    }

    bool find_in_fixed_tables(const rational& mpq, bool is_int, unsigned & j) const {
        return is_int? fixed_var_table_int().find(mpq, j) :
            fixed_var_table_real().find(mpq, j);
    }
    
    template <typename T> void remove_non_fixed_from_table(T&);
    unsigned external_to_column_index(unsigned) const;
    bool inside_bounds(lpvar, const impq&) const;
    inline void set_column_value(unsigned j, const impq& v) {
        m_mpq_lar_core_solver.m_r_solver.update_x(j, v);
    }
    inline void set_column_value_test(unsigned j, const impq& v) {
        set_column_value(j, v);
    }
    unsigned get_total_iterations() const;
    var_index add_named_var(unsigned ext_j, bool is_integer, const std::string&);
    lp_status maximize_term(unsigned j_or_term, impq &term_max);
    inline 
    core_solver_pretty_printer<lp::mpq, lp::impq> pp(std::ostream& out) const { return
            core_solver_pretty_printer<lp::mpq, lp::impq>(m_mpq_lar_core_solver.m_r_solver, out); }
    void get_infeasibility_explanation(explanation &) const;
    inline void backup_x() { m_backup_x = m_mpq_lar_core_solver.m_r_x; }
    inline void restore_x() { m_mpq_lar_core_solver.m_r_x = m_backup_x; }
    template <typename T>
    void explain_implied_bound(const implied_bound & ib, lp_bound_propagator<T> & bp) {
        unsigned i = ib.m_row_or_term_index;
        int bound_sign = ib.m_is_lower_bound? 1: -1;
        int j_sign = (ib.m_coeff_before_j_is_pos ? 1 :-1) * bound_sign;
        unsigned bound_j = ib.m_j;
        if (tv::is_term(bound_j)) {
            bound_j = m_var_register.external_to_local(bound_j);
        }
        for (auto const& r : A_r().m_rows[i]) {
            unsigned j = r.var();
            if (j == bound_j) continue;
            mpq const& a = r.coeff();
            int a_sign = is_pos(a)? 1: -1;
            int sign = j_sign * a_sign;
            const ul_pair & ul =  m_columns_to_ul_pairs[j];
            auto witness = sign > 0? ul.upper_bound_witness(): ul.lower_bound_witness();
            lp_assert(is_valid(witness));
            bp.consume(a, witness);
        }
    }
    // lp_assert(implied_bound_is_correctly_explained(ib, explanation)); }
    constraint_index mk_var_bound(var_index j, lconstraint_kind kind, const mpq & right_side);
    void activate_check_on_equal(constraint_index, var_index&);
    void activate(constraint_index);
    void random_update(unsigned sz, var_index const * vars);
    void mark_rows_for_bound_prop(lpvar j);
    template <typename T>
    void propagate_bounds_for_touched_rows(lp_bound_propagator<T> & bp) {
        SASSERT(use_tableau());
        for (unsigned i : m_rows_with_changed_bounds) {
            calculate_implied_bounds_for_row(i, bp);
            if (settings().get_cancel_flag())
                return;
        }
        // these two loops should be run sequentially
        // since the first loop might change column bounds
        // and add fixed columns this way
        if (settings().cheap_eqs()) {
            bp.clear_for_eq();
            for (unsigned i : m_rows_with_changed_bounds) {
                calculate_cheap_eqs_for_row(i, bp);
                if (settings().get_cancel_flag())
                    return;
            }
        }
        m_rows_with_changed_bounds.clear();
    }
    template <typename T>
    void calculate_cheap_eqs_for_row(unsigned i, lp_bound_propagator<T> & bp) {
        bp.cheap_eq_tree(i);
    }
    
    bool is_fixed(column_index const& j) const { return column_is_fixed(j); }
    inline column_index to_column_index(unsigned v) const { return column_index(external_to_column_index(v)); }
    bool external_is_used(unsigned) const;
    void pop(unsigned k);
    bool compare_values(var_index j, lconstraint_kind kind, const mpq & right_side);
    var_index add_term(const vector<std::pair<mpq, var_index>> & coeffs, unsigned ext_i);
    void register_existing_terms();
    constraint_index add_var_bound(var_index, lconstraint_kind, const mpq &);
    constraint_index add_var_bound_check_on_equal(var_index, lconstraint_kind, const mpq &, var_index&);
    
    var_index add_var(unsigned ext_j, bool is_integer);
    void set_cut_strategy(unsigned cut_frequency);
    inline unsigned column_count() const { return A_r().column_count(); }
    inline var_index local_to_external(var_index idx) const {
        return tv::is_term(idx)?
            m_term_register.local_to_external(idx) : m_var_register.local_to_external(idx);
    }
    bool column_corresponds_to_term(unsigned) const;
    inline unsigned row_count() const { return A_r().row_count(); }
    bool var_is_registered(var_index vj) const;
    void clear_inf_set() {
        m_mpq_lar_core_solver.m_r_solver.inf_set().clear();        
    }
    inline void remove_column_from_inf_set(unsigned j) {
        m_mpq_lar_core_solver.m_r_solver.remove_column_from_inf_set(j);
    }
    template <typename ChangeReport>
    void change_basic_columns_dependend_on_a_given_nb_column_report(unsigned j,
                                                                    const numeric_pair<mpq> & delta,
                                                                    const ChangeReport& after) {
        if (use_tableau()) {
            for (const auto & c : A_r().m_columns[j]) {
                unsigned bj = m_mpq_lar_core_solver.m_r_basis[c.var()];
                if (tableau_with_costs()) {
                    m_basic_columns_with_changed_cost.insert(bj);
                }
                m_mpq_lar_core_solver.m_r_solver.add_delta_to_x_and_track_feasibility(bj, - A_r().get_val(c) * delta);
                after(bj);
                TRACE("change_x_del",
                      tout << "changed basis column " << bj << ", it is " <<
                      ( m_mpq_lar_core_solver.m_r_solver.column_is_feasible(bj)?  "feas":"inf") << std::endl;);
                
                  
            }
        } else {
            NOT_IMPLEMENTED_YET();
            m_column_buffer.clear();
            m_column_buffer.resize(A_r().row_count());
            m_mpq_lar_core_solver.m_r_solver.solve_Bd(j, m_column_buffer);
            for (unsigned i : m_column_buffer.m_index) {
                unsigned bj = m_mpq_lar_core_solver.m_r_basis[i];
                m_mpq_lar_core_solver.m_r_solver.add_delta_to_x_and_track_feasibility(bj, -m_column_buffer[i] * delta); 
            }
        }
    }

    template <typename ChangeReport>
    void set_value_for_nbasic_column_report(unsigned j,
                                            const impq & new_val,
                                            const ChangeReport& after) {

        lp_assert(!is_base(j));
        auto & x = m_mpq_lar_core_solver.m_r_x[j];        
        auto delta = new_val - x;
        x = new_val;
        after(j);
        change_basic_columns_dependend_on_a_given_nb_column_report(j, delta, after);
    }
    
    template <typename Blocker, typename ChangeReport>
    bool try_to_patch(lpvar j, const mpq& val,
                      const Blocker& is_blocked,
                      const ChangeReport& change_report) {
        if (is_base(j)) {
            TRACE("nla_solver", get_int_solver()->display_row_info(tout, row_of_basic_column(j)) << "\n";);
            remove_from_basis(j);
        }

        impq ival(val);
        if (is_blocked(j, ival))
            return false;
        TRACE("nla_solver", tout << "j" << j << " not blocked\n";);
        impq delta = get_column_value(j) - ival;
        for (auto c : A_r().column(j)) {
            unsigned row_index = c.var();
            const mpq & a = c.coeff();        
            unsigned rj = m_mpq_lar_core_solver.m_r_basis[row_index];      
            impq rj_new_val = a * delta + get_column_value(rj);
            // if (column_is_int(rj) && !rj_new_val.is_int())
            //     return false;
            if (is_blocked(rj, rj_new_val))
                return false;
        }

        set_value_for_nbasic_column_report(j, ival, change_report);
        return true;
    }
    inline bool column_has_upper_bound(unsigned j) const {
        return m_mpq_lar_core_solver.m_r_solver.column_has_upper_bound(j);
    }

    inline bool column_has_lower_bound(unsigned j) const {
        return m_mpq_lar_core_solver.m_r_solver.column_has_lower_bound(j);
    }    

    inline
    constraint_index get_column_upper_bound_witness(unsigned j) const {
        if (tv::is_term(j)) {
            j = m_var_register.external_to_local(j);
        }
        return m_columns_to_ul_pairs()[j].upper_bound_witness();
    }

    inline
    const impq& get_upper_bound(column_index j) const {
        return m_mpq_lar_core_solver.m_r_solver.m_upper_bounds[j];
    }

    inline
    const impq& get_lower_bound(column_index j) const {
        return m_mpq_lar_core_solver.m_r_solver.m_lower_bounds[j];
    }
    bool has_lower_bound(var_index var, constraint_index& ci, mpq& value, bool& is_strict) const;    
    bool has_upper_bound(var_index var, constraint_index& ci, mpq& value, bool& is_strict) const;
    bool has_value(var_index var, mpq& value) const;
    bool fetch_normalized_term_column(const lar_term& t, std::pair<mpq, lpvar>& ) const;
    unsigned map_term_index_to_column_index(unsigned j) const;
    bool column_is_fixed(unsigned j) const;
    bool column_is_free(unsigned j) const;
    unsigned column_to_reported_index(unsigned j) const;
    lp_settings & settings();
    lp_settings const & settings() const;
    void updt_params(params_ref const& p);
    column_type get_column_type(unsigned j) const { return m_mpq_lar_core_solver.m_column_types()[j]; }
    const impq & get_lower_bound(unsigned j) const { return m_mpq_lar_core_solver.m_r_lower_bounds()[j]; }
    const impq & get_upper_bound(unsigned j) const { return m_mpq_lar_core_solver.m_r_upper_bounds()[j]; }
    std::ostream& print_terms(std::ostream& out) const;
    std::ostream& print_term(lar_term const& term, std::ostream & out) const;
    static std::ostream& print_term_as_indices(lar_term const& term, std::ostream & out);
    std::ostream& print_constraint_indices_only(const lar_base_constraint * c, std::ostream & out) const;
    std::ostream& print_implied_bound(const implied_bound& be, std::ostream & out) const;
    std::ostream& print_values(std::ostream& out) const;
    std::ostream& display(std::ostream& out) const;

    bool init_model() const;
    mpq get_value(column_index const& j) const;
    mpq get_tv_value(tv const& t) const;
    impq get_tv_ivalue(tv const& t) const;
    void get_model(std::unordered_map<var_index, mpq> & variable_values) const;
    void get_rid_of_inf_eps();
    void get_model_do_not_care_about_diff_vars(std::unordered_map<var_index, mpq> & variable_values) const;
    std::string get_variable_name(var_index vi) const;
    void set_variable_name(var_index vi, std::string);
    inline unsigned number_of_vars() const { return m_var_register.size(); }
    inline bool is_base(unsigned j) const { return m_mpq_lar_core_solver.m_r_heading[j] >= 0; }
    inline const impq & column_lower_bound(unsigned j) const {
        return m_mpq_lar_core_solver.lower_bound(j);
    }

    void pivot_column_tableau(unsigned j, unsigned row_index);
    
    inline const impq & column_upper_bound(unsigned j) const {
        return m_mpq_lar_core_solver.upper_bound(j);
    }

    inline bool column_is_bounded(unsigned j) const {
        return m_mpq_lar_core_solver.column_is_bounded(j);
    }

    std::pair<constraint_index, constraint_index> add_equality(lpvar j, lpvar k);
    
    inline void get_bound_constraint_witnesses_for_column(unsigned j, constraint_index & lc, constraint_index & uc) const {
        const ul_pair & ul = m_columns_to_ul_pairs[j];
        lc = ul.lower_bound_witness();
        uc = ul.upper_bound_witness();
    }
    inline constraint_set const& constraints() const { return m_constraints; }
    void push();
    void pop();
    inline constraint_index get_column_lower_bound_witness(unsigned j) const {
        if (tv::is_term(j)) {
            j = m_var_register.external_to_local(j);
        }
        return m_columns_to_ul_pairs()[j].lower_bound_witness();
    }

    inline tv column2tv(column_index const& c) const {
        return tv::raw(column_to_reported_index(c));
    }
    
    inline std::ostream& print_column_info(unsigned j, std::ostream& out) const {
        m_mpq_lar_core_solver.m_r_solver.print_column_info(j, out);
        if (tv::is_term(j)) {
            print_term_as_indices(get_term(j), out) << "\n";
            
        } else if (column_corresponds_to_term(j)) { 
            const lar_term& t = get_term(m_var_register.local_to_external(j));
            print_term_as_indices(t, out) << "\n";
        }
        return out;
    }
    
    void subst_known_terms(lar_term*);

    inline std::ostream& print_column_bound_info(unsigned j, std::ostream& out) const {
        return m_mpq_lar_core_solver.m_r_solver.print_column_bound_info(j, out);
    }

    bool has_int_var() const;

    inline bool has_inf_int() const {
        for (unsigned j = 0; j < column_count(); j++) {
            if (column_is_int(j) && ! column_value_is_int(j))
                return true;
        }
        return false;
    }
    inline const vector<lar_term*> & terms() const { return m_terms; }
    inline lar_term const& term(unsigned i) const { return *m_terms[i]; }
    inline void set_int_solver(int_solver * int_slv) { m_int_solver = int_slv; }
    inline int_solver * get_int_solver() { return m_int_solver; }
    inline const int_solver * get_int_solver() const { return m_int_solver; }
    inline const lar_term & get_term(tv const& t) const { lp_assert(t.is_term()); return *m_terms[t.id()]; }
    lp_status find_feasible_solution();   
    void move_non_basic_columns_to_bounds(bool);
    bool move_non_basic_column_to_bounds(unsigned j, bool);
    inline bool r_basis_has_inf_int() const {
        for (unsigned j : r_basis()) {
            if (column_is_int(j) && ! column_value_is_int(j))
                return true;
        }
        return false;
    }
    void round_to_integer_solution();
    inline const row_strip<mpq> &  get_row(unsigned i) const { return A_r().m_rows[i]; }
    inline const column_strip &  get_column(unsigned i) const { return A_r().m_columns[i]; }
    bool row_is_correct(unsigned i) const;
    bool ax_is_correct() const;
    bool get_equality_and_right_side_for_term_on_current_x(tv const& t, mpq &rs, constraint_index& ci, bool &upper_bound) const;
    bool var_is_int(var_index v) const;
    inline const vector<int> & r_heading() const { return m_mpq_lar_core_solver.m_r_heading; }
    inline const vector<unsigned> & r_basis() const { return m_mpq_lar_core_solver.r_basis(); }
    inline const vector<unsigned> & r_nbasis() const { return m_mpq_lar_core_solver.r_nbasis(); }
    inline bool column_is_real(unsigned j) const { return !column_is_int(j); }	
    lp_status get_status() const;
    bool has_changed_columns() const { return !m_columns_with_changed_bounds.empty();  }
    void set_status(lp_status s);
    lp_status solve();
    void fill_explanation_from_crossed_bounds_column(explanation & evidence) const;
    bool term_is_used_as_row(unsigned term) const;
    bool tighten_term_bounds_by_delta(tv const& t, const impq&);
    lar_solver();
    void set_track_pivoted_rows(bool v);
    bool get_track_pivoted_rows() const;    
    virtual ~lar_solver();
    const vector<impq>& r_x() const { return m_mpq_lar_core_solver.m_r_x; }
    bool column_is_int(unsigned j) const;
    inline bool column_value_is_int(unsigned j) const { return m_mpq_lar_core_solver.m_r_x[j].is_int(); }
    inline static_matrix<mpq, impq> & A_r() { return m_mpq_lar_core_solver.m_r_A; }
    inline const static_matrix<mpq, impq> & A_r() const { return m_mpq_lar_core_solver.m_r_A; }
    // columns
    bool column_is_int(column_index const& j) const { return column_is_int((unsigned)j); }
//    const impq& get_ivalue(column_index const& j) const { return get_column_value(j); }
    const impq& get_column_value(column_index const& j) const { return m_mpq_lar_core_solver.m_r_x[j]; }
    inline
    var_index external_to_local(unsigned j) const {
        var_index local_j;
        if (m_var_register.external_is_used(j, local_j) ||
            m_term_register.external_is_used(j, local_j)) {
            return local_j;
        }
        else {
            return -1;
        }
    }
    unsigned usage_in_terms(column_index j) const {
        if (j >= m_usage_in_terms.size())
            return 0;
        return m_usage_in_terms[j];
    }
    friend int_solver;
    friend int_branch;
    
};
}
