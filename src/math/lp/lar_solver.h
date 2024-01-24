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
#include <algorithm>
#include <functional>
#include <stack>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#include "math/lp/bound_analyzer_on_row.h"
#include "math/lp/implied_bound.h"
#include "math/lp/int_solver.h"
#include "math/lp/lar_constraints.h"
#include "math/lp/lar_core_solver.h"
#include "math/lp/lp_bound_propagator.h"
#include "math/lp/lp_primal_core_solver.h"
#include "math/lp/lp_types.h"
#include "math/lp/nra_solver.h"
#include "math/lp/numeric_pair.h"
#include "math/lp/random_updater.h"
#include "math/lp/stacked_vector.h"
#include "util/buffer.h"
#include "util/debug.h"
#include "util/stacked_value.h"
#include "util/vector.h"
#include "util/trail.h"

namespace lp {

class int_branch;
class int_solver;

    
class lar_solver : public column_namer {
    struct term_hasher {
        std::size_t operator()(const lar_term& t) const {
            using std::hash;
            using std::size_t;
            using std::string;
            size_t seed = 0;
            int i = 0;
            for (const auto p : t) {
                hash_combine(seed, (unsigned)p.j());
                hash_combine(seed, p.coeff());
                if (i++ > 10)
                    break;
            }
            return seed;
        }
    };

    struct term_comparer {
        bool operator()(const lar_term& a, const lar_term& b) const {
            return a == b;
        }
    };

    //////////////////// fields //////////////////////////
    trail_stack m_trail;
    lp_settings m_settings;
    lp_status m_status = lp_status::UNKNOWN;
    stacked_value<simplex_strategy_enum> m_simplex_strategy;
    // such can be found at the initialization step: u < l
    lpvar m_crossed_bounds_column = null_lpvar;
    u_dependency* m_crossed_bounds_deps = nullptr;
    lar_core_solver m_mpq_lar_core_solver;
    int_solver* m_int_solver = nullptr;
    bool m_need_register_terms = false;
    var_register m_var_register;
    svector<column> m_columns;
    constraint_set m_constraints;
    // the set of column indices j such that bounds have changed for j
    indexed_uint_set m_columns_with_changed_bounds;
    indexed_uint_set m_touched_rows;
    unsigned_vector m_row_bounds_to_replay;
    u_dependency_manager m_dependencies;
    svector<constraint_index> m_tmp_dependencies;

    indexed_uint_set m_basic_columns_with_changed_cost;
    // these are basic columns with the value changed, so the corresponding row in the tableau
    // does not sum to zero anymore
    indexed_uint_set m_incorrect_columns;
    // copy of m_r_solver.inf_heap()
    unsigned_vector m_inf_index_copy;
    vector<lar_term*> m_terms;
    indexed_vector<mpq> m_column_buffer;
    std::unordered_map<lar_term, std::pair<mpq, unsigned>, term_hasher, term_comparer>
        m_normalized_terms_to_columns;
    vector<impq> m_backup_x;
    stacked_vector<unsigned> m_usage_in_terms;
    // ((x[j], is_int(j))->j)  for fixed j, used in equalities propagation
    // maps values to integral fixed vars
    map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>> m_fixed_var_table_int;
    // maps values to non-integral fixed vars
    map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>> m_fixed_var_table_real;
    // the set of fixed variables which are also base variables
    indexed_uint_set                                   m_fixed_base_var_set;
    // end of fields

    ////////////////// nested structs /////////////////////////
    struct undo_add_column;

    ////////////////// methods ////////////////////////////////

    static bool valid_index(unsigned j) { return static_cast<int>(j) >= 0; }
    bool row_has_a_big_num(unsigned i) const;
    // init region
    void register_new_external_var(unsigned ext_v, bool is_int);
    bool term_is_int(const lar_term* t) const;
    bool term_is_int(const vector<std::pair<mpq, unsigned int>>& coeffs) const;
    void add_non_basic_var_to_core_fields(unsigned ext_j, bool is_int);
    void add_new_var_to_core_fields_for_mpq(bool register_in_basis);
    mpq adjust_bound_for_int(lpvar j, lconstraint_kind&, const mpq&);

    // terms
    bool all_vars_are_registered(const vector<std::pair<mpq, lpvar>>& coeffs);
    bool term_coeffs_are_ok(const vector<std::pair<mpq, lpvar>>& coeffs);
    void add_row_from_term_no_constraint(lar_term* term, unsigned term_ext_index);
    void add_basic_var_to_core_fields();
    bool compare_values(impq const& lhs, lconstraint_kind k, const mpq& rhs);

    inline void clear_columns_with_changed_bounds() { m_columns_with_changed_bounds.reset(); }
 public:
    const auto& columns_with_changed_bounds() const { return m_columns_with_changed_bounds; }
    void insert_to_columns_with_changed_bounds(unsigned j);
    const u_dependency* crossed_bounds_deps() const { return m_crossed_bounds_deps;}
    u_dependency*& crossed_bounds_deps() { return m_crossed_bounds_deps;}

    lpvar crossed_bounds_column() const { return m_crossed_bounds_column; }
    lpvar& crossed_bounds_column() { return m_crossed_bounds_column; } 
        

 private:
    bool validate_bound(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);   
    void add_dep_constraints_to_solver(lar_solver& ls, u_dependency* dep);
    void add_bound_negation_to_solver(lar_solver& ls, lpvar j, lconstraint_kind kind, const mpq& right_side);
    void add_constraint_to_validate(lar_solver& ls, constraint_index ci);
    bool m_validate_blocker = false;
    void update_column_type_and_bound_check_on_equal(unsigned j, const mpq& right_side, constraint_index ci, unsigned&);
    void update_column_type_and_bound(unsigned j, const mpq& right_side, constraint_index ci);
 public:   
    bool validate_blocker() const { return m_validate_blocker; }
    bool & validate_blocker() { return m_validate_blocker; }   
	void update_column_type_and_bound(unsigned j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);
 private:
    void require_nbasis_sort() { m_mpq_lar_core_solver.m_r_solver.m_nbasis_sort_counter = 0; }   
    void update_column_type_and_bound_with_ub(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);
    void update_column_type_and_bound_with_no_ub(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);
    void update_bound_with_ub_lb(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);
    void update_bound_with_no_ub_lb(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);
    void update_bound_with_ub_no_lb(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);
    void update_bound_with_no_ub_no_lb(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);
    void register_in_fixed_var_table(unsigned, unsigned&);
    void remove_non_fixed_from_fixed_var_table();
    constraint_index add_var_bound_on_constraint_for_term(lpvar j, lconstraint_kind kind, const mpq& right_side);
    void set_crossed_bounds_column_and_deps(unsigned j, bool lower_bound, u_dependency* dep);
    unsigned row_of_basic_column(unsigned) const;
    bool sizes_are_correct() const;
    bool implied_bound_is_correctly_explained(implied_bound const& be, const vector<std::pair<mpq, unsigned>>& explanation) const;

    template <typename T>
    unsigned calculate_implied_bounds_for_row(unsigned row_index, lp_bound_propagator<T>& bp) {
        if (A_r().m_rows[row_index].size() > settings().max_row_length_for_bound_propagation || row_has_a_big_num(row_index))
            return 0;

        return bound_analyzer_on_row<row_strip<mpq>, lp_bound_propagator<T>>::analyze_row(
            A_r().m_rows[row_index],
            null_ci,
            zero_of_type<numeric_pair<mpq>>(),
            row_index,
            bp);
    }

    static void clean_popped_elements_for_heap(unsigned n, lpvar_heap& set);
    static void clean_popped_elements(unsigned n, indexed_uint_set& set);
    bool maximize_term_on_tableau(const lar_term& term, impq& term_max);
    bool costs_are_zeros_for_r_solver() const;
    bool reduced_costs_are_zeroes_for_r_solver() const;
    void set_costs_to_zero(const lar_term& term);
    void prepare_costs_for_r_solver(const lar_term& term);
    bool maximize_term_on_feasible_r_solver(lar_term& term, impq& term_max, vector<std::pair<mpq,lpvar>>* max_coeffs);
    u_dependency* get_dependencies_of_maximum(const vector<std::pair<mpq,lpvar>>& max_coeffs);
    
    void pop_core_solver_params();
    void pop_core_solver_params(unsigned k);
    void set_upper_bound_witness(lpvar j, u_dependency* ci);
    void set_lower_bound_witness(lpvar j, u_dependency* ci);
    void substitute_terms_in_linear_expression(const vector<std::pair<mpq, lpvar>>& left_side_with_terms,
                                               vector<std::pair<mpq, lpvar>>& left_side) const;

    bool use_tableau_costs() const;
    bool tableau_with_costs() const;
    bool costs_are_used() const;
    void change_basic_columns_dependend_on_a_given_nb_column(unsigned j, const numeric_pair<mpq>& delta);
    void update_x_and_inf_costs_for_column_with_changed_bounds(unsigned j);
    void add_touched_row(unsigned rid);
    void detect_rows_with_changed_bounds_for_column(unsigned j);
    void detect_rows_with_changed_bounds();

    void update_x_and_inf_costs_for_columns_with_changed_bounds_tableau();
    void solve_with_core_solver();
    numeric_pair<mpq> get_basic_var_value_from_row(unsigned i);
    bool all_constrained_variables_are_registered(const vector<std::pair<mpq, lpvar>>& left_side);
    bool all_constraints_hold() const;
    bool constraint_holds(const lar_base_constraint& constr, std::unordered_map<lpvar, mpq>& var_map) const;
    static void register_in_map(std::unordered_map<lpvar, mpq>& coeffs, const lar_base_constraint& cn, const mpq& a);
    static void register_monoid_in_map(std::unordered_map<lpvar, mpq>& coeffs, const mpq& a, unsigned j);
    bool the_left_sides_sum_to_zero(const vector<std::pair<mpq, unsigned>>& evidence) const;
    bool explanation_is_correct(explanation&) const;
    bool inf_explanation_is_correct() const;
    mpq sum_of_right_sides_of_explanation(explanation&) const;
    void get_infeasibility_explanation_for_inf_sign(
        explanation& exp,
        const vector<std::pair<mpq, unsigned>>& inf_row,
        int inf_sign) const;
    mpq get_left_side_val(const lar_base_constraint& cns, const std::unordered_map<lpvar, mpq>& var_map) const;
    void fill_var_set_for_random_update(unsigned sz, lpvar const* vars, vector<unsigned>& column_list);
    bool column_represents_row_in_tableau(unsigned j);
    void make_sure_that_the_bottom_right_elem_not_zero_in_tableau(unsigned i, unsigned j);
    void remove_last_row_and_column_from_tableau(unsigned j);
    void remove_last_column_from_A();

    void remove_last_column_from_basis_tableau(unsigned j);
    void remove_last_column_from_tableau();
    void clean_inf_heap_of_r_solver_after_pop();
    inline bool column_value_is_integer(unsigned j) const { return get_column_value(j).is_int(); }
    bool model_is_int_feasible() const;

    bool bound_is_integer_for_integer_column(unsigned j, const mpq& right_side) const;
    inline lar_core_solver& get_core_solver() { return m_mpq_lar_core_solver; }
    lpvar to_column(unsigned ext_j) const;
    void fix_terms_with_rounded_columns();
    bool remove_from_basis(unsigned);
    lar_term get_term_to_maximize(unsigned ext_j) const;
    bool sum_first_coords(const lar_term& t, mpq& val) const;
    void register_normalized_term(const lar_term&, lpvar);
    void deregister_normalized_term(const lar_term&);

    mutable std::unordered_set<impq> m_set_of_different_pairs;
    mutable std::unordered_set<mpq> m_set_of_different_singles;
    mutable mpq m_delta;

public:
    u_dependency* find_improved_bound(lpvar j, bool is_lower, mpq& bound);

    std::ostream& print_explanation(
        std::ostream& out, const explanation& exp, 
        std::function<std::string(lpvar)> var_str = [](lpvar j) { return std::string("j") + T_to_string(j); }) const;
    // this function just looks at the status
    bool is_feasible() const;

    const map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>>& fixed_var_table_int() const {
        return m_fixed_var_table_int;
    }

    const map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>>& fixed_var_table_real() const {
        return m_fixed_var_table_real;
    }

    map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>>& fixed_var_table_real() {
        return m_fixed_var_table_real;
    }

    bool find_in_fixed_tables(const rational& mpq, bool is_int, unsigned& j) const {
        return is_int ? fixed_var_table_int().find(mpq, j) : fixed_var_table_real().find(mpq, j);
    }

    template <typename T>
    void remove_non_fixed_from_table(T&);

    bool inside_bounds(lpvar, const impq&) const;

    inline void set_column_value(unsigned j, const impq& v) {
        m_mpq_lar_core_solver.m_r_solver.update_x(j, v);
    }

    inline void set_column_value_test(unsigned j, const impq& v) {
        set_column_value(j, v);
    }

    lpvar add_named_var(unsigned ext_j, bool is_integer, const std::string&);

    lp_status maximize_term(unsigned j_or_term, impq& term_max);

    inline core_solver_pretty_printer<lp::mpq, lp::impq> pp(std::ostream& out) const {
        return core_solver_pretty_printer<lp::mpq, lp::impq>(m_mpq_lar_core_solver.m_r_solver, out);
    }

    void get_infeasibility_explanation(explanation&) const;

    inline void backup_x() { m_backup_x = m_mpq_lar_core_solver.m_r_x; }

    inline void restore_x() { m_mpq_lar_core_solver.m_r_x = m_backup_x; }

    template <typename T>
    void explain_implied_bound(const implied_bound& ib, lp_bound_propagator<T>& bp) {
        u_dependency* dep = ib.explain_implied();
        for (auto ci : flatten(dep))
            bp.consume(mpq(1), ci); // TODO: flatten should provide the coefficients
        /*
        if (ib.m_is_monic) {
            NOT_IMPLEMENTED_YET();
        } else {
            unsigned i = ib.m_row_or_term_index;
            int bound_sign = (ib.m_is_lower_bound ? 1 : -1);
            int j_sign = (ib.m_coeff_before_j_is_pos ? 1 : -1) * bound_sign;
            unsigned bound_j = ib.m_j;
            if (tv::is_term(bound_j))
                bound_j = m_var_register.external_to_local(bound_j);

            for (auto const& r : get_row(i)) {
                unsigned j = r.var();
                if (j == bound_j)
                    continue;
                mpq const& a = r.coeff();
                int a_sign = is_pos(a) ? 1 : -1;
                int sign = j_sign * a_sign;
                const column& ul = m_columns[j];
                auto* witness = sign > 0 ? ul.upper_bound_witness() : ul.lower_bound_witness();
                lp_assert(witness);
                for (auto ci : flatten(witness))
                    bp.consume(a, ci);
            }
            }*/
    }

    void set_value_for_nbasic_column(unsigned j, const impq& new_val);

    void remove_fixed_vars_from_base();

    inline unsigned get_base_column_in_row(unsigned row_index) const {
        return m_mpq_lar_core_solver.m_r_solver.get_base_column_in_row(row_index);
    }
#ifdef Z3DEBUG
    bool fixed_base_removed_correctly() const;
#endif
    constraint_index mk_var_bound(lpvar j, lconstraint_kind kind, const mpq& right_side);
    void activate_check_on_equal(constraint_index, lpvar&);
    void activate(constraint_index);
    void random_update(unsigned sz, lpvar const* vars);
    void add_column_rows_to_touched_rows(lpvar j);
    template <typename T>
    void propagate_bounds_for_touched_rows(lp_bound_propagator<T>& bp) {
        if (settings().propagate_eqs()) {
            if (settings().random_next() % 10 == 0) 
                remove_fixed_vars_from_base();
            bp.clear_for_eq();
            for (unsigned i : m_touched_rows) {
                unsigned offset_eqs = stats().m_offset_eqs;
                bp.cheap_eq_on_nbase(i);
                if (settings().get_cancel_flag())
                    return;
                if (stats().m_offset_eqs > offset_eqs)
                    m_row_bounds_to_replay.push_back(i);
            }
        }
        for (unsigned i : m_touched_rows) {
            calculate_implied_bounds_for_row(i, bp);
            if (settings().get_cancel_flag())
                return;
        }
        m_touched_rows.reset();
    }
    void collect_more_rows_for_lp_propagation();
    template <typename T>
    void check_missed_propagations(lp_bound_propagator<T>& bp) {
        for (unsigned i = 0; i < A_r().row_count(); i++)
            if (!m_touched_rows.contains(i))
                if (0 < calculate_implied_bounds_for_row(i, bp)) {
                    verbose_stream() << i << ": " << get_row(i) << "\n";
                }
    }

    bool external_is_used(unsigned) const;
    void pop(unsigned k);
    unsigned num_scopes() const { return m_trail.get_num_scopes(); }
    bool compare_values(lpvar j, lconstraint_kind kind, const mpq& right_side);
    lpvar add_term(const vector<std::pair<mpq, lpvar>>& coeffs, unsigned ext_i);
    void register_existing_terms();
    constraint_index add_var_bound(lpvar, lconstraint_kind, const mpq&);
    constraint_index add_var_bound_check_on_equal(lpvar, lconstraint_kind, const mpq&, lpvar&);

    lpvar add_var(unsigned ext_j, bool is_integer);
    void set_cut_strategy(unsigned cut_frequency);
    inline unsigned column_count() const { return A_r().column_count(); }
    inline lpvar local_to_external(lpvar idx) const {
        return m_var_register.local_to_external(idx);
    }
    inline bool column_associated_with_row(lpvar j) const { return m_columns[j].associated_with_row(); }
    inline unsigned row_count() const { return A_r().row_count(); }
    bool var_is_registered(lpvar vj) const;
    void clear_inf_heap() {
        m_mpq_lar_core_solver.m_r_solver.inf_heap().clear();
    }

    void pivot(int entering, int leaving) {
        m_mpq_lar_core_solver.pivot(entering, leaving);
    }

    template <typename ChangeReport>
    void change_basic_columns_dependend_on_a_given_nb_column_report(unsigned j,
                                                                    const numeric_pair<mpq>& delta,
                                                                    const ChangeReport& after) {
        for (const auto& c : A_r().m_columns[j]) {
            unsigned bj = m_mpq_lar_core_solver.m_r_basis[c.var()];
            if (tableau_with_costs())
                m_basic_columns_with_changed_cost.insert(bj);
            m_mpq_lar_core_solver.m_r_solver.add_delta_to_x_and_track_feasibility(bj, -A_r().get_val(c) * delta);
            after(bj);
            TRACE("change_x_del",
                  tout << "changed basis column " << bj << ", it is " << (m_mpq_lar_core_solver.m_r_solver.column_is_feasible(bj) ? "feas" : "inf") << std::endl;);
        }
    }

    template <typename ChangeReport>
    void set_value_for_nbasic_column_report(unsigned j,
                                            const impq& new_val,
                                            const ChangeReport& after) {
        lp_assert(!is_base(j));
        auto& x = m_mpq_lar_core_solver.m_r_x[j];
        auto delta = new_val - x;
        x = new_val;
        after(j);
        change_basic_columns_dependend_on_a_given_nb_column_report(j, delta, after);
    }

    template <typename Blocker, typename ChangeReport>
    bool try_to_patch(lpvar j, const mpq& val,
                      const Blocker& is_blocked,
                      const ChangeReport& change_report) {
        if (is_base(j))  {
            TRACE("nla_solver", get_int_solver()->display_row_info(tout, row_of_basic_column(j)) << "\n";);
            if (!remove_from_basis(j))
               return false;
        }

        impq ival(val);
        if (is_blocked(j, ival))
            return false;
        TRACE("nla_solver", tout << "j" << j << " not blocked\n";);
        impq delta = get_column_value(j) - ival;
        for (auto c : A_r().column(j)) {
            unsigned row_index = c.var();
            const mpq& a = c.coeff();
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

    svector<constraint_index> const& flatten(u_dependency* d) {
        m_tmp_dependencies.reset();
        m_dependencies.linearize(d, m_tmp_dependencies);
        return m_tmp_dependencies;
    }

    void push_explanation(u_dependency* d, explanation& ex) {
        for (auto ci : flatten(d))
            ex.push_back(ci);
    }

    u_dependency_manager& dep_manager() { return m_dependencies; }

    inline u_dependency* get_column_upper_bound_witness(unsigned j) const {
         return m_columns[j].upper_bound_witness();
    }

    inline const impq& get_upper_bound(lpvar j) const {
        return m_mpq_lar_core_solver.m_r_solver.m_upper_bounds[j];
    }

    inline const impq& get_lower_bound(lpvar j) const {
        return m_mpq_lar_core_solver.m_r_solver.m_lower_bounds[j];
    }

    inline mpq bound_span_x(lpvar j) const {
        return m_mpq_lar_core_solver.m_r_solver.m_upper_bounds[j].x - m_mpq_lar_core_solver.m_r_solver.m_lower_bounds[j].x;
    }
    
    bool has_lower_bound(lpvar var, u_dependency*& ci, mpq& value, bool& is_strict) const;
    bool has_upper_bound(lpvar var, u_dependency*& ci, mpq& value, bool& is_strict) const;
    bool has_value(lpvar var, mpq& value) const;
    bool fetch_normalized_term_column(const lar_term& t, std::pair<mpq, lpvar>&) const;
    bool column_is_fixed(unsigned j) const;
    bool column_is_free(unsigned j) const;
    bool column_is_feasible(unsigned j) const { return m_mpq_lar_core_solver.m_r_solver.column_is_feasible(j);}
    lp_settings& settings();
    lp_settings const& settings() const;
    statistics& stats();

    void updt_params(params_ref const& p);
    column_type get_column_type(unsigned j) const { return m_mpq_lar_core_solver.m_column_types()[j]; }
    const vector<column_type>&  get_column_types() const { return m_mpq_lar_core_solver.m_column_types(); }
    std::ostream& print_terms(std::ostream& out) const;
    std::ostream& print_term(lar_term const& term, std::ostream& out) const;
    static std::ostream& print_term_as_indices(lar_term const& term, std::ostream& out);
    std::ostream& print_constraint_indices_only(const lar_base_constraint* c, std::ostream& out) const;
    std::ostream& print_implied_bound(const implied_bound& be, std::ostream& out) const;
    std::ostream& print_values(std::ostream& out) const;
    std::ostream& display(std::ostream& out) const;
    std::ostream& display_constraint(std::ostream& out, constraint_index ci) const {
        return m_constraints.display(out, ci);
    }
    bool init_model() const;
    mpq from_model_in_impq_to_mpq(const impq& v) const { return v.x + m_delta * v.y; }
    mpq get_value(lpvar j) const;
    void get_model(std::unordered_map<lpvar, mpq>& variable_values) const;
    void get_rid_of_inf_eps();
    void get_model_do_not_care_about_diff_vars(std::unordered_map<lpvar, mpq>& variable_values) const;
    std::string get_variable_name(lpvar vi) const override;
    void set_variable_name(lpvar vi, std::string);
    inline unsigned number_of_vars() const { return m_var_register.size(); }
    inline bool is_base(unsigned j) const { return m_mpq_lar_core_solver.m_r_heading[j] >= 0; }
    inline const impq& column_lower_bound(unsigned j) const {
        return m_mpq_lar_core_solver.lower_bound(j);
    }

    inline const impq& column_upper_bound(unsigned j) const {
        return m_mpq_lar_core_solver.upper_bound(j);
    }

    inline bool column_is_bounded(unsigned j) const {
        return m_mpq_lar_core_solver.column_is_bounded(j);
    }

    bool check_feasible() const {
        return m_mpq_lar_core_solver.m_r_solver.calc_current_x_is_feasible_include_non_basis();
    }

    std::pair<constraint_index, constraint_index> add_equality(lpvar j, lpvar k);

    u_dependency* get_bound_constraint_witnesses_for_column(unsigned j) {
        const column& ul = m_columns[j];
        return m_dependencies.mk_join(ul.lower_bound_witness(), ul.upper_bound_witness());
    }
    template <typename T>
    u_dependency* get_bound_constraint_witnesses_for_columns(const T& collection) {
        u_dependency* dep = nullptr;
        for (auto j : collection) {
            u_dependency* d = get_bound_constraint_witnesses_for_column(j);
            dep = m_dependencies.mk_join(dep, d);
        }
        return dep;
    }
    u_dependency* join_deps(u_dependency* a, u_dependency *b) { return m_dependencies.mk_join(a, b); }
    inline constraint_set const& constraints() const { return m_constraints; }
    void push();
    void pop();

    inline u_dependency* get_column_lower_bound_witness(unsigned j) const {
        return m_columns[j].lower_bound_witness();
    }
    inline bool column_has_term(lpvar j) const { return m_columns[j].term() != nullptr; }
    inline std::ostream& print_column_info(unsigned j, std::ostream& out) const {
        m_mpq_lar_core_solver.m_r_solver.print_column_info(j, out);
        if (column_has_term(j)) {
            print_term_as_indices(get_term(j), out) << "\n";

        } else if (column_has_term(j)) {
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
            if (column_is_int(j) && !column_value_is_int(j))
                return true;
        }
        return false;
    }
    inline const vector<lar_term*>& terms() const { return m_terms; }
    
    inline void set_int_solver(int_solver* int_slv) { m_int_solver = int_slv; }
    inline int_solver* get_int_solver() { return m_int_solver; }
    inline const int_solver* get_int_solver() const { return m_int_solver; }
    inline const lar_term& get_term(lpvar j) const {
        return *m_columns[j].term();
    }
    lp_status find_feasible_solution();
    void move_non_basic_columns_to_bounds();
    bool move_non_basic_column_to_bounds(unsigned j);
    inline bool r_basis_has_inf_int() const {
        for (unsigned j : r_basis()) {
            if (column_is_int(j) && !column_value_is_int(j))
                return true;
        }
        return false;
    }
    void round_to_integer_solution();
    inline const row_strip<mpq>& get_row(unsigned i) const { return A_r().m_rows[i]; }
    inline const row_strip<mpq>& basic2row(unsigned i) const { return A_r().m_rows[row_of_basic_column(i)]; }
    inline const column_strip& get_column(unsigned i) const { return A_r().m_columns[i]; }
    bool row_is_correct(unsigned i) const;
    bool ax_is_correct() const;
    bool get_equality_and_right_side_for_term_on_current_x(lpvar j, mpq& rs, u_dependency*& ci, bool& upper_bound) const;
    bool var_is_int(lpvar v) const;
    inline const vector<int>& r_heading() const { return m_mpq_lar_core_solver.m_r_heading; }
    inline const vector<unsigned>& r_basis() const { return m_mpq_lar_core_solver.r_basis(); }
    inline const vector<unsigned>& r_nbasis() const { return m_mpq_lar_core_solver.r_nbasis(); }
    inline bool column_is_real(unsigned j) const { return !column_is_int(j); }
    lp_status get_status() const;
    bool has_changed_columns() const { return !m_columns_with_changed_bounds.empty(); }
    void set_status(lp_status s);
    lp_status solve();
    void fill_explanation_from_crossed_bounds_column(explanation& evidence) const;
    bool term_is_used_as_row(unsigned term) const;
    bool tighten_term_bounds_by_delta(lpvar j, const impq&);
    lar_solver();
    void track_touched_rows(bool v);
    bool touched_rows_are_tracked() const;
    ~lar_solver() override;
    const vector<impq>& r_x() const { return m_mpq_lar_core_solver.m_r_x; }
    bool column_is_int(unsigned j) const;
    inline bool column_value_is_int(unsigned j) const { return m_mpq_lar_core_solver.m_r_x[j].is_int(); }
    inline static_matrix<mpq, impq>& A_r() { return m_mpq_lar_core_solver.m_r_A; }
    inline const static_matrix<mpq, impq>& A_r() const { return m_mpq_lar_core_solver.m_r_A; }
    // columns
    const impq& get_column_value(lpvar j) const { return m_mpq_lar_core_solver.m_r_x[j]; }
    inline lpvar external_to_local(unsigned j) const {
        lpvar local_j;
        if (m_var_register.external_is_used(j, local_j)) {
            return local_j;
        } else {
            return -1;
        }
    }
    unsigned usage_in_terms(lpvar j) const {
        if (j >= m_usage_in_terms.size())
            return 0;
        return m_usage_in_terms[j];
    }
    std::function<void (const indexed_uint_set& columns_with_changed_bound)> m_find_monics_with_changed_bounds_func = nullptr;
    friend int_solver;
    friend int_branch;
};
}  // namespace lp
