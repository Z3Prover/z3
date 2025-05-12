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
    struct imp;
    imp* m_imp;

    ////////////////// methods ////////////////////////////////

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

    void clear_columns_with_changed_bounds();

    struct scoped_backup;
 public:
    const indexed_uint_set& columns_with_changed_bounds() const;
    void insert_to_columns_with_changed_bounds(unsigned j);
    const u_dependency* crossed_bounds_deps() const;
    u_dependency*& crossed_bounds_deps();

    lpvar crossed_bounds_column() const;
    lpvar& crossed_bounds_column();
        

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
    void update_column_type_and_bound_with_ub(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);
    void update_column_type_and_bound_with_no_ub(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);
    void update_bound_with_ub_lb(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);
    void update_bound_with_no_ub_lb(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);
    void update_bound_with_ub_no_lb(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);
    void update_bound_with_no_ub_no_lb(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep);
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
            zero_of_type<numeric_pair<mpq>>(),
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
    void set_upper_bound_witness(lpvar j, u_dependency* ci, impq const& high);
    void set_lower_bound_witness(lpvar j, u_dependency* ci, impq const& low);
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
    const lar_core_solver& get_core_solver() const;
    lar_core_solver& get_core_solver();
    lpvar to_column(unsigned ext_j) const;
    void fix_terms_with_rounded_columns();
    bool remove_from_basis(unsigned);
    lar_term get_term_to_maximize(unsigned ext_j) const;
    bool sum_first_coords(const lar_term& t, mpq& val) const;
    void register_normalized_term(const lar_term&, lpvar);
    void deregister_normalized_term(const lar_term&);

public:
    u_dependency* find_improved_bound(lpvar j, bool is_lower, mpq& bound);

    std::ostream& print_explanation(
        std::ostream& out, const explanation& exp, 
        std::function<std::string(lpvar)> var_str = [](lpvar j) { return std::string("j") + T_to_string(j); }) const;
    // this function just looks at the status
    bool is_feasible() const;

    const map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>>& fixed_var_table_int() const;
    const map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>>& fixed_var_table_real() const;

    bool find_in_fixed_tables(const rational& mpq, bool is_int, unsigned& j) const {
        return is_int ? fixed_var_table_int().find(mpq, j) : fixed_var_table_real().find(mpq, j);
    }

    template <typename T>
    void remove_non_fixed_from_table(T&);

    bool inside_bounds(lpvar, const impq&) const;

    void set_column_value(unsigned j, const impq& v);
    
    inline void set_column_value_test(unsigned j, const impq& v) {
        set_column_value(j, v);
    }

    lp_status maximize_term(unsigned j_or_term, impq& term_max);

    core_solver_pretty_printer<lp::mpq, lp::impq> pp(std::ostream& out) const;
    
    void get_infeasibility_explanation(explanation&) const;


    std::function<void(lpvar)> m_fixed_var_eh;
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
                SASSERT(witness);
                for (auto ci : flatten(witness))
                    bp.consume(a, ci);
            }
            }*/
    }

    void set_value_for_nbasic_column(unsigned j, const impq& new_val);

    void remove_fixed_vars_from_base();
    /**
     * \brief set j to basic (if not already basic)
     * return the rest of the row as t comprising of non-fixed variables and coeff as sum of fixed variables.
     * return false if j has no rows.
     */

    struct solution {
        unsigned j;
        lar_term t;
    };

    lpvar add_named_var(unsigned ext_j, bool is_integer, const std::string&);
    void solve_for(unsigned_vector const& js, vector<solution>& sol);
    void check_fixed(unsigned j);
    void solve_for(unsigned j, uint_set& tabu, vector<solution>& sol);

    unsigned get_base_column_in_row(unsigned row_index) const;
#ifdef Z3DEBUG
    bool fixed_base_removed_correctly() const;
#endif
    constraint_index mk_var_bound(lpvar j, lconstraint_kind kind, const mpq& right_side);
    void activate_check_on_equal(constraint_index, lpvar&);
    void activate(constraint_index);
    void random_update(unsigned sz, lpvar const* vars);
    void add_column_rows_to_touched_rows(lpvar j);
    const indexed_uint_set & touched_rows() const;
    indexed_uint_set & touched_rows();
    unsigned_vector& row_bounds_to_replay();
    template <typename T>
    void propagate_bounds_for_touched_rows(lp_bound_propagator<T>& bp) {
        if (settings().propagate_eqs()) {
            if (settings().random_next() % 10 == 0) 
                remove_fixed_vars_from_base();
            bp.clear_for_eq();
            for (unsigned i : touched_rows()) {
                unsigned offset_eqs = stats().m_offset_eqs;
                bp.cheap_eq_on_nbase(i);
                if (settings().get_cancel_flag())
                    return;
                if (stats().m_offset_eqs > offset_eqs)
                    row_bounds_to_replay().push_back(i);
            }
        }
        for (unsigned i : touched_rows()) {
            calculate_implied_bounds_for_row(i, bp);
            if (settings().get_cancel_flag())
                return;
        }
        touched_rows().reset();
    }
    void collect_more_rows_for_lp_propagation();
    template <typename T>
    void check_missed_propagations(lp_bound_propagator<T>& bp) {
        for (unsigned i = 0; i < A_r().row_count(); i++)
            if (!touched_rows().contains(i))
                if (0 < calculate_implied_bounds_for_row(i, bp)) {
                    verbose_stream() << i << ": " << get_row(i) << "\n";
                }
    }

    
    public:
    std::function<void (const lar_term*)> m_add_term_callback;
    std::function<void (unsigned)> m_update_column_bound_callback;  
    bool external_is_used(unsigned) const;
    void pop(unsigned k);
    trail_stack& trail();
    bool compare_values(lpvar j, lconstraint_kind kind, const mpq& right_side);
    lpvar add_term(const vector<std::pair<mpq, lpvar>>& coeffs, unsigned ext_i);
    void register_existing_terms();
    constraint_index add_var_bound(lpvar, lconstraint_kind, const mpq&);
    constraint_index add_var_bound_check_on_equal(lpvar, lconstraint_kind, const mpq&, lpvar&);

    lpvar add_var(unsigned ext_j, bool is_integer);
    void set_cut_strategy(unsigned cut_frequency);
    inline unsigned column_count() const { return A_r().column_count(); }
    lpvar local_to_external(lpvar idx) const; 
    bool column_associated_with_row(lpvar j) const;
    unsigned row_count() const { return A_r().row_count(); }
    bool var_is_registered(lpvar vj) const;
    void clear_inf_heap() {
        get_core_solver().m_r_solver.inf_heap().clear();
    }

    void pivot(int entering, int leaving) {
        get_core_solver().pivot(entering, leaving);
    }

    indexed_uint_set& basic_columns_with_changed_cost();

    template <typename ChangeReport>
    void change_basic_columns_dependend_on_a_given_nb_column_report(unsigned j,
                                                                    const numeric_pair<mpq>& delta,
                                                                    const ChangeReport& after) {
        for (const auto& c : A_r().m_columns[j]) {
            unsigned bj = get_core_solver().m_r_basis[c.var()];
            if (tableau_with_costs())
                basic_columns_with_changed_cost().insert(bj);
            get_core_solver().m_r_solver.add_delta_to_x_and_track_feasibility(bj, -A_r().get_val(c) * delta);
            after(bj);
            TRACE("change_x_del",
                  tout << "changed basis column " << bj << ", it is " << (get_core_solver().m_r_solver.column_is_feasible(bj) ? "feas" : "inf") << std::endl;);
        }
    }

    template <typename ChangeReport>
    void set_value_for_nbasic_column_report(unsigned j,
                                            const impq& new_val,
                                            const ChangeReport& after) {
        SASSERT(!is_base(j));
        auto& x = get_core_solver().r_x(j);
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
            unsigned rj = get_core_solver().m_r_basis[row_index];
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
        return get_core_solver().m_r_solver.column_has_upper_bound(j);
    }

    inline bool column_has_lower_bound(unsigned j) const {
        return get_core_solver().m_r_solver.column_has_lower_bound(j);
    }

    svector<constraint_index> const& flatten(u_dependency* d);
    void push_explanation(u_dependency* d, explanation& ex) {
        for (auto ci : flatten(d))
            ex.push_back(ci);
    }    
    
    const u_dependency_manager& dep_manager() const;
    u_dependency_manager& dep_manager();

    u_dependency* get_column_upper_bound_witness(unsigned j) const;
    
    const impq& get_upper_bound(lpvar j) const;
    const impq& get_lower_bound(lpvar j) const;
    mpq bound_span_x(lpvar j) const;
    bool has_lower_bound(lpvar var, u_dependency*& ci, mpq& value, bool& is_strict) const;
    bool has_upper_bound(lpvar var, u_dependency*& ci, mpq& value, bool& is_strict) const;
    bool has_bound_of_type(lpvar var, u_dependency*& ci, mpq& value, bool& is_strict, bool is_upper) const;
  
    bool has_value(lpvar var, mpq& value) const;
    bool fetch_normalized_term_column(const lar_term& t, std::pair<mpq, lpvar>&) const;
    bool column_is_fixed(unsigned j) const;
    bool column_is_free(unsigned j) const;
    bool column_is_feasible(unsigned j) const;
    lp_settings& settings();
    lp_settings const& settings() const;
    statistics& stats();

    void backup_x() { get_core_solver().backup_x(); }
    void restore_x() { get_core_solver().restore_x(); }

    void updt_params(params_ref const& p);
    column_type get_column_type(unsigned j) const { return get_core_solver().m_column_types()[j]; }
    const vector<column_type>&  get_column_types() const { return get_core_solver().m_column_types(); }
    std::ostream& print_terms(std::ostream& out) const;
    std::ostream& print_term(lar_term const& term, std::ostream& out) const;
    static std::ostream& print_term_as_indices(lar_term const& term, std::ostream& out);
    std::ostream& print_constraint_indices_only(const lar_base_constraint* c, std::ostream& out) const;
    std::ostream& print_implied_bound(const implied_bound& be, std::ostream& out) const;
    std::ostream& print_values(std::ostream& out) const;
    std::ostream& display(std::ostream& out) const;
    std::ostream& display_constraint(std::ostream& out, constraint_index ci) const;
    bool init_model() const;
    mpq from_model_in_impq_to_mpq(const impq& v) const;
    mpq get_value(lpvar j) const;
    void get_model(std::unordered_map<lpvar, mpq>& variable_values) const;
    void get_rid_of_inf_eps();
    void get_model_do_not_care_about_diff_vars(std::unordered_map<lpvar, mpq>& variable_values) const;
    std::string get_variable_name(lpvar vi) const override;
    void set_variable_name(lpvar vi, std::string);
    unsigned number_of_vars() const;
    inline bool is_base(unsigned j) const { return get_core_solver().m_r_heading[j] >= 0; }
    inline const impq& column_lower_bound(unsigned j) const {
        return get_core_solver().lower_bound(j);
    }

    inline const impq& column_upper_bound(unsigned j) const {
        return get_core_solver().upper_bound(j);
    }

    inline bool column_is_bounded(unsigned j) const {
        return get_core_solver().column_is_bounded(j);
    }

    bool check_feasible() const {
        return get_core_solver().m_r_solver.calc_current_x_is_feasible_include_non_basis();
    }

    bool are_equal(lpvar j, lpvar k);
    std::pair<constraint_index, constraint_index> add_equality(lpvar j, lpvar k);

    u_dependency* get_bound_constraint_witnesses_for_column(unsigned j);
    
    template <typename T>
    u_dependency* get_bound_constraint_witnesses_for_columns(const T& collection) {
        u_dependency* dep = nullptr;
        for (auto j : collection) {
            u_dependency* d = get_bound_constraint_witnesses_for_column(j);
            dep = dep_manager().mk_join(dep, d);
        }
        return dep;
    }

    std::ostream& print_expl(std::ostream& out, const explanation& exp) const {
        for (auto p : exp)
            constraints().display(
                out, [this](lpvar j) { return get_variable_name(j); }, p.ci());
        return out;
    }

    void explain_fixed_column(unsigned j, explanation& ex);
    u_dependency* join_deps(u_dependency* a, u_dependency *b) { return dep_manager().mk_join(a, b); }
    const constraint_set & constraints() const;
    void push();
    void pop();

    u_dependency* get_column_lower_bound_witness(unsigned j) const;
    
    bool column_has_term(lpvar j) const;

    std::ostream& print_column_info(unsigned j, std::ostream& out, bool print_expl = false) const;

    std::ostream& display_column_explanation(std::ostream& out, unsigned j) const;
    
    void subst_known_terms(lar_term*);

    std::ostream& print_column_bound_info(unsigned j, std::ostream& out) const {
        return get_core_solver().m_r_solver.print_column_bound_info(j, out);
    }

    bool has_int_var() const;

    inline bool has_inf_int() const {
        for (unsigned j = 0; j < column_count(); j++) {
            if (column_is_int(j) && !column_value_is_int(j))
                return true;
        }
        return false;
    }

    const vector<lar_term*>& terms() const;
    
    void set_int_solver(int_solver* int_slv);
    int_solver* get_int_solver();
    const int_solver* get_int_solver() const;
    const lar_term& get_term(lpvar j) const;
    lp_status find_feasible_solution();
    void move_non_basic_columns_to_bounds();
    bool move_non_basic_column_to_bounds(unsigned j);
    bool move_lpvar_to_value(lpvar j, mpq const& value);
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
    inline const std_vector<int>& r_heading() const { return get_core_solver().m_r_heading; }
    inline const vector<unsigned>& r_basis() const { return get_core_solver().r_basis(); }
    inline const vector<unsigned>& r_nbasis() const { return get_core_solver().r_nbasis(); }
    inline bool column_is_real(unsigned j) const { return !column_is_int(j); }
    lp_status get_status() const;
    bool has_changed_columns() const;
    void set_status(lp_status s);
    lp_status solve();
    void fill_explanation_from_crossed_bounds_column(explanation& evidence) const;
    bool tighten_term_bounds_by_delta(lpvar j, const impq&);
    lar_solver();
    void track_touched_rows(bool v);
    bool touched_rows_are_tracked() const;
    ~lar_solver() override;
    const vector<impq>& r_x() const { return get_core_solver().r_x(); }
    bool column_is_int(unsigned j) const;
    inline bool column_value_is_int(unsigned j) const { return get_core_solver().r_x(j).is_int(); }
    inline static_matrix<mpq, impq>& A_r() { return get_core_solver().m_r_A; }
    inline const static_matrix<mpq, impq>& A_r() const { return get_core_solver().m_r_A; }
    // columns
    const impq& get_column_value(lpvar j) const { return get_core_solver().r_x(j); }
    lpvar external_to_local(unsigned j) const;
    unsigned usage_in_terms(lpvar j) const;

    std::string get_bounds_string(unsigned j) const;
    void write_bound_lemma(unsigned j, bool is_low, const std::string & location, std::ostream & out) const;

    std::function<void (const indexed_uint_set& columns_with_changed_bound)> m_find_monics_with_changed_bounds_func = nullptr;
    friend int_solver;
    friend int_branch;
    friend imp;

};
}  // namespace lp
