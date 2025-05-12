/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner, Lev Nachmanson
*/
#include "math/lp/lar_solver.h"
#include "smt/params/smt_params_helper.hpp"
#include "lar_solver.h"


namespace lp {
    struct column_update {
        bool m_is_upper;
        unsigned m_j; 
        impq m_bound;
        column m_column;
    };
    
    struct lar_solver::imp {
        struct undo_add_column;
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

        lar_solver &lra;
        var_register m_var_register;
        svector<column> m_columns;
        vector<column_update> m_column_updates;
        trail_stack m_trail;
        lp_settings m_settings;
        lp_status m_status = lp_status::UNKNOWN;
        stacked_value<simplex_strategy_enum> m_simplex_strategy;
        lar_core_solver m_mpq_lar_core_solver;
        int_solver* m_int_solver = nullptr;
        bool m_need_register_terms = false;
        
        constraint_set m_constraints;
        indexed_uint_set m_columns_with_changed_bounds;
        indexed_uint_set m_touched_rows;
        unsigned_vector m_row_bounds_to_replay;
        u_dependency_manager m_dependencies;
        svector<constraint_index> m_tmp_dependencies;

        u_dependency* m_crossed_bounds_deps = nullptr;
        lpvar m_crossed_bounds_column = null_lpvar;
        
        indexed_uint_set m_basic_columns_with_changed_cost;
        indexed_uint_set m_incorrect_columns;
        unsigned_vector m_inf_index_copy;
        vector<lar_term*> m_terms;
        indexed_vector<mpq> m_column_buffer;
        std::unordered_map<lar_term, std::pair<mpq, unsigned>, term_hasher, term_comparer>
        m_normalized_terms_to_columns;

        stacked_vector<unsigned> m_usage_in_terms;
        map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>> m_fixed_var_table_int;
        map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>> m_fixed_var_table_real;
        indexed_uint_set m_fixed_base_var_set;
        
        mutable std::unordered_set<impq> m_set_of_different_pairs;
        mutable std::unordered_set<mpq> m_set_of_different_singles;
        mutable mpq m_delta;

        bool m_validate_blocker = false;

        
        void set_r_upper_bound(unsigned j, const impq& b) {
            m_mpq_lar_core_solver.m_r_upper_bounds[j] = b;
        }
        void set_r_lower_bound(unsigned j, const impq& b) {
            m_mpq_lar_core_solver.m_r_lower_bounds[j] = b;
        }
        
        imp(lar_solver& s) : 
            lra(s),
            m_mpq_lar_core_solver(m_settings, s),
            m_constraints(m_dependencies, s) {}

        void set_column(unsigned j, const column& c) {
            m_columns[j] = c;
        }
        
        struct column_update_trail : public trail {
            imp& m_imp;
            column_update_trail(imp & i) : m_imp(i) {}
            void undo() override {
                auto& [is_upper, j, bound, column] = m_imp.m_column_updates.back();
                if (is_upper)
                    m_imp.set_r_upper_bound(j, bound);
                else
                    m_imp.set_r_lower_bound(j, bound);
                m_imp.set_column(j, column);
                m_imp.m_column_updates.pop_back();
            }
        };

        bool validate_bound(lpvar j, lconstraint_kind kind, const mpq& rs, u_dependency* dep) {
            if (m_validate_blocker) return true;
            
            lar_solver solver;
            solver.m_validate_blocker = true;
            TRACE("lar_solver_validate", tout << lra.get_variable_name(j) << " " << lconstraint_kind_string(kind) << " " << rs << std::endl;);
            lra.add_dep_constraints_to_solver(solver, dep);
            if (solver.external_to_local(j) == null_lpvar) {
                return false; // we have to mention j in the dep
            }
            if (kind != EQ) {
                lra.add_bound_negation_to_solver(solver, j, kind, rs);
                solver.find_feasible_solution();
                return solver.get_status() == lp_status::INFEASIBLE;
            }
            else {
                solver.push();
                lra.add_bound_negation_to_solver(solver, j, LE, rs);
                solver.find_feasible_solution();
                if (solver.get_status() != lp_status::INFEASIBLE)
                    return false;
                solver.pop();
                lra.add_bound_negation_to_solver(solver, j, GE, rs);
                solver.find_feasible_solution();
                return solver.get_status() == lp_status::INFEASIBLE;
            }
        }
        void require_nbasis_sort() { m_mpq_lar_core_solver.m_r_solver.m_nbasis_sort_counter = 0; }   
        void register_in_fixed_var_table(unsigned j, unsigned& equal_to_j) {
            SASSERT(lra.column_is_fixed(j));
            equal_to_j = null_lpvar;
            const impq& bound = lra.get_lower_bound(j);
            if (!bound.y.is_zero())
                return;
            
            const mpq& key = bound.x;
            unsigned k;
            bool j_is_int = lra.column_is_int(j);
            if (j_is_int) {
                if (!m_fixed_var_table_int.find(key, k)) {
                    m_fixed_var_table_int.insert(key, j);
                    return;
                }
            }
            else { // j is not integral column        
                if (!m_fixed_var_table_real.find(key, k)) {
                m_fixed_var_table_real.insert(key, j);
                return;
            }
            }

            CTRACE("arith", !lra.column_is_fixed(k), lra.print_terms(tout););
            // SASSERT(column_is_fixed(k));
            if (j != k && lra.column_is_fixed(k)) {
                SASSERT(lra.column_is_int(j) == lra.column_is_int(k));
                equal_to_j = k;
                TRACE("lar_solver", tout << "found equal column k = " << k <<
                      ", external = " << equal_to_j << "\n";);
            }
        }
        void get_infeasibility_explanation_for_inf_sign(
            explanation& exp,
            const vector<std::pair<mpq, unsigned>>& inf_row,
            int inf_sign) const {
            for (auto& [coeff, j]: inf_row) {
                int adj_sign = coeff.is_pos() ? inf_sign : -inf_sign;
                const column& ul = m_columns[j];

                u_dependency* bound_constr_i = adj_sign < 0 ? ul.upper_bound_witness() : ul.lower_bound_witness();
                svector<constraint_index> deps;
                m_dependencies.linearize(bound_constr_i, deps);
                for (auto d : deps) {
                    SASSERT(m_constraints.valid_index(d));
                    exp.add_pair(d, coeff);
                }
            }
        }        
    }; // imp
    unsigned_vector& lar_solver::row_bounds_to_replay() { return m_imp->m_row_bounds_to_replay; }

    trail_stack& lar_solver::trail() { return m_imp->m_trail; }

    lp_settings& lar_solver::settings() { return m_imp->m_settings; }

    lp_settings const& lar_solver::settings() const { return m_imp->m_settings; }

    statistics& lar_solver::stats() { return m_imp->m_settings.stats(); }

    void lar_solver::updt_params(params_ref const& _p) {
        smt_params_helper p(_p);
        track_touched_rows(p.arith_bprop_on_pivoted_rows());
        set_cut_strategy(p.arith_branch_cut_ratio());
        m_imp->m_settings.updt_params(_p);
    }

    lar_solver::lar_solver() :
        m_imp(alloc(imp, *this)) {
    }

    const lar_core_solver& lar_solver::get_core_solver() const {
        return m_imp->m_mpq_lar_core_solver;
    }
    lar_core_solver& lar_solver::get_core_solver() {
        return m_imp->m_mpq_lar_core_solver;
    }
    
    // start or ends tracking the rows that were changed by solve()
    void lar_solver::track_touched_rows(bool v) {
        get_core_solver().m_r_solver.m_touched_rows = v ? (&m_imp->m_touched_rows) : nullptr;
    }
   
    // returns true iff the solver tracks the rows that were changed by solve()    
    bool lar_solver::touched_rows_are_tracked() const {
        return get_core_solver().m_r_solver.m_touched_rows != nullptr;
    }

    lar_solver::~lar_solver() {
        for (auto t : m_imp->m_terms)
            delete t;
    }
    
    void lar_solver::clear_columns_with_changed_bounds() { m_imp->m_columns_with_changed_bounds.reset(); }
    const indexed_uint_set& lar_solver::columns_with_changed_bounds() const { return m_imp->m_columns_with_changed_bounds; }

    const map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>>& lar_solver::fixed_var_table_int() const {
        return m_imp->m_fixed_var_table_int;
    }

    const map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>>& lar_solver::fixed_var_table_real() const {
        return m_imp->m_fixed_var_table_real;
    }
    void lar_solver::set_column_value(unsigned j, const impq& v) {
        m_imp->m_mpq_lar_core_solver.m_r_solver.update_x(j, v);
    }

    const vector<lar_term*>& lar_solver::terms() const { return m_imp->m_terms; }

    void lar_solver::set_int_solver(int_solver* int_slv) { m_imp->m_int_solver = int_slv; }
    int_solver* lar_solver::get_int_solver() { return m_imp->m_int_solver; }
    const int_solver* lar_solver::get_int_solver() const { return m_imp->m_int_solver; }
    bool lar_solver::has_changed_columns() const { return !m_imp->m_columns_with_changed_bounds.empty(); }
    unsigned lar_solver::usage_in_terms(lpvar j) const {
        if (j >= m_imp->m_usage_in_terms.size())
            return 0;
        return m_imp->m_usage_in_terms[j];
    }

    indexed_uint_set& lar_solver::basic_columns_with_changed_cost() { return m_imp->m_basic_columns_with_changed_cost; }
    
    mpq lar_solver::bound_span_x(lpvar j) const {
        SASSERT(column_has_upper_bound(j) && column_has_lower_bound(j));
        return get_upper_bound(j).x - get_lower_bound(j).x;
    }

    
    core_solver_pretty_printer<lp::mpq, lp::impq> lar_solver::pp(std::ostream& out) const {
        return core_solver_pretty_printer<lp::mpq, lp::impq>(m_imp->m_mpq_lar_core_solver.m_r_solver, out);
    }

    unsigned lar_solver::get_base_column_in_row(unsigned row_index) const {
        return m_imp->m_mpq_lar_core_solver.m_r_solver.get_base_column_in_row(row_index);
    }


    bool lar_solver::sizes_are_correct() const {
        SASSERT(A_r().column_count() == get_core_solver().m_r_solver.m_column_types.size());
        SASSERT(A_r().column_count() == get_core_solver().m_r_solver.m_costs.size());
        SASSERT(A_r().column_count() == get_core_solver().r_x().size());
        return true;
    }

    std::ostream& lar_solver::print_implied_bound(const implied_bound& be, std::ostream& out) const {
        out << "implied bound\n";
        unsigned v = be.m_j;
        if (column_has_term(v)) {
            out << "term for column  " << v << std::endl;
            print_term(*(m_imp->m_columns[v].term()), out);
        }
        else {
            out << get_variable_name(v);
        }
        out << " " << lconstraint_kind_string(be.kind()) << " " << be.m_bound << std::endl;
        out << "end of implied bound" << std::endl;
        return out;
    }

    std::ostream& lar_solver::print_values(std::ostream& out) const {
        for (unsigned i = 0; i < get_core_solver().r_x().size(); i++) {
            const numeric_pair<mpq>& rp = get_core_solver().r_x(i);
            out << this->get_variable_name(i) << " -> " << rp << "\n";
        }
        return out;
    }

    bool lar_solver::implied_bound_is_correctly_explained(implied_bound const& be, const vector<std::pair<mpq, unsigned>>& explanation) const {
        std::unordered_map<unsigned, mpq> coeff_map;
        auto rs_of_evidence = zero_of_type<mpq>();
        unsigned n_of_G = 0, n_of_L = 0;
        bool strict = false;
        for (auto& it : explanation) {
            mpq coeff = it.first;
            constraint_index con_ind = it.second;
            const auto& constr = m_imp->m_constraints[con_ind];
            lconstraint_kind kind = coeff.is_pos() ? constr.kind() : flip_kind(constr.kind());
            register_in_map(coeff_map, constr, coeff);
            if (kind == GT || kind == LT)
                strict = true;
            if (kind == GE || kind == GT) n_of_G++;
            else if (kind == LE || kind == LT) n_of_L++;
            rs_of_evidence += coeff * constr.rhs();
        }
        SASSERT(n_of_G == 0 || n_of_L == 0);
        lconstraint_kind kind = n_of_G ? GE : (n_of_L ? LE : EQ);
        if (strict)
            kind = static_cast<lconstraint_kind>((static_cast<int>(kind) / 2));

        if (!column_has_term(be.m_j)) {
            if (coeff_map.size() != 1)
                return false;
            auto it = coeff_map.find(be.m_j);
            if (it == coeff_map.end()) return false;
            mpq ratio = it->second;
            if (ratio < zero_of_type<mpq>()) {
                kind = static_cast<lconstraint_kind>(-kind);
            }
            rs_of_evidence /= ratio;
        }
        else {
            lar_term const& t = get_term(be.m_j);
            auto first_coeff = t.begin();
            unsigned j = (*first_coeff).j();
            auto it = coeff_map.find(j);
            if (it == coeff_map.end())
                return false;
            mpq ratio = it->second / (*first_coeff).coeff();
            for (auto p : t) {
                it = coeff_map.find(p.j());
                if (it == coeff_map.end())
                    return false;
                if (p.coeff() * ratio != it->second)
                    return false;
            }
            if (ratio < zero_of_type<mpq>()) {
                kind = static_cast<lconstraint_kind>(-kind);
            }
            rs_of_evidence /= ratio;
            // rs_of_evidence += t->m_v * ratio;
        }

        return kind == be.kind() && rs_of_evidence == be.m_bound;
    }


    bool lar_solver::row_has_a_big_num(unsigned i) const {
        for (const auto& c : A_r().m_rows[i]) 
            if (c.coeff().is_big())
                return true;
        return false;
    }

    lp_status lar_solver::get_status() const { return m_imp->m_status; }

    void lar_solver::set_status(lp_status s) {
        TRACE("lar_solver", tout << "setting status to " << s << "\n";);
        m_imp->m_status = s; 
    }
    const u_dependency* lar_solver::crossed_bounds_deps() const { return m_imp->m_crossed_bounds_deps;}
    u_dependency*& lar_solver::crossed_bounds_deps() { return m_imp->m_crossed_bounds_deps;}
    lpvar lar_solver::crossed_bounds_column() const { return m_imp->m_crossed_bounds_column; }
    lpvar& lar_solver::crossed_bounds_column() { return m_imp->m_crossed_bounds_column; } 
    lpvar lar_solver::local_to_external(lpvar idx) const { return m_imp->m_var_register.local_to_external(idx); }
    bool lar_solver::column_associated_with_row(lpvar j) const { return m_imp->m_columns[j].associated_with_row(); }

    u_dependency* lar_solver::get_column_upper_bound_witness(unsigned j) const {
        return m_imp->m_columns[j].upper_bound_witness();
    }

    unsigned lar_solver::number_of_vars() const { return m_imp->m_var_register.size(); }
    
    u_dependency* lar_solver::get_bound_constraint_witnesses_for_column(unsigned j) {
        const column& ul = m_imp->m_columns[j];
        return m_imp->m_dependencies.mk_join(ul.lower_bound_witness(), ul.upper_bound_witness());
    }


    u_dependency* lar_solver::get_column_lower_bound_witness(unsigned j) const {
        return m_imp->m_columns[j].lower_bound_witness();
    }

    bool lar_solver::column_has_term(lpvar j) const { return m_imp->m_columns[j].term() != nullptr; }

    const lar_term& lar_solver::get_term(lpvar j) const {
        SASSERT(column_has_term(j));
        return * (m_imp->m_columns[j].term());
    }

    lpvar lar_solver::external_to_local(unsigned j) const {
        lpvar local_j;
        if (m_imp->m_var_register.external_is_used(j, local_j)) {
            return local_j;
        } else {
            return -1;
        }
    }
    
    std::ostream& lar_solver::print_column_info(unsigned j, std::ostream& out, bool print_expl) const {
        get_core_solver().m_r_solver.print_column_info(j, out, false);
        if (column_has_term(j)) 
            print_term_as_indices(get_term(j), out << "   := ") << " ";
        out << "\n";
        if (print_expl)
            display_column_explanation(out, j);        
        return out;
    }

    std::ostream& lar_solver::display_column_explanation(std::ostream& out, unsigned j) const {
        const column& ul = m_imp->m_columns[j];
        svector<unsigned> vs1, vs2;
        m_imp->m_dependencies.linearize(ul.lower_bound_witness(), vs1);
        m_imp->m_dependencies.linearize(ul.upper_bound_witness(), vs2);
        if (!vs1.empty()) {
            out << " lo:\n";
            for (unsigned ci : vs1) {
                display_constraint(out, ci) << "\n";
            }
        }
        if (!vs2.empty()) {
            out << " hi:\n";
            for (unsigned ci : vs2) {
                display_constraint(out, ci) << "\n";
            }
        }     
        if (!vs1.empty() || !vs2.empty())
            out << "\n";
        return out;
    }

    
    lp_status lar_solver::find_feasible_solution() {
        stats().m_make_feasible++;
        if (A_r().column_count() > stats().m_max_cols)
            stats().m_max_cols = A_r().column_count();
        if (A_r().row_count() > stats().m_max_rows)
            stats().m_max_rows = A_r().row_count();
        flet f(settings().simplex_strategy(), simplex_strategy_enum::tableau_rows);
        get_core_solver().m_r_solver.m_look_for_feasible_solution_only = true;
        auto ret = solve();
        return ret;
    }

    lp_status lar_solver::solve() {
        if (m_imp->m_status == lp_status::INFEASIBLE || m_imp->m_status == lp_status::CANCELLED)
            return m_imp->m_status;
        
        solve_with_core_solver();
        if (m_imp->m_status == lp_status::INFEASIBLE || m_imp->m_status == lp_status::CANCELLED)
            return m_imp->m_status;
        
        if (m_imp->m_settings.bound_propagation())
            detect_rows_with_changed_bounds();

        clear_columns_with_changed_bounds();
        return m_imp->m_status;
    }

    svector<constraint_index> const& lar_solver::flatten(u_dependency* d) {
        m_imp->m_tmp_dependencies.reset();
        m_imp->m_dependencies.linearize(d, m_imp->m_tmp_dependencies);
        return m_imp->m_tmp_dependencies;
    }

    const u_dependency_manager& lar_solver::dep_manager() const { return m_imp->m_dependencies; }
    u_dependency_manager& lar_solver::dep_manager() { return m_imp->m_dependencies; }
    const constraint_set& lar_solver::constraints() const { return m_imp->m_constraints; }


    bool lar_solver::column_is_feasible(unsigned j) const { return get_core_solver().m_r_solver.column_is_feasible(j);}

    std::ostream& lar_solver::display_constraint(std::ostream& out, constraint_index ci) const {
        return m_imp->m_constraints.display(out, ci);
    }

    mpq lar_solver::from_model_in_impq_to_mpq(const impq& v) const { return v.x + m_imp->m_delta * v.y; }

    
    const impq& lar_solver::get_upper_bound(lpvar j) const {
        return get_core_solver().m_r_solver.m_upper_bounds[j];
    }

    const impq& lar_solver::get_lower_bound(lpvar j) const {
        return get_core_solver().m_r_solver.m_lower_bounds[j];
    }



    void lar_solver::fill_explanation_from_crossed_bounds_column(explanation& evidence) const {
        // this is the case when the lower bound is in conflict with the upper one
        svector<constraint_index> deps;
        SASSERT(m_imp->m_crossed_bounds_deps != nullptr);
        m_imp->m_dependencies.linearize(m_imp->m_crossed_bounds_deps, deps);
        for (auto d : deps)
            evidence.add_pair(d, -numeric_traits<mpq>::one());
    }

    void lar_solver::push() {
        m_imp->m_trail.push_scope();
        m_imp->m_simplex_strategy = m_imp->m_settings.simplex_strategy();
        m_imp->m_simplex_strategy.push();
        m_imp->m_crossed_bounds_column = null_lpvar;
        m_imp->m_crossed_bounds_deps = nullptr;
        get_core_solver().push();
        m_imp->m_constraints.push();
        m_imp->m_usage_in_terms.push();
        m_imp->m_dependencies.push_scope();
    }
    
    void lar_solver::clean_popped_elements(unsigned n, indexed_uint_set& set) {
        vector<int> to_remove;
        for (unsigned j : set)
            if (j >= n)
                to_remove.push_back(j);
        for (unsigned j : to_remove)
            set.remove(j);
    }

    void lar_solver::clean_popped_elements_for_heap(unsigned n, lpvar_heap& heap) {
        vector<int> to_remove;
        for (unsigned j : heap)
            if (j >= n)
                to_remove.push_back(j);
        for (unsigned j : to_remove)
            heap.erase(j);
    }
    

    void lar_solver::pop(unsigned k) {
        TRACE("lar_solver", tout << "k = " << k << std::endl;);
        m_imp->m_crossed_bounds_column = null_lpvar;
        m_imp->m_crossed_bounds_deps = nullptr;
        m_imp->m_trail.pop_scope(k);
        unsigned n = m_imp->m_columns.size();
        m_imp->m_var_register.shrink(n);

        SASSERT(get_core_solver().m_r_solver.m_costs.size() == A_r().column_count());
        SASSERT(get_core_solver().m_r_solver.m_basis.size() == A_r().row_count());
        SASSERT(get_core_solver().m_r_solver.basis_heading_is_correct());
        SASSERT(A_r().column_count() == n);
        TRACE("lar_solver_details", for (unsigned j = 0; j < n; j++) print_column_info(j, tout) << "\n";);

        get_core_solver().pop(k);
        remove_non_fixed_from_fixed_var_table();

        for (auto rid : m_imp->m_row_bounds_to_replay)
            add_touched_row(rid);
        m_imp->m_row_bounds_to_replay.reset();

        unsigned m = A_r().row_count();
        clean_popped_elements(m, m_imp->m_touched_rows);
        clean_inf_heap_of_r_solver_after_pop();
        SASSERT(get_core_solver().m_r_solver.reduced_costs_are_correct_tableau());

        m_imp->m_constraints.pop(k);
        m_imp->m_simplex_strategy.pop(k);
        m_imp->m_settings.simplex_strategy() = m_imp->m_simplex_strategy;
        SASSERT(sizes_are_correct());
        SASSERT(get_core_solver().m_r_solver.reduced_costs_are_correct_tableau());
        m_imp->m_usage_in_terms.pop(k);
        m_imp->m_dependencies.pop_scope(k);
        // init the nbasis sorting
        m_imp->require_nbasis_sort();
        set_status(lp_status::UNKNOWN);
    }


    bool lar_solver::maximize_term_on_tableau(const lar_term& term,
        impq& term_max) {
        flet f(get_core_solver().m_r_solver.m_look_for_feasible_solution_only, false);    
        get_core_solver().m_r_solver.set_status(lp_status::FEASIBLE);
        get_core_solver().solve();
        lp_status st = get_core_solver().m_r_solver.get_status();
        TRACE("lar_solver", tout << st << "\n";);
        SASSERT(get_core_solver().m_r_solver.calc_current_x_is_feasible_include_non_basis());
        if (st == lp_status::UNBOUNDED || st == lp_status::CANCELLED) {
            return false;
        }
        else {
            term_max = term.apply(get_core_solver().r_x());
            return true;
        }
    }

    // get dependencies of the corresponding bounds from max_coeffs
    u_dependency* lar_solver::get_dependencies_of_maximum(const vector<std::pair<mpq,lpvar>>& max_coeffs) {        
        // The linear combinations of d_j*x[j] = the term that got maximized, where (d_j, j) is in max_coeffs
        // Every j with positive coeff is at its upper bound,
        // and every j with negative coeff is at its lower bound: so the sum cannot be increased.
        // All variables j in the sum are non-basic.
        u_dependency* dep = nullptr;
        for (const auto & [d_j, j]: max_coeffs) {
            SASSERT (!d_j.is_zero());
                
            TRACE("lar_solver_improve_bounds", tout << "d[" << j << "] = " << d_j << "\n";
                                               this->get_core_solver().m_r_solver.print_column_info(j, tout););
            const column& ul = m_imp->m_columns[j];
            u_dependency * bound_dep;
            if (d_j.is_pos()) 
                bound_dep = ul.upper_bound_witness();
            else 
                bound_dep = ul.lower_bound_witness();               
            TRACE("lar_solver_improve_bounds", {
	           svector<constraint_index> cs;
                   dep_manager().linearize(bound_dep, cs);
               for (auto c : cs) 
                    m_imp->m_constraints.display(tout, c) << "\n";
            });
            SASSERT(bound_dep != nullptr);
            dep = dep_manager().mk_join(dep, bound_dep);
        }
        return dep;
    }
    // returns nullptr if the bound is not improved, otherwise returns the witness of the bound
    u_dependency* lar_solver::find_improved_bound(lpvar j, bool lower_bound, mpq& bound) {
        
        SASSERT(is_feasible());
        if (lower_bound  && column_has_lower_bound(j) && get_column_value(j) == column_lower_bound(j))
            return nullptr;  // cannot do better
        if (!lower_bound && column_has_upper_bound(j) && get_column_value(j) == column_upper_bound(j))
            return nullptr;  // cannot do better
        

        lar_term term = get_term_to_maximize(j);
        if (lower_bound)
            term.negate();
        vector<std::pair<mpq, unsigned>> max_coeffs;
        TRACE("lar_solver_improve_bounds", tout << "j = " << j << ", "; print_term(term, tout << "term to maximize\n"););
        impq term_max;
        if (!maximize_term_on_feasible_r_solver(term, term_max, &max_coeffs))
            return nullptr;
        // term_max is equal to the sum of m_d[j]*x[j] over all non basic j.
        // For the sum to be at the maximum all non basic variables should be at their bounds: if (m_d[j] > 0) x[j] = u[j], otherwise x[j] = l[j]. At upper bounds we have u[j].y <= 0, and at lower bounds we have l[j].y >= 0, therefore for the sum term_max.y <= 0.   
        SASSERT(!term_max.y.is_pos()); 
      
        // To keep it simpler we ignore possible improvements from non-strict to strict bounds.
        bound = term_max.x;
        if (lower_bound) {
            bound.neg();
            if (column_is_int(j))
                bound = ceil(bound);
         
            if (column_has_lower_bound(j) && column_is_int(j) && bound <= column_lower_bound(j).x)
                return nullptr;

            TRACE("lar_solver_improve_bounds",
                  tout << "setting lower bound for " << j << " to " << bound << "\n";
                  if (column_has_lower_bound(j)) tout << "bound was = " << column_lower_bound(j) << "\n";);                
        }
        else {
            if (column_is_int(j))
                bound = floor(bound);
            
            if (column_has_upper_bound(j)) {
                if (bound >= column_upper_bound(j).x)
                    return nullptr;
            }
            TRACE("lar_solver_improve_bounds",
                  tout << "setting upper bound for " << j << " to " << bound << "\n";
                  if (column_has_upper_bound(j)) tout << "bound was = " << column_upper_bound(j) << "\n";;);
        }   
        return get_dependencies_of_maximum(max_coeffs);
    }

    bool lar_solver::costs_are_zeros_for_r_solver() const {
        for (unsigned j = 0; j < get_core_solver().m_r_solver.m_costs.size(); j++) {
            SASSERT(is_zero(get_core_solver().m_r_solver.m_costs[j]));
        }
        return true;
    }
    bool lar_solver::reduced_costs_are_zeroes_for_r_solver() const {
        for (unsigned j = 0; j < get_core_solver().m_r_solver.m_d.size(); j++) {
            SASSERT(is_zero(get_core_solver().m_r_solver.m_d[j]));
        }
        return true;
    }

    void lar_solver::set_costs_to_zero(const lar_term& term) {
        auto& rslv = get_core_solver().m_r_solver;
        auto& d = rslv.m_d;
        auto& costs = rslv.m_costs;
        for (lar_term::ival p : term) {
            unsigned j = p.j();
            costs[j] = zero_of_type<mpq>();
            int i = rslv.m_basis_heading[j];
            if (i < 0) 
                d[j] = zero_of_type<mpq>();            
            else 
                for (const auto& rc : A_r().m_rows[i])
                    d[rc.var()] = zero_of_type<mpq>();
        }
        
        SASSERT(reduced_costs_are_zeroes_for_r_solver());
        SASSERT(costs_are_zeros_for_r_solver());
    }

    void lar_solver::prepare_costs_for_r_solver(const lar_term& term) {
        TRACE("lar_solver", print_term(term, tout << "prepare: ") << "\n";);
        auto& rslv = get_core_solver().m_r_solver;
        SASSERT(costs_are_zeros_for_r_solver());
        SASSERT(reduced_costs_are_zeroes_for_r_solver());
        move_non_basic_columns_to_bounds();
        rslv.m_costs.resize(A_r().column_count(), zero_of_type<mpq>());
        for (lar_term::ival p : term) {
            unsigned j = p.j();
            rslv.m_costs[j] = p.coeff();
            if (rslv.m_basis_heading[j] < 0)
                rslv.m_d[j] += p.coeff();
            else
                rslv.update_reduced_cost_for_basic_column_cost_change(-p.coeff(), j);
        }
        if (settings().backup_costs)
            rslv.m_costs_backup = rslv.m_costs;
        SASSERT(rslv.reduced_costs_are_correct_tableau());
    }

    void lar_solver::move_non_basic_columns_to_bounds() {
        auto& lcs = get_core_solver();
        bool change = false;
        for (unsigned j : lcs.m_r_nbasis) {
            if (move_non_basic_column_to_bounds(j))
                change = true;
        }
        if (!change)
            return;
        if (settings().simplex_strategy() == simplex_strategy_enum::tableau_costs)
            update_x_and_inf_costs_for_columns_with_changed_bounds_tableau();

        find_feasible_solution();
    }

    bool lar_solver::move_non_basic_column_to_bounds(unsigned j) {
        auto& lcs = get_core_solver();
        auto& val = lcs.r_x(j);
        switch (lcs.m_column_types()[j]) {
        case column_type::boxed: {
            const auto& l = lcs.m_r_lower_bounds[j];
            if (val == l || val == lcs.m_r_upper_bounds[j]) return false;
            set_value_for_nbasic_column(j, l);
            return true;
        }
                                        
        case column_type::lower_bound: {
            const auto& l = lcs.m_r_lower_bounds[j];
            if (val != l) {
                set_value_for_nbasic_column(j, l);
                return true;
            }
            return false;
        }
        case column_type::fixed:
        case column_type::upper_bound: {
            const auto & u = lcs.m_r_upper_bounds[j];
            if (val != u) {
                set_value_for_nbasic_column(j, u);
                return true;
            }
            return false;
        }
        case column_type::free_column:
            if (column_is_int(j) && !val.is_int()) {
                set_value_for_nbasic_column(j, impq(floor(val)));
                return true;
            }
            return false;
        default:
            SASSERT(false);
        }
        return false;
    }

    void lar_solver::set_value_for_nbasic_column(unsigned j, const impq& new_val) {
        SASSERT(!is_base(j));
        auto& x = get_core_solver().r_x(j);
        auto delta = new_val - x;
        x = new_val;
        TRACE("lar_solver_feas", tout << "setting " << j << " to "
         << new_val << (column_is_feasible(j)?"feas":"non-feas") << "\n";);
        change_basic_columns_dependend_on_a_given_nb_column(j, delta);
    }

    bool lar_solver::maximize_term_on_feasible_r_solver(lar_term& term,
                                                        impq& term_max, vector<std::pair<mpq, lpvar>>* max_coeffs = nullptr) {
        settings().backup_costs = false;
        bool ret = false;
        TRACE("lar_solver", print_term(term, tout << "maximize: ") << "\n"
                                                                   << constraints() << ", strategy = " << (int)settings().simplex_strategy() << "\n";);
        if (settings().simplex_strategy() != simplex_strategy_enum::tableau_costs)
            m_imp->require_nbasis_sort();
        flet f(settings().simplex_strategy(), simplex_strategy_enum::tableau_costs);
        prepare_costs_for_r_solver(term);
        ret = maximize_term_on_tableau(term, term_max);
        if (ret && max_coeffs != nullptr) {
            for (unsigned j = 0; j < column_count(); j++) {
                const mpq& d_j = get_core_solver().m_r_solver.m_d[j];
                if (d_j.is_zero())
                    continue;
                max_coeffs->push_back(std::make_pair(d_j, j));
                TRACE("lar_solver", tout<<"m_d["<<j<<"] = " << d_j<< ",\n";print_column_info(j, tout) << "\n";);
            }
        }
        set_costs_to_zero(term);
        get_core_solver().m_r_solver.set_status(lp_status::OPTIMAL);
        return ret;
    }

    // returns true iff the row of j has a non-fixed column different from j
    bool lar_solver::remove_from_basis(unsigned j) {
        SASSERT(is_base(j));
        unsigned i = row_of_basic_column(j);
        for (const auto & c : A_r().m_rows[i]) 
            if (j != c.var() && !column_is_fixed(c.var())) 
                return get_core_solver().m_r_solver.remove_from_basis_core(c.var(), j);
        return false;
    }

    lar_term lar_solver::get_term_to_maximize(unsigned j) const {
        if (column_has_term(j)) {
            return * (m_imp->m_columns[j].term());
        }
        if (j < get_core_solver().r_x().size()) {
            lar_term r;
            r.add_monomial(one_of_type<mpq>(), j);
            return r;
        }
        return lar_term(); // return an empty term
    }

    lp_status lar_solver::maximize_term(unsigned j,
        impq& term_max) {
        TRACE("lar_solver", print_values(tout););
        SASSERT(get_core_solver().m_r_solver.calc_current_x_is_feasible_include_non_basis());
        lar_term term = get_term_to_maximize(j);
        if (term.is_empty()) return lp_status::UNBOUNDED;
        get_core_solver().backup_x();
        impq prev_value = term.apply(get_core_solver().r_x());
        auto restore = [&]() {
            get_core_solver().restore_x();
        };
        if (!maximize_term_on_feasible_r_solver(term, term_max, nullptr)) {
            restore();
            return lp_status::UNBOUNDED;
        }

        impq opt_val = term_max;

        bool change = false;
        for (unsigned j = 0; j < get_core_solver().r_x().size(); j++) {
            if (!column_is_int(j))
                continue;
            if (column_value_is_integer(j))
                continue;
            if (m_imp->m_int_solver->is_base(j)) {
                if (!remove_from_basis(j)) { // consider a special version of remove_from_basis that would not remove inf_int columns
                    restore();
                    term_max = prev_value;
                    return lp_status::FEASIBLE; // it should not happen
                }
            }
            if (!column_value_is_integer(j)) {
                term_max = prev_value;
                restore();
                return lp_status::FEASIBLE;
            }
            change = true;
        }
        if (change) {
            term_max = term.apply(get_core_solver().r_x());
        }
        if (term_max < prev_value) {
            term_max = prev_value;
            restore();
        }
        TRACE("lar_solver", print_values(tout););
        if (term_max == opt_val) {
            set_status(lp_status::OPTIMAL);
            return lp_status::OPTIMAL;
        }
        return lp_status::FEASIBLE;
    }

    void lar_solver::set_upper_bound_witness(lpvar j, u_dependency* dep, impq const& high) {
        bool has_upper = m_imp->m_columns[j].upper_bound_witness() != nullptr;
        m_imp->m_column_updates.push_back({true, j, get_upper_bound(j), m_imp->m_columns[j]});
        m_imp->m_trail.push(imp::column_update_trail(*this->m_imp));
        m_imp->m_columns[j].set_upper_bound_witness(dep);
        if (has_upper)
            m_imp->m_columns[j].set_previous_upper(m_imp->m_column_updates.size() - 1);
        get_core_solver().m_r_upper_bounds[j] = high;
        insert_to_columns_with_changed_bounds(j);
    }

    void lar_solver::set_lower_bound_witness(lpvar j, u_dependency* dep, impq const& low) {
        bool has_lower = m_imp->m_columns[j].lower_bound_witness() != nullptr;
        m_imp->m_column_updates.push_back({false, j, get_lower_bound(j), m_imp->m_columns[j]});
        m_imp->m_trail.push(imp::column_update_trail(*this->m_imp));
        m_imp->m_columns[j].set_lower_bound_witness(dep);
        if (has_lower)
            m_imp->m_columns[j].set_previous_lower(m_imp->m_column_updates.size() - 1);
        get_core_solver().m_r_lower_bounds[j] = low;
        insert_to_columns_with_changed_bounds(j);
    }

    void lar_solver::register_monoid_in_map(std::unordered_map<lpvar, mpq>& coeffs, const mpq& a, unsigned j) {
        auto it = coeffs.find(j);
        if (it == coeffs.end()) 
            coeffs[j] = a;
        else 
            it->second += a;
    }

    void lar_solver::substitute_terms_in_linear_expression(const vector<std::pair<mpq, lpvar>>& left_side_with_terms,
        vector<std::pair<mpq, lpvar>>& left_side) const {
        std::unordered_map<lpvar, mpq> coeffs;
        for (auto& t : left_side_with_terms) {
            unsigned j = t.second;
            if (!column_has_term(j)) {
                register_monoid_in_map(coeffs, t.first, j);
            }
            else {
                const lar_term& term = *(m_imp->m_columns[t.second].term());

                for (auto p : term) 
                    register_monoid_in_map(coeffs, t.first * p.coeff(), p.j());
            }
        }

        for (auto& [v, c] : coeffs)
            if (!is_zero(c))
                left_side.push_back(std::make_pair(c, v));        
    }

    void lar_solver::add_touched_row(unsigned rid) {
        if (m_imp->m_settings.bound_propagation()) 
            m_imp->m_touched_rows.insert(rid);
    }

    void lar_solver::check_fixed(unsigned j) {
        if (column_is_fixed(j))
            return;

        auto explain = [&](constraint_index ci, lp::explanation const& exp) {
            u_dependency* d = nullptr;
            for (auto const& e : exp)
                if (e.ci() != ci) 
                    d = join_deps(d, dep_manager().mk_leaf(e.ci()));                
            return d;
        };

        if (!column_has_lower_bound(j) || column_lower_bound(j) != get_value(j)) {
            push();
            mpq val = get_value(j);
            auto ci = add_var_bound(j, lconstraint_kind::LT, val);
            auto r = solve();
            lp::explanation exp;
            if (r == lp_status::INFEASIBLE) 
                get_infeasibility_explanation(exp);            
            pop();
            if (r == lp_status::INFEASIBLE) {
                auto d = explain(ci, exp);
                update_column_type_and_bound(j, lconstraint_kind::GE, val, d);
            }
            solve();
        }

        if (!column_has_upper_bound(j) || column_upper_bound(j) != get_value(j)) {
            push();
            auto val = get_value(j);
            auto ci = add_var_bound(j, lconstraint_kind::GT, val);
            auto r = solve();
            lp::explanation exp;
            if (r == lp_status::INFEASIBLE) 
                get_infeasibility_explanation(exp);
            pop();
            if (r == lp_status::INFEASIBLE) {
                auto d = explain(ci, exp);
                update_column_type_and_bound(j, lconstraint_kind::LE, val, d);
            }
            solve();
        }
    }

    void lar_solver::solve_for(unsigned_vector const& js, vector<solution>& sols) {
        uint_set tabu, fixed_checked;
        for (auto j : js)
            solve_for(j, tabu, sols);
        solve();  // clear updated columns.
        auto check = [&](unsigned j) {
            if (fixed_checked.contains(j))
                return;
            fixed_checked.insert(j);
            check_fixed(j);
        };
        for (auto const& [j, t] : sols) {
            check(j);
            for (auto const& v : t) 
                check(v.j());            
        }
    }

    void lar_solver::solve_for(unsigned j, uint_set& tabu, vector<solution>& sols) {
        if (tabu.contains(j))
            return;
        tabu.insert(j);
        IF_VERBOSE(10, verbose_stream() << "solve for " << j << " base " << is_base(j) << " " << column_is_fixed(j) << "\n");
        TRACE("arith", tout << "solve for " << j << " base " << is_base(j) << " " << column_is_fixed(j) << "\n");
        if (column_is_fixed(j)) 
            return;
        
        if (!is_base(j)) {
            for (const auto& c : A_r().m_columns[j]) {
                lpvar basic_in_row = r_basis()[c.var()];
                if (tabu.contains(basic_in_row))
                    continue;
                pivot(j, basic_in_row);
                break;
            }
        }
        if (!is_base(j)) 
            return;
        
        lar_term t;
        //auto const& col = m_columns[j];
        auto const& r = basic2row(j);
        for (auto const& c : r) {
            if (c.var() != j)       
                t.add_monomial(-c.coeff(), c.var());            
        }            
        for (auto const& v : t) 
            solve_for(v.j(), tabu, sols); 
        lp::impq lo, hi;
        bool lo_valid = true, hi_valid = true;
        for (auto const& v : t) {
            if (v.coeff().is_pos()) {
                if (lo_valid && column_has_lower_bound(v.j()))
                    lo += column_lower_bound(v.j()) * v.coeff();
                else
                    lo_valid = false;
                if (hi_valid && column_has_upper_bound(v.j()))
                    hi += column_upper_bound(v.j()) * v.coeff();
                else
                    hi_valid = false;
            }
            else {
                if (lo_valid && column_has_upper_bound(v.j()))
                    lo += column_upper_bound(v.j()) * v.coeff();
                else
                    lo_valid = false;
                if (hi_valid && column_has_lower_bound(v.j()))
                    hi += column_lower_bound(v.j()) * v.coeff();
                else
                    hi_valid = false;
            }
        }        

        if (lo_valid && (!column_has_lower_bound(j) || lo > column_lower_bound(j).x)) {
            u_dependency* dep = nullptr;
            for (auto const& v : t) {
                if (v.coeff().is_pos())
                    dep = join_deps(dep, m_imp->m_columns[v.j()].lower_bound_witness());
                else
                    dep = join_deps(dep, m_imp->m_columns[v.j()].upper_bound_witness());
            }
            update_column_type_and_bound(j, lo.y == 0 ? lconstraint_kind::GE : lconstraint_kind::GT, lo.x, dep);
        }

        if (hi_valid && (!column_has_upper_bound(j) || hi < column_upper_bound(j).x)) {
            u_dependency* dep = nullptr;
            for (auto const& v : t) {
                if (v.coeff().is_pos())
                    dep = join_deps(dep, m_imp->m_columns[v.j()].upper_bound_witness());
                else
                    dep = join_deps(dep, m_imp->m_columns[v.j()].lower_bound_witness());
            }
            update_column_type_and_bound(j, hi.y == 0 ? lconstraint_kind::LE : lconstraint_kind::LT, hi.x, dep);
        }

        TRACE("arith", print_term(t, tout << "j" << j << " := ") << "\n");
        if (!column_is_fixed(j))             
            sols.push_back({j, t});
    }


    void lar_solver::explain_fixed_column(unsigned j, explanation& ex) {
        SASSERT(column_is_fixed(j));
        auto* deps = get_bound_constraint_witnesses_for_column(j);
        for (auto ci : flatten(deps))
            ex.push_back(ci);
    }

    void lar_solver::remove_fixed_vars_from_base() {
        // this will allow to disable and restore the tracking of the touched rows
        flet<indexed_uint_set*> f(get_core_solver().m_r_solver.m_touched_rows, nullptr);
        unsigned num = A_r().column_count();
        unsigned_vector to_remove;
        for (unsigned j : m_imp->m_fixed_base_var_set) {
            if (j >= num || !is_base(j) || !column_is_fixed(j)) {
                to_remove.push_back(j);
                continue;
            }

            SASSERT(is_base(j) && column_is_fixed(j));
            auto const& r = basic2row(j);
            for (auto const& c : r) {
                unsigned j_entering = c.var();
                if (!column_is_fixed(j_entering)) {
                    pivot(j_entering, j);
                    to_remove.push_back(j);
                    SASSERT(is_base(j_entering));
                    break;
                }
            }
        }
        for (unsigned j : to_remove) {
            m_imp->m_fixed_base_var_set.remove(j);
        }
        SASSERT(fixed_base_removed_correctly());
    }
#ifdef Z3DEBUG    
    bool lar_solver::fixed_base_removed_correctly() const {
        for (unsigned i = 0; i < A_r().row_count(); i++) {
            unsigned j = get_base_column_in_row(i);
            if (column_is_fixed(j)) {
                for (const auto & c : A_r().m_rows[i] ) {
                    if (!column_is_fixed(c.var())) {
                        TRACE("lar_solver", print_row(A_r().m_rows[i], tout) << "\n";
                        for(const auto & c : A_r().m_rows[i]) {
                            print_column_info(c.var(), tout) << "\n";
                        });
                        return false;
                    }
                }                
            }
        }
        return true;
    }
#endif

    bool lar_solver::use_tableau_costs() const {
        return m_imp->m_settings.simplex_strategy() == simplex_strategy_enum::tableau_costs;
    }
    bool lar_solver::row_is_correct(unsigned i) const {
        numeric_pair<mpq> r = zero_of_type<numeric_pair<mpq>>();
        for (const auto& c : A_r().m_rows[i]) {
            r += c.coeff() * get_core_solver().r_x(c.var());
        }
        CTRACE("lar_solver", !is_zero(r), tout << "row = " << i << ", j = " << get_core_solver().m_r_basis[i] << "\n";
               print_row(A_r().m_rows[i], tout);  tout << " = " << r << "\n");
        return is_zero(r);
    }

    unsigned lar_solver::row_of_basic_column(unsigned j) const {
        return get_core_solver().m_r_heading[j];
    }


    bool lar_solver::ax_is_correct() const {
        for (unsigned i = 0; i < A_r().row_count(); i++) {
            if (!row_is_correct(i)) {
                return false;
            }
        }
        return true;
    }

    bool lar_solver::tableau_with_costs() const {
        return m_imp->m_settings.simplex_strategy() == simplex_strategy_enum::tableau_costs;
    }

    bool lar_solver::costs_are_used() const {
        return m_imp->m_settings.simplex_strategy() != simplex_strategy_enum::tableau_rows;
    }

    void lar_solver::change_basic_columns_dependend_on_a_given_nb_column(unsigned j, const numeric_pair<mpq>& delta) {
        for (const auto& c : A_r().m_columns[j]) {
           unsigned bj = get_core_solver().m_r_basis[c.var()];
           if (tableau_with_costs()) {
              m_imp->m_basic_columns_with_changed_cost.insert(bj);
           }
           get_core_solver().m_r_solver.add_delta_to_x_and_track_feasibility(bj, -A_r().get_val(c) * delta);
           TRACE("change_x_del",
              tout << "changed basis column " << bj << ", it is " <<
              (column_is_feasible(bj) ? "feas" : "inf") << std::endl;);
        }
    }

    void lar_solver::update_x_and_inf_costs_for_column_with_changed_bounds(unsigned j) {
        if (get_core_solver().m_r_heading[j] >= 0) {
            if (costs_are_used()) {
                bool was_infeas = get_core_solver().m_r_solver.inf_heap_contains(j);
                get_core_solver().m_r_solver.track_column_feasibility(j);
                if (was_infeas != get_core_solver().m_r_solver.inf_heap_contains(j))
                    m_imp->m_basic_columns_with_changed_cost.insert(j);
            }
            else {
                get_core_solver().m_r_solver.track_column_feasibility(j);
            }
        }
        else {
            numeric_pair<mpq> delta;
            if (get_core_solver().m_r_solver.make_column_feasible(j, delta))
                change_basic_columns_dependend_on_a_given_nb_column(j, delta);
        }
    }

    void lar_solver::detect_rows_with_changed_bounds_for_column(unsigned j) {
        if (get_core_solver().m_r_heading[j] >= 0) 
            add_touched_row(get_core_solver().m_r_heading[j]);
        else 
            add_column_rows_to_touched_rows(j);        
    }

    void lar_solver::detect_rows_with_changed_bounds() {
        for (auto j : m_imp->m_columns_with_changed_bounds)
            detect_rows_with_changed_bounds_for_column(j);
        if (m_find_monics_with_changed_bounds_func)
            m_find_monics_with_changed_bounds_func(m_imp->m_columns_with_changed_bounds);
    }

    void lar_solver::update_x_and_inf_costs_for_columns_with_changed_bounds_tableau() {
        for (auto j : m_imp->m_columns_with_changed_bounds)
            update_x_and_inf_costs_for_column_with_changed_bounds(j);
    }


    void lar_solver::solve_with_core_solver() {
        get_core_solver().prefix_r();
        update_x_and_inf_costs_for_columns_with_changed_bounds_tableau();
        get_core_solver().solve();
        set_status(get_core_solver().m_r_solver.get_status());
        SASSERT(((stats().m_make_feasible% 100) != 0) || m_imp->m_status != lp_status::OPTIMAL || all_constraints_hold());
    }


    // this function just looks at the status    
    bool lar_solver::is_feasible() const {
        switch (this->get_status()) {
        case lp_status::OPTIMAL:
        case lp_status::FEASIBLE:
        case lp_status::UNBOUNDED: 
            SASSERT(get_core_solver().m_r_solver.inf_heap().size() == 0);
            return true;
        default:
            return false;
        }
    }
    
    numeric_pair<mpq> lar_solver::get_basic_var_value_from_row(unsigned i) {
        numeric_pair<mpq> r = zero_of_type<numeric_pair<mpq>>();

        unsigned bj = get_core_solver().m_r_solver.m_basis[i];
        for (const auto& c : A_r().m_rows[i]) {
            if (c.var() == bj) continue;
            const auto& x = get_core_solver().r_x(c.var());
            if (!is_zero(x))
                r -= c.coeff() * x;
        }
        return r;
    }

    bool lar_solver::var_is_registered(lpvar vj) const {
         return vj < A_r().column_count();
    }


    bool lar_solver::all_constrained_variables_are_registered(const vector<std::pair<mpq, lpvar>>& left_side) {
        for (auto it : left_side) {
            if (!var_is_registered(it.second))
                return false;
        }
        return true;
    }

    bool lar_solver::all_constraints_hold() const {
        if (m_imp->m_settings.get_cancel_flag())
            return true;
        std::unordered_map<lpvar, mpq> var_map;
        get_model_do_not_care_about_diff_vars(var_map);

        for (auto const& c : m_imp->m_constraints.active()) {
            if (!constraint_holds(c, var_map)) {
                TRACE("lar_solver",
                    m_imp->m_constraints.display(tout, c) << "\n";
                for (auto p : c.coeffs()) {
                    get_core_solver().m_r_solver.print_column_info(p.second, tout);
                });
                return false;
            }
        }
        return true;
    }

    bool lar_solver::constraint_holds(const lar_base_constraint& constr, std::unordered_map<lpvar, mpq>& var_map) const {
        mpq left_side_val = get_left_side_val(constr, var_map);
        switch (constr.kind()) {
        case LE: return left_side_val <= constr.rhs();
        case LT: return left_side_val < constr.rhs();
        case GE: return left_side_val >= constr.rhs();
        case GT: return left_side_val > constr.rhs();
        case EQ: return left_side_val == constr.rhs();
        default:
            UNREACHABLE();
        }
        return false; // it is unreachable
    }


    void lar_solver::register_in_map(std::unordered_map<lpvar, mpq>& coeffs, const lar_base_constraint& cn, const mpq& a) {
        for (auto& it : cn.coeffs()) {
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

    bool lar_solver::the_left_sides_sum_to_zero(const vector<std::pair<mpq, unsigned>>& evidence) const {
        std::unordered_map<lpvar, mpq> coeff_map;
        for (auto const & [coeff, con_ind] : evidence) {
            SASSERT(m_imp->m_constraints.valid_index(con_ind));
            register_in_map(coeff_map, m_imp->m_constraints[con_ind], coeff);
        }

        if (!coeff_map.empty()) {
            return false;
        }

        return true;
    }


    bool lar_solver::explanation_is_correct(explanation& explanation) const {
        return true;
#if 0
        // disabled: kind is uninitialized
#ifdef Z3DEBUG
        lconstraint_kind kind;
        SASSERT(the_left_sides_sum_to_zero(explanation));
        mpq rs = sum_of_right_sides_of_explanation(explanation);
        switch (kind) {
        case LE: SASSERT(rs < zero_of_type<mpq>());
            break;
        case LT: SASSERT(rs <= zero_of_type<mpq>());
            break;
        case GE: SASSERT(rs > zero_of_type<mpq>());
            break;
        case GT: SASSERT(rs >= zero_of_type<mpq>());
            break;
        case EQ: SASSERT(rs != zero_of_type<mpq>());
            break;
        default:
            UNREACHABLE();
            return false;
        }
#endif
#endif
        return true;
    }
    lpvar lar_solver::add_named_var(unsigned ext_j, bool is_int, const std::string& name) {
        lpvar j = add_var(ext_j, is_int);
        m_imp->m_var_register.set_name(j, name);
        return j;
    }

    bool lar_solver::inf_explanation_is_correct() const {
#ifdef Z3DEBUG
        explanation exp;
        get_infeasibility_explanation(exp);
        return explanation_is_correct(exp);
#endif
        return true;
    }

    mpq lar_solver::sum_of_right_sides_of_explanation(explanation& exp) const {
        mpq ret = numeric_traits<mpq>::zero();
        for (auto it : exp) {
            mpq coeff = it.coeff();
            constraint_index con_ind = it.ci();
            SASSERT(m_imp->m_constraints.valid_index(con_ind));
            ret += (m_imp->m_constraints[con_ind].rhs() - m_imp->m_constraints[con_ind].get_free_coeff_of_left_side()) * coeff;
        }
        return ret;
    }
    bool lar_solver::has_bound_of_type(lpvar var, u_dependency*& ci, mpq& value, bool& is_strict, bool is_upper) const {
        if (is_upper) {
            return has_upper_bound(var, ci, value, is_strict);
        } else {
            return has_lower_bound(var, ci, value, is_strict);
        }
    }
    bool lar_solver::has_lower_bound(lpvar var, u_dependency*& dep, mpq& value, bool& is_strict) const {

        if (var >= m_imp->m_columns.size()) {
            // TBD: bounds on terms could also be used, caller may have to track these.
            return false;
        }
        const column& ul = m_imp->m_columns[var];
        dep = ul.lower_bound_witness();
        if (dep != nullptr) {
            auto& p = get_core_solver().m_r_lower_bounds[var];
            value = p.x;
            is_strict = p.y.is_pos();
            return true;
        }
        else {
            return false;
        }
    }

    bool lar_solver::has_upper_bound(lpvar var, u_dependency*& dep, mpq& value, bool& is_strict) const {

        if (var >= m_imp->m_columns.size()) {
            // TBD: bounds on terms could also be used, caller may have to track these.
            return false;
        }
        const column& ul = m_imp->m_columns[var];
        dep = ul.upper_bound_witness();
        if (dep != nullptr) {
            auto& p = get_core_solver().m_r_upper_bounds[var];
            value = p.x;
            is_strict = p.y.is_neg();
            return true;
        }
        else {
            return false;
        }
    }

    bool lar_solver::has_value(lpvar var, mpq& value) const {
        if (column_has_term(var)) {
            lar_term const& t = get_term(var);
            value = 0;
            for (lar_term::ival cv : t) {
                impq const& r = get_column_value(cv.j());
                if (!numeric_traits<mpq>::is_zero(r.y)) return false;
                value += r.x * cv.coeff();
            }
            return true;
        }
        else {
            impq const& r = get_column_value(var);
            value = r.x;
            return numeric_traits<mpq>::is_zero(r.y);
        }
    }


    void lar_solver::get_infeasibility_explanation(explanation& exp) const {
        exp.clear();
        if (m_imp->m_crossed_bounds_column != null_lpvar) {
            fill_explanation_from_crossed_bounds_column(exp);
            return;
        }
        if (get_core_solver().get_infeasible_sum_sign() == 0) {
            return;
        }
        // the infeasibility sign
        int inf_sign;
        auto inf_row = get_core_solver().get_infeasibility_info(inf_sign);
        m_imp->get_infeasibility_explanation_for_inf_sign(exp, inf_row, inf_sign);
        SASSERT(explanation_is_correct(exp));
    }

    // (x, y) != (x', y') => (x + delta*y) != (x' + delta*y')
    void lar_solver::get_model(std::unordered_map<lpvar, mpq>& variable_values) const {
        variable_values.clear();
        if (!init_model())
            return;

        unsigned n = get_core_solver().r_x().size();

        for (unsigned j = 0; j < n; j++) 
            variable_values[j] = get_value(j);

        TRACE("lar_solver_model", tout << "delta = " << m_imp->m_delta << "\nmodel:\n";
               for (auto p : variable_values) tout << this->get_variable_name(p.first) << " = " << p.second << "\n";);
    }

    bool lar_solver::init_model() const {
        auto& rslv = get_core_solver().m_r_solver;
        (void)rslv;
        SASSERT(A_r().column_count() == rslv.m_costs.size());
        SASSERT(A_r().column_count() == get_core_solver().r_x().size());
        SASSERT(A_r().column_count() == rslv.m_d.size());
        CTRACE("lar_solver_model",!m_imp->m_columns_with_changed_bounds.empty(), tout << "non-empty changed bounds\n");
        TRACE("lar_solver_model", tout << get_status() << "\n");
        auto status = get_status();
        SASSERT((status != lp_status::OPTIMAL && status != lp_status::FEASIBLE) 
            || rslv.calc_current_x_is_feasible_include_non_basis());
        if (status != lp_status::OPTIMAL && status != lp_status::FEASIBLE)
            return false;
        if (!m_imp->m_columns_with_changed_bounds.empty())
            return false;

        m_imp->m_delta = get_core_solver().find_delta_for_strict_bounds(mpq(1));
        unsigned j;
        unsigned n = get_core_solver().r_x().size();
        do {
            m_imp->m_set_of_different_pairs.clear();
            m_imp->m_set_of_different_singles.clear();
            for (j = 0; j < n; j++) {
                const numeric_pair<mpq>& rp = get_core_solver().r_x(j);
                mpq x = rp.x + m_imp->m_delta * rp.y;
                m_imp->m_set_of_different_pairs.insert(rp);
                m_imp->m_set_of_different_singles.insert(x);
                if (m_imp->m_set_of_different_pairs.size() != m_imp->m_set_of_different_singles.size()) {
                    m_imp->m_delta /= mpq(2);
                    break;
                }
            }
        } while (j != n);
        TRACE("lar_solver_model", tout << "delta = " << m_imp->m_delta << "\nmodel:\n";);
        return true;
    }

    void lar_solver::get_model_do_not_care_about_diff_vars(std::unordered_map<lpvar, mpq>& variable_values) const {
        mpq delta = get_core_solver().find_delta_for_strict_bounds(mpq(1));
        for (unsigned i = 0; i < get_core_solver().r_x().size(); i++) {
            const impq& rp = get_core_solver().r_x(i);
            variable_values[i] = rp.x + delta * rp.y;
        }
    }

    mpq lar_solver::get_value(lpvar j) const {
        SASSERT(get_status() == lp_status::OPTIMAL || get_status() == lp_status::FEASIBLE);
        VERIFY(m_imp->m_columns_with_changed_bounds.empty());       
        numeric_pair<mpq> const& rp = get_column_value(j);
        return from_model_in_impq_to_mpq(rp);        
    }

    void lar_solver::get_rid_of_inf_eps() {
        bool y_is_zero = true;
        for (unsigned j = 0; j < number_of_vars(); j++) {
            if (!get_core_solver().r_x(j).y.is_zero()) {
                y_is_zero = false;
                break;
            }
        }
        if (y_is_zero)
            return;
        mpq delta = get_core_solver().find_delta_for_strict_bounds(mpq(1));
        for (unsigned j = 0; j < number_of_vars(); j++) {
            auto& v = get_core_solver().r_x(j);
            if (!v.y.is_zero()) {
                v = impq(v.x + delta * v.y);
                TRACE("lar_solver_feas", tout << "x[" << j << "] = " << v << "\n";);
            }
        }
    }

    void lar_solver::set_variable_name(lpvar vi, std::string name) {
        m_imp->m_var_register.set_name(vi, name);
    }

    std::string lar_solver::get_variable_name(lpvar j) const {
        if (column_has_term(j))
            return std::string("_t") + T_to_string(j);
        if (j >= m_imp->m_var_register.size())
            return std::string("_s") + T_to_string(j);

        std::string s = m_imp->m_var_register.get_name(j);
        if (!s.empty()) {
            return s;
        }
        if (m_imp->m_settings.print_external_var_name()) {
            return std::string("j") + T_to_string(m_imp->m_var_register.local_to_external(j));
        }
        else {
            std::string s = column_has_term(j) ? "t" : "j";
            return s + T_to_string(j);
        }
    }

    // ********** print region start

    std::ostream& lar_solver::display(std::ostream& out) const {
        out << constraints();
        print_terms(out);
        pp(out).print();
        for (unsigned j = 0; j < number_of_vars(); j++) 
            print_column_info(j, out);
        return out;
    }

    std::ostream& lar_solver::print_terms(std::ostream& out) const {
        for (auto it : m_imp->m_terms) {
            print_term(*it, out) << "\n";
        }
        return out;
    }

    std::ostream& lar_solver::print_term(lar_term const& term, std::ostream& out) const {
        if (term.size() == 0) {
            out << "0";
            return out;
        }
        bool first = true;
        for (const auto p : term) {
            mpq val = p.coeff();
            if (first) {
                first = false;
            }
            else if (is_pos(val)) {
                out << " + ";
            }
            else {
                out << " - ";
                val = -val;
            }
            if (val == -numeric_traits<mpq>::one())
                out << " - ";
            else if (val != numeric_traits<mpq>::one())
                out << T_to_string(val);
            out << this->get_variable_name(p.j());
        }
        return out;
    }

    std::ostream& lar_solver::print_term_as_indices(lar_term const& term, std::ostream& out) {
        print_linear_combination_of_column_indices_only(term.coeffs_as_vector(), out);
        return out;
    }

    mpq lar_solver::get_left_side_val(const lar_base_constraint& cns, const std::unordered_map<lpvar, mpq>& var_map) const {
        mpq ret = cns.get_free_coeff_of_left_side();
        for (auto& it : cns.coeffs()) {
            lpvar j = it.second;
            auto vi = var_map.find(j);
            SASSERT(vi != var_map.end());
            ret += it.first * vi->second;
        }
        return ret;
    }


    void lar_solver::fill_var_set_for_random_update(unsigned sz, lpvar const* vars, vector<unsigned>& column_list) {
        TRACE("lar_solver_rand", tout << "sz = " << sz << "\n";);
        for (unsigned i = 0; i < sz; i++) {
            lpvar var = vars[i];
            if (column_has_term(var)) {
                if (m_imp->m_columns[var].associated_with_row()) {
                    column_list.push_back(var);
                }
            }
            else {
                column_list.push_back(var);
            }
        }
    }

    void lar_solver::random_update(unsigned sz, lpvar const* vars) {
        vector<unsigned> column_list;
        fill_var_set_for_random_update(sz, vars, column_list);
        random_updater ru(*this, column_list);
        ru.update();
    }

    void lar_solver::add_column_rows_to_touched_rows(lpvar j) {
        const auto& column = A_r().m_columns[j];
        for (auto const& r : column) 
            add_touched_row(r.var());        
    }

    void lar_solver::pop() {
        pop(1);
    }

    bool lar_solver::column_represents_row_in_tableau(unsigned j) {
        return m_imp->m_columns[j].associated_with_row();
    }

    void lar_solver::make_sure_that_the_bottom_right_elem_not_zero_in_tableau(unsigned i, unsigned j) {
        // i, j - is the indices of the bottom-right element of the tableau
        SASSERT(A_r().row_count() == i + 1 && A_r().column_count() == j + 1);
        auto& last_column = A_r().m_columns[j];
        int non_zero_column_cell_index = -1;
        for (unsigned k = static_cast<unsigned>(last_column.size()); k-- > 0;) {
            auto& cc = last_column[k];
            if (cc.var() == i)
                return;
            non_zero_column_cell_index = k;
        }

        SASSERT(non_zero_column_cell_index != -1);
        SASSERT(static_cast<unsigned>(non_zero_column_cell_index) != i);
        get_core_solver().m_r_solver.transpose_rows_tableau(last_column[non_zero_column_cell_index].var(), i);
    }

    void lar_solver::remove_last_row_and_column_from_tableau(unsigned j) {
        SASSERT(A_r().column_count() == get_core_solver().m_r_solver.m_costs.size());
        auto& slv = get_core_solver().m_r_solver;
        unsigned i = A_r().row_count() - 1; //last row index
        make_sure_that_the_bottom_right_elem_not_zero_in_tableau(i, j);
        if (slv.m_basis_heading[j] < 0) {
            slv.pivot_column_tableau(j, i);
        }

        auto& last_row = A_r().m_rows[i];
        mpq& cost_j = get_core_solver().m_r_solver.m_costs[j];
        bool cost_is_nz = !is_zero(cost_j);
        for (unsigned k = static_cast<unsigned>(last_row.size()); k-- > 0;) {
            auto& rc = last_row[k];
            if (cost_is_nz) {
                get_core_solver().m_r_solver.m_d[rc.var()] += cost_j * rc.coeff();
            }
            A_r().remove_element(last_row, rc);
        }
        SASSERT(last_row.size() == 0);
        SASSERT(A_r().m_columns[j].size() == 0);
        A_r().m_rows.pop_back();
        A_r().m_columns.pop_back();
        CASSERT("check_static_matrix", A_r().is_correct());
    }

    void lar_solver::remove_last_column_from_A() {
        // the last column has to be empty
        SASSERT(A_r().m_columns.back().size() == 0);
        A_r().m_columns.pop_back();
    }

    void lar_solver::remove_last_column_from_basis_tableau(unsigned j) {
        auto& rslv = get_core_solver().m_r_solver;
        int i = rslv.m_basis_heading[j];
        if (i >= 0) { // j is a basic var
            int last_pos = static_cast<int>(rslv.m_basis.size()) - 1;
            SASSERT(last_pos >= 0);
            if (i != last_pos) {
                unsigned j_at_last_pos = rslv.m_basis[last_pos];
                rslv.m_basis[i] = j_at_last_pos;
                rslv.m_basis_heading[j_at_last_pos] = i;
            }
            rslv.m_basis.pop_back(); // remove j from the basis
        }
        else {
            int last_pos = static_cast<int>(rslv.m_nbasis.size()) - 1;
            SASSERT(last_pos >= 0);
            i = -1 - i;
            if (i != last_pos) {
                unsigned j_at_last_pos = rslv.m_nbasis[last_pos];
                rslv.m_nbasis[i] = j_at_last_pos;
                rslv.m_basis_heading[j_at_last_pos] = -i - 1;
            }
            rslv.m_nbasis.pop_back(); // remove j from the basis
        }
        rslv.m_basis_heading.pop_back();
        SASSERT(rslv.m_basis.size() == A_r().row_count());
        SASSERT(rslv.basis_heading_is_correct());
    }

    void lar_solver::remove_last_column_from_tableau() {
        auto& rslv = get_core_solver().m_r_solver;
        unsigned j = A_r().column_count() - 1;
        SASSERT(A_r().column_count() == rslv.m_costs.size());
        if (column_represents_row_in_tableau(j)) {
            remove_last_row_and_column_from_tableau(j);
            if (rslv.m_basis_heading[j] < 0)
                rslv.change_basis_unconditionally(j, rslv.m_basis[A_r().row_count()]); // A_r().row_count() is the index of the last row in the basis still
        }
        else {
            remove_last_column_from_A();
        }
        get_core_solver().resize_x(A_r().column_count());
        rslv.m_d.pop_back();
        rslv.m_costs.pop_back();

        remove_last_column_from_basis_tableau(j);
        SASSERT(get_core_solver().r_basis_is_OK());
        SASSERT(A_r().column_count() == rslv.m_costs.size());
        SASSERT(A_r().column_count() == get_core_solver().r_x().size());
        SASSERT(A_r().column_count() == rslv.m_d.size());
    }


    void lar_solver::clean_inf_heap_of_r_solver_after_pop() {
        vector<unsigned> became_feas;
        clean_popped_elements_for_heap(A_r().column_count(), get_core_solver().m_r_solver.inf_heap());
        std::unordered_set<unsigned> basic_columns_with_changed_cost;
        m_imp->m_inf_index_copy.reset();
        for (auto j : get_core_solver().m_r_solver.inf_heap())
            m_imp->m_inf_index_copy.push_back(j);
        for (auto j : m_imp->m_inf_index_copy) {
            if (get_core_solver().m_r_heading[j] >= 0) {
                continue;
            }
            // some basic columns might become non-basic - these columns need to be made feasible
            numeric_pair<mpq> delta;
            if (get_core_solver().m_r_solver.make_column_feasible(j, delta)) {
                change_basic_columns_dependend_on_a_given_nb_column(j, delta);
            }
            became_feas.push_back(j);
        }

        for (unsigned j : became_feas) {
            SASSERT(get_core_solver().m_r_solver.m_basis_heading[j] < 0);
            get_core_solver().m_r_solver.m_d[j] -= get_core_solver().m_r_solver.m_costs[j];
            get_core_solver().m_r_solver.m_costs[j] = zero_of_type<mpq>();
            get_core_solver().m_r_solver.remove_column_from_inf_heap(j);
        }
        became_feas.clear();
        for (unsigned j : get_core_solver().m_r_solver.inf_heap()) {
            SASSERT(get_core_solver().m_r_heading[j] >= 0);
            if (column_is_feasible(j))
                became_feas.push_back(j);
        }
        for (unsigned j : became_feas)
            get_core_solver().m_r_solver.remove_column_from_inf_heap(j);

    }

    bool lar_solver::model_is_int_feasible() const {
        unsigned n = A_r().column_count();
        for (unsigned j = 0; j < n; j++) {
            if (column_is_int(j) && !column_value_is_integer(j))
                return false;
        }
        return true;
    }

    bool lar_solver::term_is_int(const lar_term* t) const {
        for (auto const p : *t)
            if (!(column_is_int(p.j()) && p.coeff().is_int()))
                return false;
        return true;
    }

    bool lar_solver::term_is_int(const vector<std::pair<mpq, unsigned int>>& coeffs) const {
        for (auto const& [coeff, v] : coeffs)
            if (!(column_is_int(v) && coeff.is_int()))
                return false;
        return true;
    }

    bool lar_solver::var_is_int(lpvar v) const {       
        SASSERT(!column_has_term(v) || term_is_int(&get_term(v)) == column_is_int(v));
        return column_is_int(v);
    }

    bool lar_solver::column_is_int(unsigned j) const {
        return m_imp->m_var_register.local_is_int(j);
    }

    bool lar_solver::column_is_fixed(unsigned j) const {
        return get_core_solver().column_is_fixed(j);
    }

    bool lar_solver::column_is_free(unsigned j) const {
        return get_core_solver().column_is_free(j);
    }

    struct lar_solver::imp::undo_add_column : public trail {
        lar_solver& s;
        undo_add_column(lar_solver& s) : s(s) {}
        void undo() override {
            auto& col = s.m_imp->m_columns.back();
            if (col.term() != nullptr) {
                if (s.m_imp->m_need_register_terms)
                    s.deregister_normalized_term(*col.term());
                delete col.term();
                s.m_imp->m_terms.pop_back();
            }
            s.remove_last_column_from_tableau();            
            s.m_imp->m_columns.pop_back();
            unsigned j = s.m_imp->m_columns.size();
            if (s.m_imp->m_columns_with_changed_bounds.contains(j))
                s.m_imp->m_columns_with_changed_bounds.remove(j);
            if (s.m_imp->m_incorrect_columns.contains(j))
                s.m_imp->m_incorrect_columns.remove(j);
        }
    };

    lpvar lar_solver::add_var(unsigned ext_j, bool is_int) {
        TRACE("add_var", tout << "adding var " << ext_j << (is_int ? " int" : " nonint") << std::endl;);
        lpvar local_j;
        if (m_imp->m_var_register.external_is_used(ext_j, local_j))
            return local_j;
        SASSERT(m_imp->m_columns.size() == A_r().column_count());
        local_j = A_r().column_count();
        m_imp->m_columns.push_back(column());
        trail().push(imp::undo_add_column(*this));
        while (m_imp->m_usage_in_terms.size() <= local_j) 
            m_imp->m_usage_in_terms.push_back(0);
        add_non_basic_var_to_core_fields(ext_j, is_int);
        SASSERT(sizes_are_correct());
        return local_j;
    }

    bool lar_solver::has_int_var() const {
        return m_imp->m_var_register.has_int_var();
    }

    void lar_solver::register_new_external_var(unsigned ext_v, bool is_int) {
        SASSERT(!m_imp->m_var_register.external_is_used(ext_v));
        m_imp->m_var_register.add_var(ext_v, is_int);
    }

    bool lar_solver::external_is_used(unsigned v) const {
        return m_imp->m_var_register.external_is_used(v);
    }
    
    void lar_solver::add_non_basic_var_to_core_fields(unsigned ext_j, bool is_int) {
        register_new_external_var(ext_j, is_int);
        get_core_solver().m_column_types.push_back(column_type::free_column);
        add_new_var_to_core_fields_for_mpq(false); // false for not adding a row        
    }
    
    void lar_solver::add_new_var_to_core_fields_for_mpq(bool register_in_basis) {
        unsigned j = A_r().column_count();
        TRACE("add_var", tout << "j = " << j << std::endl;);
        A_r().add_column();
        SASSERT(get_core_solver().r_x().size() == j);
        //        SASSERT(get_core_solver().m_r_lower_bounds.size() == j && get_core_solver().m_r_upper_bounds.size() == j);  // restore later
        get_core_solver().resize_x(j + 1);
        auto& rslv = get_core_solver().m_r_solver;
        get_core_solver().m_r_lower_bounds.reserve(j + 1);
        get_core_solver().m_r_upper_bounds.reserve(j + 1);
        rslv.inf_heap_increase_size_by_one();
        rslv.m_costs.resize(j + 1);
        rslv.m_d.resize(j + 1);
        SASSERT(get_core_solver().m_r_heading.size() == j); // as A().column_count() on the entry to the method
        if (register_in_basis) {
            A_r().add_row();
            get_core_solver().m_r_heading.push_back(get_core_solver().m_r_basis.size());
            get_core_solver().m_r_basis.push_back(j);
            add_touched_row(A_r().row_count() - 1);
        }
        else {
            get_core_solver().m_r_heading.push_back(-static_cast<int>(get_core_solver().m_r_nbasis.size()) - 1);
            get_core_solver().m_r_nbasis.push_back(j);
            m_imp->require_nbasis_sort();
        }
    }

#if Z3DEBUG_CHECK_UNIQUE_TERMS
    bool lar_solver::term_coeffs_are_ok(const vector<std::pair<mpq, lpvar>>& coeffs) {

        for (const auto& p : coeffs) 
            if (column_is_real(p.second))
                return true;

        mpq g;
        bool g_is_set = false;
        for (const auto& p : coeffs) {
            if (!p.first.is_int()) 
                return false;
            if (!g_is_set) {
                g_is_set = true;
                g = p.first;
            }
            else 
                g = gcd(g, p.first);
        }
        if (g == one_of_type<mpq>())
            return true;

        return false;
    }
#endif
    
  
    // terms
    bool lar_solver::all_vars_are_registered(const vector<std::pair<mpq, lpvar>>& coeffs) {
        return all_of(coeffs, [&](const auto& p) { return p.second < m_imp->m_var_register.size(); });
    }

    void lar_solver::subst_known_terms(lar_term* t) {
        std::set<unsigned> seen_terms;
        for (auto p : *t) {
            auto j = p.j();
            if (this->column_has_term(j)) 
                seen_terms.insert(j);
        }
        while (!seen_terms.empty()) {
            unsigned j = *seen_terms.begin();
            seen_terms.erase(j);
            const lar_term& ot = this->get_term(j);
            for (auto p : ot)
                if (this->column_has_term(p.j())) 
                    seen_terms.insert(p.j());
            t->subst_by_term(ot, j);
        }
    }
    // if UINT_MAX == null_lpvar then the term does not correspond and external variable
    lpvar lar_solver::add_term(const vector<std::pair<mpq, lpvar>>& coeffs, unsigned ext_i) {
         TRACE("lar_solver_terms", print_linear_combination_of_column_indices_only(coeffs, tout) << ", ext_i =" << ext_i << "\n";);
        SASSERT(!m_imp->m_var_register.external_is_used(ext_i));
        SASSERT(all_vars_are_registered(coeffs));
        lar_term* t = new lar_term(coeffs);
        subst_known_terms(t);
        SASSERT (!t->is_empty());
        m_imp->m_terms.push_back(t);
        lpvar ret = A_r().column_count();
        add_row_from_term_no_constraint(t, ext_i);
        
        SASSERT(m_imp->m_var_register.size() == A_r().column_count());
        if (m_imp->m_need_register_terms) 
            register_normalized_term(*t, A_r().column_count() - 1);
        if (m_add_term_callback)
            m_add_term_callback(t);    
        return ret;
    }

    void lar_solver::add_row_from_term_no_constraint(lar_term* term, unsigned ext_index) {
        TRACE("dump_terms", print_term(*term, tout) << std::endl;);
        register_new_external_var(ext_index, term_is_int(term));
        // j will be a new variable
        unsigned j = A_r().column_count();
        SASSERT(ext_index == null_lpvar || external_to_local(ext_index) == j);
        column ul(term);
        term->set_j(j); // point from the term to the column
        m_imp->m_columns.push_back(ul);
        m_imp->m_trail.push(imp::undo_add_column(*this));
        add_basic_var_to_core_fields();
         
        A_r().fill_last_row_with_pivoting(*term,
                j,
                get_core_solver().m_r_solver.m_basis_heading); 
        
        
        get_core_solver().m_r_solver.update_x(j, get_basic_var_value_from_row(A_r().row_count() - 1));
        for (lar_term::ival c : *term) {
            unsigned j = c.j();
            while (m_imp->m_usage_in_terms.size() <= j) 
                m_imp->m_usage_in_terms.push_back(0);
            m_imp->m_usage_in_terms[j] = m_imp->m_usage_in_terms[j] + 1;
        }
    }

    void lar_solver::add_basic_var_to_core_fields() {
        get_core_solver().m_column_types.push_back(column_type::free_column);
        add_new_var_to_core_fields_for_mpq(true);
    }

    bool lar_solver::bound_is_integer_for_integer_column(unsigned j, const mpq& right_side) const {
        return !column_is_int(j) || right_side.is_int();
    }

    constraint_index lar_solver::add_var_bound_check_on_equal(lpvar j, lconstraint_kind kind, const mpq& right_side, lpvar& equal_var) {
        constraint_index ci = mk_var_bound(j, kind, right_side);
        activate_check_on_equal(ci, equal_var);
        return ci;
    }

    constraint_index lar_solver::add_var_bound(lpvar j, lconstraint_kind kind, const mpq& right_side) {
        constraint_index ci = mk_var_bound(j, kind, right_side);
        activate(ci);
        return ci;
    }

    template <typename T>
    void lar_solver::remove_non_fixed_from_table(T& table) {
        vector<mpq> to_remove;
        for (const auto& p : table) {
            unsigned j = p.m_value;
            if (j >= column_count() || !column_is_fixed(j))
                to_remove.push_back(p.m_key);
        }
        for (const auto& p : to_remove)
            table.erase(p);
    }

    void lar_solver::remove_non_fixed_from_fixed_var_table() {
        remove_non_fixed_from_table(m_imp->m_fixed_var_table_int);
        remove_non_fixed_from_table(m_imp->m_fixed_var_table_real);
    }


    void lar_solver::activate_check_on_equal(constraint_index ci, unsigned& equal_column) {
        auto const& c = m_imp->m_constraints[ci];
        update_column_type_and_bound_check_on_equal(c.column(), c.rhs(), ci, equal_column);
    }

    void lar_solver::activate(constraint_index ci) {
        auto const& c = m_imp->m_constraints[ci];
        update_column_type_and_bound(c.column(), c.rhs(), ci);
    }

    mpq lar_solver::adjust_bound_for_int(lpvar j, lconstraint_kind& k, const mpq& bound) {
        if (!column_is_int(j))
            return bound;
        if (bound.is_int())
            return bound;
        switch (k) {
        case LT:
            k = LE;
            Z3_fallthrough;
        case LE:
            return floor(bound);
        case GT:
            k = GE;
            Z3_fallthrough;
        case GE:
            return ceil(bound);
        case EQ:
            return bound;
        default:
            UNREACHABLE();
        }

        return bound;

    }

    constraint_index lar_solver::mk_var_bound(lpvar j, lconstraint_kind kind, const mpq& right_side) {
        TRACE("lar_solver", tout << "j = " << get_variable_name(j) << " " << lconstraint_kind_string(kind) << " " << right_side << std::endl;);
        constraint_index ci;
        if (!column_has_term(j)) { 
            mpq rs = adjust_bound_for_int(j, kind, right_side);
            SASSERT(bound_is_integer_for_integer_column(j, rs));
            ci = m_imp->m_constraints.add_var_constraint(j, kind, rs);
        }
        else {
            ci = add_var_bound_on_constraint_for_term(j, kind, right_side);
        }
        SASSERT(sizes_are_correct());
        return ci;
    }

    bool lar_solver::compare_values(lpvar j, lconstraint_kind k, const mpq& rhs) {
        return compare_values(get_column_value(j), k, rhs);
    }

    bool lar_solver::compare_values(impq const& lhs, lconstraint_kind k, const mpq& rhs) {
        switch (k) {
        case LT: return lhs < rhs;
        case LE: return lhs <= rhs;
        case GT: return lhs > rhs;
        case GE: return lhs >= rhs;
        case EQ: return lhs == rhs;
        default:
            UNREACHABLE();
            return true;
        }
    }

    void lar_solver::update_column_type_and_bound(unsigned j,
        const mpq& right_side,
        constraint_index constr_index) {
        TRACE("lar_solver_feas", tout << "j = " << j << " was " << (this->column_is_feasible(j)?"feas":"non-feas") << std::endl;);
        m_imp->m_constraints.activate(constr_index);
        lconstraint_kind kind = m_imp->m_constraints[constr_index].kind();
        u_dependency* dep = m_imp->m_constraints[constr_index].dep();
        update_column_type_and_bound(j, kind, right_side, dep);
    }


    bool lar_solver::validate_bound(lpvar j, lconstraint_kind kind, const mpq& rs, u_dependency* dep) {
        return m_imp->validate_bound(j, kind, rs, dep);
    }

    void lar_solver::add_dep_constraints_to_solver(lar_solver& ls, u_dependency* dep) {
        auto constraints = flatten(dep);
        for (auto c : constraints) 
            add_constraint_to_validate(ls, c);
    }
    void lar_solver::add_bound_negation_to_solver(lar_solver& ls, lpvar j, lconstraint_kind kind, const mpq& right_side) {
        j = ls.external_to_local(j);
        switch (kind) {
        case LE:
            ls.add_var_bound(j, GT, right_side);
            break;
        case LT:
            ls.add_var_bound(j, GE, right_side);
            break;
        case GE:
            ls.add_var_bound(j, LT, right_side);
            break;
        case GT:
            ls.add_var_bound(j, LE, right_side);
            break;
        default:
            UNREACHABLE();
            break;
        }                
    }
    void lar_solver::add_constraint_to_validate(lar_solver& ls, constraint_index ci) {
        auto const& c = m_imp->m_constraints[ci];
        TRACE("lar_solver_validate", tout << "adding constr with column = "<< c.column() << "\n"; m_imp->m_constraints.display(tout, c); tout << std::endl;);
        vector<std::pair<mpq, lpvar>> coeffs;
        for (auto const& [coeff, jext] : c.coeffs()) {
            lpvar j = ls.external_to_local(jext);
            if (j == null_lpvar) { 
                ls.add_var(jext, column_is_int(jext));
                j = ls.external_to_local(jext);
            }
            coeffs.push_back({coeff, j});
        }
        
        lpvar column_ext = c.column();
        unsigned j = ls.external_to_local(column_ext);
        lpvar tv;
        if (j == UINT_MAX) {
            tv = ls.add_term(coeffs, column_ext);
        }
        else {            
            tv = ls.add_term(coeffs, null_lpvar);
        }
        ls.add_var_bound(tv, c.kind(), c.rhs());
    }
    void lar_solver::update_column_type_and_bound(unsigned j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep) {
        // SASSERT(validate_bound(j, kind, right_side, dep));
        TRACE(
            "lar_solver_feas",
            tout << "j" << j << " " << lconstraint_kind_string(kind) << " " << right_side << std::endl;   
            print_column_info(j, tout) << "\n";
            if (dep) {
                tout << "dep:\n";
                auto cs = flatten(dep);
                for (auto c : cs) {
                    constraints().display(tout, c);
                    tout << std::endl;
                }
            });
        bool was_fixed = column_is_fixed(j);
        mpq rs = adjust_bound_for_int(j, kind, right_side);
        if (column_has_upper_bound(j))
            update_column_type_and_bound_with_ub(j, kind, rs, dep);
        else
            update_column_type_and_bound_with_no_ub(j, kind, rs, dep);

        if (!was_fixed && column_is_fixed(j) && m_fixed_var_eh)
            m_fixed_var_eh(j);

        if (is_base(j) && column_is_fixed(j)) 
            m_imp->m_fixed_base_var_set.insert(j);
        

        TRACE("lar_solver_feas", tout << "j = " << j << " became " << (this->column_is_feasible(j) ? "feas" : "non-feas") << ", and " << (this->column_is_bounded(j) ? "bounded" : "non-bounded") << std::endl;);
        if (m_update_column_bound_callback)
            m_update_column_bound_callback(j);

        if (settings().dump_bound_lemmas()) {
            if (kind == LE)
                write_bound_lemma(j, false, __func__, std::cout);
            else if (kind == GE)
                write_bound_lemma(j, true, __func__, std::cout);
            else
                NOT_IMPLEMENTED_YET();
        }
    }

    void lar_solver::insert_to_columns_with_changed_bounds(unsigned j) {
        m_imp->m_columns_with_changed_bounds.insert(j);
        TRACE("lar_solver", tout << "column " << j << (column_is_feasible(j) ? " feas" : " non-feas") << "\n";);
    }

    void lar_solver::update_column_type_and_bound_check_on_equal(unsigned j,
                                                                 const mpq& right_side,
                                                                 constraint_index constr_index,
                                                                 unsigned& equal_to_j) {
        update_column_type_and_bound(j, right_side, constr_index);
        equal_to_j = null_lpvar;
        if (column_is_fixed(j)) {
            m_imp->register_in_fixed_var_table(j, equal_to_j);
        }
    }

    constraint_index lar_solver::add_var_bound_on_constraint_for_term(lpvar j, lconstraint_kind kind, const mpq& right_side) {
        mpq rs = adjust_bound_for_int(j, kind, right_side);
        SASSERT(bound_is_integer_for_integer_column(j, rs));
        return m_imp->m_constraints.add_term_constraint(j, m_imp->m_columns[j].term(), kind, rs);
    }

    struct lar_solver::scoped_backup {
        lar_solver& m_s;
        scoped_backup(lar_solver& s) : m_s(s) {
            m_s.get_core_solver().backup_x();
        }
        ~scoped_backup() {
            m_s.get_core_solver().restore_x();
        }
    };
   
    void lar_solver::update_column_type_and_bound_with_ub(unsigned j, lp::lconstraint_kind kind, const mpq& right_side, u_dependency* dep) {
        SASSERT(column_has_upper_bound(j));
        if (column_has_lower_bound(j)) {
            update_bound_with_ub_lb(j, kind, right_side, dep);
        }
        else {
            update_bound_with_ub_no_lb(j, kind, right_side, dep);
        }
    }

    void lar_solver::update_column_type_and_bound_with_no_ub(unsigned j, lp::lconstraint_kind kind, const mpq& right_side, u_dependency* dep) {
        SASSERT(!column_has_upper_bound(j));
        if (column_has_lower_bound(j)) {
            update_bound_with_no_ub_lb(j, kind, right_side, dep);
        }
        else {
            update_bound_with_no_ub_no_lb(j, kind, right_side, dep);
        }
    }

    void lar_solver::update_bound_with_ub_lb(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep) {
        SASSERT(column_has_lower_bound(j) && column_has_upper_bound(j));
        SASSERT(get_core_solver().m_column_types[j] == column_type::boxed ||
                  get_core_solver().m_column_types[j] == column_type::fixed);

        mpq y_of_bound(0);
        switch (kind) {
            case LT:
                y_of_bound = -1;
                Z3_fallthrough;
            case LE: {
                auto up = numeric_pair<mpq>(right_side, y_of_bound);
                if (up < get_lower_bound(j)) {
                    set_crossed_bounds_column_and_deps(j, true, dep);
                }
                else {
                    if (up >= get_upper_bound(j))
                        return;
                    set_upper_bound_witness(j, dep, up);
                }
                break;
            }
            case GT:
                y_of_bound = 1;
                Z3_fallthrough;
            case GE: {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                if (low > get_upper_bound(j)) {
                    set_crossed_bounds_column_and_deps(j, false, dep);
                } 
                else {
                    if (low < get_lower_bound(j))
                        return;                    
                    set_lower_bound_witness(j, dep, low);
                    get_core_solver().m_column_types[j] = (low == get_upper_bound(j) ? column_type::fixed : column_type::boxed);
                }
                break;                
            } 
            case EQ: {
                auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
                if (v > get_upper_bound(j))
                    set_crossed_bounds_column_and_deps(j, false, dep);                
                else if (v < get_lower_bound(j)) 
                    set_crossed_bounds_column_and_deps(j, true, dep);                
                else {
                    set_upper_bound_witness(j, dep, v);
                    set_lower_bound_witness(j, dep, v);
                }
                break;
            }

            default:
                UNREACHABLE();
        }
        numeric_pair<mpq> const& lo = get_lower_bound(j);
        numeric_pair<mpq> const& hi = get_upper_bound(j);
        if (lo == hi)
            get_core_solver().m_column_types[j] = column_type::fixed;
    }
    
    void lar_solver::update_bound_with_no_ub_lb(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep) {
        SASSERT(column_has_lower_bound(j) && !column_has_upper_bound(j));
        SASSERT(get_core_solver().m_column_types[j] == column_type::lower_bound);

        mpq y_of_bound(0);
        switch (kind) {
            case LT:
                y_of_bound = -1;
                Z3_fallthrough;
            case LE: {
                auto up = numeric_pair<mpq>(right_side, y_of_bound);
                if (up < get_lower_bound(j)) {
                    set_crossed_bounds_column_and_deps(j, true, dep);
                }
                else {
                    set_upper_bound_witness(j, dep, up);
                    get_core_solver().m_column_types[j] = (up == get_lower_bound(j) ? column_type::fixed : column_type::boxed);
                }
                break;
            } 
            case GT:
                y_of_bound = 1;
            case GE: {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                if (low < get_lower_bound(j)) {
                    return;
                }
                set_lower_bound_witness(j, dep, low);
                break;
            } 
            case EQ: {
                auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
                if (v < get_lower_bound(j)) {
                    set_crossed_bounds_column_and_deps(j, true, dep);
                } 
                else {
                    set_upper_bound_witness(j, dep, v);
                    set_lower_bound_witness(j, dep, v);
                    get_core_solver().m_column_types[j] = column_type::fixed;
                }
                break;
            }

            default:
                UNREACHABLE();
        }
    }
   
    void lar_solver::update_bound_with_ub_no_lb(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep) {
        SASSERT(!column_has_lower_bound(j) && column_has_upper_bound(j));
        SASSERT(get_core_solver().m_column_types[j] == column_type::upper_bound);
        mpq y_of_bound(0);
        switch (kind) {
        case LT:
            y_of_bound = -1;
            Z3_fallthrough;
        case LE:
        {
            auto up = numeric_pair<mpq>(right_side, y_of_bound);
            if (up >= get_upper_bound(j)) 
                return;
            set_upper_bound_witness(j, dep, up);
        }
        break;
        case GT:
            y_of_bound = 1;
            Z3_fallthrough;
        case GE:
        {
            auto low = numeric_pair<mpq>(right_side, y_of_bound);
            if (low > get_upper_bound(j)) {
                set_crossed_bounds_column_and_deps(j, false, dep);
            }
            else {
                set_lower_bound_witness(j, dep, low);
                get_core_solver().m_column_types[j] = (low == get_upper_bound(j) ? column_type::fixed : column_type::boxed);
            }
        }
        break;
        case EQ:
        {
            auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
            if (v > get_upper_bound(j)) {
                set_crossed_bounds_column_and_deps(j, false, dep);
            }
            else {
                set_upper_bound_witness(j, dep, v);
                set_lower_bound_witness(j, dep, v);
                get_core_solver().m_column_types[j] = column_type::fixed;
            }
            break;
        }

        default:
            UNREACHABLE();
        }
    }
   
    void lar_solver::update_bound_with_no_ub_no_lb(lpvar j, lconstraint_kind kind, const mpq& right_side, u_dependency* dep) {
        SASSERT(!column_has_lower_bound(j) && !column_has_upper_bound(j));

        mpq y_of_bound(0);
        switch (kind) {
            case LT:
                y_of_bound = -1;
                Z3_fallthrough;
            case LE: {
                auto up = numeric_pair<mpq>(right_side, y_of_bound);
                set_upper_bound_witness(j, dep, up);
                get_core_solver().m_column_types[j] = column_type::upper_bound;
            } break;
            case GT:
                y_of_bound = 1;
                Z3_fallthrough;
            case GE: {
                auto low = numeric_pair<mpq>(right_side, y_of_bound);
                set_lower_bound_witness(j, dep, low);
                get_core_solver().m_column_types[j] = column_type::lower_bound;

            } break;
            case EQ: {
                auto v = numeric_pair<mpq>(right_side, zero_of_type<mpq>());
                set_upper_bound_witness(j, dep, v);
                set_lower_bound_witness(j, dep, v);
                get_core_solver().m_column_types[j] = column_type::fixed;
                break;
            }

            default:
                UNREACHABLE();
        }
    }    

    lpvar lar_solver::to_column(unsigned ext_j) const {
        return m_imp->m_var_register.external_to_local(ext_j);
    }
    
    bool lar_solver::move_lpvar_to_value(lpvar j, mpq const& value) {
        if (is_base(j))
            return false;

        impq ivalue(value);
        auto& lcs = get_core_solver();

        if (column_has_upper_bound(j) && lcs.m_r_upper_bounds[j] < ivalue)
            return false;
        if (column_has_lower_bound(j) && lcs.m_r_lower_bounds[j] > ivalue)
            return false;
        
        set_value_for_nbasic_column(j, ivalue);
        return true;
    }


    bool lar_solver::tighten_term_bounds_by_delta(lpvar j, const impq& delta) {
        SASSERT(column_has_term(j));
        TRACE("cube", tout << "delta = " << delta << std::endl;
              m_imp->m_int_solver->display_column(tout, j); );
        if (column_has_upper_bound(j) && column_has_lower_bound(j)) {
            if (get_upper_bound(j) - delta < get_lower_bound(j) + delta) {
                TRACE("cube", tout << "cannot tighten, delta = " << delta;);
                return false;
            }
        }
        TRACE("cube", tout << "can tighten";);
        if (column_has_upper_bound(j)) {
            if (!is_zero(delta.y) || !is_zero(get_upper_bound(j).y))
                add_var_bound(j, lconstraint_kind::LT, get_upper_bound(j).x - delta.x);
            else
                add_var_bound(j, lconstraint_kind::LE, get_upper_bound(j).x - delta.x);
        }
        if (column_has_lower_bound(j)) {
            if (!is_zero(delta.y) || !is_zero(get_lower_bound(j).y))
                add_var_bound(j, lconstraint_kind::GT, get_lower_bound(j).x + delta.x);
            else
                add_var_bound(j, lconstraint_kind::GE, get_lower_bound(j).x + delta.x);
        }
        return true;
    }


    void lar_solver::round_to_integer_solution() {
        for (unsigned j = 0; j < column_count(); j++) {
            if (!column_is_int(j)) continue;
            if (column_has_term(j)) continue;
            impq & v = get_core_solver().r_x(j);
            if (v.is_int())
                continue;
            TRACE("cube", m_imp->m_int_solver->display_column(tout, j););
            impq flv = impq(floor(v));
            auto del = flv - v; // del is negative
            if (del < -impq(mpq(1, 2))) {
                del = impq(one_of_type<mpq>()) + del;
                v = impq(ceil(v));
            }
            else {
                v = flv;
            }
            m_imp->m_incorrect_columns.insert(j);
            TRACE("cube", tout << "new val = " << v << " column: " << j << "\n";);
        }
        if (!m_imp->m_incorrect_columns.empty()) {
            fix_terms_with_rounded_columns();
            m_imp->m_incorrect_columns.reset();
        }
    }

    void lar_solver::fix_terms_with_rounded_columns() {

        for (const lar_term* t : m_imp->m_terms) {
            lpvar j = t->j();
            if (!m_imp->m_columns[j].associated_with_row())
                continue;
            bool need_to_fix = false;
          
            for (lar_term::ival p : * t) {
                if (m_imp->m_incorrect_columns.contains(p.j())) {
                    need_to_fix = true;
                    break;
                }
            }
            if (need_to_fix) {
                impq v = t->apply(get_core_solver().r_x());
                get_core_solver().m_r_solver.update_x(j, v);
            }
        }

        SASSERT(ax_is_correct());
    }

    // return true if all y coords are zeroes
    bool lar_solver::sum_first_coords(const lar_term& t, mpq& val) const {
        val = zero_of_type<mpq>();
        for (lar_term::ival c : t) {
            const auto& x = get_core_solver().r_x(c.j());
            if (!is_zero(x.y))
                return false;
            val += x.x * c.coeff();
        }
        return true;
    }

    bool lar_solver::get_equality_and_right_side_for_term_on_current_x(lpvar j, mpq& rs, u_dependency*& ci, bool& upper_bound) const {
        SASSERT(column_has_term(j));
        if (!column_is_int(j)) // todo - allow for the next version of hnf
            return false;
        bool rs_is_calculated = false;
        mpq b;
        bool is_strict;
        const lar_term& term = get_term(j);
        if (has_upper_bound(j, ci, b, is_strict) && !is_strict) {
            SASSERT(b.is_int());
            if (!sum_first_coords(term, rs))
                return false;
            rs_is_calculated = true;
            if (rs == b) {
                upper_bound = true;
                return true;
            }
        }
        if (has_lower_bound(j, ci, b, is_strict) && !is_strict) {
            if (!rs_is_calculated) {
                if (!sum_first_coords(term, rs))
                    return false;
            }
            SASSERT(b.is_int());

            if (rs == b) {
                upper_bound = false;
                return true;
            }
        }
        return false;
    }

    void lar_solver::set_cut_strategy(unsigned cut_frequency) {
        if (cut_frequency < 4) {
            settings().m_int_gomory_cut_period = 2; // do it often
            settings().set_hnf_cut_period(4); // also create hnf cuts
        }
        else if (cut_frequency == 4) { // enable all cuts and cube equally
            settings().m_int_gomory_cut_period = 4;
            settings().set_hnf_cut_period(4);
        }
        else {
            // disable all heuristics except cube
            settings().m_int_gomory_cut_period = 10000000;
            settings().set_hnf_cut_period(100000000);
        }
    }


    void lar_solver::register_normalized_term(const lar_term& t, lpvar j) {
        mpq a;
        lar_term normalized_t = t.get_normalized_by_min_var(a);
        TRACE("lar_solver_terms", tout << "t="; print_term_as_indices(t, tout);
        tout << ", normalized_t="; print_term_as_indices(normalized_t, tout) << "\n";);
        if (m_imp->m_normalized_terms_to_columns.find(normalized_t) == m_imp->m_normalized_terms_to_columns.end()) {
            m_imp->m_normalized_terms_to_columns[normalized_t] = std::make_pair(a, j);
        }
        else {
            TRACE("lar_solver_terms", tout << "the term has been seen already\n";);
        }
    }

    void lar_solver::deregister_normalized_term(const lar_term& t) {
        TRACE("lar_solver_terms", tout << "deregister term ";
        print_term_as_indices(t, tout) << "\n";);
        mpq a;
        lar_term normalized_t = t.get_normalized_by_min_var(a);
        m_imp->m_normalized_terms_to_columns.erase(normalized_t);
    }

    void lar_solver::register_existing_terms() {
        if (!m_imp->m_need_register_terms) {
            TRACE("nla_solver", tout << "registering " << m_imp->m_terms.size() << " terms\n";);
            for (const lar_term* t  : m_imp->m_terms) {
                register_normalized_term(*t, t->j());
            }
        }
        m_imp->m_need_register_terms = true;
    }
    // a_j.first gives the normalised coefficient,
    // a_j.second givis the column
    bool lar_solver::fetch_normalized_term_column(const lar_term& c, std::pair<mpq, lpvar>& a_j) const {
        TRACE("lar_solver_terms", print_term_as_indices(c, tout << "looking for term ") << "\n";);
        SASSERT(c.is_normalized());
        auto it = m_imp->m_normalized_terms_to_columns.find(c);
        if (it != m_imp->m_normalized_terms_to_columns.end()) {
            TRACE("lar_solver_terms", tout << "got " << it->second << "\n";);
            a_j = it->second;
            return true;
        }
        TRACE("lar_solver_terms", tout << "have not found\n";);
        return false;
    }

    bool lar_solver::are_equal(lpvar j, lpvar k) {
        vector<std::pair<mpq, lpvar>> coeffs;        
        coeffs.push_back(std::make_pair(mpq(1), j));
        coeffs.push_back(std::make_pair(mpq(-1), k));
        lar_term t(coeffs);
        subst_known_terms(&t);
        return t.is_empty();
    }

    std::pair<constraint_index, constraint_index> lar_solver::add_equality(lpvar j, lpvar k) {
        vector<std::pair<mpq, lpvar>> coeffs;
        
        coeffs.push_back(std::make_pair(mpq(1), j));
        coeffs.push_back(std::make_pair(mpq(-1), k));
        unsigned ej = add_term(coeffs, UINT_MAX); // UINT_MAX is the external null var
            

        if (get_column_value(j) != get_column_value(k))
            set_status(lp_status::UNKNOWN);

        return std::pair<constraint_index, constraint_index>(
            add_var_bound(ej, lconstraint_kind::LE, mpq(0)),
            add_var_bound(ej, lconstraint_kind::GE, mpq(0)));
    }

    bool lar_solver::inside_bounds(lpvar j, const impq& val) const {
        if (column_has_upper_bound(j) && val > get_upper_bound(j))
            return false;
        if (column_has_lower_bound(j) && val < get_lower_bound(j))
            return false;
        return true;
    }
    // If lower_bound is true than the new asserted upper bound is less than the existing lower bound.
    // Otherwise the new asserted lower bound is is greater than the existing upper bound.
    // dep is the reason for the new bound

    void lar_solver::set_crossed_bounds_column_and_deps(unsigned j, bool lower_bound, u_dependency* dep) {
        if (m_imp->m_crossed_bounds_column != null_lpvar) return; // already set
        SASSERT(m_imp->m_crossed_bounds_deps == nullptr);
        set_status(lp_status::INFEASIBLE);
        m_imp->m_crossed_bounds_column = j;
        const auto& ul = m_imp->m_columns[j];
        u_dependency* bdep = lower_bound? ul.lower_bound_witness() : ul.upper_bound_witness();
        SASSERT(bdep != nullptr);
        m_imp->m_crossed_bounds_deps = dep_manager().mk_join(bdep, dep);
        TRACE("dio", tout << "crossed_bound_deps:\n";  print_explanation(tout, flatten(m_imp->m_crossed_bounds_deps)) << "\n";);
    }
    const indexed_uint_set & lar_solver::touched_rows() const { return m_imp->m_touched_rows; }
    indexed_uint_set & lar_solver::touched_rows() { return m_imp->m_touched_rows; }

    void lar_solver::collect_more_rows_for_lp_propagation(){
        for (auto j : m_imp->m_columns_with_changed_bounds)
            detect_rows_with_changed_bounds_for_column(j); 
    }
    std::ostream& lar_solver::print_explanation(
        std::ostream& out, const explanation& exp,
        std::function<std::string(lpvar)> var_str) const {
        out << "expl: ";
        unsigned i = 0;
        for (auto p : exp) {
            out << "(" << p.ci() << ")";
            constraints().display(out, var_str, p.ci());
            if (++i < exp.size())
                out << "      ";
        }
        return out;
    }
    std::string lar_solver::get_bounds_string(unsigned j) const {
        mpq lb, ub;
        bool is_strict_lower = false, is_strict_upper = false;
        u_dependency* dep = nullptr;
        bool has_lower = has_lower_bound(j, dep, lb, is_strict_lower);
        bool has_upper = has_upper_bound(j, dep, ub, is_strict_upper);
    
        std::ostringstream oss;
    
        if (!has_lower && !has_upper) {
            oss << "(-oo, oo)";
        } 
        else if (has_lower && !has_upper) {
            oss << (is_strict_lower ? "(" : "[") << lb << ", oo)";
        }
        else if (!has_lower && has_upper) {
            oss << "(-oo, " << ub << (is_strict_upper ? ")" : "]");
        }
        else { // has both bounds
            oss << (is_strict_lower ? "(" : "[") << lb << ", " << ub << (is_strict_upper ? ")" : "]");
        }
    
        return oss.str();
    }
        // Helper function to format constants in SMT2 format
    std::string format_smt2_constant(const mpq& val) {
        if (val.is_neg()) {
            // Negative constant - use unary minus operator
            return std::string("(- ") + abs(val).to_string() + ")";
        } else {
            // Positive or zero constant - write directly
            return val.to_string();
        }
    }

    void lar_solver::write_bound_lemma(unsigned j, bool is_low, const std::string& location, std::ostream & out) const {
        // Get the bound value and dependency
        mpq bound_val;
        bool is_strict = false;
        u_dependency* bound_dep = nullptr;
    
        // Get the appropriate bound info
        if (is_low) {
            if (!has_lower_bound(j, bound_dep, bound_val, is_strict)) {
                out << "; Error: Variable " << j << " has no lower bound\n";
                return;
            }
        } else {
            if (!has_upper_bound(j, bound_dep, bound_val, is_strict)) {
                out << "; Error: Variable " << j << " has no upper bound\n";
                return;
            }
        }
            // Start SMT2 file
        out << "(set-info : \"generated at " << location;
        out << " for " << (is_low ? "lower" : "upper") << " bound of variable " << j << ",";
        out << " bound value: " << bound_val << (is_strict ? (is_low ? " < " : " > ") : (is_low ? " <= " : " >= ")) << "x" << j << "\")\n";
        
        // Collect all variables used in dependencies
        std::unordered_set<unsigned> vars_used;
        vars_used.insert(j);
        bool is_int = column_is_int(j);
        
        // Linearize the dependencies
        svector<constraint_index> deps;
        dep_manager().linearize(bound_dep, deps);
        
        // Collect variables from constraints
        for (auto ci : deps) {
            const auto& c = m_imp->m_constraints[ci];
            for (const auto& p : c.coeffs()) {
                vars_used.insert(p.second);
                if (!column_is_int(p.second))
                    is_int = false;
            }
        }
        
        // Collect variables from terms
        std::unordered_set<unsigned> term_variables;
        for (unsigned var : vars_used) {
            if (column_has_term(var)) {
                const lar_term& term = get_term(var);
                for (const auto& p : term) {
                    term_variables.insert(p.j());
                    if (!column_is_int(p.j()))
                        is_int = false;
                }
            }
        }
        // Add term variables to vars_used
        vars_used.insert(term_variables.begin(), term_variables.end());
                
        if (is_int) {
            out << "(set-logic QF_LIA)\n\n";
        }
        
        // Declare variables
        out << "; Variable declarations\n";
        for (unsigned var : vars_used) {
            out << "(declare-const x" << var << " " << (column_is_int(var) ? "Int" : "Real") << ")\n";
        }
        out << "\n";
        
        // Define term relationships
        out << "; Term definitions\n";
        for (unsigned var : vars_used) {
            if (column_has_term(var)) {
                const lar_term& term = get_term(var);
                out << "(assert (= x" << var << " ";
                    
                if (term.size() == 0) {
                    out << "0";
                } else {
                    if (term.size() > 1) out << "(+ ";
                        
                    bool first = true;
                    for (const auto& p : term) {
                        if (first) first = false;
                        else out << " ";
                            
                        if (p.coeff().is_one()) {
                            out << "x" << p.j();
                        } else {
                            out << "(* " << format_smt2_constant(p.coeff()) << " x" << p.j() << ")";
                        }
                    }
                        
                    if (term.size() > 1) out << ")";
                }
                    
                out << "))\n";
            }
        }
        out << "\n";
        
        // Add assertions for the dependencies
        out << "; Bound dependencies\n";
        
        for (auto ci : deps) {
            const auto& c = m_imp->m_constraints[ci];
            out << "(assert ";
            
            // Handle the constraint type and expression
            auto k = c.kind();
            
            // Normal constraint with variables
            switch (k) {
            case LE: out << "(<= "; break;
            case LT: out << "(< "; break;
            case GE: out << "(>= "; break;
            case GT: out << "(> "; break;
            case EQ: out << "(= "; break;
            default: out << "(unknown-constraint-type "; break;
            }
            
            // Left-hand side (variables)
            if (c.coeffs().size() == 1) {
                // Single variable
                auto p = *c.coeffs().begin();
                if (p.first.is_one()) {
                    out << "x" << p.second << " ";
                } else {
                    out << "(* " << format_smt2_constant(p.first) << " x" << p.second << ") ";
                }
            } else {
                // Multiple variables - create a sum
                out << "(+ ";
                for (auto const& p : c.coeffs()) {
                    if (p.first.is_one()) {
                        out << "x" << p.second << " ";
                    } else {
                        out << "(* " << format_smt2_constant(p.first) << " x" << p.second << ") ";
                    }
                }
                out << ") ";
            }
            
            // Right-hand side (constant)
            out << format_smt2_constant(c.rhs());
            out << "))\n";
        }
        out << "\n";
        
        // Now add the assertion that contradicts the bound
        out << "; Negation of the derived bound\n";
        if (is_low) {
            if (is_strict) {
                out << "(assert (<= x" << j << " " << format_smt2_constant(bound_val) << "))\n";
            } else {
                out << "(assert (< x" << j << " " << format_smt2_constant(bound_val) << "))\n";
            }
        } else {
            if (is_strict) {
                out << "(assert (>= x" << j << " " << format_smt2_constant(bound_val) << "))\n";
            } else {
                out << "(assert (> x" << j << " " << format_smt2_constant(bound_val) << "))\n";
            }
        }
        out << "\n";
        
        // Check sat and get model if available
        out << "(check-sat)\n";
        out << "(exit)\n";
        }
} // namespace lp


