/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#pragma once
#include "util/vector.h"
#include <utility>
#include "util/debug.h"
#include "util/buffer.h"
#include <unordered_map>
#include <unordered_set>
#include <string>
#include "util/lp/lar_constraints.h"
#include <functional>
#include "util/lp/lar_core_solver.h"
#include <algorithm>
#include "util/lp/numeric_pair.h"
#include "util/lp/scaler.h"
#include "util/lp/lp_primal_core_solver.h"
#include "util/lp/random_updater.h"
#include <stack>
#include "util/lp/stacked_map.h"
#include "util/lp/stacked_value.h"
#include "util/lp/stacked_vector.h"
#include "util/lp/stacked_unordered_set.h"
#include "util/lp/iterator_on_pivot_row.h"
#include "util/lp/implied_bound.h"
#include "util/lp/bound_analyzer_on_row.h"
#include "util/lp/iterator_on_term_with_basis_var.h"
#include "util/lp/iterator_on_row.h"
#include "util/lp/quick_xplain.h"
#include "util/lp/conversion_helper.h"
namespace lean {

class lar_solver : public column_namer {
    //////////////////// fields //////////////////////////
    lp_settings                             m_settings;
    stacked_value<lp_status>                m_status;
    stacked_value<simplex_strategy_enum>    m_simplex_strategy;
    std::unordered_map<unsigned, var_index> m_ext_vars_to_columns;
    vector<unsigned>                        m_columns_to_ext_vars_or_term_indices;
    stacked_vector<ul_pair>                 m_vars_to_ul_pairs;
    vector<lar_base_constraint*>            m_constraints;
    stacked_value<unsigned>                 m_constraint_count;
    // the set of column indices j such that bounds have changed for j
    int_set                                 m_columns_with_changed_bound;
    int_set                                 m_rows_with_changed_bounds;
    int_set                                 m_basic_columns_with_changed_cost;
    stacked_value<int>                      m_infeasible_column_index; // such can be found at the initialization step
    stacked_value<unsigned>                 m_term_count;
    vector<lar_term*>                       m_terms;
    vector<lar_term*>                       m_orig_terms;
    const var_index                         m_terms_start_index;
    indexed_vector<mpq>                     m_column_buffer;    
public:
    lar_core_solver m_mpq_lar_core_solver;
    unsigned constraint_count() const {
        return m_constraints.size();
    }
    const lar_base_constraint& get_constraint(unsigned ci) const {
        return *(m_constraints[ci]);
    }

    ////////////////// methods ////////////////////////////////
    static_matrix<mpq, numeric_pair<mpq>> & A_r() { return m_mpq_lar_core_solver.m_r_A;}
    static_matrix<mpq, numeric_pair<mpq>> const & A_r() const { return m_mpq_lar_core_solver.m_r_A;}
    static_matrix<double, double> & A_d() { return m_mpq_lar_core_solver.m_d_A;}
    static_matrix<double, double > const & A_d() const { return m_mpq_lar_core_solver.m_d_A;}
    
    static bool valid_index(unsigned j){ return static_cast<int>(j) >= 0;}


public:
    lp_settings & settings() { return m_settings;}

    lp_settings const & settings() const { return m_settings;}

    void clear() {lean_assert(false); // not implemented
    }


    lar_solver() : m_status(OPTIMAL),
                   m_infeasible_column_index(-1),
                   m_terms_start_index(1000000),
                   m_mpq_lar_core_solver(m_settings, *this)
    {}
    
    void set_propagate_bounds_on_pivoted_rows_mode(bool v) {
        m_mpq_lar_core_solver.m_r_solver.m_pivoted_rows = v? (& m_rows_with_changed_bounds) : nullptr;
    }

    virtual ~lar_solver(){
        for (auto c : m_constraints)
            delete c;
        for (auto t : m_terms)
            delete t;
        for (auto t : m_orig_terms)
            delete t;
    }

#include "util/lp/init_lar_solver.h"
    
    numeric_pair<mpq> const& get_value(var_index vi) const { return m_mpq_lar_core_solver.m_r_x[vi]; }

    bool is_term(var_index j) const {
        return j >= m_terms_start_index && j - m_terms_start_index < m_terms.size();
    }

    unsigned adjust_term_index(unsigned j) const {
        lean_assert(is_term(j));
        return j - m_terms_start_index;
    }


    bool use_lu() const { return m_settings.simplex_strategy() == simplex_strategy_enum::lu; }
    
    bool sizes_are_correct() const {
        lean_assert(strategy_is_undecided() || !m_mpq_lar_core_solver.need_to_presolve_with_double_solver() || A_r().column_count() == A_d().column_count());
        lean_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_solver.m_column_types.size());
        lean_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_solver.m_costs.size());
        lean_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_x.size());
        return true;
    }
    
 
    void print_implied_bound(const implied_bound& be, std::ostream & out) const {
        out << "implied bound\n";
        unsigned v = be.m_j;
        if (is_term(v)) {
            out << "it is a term number " << be.m_j << std::endl;
            print_term(*m_orig_terms[be.m_j - m_terms_start_index],  out);
        }
        else {
            out << get_column_name(v);
        }
        out << " " << lconstraint_kind_string(be.kind()) << " "  << be.m_bound << std::endl;
        // for (auto & p : be.m_explanation) {
        //     out << p.first << " : ";
        //     print_constraint(p.second, out);
        // }
        
        // m_mpq_lar_core_solver.m_r_solver.print_column_info(be.m_j< m_terms_start_index? be.m_j : adjust_term_index(be.m_j), out);
        out << "end of implied bound" << std::endl;
    }
    
    bool implied_bound_is_correctly_explained(implied_bound const & be, const vector<std::pair<mpq, unsigned>> & explanation) const {
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
        lean_assert(n_of_G == 0 || n_of_L == 0);
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
            const lar_term * t = m_orig_terms[adjust_term_index(be.m_j)];
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

    
    void analyze_new_bounds_on_row(
                                   unsigned row_index,
                                   bound_propagator & bp) {
        lean_assert(!use_tableau());
        iterator_on_pivot_row<mpq> it(m_mpq_lar_core_solver.get_pivot_row(), m_mpq_lar_core_solver.m_r_basis[row_index]);
     
        bound_analyzer_on_row ra_pos(it,
                                     zero_of_type<numeric_pair<mpq>>(),
                                     row_index,
                                     bp
                                     );
        ra_pos.analyze();
    }

    void analyze_new_bounds_on_row_tableau(
                                           unsigned row_index,
                                           bound_propagator & bp
                                           ) {

        if (A_r().m_rows[row_index].size() > settings().max_row_length_for_bound_propagation)
            return;
        iterator_on_row<mpq> it(A_r().m_rows[row_index]);
        lean_assert(use_tableau());
        bound_analyzer_on_row::analyze_row(it,
                                           zero_of_type<numeric_pair<mpq>>(),
                                           row_index,
                                           bp
                                           );
    }

    
    void substitute_basis_var_in_terms_for_row(unsigned i) {
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
    
    void calculate_implied_bounds_for_row(unsigned i, bound_propagator & bp) {
        if(use_tableau()) {
            analyze_new_bounds_on_row_tableau(i, bp);
        } else {
            m_mpq_lar_core_solver.calculate_pivot_row(i);
            substitute_basis_var_in_terms_for_row(i);
            analyze_new_bounds_on_row(i, bp);
        }
    }

    /*
      void process_new_implied_evidence_for_low_bound(
      implied_bound_explanation& implied_evidence, // not pushed yet
      vector<bound_evidence> & bound_evidences,
      std::unordered_map<unsigned, unsigned> & improved_low_bounds) {

      unsigned existing_index;
      if (try_get_val(improved_low_bounds, implied_evidence.m_j, existing_index)) {
      // we are improving the existent bound
      bound_evidences[existing_index] = fill_bound_evidence(implied_evidence);
      } else {
      improved_low_bounds[implied_evidence.m_j] = bound_evidences.size();
      bound_evidences.push_back(fill_bound_evidence(implied_evidence));
      }
      }
    
      void fill_bound_evidence_on_term(implied_bound & ie, implied_bound& be) {
      lean_assert(false);
      }
      void fill_implied_bound_on_row(implied_bound & ie, implied_bound& be) {
      iterator_on_row<mpq> it(A_r().m_rows[ie.m_row_or_term_index]);
      mpq a; unsigned j;
      bool toggle = ie.m_coeff_before_j_is_pos;
      if (!ie.m_is_low_bound)
      toggle = !toggle;
      while (it.next(a, j)) {
      if (j == ie.m_j) continue;
      const ul_pair & ul = m_vars_to_ul_pairs[j];
            
      if (is_neg(a)) { // so the monoid has a positive coeff on the right side
      constraint_index witness = toggle ? ul.m_low_bound_witness : ul.m_upper_bound_witness;
      lean_assert(is_valid(witness));
      be.m_explanation.emplace_back(a, witness);
      }
      }
      }
    */
    /*
      implied_bound fill_implied_bound_for_low_bound(implied_bound& ie) {
      implied_bound be(ie.m_j, ie.m_bound.y.is_zero() ? GE : GT, ie.m_bound.x);
      if (is_term(ie.m_row_or_term_index)) {
      fill_implied_bound_for_low_bound_on_term(ie, be);
      }
      else {
      fill_implied_bound_for_low_bound_on_row(ie, be);
      }
      return be;
      }

      implied_bound fill_implied_bound_for_upper_bound(implied_bound& implied_evidence) {
      lean_assert(false);
        
      be.m_j = implied_evidence.m_j;
      be.m_bound = implied_evidence.m_bound.x;
      be.m_kind = implied_evidence.m_bound.y.is_zero() ? LE : LT;
      for (auto t : implied_evidence.m_vector_of_bound_signatures) {
      const ul_pair & ul = m_vars_to_ul_pairs[t.m_column_index];
      constraint_index witness = t.m_low_bound ? ul.m_low_bound_witness : ul.m_upper_bound_witness;
      lean_assert(is_valid(witness));
      be.m_explanation.emplace_back(t.m_coeff, witness);
      }
        
      }
    */
    /*
      void process_new_implied_evidence_for_upper_bound(
      implied_bound& implied_evidence, 
      vector<implied_bound> & implied_bounds,
      std::unordered_map<unsigned, unsigned> & improved_upper_bounds) {
      unsigned existing_index;
      if (try_get_val(improved_upper_bounds, implied_evidence.m_j, existing_index)) {
      implied_bound & be = implied_bounds[existing_index];
      be.m_explanation.clear();
      // we are improving the existent bound improve the existing bound
      be = fill_implied_bound_for_upper_bound(implied_evidence);
      } else {
      improved_upper_bounds[implied_evidence.m_j] = implied_bounds.size();
      implied_bounds.push_back(fill_implied_bound_for_upper_bound(implied_evidence));
      }
      }
    */
    //    implied_bound * get_existing_
  
    linear_combination_iterator<mpq> * create_new_iter_from_term(unsigned term_index) const {
        lean_assert(false); // not implemented
        return nullptr;
        //        new linear_combination_iterator_on_vector<mpq>(m_terms[adjust_term_index(term_index)]->coeffs_as_vector());
    }

    unsigned adjust_column_index_to_term_index(unsigned j) const {
        unsigned ext_var_or_term = m_columns_to_ext_vars_or_term_indices[j];
        return ext_var_or_term < m_terms_start_index ? j : ext_var_or_term;
    }
    
    void propagate_bounds_on_a_term(const lar_term& t, bound_propagator & bp, unsigned term_offset) {
        lean_assert(false); // not implemented
    }


    void explain_implied_bound(implied_bound & ib, bound_propagator & bp) {
        unsigned i = ib.m_row_or_term_index;
        int bound_sign = ib.m_is_low_bound? 1: -1;
        int j_sign = (ib.m_coeff_before_j_is_pos ? 1 :-1) * bound_sign;
        unsigned m_j = ib.m_j;
        if (is_term(m_j)) {
            m_j = m_ext_vars_to_columns[m_j];
        }
        for (auto const& r : A_r().m_rows[i]) {
            unsigned j = r.m_j;
            mpq const& a = r.get_val();
            if (j == m_j) continue;
            if (is_term(j)) {
                j = m_ext_vars_to_columns[j];
            } 
            int a_sign = is_pos(a)? 1: -1;
            int sign = j_sign * a_sign;
            const ul_pair & ul =  m_vars_to_ul_pairs[j];
            auto witness = sign > 0? ul.upper_bound_witness(): ul.low_bound_witness();
            lean_assert(is_valid(witness));
            bp.consume(a, witness);
        }
        // lean_assert(implied_bound_is_correctly_explained(ib, explanation));
    }


    bool term_is_used_as_row(unsigned term) const {
		lean_assert(is_term(term));
		return contains(m_ext_vars_to_columns, term);
    }
    
    void propagate_bounds_on_terms(bound_propagator & bp) {
        for (unsigned i = 0; i < m_terms.size(); i++) {
            if (term_is_used_as_row(i + m_terms_start_index))
                continue; // this term is used a left side of a constraint,
                          // it was processed as a touched row if needed
            propagate_bounds_on_a_term(*m_terms[i], bp, i);
        }
    }


    // goes over touched rows and tries to induce bounds
    void propagate_bounds_for_touched_rows(bound_propagator & bp) {
        if (!use_tableau())
            return;  // ! todo : enable bound propagaion here. The current bug is that after the pop
        // the changed terms become incorrect!

        for (unsigned i : m_rows_with_changed_bounds.m_index) {
            calculate_implied_bounds_for_row(i, bp);
        }
        m_rows_with_changed_bounds.clear();
        if (!use_tableau()) {
            propagate_bounds_on_terms(bp);
        }
    }

    lp_status get_status() const { return m_status;}

    void set_status(lp_status s) {m_status = s;}

    lp_status find_feasible_solution() {
        if (strategy_is_undecided())
            decide_on_strategy_and_adjust_initial_state();

        m_mpq_lar_core_solver.m_r_solver.m_look_for_feasible_solution_only = true;
        return solve();
    }
    
    lp_status solve() {
        if (m_status == INFEASIBLE) {
            return m_status;
        }
        solve_with_core_solver();
        if (m_status != INFEASIBLE) {
            if (m_settings.bound_propagation())
                detect_rows_with_changed_bounds();
        }
       
        m_columns_with_changed_bound.clear();
        return m_status;
    }

    void fill_explanation_from_infeasible_column(vector<std::pair<mpq, constraint_index>> & evidence) const{

        // this is the case when the lower bound is in conflict with the upper one
        const ul_pair & ul =  m_vars_to_ul_pairs[m_infeasible_column_index];
        evidence.push_back(std::make_pair(numeric_traits<mpq>::one(), ul.upper_bound_witness()));
        evidence.push_back(std::make_pair(-numeric_traits<mpq>::one(), ul.low_bound_witness()));
    }

    
    unsigned get_total_iterations() const { return m_mpq_lar_core_solver.m_r_solver.total_iterations(); }
    // see http://research.microsoft.com/projects/z3/smt07.pdf
    // This method searches for a feasible solution with as many different values of variables, reverenced in vars, as it can find
    // Attention, after a call to this method the non-basic variables don't necesserarly stick to their bounds anymore
    vector<unsigned> get_list_of_all_var_indices() const {
        vector<unsigned> ret;
        for (unsigned j = 0; j < m_mpq_lar_core_solver.m_r_heading.size(); j++)
            ret.push_back(j);
        return ret;
    }
    void push() {
        m_simplex_strategy = m_settings.simplex_strategy();
        m_simplex_strategy.push();
        m_status.push();
        m_vars_to_ul_pairs.push();
        m_infeasible_column_index.push();
        m_mpq_lar_core_solver.push();
        m_term_count = m_terms.size();
        m_term_count.push();
        m_constraint_count = m_constraints.size();
        m_constraint_count.push();
    }

    static void clean_large_elements_after_pop(unsigned n, int_set& set) {
        vector<int> to_remove;
        for (unsigned j: set.m_index)
            if (j >= n)
                to_remove.push_back(j);
        for (unsigned j : to_remove)
            set.erase(j);
    }

    static void shrink_inf_set_after_pop(unsigned n, int_set & set) {
        clean_large_elements_after_pop(n, set);
        set.resize(n);
    }

    
    void pop(unsigned k) {
        int n_was = static_cast<int>(m_ext_vars_to_columns.size());
		m_status.pop(k);
		m_infeasible_column_index.pop(k);
        unsigned n = m_vars_to_ul_pairs.peek_size(k);
		for (unsigned j = n_was; j-- > n;)
			m_ext_vars_to_columns.erase(m_columns_to_ext_vars_or_term_indices[j]);
		m_columns_to_ext_vars_or_term_indices.resize(n);
		if (m_settings.use_tableau()) {
            pop_tableau();
        }
		m_vars_to_ul_pairs.pop(k);

        m_mpq_lar_core_solver.pop(k);
        clean_large_elements_after_pop(n, m_columns_with_changed_bound);
        unsigned m = A_r().row_count();
        clean_large_elements_after_pop(m, m_rows_with_changed_bounds);
        clean_inf_set_of_r_solver_after_pop();
        lean_assert(m_settings.simplex_strategy() == simplex_strategy_enum::undecided ||
			(!use_tableau()) || m_mpq_lar_core_solver.m_r_solver.reduced_costs_are_correct_tableau());
        
        
        lean_assert(ax_is_correct());
        lean_assert(m_mpq_lar_core_solver.m_r_solver.inf_set_is_correct());
        m_constraint_count.pop(k);
        for (unsigned i = m_constraint_count; i < m_constraints.size(); i++)
            delete m_constraints[i];
        
        m_constraints.resize(m_constraint_count);
        m_term_count.pop(k);
        for (unsigned i = m_term_count; i < m_terms.size(); i++) {
            delete m_terms[i];
            delete m_orig_terms[i];
        }
        m_terms.resize(m_term_count);
        m_orig_terms.resize(m_term_count);
		m_simplex_strategy.pop(k);
		m_settings.simplex_strategy() = m_simplex_strategy;
		lean_assert(sizes_are_correct());
        lean_assert((!m_settings.use_tableau()) || m_mpq_lar_core_solver.m_r_solver.reduced_costs_are_correct_tableau());
    }
    
    vector<constraint_index> get_all_constraint_indices() const {
        vector<constraint_index> ret;
        constraint_index i = 0;
        while ( i < m_constraints.size())
            ret.push_back(i++);
        return ret;
    }

    bool maximize_term_on_tableau(const vector<std::pair<mpq, var_index>> & term,
                                  impq &term_max) {
        if (settings().simplex_strategy() == simplex_strategy_enum::undecided)
            decide_on_strategy_and_adjust_initial_state();
 
        m_mpq_lar_core_solver.solve();
        if (m_mpq_lar_core_solver.m_r_solver.get_status() == UNBOUNDED)
            return false;

        term_max = 0;
        for (auto & p : term)
            term_max += p.first * m_mpq_lar_core_solver.m_r_x[p.second];

        return true;
    }

    bool costs_are_zeros_for_r_solver() const {
        for (unsigned j = 0; j < m_mpq_lar_core_solver.m_r_solver.m_costs.size(); j++) {
            lean_assert(is_zero(m_mpq_lar_core_solver.m_r_solver.m_costs[j]));
        }
        return true;
    }
    bool reduced_costs_are_zeroes_for_r_solver() const {
        for (unsigned j = 0; j < m_mpq_lar_core_solver.m_r_solver.m_d.size(); j++) {
            lean_assert(is_zero(m_mpq_lar_core_solver.m_r_solver.m_d[j]));
        }
        return true;
    }
    
    void set_costs_to_zero(const vector<std::pair<mpq, var_index>> & term) {
        auto & rslv = m_mpq_lar_core_solver.m_r_solver;
        auto & jset = m_mpq_lar_core_solver.m_r_solver.m_inf_set; // hijack this set that should be empty right now
        lean_assert(jset.m_index.size()==0);
        
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
        
        lean_assert(reduced_costs_are_zeroes_for_r_solver());
        lean_assert(costs_are_zeros_for_r_solver());
    }

    void prepare_costs_for_r_solver(const vector<std::pair<mpq, var_index>> & term) {
        
        auto & rslv = m_mpq_lar_core_solver.m_r_solver;
        rslv.m_using_infeas_costs = false;
        lean_assert(costs_are_zeros_for_r_solver());
        lean_assert(reduced_costs_are_zeroes_for_r_solver());
        rslv.m_costs.resize(A_r().column_count(), zero_of_type<mpq>());
        for (auto & p : term) {
            unsigned j = p.second;
            rslv.m_costs[j] = p.first;
            if (rslv.m_basis_heading[j] < 0)
                rslv.m_d[j] += p.first;
            else
                rslv.update_reduced_cost_for_basic_column_cost_change(- p.first, j);
        }
        lean_assert(rslv.reduced_costs_are_correct_tableau());
    }
    
    bool maximize_term_on_corrected_r_solver(const vector<std::pair<mpq, var_index>> & term,
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
                m_mpq_lar_core_solver.m_r_solver.set_status(OPTIMAL);
                return ret;
            }
        case simplex_strategy_enum::tableau_costs:
            prepare_costs_for_r_solver(term);
            {
                bool ret = maximize_term_on_tableau(term, term_max);
                set_costs_to_zero(term);
                m_mpq_lar_core_solver.m_r_solver.set_status(OPTIMAL);
                return ret;
            }
            
        case simplex_strategy_enum::lu:
            lean_assert(false); // not implemented
            return false;
        default:
            lean_unreachable(); // wrong mode
        }
        return false;
    }    
    // starting from a given feasible state look for the maximum of the term
    // return true if found and false if unbounded
    bool maximize_term(const vector<std::pair<mpq, var_index>> & term,
                       impq &term_max) {
        lean_assert(m_mpq_lar_core_solver.m_r_solver.current_x_is_feasible());
        m_mpq_lar_core_solver.m_r_solver.m_look_for_feasible_solution_only = false;
        return maximize_term_on_corrected_r_solver(term, term_max);
    }
    

    
    const lar_term &  get_term(unsigned j) const {
        lean_assert(j >= m_terms_start_index);
        return *m_terms[j - m_terms_start_index];
    }

    void pop_core_solver_params() {
        pop_core_solver_params(1);
    }

    void pop_core_solver_params(unsigned k) {
        A_r().pop(k);
        A_d().pop(k);
    }


    void set_upper_bound_witness(var_index j, constraint_index ci) {
        ul_pair ul = m_vars_to_ul_pairs[j];
        ul.upper_bound_witness() = ci;
        m_vars_to_ul_pairs[j] = ul;
    }

    void set_low_bound_witness(var_index j, constraint_index ci) {
        ul_pair ul = m_vars_to_ul_pairs[j];
        ul.low_bound_witness() = ci;
        m_vars_to_ul_pairs[j] = ul;
    }


    void substitute_terms(const mpq & mult,
                          const vector<std::pair<mpq, var_index>>& left_side_with_terms,
                          vector<std::pair<mpq, var_index>> &left_side, mpq & right_side) const {
        for (auto & t : left_side_with_terms) {
            if (t.second < m_terms_start_index) {
                lean_assert(t.second < A_r().column_count());
                left_side.push_back(std::pair<mpq, var_index>(mult * t.first, t.second));
            } else {
                const lar_term & term = * m_terms[adjust_term_index(t.second)];
                substitute_terms(mult * t.first, left_side_with_terms, left_side, right_side);
                right_side -= mult * term.m_v;
            }
        }
    }


    void detect_rows_of_bound_change_column_for_nbasic_column(unsigned j) {
        if (A_r().row_count() != m_column_buffer.data_size())
            m_column_buffer.resize(A_r().row_count());
        else
            m_column_buffer.clear();
        lean_assert(m_column_buffer.size() == 0 && m_column_buffer.is_OK());
        
        m_mpq_lar_core_solver.m_r_solver.solve_Bd(j, m_column_buffer);
        for (unsigned i : m_column_buffer.m_index)
            m_rows_with_changed_bounds.insert(i);
    }


    
    void detect_rows_of_bound_change_column_for_nbasic_column_tableau(unsigned j) {
        for (auto & rc : m_mpq_lar_core_solver.m_r_A.m_columns[j])
            m_rows_with_changed_bounds.insert(rc.m_i);
    }

    bool use_tableau() const { return m_settings.use_tableau(); }

    bool use_tableau_costs() const {
        return m_settings.simplex_strategy() == simplex_strategy_enum::tableau_costs;
    }
    
    void detect_rows_of_column_with_bound_change(unsigned j) {
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

    void adjust_x_of_column(unsigned j) {
        lean_assert(false);
    }

    bool row_is_correct(unsigned i) const {
        numeric_pair<mpq> r = zero_of_type<numeric_pair<mpq>>();
        for (const auto & c : A_r().m_rows[i])
            r += c.m_value * m_mpq_lar_core_solver.m_r_x[c.m_j];
        return is_zero(r);
    }
    
    bool ax_is_correct() const {
        for (unsigned i = 0; i < A_r().row_count(); i++) {
            if (!row_is_correct(i))
                return false;
        }
        return true;
    }

    bool tableau_with_costs() const {
        return m_settings.simplex_strategy() == simplex_strategy_enum::tableau_costs;
    }

    bool costs_are_used() const {
        return m_settings.simplex_strategy() != simplex_strategy_enum::tableau_rows;
    }
    
    void change_basic_x_by_delta_on_column(unsigned j, const numeric_pair<mpq> & delta) {
        if (use_tableau()) {
            for (const auto & c : A_r().m_columns[j]) {
                unsigned bj = m_mpq_lar_core_solver.m_r_basis[c.m_i];
                m_mpq_lar_core_solver.m_r_x[bj] -= A_r().get_val(c) * delta;
                if (tableau_with_costs()) {
                    m_basic_columns_with_changed_cost.insert(bj);
                }
                m_mpq_lar_core_solver.m_r_solver.update_column_in_inf_set(bj);
            }
        } else {
            m_column_buffer.clear();
            m_column_buffer.resize(A_r().row_count());
            m_mpq_lar_core_solver.m_r_solver.solve_Bd(j, m_column_buffer);
            for (unsigned i : m_column_buffer.m_index) {
                unsigned bj = m_mpq_lar_core_solver.m_r_basis[i];
                m_mpq_lar_core_solver.m_r_x[bj] -= m_column_buffer[i] * delta;
                m_mpq_lar_core_solver.m_r_solver.update_column_in_inf_set(bj);
            }
        }
    }

    void update_x_and_inf_costs_for_column_with_changed_bounds(unsigned j) {
        if (m_mpq_lar_core_solver.m_r_heading[j] >= 0) {
            if (costs_are_used()) {
                bool was_infeas = m_mpq_lar_core_solver.m_r_solver.m_inf_set.contains(j);
                m_mpq_lar_core_solver.m_r_solver.update_column_in_inf_set(j);
                if (was_infeas != m_mpq_lar_core_solver.m_r_solver.m_inf_set.contains(j))
                    m_basic_columns_with_changed_cost.insert(j);
            } else {
                m_mpq_lar_core_solver.m_r_solver.update_column_in_inf_set(j);
            }
        } else {
            numeric_pair<mpq> delta;
            if (m_mpq_lar_core_solver.m_r_solver.make_column_feasible(j, delta))
                change_basic_x_by_delta_on_column(j, delta);
        }
    }

    
    void detect_rows_with_changed_bounds_for_column(unsigned j) {
        if (m_mpq_lar_core_solver.m_r_heading[j] >= 0) {
            m_rows_with_changed_bounds.insert(m_mpq_lar_core_solver.m_r_heading[j]);
            return;
        }

        if (use_tableau())
            detect_rows_of_bound_change_column_for_nbasic_column_tableau(j);
        else 
            detect_rows_of_bound_change_column_for_nbasic_column(j);
    }
    
    void detect_rows_with_changed_bounds() {
        for (auto j : m_columns_with_changed_bound.m_index)
            detect_rows_with_changed_bounds_for_column(j);
    }

    void update_x_and_inf_costs_for_columns_with_changed_bounds() {
        for (auto j : m_columns_with_changed_bound.m_index)
            update_x_and_inf_costs_for_column_with_changed_bounds(j);
    }

    void update_x_and_inf_costs_for_columns_with_changed_bounds_tableau() {
        lean_assert(ax_is_correct());
        for (auto j : m_columns_with_changed_bound.m_index)
            update_x_and_inf_costs_for_column_with_changed_bounds(j);

        if (tableau_with_costs()) {
            for (unsigned j : m_basic_columns_with_changed_cost.m_index)
                m_mpq_lar_core_solver.m_r_solver.update_inf_cost_for_column_tableau(j);
            lean_assert(m_mpq_lar_core_solver.m_r_solver.reduced_costs_are_correct_tableau());
        }
    }

    
    void solve_with_core_solver() {
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
        m_mpq_lar_core_solver.solve();
        set_status(m_mpq_lar_core_solver.m_r_solver.get_status());
        lean_assert(m_status != OPTIMAL || all_constraints_hold());
    }

    
    numeric_pair<mpq> get_basic_var_value_from_row_directly(unsigned i) {
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
    
    
    
    numeric_pair<mpq> get_basic_var_value_from_row(unsigned i) {
        if (settings().use_tableau()) {
            return get_basic_var_value_from_row_directly(i);
        }
        
        numeric_pair<mpq> r = zero_of_type<numeric_pair<mpq>>();
        m_mpq_lar_core_solver.calculate_pivot_row(i);
        for (unsigned j : m_mpq_lar_core_solver.m_r_solver.m_pivot_row.m_index) {
            lean_assert(m_mpq_lar_core_solver.m_r_solver.m_basis_heading[j] < 0);
            r -= m_mpq_lar_core_solver.m_r_solver.m_pivot_row.m_data[j] * m_mpq_lar_core_solver.m_r_x[j];
        }
        return r;
    }

    template <typename K, typename L>
    void add_last_rows_to_lu(lp_primal_core_solver<K,L> & s) {
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
    
    bool x_is_correct() const {
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

    bool var_is_registered(var_index vj) const {
        if (vj >= m_terms_start_index) {
            if (vj - m_terms_start_index >= m_terms.size())
                return false;
        } else if ( vj >= A_r().column_count()) {
            return false;
        }
        return true;
    }

    unsigned constraint_stack_size() const {
        return m_constraint_count.stack_size();
    }

    void fill_last_row_of_A_r(static_matrix<mpq, numeric_pair<mpq>> & A, const lar_term * ls) {    
        lean_assert(A.row_count() > 0);
        lean_assert(A.column_count() > 0);
        unsigned last_row = A.row_count() - 1;
        lean_assert(A.m_rows[last_row].size() == 0);
        for (auto & t : ls->m_coeffs) {
            lean_assert(!is_zero(t.second));
            var_index j = t.first;
            A.set(last_row, j, - t.second);
        }
        unsigned basis_j = A.column_count() - 1;
        A.set(last_row, basis_j, mpq(1));
    }

    template <typename U, typename V>
    void create_matrix_A(static_matrix<U, V> & matr) {
        lean_assert(false); // not implemented
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
    void copy_from_mpq_matrix(static_matrix<U, V> & matr) {
		matr.m_rows.resize(A_r().row_count());
		matr.m_columns.resize(A_r().column_count());
        for (unsigned i = 0; i < matr.row_count(); i++) {
            for (auto & it : A_r().m_rows[i]) {
                matr.set(i, it.m_j,  convert_struct<U, mpq>::convert(it.get_val()));
            }
        }
    }


    bool try_to_set_fixed(column_info<mpq> & ci) {
        if (ci.upper_bound_is_set() && ci.low_bound_is_set() && ci.get_upper_bound() == ci.get_low_bound() && !ci.is_fixed()) {
            ci.set_fixed_value(ci.get_upper_bound());
            return true;
        }
        return false;
    }

    column_type get_column_type(const column_info<mpq> & ci) {
        auto ret = ci.get_column_type_no_flipping();
        if (ret == column_type::boxed) { // changing boxed to fixed because of the no span
            if (ci.get_low_bound() == ci.get_upper_bound())
                ret = column_type::fixed;
        }
        return ret;
    }

    std::string get_column_name(unsigned j) const {
        if (j >= m_terms_start_index) 
            return std::string("_t") + T_to_string(j);
        if (j >= m_columns_to_ext_vars_or_term_indices.size())
            return std::string("_s") + T_to_string(j);

        return std::string("v") + T_to_string(m_columns_to_ext_vars_or_term_indices[j]);
    }

    bool all_constrained_variables_are_registered(const vector<std::pair<mpq, var_index>>& left_side) {
        for (auto it : left_side) {
            if (! var_is_registered(it.second))
                return false;
        }
        return true;
    }

    constraint_index add_constraint(const vector<std::pair<mpq, var_index>>& left_side_with_terms, lconstraint_kind kind_par, const mpq& right_side_parm) {
        /*
          mpq rs = right_side_parm;
          vector<std::pair<mpq, var_index>> left_side;
          substitute_terms(one_of_type<mpq>(), left_side_with_terms, left_side, rs);
          lean_assert(left_side.size() > 0);
          lean_assert(all_constrained_variables_are_registered(left_side));
          lar_constraint original_constr(left_side, kind_par, rs);
          unsigned j; // j is the index of the basic variables corresponding to the left side
          canonic_left_side ls = create_or_fetch_canonic_left_side(left_side, j);
          mpq ratio = find_ratio_of_original_constraint_to_normalized(ls, original_constr);
          auto kind = ratio.is_neg() ? flip_kind(kind_par) : kind_par;
          rs/= ratio;
          lar_normalized_constraint normalized_constraint(ls, ratio, kind, rs, original_constr);
          m_constraints.push_back(normalized_constraint);
          constraint_index constr_ind = m_constraints.size() - 1;
          update_column_type_and_bound(j, kind, rs, constr_ind);
          return constr_ind;
        */
        lean_assert(false); // not implemented
        return 0;
    }

    bool all_constraints_hold() const {
        if (m_settings.get_cancel_flag())
            return true;
        std::unordered_map<var_index, mpq> var_map;
        get_model(var_map);
    
        for (unsigned i = 0; i < m_constraints.size(); i++) {
            if (!constraint_holds(*m_constraints[i], var_map)) {
                print_constraint(i, std::cout);
                return false;
            }
        }
        return true;
    }

    bool constraint_holds(const lar_base_constraint & constr, std::unordered_map<var_index, mpq> & var_map) const {
        mpq left_side_val = get_left_side_val(constr, var_map);
        switch (constr.m_kind) {
        case LE: return left_side_val <= constr.m_right_side;
        case LT: return left_side_val < constr.m_right_side;
        case GE: return left_side_val >= constr.m_right_side;
        case GT: return left_side_val > constr.m_right_side;
        case EQ: return left_side_val == constr.m_right_side;
        default:
            lean_unreachable();
        }
        return false; // it is unreachable
    }







    bool the_relations_are_of_same_type(const vector<std::pair<mpq, unsigned>> & evidence, lconstraint_kind & the_kind_of_sum) const {
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

    static void register_in_map(std::unordered_map<var_index, mpq> & coeffs, const lar_base_constraint & cn, const mpq & a) {
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
    bool the_left_sides_sum_to_zero(const vector<std::pair<mpq, unsigned>> & evidence) const {
        std::unordered_map<var_index, mpq> coeff_map;
        for (auto & it : evidence) {
            mpq coeff = it.first;
            constraint_index con_ind = it.second;
            lean_assert(con_ind < m_constraints.size());
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

    bool the_right_sides_do_not_sum_to_zero(const vector<std::pair<mpq, unsigned>> & evidence) {
        mpq ret = numeric_traits<mpq>::zero();
        for (auto & it : evidence) {
            mpq coeff = it.first;
            constraint_index con_ind = it.second;
            lean_assert(con_ind < m_constraints.size());
            const lar_constraint & constr = *m_constraints[con_ind];
            ret += constr.m_right_side * coeff;
        }
        return !numeric_traits<mpq>::is_zero(ret);
    }

    bool explanation_is_correct(const vector<std::pair<mpq, unsigned>>& explanation) const {
#ifdef LEAN_DEBUG
        lconstraint_kind kind;
        lean_assert(the_relations_are_of_same_type(explanation, kind));
        lean_assert(the_left_sides_sum_to_zero(explanation));
        mpq rs = sum_of_right_sides_of_explanation(explanation);
        switch (kind) {
        case LE: lean_assert(rs < zero_of_type<mpq>());
            break;
        case LT: lean_assert(rs <= zero_of_type<mpq>());
            break;
        case GE: lean_assert(rs > zero_of_type<mpq>());
            break;
        case GT: lean_assert(rs >= zero_of_type<mpq>());
            break;
        case EQ: lean_assert(rs != zero_of_type<mpq>());
            break;
        default:
            lean_assert(false);
            return false;
        }
#endif
        return true;
    }

    bool inf_explanation_is_correct() const {
#ifdef LEAN_DEBUG
        vector<std::pair<mpq, unsigned>> explanation;
        get_infeasibility_explanation(explanation);
        return explanation_is_correct(explanation);
#endif
        return true;
    }

    mpq sum_of_right_sides_of_explanation(const vector<std::pair<mpq, unsigned>> & explanation) const {
        mpq ret = numeric_traits<mpq>::zero();
        for (auto & it : explanation) {
            mpq coeff = it.first;
            constraint_index con_ind = it.second;
            lean_assert(con_ind < m_constraints.size());
            ret += (m_constraints[con_ind]->m_right_side - m_constraints[con_ind]->get_free_coeff_of_left_side()) * coeff;
        }
        return ret;
    }

    bool has_lower_bound(var_index var, constraint_index& ci, mpq& value, bool& is_strict) {

        if (var >= m_vars_to_ul_pairs.size()) {
            // TBD: bounds on terms could also be used, caller may have to track these.
            return false;
        }
        const ul_pair & ul = m_vars_to_ul_pairs[var];
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
    
    bool has_upper_bound(var_index var, constraint_index& ci, mpq& value, bool& is_strict) {

        if (var >= m_vars_to_ul_pairs.size()) {
            // TBD: bounds on terms could also be used, caller may have to track these.
            return false;
        }
        const ul_pair & ul = m_vars_to_ul_pairs[var];
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


    void get_infeasibility_explanation(vector<std::pair<mpq, constraint_index>> & explanation) const {
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
        lean_assert(explanation_is_correct(explanation));
    }

    void get_infeasibility_explanation_for_inf_sign(
                                                    vector<std::pair<mpq, constraint_index>> & explanation,
                                                    const vector<std::pair<mpq, unsigned>> & inf_row,
                                                    int inf_sign) const {

        for (auto & it : inf_row) {
            mpq coeff = it.first;
            unsigned j = it.second;

            int adj_sign = coeff.is_pos() ? inf_sign : -inf_sign;
            const ul_pair & ul = m_vars_to_ul_pairs[j];

            constraint_index bound_constr_i = adj_sign < 0 ? ul.upper_bound_witness() : ul.low_bound_witness();
            lean_assert(bound_constr_i < m_constraints.size());
            explanation.push_back(std::make_pair(coeff, bound_constr_i));
        } 
    }



    void get_model(std::unordered_map<var_index, mpq> & variable_values) const {
        mpq delta = mpq(1, 2); // start from 0.5 to have less clashes
        lean_assert(m_status == OPTIMAL);
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


    std::string get_variable_name(var_index vi) const {
        return get_column_name(vi);
    }

    // ********** print region start
    void print_constraint(constraint_index ci, std::ostream & out) const {
        if (ci >= m_constraints.size()) {
            out << "constraint " << T_to_string(ci) << " is not found";
            out << std::endl;
            return;
        }

        print_constraint(m_constraints[ci], out);
    }

    void print_constraints(std::ostream& out) const  {
        for (auto c : m_constraints) {
            print_constraint(c, out);
        }
    }

    void print_terms(std::ostream& out) const  {
        for (auto it : m_terms) {
            print_term(*it, out);
            out << "\n";
        }
    }

    void print_left_side_of_constraint(const lar_base_constraint * c, std::ostream & out) const {
        print_linear_combination_of_column_indices(c->get_left_side_coefficients(), out);
        mpq free_coeff = c->get_free_coeff_of_left_side();
        if (!is_zero(free_coeff))
            out << " + " << free_coeff;
        
    }

    void print_term(lar_term const& term, std::ostream & out) const {
        if (!numeric_traits<mpq>::is_zero(term.m_v)) {
            out << term.m_v << " + ";
        }
        print_linear_combination_of_column_indices(term.coeffs_as_vector(), out);
    }

    mpq get_left_side_val(const lar_base_constraint &  cns, const std::unordered_map<var_index, mpq> & var_map) const {
        mpq ret = cns.get_free_coeff_of_left_side();
        for (auto & it : cns.get_left_side_coefficients()) {
            var_index j = it.second;
            auto vi = var_map.find(j);
            lean_assert(vi != var_map.end());
            ret += it.first * vi->second;
        }
        return ret;
    }

    void print_constraint(const lar_base_constraint * c, std::ostream & out) const {
        print_left_side_of_constraint(c, out);
        out << " " << lconstraint_kind_string(c->m_kind) << " " << c->m_right_side << std::endl;
    }

    void fill_var_set_for_random_update(unsigned sz, var_index const * vars, vector<unsigned>& column_list) {
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

    void random_update(unsigned sz, var_index const * vars) {
        vector<unsigned> column_list;
        fill_var_set_for_random_update(sz, vars, column_list);
        random_updater ru(m_mpq_lar_core_solver, column_list);
        ru.update();
    }


    void try_pivot_fixed_vars_from_basis() {
        m_mpq_lar_core_solver.m_r_solver.pivot_fixed_vars_from_basis();
    }

    void pop() {
        pop(1);
    }


    bool column_represents_row_in_tableau(unsigned j) {
        return m_vars_to_ul_pairs()[j].m_i != static_cast<row_index>(-1);
    }

    void make_sure_that_the_bottom_right_elem_not_zero_in_tableau(unsigned i, unsigned j) {
        // i, j - is the indices of the bottom-right element of the tableau
        lean_assert(A_r().row_count() == i + 1 && A_r().column_count() == j + 1);
        auto & last_column = A_r().m_columns[j];
        int non_zero_column_cell_index = -1;
        for (unsigned k = last_column.size(); k-- > 0;){
            auto & cc = last_column[k];
            if (cc.m_i == i)
                return;
            non_zero_column_cell_index = k;
        }

        lean_assert(non_zero_column_cell_index != -1);
        lean_assert(static_cast<unsigned>(non_zero_column_cell_index) != i);
        m_mpq_lar_core_solver.m_r_solver.transpose_rows_tableau(last_column[non_zero_column_cell_index].m_i, i);
    }

    void remove_last_row_and_column_from_tableau(unsigned j) {
        lean_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_solver.m_costs.size());
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
        lean_assert(last_row.size() == 0);
        lean_assert(A_r().m_columns[j].size() == 0);
        A_r().m_rows.pop_back();
        A_r().m_columns.pop_back();
        slv.m_b.pop_back();
    }

    void remove_last_column_from_tableau(unsigned j) {
        lean_assert(j == A_r().column_count() - 1);
        // the last column has to be empty
        lean_assert(A_r().m_columns[j].size() == 0);
        A_r().m_columns.pop_back();
    }

    void remove_last_column_from_basis_tableau(unsigned j) {
        auto& rslv = m_mpq_lar_core_solver.m_r_solver;
        int i = rslv.m_basis_heading[j];
        if (i >= 0) { // j is a basic var
            int last_pos = static_cast<int>(rslv.m_basis.size()) - 1;
            lean_assert(last_pos >= 0);
            if (i != last_pos) {
                unsigned j_at_last_pos = rslv.m_basis[last_pos];
                rslv.m_basis[i] = j_at_last_pos;
                rslv.m_basis_heading[j_at_last_pos] = i;
            }
            rslv.m_basis.pop_back(); // remove j from the basis
        } else {
            int last_pos = static_cast<int>(rslv.m_nbasis.size()) - 1;
            lean_assert(last_pos >= 0);
            i = - 1 - i;
            if (i != last_pos) {
                unsigned j_at_last_pos = rslv.m_nbasis[last_pos];
                rslv.m_nbasis[i] = j_at_last_pos;
                rslv.m_basis_heading[j_at_last_pos] = - i - 1;
            }
            rslv.m_nbasis.pop_back(); // remove j from the basis
        }
        rslv.m_basis_heading.pop_back();
        lean_assert(rslv.m_basis.size() == A_r().row_count());
        lean_assert(rslv.basis_heading_is_correct());
    }

    void remove_column_from_tableau(unsigned j) {
        auto& rslv = m_mpq_lar_core_solver.m_r_solver;
        lean_assert(j == A_r().column_count() - 1);
        lean_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_solver.m_costs.size());
        if (column_represents_row_in_tableau(j)) {
            remove_last_row_and_column_from_tableau(j);
            if (rslv.m_basis_heading[j] < 0)
                rslv.change_basis_unconditionally(j, rslv.m_basis[A_r().row_count()]); // A_r().row_count() is the index of the last row in the basis still
        }
        else {
            remove_last_column_from_tableau(j);
        }
        rslv.m_x.pop_back();
        rslv.m_d.pop_back();
        rslv.m_costs.pop_back();

        remove_last_column_from_basis_tableau(j);
        lean_assert(m_mpq_lar_core_solver.r_basis_is_OK());
        lean_assert(A_r().column_count() == m_mpq_lar_core_solver.m_r_solver.m_costs.size());
    }


    void pop_tableau() {
        lean_assert(m_mpq_lar_core_solver.m_r_solver.m_costs.size() == A_r().column_count());

        lean_assert(m_mpq_lar_core_solver.m_r_solver.m_basis.size() == A_r().row_count());
        lean_assert(m_mpq_lar_core_solver.m_r_solver.basis_heading_is_correct());
        // We remove last variables starting from m_column_names.size() to m_vec_of_canonic_left_sides.size().    
        // At this moment m_column_names is already popped
        for (unsigned j = A_r().column_count(); j-- > m_columns_to_ext_vars_or_term_indices.size();)
            remove_column_from_tableau(j);
        lean_assert(m_mpq_lar_core_solver.m_r_solver.m_costs.size() == A_r().column_count());
        lean_assert(m_mpq_lar_core_solver.m_r_solver.m_basis.size() == A_r().row_count());
        lean_assert(m_mpq_lar_core_solver.m_r_solver.basis_heading_is_correct());
    }




    void clean_inf_set_of_r_solver_after_pop() {
        vector<unsigned> became_feas;
        clean_large_elements_after_pop(A_r().column_count(), m_mpq_lar_core_solver.m_r_solver.m_inf_set);
        std::unordered_set<unsigned> basic_columns_with_changed_cost;
        auto inf_index_copy = m_mpq_lar_core_solver.m_r_solver.m_inf_set.m_index;
        for (auto j: inf_index_copy) {
            if (m_mpq_lar_core_solver.m_r_heading[j] >= 0) {
                continue;
            }
            // some basic columns might become non-basic - these columns need to be made feasible
            numeric_pair<mpq> delta;
            if (m_mpq_lar_core_solver.m_r_solver.make_column_feasible(j, delta))
                change_basic_x_by_delta_on_column(j, delta);
            became_feas.push_back(j);
        }

        for (unsigned j : became_feas) {
            lean_assert(m_mpq_lar_core_solver.m_r_solver.m_basis_heading[j] < 0);
            m_mpq_lar_core_solver.m_r_solver.m_d[j] -= m_mpq_lar_core_solver.m_r_solver.m_costs[j];
            m_mpq_lar_core_solver.m_r_solver.m_costs[j] = zero_of_type<mpq>();
            m_mpq_lar_core_solver.m_r_solver.m_inf_set.erase(j);
        }
        became_feas.clear();
        for (unsigned j : m_mpq_lar_core_solver.m_r_solver.m_inf_set.m_index) {
            lean_assert(m_mpq_lar_core_solver.m_r_heading[j] >= 0);
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
            lean_assert(m_mpq_lar_core_solver.m_r_solver.reduced_costs_are_correct_tableau());
        }
    }


    void shrink_explanation_to_minimum(vector<std::pair<mpq, constraint_index>> & explanation) const {
        // implementing quickXplain
        quick_xplain::run(explanation, *this);
        lean_assert(this->explanation_is_correct(explanation));
    }

    
};
}
