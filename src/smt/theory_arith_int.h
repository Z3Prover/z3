/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_arith_int.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-17.

Revision History:

--*/
#ifndef THEORY_ARITH_INT_H_
#define THEORY_ARITH_INT_H_

#include "util/numeral_buffer.h"
#include "ast/ast_ll_pp.h"
#include "ast/well_sorted.h"
#include "ast/ast_smt2_pp.h"
#include "math/euclid/euclidean_solver.h"

namespace smt {

    // -----------------------------------
    //
    // Integrality
    //
    // -----------------------------------
       
    
    /**
       \brief Move non base variables to one of its bounds.
       If the variable does not have bounds, it is integer, but it is not assigned to an integer value, then the 
       variable is set to an integer value.
       In mixed integer/real problems moving a real variable to a bound could cause an integer value to 
       have an infinitesimal. Such an assignment would disable mk_gomory_cut, and Z3 would loop.
       
    */
    template<typename Ext>
    void theory_arith<Ext>::move_non_base_vars_to_bounds() {
        theory_var num = get_num_vars();
        for (theory_var v = 0; v < num; v++) {
            if (is_non_base(v)) {
                bound * l               = lower(v);
                bound * u               = upper(v);
                const inf_numeral & val = get_value(v);
                if (l != nullptr && u != nullptr) {
                    if (val != l->get_value() && val != u->get_value())
                        set_value(v, l->get_value());
                }
                else if (l != nullptr) {
                    if (val != l->get_value())
                        set_value(v, l->get_value());
                }
                else if (u != nullptr) {
                    if (val != u->get_value())
                        set_value(v, u->get_value());
                }
                else {
                    if (is_int(v) && !val.is_int()) {
                        inf_numeral new_val(floor(val));
                        set_value(v, new_val);
                    }
                }
            }
        }
    }

    /**
       \brief Returns true if the there is an integer variable
       that is not assigned to an integer value.
    */
    template<typename Ext>
    bool theory_arith<Ext>::has_infeasible_int_var() {
        int num = get_num_vars();
        for (theory_var v = 0; v < num; v++) {
            if (is_int(v) && !get_value(v).is_int())
                return true;
        }
        return false;
    }

    /**
       \brief Find an integer base var that is not assigned to an
       integer value, but is bounded (i.e., it has lower and upper
       bounds). Return null_var_id if all integer base variables are
       assigned to integer values.

       If there are multiple variables satisfying the condition above,
       then select the one with the tightest bound.
    */
    template<typename Ext>
    theory_var theory_arith<Ext>::find_bounded_infeasible_int_base_var() {
        theory_var result = null_theory_var;
        numeral range;
        numeral new_range;
        numeral small_range_thresold(1024);
        unsigned n = 0;
        typename vector<row>::const_iterator it  = m_rows.begin();
        typename vector<row>::const_iterator end = m_rows.end();
        for (; it != end; ++it) {
            theory_var v = it->get_base_var();
            if (v == null_theory_var)
                continue;
            if (!is_base(v))
                continue;
            if (!is_int(v))
                continue;
            if (get_value(v).is_int())
                continue;
            if (!is_bounded(v))
                continue;
            numeral const & l = lower_bound(v).get_rational();
            numeral const & u = upper_bound(v).get_rational();
            new_range  = u;
            new_range -= l;
            if (new_range > small_range_thresold) 
                continue;
            if (result == null_theory_var) {
                result = v;
                range  = new_range;
                n      = 1;
                continue;
            }
            if (new_range < range) {
                n      = 1;
                result = v;
                range  = new_range;
                continue;
            }
            if (new_range == range) {
                n++;
                if (m_random() % n == 0) {
                    result = v;
                    range  = new_range;
                    continue;
                }
            }
        }
        return result;
    }

    /**
       \brief Find an integer base var that is not assigned to an integer value.
       Return null_var_id if all integer base variables are assigned to
       integer values.

       \remark This method gives preference to bounded integer variables.
       If all variables are unbounded, then it selects a random one.
    */
    template<typename Ext>
    theory_var theory_arith<Ext>::find_infeasible_int_base_var() {
        theory_var v = find_bounded_infeasible_int_base_var();
        if (v != null_theory_var) {
            TRACE("find_infeasible_int_base_var", display_var(tout, v););
            return v;
        }
        unsigned n   = 0;
        theory_var r = null_theory_var;
        
#define SELECT_VAR(VAR) if (r == null_theory_var) { n = 1; r = VAR; } else { n++; SASSERT(n >= 2); if (m_random() % n == 0) r = VAR; }

        typename vector<row>::const_iterator it  = m_rows.begin();
        typename vector<row>::const_iterator end = m_rows.end();
        for (; it != end; ++it) {
            theory_var v = it->get_base_var();
            if (v != null_theory_var && is_base(v) && is_int(v) && !get_value(v).is_int()) {
                SELECT_VAR(v);
            }
        }
        if (r == null_theory_var) {
            it  = m_rows.begin();
            for (; it != end; ++it) {
                theory_var v = it->get_base_var();
                if (v != null_theory_var && is_quasi_base(v) && is_int(v) && !get_value(v).is_int()) {
                    quasi_base_row2base_row(get_var_row(v));
                    SELECT_VAR(v);
                }
            }
            if (r == null_theory_var)
                return null_theory_var;
        }
        CASSERT("arith", wf_rows());
        CASSERT("arith", wf_columns());
        return r;
    }


    /**
       \brief Create "branch and bound" case-split.
    */
    template<typename Ext>
    void theory_arith<Ext>::branch_infeasible_int_var(theory_var v) {
        SASSERT(is_int(v));
        SASSERT(!get_value(v).is_int());
        ast_manager & m = get_manager();
        m_stats.m_branches++;
        numeral k     = ceil(get_value(v));
        rational _k   = k.to_rational();
        TRACE("arith_int", tout << "branching v" << v << " = " << get_value(v) << "\n";
              display_var(tout, v);
              tout << "k = " << k << ", _k = "<< _k << std::endl;
              );
        expr_ref bound(m);
        expr* e = get_enode(v)->get_owner();
        bound  = m_util.mk_ge(e, m_util.mk_numeral(_k, m_util.is_int(e)));
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_or(to_app(bound), m.mk_not(to_app(bound)));
            log_axiom_instantiation(body);
        }
        TRACE("arith_int", tout << mk_bounded_pp(bound, m) << "\n";);
        context & ctx = get_context();
        ctx.internalize(bound, true);
        ctx.mark_as_relevant(bound.get());
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
    }

    
    /**
       \brief Create a "cut from proof" lemma.

       The set of rows where the base variable is tight are extracted.
       These row equalities are checked for integer feasiability.
       If they are not integer feasible, then an integer infeasible
       equation, that is implied from the extracted equalities is extracted.
       The extracted equality a*x = 0 is blocked by asserting the disjunction
       (a*x > 0 \/ a*x < 0)
    */
    template<typename Ext>
    bool theory_arith<Ext>::branch_infeasible_int_equality() {

        typename vector<row>::const_iterator it  = m_rows.begin();
        typename vector<row>::const_iterator end = m_rows.end();

        vector<vector<rational> > rows;
        unsigned max_row = 1;                // all rows should contain a constant in the last position.
        u_map<unsigned>   var2index;         // map theory variables to positions in 'rows'.
        u_map<theory_var> index2var;         // map back positions in 'rows' to theory variables.

        for (; it != end; ++it) {
            theory_var b = it->get_base_var();
            if (b == null_theory_var) {
                TRACE("arith_int", display_row(tout << "null: ", *it, true); );
                continue;
            }
            bool is_tight = false;
            numeral const_coeff(0);

            bound* l = lower(b), *u = upper(b);
            if (l != nullptr && get_value(b) - inf_numeral(1) < l->get_value()) {
                SASSERT(l->get_value() <= get_value(b));
                is_tight = true;
                const_coeff = l->get_value().get_rational();
            }
            else if (u != nullptr && get_value(b) + inf_numeral(1) > u->get_value()) {
                SASSERT(get_value(b) <= u->get_value());
                is_tight = true;
                const_coeff = u->get_value().get_rational();
            }
            if (!is_tight) {
                TRACE("arith_int", 
                      display_row(tout << "!tight: ", *it, true); 
                      display_var(tout, b);
                      );
                continue;
            }
            rows.push_back(vector<rational>(max_row));
            vector<rational>& row = rows.back();
            numeral denom(1);
            unsigned index = 0;

            typename vector<row_entry>::const_iterator it_r  = it->begin_entries();
            typename vector<row_entry>::const_iterator end_r = it->end_entries();

            for (; it_r != end_r && is_tight; ++it_r) {
                if (it_r->is_dead())
                    continue;
                theory_var x = it_r->m_var;
                if (x == b)
                    continue;
                numeral coeff = it_r->m_coeff;
                if (is_fixed(x)) {
                    const_coeff += coeff*lower(x)->get_value().get_rational();
                    continue;
                }
                if (!is_int(x)) {
                    TRACE("theory_arith_int", display_row(tout << "!int:  ", *it, true); );
                    is_tight = false;
                    continue;
                }
                if (var2index.find(x, index)) {
                    row[index] = coeff.to_rational();
                }
                else {
                    row.push_back(coeff.to_rational());
                    var2index.insert(x, max_row);
                    index2var.insert(max_row, x);
                    ++max_row;
                }
                numeral tmp_coeff = denominator(coeff);
                denom = lcm(tmp_coeff, denom);
            }
            if (!is_tight) {
                rows.pop_back();
                continue;
            }
            row[0] = const_coeff.to_rational();
            numeral tmp_const_coeff = denominator(const_coeff);
            denom = lcm(tmp_const_coeff, denom);
            if (!denom.is_one()) {
                for (unsigned i = 0; i < max_row; ++i) {
                    row[i] *= denom.to_rational();
                }
            }
            TRACE("theory_arith_int",
                  tout << "extracted row:\n";
                  for (unsigned i = 0; i < max_row; ++i) {
                      tout << row[i] << " ";
                  }
                  tout << " = 0\n";
                  tout << "base value: " << get_value(b) << "\n";
                  display_row(tout, *it, true);
                  );
        }    
        // 
        // Align the sizes of rows.
        // The sizes are monotonically increasing.
        // 
        for (unsigned i = 0; i < rows.size(); ++i) {
            unsigned sz = rows[i].size();
            SASSERT(sz <= max_row);
            if (sz == max_row) {
                break;
            }
            rows[i].resize(max_row);
        }
        vector<rational> unsat_row;

        if (m_arith_eq_solver.solve_integer_equations(rows, unsat_row)) {
            // The equalities were integer feasiable.
            return false;
        }

        buffer<row_entry> pol;
        for (unsigned i = 1; i < unsat_row.size(); ++i) {
            numeral c(unsat_row[i]);
            if (!c.is_zero()) {
                theory_var var;
                if (!index2var.find(i, var)) {
                    UNREACHABLE();
                }
                pol.push_back(row_entry(c, var));
            }
        }            
        if (pol.empty()) {
            TRACE("theory_arith_int", tout << "The witness is trivial\n";);
            return false;
        }
        expr_ref p1(get_manager()), p2(get_manager());
        
        mk_polynomial_ge(pol.size(), pol.c_ptr(), -unsat_row[0]+rational(1), p1);
        for (unsigned i = 0; i < pol.size(); ++i) {
            pol[i].m_coeff.neg();
        }
        mk_polynomial_ge(pol.size(), pol.c_ptr(), unsat_row[0]+rational(1), p2);
        
        context& ctx = get_context();
        if (get_manager().has_trace_stream()) {
            app_ref body(get_manager());
            body = get_manager().mk_or(p1, p2);
            log_axiom_instantiation(body);
        }
        ctx.internalize(p1, false);
        ctx.internalize(p2, false);
        literal l1(ctx.get_literal(p1)), l2(ctx.get_literal(p2));
        ctx.mark_as_relevant(p1.get());
        ctx.mark_as_relevant(p2.get());
        
        ctx.mk_th_axiom(get_id(), l1, l2);
        if (get_manager().has_trace_stream()) get_manager().trace_stream() << "[end-of-instance]\n";
       
        TRACE("arith_int", 
              tout << "cut: (or " << mk_pp(p1, get_manager()) << " " << mk_pp(p2, get_manager()) << ")\n";
              );

        return true;
    }


    /**
       \brief Create bounds for (non base) free vars in the given row.
       Return true if at least one variable was constrained.
       This method is used to enable the application of gomory cuts.
    */
    template<typename Ext>
    bool theory_arith<Ext>::constrain_free_vars(row const & r) {
        bool result = false;
        theory_var b = r.get_base_var();
        SASSERT(b != null_theory_var);
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead() && it->m_var != b && is_free(it->m_var)) {
                theory_var v  = it->m_var;
                expr* e = get_enode(v)->get_owner();
                bool _is_int = m_util.is_int(e);
                expr * bound  = m_util.mk_ge(e, m_util.mk_numeral(rational::zero(), _is_int));
                context & ctx = get_context();
                if (get_manager().has_trace_stream()) log_axiom_instantiation(bound);
                ctx.internalize(bound, true);
                if (get_manager().has_trace_stream()) get_manager().trace_stream() << "[end-of-instance]\n";
                ctx.mark_as_relevant(bound);
                result = true;
            }
        }
        return result;
    }
   
    /**
       \brief Return true if it is possible to apply a gomory cut on the given row. 
      
       \sa constrain_free_vars
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_gomory_cut_target(row const & r) {
        TRACE("gomory_cut", r.display(tout););
        theory_var b = r.get_base_var();
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            // All non base variables must be at their bounds and assigned to rationals (that is, infinitesimals are not allowed).
            if (!it->is_dead() && it->m_var != b && (!at_bound(it->m_var) || !get_value(it->m_var).is_rational())) {
                TRACE("gomory_cut", tout << "row is not gomory cut target:\n";
                      display_var(tout, it->m_var);
                      tout << "at_bound:      " << at_bound(it->m_var) << "\n";
                      tout << "infinitesimal: " << !get_value(it->m_var).is_rational() << "\n";);
                return false;
            }
        }
        return true;
    }

    template<typename Ext>
    void theory_arith<Ext>::mk_polynomial_ge(unsigned num_args, row_entry const * args, rational const& k, expr_ref & result) {
        // Remark: the polynomials internalized by theory_arith may not satisfy poly_simplifier_plugin->wf_polynomial assertion. 
        bool all_int = true;
        for (unsigned i = 0; i < num_args && all_int; ++i) {
            all_int = is_int(args[i].m_var);
        }
        
        ast_manager & m = get_manager();
        expr_ref_vector _args(m);
        
        for (unsigned i = 0; i < num_args; i++) {
            rational _k = args[i].m_coeff.to_rational();
            expr * x = get_enode(args[i].m_var)->get_owner();
            if (m_util.is_int(x) && !all_int)
                x = m_util.mk_to_real(x);
            if (_k.is_one())
                _args.push_back(x);
            else
                _args.push_back(m_util.mk_mul(m_util.mk_numeral(_k, m_util.is_int(x)), x));
        }

        expr_ref pol(m);
        pol = m_util.mk_add(_args.size(), _args.c_ptr());
        result = m_util.mk_ge(pol, m_util.mk_numeral(k, all_int));
        TRACE("arith_mk_polynomial", tout << "before simplification:\n" << result << "\n";);
        proof_ref pr(m);
        get_context().get_rewriter()(result, result, pr);
        TRACE("arith_mk_polynomial", tout << "after simplification:\n" << result << "\n";);
        SASSERT(is_well_sorted(get_manager(), result));
    }

    template<typename Ext>
    class theory_arith<Ext>::gomory_cut_justification : public ext_theory_propagation_justification {
    public:
         gomory_cut_justification(family_id fid, region & r, 
                                 unsigned num_lits, literal const * lits, 
                                 unsigned num_eqs, enode_pair const * eqs,
                                 antecedents& bounds, 
                                 literal consequent):
        ext_theory_propagation_justification(fid, r, num_lits, lits, num_eqs, eqs, consequent,
                                             bounds.num_params(), bounds.params("gomory-cut")) {
        }
        // Remark: the assignment must be propagated back to arith
        theory_id get_from_theory() const override { return null_theory_id; }
    };

    /**
       \brief Create a gomory cut for the given row.
    */
    template<typename Ext>
    bool theory_arith<Ext>::mk_gomory_cut(row const & r) {
        // The following assertion is wrong. It may be violated in mixed-integer problems.
        // SASSERT(!all_coeff_int(r));
        theory_var x_i = r.get_base_var();
        
        SASSERT(is_int(x_i));
        // The following assertion is wrong. It may be violated in mixed-real-interger problems.
        // The check is_gomory_cut_target will discard rows where any variable contains infinitesimals.
        // SASSERT(m_value[x_i].is_rational()); // infinitesimals are not used for integer variables
        SASSERT(!m_value[x_i].is_int());     // the base variable is not assigned to an integer value.

        if (constrain_free_vars(r) || !is_gomory_cut_target(r)) {
            TRACE("gomory_cut", tout << "failed to apply gomory cut:\n";
                  tout << "constrain_free_vars(r):  " << constrain_free_vars(r) << "\n";);
            return false;
        }

        TRACE("gomory_cut", tout << "applying cut at:\n"; display_row_info(tout, r););
        
        antecedents ante(*this);

        m_stats.m_gomory_cuts++;

        // gomory will be   pol >= k
        numeral k(1);
        buffer<row_entry> pol;
        
        numeral f_0  = Ext::fractional_part(m_value[x_i]);
        numeral one_minus_f_0 = numeral(1) - f_0; 
        SASSERT(!f_0.is_zero());
        SASSERT(!one_minus_f_0.is_zero());
        
        numeral lcm_den(1);
        unsigned num_ints = 0;

        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead() && it->m_var != x_i) {
                theory_var x_j   = it->m_var;
                numeral a_ij = it->m_coeff;
                a_ij.neg();  // make the used format compatible with the format used in: Integrating Simplex with DPLL(T)
                if (is_real(x_j)) {
                    numeral new_a_ij;
                    if (at_lower(x_j)) {
                        if (a_ij.is_pos()) {
                            new_a_ij  =  a_ij / one_minus_f_0;
                        }
                        else {
                            new_a_ij  =  a_ij / f_0;
                            new_a_ij.neg();
                        }
                        k.addmul(new_a_ij, lower_bound(x_j).get_rational());
                        lower(x_j)->push_justification(ante, new_a_ij, coeffs_enabled());
                    }
                    else {
                        SASSERT(at_upper(x_j));
                        if (a_ij.is_pos()) {
                            new_a_ij =   a_ij / f_0; 
                            new_a_ij.neg(); // the upper terms are inverted.
                        }
                        else {
                            new_a_ij =   a_ij / one_minus_f_0; 
                        }
                        k.addmul(new_a_ij, upper_bound(x_j).get_rational());
                        upper(x_j)->push_justification(ante, new_a_ij, coeffs_enabled());
                    }
                    TRACE("gomory_cut_detail", tout << a_ij << "*v" << x_j << " k: " << k << "\n";);
                    pol.push_back(row_entry(new_a_ij, x_j));
                }
                else {
                    ++num_ints;
                    SASSERT(is_int(x_j));
                    numeral f_j = Ext::fractional_part(a_ij);
                    TRACE("gomory_cut_detail", 
                          tout << a_ij << "*v" << x_j << "\n";
                          tout << "fractional_part: " << Ext::fractional_part(a_ij) << "\n";
                          tout << "f_j: " << f_j << "\n";
                          tout << "f_0: " << f_0 << "\n";
                          tout << "one_minus_f_0: " << one_minus_f_0 << "\n";);
                    if (!f_j.is_zero()) {
                        numeral new_a_ij;
                        if (at_lower(x_j)) {
                            if (f_j <= one_minus_f_0) {
                                new_a_ij = f_j / one_minus_f_0;
                            }
                            else {
                                new_a_ij = (numeral(1) - f_j) / f_0;
                            }
                            k.addmul(new_a_ij, lower_bound(x_j).get_rational());
                            lower(x_j)->push_justification(ante, new_a_ij, coeffs_enabled());
                        }
                        else {
                            SASSERT(at_upper(x_j));
                            if (f_j <= f_0) {
                                new_a_ij = f_j / f_0;
                            }
                            else {
                                new_a_ij = (numeral(1) - f_j) / one_minus_f_0;
                            }
                            new_a_ij.neg(); // the upper terms are inverted
                            k.addmul(new_a_ij, upper_bound(x_j).get_rational());
                            upper(x_j)->push_justification(ante, new_a_ij, coeffs_enabled());
                        }
                        TRACE("gomory_cut_detail", tout << "new_a_ij: " << new_a_ij << " k: " << k << "\n";);
                        pol.push_back(row_entry(new_a_ij, x_j));
                        lcm_den = lcm(lcm_den, denominator(new_a_ij));
                    }
                }
            }
        }

        CTRACE("empty_pol", pol.empty(), display_row_info(tout, r););

        expr_ref bound(get_manager());
        if (pol.empty()) {
            SASSERT(k.is_pos());
            // conflict 0 >= k where k is positive
            set_conflict(ante, ante, "gomory-cut");
            return true;
        }
        else if (pol.size() == 1) {
            theory_var v = pol[0].m_var;
            k /= pol[0].m_coeff;
            bool is_lower = pol[0].m_coeff.is_pos();
            if (is_int(v) && !k.is_int()) {
                k = is_lower?ceil(k):floor(k);
            }
            rational _k = k.to_rational();
            if (is_lower)
                bound = m_util.mk_ge(get_enode(v)->get_owner(), m_util.mk_numeral(_k, is_int(v)));
            else
                bound = m_util.mk_le(get_enode(v)->get_owner(), m_util.mk_numeral(_k, is_int(v)));
        }
        else { 
            if (num_ints > 0) {
                lcm_den = lcm(lcm_den, denominator(k));
                TRACE("gomory_cut_detail", tout << "k: " << k << " lcm_den: " << lcm_den << "\n";
                      for (unsigned i = 0; i < pol.size(); i++) {
                          tout << pol[i].m_coeff << " " << pol[i].m_var << "\n";
                      }
                      tout << "k: " << k << "\n";);
                SASSERT(lcm_den.is_pos());
                if (!lcm_den.is_one()) {
                    // normalize coefficients of integer parameters to be integers.
                    unsigned n = pol.size();
                    for (unsigned i = 0; i < n; i++) {
                        pol[i].m_coeff *= lcm_den;
                        SASSERT(!is_int(pol[i].m_var) || pol[i].m_coeff.is_int());
                    }
                    k *= lcm_den;
                }
                TRACE("gomory_cut_detail", tout << "after *lcm\n";
                      for (unsigned i = 0; i < pol.size(); i++) {
                          tout << pol[i].m_coeff << " * v" << pol[i].m_var << "\n";
                      }
                      tout << "k: " << k << "\n";);
            }
            mk_polynomial_ge(pol.size(), pol.c_ptr(), k.to_rational(), bound);            
        }
        TRACE("gomory_cut", tout << "new cut:\n" << bound << "\n"; ante.display(tout););
        literal l     = null_literal;
        context & ctx = get_context();
        if (get_manager().has_trace_stream()) log_axiom_instantiation(bound);
        ctx.internalize(bound, true);
        if (get_manager().has_trace_stream()) get_manager().trace_stream() << "[end-of-instance]\n";
        l = ctx.get_literal(bound);
        ctx.mark_as_relevant(l);
        dump_lemmas(l, ante);
        ctx.assign(l, ctx.mk_justification(
                       gomory_cut_justification(
                           get_id(), ctx.get_region(), 
                           ante.lits().size(), ante.lits().c_ptr(), 
                           ante.eqs().size(), ante.eqs().c_ptr(), ante, l)));
        return true;
    }
    
    /**
       \brief Return false if the row failed the GCD test, that is, a conflict was detected.
       
       \remark if the variables with the least coefficient are bounded,
       then the ext_gcd_test is invoked.
    */
    template<typename Ext>
    bool theory_arith<Ext>::gcd_test(row const & r) {
        if (!m_params.m_arith_gcd_test)
            return true;
        m_stats.m_gcd_tests++;
        numeral lcm_den = r.get_denominators_lcm();
        TRACE("gcd_test_bug", r.display(tout); tout << "lcm: " << lcm_den << "\n";);
        numeral consts(0);
        numeral gcds(0);
        numeral least_coeff(0);
        bool    least_coeff_is_bounded = false;
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                if (is_fixed(it->m_var)) {
                    // WARNINING: it is not safe to use get_value(it->m_var) here, since
                    // get_value(it->m_var) may not satisfy it->m_var bounds at this point.
                    numeral aux = lcm_den * it->m_coeff;
                    consts += aux * lower_bound(it->m_var).get_rational();
                }
                else if (is_real(it->m_var)) {
                    return true;
                }
                else if (gcds.is_zero()) {
                    gcds = abs(lcm_den * it->m_coeff);
                    least_coeff = gcds;
                    least_coeff_is_bounded = is_bounded(it->m_var);
                }
                else {
                    numeral aux = abs(lcm_den * it->m_coeff);
                    gcds = gcd(gcds, aux);
                    if (aux < least_coeff) {
                        least_coeff = aux;
                        least_coeff_is_bounded = is_bounded(it->m_var);
                    }
                    else if (least_coeff_is_bounded && aux == least_coeff) {
                        least_coeff_is_bounded = is_bounded(it->m_var);
                    }
                }
                SASSERT(gcds.is_int());
                SASSERT(least_coeff.is_int());
                TRACE("gcd_test_bug", tout << "coeff: " << it->m_coeff << ", gcds: " << gcds 
                      << " least_coeff: " << least_coeff << " consts: " << consts << "\n";);
            }
        }

        if (gcds.is_zero()) {
            // All variables are fixed.
            // This theory guarantees that the assignment satisfies each row, and
            // fixed integer variables are assigned to integer values.
            return true;
        }

        if (!(consts / gcds).is_int()) {
            TRACE("gcd_test", tout << "row failed the GCD test:\n"; display_row_info(tout, r););
            antecedents ante(*this);
            collect_fixed_var_justifications(r, ante);
            context & ctx         = get_context();
            ctx.set_conflict(
                ctx.mk_justification(
                    ext_theory_conflict_justification(
                        get_id(), ctx.get_region(), ante.lits().size(), ante.lits().c_ptr(), 
                        ante.eqs().size(), ante.eqs().c_ptr(), 
                        ante.num_params(), ante.params("gcd-test"))));
            return false;
        }
        
        if (least_coeff.is_one() && !least_coeff_is_bounded) {
            SASSERT(gcds.is_one());
            return true;
        }
        
        if (least_coeff_is_bounded) {
            return ext_gcd_test(r, least_coeff, lcm_den, consts);
        }
        return true;
    }

    /**
       \brief Auxiliary method for gcd_test.
    */
    template<typename Ext>
    bool theory_arith<Ext>::ext_gcd_test(row const & r, numeral const & least_coeff, 
                                         numeral const & lcm_den, numeral const & consts) {
        numeral gcds(0);
        numeral l(consts);
        numeral u(consts);

        antecedents ante(*this);


        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead() && !is_fixed(it->m_var)) {
                theory_var v = it->m_var;
                SASSERT(!is_real(v));
                numeral ncoeff = lcm_den * it->m_coeff;
                SASSERT(ncoeff.is_int());
                numeral abs_ncoeff = abs(ncoeff);
                if (abs_ncoeff == least_coeff) {
                    SASSERT(is_bounded(v));
                    if (ncoeff.is_pos()) {
                        // l += ncoeff * lower_bound(v).get_rational();
                        l.addmul(ncoeff, lower_bound(v).get_rational());
                        // u += ncoeff * upper_bound(v).get_rational();
                        u.addmul(ncoeff, upper_bound(v).get_rational());
                    }
                    else {
                        // l += ncoeff * upper_bound(v).get_rational();
                        l.addmul(ncoeff, upper_bound(v).get_rational());
                        // u += ncoeff * lower_bound(v).get_rational();
                        u.addmul(ncoeff, lower_bound(v).get_rational());
                    }
                    lower(v)->push_justification(ante, it->m_coeff, coeffs_enabled());
                    upper(v)->push_justification(ante, it->m_coeff, coeffs_enabled());
                }
                else if (gcds.is_zero()) {
                    gcds = abs_ncoeff; 
                }
                else {
                    gcds = gcd(gcds, abs_ncoeff);
                }
                SASSERT(gcds.is_int());
            }
        }
        
        if (gcds.is_zero()) {
            return true;
        }
        
        numeral l1 = ceil(l/gcds);
        numeral u1 = floor(u/gcds);
        
        if (u1 < l1) {
            TRACE("gcd_test", tout << "row failed the extended GCD test:\n"; display_row_info(tout, r););
            collect_fixed_var_justifications(r, ante);
            context & ctx         = get_context();
            ctx.set_conflict(
                ctx.mk_justification(
                    ext_theory_conflict_justification(
                        get_id(), ctx.get_region(), 
                        ante.lits().size(), ante.lits().c_ptr(), ante.eqs().size(), ante.eqs().c_ptr(),
                        ante.num_params(), ante.params("gcd-test"))));
            return false;
        }
        
        return true;
    }

    /**
       \brief Return true if all rows pass the GCD test.
    */
    template<typename Ext>
    bool theory_arith<Ext>::gcd_test() {
        if (!m_params.m_arith_gcd_test)
            return true;
        if (m_eager_gcd)
            return true;
        typename vector<row>::const_iterator it  = m_rows.begin();
        typename vector<row>::const_iterator end = m_rows.end();
        for (; it != end; ++it) {
            theory_var v = it->get_base_var();
            if (v != null_theory_var && is_int(v) && !get_value(v).is_int() && !gcd_test(*it)) {
                if (m_params.m_arith_adaptive_gcd)
                    m_eager_gcd = true;
                return false;
            }
        }
        return true;
    }

    /**
       \brief Try to create bounds for unbounded infeasible integer variables.
       Return false if an inconsistency is detected.
    */
    template<typename Ext>
    bool theory_arith<Ext>::max_min_infeasible_int_vars() {
        var_set & already_processed = m_tmp_var_set;
        already_processed.reset();
        svector<theory_var> vars;
        for (;;) {
            vars.reset();
            // Collect infeasible integer variables.
            typename vector<row>::const_iterator it  = m_rows.begin();
            typename vector<row>::const_iterator end = m_rows.end();
            for (; it != end; ++it) {
                theory_var v = it->get_base_var();
                if (v != null_theory_var && is_int(v) && !get_value(v).is_int() && !is_bounded(v) && !already_processed.contains(v)) {
                    vars.push_back(v);
                    already_processed.insert(v);
                }
            }
            if (vars.empty())
                return true;
            if (max_min(vars))
                return false;
        }
    }

    /**
       \brief Try to patch int infeasible vars using freedom intervals.
    */
    template<typename Ext>
    void theory_arith<Ext>::patch_int_infeasible_vars() {
        SASSERT(m_to_patch.empty());
        int num = get_num_vars();
        bool inf_l, inf_u;
        inf_numeral l, u;
        numeral m;
        for (theory_var v = 0; v < num; v++) {
            if (!is_non_base(v)) 
                continue;
            get_freedom_interval(v, inf_l, l, inf_u, u, m);
            if (m.is_one() && get_value(v).is_int())
                continue;
            // check whether value of v is already a multiple of m.
            if ((get_value(v).get_rational() / m).is_int())
                continue;
            TRACE("patch_int",
                  tout << "TARGET v" << v << " -> [";
                  if (inf_l) tout << "-oo"; else tout << ceil(l);
                  tout << ", ";
                  if (inf_u) tout << "oo"; else tout << floor(u);
                  tout << "]";
                  tout << ", m: " << m << ", val: " << get_value(v) << ", is_int: " << is_int(v) << "\n";);
            if (!inf_l)
                l = ceil(l);
            if (!inf_u)
                u = floor(u);
            if (!m.is_one()) {
                if (!inf_l)
                    l = m*ceil(l/m);
                if (!inf_u)
                    u = m*floor(u/m);
            }
            if (!inf_l && !inf_u && l > u)
                continue; // cannot patch
            if (!inf_l)
                set_value(v, l);
            else if (!inf_u)
                set_value(v, u);
            else 
                set_value(v, inf_numeral(0));
        }
        SASSERT(m_to_patch.empty());
    }

    /**
       \brief Force all non basic variables to be assigned to integer values.
    */
    template<typename Ext>
    void theory_arith<Ext>::fix_non_base_vars() {
        int num = get_num_vars();
        for (theory_var v = 0; v < num; v++) {
            if (!is_non_base(v)) 
                continue;
            if (!is_int(v))
                continue;
            if (get_value(v).is_int())
                continue;
            inf_numeral new_val(floor(get_value(v)));
            set_value(v, new_val);
        }
        if (!make_feasible())
            failed();
    }

    template<typename Ext>
    struct theory_arith<Ext>::euclidean_solver_bridge {
        typedef numeral_buffer<mpz, euclidean_solver::numeral_manager> mpz_buffer;
        theory_arith &                t;
        euclidean_solver              m_solver;
        unsigned_vector               m_tv2v; // theory var to euclidean solver var
        svector<theory_var>           m_j2v;  // justification to theory var
        
        // aux fields
        unsigned_vector               m_xs;
        mpz_buffer                    m_as;
        unsigned_vector               m_js;

        typedef euclidean_solver::var            evar;
        typedef euclidean_solver::justification  ejustification;
        euclidean_solver_bridge(theory_arith & _t):t(_t), m_solver(&t.m_es_num_manager), m_as(m_solver.m()) {}
        
        evar mk_var(theory_var v) {
            m_tv2v.reserve(v+1, UINT_MAX);
            if (m_tv2v[v] == UINT_MAX)
                m_tv2v[v] = m_solver.mk_var();
            return m_tv2v[v];
        }

        /**
           \brief Given a monomial, retrieve its coefficient and the power product
           That is, mon = a * pp
        */
        void get_monomial(expr * mon, rational & a, expr * & pp) {
            expr * a_expr;
            if (t.m_util.is_mul(mon, a_expr, pp) && t.m_util.is_numeral(a_expr, a))
                return;
            a  = rational(1);
            pp = mon;
        }

        /**
           \brief Return the theory var associated with the given power product.
         */
        theory_var get_theory_var(expr * pp) {
            context & ctx = t.get_context();
            if (ctx.e_internalized(pp)) {
                enode * e    = ctx.get_enode(pp);
                if (t.is_attached_to_var(e))
                    return e->get_th_var(t.get_id());
            }
            return null_theory_var;
        }

        /**
           \brief Create an euclidean_solver variable for the given
           power product, if it has a theory variable associated with
           it.
        */
        evar mk_var(expr * pp) {
            theory_var v = get_theory_var(pp);
            if (v == null_theory_var)
                return UINT_MAX;
            return mk_var(v);
        }
        
        /**
           \brief Return the euclidean_solver variable associated with the given
           power product. Return UINT_MAX, if it doesn't have one.
        */
        evar get_var(expr * pp) {
            theory_var v = get_theory_var(pp);
            if (v == null_theory_var || v >= static_cast<int>(m_tv2v.size()))
                return UINT_MAX;
            return m_tv2v[v];
        }
        
        void assert_eqs() {
            // traverse definitions looking for equalities
            mpz c, a;
            mpz one;
            euclidean_solver::numeral_manager & m = m_solver.m();
            m.set(one, 1);
            mpz_buffer & as = m_as;
            unsigned_vector & xs = m_xs;
            int num = t.get_num_vars();
            for (theory_var v = 0; v < num; v++) {
                if (!t.is_fixed(v)) 
                    continue;
                if (!t.is_int(v))
                    continue; // only integer variables
                expr * n = t.get_enode(v)->get_owner();
                if (t.m_util.is_numeral(n))
                    continue; // skip stupid equality c - c = 0
                inf_numeral const & val = t.get_value(v);
                rational num = val.get_rational().to_rational();
                SASSERT(num.is_int());
                num.neg();
                m.set(c, num.to_mpq().numerator());
                ejustification j = m_solver.mk_justification();
                m_j2v.reserve(j+1, null_theory_var);
                m_j2v[j] = v;
                as.reset();
                xs.reset();
                bool failed = false;
                unsigned num_args;
                expr * const * args;
                if (t.m_util.is_add(n)) {
                    num_args = to_app(n)->get_num_args();
                    args     = to_app(n)->get_args();
                }
                else {
                    num_args = 1;
                    args     = &n;
                }
                for (unsigned i = 0; i < num_args; i++) {
                    expr * arg = args[i];
                    expr * pp;
                    rational a_val;
                    get_monomial(arg, a_val, pp);
                    if (!a_val.is_int()) {
                        failed = true;
                        break;
                    }
                    evar x = mk_var(pp);
                    if (x == UINT_MAX) {
                        failed = true;
                        break; 
                    }
                    m.set(a, a_val.to_mpq().numerator());
                    as.push_back(a);
                    xs.push_back(x);
                }
                if (!failed) {
                    m_solver.assert_eq(as.size(), as.c_ptr(), xs.c_ptr(), c, j);
                    TRACE("euclidean_solver", tout << "add definition: v" << v << " := " << mk_ismt2_pp(n, t.get_manager()) << "\n";);
                }
                else {
                    TRACE("euclidean_solver", tout << "failed for:\n" << mk_ismt2_pp(n, t.get_manager()) << "\n";);
                }
            }
            m.del(a);
            m.del(c);
            m.del(one);
        }

        void mk_bound(theory_var v, rational k, bool lower, bound * old_bound, unsigned_vector const & js) {
            derived_bound * new_bound = alloc(derived_bound, v, inf_numeral(k), lower ? B_LOWER : B_UPPER);
            t.m_tmp_lit_set.reset();
            t.m_tmp_eq_set.reset();
            if (old_bound != nullptr) {
                t.accumulate_justification(*old_bound, *new_bound, numeral(0) /* refine for proof gen */, t.m_tmp_lit_set, t.m_tmp_eq_set); 
            }
            unsigned_vector::const_iterator it  = js.begin();
            unsigned_vector::const_iterator end = js.end();
            for (; it != end; ++it) {
                ejustification    j = *it;
                theory_var fixed_v = m_j2v[j];
                SASSERT(fixed_v != null_theory_var);
                t.accumulate_justification(*(t.lower(fixed_v)), *new_bound, numeral(0) /* refine for proof gen */, t.m_tmp_lit_set, t.m_tmp_eq_set); 
                t.accumulate_justification(*(t.upper(fixed_v)), *new_bound, numeral(0) /* refine for proof gen */, t.m_tmp_lit_set, t.m_tmp_eq_set); 
            }
            t.m_bounds_to_delete.push_back(new_bound);
            t.m_asserted_bounds.push_back(new_bound);
        }

        void mk_lower(theory_var v, rational k, bound * old_bound, unsigned_vector const & js) {
            mk_bound(v, k, true, old_bound, js);
        }

        void mk_upper(theory_var v, rational k, bound * old_bound, unsigned_vector const & js) {
            mk_bound(v, k, false, old_bound, js);
        }
        
        bool tight_bounds(theory_var v) {
            SASSERT(!t.is_fixed(v));
            euclidean_solver::numeral_manager & m = m_solver.m();
            expr * n = t.get_enode(v)->get_owner();
            SASSERT(!t.m_util.is_numeral(n)); // should not be a numeral since v is not fixed.
            bool propagated = false;
            mpz a;
            mpz c;
            rational  g; // gcd of the coefficients of the variables that are not in m_solver
            rational c2;
            bool init_g = false;
            mpz_buffer & as      = m_as;
            unsigned_vector & xs = m_xs;
            as.reset();
            xs.reset();

            unsigned num_args;
            expr * const * args;
            if (t.m_util.is_add(n)) {
                num_args = to_app(n)->get_num_args();
                args     = to_app(n)->get_args();
            }
            else {
                num_args = 1;
                args     = &n;
            }
            for (unsigned j = 0; j < num_args; j++) {
                expr * arg = args[j];
                expr * pp;
                rational a_val;
                get_monomial(arg, a_val, pp);
                if (!a_val.is_int())
                    goto cleanup;
                evar x = get_var(pp);
                if (x == UINT_MAX) {
                    a_val = abs(a_val);
                    if (init_g)
                        g  = gcd(g, a_val);
                    else
                        g  = a_val;
                    init_g = true;
                    if (g.is_one())
                        goto cleanup; // gcd of the coeffs is one.
                }
                else {
                    m.set(a, a_val.to_mpq().numerator());
                    as.push_back(a);
                    xs.push_back(x);
                }
            }
            m_js.reset();
            m_solver.normalize(as.size(), as.c_ptr(), xs.c_ptr(), c, a, c, m_js);
            if (init_g) {
                if (!m.is_zero(a))
                    g = gcd(g, rational(a));
            }
            else {
                g = rational(a);
            }
            TRACE("euclidean_solver", tout << "tightening " << mk_ismt2_pp(t.get_enode(v)->get_owner(), t.get_manager()) << "\n";
                  tout << "g: " << g << ", a: " << m.to_string(a) << ", c: " << m.to_string(c) << "\n";
                  t.display_var(tout, v););
            if (g.is_one())
                goto cleanup;
            CTRACE("euclidean_solver_zero", g.is_zero(), tout << "tightening " << mk_ismt2_pp(t.get_enode(v)->get_owner(), t.get_manager()) << "\n";
                   tout << "g: " << g << ", a: " << m.to_string(a) << ", c: " << m.to_string(c) << "\n";
                   t.display(tout);
                   tout << "------------\nSolver state:\n";
                   m_solver.display(tout););
            if (g.is_zero()) {
                // The definition of v is equal to (0 + c).
                // That is, v is fixed at c. 
                // The justification is just m_js, the existing bounds of v are not needed for justifying the new bounds for v.
                c2 = rational(c);
                TRACE("euclidean_solver_new", tout << "new fixed: " << c2 << "\n";);
                propagated = true;
                mk_lower(v, c2, nullptr, m_js);
                mk_upper(v, c2, nullptr, m_js);
            }
            else {
                TRACE("euclidean_solver", tout << "inequality can be tightned, since all coefficients are multiple of: " << g << "\n";);
                // Let l and u be the current lower and upper bounds.
                // Then, the following new bounds can be generated:
                //
                // l' := g*ceil((l - c)/g) + c 
                // u' := g*floor((l - c)/g) + c
                bound * l = t.lower(v);
                bound * u = t.upper(v);
                c2 = rational(c);
                if (l != nullptr) {
                    rational l_old = l->get_value().get_rational().to_rational();
                    rational l_new = g*ceil((l_old - c2)/g) + c2;
                    TRACE("euclidean_solver_new", tout << "new lower: " << l_new << " old: " << l_old << "\n";
                          tout << "c: " << c2 << " ceil((l_old - c2)/g): " << (ceil((l_old - c2)/g)) << "\n";);
                    if (l_new > l_old) {
                        propagated = true;
                        mk_lower(v, l_new, l, m_js);
                    }
                }
                if (u != nullptr) {
                    rational u_old  = u->get_value().get_rational().to_rational();
                    rational u_new  = g*floor((u_old - c2)/g) + c2;
                    TRACE("euclidean_solver_new", tout << "new upper: " << u_new << " old: " << u_old << "\n";);
                    if (u_new < u_old) {
                        propagated = true;
                        mk_upper(v, u_new, u, m_js);
                    }
                }
            }
        cleanup:
            m.del(a);
            m.del(c);
            return propagated;
        }

        bool tight_bounds() {
            bool propagated = false;
            context & ctx = t.get_context();
            // try to apply solution set to every definition
            int num = t.get_num_vars();
            for (theory_var v = 0; v < num; v++) {
                if (t.is_fixed(v)) 
                    continue; // skip equations...
                if (!t.is_int(v))
                    continue; // skip non integer definitions...
                if (t.lower(v) == nullptr && t.upper(v) == nullptr)
                    continue; // there is nothing to be tightned
                if (tight_bounds(v))
                    propagated = true;
                if (ctx.inconsistent())
                    break;
            }
            return propagated;
        }

        bool operator()() {
            TRACE("euclidean_solver", t.display(tout););
            assert_eqs();
            m_solver.solve();
            if (m_solver.inconsistent()) {
                // TODO: set conflict
                TRACE("euclidean_solver_conflict", tout << "conflict detected...\n"; m_solver.display(tout););
                return false;
            }
            return tight_bounds();
        }
    };


    template<typename Ext>
    bool theory_arith<Ext>::apply_euclidean_solver() {
        TRACE("euclidean_solver", tout << "executing euclidean solver...\n";);
        euclidean_solver_bridge esb(*this);
        if (esb()) {
            propagate_core();
            return true;
        }
        return false;
    }

    /**
       \brief Return FC_DONE if the assignment is int feasible. Otherwise, apply GCD test,
       branch and bound and Gomory Cuts.
    */
    template<typename Ext>
    final_check_status theory_arith<Ext>::check_int_feasibility() {
        TRACE("arith_int_detail", get_context().display(tout););
        if (!has_infeasible_int_var()) {
            TRACE("arith", tout << "FC_DONE 1...\n"; display(tout););
            return FC_DONE;
        }

        TRACE("arith",
              int num = get_num_vars();
              for (theory_var v = 0; v < num; v++) {
                  if (is_int(v) && !get_value(v).is_int()) {
                      numeral f1 = get_value(v).get_rational() - floor(get_value(v).get_rational());
                      numeral f2 = ceil(get_value(v).get_rational()) - get_value(v).get_rational();
                      if (f2 < f1)
                          f1 = f2;
                      tout << "v" << v << " -> " << f1 << " ";
                      display_var(tout, v);
                  }
              });

        TRACE("arith_int_fracs_min_max",
              numeral max(0);
              numeral min(1);
              int num = get_num_vars();
              for (theory_var v = 0; v < num; v++) {
                  if (is_int(v) && !get_value(v).is_int()) {
                      numeral f1 = get_value(v).get_rational() - floor(get_value(v).get_rational());
                      numeral f2 = ceil(get_value(v).get_rational()) - get_value(v).get_rational();
                      if (f1 < min) min = f1;
                      if (f2 < min) min = f2;
                      if (f1 > max) max = f1;
                      if (f2 > max) max = f2;
                  }
              }
              tout << "max: " << max << ", min: " << min << "\n";);

        if (m_params.m_arith_ignore_int) {
            TRACE("arith", tout << "Ignore int: give up\n";);
            return FC_GIVEUP;
        }

        if (!gcd_test())
            return FC_CONTINUE;

        if (m_params.m_arith_euclidean_solver)
            apply_euclidean_solver();
        
        if (get_context().inconsistent())
            return FC_CONTINUE;

        remove_fixed_vars_from_base();

        TRACE("arith_int_freedom",
              int num = get_num_vars();
              bool inf_l; bool inf_u;
              inf_numeral l; inf_numeral u;
              numeral m;
              for (theory_var v = 0; v < num; v++) {
                  if (is_non_base(v)) {
                      get_freedom_interval(v, inf_l, l, inf_u, u, m);
                      if ((!m.is_one() /* && !l.is_zero() */) || !get_value(v).is_int()) {
                          tout << "TARGET v" << v << " -> [";
                          if (inf_l) tout << "-oo"; else tout << ceil(l);
                          tout << ", ";
                          if (inf_u) tout << "oo"; else tout << floor(u);
                          tout << "]";
                          tout << ", m: " << m << ", val: " << get_value(v) << ", is_int: " << is_int(v) << "\n";
                      }
                  }
              });
        m_stats.m_patches++;
        patch_int_infeasible_vars();
        fix_non_base_vars();
        
        if (get_context().inconsistent())
            return FC_CONTINUE;
        
        TRACE("arith_int_inf",
              int num = get_num_vars();
              for (theory_var v = 0; v < num; v++) {
                  if (is_int(v) && !get_value(v).is_int()) {
                      display_var(tout, v);
                  }
              });

        TRACE("arith_int_rows",
              unsigned num = 0;
              typename vector<row>::const_iterator it  = m_rows.begin();
              typename vector<row>::const_iterator end = m_rows.end();
              for (; it != end; ++it) {
                  theory_var v = it->get_base_var();
                  if (v == null_theory_var)
                      continue;
                  if (is_int(v) && !get_value(v).is_int()) {
                      num++;
                      display_simplified_row(tout, *it);
                      tout << "\n";
                  }
              }
              tout << "num infeasible: " << num << "\n";);
        
        theory_var int_var = find_infeasible_int_base_var();
        if (int_var == null_theory_var) {
            m_stats.m_patches_succ++;
            TRACE("arith_int_incomp", tout << "FC_DONE 2...\n"; display(tout););
            return m_liberal_final_check || !m_changed_assignment ? FC_DONE : FC_CONTINUE;
        }
        
#if 0
        if (find_bounded_infeasible_int_base_var() == null_theory_var) {
            // TODO: this is too expensive... I should replace it by a procedure
            // that refine bounds using the current state of the tableau.
            if (!max_min_infeasible_int_vars())
                return FC_CONTINUE;
            if (!gcd_test())
                return FC_CONTINUE;
        }
#endif 

        m_branch_cut_counter++;
        // TODO: add giveup code
        TRACE("gomory_cut", tout << m_branch_cut_counter << ", " << m_params.m_arith_branch_cut_ratio << std::endl;);
        if (m_branch_cut_counter % m_params.m_arith_branch_cut_ratio == 0) {
            TRACE("opt_verbose", display(tout););
            move_non_base_vars_to_bounds();
            if (!make_feasible()) {
                TRACE("arith_int", tout << "failed to move variables to bounds.\n";);
                failed();
                return FC_CONTINUE;
            }
            theory_var int_var = find_infeasible_int_base_var();
            if (int_var != null_theory_var) {
                TRACE("arith_int", tout << "v" << int_var << " does not have an integer assignment: " << get_value(int_var) << "\n";);
                SASSERT(is_base(int_var));
                row const & r = m_rows[get_var_row(int_var)];
                if (!mk_gomory_cut(r)) {
                    TRACE("gomory_cut", tout << "silent failure\n";);
                }
                return FC_CONTINUE;
            }
        }
        else {
            if (m_params.m_arith_int_eq_branching && branch_infeasible_int_equality()) {
                return FC_CONTINUE;
            }

            theory_var int_var = find_infeasible_int_base_var();
            if (int_var != null_theory_var) {
                TRACE("arith_int", tout << "v" << int_var << " does not have an integer assignment: " << get_value(int_var) << "\n";);
                // apply branching 
                branch_infeasible_int_var(int_var);
                return FC_CONTINUE;
            }
        }
        return m_liberal_final_check || !m_changed_assignment ? FC_DONE : FC_CONTINUE;
    }

};

#endif /* THEORY_ARITH_INT_H_ */

