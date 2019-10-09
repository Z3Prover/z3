/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_arith_nl.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-12-08.

Revision History:

--*/
#ifndef THEORY_ARITH_NL_H_
#define THEORY_ARITH_NL_H_

#include "ast/ast_smt2_pp.h"

namespace smt {

    template<typename Ext>
    expr * theory_arith<Ext>::mk_nary_mul(unsigned sz, expr * const * args, bool is_int) {
        if (sz == 0)
            return m_util.mk_numeral(rational(1), is_int);
        if (sz == 1)
            return args[0];
        if (sz == 2)
            return m_util.mk_mul(args[0], args[1]);
        if (m_util.is_numeral(args[0]))
            return m_util.mk_mul(args[0], m_util.mk_mul(sz - 1, args + 1));
        return m_util.mk_mul(sz, args);
    }

    template<typename Ext>
    expr * theory_arith<Ext>::mk_nary_add(unsigned sz, expr * const * args, bool is_int) {
        if (sz == 0)
            return m_util.mk_numeral(rational(0), is_int);
        if (sz == 1)
            return args[0];
        return m_util.mk_add(sz, args);
    }

    template<typename Ext>
    expr * theory_arith<Ext>::mk_nary_add(unsigned sz, expr * const * args) {
        SASSERT(sz != 0);
        return mk_nary_add(sz, args, false);
    }

    /**
       \brief Insert v into vars and already_found if v is not already in already_found.
    */
    template<typename Ext>
    void theory_arith<Ext>::mark_var(theory_var v, svector<theory_var> & vars, var_set & already_found) {
        if (already_found.contains(v))
            return;
        already_found.insert(v);
        vars.push_back(v);
    }

    /**
       \brief Invoke mark_var for all variables in rows that contain v.
    */
    template<typename Ext>
    void theory_arith<Ext>::mark_dependents(theory_var v, svector<theory_var> & vars, var_set & already_found, row_set & already_visited_rows) {
        if (is_pure_monomial(v)) {
            expr * n     = var2expr(v);
            SASSERT(m_util.is_mul(n));
            for (expr * curr : *to_app(n)) {
                theory_var v = expr2var(curr);
                SASSERT(v != null_theory_var);
                mark_var(v, vars, already_found);
            }
        }
        if (is_fixed(v))
            return;
        column & c      = m_columns[v];
        typename svector<col_entry>::iterator it  = c.begin_entries();
        typename svector<col_entry>::iterator end = c.end_entries();
        for (; it != end; ++it) {
            if (it->is_dead() || already_visited_rows.contains(it->m_row_id))
                continue;
            TRACE("non_linear_bug", tout << "visiting row: " << it->m_row_id << "\n";);
            already_visited_rows.insert(it->m_row_id);
            row & r        = m_rows[it->m_row_id];
            theory_var s  = r.get_base_var();
            // ignore quasi base vars... actually they should not be used if the problem is non linear...
            if (is_quasi_base(s))
                continue;
            // If s is a base variable different from v and it is free, then this row can be ignored.
            // It doesn't need to be part of the non linear cluster. For all purposes, this variable
            // was eliminated by substitution.
            if (is_free(s) && s != v)
                continue;
            typename vector<row_entry>::const_iterator it2  = r.begin_entries();
            typename vector<row_entry>::const_iterator end2 = r.end_entries();
            for (; it2 != end2; ++it2) {
                if (!it2->is_dead() && !is_fixed(it2->m_var))
                    mark_var(it2->m_var, vars, already_found);
            }
        }
    }

    /**
       \brief Store in vars the variables that are in the non linear cluster of constraints,
       and are not satisfied by the current assignment.
    */
    template<typename Ext>
    void theory_arith<Ext>::get_non_linear_cluster(svector<theory_var> & vars) {
        if (m_nl_monomials.empty())
            return;
        var_set already_found;
        row_set already_visited_rows;
        context & ctx = get_context();
        for (theory_var v : m_nl_monomials) {
            expr * n     = var2expr(v);
            if (ctx.is_relevant(n))
                mark_var(v, vars, already_found);
        }
        // NB: vars changes inside of loop
        for (unsigned idx = 0; idx < vars.size(); ++idx) {
            theory_var v = vars[idx];
            TRACE("non_linear", tout << "marking dependents of: v" << v << "\n";);
            mark_dependents(v, vars, already_found, already_visited_rows);
        }
        TRACE("non_linear", tout << "variables in non linear cluster:\n";
              for (theory_var v : vars) tout << "v" << v << " ";
              tout << "\n";);
    }

    /**
       \brief Return the number of variables that
       do not have bounds associated with it.
       The result is 0, 1, or 2. The value 2 means "2 or more".
       The second value is the idx of the variable that does not
       have bounds associated with it. It is only useful when the first value is 1.
       The second value is -1 if such variable does not exist, that is, the first
       value is 0.

       \remark if a variables has an even number of occurrences, then
       I consider that it has a bound associated with it.

       Examples:
       1) Assume x1, x4 have bounds:
       analyze_monomial(x1 * x2 * x2 * x3 * x3 * x3 * x4)
       -->
       (1,2)
       Explanation: x2 doesn't have bounds, but x2 has an even power.
       So x2*x2 has bound [0, oo). So, there is one variable without bounds x3.
       It is the third variable in the monomial, then its idx is 2.
    */
    template<typename Ext>
    std::pair<unsigned, int> theory_arith<Ext>::analyze_monomial(expr * m) const {
        SASSERT(is_pure_monomial(m));
        expr * var       = nullptr;
        unsigned power   = 0;
        unsigned c       = 0;
        int free_var_idx = -1;
        int idx          = 0;
        for (unsigned i = 0; i < to_app(m)->get_num_args(); i++) {
            expr * arg = to_app(m)->get_arg(i);
            if (var == nullptr) {
                var   = arg;
                power = 1;
            }
            else if (arg == var) {
                power++;
            }
            else {
                if (power % 2 == 1 && is_free(var)) {
                    c++;
                    free_var_idx = idx;
                    if (c > 1)
                        return std::make_pair(2, free_var_idx);
                }
                var   = arg;
                power = 1;
                idx++;
            }
        }
        if (power % 2 == 1 && is_free(var)) {
            c++;
            free_var_idx = idx;
        }
        return std::make_pair(c, free_var_idx);
    }

    /**
       \brief Given a monomial c*M, return M
    */
    template<typename Ext>
    expr * theory_arith<Ext>::get_monomial_body(expr * m) const {
        SASSERT(m_util.is_mul(m));
        if (m_util.is_numeral(to_app(m)->get_arg(0)))
            return to_app(m)->get_arg(1);
        return m;
    }

    /**
       \brief Given a monomial c*M, return c
    */
    template<typename Ext>
    rational theory_arith<Ext>::get_monomial_coeff(expr * m) const {
        SASSERT(m_util.is_mul(m));
        rational r;
        if (m_util.is_numeral(to_app(m)->get_arg(0), r))
            return r;
        return rational(1);
    }

    /**
       \brief Return the number of distinct variables in the given monomial.
    */
    template<typename Ext>
    unsigned theory_arith<Ext>::get_num_vars_in_monomial(expr * m) const {
        SASSERT(m_util.is_mul(m));
        m = get_monomial_body(m);
        SASSERT(!m_util.is_numeral(m));
        if (m_util.is_mul(m)) {
            unsigned num_vars = 0;
            expr * var = nullptr;
            for (expr * curr : *to_app(m)) {
                if (var != curr) {
                    num_vars++;
                    var = curr;
                }
            }
            return num_vars;
        }
        else {
            return 1;
        }
    }

    /**
       \brief Return the i-th var of m and its power.
    */
    template<typename Ext>
    typename theory_arith<Ext>::var_power_pair theory_arith<Ext>::get_var_and_degree(expr * m, unsigned i) const {
        SASSERT(m_util.is_mul(m));
        SASSERT(i < get_num_vars_in_monomial(m));
        m = get_monomial_body(m);
        if (m_util.is_mul(m)) {
            unsigned curr_idx = 0;
            expr * var        = nullptr;
            unsigned power    = 0;
            for (expr * arg : *to_app(m)) {
                if (var == nullptr) {
                    var   = arg;
                    power = 1;
                }
                else if (var == arg) {
                    power++;
                }
                else {
                    if (curr_idx == i)
                        return var_power_pair(var, power);
                    curr_idx++;
                    var   = arg;
                    power = 1;
                }
            }
            SASSERT(curr_idx == i);
            return var_power_pair(var, power);
        }
        else {
            SASSERT(i == 0);
            return var_power_pair(m, 1);
        }
    }

    /**
       \brief Return an interval using the bounds for v.
    */
    template<typename Ext>
    interval theory_arith<Ext>::mk_interval_for(theory_var v) {
        bound * l = lower(v);
        bound * u = upper(v);
        if (l && u) {
            return interval(m_dep_manager,
                            l->get_value().get_rational().to_rational(),
                            !l->get_value().get_infinitesimal().to_rational().is_zero(),
                            m_dep_manager.mk_leaf(l),
                            u->get_value().get_rational().to_rational(),
                            !u->get_value().get_infinitesimal().to_rational().is_zero(),
                            m_dep_manager.mk_leaf(u));
        }
        else if (l) {
            return interval(m_dep_manager,
                            l->get_value().get_rational().to_rational(),
                            !l->get_value().get_infinitesimal().to_rational().is_zero(),
                            true,
                            m_dep_manager.mk_leaf(l));
        }
        else if (u) {
            return interval(m_dep_manager,
                            u->get_value().get_rational().to_rational(),
                            !u->get_value().get_infinitesimal().to_rational().is_zero(),
                            false,
                            m_dep_manager.mk_leaf(u));
        }
        else {
            return interval(m_dep_manager);
        }
    }

    /**
       \brief Return an interval for the given expression using its bounds.
    */
    template<typename Ext>
    interval theory_arith<Ext>::mk_interval_for(expr * n) {
        if (!has_var(n))
            return interval(m_dep_manager);
        return mk_interval_for(expr2var(n));
    }

    /**
       \brief target *= [lower(var), upper(var)]^power
    */
    template<typename Ext>
    void theory_arith<Ext>::mul_bound_of(expr * var, unsigned power, interval & target) {
        theory_var v  = expr2var(var);
        interval i = mk_interval_for(v);

        TRACE("non_linear",
              display_interval(tout << "bound: ",i); tout << i << "\n";
              tout << mk_pp(var, get_manager()) << "\n";
              tout << "power " << power << ": " << expt(i, power) << "\n";
              display_interval(tout << "target before: ", target); tout << "\n";);

        i.expt(power);
        target *= i;

        get_manager().limit().inc((target.is_lower_open() || target.minus_infinity()) ? 1 : target.get_lower_value().bitsize());
        get_manager().limit().inc((target.is_upper_open() || target.plus_infinity()) ? 1 : target.get_upper_value().bitsize());

        TRACE("non_linear", display_interval(tout << "target after: ", target); tout << "\n";);
    }

    /**
       \brief Evaluate the given expression using interval arithmetic.

       - If a subexpression is internalized, then mk_interval_for is used to
       compute its interval.

       - Only +, *, and numerals are handled.
    */
    template<typename Ext>
    interval theory_arith<Ext>::evaluate_as_interval(expr * n) {
        expr* arg;
        rational val;
        TRACE("nl_evaluate", tout << "evaluating: " << mk_bounded_pp(n, get_manager(), 10) << "\n";);
        if (has_var(n)) {
            TRACE("nl_evaluate", tout << "n has a variable associated with it\n";);
            TRACE("cross_nested_eval_bug", display_nested_form(tout, n); tout << "\ninterval: " << mk_interval_for(n) << "\n";
                  display_var(tout, expr2var(n)););
            return mk_interval_for(n);
        }
        else if (m_util.is_add(n)) {
            TRACE("nl_evaluate", tout << "is add\n";);
            interval r(m_dep_manager, rational(0));
            for (expr* arg : *to_app(n)) {
                r += evaluate_as_interval(arg);
            }
            TRACE("cross_nested_eval_bug", display_nested_form(tout, n); tout << "\ninterval: " << r << "\n";);
            return r;
        }
        else if (m_util.is_mul(n)) {
            TRACE("nl_evaluate", tout << "is mul\n";);
            interval r(m_dep_manager, get_monomial_coeff(n));
            unsigned num_vars = get_num_vars_in_monomial(n);
            for (unsigned i = 0; i < num_vars; i++) {
                var_power_pair p = get_var_and_degree(n, i);
                expr * var       = p.first;
                unsigned power   = p.second;
                interval it      = evaluate_as_interval(var);
                it.expt(power);
                r               *= it;
            }
            TRACE("nl_evaluate", display_nested_form(tout, n); tout << "\ninterval: " << r << "\n";);
            return r;
        }
        else if (m_util.is_to_real(n, arg)) {
            return evaluate_as_interval(arg);
        }
        else if (m_util.is_numeral(n, val)) {
            TRACE("nl_evaluate", tout << "is numeral\n";);
            return interval(m_dep_manager, val);
        }
        else {
            TRACE("nl_evaluate", tout << "is unknown\n";);
            return interval(m_dep_manager);
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::display_monomial(std::ostream & out, expr * n) const {
        bool first = true;
        unsigned num_vars = get_num_vars_in_monomial(n);
        for (unsigned i = 0; i < num_vars; i++) {
            var_power_pair p = get_var_and_degree(n, i);
            SASSERT(p.first != 0);
            if (first) first = false; else out << " * ";
            out << mk_bounded_pp(p.first, get_manager()) << "^" << p.second;
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::dependency2new_bound(v_dependency * dep, derived_bound& new_bound) {
        ptr_vector<void> bounds;
        m_dep_manager.linearize(dep, bounds);
        m_tmp_lit_set.reset();
        m_tmp_eq_set.reset();
        for (void* _b : bounds) {
            bound * b = static_cast<bound*>(_b);
            accumulate_justification(*b, new_bound, numeral::zero(), m_tmp_lit_set, m_tmp_eq_set);
        }
    }

    /**
       \brief Create a new derived bound. The justification is stored in the object dep.
    */
    template<typename Ext>
    void theory_arith<Ext>::mk_derived_nl_bound(theory_var v, inf_numeral const & coeff, bound_kind k, v_dependency * dep) {
        inf_numeral coeff_norm = normalize_bound(v, coeff, k);
        derived_bound * new_bound = alloc(derived_bound, v, coeff_norm, k);
        m_bounds_to_delete.push_back(new_bound);
        m_asserted_bounds.push_back(new_bound);
        // copy justification to new bound
        dependency2new_bound(dep, *new_bound);
        TRACE("non_linear", new_bound->display(*this, tout); tout << "\n";);
    }

    /**
       \brief Update the bounds of v, using the interval i.
       Return true if i improves the bounds of v.
    */
    template<typename Ext>
    bool theory_arith<Ext>::update_bounds_using_interval(theory_var v, interval const & i) {
        SASSERT(v != null_theory_var);
        bool r = false;
        if (!i.minus_infinity()) {
            inf_numeral new_lower(i.get_lower_value());
            if (i.is_lower_open()) {
                if (is_int(v)) {
                    if (new_lower.is_int()) {
                        new_lower += rational::one();
                    }
                    else {
                        new_lower = ceil(new_lower.get_rational());
                    }
                }
                else {
                    new_lower += get_epsilon(v);
                }
            }
            bound * old_lower = lower(v);
            if (old_lower == nullptr || new_lower > old_lower->get_value()) {
                TRACE("non_linear", tout << "NEW lower bound for v" << v << " " << new_lower << "\n";
                      display_interval(tout, i); tout << "\n";);
                mk_derived_nl_bound(v, new_lower, B_LOWER, i.get_lower_dependencies());
                r = true;
            }
        }
        if (!i.plus_infinity()) {
            inf_numeral new_upper(i.get_upper_value());
            if (i.is_upper_open()) {
                if (is_int(v)) {
                    if (new_upper.is_int()) {
                        new_upper -= rational::one();
                    }
                    else {
                        new_upper = floor(new_upper.get_rational());
                    }
                }
                else {
                    new_upper -= get_epsilon(v);
                }
            }
            bound * old_upper = upper(v);
            if (old_upper == nullptr || new_upper < old_upper->get_value()) {
                TRACE("non_linear", tout << "NEW upper bound for v" << v << " " << new_upper << "\n";
                      display_interval(tout, i); tout << "\n";);
                mk_derived_nl_bound(v, new_upper, B_UPPER, i.get_upper_dependencies());
                r = true;
            }
        }
        return r;
    }

    template<typename Ext>
    bool theory_arith<Ext>::update_bounds_using_interval(expr * n, interval const & i) {
        SASSERT(expr2var(n) != null_theory_var);
        TRACE("non_linear", tout << "NL bounds for m: " << i << "\n" << mk_pp(n, get_manager()) << "\n";);
        return update_bounds_using_interval(expr2var(n), i);
    }

    /**
       \brief Use the bounds of the variables to build a bound for m.
    */
    template<typename Ext>
    bool theory_arith<Ext>::propagate_nl_upward(expr * m) {
        SASSERT(is_pure_monomial(m));
        unsigned num_vars = get_num_vars_in_monomial(m);
        interval new_bounds(m_dep_manager, rational(1));
        // TODO: the following code can be improved it is quadratic on the degree of the monomial.
        TRACE("nl_arith_bug", tout << "processing upward:\n" << mk_pp(m, get_manager()) << "\n";);
        for (unsigned i = 0; i < num_vars; i++) {
            var_power_pair p = get_var_and_degree(m, i);
            expr * var       = p.first;
            unsigned power   = p.second;
            TRACE("nl_arith_bug", tout << "interval before: " << new_bounds << "\n";
                  theory_var v  = expr2var(var);
                  interval i = mk_interval_for(v);
                  display_var(tout, v);
                  tout << "interval for var: " << i << "\n" << mk_pp(var, get_manager()) << "\npower: " << power << " " << expt(i, power) << "\n";);
            mul_bound_of(var, power, new_bounds);
            TRACE("nl_arith_bug", tout << "interval after: " << new_bounds << "\n";);
        }
        return update_bounds_using_interval(m, new_bounds);
    }

    /**
       \brief Propagate a bound to the i-th variable of the given monomial
       using the bounds of m and other variables in m.

       \remark We do not support roots in interval... so, if the i-th var has power != 1
       the method returns without doing anything.
    */
    template<typename Ext>
    bool theory_arith<Ext>::propagate_nl_downward(expr * n, unsigned i) {
        SASSERT(is_pure_monomial(n));
        SASSERT(i < get_num_vars_in_monomial(n));
        var_power_pair p = get_var_and_degree(n, i);
        expr * v         = p.first;
        unsigned power   = p.second;
        if (power != 1)
            return false; // TODO: remove, when the n-th root is implemented in interval.
        unsigned num_vars = get_num_vars_in_monomial(n);
        interval other_bounds(m_dep_manager, rational(1));
        // TODO: the following code can be improved it is quadratic on the degree of the monomial.
        for (unsigned i = 0; i < num_vars; i++) {
            var_power_pair p = get_var_and_degree(n, i);
            if (p.first == v)
                continue;
            expr * var       = p.first;
            unsigned power   = p.second;
            mul_bound_of(var, power, other_bounds);
        }
        if (other_bounds.contains_zero())
            return false; // interval division requires that divisor doesn't contain 0.
        interval r = mk_interval_for(n);
        TRACE("nl_arith_bug", tout << "m: " << mk_ismt2_pp(n, get_manager()) << "\nv: " << mk_ismt2_pp(v, get_manager()) <<
              "\npower: " << power << "\n";
              tout << "num_vars: " << num_vars << "\n";
              display_interval(tout << "monomial bounds\n", r);
              display_interval(tout << "other bounds\n", other_bounds);
              );
        r /= other_bounds;
        return update_bounds_using_interval(v, r);
    }

    /**
       \brief Try to propagate a bound using the given non linear
       monomial.
       Return true if some bound was propagated.
       If i == -1, then use the bound of the variables to propagate a bound for
       the monomial m.
       If i != -1, then it is the index of the variable that I will compute bounds for.
    */
    template<typename Ext>
    bool theory_arith<Ext>::propagate_nl_bound(expr * m, int i) {
        TRACE("propagate_nl_bound", tout << "propagate using i: " << i << "\n"; display_monomial(tout, m); tout << "\n";);
        if (i == -1)
            return propagate_nl_upward(m);
        else
            return propagate_nl_downward(m, i);
    }

    /**
       \brief The given monomial and its elements have bounds.
       Propagate bounds to all of them.
       Return true if some bound was propagated.
    */
    template<typename Ext>
    bool theory_arith<Ext>::propagate_nl_bounds(expr * m) {
        TRACE("non_linear", tout << "propagate several bounds using:\n"; display_monomial(tout, m); tout << "\n";);
        bool result = propagate_nl_upward(m);
        unsigned num_vars = get_num_vars_in_monomial(m);
        for (unsigned i = 0; i < num_vars; i++)
            if (propagate_nl_downward(m, i)) {
                m_stats.m_nl_bounds++;
                result = true;
            }
        return result;
    }

    /**
       \brief Try to propagate bounds using non linear monomials.
       Return true if some bound was propagated.
    */
    template<typename Ext>
    bool theory_arith<Ext>::propagate_nl_bounds() {
        m_dep_manager.reset();
        bool propagated = false;
        context & ctx = get_context();
        for (unsigned i = 0; i < m_nl_monomials.size(); i++) {
            theory_var v = m_nl_monomials[i];
            expr * m     = var2expr(v);
            if (!ctx.is_relevant(m))
                continue;
            std::pair<unsigned, int> p = analyze_monomial(m);
            TRACE("propagate_nl_bound", tout << "m: " << mk_ismt2_pp(m, get_manager()) << "\n" << "p: " << p.first << " " << p.second << "\n";);
            unsigned num_bad_vars = p.first;
            int      free_var_idx = p.second;
            SASSERT(num_bad_vars != 1 || free_var_idx != -1);
            if (num_bad_vars >= 2)
                continue;
            bool is_free_m = is_free(m);
            TRACE("propagate_nl_bound", tout << "is_free_m: " << is_free_m << "\n";);
            if (num_bad_vars == 1 && is_free_m)
                continue;
            if (num_bad_vars == 0) {
                if (!is_free_m) {
                    if (propagate_nl_bounds(m))
                        propagated = true;
                }
                else {
                    if (propagate_nl_bound(m, -1)) {
                        m_stats.m_nl_bounds++;
                        propagated = true;
                    }
                }
            }
            else {
                SASSERT (!is_free_m);
                if (propagate_nl_bound(m, free_var_idx)) {
                    m_stats.m_nl_bounds++;
                    propagated = true;
                }
            }
        }
        return propagated;
    }

    /**
       \brief Return the value of v as a rational. If computed_epsilon = false and v has an infinitesimal, then
       compute_epsilon() is invoked.
    */
    template<typename Ext>
    rational theory_arith<Ext>::get_value(theory_var v, bool & computed_epsilon) {
        inf_numeral const & val = get_value(v);
        if (!val.get_infinitesimal().is_zero() && !computed_epsilon) {
            compute_epsilon();
            computed_epsilon = true;
            m_model_depends_on_computed_epsilon = true;
        }
        return  val.get_rational().to_rational() + m_epsilon.to_rational() * val.get_infinitesimal().to_rational();
    }

    /**
       \brief Return true if for the monomial x_1 * ... * x_n associated with v,
       the following holds:

       get_value(x_1) * ... * get_value(x_n) = get_value(v)
    */
    template<typename Ext>
    bool theory_arith<Ext>::check_monomial_assignment(theory_var v, bool & computed_epsilon) {
        SASSERT(is_pure_monomial(var2expr(v)));
        expr * m      = var2expr(v);
        rational val(1), v_val;
        for (expr* arg : *to_app(m)) {
            theory_var curr = expr2var(arg);
            SASSERT(curr != null_theory_var);
            v_val = get_value(curr, computed_epsilon);
            TRACE("non_linear", tout << mk_pp(arg, get_manager()) << " = " << v_val << "\n";);
            val *= v_val;
        }
        v_val = get_value(v, computed_epsilon);
        TRACE("non_linear", tout << "v" << v << " := " << v_val << " == " << val << "\n";);
        return v_val == val;
    }


    /**
       \brief Return true if for every monomial x_1 * ... * x_n,
       get_value(x_1) * ... * get_value(x_n) = get_value(x_1 * ... * x_n)
    */
    template<typename Ext>
    bool theory_arith<Ext>::check_monomial_assignments() {
        bool computed_epsilon = false;
        context & ctx         = get_context();
        svector<theory_var>::const_iterator it  = m_nl_monomials.begin();
        svector<theory_var>::const_iterator end = m_nl_monomials.end();
        for (; it != end; ++it) {
            TRACE("non_linear", tout << "v" << *it << " is relevant: " << ctx.is_relevant(get_enode(*it)) << "\n";
                  tout << "check_monomial_assignments result: " << check_monomial_assignment(*it, computed_epsilon) << "\n";
                  tout << "computed_epsilon: " << computed_epsilon << "\n";);
            if (ctx.is_relevant(get_enode(*it)) && !check_monomial_assignment(*it, computed_epsilon)) {
                TRACE("non_linear_failed", tout << "check_monomial_assignment failed for:\n" << mk_ismt2_pp(var2expr(*it), get_manager()) << "\n";
                      display_var(tout, *it););
                
                return false;
            }
        }
        return true;
    }

    /**
       \brief Try to find an integer variable for performing branching
       in the non linear cluster.

       The idea is select a variable in a monomial with an invalid
       assignment. I give preference to variables with small ranges.
       If no variable is bounded, then select a random one.

       Free variables are not considered.
    */
    template<typename Ext>
    theory_var theory_arith<Ext>::find_nl_var_for_branching() {
        TRACE("nl_branching", tout << "looking for variable to branch...\n"; display(tout););
        context & ctx     = get_context();
        theory_var target = null_theory_var;
        bool bounded      = false;
        unsigned n        = 0;
        numeral range;
        for (unsigned j = 0; j < m_nl_monomials.size(); ++j) {
            theory_var v = m_nl_monomials[j];
            if (is_real(v))
                continue;
            bool computed_epsilon = false;
            bool r = check_monomial_assignment(v, computed_epsilon);
            if (!r) {
                expr * m = get_enode(v)->get_owner();
                SASSERT(is_pure_monomial(m));
                for (unsigned i = 0; i < to_app(m)->get_num_args(); i++) {
                    expr * arg = to_app(m)->get_arg(i);
                    theory_var curr = ctx.get_enode(arg)->get_th_var(get_id());
                    TRACE("nl_branching", tout << "target: v" << target << ", curr: v" << curr << "\n";);
                    if (!is_fixed(curr) && is_int(curr)) {
                        if (is_bounded(curr)) {
                            numeral new_range;
                            new_range  = upper_bound(curr).get_rational();
                            new_range -= lower_bound(curr).get_rational();
                            if (!bounded || new_range < range) {
                                target  = curr;
                                range   = new_range;
                                bounded = true;
                            }
                        }
                        else if (!bounded) {
                            n++;
                            TRACE("nl_branching", tout << "n: " << n << "\n";);
                            if (m_random()%n == 0)
                                target = curr;
                            SASSERT(target != null_theory_var);
                        }
                        SASSERT(target != null_theory_var);
                    }
                    TRACE("nl_branching", tout << "after target: v" << target << "\n";);
                }
            }
        }
        return target;
    }

    /**
       \brief Branch on an integer variable. This method is invoked when v is part
       of a non linear monomial that is not satisfied by the current assignment.
       if v >= l, then create the case split v >= l+1
       else v <= u, then create the case split v <= u-1
       else create the bound v = 0 and case split on it.
    */
    template<typename Ext>
    bool theory_arith<Ext>::branch_nl_int_var(theory_var v) {
        TRACE("non_linear", tout << "BRANCHING on v" << v << "\n";);
        m_stats.m_nl_branching++;
        SASSERT(is_int(v));
        expr * bound = nullptr;
        if (lower(v))
            bound  = m_util.mk_le(var2expr(v), m_util.mk_numeral(lower_bound(v).get_rational().to_rational(), true));
        else if (upper(v))
            bound  = m_util.mk_ge(var2expr(v), m_util.mk_numeral(upper_bound(v).get_rational().to_rational(), true));
        else
            bound  = m_util.mk_eq(var2expr(v), m_util.mk_numeral(rational(0), true));
        TRACE("non_linear", tout << "new bound:\n" << mk_pp(bound, get_manager()) << "\n";);
        context & ctx = get_context();
        ast_manager & m = get_manager();
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_or(bound, m.mk_not(bound));
            log_axiom_instantiation(body);
        }
        ctx.internalize(bound, true);
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        ctx.mark_as_relevant(bound);
        literal l     = ctx.get_literal(bound);
        SASSERT(!l.sign());
        ctx.set_true_first_flag(l.var()); // force the context to case split to true first, independently of the phase selection strategy.
        return true;
    }

    /**
       \brief Return true if the given monomial is linear.
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_monomial_linear(expr * m) const {
        SASSERT(is_pure_monomial(m));
        unsigned num_nl_vars = 0;
        for (expr* arg : *to_app(m)) {
            theory_var _var = expr2var(arg);
            if (!is_fixed(_var)) {
                num_nl_vars++;
            }
            else if (lower_bound(_var).is_zero()) {
                return true;
            }
        }
        return num_nl_vars <= 1;
    }

    /**
       \brief Return the product of the value of the fixed variables in the
       monomial m.
    */
    template<typename Ext>
    typename theory_arith<Ext>::numeral theory_arith<Ext>::get_monomial_fixed_var_product(expr * m) const {
        SASSERT(is_pure_monomial(m));
        numeral r(1);
        for (unsigned i = 0; i < to_app(m)->get_num_args(); i++) {
            expr * arg = to_app(m)->get_arg(i);
            theory_var _var = expr2var(arg);
            if (is_fixed(_var))
                r *= lower_bound(_var).get_rational();
        }
        TRACE("arith", tout << mk_pp(m, get_manager()) << " " << r << "\n";);
        return r;
    }

    /**
       \brief Return the first non fixed variable in the given monomial.
       Return 0, if the monomial does not have a non fixed variable.
    */
    template<typename Ext>
    expr * theory_arith<Ext>::get_monomial_non_fixed_var(expr * m) const {
        SASSERT(is_pure_monomial(m));
        for (unsigned i = 0; i < to_app(m)->get_num_args(); i++) {
            expr * arg = to_app(m)->get_arg(i);
            theory_var _var = expr2var(arg);
            if (!is_fixed(_var))
                return arg;
        }
        return nullptr;
    }

    /**
       \brief Propagate linear monomial. Check whether the give
       monomial became linear and propagate.
    */
    template<typename Ext>
    bool theory_arith<Ext>::propagate_linear_monomial(theory_var v) {
        TRACE("non_linear", tout << "checking whether v" << v << " became linear...\n";);
        if (m_data[v].m_nl_propagated)
            return false; // already propagated this monomial.
        expr * m = var2expr(v);
        if (!is_monomial_linear(m))
            return false; // monomial is not linear.

        m_stats.m_nl_linear++;

        m_data[v].m_nl_propagated = true;
        m_nl_propagated.push_back(v);
        TRACE("non_linear", tout << "v" << v << " is linear " << mk_pp(m, get_manager()) << "\n";);


        numeral k                 = get_monomial_fixed_var_product(m);
        TRACE("non_linear", tout << "new linear monomial... k: " << k << "\n";);
        expr *  x_n               = k.is_zero() ? nullptr : get_monomial_non_fixed_var(m);
        TRACE("non_linear_bug", if (x_n != 0) { tout << "x_n: " << mk_bounded_pp(x_n, get_manager()) << "\nx_n: #" << x_n->get_id() << "\n"; });
        context & ctx             = get_context();
        derived_bound * new_lower = nullptr;
        derived_bound * new_upper = nullptr;
        if (x_n != nullptr) {
            // All but one of the x_i variables are assigned.
            // Let x_n be the unassigned variable.
            // Then, we know that x_1*...*x_n = k*x_n, where k is the product of beta(x_1)*...*beta(x_{n-1})
            // beta(x_i) == lower(x_i)

            // Let m be (* x_1 ... x_n), then assert equality
            // (= (+ (* x_1 ... x_n) (* -k x_n)) 0) when x_1 ... x_{n-1} are fixed variables.
            // where k = lower(x_1)*...*lower(x_{n-1})
            TRACE("non_linear", tout << "x_n: " << mk_pp(x_n, get_manager()) << "\n";);
            k.neg();
            expr * k_x_n = k.is_one() ? x_n : m_util.mk_mul(m_util.mk_numeral(k.to_rational(), is_int(v)), x_n);
            expr * rhs   = m_util.mk_add(m, k_x_n);
            TRACE("non_linear_bug", tout << "rhs: " << mk_bounded_pp(rhs, get_manager(),5) << "\ninternalized: " << ctx.e_internalized(rhs) << "\n";);
            if (!has_var(rhs)) {
                ctx.internalize(rhs, false);
                ctx.mark_as_relevant(rhs);
            }
            TRACE("non_linear_bug", tout << "enode: " << get_context().get_enode(rhs) << " enode_id: " << get_context().get_enode(rhs)->get_owner_id() << "\n";);
            theory_var new_v = expr2var(rhs);
            SASSERT(new_v != null_theory_var);
            new_lower    = alloc(derived_bound, new_v, inf_numeral(0), B_LOWER);
            new_upper    = alloc(derived_bound, new_v, inf_numeral(0), B_UPPER);
        }
        else {
            // One of the x_i variables is zero,
            // or all of them are assigned.

            // Assert the equality
            // (= (* x_1 ... x_n) k)
            TRACE("non_linear", tout << "all variables are fixed, and bound is: " << k << "\n";);
            new_lower    = alloc(derived_bound, v, inf_numeral(k), B_LOWER);
            new_upper    = alloc(derived_bound, v, inf_numeral(k), B_UPPER);
        }
        SASSERT(new_lower != 0);
        SASSERT(new_upper != 0);
        m_bounds_to_delete.push_back(new_lower);
        m_asserted_bounds.push_back(new_lower);
        m_bounds_to_delete.push_back(new_upper);
        m_asserted_bounds.push_back(new_upper);

        // Add the justification for new_lower and new_upper.
        // The justification is the lower and upper bounds of all fixed variables.
        m_tmp_lit_set.reset();
        m_tmp_eq_set.reset();

        SASSERT(is_pure_monomial(m));
        bool found_zero = false;
        for (unsigned i = 0; !found_zero && i < to_app(m)->get_num_args(); i++) {
            expr * arg = to_app(m)->get_arg(i);
            theory_var _var = expr2var(arg);
            if (is_fixed(_var)) {
                bound * l  = lower(_var);
                bound * u  = upper(_var);
                if (l->get_value().is_zero()) {
                    /* if zero was found, then it is the explanation */
                    SASSERT(k.is_zero());
                    found_zero = true;
                    m_tmp_lit_set.reset();
                    m_tmp_eq_set.reset();
                    new_lower->m_lits.reset();
                    new_lower->m_eqs.reset();
                }
                accumulate_justification(*l, *new_lower, numeral::zero(), m_tmp_lit_set, m_tmp_eq_set);

                TRACE("non_linear", 
                      for (literal l : new_lower->m_lits) {
                          ctx.display_detailed_literal(tout, l) << " ";
                      }
                      tout << "\n";);

                accumulate_justification(*u, *new_lower, numeral::zero(), m_tmp_lit_set, m_tmp_eq_set);

                TRACE("non_linear",
                      for (literal l : new_lower->m_lits) {
                          ctx.display_detailed_literal(tout, l) << " ";
                      }
                      tout << "\n";);

            }
        }
        new_upper->m_lits.append(new_lower->m_lits);
        new_upper->m_eqs.append(new_lower->m_eqs);

        TRACE("non_linear",
              new_lower->display(*this, tout << "lower: "); tout << "\n";
              new_upper->display(*this, tout << "upper: "); tout << "\n";
              for (literal lit : new_upper->m_lits) {
                  ctx.display_detailed_literal(tout, lit) << " ";
              }
              tout << "\n";);

        return true;
    }

    /**
       \brief Traverse all non linear monomials, and check the ones that became
       linear and propagate. Return true if propagated.
    */
    template<typename Ext>
    bool theory_arith<Ext>::propagate_linear_monomials() {
        TRACE("non_linear", tout << "propagating linear monomials...\n";);
        bool p = false;
        // CMW: m_nl_monomials is sometimes modified while executing
        // propagate_linear_monomial(...), invalidating the iterator `it'.
        // (Via the relevancy propagation that internalizes a new axiom
        // in mk_div_axiom and possibly others.) I'm replacing the iterator
        // with an index `i'.

        // Was previously:
        // svector<theory_var>::const_iterator it  = m_nl_monomials.begin();
        // svector<theory_var>::const_iterator end = m_nl_monomials.end();
        // for (; it != end; ++it) {
        //     theory_var v = *it;
        for (unsigned i = 0; i < m_nl_monomials.size(); i++) {
            theory_var v = m_nl_monomials[i];
            if (propagate_linear_monomial(v))
                p = true;
        }
        CTRACE("non_linear", p, display(tout););
        return p;
    }

    /*
      Interval arithmetic does not satisfy distributivity.
      Actually, it satisfies the sub-distributivity property:

      x*(y + z) \subseteq x*y + x*z

      The sub-distributivity property only holds if condensation
      is not used. For example:

      x * (x^3 + 1) \subseteq x*x^3 + x,

      but it is not the case that

      x * (x^3 + 1) \subseteq x^4 + x

      for example, for x = [-2,1]

      x*(x^3+1) = [-7, 14]
      x^4 + x   = [-2, 17]

      This weakness of AI is known as the "dependency problem",
      which comes from the decorrelation of the multiple occurrences
      of one variable during interval evaluation.

      Given a polynomial:
      p(x) = a_0 + a_1 * x + ... + a_n * x^n
      The horner extension is:
      h_p(x) = a_0 + x*(a_1 + ... + x*(a_{n-1} + a_n * x) + ...)

      The horner extension of p(x) = x^4 + x^3 + 2*x is:
      h_p(x) = x(2 + x^3(1 + x))

      The horner extension evaluates tighter intervals when
      condensation is not used.

      Remark: there is no guarantee that horner extension will
      provide a tighter interval than a sum of monomials when
      condensation is used.

      For multivariate polynomials nested (or cross nested) forms
      are used. The idea is to select one variable, and pretend the
      other are parameters. The horner form is computed for the selected
      variable, and the computation continues for the polynomials on the
      parameters.

      As described above, the horner form is not optimal with respect to
      to condensation. I use the following two properties to deal with
      monovariate polynomials with two monomials:

      p(x) = a*x^n + b*x^{n+m}  for n >= m
      is equivalent to

      b*x^{n-m}*[(x^{m} + a/(2b))^2 - (a/2b)^2]

      This polynomial provides tight bound when n and m have the same parity and:
        1) a*b > 0 and (lower(x) >= 0 or upper(x)^m <= -a/b)
        2) a*b < 0 and (upper(x) <= 0 or lower(x)^m >=  a/b)

      This polynomial also provides tight bounds when n = m,
      and the polynomial is simplified to, and n and m may have arbitrary parities:

      b*[(x^{n} + a/(2b))^2 - (a/2b)^2]

      Example:
      x > 1
      x^2 - x <= 0
      is unsatisfiable

      If we compute the bounds for x^2 - x we obtain
      (-oo, oo).

      On the other hand, if we compute the bounds for
      (x - 1/2)^2 - 1/4
      we obtain the bounds (0, oo), and the inconsistency
      is detected.

      Remark: In Z3, I condensate multiple occurrences of a variable
      when evaluating monomials.  So, the interval for a monomial is
      always tight.

      Remark: M1*(M2 + M3) is more precise than M1 * M2 + M1 * M3,
      if intersection(Vars(M1), union(Vars(M2), Vars(M3))) = empty-set,

      Remark: A trivial consequence of Moore's theorem for interval
      arithmetic.  If two monomials M1 and M2 do not share variables,
      then the interval for M1 + M2 is tight.
    */

    /**
       \brief Check whether the same variable occurs in two different monomials.

       \remark Fixed variables are ignored.

       \remark A trivial consequence of Moore's theorem for interval
       arithmetic.  If two monomials M1 and M2 do not share variables,
       then the interval for M1 + M2 is tight.
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_problematic_non_linear_row(row const & r) {
        m_tmp_var_set.reset();
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                theory_var v = it->m_var;
                if (is_fixed(v))
                    continue;
                if (is_pure_monomial(v)) {
                    expr * m = var2expr(v);
                    for (expr* arg : *to_app(m)) {
                        theory_var curr = expr2var(arg);
                        if (m_tmp_var_set.contains(curr))
                            return true;
                    }
                    SASSERT(m == var2expr(v));
                    for (expr* arg : *to_app(m)) {
                        theory_var curr = expr2var(arg);
                        if (!is_fixed(curr))
                            m_tmp_var_set.insert(curr);
                    }
                }
                else {
                    if (m_tmp_var_set.contains(v))
                        return true;
                    SASSERT(!is_fixed(v));
                    m_tmp_var_set.insert(v);
                }
            }
        }
        return false;
    }

    /**
       \brief Return true if the row mixes real and integer variables.
       This kind of row cannot be converted back to an expression, since
       expressions in Z3 cannot have mixed sorts.
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_mixed_real_integer(row const & r) const {
        bool found_int  = false;
        bool found_real = false;
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (it->is_dead())
                continue;
            theory_var v = it->m_var;
            // TODO: possible improvement... ignore fixed variables.
            // If we implement this improvement, we are actually changing the contract of this function
            // and we will also have to fix the affected functions.
            if (is_int(v))
                found_int = true;
            if (is_real(v))
                found_real = true;
            if (found_int && found_real)
                return true;
        }
        return false;
    }

    /**
       \brief Return true if the row contains only integer variables.
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_integer(row const & r) const {
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (it->is_dead())
                continue;
            theory_var v = it->m_var;
            // TODO: possible improvement... ignore fixed variables.
            if (!is_int(v))
                return false;
        }
        return true;
    }

    template<typename Ext>
    void theory_arith<Ext>::display_coeff_exprs(std::ostream & out, sbuffer<coeff_expr> const & p) const {
        typename sbuffer<coeff_expr>::const_iterator it  = p.begin();
        typename sbuffer<coeff_expr>::const_iterator end = p.end();
        for (bool first = true; it != end; ++it) {
            if (first)
                first = false;
            else
                out << "+\n";
            out << it->first << " * " << mk_pp(it->second, get_manager()) << "\n";
        }
    }

    /**
       \brief Traverse p and store in vars the (non-fixed) variables
       that occur in more than one monomial.  The number of
       occurrences is also stored.
     */
    template<typename Ext>
    void theory_arith<Ext>::get_polynomial_info(sbuffer<coeff_expr> const & p, sbuffer<var_num_occs> & varinfo) {
        context & ctx = get_context();
        varinfo.reset();
        m_var2num_occs.reset();

#define ADD_OCC(VAR) if (has_var(VAR) && !is_fixed(expr2var(VAR))) {                                    \
            TRACE("nl_info", tout << "adding occ: " << mk_bounded_pp(VAR, get_manager()) << "\n";);     \
            unsigned occs = 0;                                                                          \
            m_var2num_occs.find(VAR, occs);                                                             \
            occs++;                                                                                     \
            m_var2num_occs.insert(VAR, occs);                                                           \
        }

        for (coeff_expr const& kv : p) {
            expr * m = kv.second;
            if (is_pure_monomial(m)) {
                unsigned num_vars = get_num_vars_in_monomial(m);
                for (unsigned i = 0; i < num_vars; i++) {
                    var_power_pair p = get_var_and_degree(m, i);
                    ADD_OCC(p.first);
                }
            }
            else if (m_util.is_numeral(m)) {
                continue;
            }
            else if (ctx.e_internalized(m)) {
                ADD_OCC(m);
            }
            else {
                ctx.internalize(m, false);
                ADD_OCC(m);
            }
        }

        // Update the number of occurrences in the result vector.
        for (auto const& vn : m_var2num_occs) {
            if (vn.m_value > 1)
                varinfo.push_back(var_num_occs(vn.m_key, vn.m_value));
        }
    }

    /**
       \brief Convert p into an expression.
    */
    template<typename Ext>
    expr * theory_arith<Ext>::p2expr(sbuffer<coeff_expr> & p) {
        SASSERT(!p.empty());
        ptr_buffer<expr> args;
        for (coeff_expr const& ce : p) {
            rational const & c = ce.first;
            expr * var         = ce.second;
            if (!c.is_one()) {
                rational c2;
                expr * m = nullptr;
                if (m_util.is_numeral(var, c2))
                    m = m_util.mk_numeral(c*c2, m_util.is_int(var) && c.is_int() && c2.is_int());
                else
                    m = m_util.mk_mul(m_util.mk_numeral(c, c.is_int() && m_util.is_int(var)), var);
                m_nl_new_exprs.push_back(m);
                args.push_back(m);
            }
            else {
                args.push_back(var);
            }
        }
        SASSERT(!args.empty());
        expr * r = mk_nary_add(args.size(), args.c_ptr());
        m_nl_new_exprs.push_back(r);
        TRACE("p2expr_bug", display_coeff_exprs(tout, p); tout << mk_pp(r, get_manager()) << "\n";);
        return r;
    }

    /**
       \brief Return expression representing: var^power
     */
    template<typename Ext>
    expr * theory_arith<Ext>::power(expr * var, unsigned power) {
        SASSERT(power > 0);
        expr * r = var;
        for (unsigned i = 1; i < power; i++)
            r = m_util.mk_mul(var, r);
        m_nl_new_exprs.push_back(r);
        return r;
    }

    /**
       \brief Return true if var only occurs in two monovariate monomials,
       and return its power and coefficients and these monomials.
       The arguments i1 and i2 contain the position in p of the two monomials.
    */
    template<typename Ext>
    bool theory_arith<Ext>::in_monovariate_monomials(sbuffer<coeff_expr> & p, expr * var,
                                                     unsigned & i1, rational & c1, unsigned & n1, unsigned & i2, rational & c2, unsigned & n2) {
        int idx = 0;
#define SET_RESULT(POWER) {                     \
            if (idx == 0) {                     \
                c1 = it->first;                 \
                n1 = POWER;                     \
                idx = 1;                        \
                i1  = i;                        \
            }                                   \
            else if (idx == 1) {                \
                c2 = it->first;                 \
                n2 = POWER;                     \
                idx = 2;                        \
                i2  = i;                        \
            }                                   \
            else                                \
                return false;                   \
        }

        typename sbuffer<coeff_expr>::const_iterator it  = p.begin();
        typename sbuffer<coeff_expr>::const_iterator end = p.end();
        for (unsigned i = 0; it != end; ++it, ++i) {
            expr * m = it->second;
            if (is_pure_monomial(m)) {
                unsigned num_vars = get_num_vars_in_monomial(m);
                for (unsigned j = 0; j < num_vars; j++) {
                    var_power_pair p = get_var_and_degree(m, j);
                    if (p.first == var) {
                        if (num_vars > 1)
                            return false;
                        SET_RESULT(p.second);
                    }
                }
            }
            else if (m == var) {
                SET_RESULT(1);
            }
        }
        if (idx != 2)
            return false;
        return true;
    }

    /**
       \brief Display a nested form expression
    */
    template<typename Ext>
    void theory_arith<Ext>::display_nested_form(std::ostream & out, expr * p) {
        if (has_var(p)) {
            out << "#" << p->get_id();
        }
        else if (m_util.is_add(p)) {
            SASSERT(!has_var(p));
            out << "(";
            for (unsigned i = 0; i < to_app(p)->get_num_args(); i++) {
                if (i > 0) out << " + ";
                display_nested_form(out, to_app(p)->get_arg(i));
            }
            out << ")";
        }
        else if (m_util.is_mul(p)) {
            rational c = get_monomial_coeff(p);
            bool first = true;
            if (!c.is_one()) {
                out << c;
                first = false;
            }
            unsigned num_vars = get_num_vars_in_monomial(p);
            for (unsigned i = 0; i < num_vars; i++) {
                if (first) first = false; else out << "*";
                var_power_pair pair = get_var_and_degree(p, i);
                expr * var          = pair.first;
                unsigned power      = pair.second;
                display_nested_form(out, var);
                if (power != 1)
                    out << "^" << power;
            }
        }
        else {
            rational val;
            if (m_util.is_numeral(p, val))
                out << val;
            else
                out << "[unknown #" << p->get_id() << "]";
        }
    }

    /**
       \brief Return the degree of var in m.
    */
    template<typename Ext>
    unsigned theory_arith<Ext>::get_degree_of(expr * m, expr * var) {
        if (m == var)
            return 1;
        if (is_pure_monomial(m)) {
            unsigned num_vars = get_num_vars_in_monomial(m);
            for (unsigned i = 0; i < num_vars; i++) {
                var_power_pair p = get_var_and_degree(m, i);
                if (p.first == var)
                    return p.second;
            }
        }
        return 0;
    }

    /**
       \brief Return the minimal degree of var in the polynomial p.
     */
    template<typename Ext>
    unsigned theory_arith<Ext>::get_min_degree(sbuffer<coeff_expr> & p, expr * var) {
        SASSERT(!p.empty());
        SASSERT(var != 0);
        // get monomial where the degree of var is min.
        unsigned d = UINT_MAX; // min. degree of var
        sbuffer<coeff_expr>::const_iterator it  = p.begin();
        sbuffer<coeff_expr>::const_iterator end = p.end();
        for (; it != end; ++it) {
            expr * m = it->second;
            d = std::min(d, get_degree_of(m, var));
            if (d == 0)
                return d;
        }
        SASSERT(d != UINT_MAX);
        return d;
    }

    /**
       \brief Divide m by var^d.
    */
    template<typename Ext>
    expr * theory_arith<Ext>::factor(expr * m, expr * var, unsigned d) {
        TRACE("factor", tout << "m: " << mk_pp(m, get_manager()) << "\nvar: " << mk_pp(var, get_manager()) << "\nd: " << d << "\n";);
        if (d == 0)
            return m;
        if (m == var) {
            SASSERT(d == 1);
            expr * result = m_util.mk_numeral(rational(1), m_util.is_int(var));
            m_nl_new_exprs.push_back(result);
            return result;
        }
        SASSERT(is_pure_monomial(m));
        unsigned idx = 0;
        ptr_buffer<expr> new_args;
        for (expr * arg : *to_app(m)) {
            if (arg == var) {
                if (idx < d)
                    idx++;
                else
                    new_args.push_back(arg);
            }
            else {
                new_args.push_back(arg);
            }
        }
        SASSERT(idx == d);
        TRACE("factor_bug", tout << "new_args:\n"; for(unsigned i = 0; i < new_args.size(); i++) tout << mk_pp(new_args[i], get_manager()) << "\n";);
        expr * result = mk_nary_mul(new_args.size(), new_args.c_ptr(), m_util.is_int(var));
        m_nl_new_exprs.push_back(result);
        TRACE("factor", tout << "result: " << mk_pp(result, get_manager()) << "\n";);
        return result;
    }

    /**
       \brief Return the horner extension of p with respect to var.
    */
    template<typename Ext>
    expr * theory_arith<Ext>::horner(sbuffer<coeff_expr> & p, expr * var) {
        SASSERT(!p.empty());
        SASSERT(var != 0);
        unsigned d = get_min_degree(p, var);
        TRACE("horner_bug", tout << "poly:\n";
              for (unsigned i = 0; i < p.size(); i++) { if (i > 0) tout << " + "; tout << p[i].first << "*" << mk_pp(p[i].second, get_manager()); } tout << "\n";
              tout << "var: " << mk_pp(var, get_manager()) << "\n";
              tout << "min_degree: " << d << "\n";);
        sbuffer<coeff_expr> e; // monomials/x^d where var occurs with degree d
        sbuffer<coeff_expr> r; // rest
        for (auto const& kv : p) {
            expr * m = kv.second;
            expr * f = factor(m, var, d);
            if (get_degree_of(m, var) == d) {
                e.push_back(coeff_expr(kv.first, f));
            }
            else {
                SASSERT(get_degree_of(m, var) > d);
                r.push_back(coeff_expr(kv.first, f));
            }
        }

        expr * s = cross_nested(e, nullptr);
        if (!r.empty()) {
            expr * q = horner(r, var);
            // TODO: improve here
            s = m_util.mk_add(q, s);
        }

        expr * result = s;
        if (d != 0) {
            expr * xd = power(var, d);
            result = m_util.mk_mul(xd, s);
        }
        m_nl_new_exprs.push_back(result);
        return result;
    }

    /**
       \brief Convert the polynomial p into an equivalent cross nested
       expression.  The idea is to obtain an expression e where
       evaluate_as_interval(e) is more precise than
       evaluate_as_interval(p).

       If var != 0, then it is used for performing the horner extension
    */
    template<typename Ext>
    expr * theory_arith<Ext>::cross_nested(sbuffer<coeff_expr> & p, expr * var) {
        TRACE("non_linear", tout << "p.size: " << p.size() << "\n";);
        if (var == nullptr) {
            sbuffer<var_num_occs> varinfo;
            get_polynomial_info(p, varinfo);
            if (varinfo.empty())
                return p2expr(p);
            sbuffer<var_num_occs>::const_iterator it  = varinfo.begin();
            sbuffer<var_num_occs>::const_iterator end = varinfo.end();
            var          = it->first;
            unsigned max = it->second;
            ++it;
            for (; it != end; ++it) {
                if (it->second > max) {
                    var = it->first;
                    max = it->second;
                }
            }
        }
        SASSERT(var != 0);
        unsigned i1 = UINT_MAX;
        unsigned i2 = UINT_MAX;
        rational a, b;
        unsigned n  = UINT_MAX;
        unsigned nm = UINT_MAX;
        if (in_monovariate_monomials(p, var, i1, a, n, i2, b, nm) && n != nm) {
            CTRACE("in_monovariate_monomials", n == nm,
                   for (unsigned i = 0; i < p.size(); i++) {
                       if (i > 0) tout << " + "; tout << p[i].first << "*" << mk_pp(p[i].second, get_manager());
                   }
                   tout << "\n";
                   tout << "var: " << mk_pp(var, get_manager()) << "\n";
                   tout << "i1: "  << i1 << "\n";
                   tout << "a: "   << a << "\n";
                   tout << "n: "   << n << "\n";
                   tout << "i2: "  << i2 << "\n";
                   tout << "b: "   << b << "\n";
                   tout << "nm: "  << nm << "\n";);
            SASSERT(n != nm);
            expr * new_expr = nullptr;
            if (nm < n) {
                std::swap(n, nm);
                std::swap(a, b);
            }
            SASSERT(nm > n);
            unsigned m = nm - n;
            if (n % 2 == m % 2 && n >= m) {
                // b*x^{n-m}*[(x^{m} + a/(2b))^2 - (a/2b)^2]
                // b*[(x^{m} + a/(2b))^2 - (a/2b)^2]  for n == m
                rational a2b   = a;
                expr * xm      = power(var, m);
                a2b /= (rational(2) * b);
                // we cannot create a numeral that has sort int, but it is a rational.
                if (!m_util.is_int(var) || a2b.is_int()) {
                    rational ma2b2 = a2b * a2b;
                    ma2b2.neg();
                    expr * xm_a2b  = m_util.mk_add(m_util.mk_numeral(a2b, m_util.is_int(var)), xm);
                    expr * xm_a2b2 = m_util.mk_mul(xm_a2b, xm_a2b);
                    expr * rhs     = m_util.mk_add(xm_a2b2, m_util.mk_numeral(ma2b2, m_util.is_int(var)));
                    expr * rhs2    = nullptr;
                    if (n > m)
                        rhs2       = m_util.mk_mul(power(var, n - m), rhs);
                    else
                        rhs2       = rhs;
                    new_expr       = b.is_one() ? rhs2 : m_util.mk_mul(m_util.mk_numeral(b, m_util.is_int(var)), rhs2);
                    m_nl_new_exprs.push_back(new_expr);
                    TRACE("non_linear", tout << "new_expr:\n"; display_nested_form(tout, new_expr); tout << "\n";);
                    sbuffer<coeff_expr> rest;
                    unsigned sz    = p.size();
                    for (unsigned i = 0; i < sz; i++) {
                        if (i != i1 && i != i2)
                            rest.push_back(p[i]);
                    }
                    if (rest.empty())
                        return new_expr;
                    TRACE("non_linear", tout << "rest size: " << rest.size() << ", i1: " << i1 << ", i2: " << i2 << "\n";);
                    expr * h = cross_nested(rest, nullptr);
                    expr * r = m_util.mk_add(new_expr, h);
                    m_nl_new_exprs.push_back(r);
                    return r;
                }
            }
        }
        return horner(p, var);
    }

    /**
       \brief Check whether the given polynomial is consistent with respect to the known
       bounds. The polynomial is converted into an equivalent cross nested form.
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_cross_nested_consistent(sbuffer<coeff_expr> & p) {
        sbuffer<var_num_occs> varinfo;
        get_polynomial_info(p, varinfo);
        if (varinfo.empty())
            return true;
        std::stable_sort(varinfo.begin(), varinfo.end(), var_num_occs_lt());
        TRACE("cross_nested", tout << "var num occs:\n";
              for (auto const& kv : varinfo) {
                  tout << mk_bounded_pp(kv.first, get_manager()) << " -> " << kv.second << "\n";
              });
        for (auto const& kv : varinfo) {
            m_nl_new_exprs.reset();
            expr * var  = kv.first;
            expr * cn   = cross_nested(p, var);
            // Remark: cn may not be well-sorted because, since a row may contain mixed integer/real monomials.
            // This is not really a problem, since evaluate_as_interval will work even if cn is not well-sorted.
            if (!cn)
                continue;
            TRACE("cross_nested", tout << "nested form for var:\n" << mk_ismt2_pp(var, get_manager()) << "\n";
                  display_nested_form(tout, cn); tout << "\n";
                  tout << "c:\n" << mk_ismt2_pp(cn, get_manager()) << "\n";);
            interval i  = evaluate_as_interval(cn);
            TRACE("cross_nested", tout << "interval: " << i << "\n";);
            v_dependency * d = nullptr;
            if (!i.minus_infinity() && (i.get_lower_value().is_pos() || (i.get_lower_value().is_zero() && i.is_lower_open())))
                d = i.get_lower_dependencies();
            else if (!i.plus_infinity() && (i.get_upper_value().is_neg() || (i.get_upper_value().is_zero() && i.is_upper_open())))
                d = i.get_upper_dependencies();
            if (d) {
                TRACE("cross_nested", tout << "nested form conflict: " << i << "\n";);
                set_conflict(d);
                return false;
            }
        }
        return true;
    }

    /**
       \brief Check whether the polynomial represented by the current row is
       consistent with respect to the known bound when converted into a
       equivalent cross nested form.
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_cross_nested_consistent(row const & r) {
        TRACE("cross_nested", tout << "is_cross_nested_consistent:\n"; display_row(tout, r, false););
        if (!is_problematic_non_linear_row(r))
            return true;

        TRACE("cross_nested", tout << "problematic...\n";);

        /*
          The method is_cross_nested converts rows back to expressions.
          The conversion back to expressions may create sort incorrect expressions.
          This is in some sense ok, since these expressions are temporary, but
          the sort incorrect expressions may generate assertion violations.

          Sort incorrect expressions may be created in the following cases:

          1) mixed real int rows.

          2) int rows that contain non integer coefficients.

          3) int rows that when converted to cross nested form use non integer coefficients.

          There are several ways to deal with this problem:

          a) Ignore the assertion violations. Disadvantage: it will prevent us from running Z3 in debug mode on some benchmarks.

          b) Remove the assertions. Disadvantage: these assertions helped us to find many important bugs in Z3

          c) Disable the assertions temporally. This sounds like a big HACK.

          d) Use a different data-structure to represent polynomials in cross-nested form. Disadvantage: code duplication, the data-structure
          is essentially identical to the ASTs we are using right now.

          e) Disable the test when we cannot create a well-sorted expression.
             I'm temporally using this solution.
             I implemented the following logic:
                1) (mixed real int) Disable the test. Most benchmarks do not contain mixed int real variables.
                2) (int coeffs) I multiply the row by a constant to force it to have only integer coefficients.
                3) (new non-int coeffs) This only happens in an optional step in the conversion. Now, for int rows, I only apply this optional step only if non-int coeffs are not created.
        */

        if (!get_manager().int_real_coercions() && is_mixed_real_integer(r))
            return true; // giving up... see comment above

        TRACE("cross_nested", tout << "checking problematic row...\n";);

        rational c = rational::one();
        if (is_integer(r))
            c      = r.get_denominators_lcm().to_rational();

        TRACE("non_linear", tout << "check problematic row:\n"; display_row(tout, r); display_row(tout, r, false););
        sbuffer<coeff_expr> p;
        for (row_entry const& re : r) {
            if (!re.is_dead())
                p.push_back(coeff_expr(re.m_coeff.to_rational() * c, var2expr(re.m_var)));
        }
        SASSERT(!p.empty());
        CTRACE("cross_nested_bug", !c.is_one(), tout << "c: " << c << "\n"; display_row(tout, r); tout << "---> p (coeffs, exprs):\n"; display_coeff_exprs(tout, p););
        return is_cross_nested_consistent(p);
    }

    /**
       \brief Check whether an inconsistency can be found using cross nested
       form in the non linear cluster.
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_cross_nested_consistent(svector<theory_var> const & nl_cluster) {
        for (theory_var v : nl_cluster) {
            if (!is_base(v))
                continue;
            m_stats.m_nl_cross_nested++;
            row const & r = m_rows[get_var_row(v)];
            if (!is_cross_nested_consistent(r))
                return false;
        }
        return true;
    }

#define FIXED          0
#define QUOTED_FIXED   1
#define BOUNDED        2
#define QUOTED_BOUNDED 3
#define NOT_FREE        4
#define QUOTED_NOT_FREE 5
#define FREE            6
#define QUOTED_FREE     7
#define MAX_DEFAULT_WEIGHT 7

    /**
       \brief Initialize variable order for grobner basis computation.
       Make:
       "quoted free vars" > "free vars" > "quoted variables with lower or upper bounds" >
       "variables with lower or upper bounds" > "quoted bounded variables" >
       "bounded variables" > "quoted fixed variables" > "fixed variables"
    */
    template<typename Ext>
    void theory_arith<Ext>::init_grobner_var_order(svector<theory_var> const & nl_cluster, grobner & gb) {
        // Initialize variable order
        for (theory_var v : nl_cluster) {
            expr * var = var2expr(v);

            if (is_fixed(v)) {
                gb.set_weight(var, is_pure_monomial(var) ? QUOTED_FIXED : FIXED);
            }
            else if (is_bounded(v)) {
                gb.set_weight(var, is_pure_monomial(var) ? QUOTED_BOUNDED : BOUNDED);
            }
            else if (lower(v) || upper(v)) {
                gb.set_weight(var, is_pure_monomial(var) ? QUOTED_NOT_FREE : NOT_FREE);
            }
            else {
                SASSERT(is_free(v));
                gb.set_weight(var, is_pure_monomial(var) ? QUOTED_FREE : FREE);
            }
        }
    }

    /**
       \brief Create a new monomial using the given coeff and m. Fixed
       variables in m are substituted by their values.  The arg dep is
       updated to store these dependencies. The set already_found is
       updated with the fixed variables in m.  A variable is only
       added to dep if it is not already in already_found.

       Return null if the monomial was simplified to 0.
    */
    template<typename Ext>
    grobner::monomial * theory_arith<Ext>::mk_gb_monomial(rational const & _coeff, expr * m, grobner & gb, v_dependency * & dep, var_set & already_found) {
        ptr_buffer<expr> vars;
        rational coeff = _coeff;
        rational r;
#undef PROC_VAR
#define PROC_VAR(VAR) {                                                 \
            if (m_util.is_numeral(VAR, r)) {                            \
                coeff *= r;                                             \
            }                                                           \
            else {                                                      \
                theory_var _var = expr2var(VAR);                        \
                if (is_fixed(_var)) {                                   \
                    if (!already_found.contains(_var)) {                \
                        already_found.insert(_var);                     \
                        dep = m_dep_manager.mk_join(dep, m_dep_manager.mk_join(m_dep_manager.mk_leaf(lower(_var)), m_dep_manager.mk_leaf(upper(_var)))); \
                    }                                                   \
                    coeff *= lower_bound(_var).get_rational().to_rational(); \
                }                                                       \
                else {                                                  \
                    vars.push_back(VAR);                                \
                }                                                       \
            }                                                           \
        }

        if (m_util.is_mul(m)) {
            coeff *= get_monomial_coeff(m);
            m      = get_monomial_body(m);
            if (m_util.is_mul(m)) {
                SASSERT(is_pure_monomial(m));
                for (unsigned i = 0; i < to_app(m)->get_num_args(); i++) {
                    expr * arg = to_app(m)->get_arg(i);
                    PROC_VAR(arg);
                }
            }
            else {
                PROC_VAR(m);
            }
        }
        else {
            PROC_VAR(m);
        }
        if (!coeff.is_zero())
            return gb.mk_monomial(coeff, vars.size(), vars.c_ptr());
        else
            return nullptr;
    }

    /**
       \brief Send the given row to the grobner basis object.
       All fixed variables are substituted before sending the row to gb.
    */
    template<typename Ext>
    void theory_arith<Ext>::add_row_to_gb(row const & r, grobner & gb) {
        TRACE("non_linear", tout << "adding row to gb\n"; display_row(tout, r););
        ptr_buffer<grobner::monomial> monomials;
        v_dependency * dep = nullptr;
        m_tmp_var_set.reset();
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                rational coeff            = it->m_coeff.to_rational();
                expr * m                  = var2expr(it->m_var);
                TRACE("non_linear", tout << "monomial: " << mk_pp(m, get_manager()) << "\n";);
                grobner::monomial * new_m = mk_gb_monomial(coeff, m, gb, dep, m_tmp_var_set);
                TRACE("non_linear", tout << "new monomial:\n"; if (new_m) gb.display_monomial(tout, *new_m); else tout << "null"; tout << "\n";);
                if (new_m)
                    monomials.push_back(new_m);
            }
        }
        gb.assert_eq_0(monomials.size(), monomials.c_ptr(), dep);
    }

    /**
       \brief v must be a pure monomial. That is, v = (quote (* x_1 ... x_n))
       Add the monomial (quote (* x_1 ... x_n)) = x_1 * ... * x_n.
       Fixed variables are substituted.
    */
    template<typename Ext>
    void theory_arith<Ext>::add_monomial_def_to_gb(theory_var v, grobner & gb) {
        ptr_buffer<grobner::monomial> monomials;
        v_dependency * dep = nullptr;
        m_tmp_var_set.reset();
        expr * m = var2expr(v);
        SASSERT(is_pure_monomial(m));
        grobner::monomial * new_m = mk_gb_monomial(rational(1), m, gb, dep, m_tmp_var_set);
        if (new_m)
            monomials.push_back(new_m);
        rational coeff(-1);
        if (is_fixed(v)) {
            dep = m_dep_manager.mk_join(dep, m_dep_manager.mk_join(m_dep_manager.mk_leaf(lower(v)), m_dep_manager.mk_leaf(upper(v))));
            coeff *= lower_bound(v).get_rational().to_rational();
            if (!coeff.is_zero())
                monomials.push_back(gb.mk_monomial(coeff, 0, nullptr));
        }
        else {
            monomials.push_back(gb.mk_monomial(coeff, 1, &m));
        }
        gb.assert_eq_0(monomials.size(), monomials.c_ptr(), dep);
    }

    /**
       Initialize grobner basis data structure using the non linear cluster.
       The GB is initialized using rows and non linear monomials.
    */
    template<typename Ext>
    void theory_arith<Ext>::init_grobner(svector<theory_var> const & nl_cluster, grobner & gb) {
        init_grobner_var_order(nl_cluster, gb);
        for (theory_var v : nl_cluster) {
            if (is_base(v)) {
                row const & r = m_rows[get_var_row(v)];
                add_row_to_gb(r, gb);
            }
            if (is_pure_monomial(v) && !m_data[v].m_nl_propagated && is_fixed(v)) {
                add_monomial_def_to_gb(v, gb);
            }
        }
    }

    /**
       \brief Return the interval for the given monomial
    */
    template<typename Ext>
    interval theory_arith<Ext>::mk_interval_for(grobner::monomial const * m) {
        interval r(m_dep_manager, rational(m->get_coeff()));
        expr * var     = nullptr;
        unsigned power = 0;
        unsigned num_vars = m->get_degree();
        for (unsigned i = 0; i < num_vars; i++) {
            expr * curr = m->get_var(i);
            if (var == nullptr) {
                var   = curr;
                power = 1;
            }
            else if (curr == var) {
                power++;
            }
            else {
                mul_bound_of(var, power, r);
                var   = curr;
                power = 1;
            }
        }
        if (var != nullptr)
            mul_bound_of(var, power, r);
        return r;
    }

    /**
       \brief Set a conflict using a dependency object.
    */
    template<typename Ext>
    void theory_arith<Ext>::set_conflict(v_dependency * d) {
        antecedents ante(*this);
        derived_bound  b(null_theory_var, inf_numeral(0), B_LOWER);
        dependency2new_bound(d, b);
        set_conflict(b, ante, "arith_nl");
        TRACE("non_linear", for (literal lit : b.m_lits) get_context().display_literal_verbose(tout, lit) << "\n"; tout << "\n";); 
    }

    /**
       \brief Return true if I.get_lower() <= - M_1 - ... - M_n <= I.get_upper() is inconsistent.
       Where M_i is monomials[i] and n = num_monomials.
       A conflict will also be set using the bounds of the variables occurring in the monomials M_i's.
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_inconsistent(interval const & I, unsigned num_monomials, grobner::monomial * const * monomials, v_dependency * dep) {
        interval r(I);
        for (unsigned i = 0; i < num_monomials; i++) {
            grobner::monomial const * m = monomials[i];
            r += mk_interval_for(m);
            if (r.minus_infinity() && r.plus_infinity())
                return false;
        }
        TRACE("non_linear_bug", tout << "is_inconsistent, r: " << r << "\n";);
        v_dependency * interval_deps = nullptr;
        bool conflict              = false;
        if (!r.minus_infinity() && (r.get_lower_value().is_pos() || (r.get_lower_value().is_zero() && r.is_lower_open()))) {
            interval_deps = r.get_lower_dependencies();
            conflict      = true;
            TRACE("non_linear_bug", tout << "is inconsistent, interval_deps: " << interval_deps << "\n";);
        }
        else if (!r.plus_infinity() && (r.get_upper_value().is_neg() || (r.get_upper_value().is_zero() && r.is_upper_open()))) {
            interval_deps = r.get_upper_dependencies();
            conflict      = true;
            TRACE("non_linear_bug", tout << "is inconsistent, interval_deps: " << interval_deps << "\n";);
        }
        // interval_deps cannot be used to check if a conflict was detected, since interval_deps may be 0 even when r does not contain 0
        if (conflict) {
            TRACE("non_linear", tout << "conflicting interval for = 0 equation: " << r << "\n";);
            set_conflict(m_dep_manager.mk_join(interval_deps, dep));
            return true;
        }
        return false;
    }

    /**
       \brief Return true if the equation is inconsistent,
       and sign a conflict.
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_inconsistent(grobner::equation const * eq, grobner & gb) {
        interval zero(m_dep_manager, rational(0));
        if (is_inconsistent(zero, eq->get_num_monomials(), eq->get_monomials(), eq->get_dependency())) {
            TRACE("non_linear", tout << "found conflict\n"; gb.display_equation(tout, *eq););
            return true;
        }
        return false;
    }

    /**
       \brief Return true if the given monomial c*M is squared.
       The square root of the c is stored in r.
    */
    bool is_perfect_square(grobner::monomial const * m, rational & r) {
        unsigned num_vars = m->get_degree();
        if (num_vars % 2 == 1)
            return false;
        if (!m->get_coeff().is_perfect_square(r))
            return false;
        expr * var     = nullptr;
        unsigned power = 0;
        for (unsigned i = 0; i < num_vars; i++) {
            expr * curr = m->get_var(i);
            if (var == nullptr) {
                var   = curr;
                power = 1;
            }
            else if (var == curr) {
                power++;
            }
            else {
                if (power % 2 == 1)
                    return false;
                var   = curr;
                power = 1;
            }
        }
        return power % 2 == 0;
    }

    /**
       \brief Return m1m2 is of the form (-2ab)*M1*M2
       assuming that
       m1_sq = a^2*M1*M1
       m2_sq = b^2*M2*M2
    */
    bool is_perfect_square(grobner::monomial const * m1_sq, rational const & a, grobner::monomial const * m2_sq, rational const & b, grobner::monomial const * m1m2) {
        DEBUG_CODE({
            rational a1;
            rational b1;
            SASSERT(is_perfect_square(m1_sq, a1) && a == a1 && is_perfect_square(m2_sq, b1) && b == b1);
        });
        if (m1m2->get_coeff().is_nonneg())
            return false;
        rational c(-2);
        c *= a;
        c *= b;
        if (m1m2->get_coeff() != c)
            return false;
        unsigned num1  = m1_sq->get_degree();
        unsigned num2  = m2_sq->get_degree();
        unsigned num12 = m1m2->get_degree();
        if (num1 + num2 != num12 * 2)
            return false;
        unsigned i1, i2, i12;
        i1 = i2 = i12 = 0;
        while (true) {
            expr * v1  = nullptr;
            expr * v2  = nullptr;
            expr * v12 = nullptr;
            if (i1 < num1)
                v1  = m1_sq->get_var(i1);
            if (i2 < num2)
                v2  = m2_sq->get_var(i2);
            if (i12 < num12)
                v12 = m1m2->get_var(i12);
            if (v1 == nullptr && v2 == nullptr && v12 == nullptr)
                return true;
            if (v12 == nullptr)
                return false;
            if (v1 == v12) {
                SASSERT(m1_sq->get_var(i1+1) == v1);
                i1  += 2;
                i12 ++;
            }
            else if (v2 == v12) {
                SASSERT(m2_sq->get_var(i2+1) == v2);
                i2  += 2;
                i12 ++;
            }
            else {
                return false;
            }
        }
    }

    /**
       \brief Return true if the equation is inconsistent. In this
       version, perfect squares are eliminated, and replaced with the
       interval [0, oo), if the interval associated with them is less
       precise than [0, oo).

       \remark I track only simple perfect squares of the form (M1 - M2)^2,
       where M1 and M2 are arbitrary monomials.
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_inconsistent2(grobner::equation const * eq, grobner & gb) {
        // TODO: a possible improvement: create a quotation for (M1 - M2)^2
        // instead of trying to find it in a specific equation.
        // This approach is more precise, but more expensive
        // since a new row must be created.
        buffer<interval> intervals;
        unsigned num = eq->get_num_monomials();
        for (unsigned i = 0; i < num; i++) {
            grobner::monomial const * m = eq->get_monomial(i);
            intervals.push_back(mk_interval_for(m));
        }
        sbuffer<bool> deleted;
        deleted.resize(num, false);
        ptr_buffer<grobner::monomial> monomials;
        // try to eliminate monomials that form perfect squares of the form (M1 - M2)^2
        for (unsigned i = 0; i < num; i++) {
            grobner::monomial const * m1 = eq->get_monomial(i);
            rational a;
            if (deleted[i])
                continue;
            if (!is_perfect_square(m1, a)) {
                monomials.push_back(const_cast<grobner::monomial*>(m1));
                continue;
            }
            TRACE("non_linear", tout << "found perfect square monomial m1: "; gb.display_monomial(tout, *m1); tout << "\n";);
            // try to find another perfect square
            unsigned j = i + 1;
            for (; j < num; j++) {
                if (deleted[j])
                    continue;
                grobner::monomial const * m2 = eq->get_monomial(j);
                rational b;
                if (!is_perfect_square(m2, b))
                    continue;
                TRACE("non_linear", tout << "found perfect square monomial m2: "; gb.display_monomial(tout, *m2); tout << "\n";);
                // try to find -2*root(m1)*root(m2)
                // This monomial must be smaller than m1, since m2 is smaller than m1.
                unsigned k = i + 1;
                for (; k < num; k++) {
                    if (deleted[k])
                        continue;
                    grobner::monomial const * m1m2 = eq->get_monomial(k);
                    if (!is_perfect_square(m1, a, m2, b, m1m2))
                        continue;
                    // m1, m2, and m1m2 form a perfect square.
                    // check if [0, oo) provides a better lowerbound than adding the intervals of m1, m2 and m1m2;
                    TRACE("non_linear", tout << "found perfect square (M1-M2)^2:\n";
                          gb.display_monomial(tout, *m1); tout << "\n";
                          gb.display_monomial(tout, *m2); tout << "\n";
                          gb.display_monomial(tout, *m1m2); tout << "\n";);
                    interval I = intervals[i];
                    I         += intervals[j];
                    I         += intervals[k];
                    if (I.minus_infinity() || I.get_lower_value().is_neg()) {
                        TRACE("non_linear", tout << "the lower bound improved when perfect square is eliminated.\n";);
                        // Found improvement...
                        // mark these monomials as deleted
                        deleted[i] = true;
                        deleted[j] = true;
                        deleted[k] = true;
                        break;
                    }
                }
                if (k < num)
                    break; // found perfect square
            }
            if (j == num) {
                // didn't find perfect square of the form (M1-M2)^2
                monomials.push_back(const_cast<grobner::monomial*>(m1));
            }
        }
        if (monomials.size() == num)
            return false; // didn't find any perfect square.
        interval ge_zero(m_dep_manager, rational(0), false, true, nullptr);
        if (is_inconsistent(ge_zero, monomials.size(), monomials.c_ptr(), eq->get_dependency())) {
            TRACE("non_linear", tout << "found conflict\n"; gb.display_equation(tout, *eq););
            return true;
        }
        return false;
    }

    template<typename Ext>
    expr * theory_arith<Ext>::monomial2expr(grobner::monomial const * m, bool is_int) {
        unsigned num_vars = m->get_degree();
        ptr_buffer<expr> args;
        if (!m->get_coeff().is_one())
            args.push_back(m_util.mk_numeral(m->get_coeff(), is_int));
        for (unsigned j = 0; j < num_vars; j++)
            args.push_back(m->get_var(j));
        return mk_nary_mul(args.size(), args.c_ptr(), is_int);
    }

    /**
       \brief Assert the new equation in the simplex tableau.
    */
    template<typename Ext>
    bool theory_arith<Ext>::internalize_gb_eq(grobner::equation const * eq) {
        bool is_int = false;
        unsigned num_monomials = eq->get_num_monomials();
        for (unsigned i = 0; i < num_monomials; i++) {
            grobner::monomial const * m = eq->get_monomial(i);
            unsigned degree = m->get_degree();
            if (degree > m_params.m_nl_arith_max_degree)
                return false;
            if (degree > 0)
                is_int = m_util.is_int(m->get_var(0));
        }
        rational k;
        ptr_buffer<expr> args;
        for (unsigned i = 0; i < num_monomials; i++) {
            grobner::monomial const * m = eq->get_monomial(i);
            if (m->get_degree() == 0)
                k -= m->get_coeff();
            else
                args.push_back(monomial2expr(eq->get_monomial(i), is_int));
        }
        context & ctx   = get_context();
        th_rewriter& s = ctx.get_rewriter();
        expr_ref pol(get_manager());
        SASSERT(!args.empty());
        pol = mk_nary_add(args.size(), args.c_ptr());
        expr_ref s_pol(get_manager());
        proof_ref pr(get_manager());
        TRACE("gb_bug", tout << mk_ll_pp(pol, get_manager()) << "\n";);
        s(pol, s_pol, pr);
        if (!has_var(s_pol)) {
            TRACE("spol_bug", tout << "internalizing...\n" << mk_ll_pp(s_pol, get_manager()) << "\n";);
            ctx.internalize(s_pol, false);
            ctx.mark_as_relevant(s_pol.get());
        }
        SASSERT(has_var(s_pol.get()));
        // s_pol = k
        theory_var v = expr2var(s_pol);
        // v = k
        CTRACE("spol_bug", v == null_theory_var, tout << mk_ll_pp(s_pol, get_manager()) << "\n"; display(tout););
        SASSERT(v != null_theory_var);
        // assert bounds for s_pol
        mk_derived_nl_bound(v, inf_numeral(k), B_LOWER, eq->get_dependency());
        mk_derived_nl_bound(v, inf_numeral(k), B_UPPER, eq->get_dependency());
        TRACE("non_linear", tout << "inserted new equation into the tableau\n"; display_var(tout, v););
        return true;
    }

    /**
       \brief Compute Grobner basis, return true if a conflict or new fixed variables were detected.
    */
    template<typename Ext>
    typename theory_arith<Ext>::gb_result theory_arith<Ext>::compute_grobner(svector<theory_var> const & nl_cluster) {
        if (m_nl_gb_exhausted)
            return GB_FAIL;
        grobner gb(get_manager(), m_dep_manager);
        init_grobner(nl_cluster, gb);
        TRACE("non_linear", display(tout););
        bool warn            = false;
        unsigned next_weight = MAX_DEFAULT_WEIGHT + 1; // next weight using during perturbation phase.
        ptr_vector<grobner::equation> eqs;

        while (true) {
            TRACE("non_linear_gb", tout << "before:\n"; gb.display(tout););
            bool r = false;
            gb.compute_basis_init();
            while (!r && gb.get_num_new_equations() < m_params.m_nl_arith_gb_threshold) {
                if (get_context().get_cancel_flag()) {
                    warn = true;
                    break;
                }
                r = gb.compute_basis_step();
            }
            m_stats.m_gb_simplify      += gb.m_stats.m_simplify;
            m_stats.m_gb_superpose     += gb.m_stats.m_superpose;
            m_stats.m_gb_num_processed += gb.m_stats.m_num_processed;
            m_stats.m_gb_compute_basis++;
            if (!r && !warn) {
                IF_VERBOSE(3, verbose_stream() << "Grobner basis computation interrupted. Increase threshold using NL_ARITH_GB_THRESHOLD=<limit>\n";);
                get_context().push_trail(value_trail<context, bool>(m_nl_gb_exhausted));
                m_nl_gb_exhausted = true;
                warn              = true;
            }
            if (get_context().get_cancel_flag()) {
                return GB_FAIL;
            }
            TRACE("non_linear_gb", tout << "after:\n"; gb.display(tout););
            // Scan the grobner basis eqs, and look for inconsistencies.
            eqs.reset();
            gb.get_equations(eqs);
            TRACE("grobner_bug", tout << "after gb\n";);
            for (grobner::equation* eq : eqs) {
                TRACE("grobner_bug", gb.display_equation(tout, *eq););
                if (is_inconsistent(eq, gb))
                    return GB_PROGRESS;
                if (is_inconsistent2(eq, gb))
                    return GB_PROGRESS;
            }
            // Scan the grobner basis eqs for equations of the form x - k = 0 or x = 0 is found, and x is not fixed,
            // then assert bounds for x, and continue
            gb_result result = GB_FAIL;
            if (m_params.m_nl_arith_gb_eqs) {
                for (grobner::equation* eq : eqs) {
                    if (!eq->is_linear_combination()) {
                        TRACE("non_linear", tout << "processing new equality:\n"; gb.display_equation(tout, *eq););
                        TRACE("non_linear_bug", tout << "processing new equality:\n"; gb.display_equation(tout, *eq););
                        if (internalize_gb_eq(eq))
                            result = GB_NEW_EQ;
                    }
                }
            }
            if (result != GB_FAIL)
                return result;
            if (!m_params.m_nl_arith_gb_perturbate)
                return result;
            if (m_nl_gb_exhausted)
                return result;
            // Try to change the variable order... in such a way the leading term is modified.
            // I only consider linear equations... (HACK)
            // Moreover, I do not change the weight of a variable more than once in this loop.
            bool modified = false;

            for (grobner::equation const* eq : eqs) {
                unsigned num_monomials = eq->get_num_monomials();
                CTRACE("grobner_bug", num_monomials <= 0, gb.display_equation(tout, *eq););
                if (num_monomials == 0)
                    continue; // HACK: the equation 0 = 0, should have been discarded by the GB module.
                if (eq->get_monomial(0)->get_degree() != 1)
                    continue;
                for (unsigned j = 1; j < num_monomials; j++) {
                    grobner::monomial const * m = eq->get_monomial(j);
                    if (m->get_degree() != 1)
                        continue;
                    expr * var = m->get_var(0);
                    if (gb.get_weight(var) > MAX_DEFAULT_WEIGHT)
                        continue; // variable was already updated
                    TRACE("non_linear", tout << "increased weight of: " << mk_bounded_pp(var, get_manager()) << "\n";);
                    gb.set_weight(var, next_weight);
                    next_weight++;
                    gb.update_order();
                    TRACE("non_linear", tout << "after updating order\n"; gb.display(tout););
                    modified = true;
                    break;
                }
                if (modified)
                    break;
            }
            if (!modified)
                return result;
        }
    }

    /**
       \brief Maximize/Minimize variables in non linear monomials.
    */
    template<typename Ext>
    bool theory_arith<Ext>::max_min_nl_vars() {
        var_set             already_found;
        svector<theory_var> vars;
        for (theory_var v : m_nl_monomials) {
            mark_var(v, vars, already_found);
            expr * n     = var2expr(v);
            SASSERT(is_pure_monomial(n));
            for (expr * curr : *to_app(n)) {
                theory_var v = expr2var(curr);
                SASSERT(v != null_theory_var);
                mark_var(v, vars, already_found);
            }
        }
        return max_min(vars);
    }

    /**
       \brief Process non linear constraints.
    */
    template<typename Ext>
    final_check_status theory_arith<Ext>::process_non_linear() {
        m_model_depends_on_computed_epsilon = false;
        if (m_nl_monomials.empty())
            return FC_DONE;

        if (check_monomial_assignments()) {
            return FC_DONE;
        }

        if (!m_params.m_nl_arith) {
            TRACE("non_linear", tout << "Non-linear is not enabled\n";);
            return FC_GIVEUP;
        }

        TRACE("process_non_linear", display(tout););

        if (m_nl_rounds > m_params.m_nl_arith_rounds) {
            TRACE("non_linear", tout << "GIVEUP non linear problem...\n";);
            IF_VERBOSE(3, verbose_stream() << "Max. non linear arithmetic rounds. Increase threshold using NL_ARITH_ROUNDS=<limit>\n";);
            return FC_GIVEUP;
        }

        get_context().push_trail(value_trail<context, unsigned>(m_nl_rounds));
        m_nl_rounds++;

        elim_quasi_base_rows();
        move_non_base_vars_to_bounds();
        TRACE("non_linear_verbose", tout << "processing non linear constraints...\n"; get_context().display(tout););
        if (!make_feasible()) {
            TRACE("non_linear", tout << "failed to move variables to bounds.\n";);
            failed();
            return FC_CONTINUE;
        }

        if (!max_min_nl_vars())
            return FC_CONTINUE;

        if (check_monomial_assignments()) {
            return m_liberal_final_check || !m_changed_assignment ? FC_DONE : FC_CONTINUE;
        }

        svector<theory_var> vars;
        get_non_linear_cluster(vars);

        bool progress;
        unsigned old_idx = m_nl_strategy_idx;
        get_context().push_trail(value_trail<context, unsigned>(m_nl_strategy_idx));

        do {
            progress = false;
            switch (m_nl_strategy_idx) {
            case 0:
                if (propagate_nl_bounds()) {
                    propagate_core();
                    progress = true;
                }
                break;
            case 1:
                if (!is_cross_nested_consistent(vars))
                    progress = true;
                break;
            case 2:
                if (m_params.m_nl_arith_gb) {
                    switch(compute_grobner(vars)) {
                    case GB_PROGRESS:
                        progress = true;
                        break;
                    case GB_NEW_EQ:
                        progress = true;
                        propagate_core();
                        break;
                    case GB_FAIL:
                        break;
                    }
                }
                break;
            case 3:
                if (m_params.m_nl_arith_branching) {
                    theory_var target = find_nl_var_for_branching();
                    if (target != null_theory_var && branch_nl_int_var(target))
                        progress = true;
                }
                break;
            }

            m_nl_strategy_idx = (m_nl_strategy_idx + 1) % 4;
            if (progress)
                return FC_CONTINUE;
        }
        while (m_nl_strategy_idx != old_idx);

        if (check_monomial_assignments()) {
            return m_liberal_final_check || !m_changed_assignment ? FC_DONE : FC_CONTINUE;
        }

        TRACE("non_linear", display(tout););

        return FC_GIVEUP;
    }

};


#endif /* THEORY_ARITH_NL_H_ */

