/*++
  Module Name:

  theory_str_regex.cpp

  Abstract:

  Regular expression components for Z3str3 (theory_str).

  Author:

  Murphy Berzish (2019-10-25)

  Revision History:

  --*/

#include "smt/theory_str.h"

namespace smt {

    // saturating unsigned addition
    unsigned inline _qadd(unsigned a, unsigned b) {
        if (a == UINT_MAX || b == UINT_MAX) {
            return UINT_MAX;
        }
        unsigned result = a + b;
        if (result < a || result < b) {
            return UINT_MAX;
        }
        return result;
    }

    // saturating unsigned multiply
    unsigned inline _qmul(unsigned a, unsigned b) {
        if (a == UINT_MAX || b == UINT_MAX) {
            return UINT_MAX;
        }
        uint64_t result = static_cast<uint64_t>(a) * static_cast<uint64_t>(b);
        if (result > UINT_MAX) {
            return UINT_MAX;
        }
        return static_cast<unsigned>(result);
    }

    // Returns false if we need to give up solving, e.g. because we found symbolic expressions in an automaton.
    bool theory_str::solve_regex_automata() {
        for (auto str_in_re : regex_terms) {
            expr * str = nullptr;
            expr * re = nullptr;
            u.str.is_in_re(str_in_re, str, re);
            if (!ctx.b_internalized(str_in_re)) {
                TRACE("str", tout << "regex term " << mk_pp(str_in_re, m) << " not internalized; fixing and continuing" << std::endl;);
                ctx.internalize(str_in_re, false);
                finalCheckProgressIndicator = true;
                continue;
            }
            lbool current_assignment = ctx.get_assignment(str_in_re);
            TRACE("str", tout << "regex term: " << mk_pp(str, m) << " in " << mk_pp(re, m) << " : " << current_assignment << std::endl;);
            if (current_assignment == l_undef) {
                continue;
            }

            if (!regex_terms_with_length_constraints.contains(str_in_re)) {
                if (current_assignment == l_true && check_regex_length_linearity(re)) {
                    TRACE("str", tout << "regex length constraints expected to be linear -- generating and asserting them" << std::endl;);

                    if (regex_term_to_length_constraint.contains(str_in_re)) {
                        // use existing length constraint
                        expr * top_level_length_constraint = nullptr;
                        regex_term_to_length_constraint.find(str_in_re, top_level_length_constraint);

                        ptr_vector<expr> extra_length_vars;
                        regex_term_to_extra_length_vars.find(str_in_re, extra_length_vars);

                        assert_axiom(top_level_length_constraint);
                        for(auto v : extra_length_vars) {
                            refresh_theory_var(v);
                            expr_ref len_constraint(m_autil.mk_ge(v, m_autil.mk_numeral(rational::zero(), true)), m);
                            assert_axiom(len_constraint);
                        }
                    } else {
                        // generate new length constraint
                        expr_ref_vector extra_length_vars(m);
                        expr_ref _top_level_length_constraint = infer_all_regex_lengths(mk_strlen(str), re, extra_length_vars);
                        expr_ref premise(str_in_re, m);
                        expr_ref top_level_length_constraint(m.mk_implies(premise, _top_level_length_constraint), m);
                        th_rewriter rw(m);
                        rw(top_level_length_constraint);
                        TRACE("str", tout << "top-level length constraint: " << mk_pp(top_level_length_constraint, m) << std::endl;);
                        // assert and track length constraint
                        assert_axiom(top_level_length_constraint);
                        for(auto v : extra_length_vars) {
                            expr_ref len_constraint(m_autil.mk_ge(v, m_autil.mk_numeral(rational::zero(), true)), m);
                            assert_axiom(len_constraint);
                        }

                        regex_term_to_length_constraint.insert(str_in_re, top_level_length_constraint);
                        ptr_vector<expr> vtmp;
                        for(auto v : extra_length_vars) {
                            vtmp.push_back(v);
                        }
                        regex_term_to_extra_length_vars.insert(str_in_re, vtmp);
                    }

                    regex_terms_with_length_constraints.insert(str_in_re);
                    m_trail_stack.push(insert_obj_trail<expr>(regex_terms_with_length_constraints, str_in_re));
                }
            } // re not in regex_terms_with_length_constraints

            rational exact_length_value;
            if (get_len_value(str, exact_length_value)) {
                TRACE("str", tout << "exact length of " << mk_pp(str, m) << " is " << exact_length_value << std::endl;);

                if (regex_terms_with_path_constraints.contains(str_in_re)) {
                    TRACE("str", tout << "term " << mk_pp(str_in_re, m) << " already has path constraints set up" << std::endl;);
                    continue;
                }

                // find a consistent automaton for this term
                bool found = false;
                regex_automaton_under_assumptions assumption;
                if (regex_automaton_assumptions.contains(re) &&
                        !regex_automaton_assumptions[re].empty()){
                    for (auto autA : regex_automaton_assumptions[re]) {
                        rational assumed_upper_bound, assumed_lower_bound;
                        bool assumes_upper_bound = autA.get_upper_bound(assumed_upper_bound);
                        bool assumes_lower_bound = autA.get_lower_bound(assumed_lower_bound);
                        if (!assumes_upper_bound && !assumes_lower_bound) {
                            // automaton with no assumptions is always usable
                            assumption = autA;
                            found = true;
                            break;
                        }
                        // TODO check consistency of bounds assumptions
                    } // foreach(a in regex_automaton_assumptions)
                }
                if (found) {
                    if (exact_length_value.is_zero()) {
                        // check consistency of 0-length solution with automaton
                        eautomaton * aut = assumption.get_automaton();
                        bool zero_solution = false;
                        unsigned initial_state = aut->init();
                        if (aut->is_final_state(initial_state)) {
                            zero_solution = true;
                        } else {
                            unsigned_vector eps_states;
                            aut->get_epsilon_closure(initial_state, eps_states);
                            for (unsigned_vector::iterator it = eps_states.begin(); it != eps_states.end(); ++it) {
                                unsigned state = *it;
                                if (aut->is_final_state(state)) {
                                    zero_solution = true;
                                    break;
                                }
                            }
                        }

                        // now check polarity of automaton wrt. original term
                        if ( (current_assignment == l_true && !assumption.get_polarity())
                                || (current_assignment == l_false && assumption.get_polarity())) {
                            // invert sense
                            zero_solution = !zero_solution;
                        }

                        if (zero_solution) {
                            TRACE("str", tout << "zero-length solution OK -- asserting empty path constraint" << std::endl;);
                            expr_ref_vector lhs_terms(m);
                            if (current_assignment == l_true) {
                                lhs_terms.push_back(str_in_re);
                            } else {
                                lhs_terms.push_back(m.mk_not(str_in_re));
                            }
                            lhs_terms.push_back(ctx.mk_eq_atom(mk_strlen(str), m_autil.mk_numeral(exact_length_value, true)));
                            expr_ref lhs(mk_and(lhs_terms), m);
                            expr_ref rhs(ctx.mk_eq_atom(str, mk_string("")), m);
                            assert_implication(lhs, rhs);
                            regex_terms_with_path_constraints.insert(str_in_re);
                            m_trail_stack.push(insert_obj_trail<expr>(regex_terms_with_path_constraints, str_in_re));
                        } else {
                            TRACE("str", tout << "zero-length solution not admitted by this automaton -- asserting conflict clause" << std::endl;);
                            expr_ref_vector lhs_terms(m);
                            if (current_assignment == l_true) {
                                lhs_terms.push_back(str_in_re);
                            } else {
                                lhs_terms.push_back(m.mk_not(str_in_re));
                            }
                            lhs_terms.push_back(ctx.mk_eq_atom(mk_strlen(str), m_autil.mk_numeral(exact_length_value, true)));
                            expr_ref lhs(mk_and(lhs_terms), m);
                            expr_ref conflict(m.mk_not(lhs), m);
                            assert_axiom(conflict);
                        }
                        regex_inc_counter(regex_length_attempt_count, re);
                        continue;
                    } else {
                        // fixed-length model construction handles path constraints on our behalf, and with a better reduction
                        continue;
                    }
                } else {
                    // no automata available, or else all bounds assumptions are invalid
                    unsigned expected_complexity = estimate_regex_complexity(re);
                    if (expected_complexity <= m_params.m_RegexAutomata_DifficultyThreshold || regex_get_counter(regex_fail_count, str_in_re) >= m_params.m_RegexAutomata_FailedAutomatonThreshold) {
                        CTRACE("str", regex_get_counter(regex_fail_count, str_in_re) >= m_params.m_RegexAutomata_FailedAutomatonThreshold,
                                tout << "failed automaton threshold reached for " << mk_pp(str_in_re, m) << " -- automatically constructing full automaton" << std::endl;);
                        eautomaton * aut = m_mk_aut(re);
                        if (aut == nullptr) {
                            TRACE("str", tout << "ERROR: symbolic automaton construction failed, likely due to non-constant term in regex" << std::endl;);
                            return false;
                        }
                        aut->compress();
                        regex_automata.push_back(aut);
                        regex_automaton_under_assumptions new_aut(re, aut, true);
                        if (!regex_automaton_assumptions.contains(re)) {
                            regex_automaton_assumptions.insert(re, svector<regex_automaton_under_assumptions>());
                        }
                        regex_automaton_assumptions[re].push_back(new_aut);
                        TRACE("str", tout << "add new automaton for " << mk_pp(re, m) << ": no assumptions" << std::endl;);
                        find_automaton_initial_bounds(str_in_re, aut);
                    } else {
                        regex_inc_counter(regex_fail_count, str_in_re);
                    }
                    continue;
                }
            } // get_len_value()
            expr_ref str_len(mk_strlen(str), m);
            rational lower_bound_value;
            rational upper_bound_value;
            bool lower_bound_exists = lower_bound(str_len, lower_bound_value);
            bool upper_bound_exists = upper_bound(str_len, upper_bound_value);
            CTRACE("str", lower_bound_exists, tout << "lower bound of " << mk_pp(str, m) << " is " << lower_bound_value << std::endl;);
            CTRACE("str", upper_bound_exists, tout << "upper bound of " << mk_pp(str, m) << " is " << upper_bound_value << std::endl;);

            bool new_lower_bound_info = true;
            bool new_upper_bound_info = true;
            // check last seen lower/upper bound to avoid performing duplicate work
            if (regex_last_lower_bound.contains(str)) {
                rational last_lb_value;
                regex_last_lower_bound.find(str, last_lb_value);
                if (last_lb_value == lower_bound_value) {
                    new_lower_bound_info = false;
                }
            }
            if (regex_last_upper_bound.contains(str)) {
                rational last_ub_value;
                regex_last_upper_bound.find(str, last_ub_value);
                if (last_ub_value == upper_bound_value) {
                    new_upper_bound_info = false;
                }
            }

            if (new_lower_bound_info) {
                regex_last_lower_bound.insert(str, lower_bound_value);
            }
            if (new_upper_bound_info) {
                regex_last_upper_bound.insert(str, upper_bound_value);
            }

            if (upper_bound_exists && new_upper_bound_info) {
                // check current assumptions
                if (regex_automaton_assumptions.contains(re) &&
                        !regex_automaton_assumptions[re].empty()){
                    // one or more existing assumptions.
                    // see if the (current best) upper bound can be refined
                    // (note that if we have an automaton with no assumption,
                    // this automatically counts as best)
                    bool need_assumption = true;
                    regex_automaton_under_assumptions last_assumption;
                    rational last_ub = rational::minus_one();
                    for (auto autA : regex_automaton_assumptions[re]) {
                        if ((current_assignment == l_true && autA.get_polarity() == false)
                                || (current_assignment == l_false && autA.get_polarity() == true)) {
                            // automaton uses incorrect polarity
                            continue;
                        }
                        rational this_ub;
                        if (autA.get_upper_bound(this_ub)) {
                            if (last_ub == rational::minus_one() || this_ub < last_ub) {
                                last_ub = this_ub;
                                last_assumption = autA;
                            }
                        } else {
                            need_assumption = false;
                            last_assumption = autA;
                            break;
                        }
                    }
                    if (!last_ub.is_minus_one() || !need_assumption) {
                        CTRACE("str", !need_assumption, tout << "using automaton with full length information" << std::endl;);
                        CTRACE("str", need_assumption, tout << "using automaton with assumed upper bound of " << last_ub << std::endl;);

                        rational refined_upper_bound;
                        bool solution_at_upper_bound = refine_automaton_upper_bound(last_assumption.get_automaton(),
                                upper_bound_value, refined_upper_bound);
                        TRACE("str", tout << "refined upper bound is " << refined_upper_bound <<
                                (solution_at_upper_bound?", solution at upper bound":", no solution at upper bound") << std::endl;);

                        expr_ref_vector lhs(m);
                        if (current_assignment == l_false) {
                            lhs.push_back(m.mk_not(str_in_re));
                        } else {
                            lhs.push_back(str_in_re);
                        }
                        if (need_assumption) {
                            lhs.push_back(m_autil.mk_le(str_len, m_autil.mk_numeral(last_ub, true)));
                        }
                        lhs.push_back(m_autil.mk_le(str_len, m_autil.mk_numeral(upper_bound_value, true)));

                        expr_ref_vector rhs(m);

                        if (solution_at_upper_bound) {
                            if (refined_upper_bound.is_minus_one()) {
                                // If there are solutions at the upper bound but not below it, make the bound exact.
                                rhs.push_back(ctx.mk_eq_atom(str_len, m_autil.mk_numeral(upper_bound_value, true)));
                            } else {
                                // If there are solutions at and below the upper bound, add an additional bound.
                                rhs.push_back(m.mk_or(
                                        ctx.mk_eq_atom(str_len, m_autil.mk_numeral(upper_bound_value, true)),
                                        m_autil.mk_le(str_len, m_autil.mk_numeral(refined_upper_bound, true))
                                        ));
                            }
                        } else {
                            if (refined_upper_bound.is_minus_one()) {
                                // If there are no solutions at or below the upper bound, assert a conflict clause.
                                rhs.push_back(m.mk_not(m_autil.mk_le(str_len, m_autil.mk_numeral(upper_bound_value, true))));
                            } else {
                                // If there are solutions below the upper bound but not at it, refine the bound.
                                rhs.push_back(m_autil.mk_le(str_len, m_autil.mk_numeral(refined_upper_bound, true)));
                            }
                        }

                        if (!rhs.empty()) {
                            expr_ref lhs_terms(mk_and(lhs), m);
                            expr_ref rhs_terms(mk_and(rhs), m);
                            assert_implication(lhs_terms, rhs_terms);
                        }
                    }
                } else {
                    // no existing automata/assumptions.
                    // if it's easy to construct a full automaton for R, do so
                    unsigned expected_complexity = estimate_regex_complexity(re);
                    bool failureThresholdExceeded = (regex_get_counter(regex_fail_count, str_in_re) >= m_params.m_RegexAutomata_FailedAutomatonThreshold);
                    if (expected_complexity <= m_params.m_RegexAutomata_DifficultyThreshold || failureThresholdExceeded) {
                        eautomaton * aut = m_mk_aut(re);
                        if (aut == nullptr) {
                            TRACE("str", tout << "ERROR: symbolic automaton construction failed, likely due to non-constant term in regex" << std::endl;);
                            return false;
                        }
                        aut->compress();
                        regex_automata.push_back(aut);
                        regex_automaton_under_assumptions new_aut(re, aut, true);
                        if (!regex_automaton_assumptions.contains(re)) {
                            regex_automaton_assumptions.insert(re, svector<regex_automaton_under_assumptions>());
                        }
                        regex_automaton_assumptions[re].push_back(new_aut);
                        TRACE("str", tout << "add new automaton for " << mk_pp(re, m) << ": no assumptions" << std::endl;);
                        find_automaton_initial_bounds(str_in_re, aut);
                    } else {
                        regex_inc_counter(regex_fail_count, str_in_re);
                    }
                    continue;
                }
            } else { // !upper_bound_exists
                // no upper bound information
                if (lower_bound_exists && !lower_bound_value.is_zero() && new_lower_bound_info) {
                    // nonzero lower bound, no upper bound

                    // check current assumptions
                    if (regex_automaton_assumptions.contains(re) &&
                            !regex_automaton_assumptions[re].empty()){
                        // one or more existing assumptions.
                        // see if the (current best) lower bound can be refined
                        // (note that if we have an automaton with no assumption,
                        // this automatically counts as best)
                        bool need_assumption = true;
                        regex_automaton_under_assumptions last_assumption;
                        rational last_lb = rational::zero(); // the default
                        for (auto autA : regex_automaton_assumptions[re]) {
                            if ((current_assignment == l_true && autA.get_polarity() == false)
                                    || (current_assignment == l_false && autA.get_polarity() == true)) {
                                // automaton uses incorrect polarity
                                continue;
                            }
                            rational this_lb;
                            if (autA.get_lower_bound(this_lb)) {
                                if (this_lb > last_lb) {
                                    last_lb = this_lb;
                                    last_assumption = autA;
                                }
                            } else {
                                need_assumption = false;
                                last_assumption = autA;
                                break;
                            }
                        }
                        if (!last_lb.is_zero() || !need_assumption) {
                            CTRACE("str", !need_assumption, tout << "using automaton with full length information" << std::endl;);
                            CTRACE("str", need_assumption, tout << "using automaton with assumed lower bound of " << last_lb << std::endl;);
                            rational refined_lower_bound;
                            bool solution_at_lower_bound = refine_automaton_lower_bound(last_assumption.get_automaton(),
                                    lower_bound_value, refined_lower_bound);
                            TRACE("str", tout << "refined lower bound is " << refined_lower_bound <<
                                    (solution_at_lower_bound?", solution at lower bound":", no solution at lower bound") << std::endl;);

                            expr_ref_vector lhs(m);
                            if (current_assignment == l_false) {
                                lhs.push_back(m.mk_not(str_in_re));
                            } else {
                                lhs.push_back(str_in_re);
                            }
                            if (need_assumption) {
                                lhs.push_back(m_autil.mk_ge(str_len, m_autil.mk_numeral(last_lb, true)));
                            }
                            lhs.push_back(m_autil.mk_ge(str_len, m_autil.mk_numeral(lower_bound_value, true)));

                            expr_ref_vector rhs(m);

                            if (solution_at_lower_bound) {
                                if (refined_lower_bound.is_minus_one()) {
                                    // If there are solutions at the lower bound but not above it, make the bound exact.
                                    rhs.push_back(ctx.mk_eq_atom(str_len, m_autil.mk_numeral(lower_bound_value, true)));
                                } else {
                                    // If there are solutions at and above the lower bound, add an additional bound.
                                    // DISABLED as this is causing non-termination in the integer solver. --mtrberzi
                                    /*
                                    rhs.push_back(m.mk_or(
                                            ctx.mk_eq_atom(str_len, m_autil.mk_numeral(lower_bound_value, true)),
                                            m_autil.mk_ge(str_len, m_autil.mk_numeral(refined_lower_bound, true))
                                    ));
                                    */
                                }
                            } else {
                                if (refined_lower_bound.is_minus_one()) {
                                    // If there are no solutions at or above the lower bound, assert a conflict clause.
                                    rhs.push_back(m.mk_not(m_autil.mk_ge(str_len, m_autil.mk_numeral(lower_bound_value, true))));
                                } else {
                                    // If there are solutions above the lower bound but not at it, refine the bound.
                                    rhs.push_back(m_autil.mk_ge(str_len, m_autil.mk_numeral(refined_lower_bound, true)));
                                }
                            }

                            if (!rhs.empty()) {
                                expr_ref lhs_terms(mk_and(lhs), m);
                                expr_ref rhs_terms(mk_and(rhs), m);
                                assert_implication(lhs_terms, rhs_terms);
                            }
                        }
                    } else {
                        // no existing automata/assumptions.
                        // if it's easy to construct a full automaton for R, do so
                        unsigned expected_complexity = estimate_regex_complexity(re);
                        bool failureThresholdExceeded = (regex_get_counter(regex_fail_count, str_in_re) >= m_params.m_RegexAutomata_FailedAutomatonThreshold);
                        if (expected_complexity <= m_params.m_RegexAutomata_DifficultyThreshold || failureThresholdExceeded) {
                            eautomaton * aut = m_mk_aut(re);
                            if (aut == nullptr) {
                                TRACE("str", tout << "ERROR: symbolic automaton construction failed, likely due to non-constant term in regex" << std::endl;);
                                return false;
                            }
                            aut->compress();
                            regex_automata.push_back(aut);
                            regex_automaton_under_assumptions new_aut(re, aut, true);
                            if (!regex_automaton_assumptions.contains(re)) {
                                regex_automaton_assumptions.insert(re, svector<regex_automaton_under_assumptions>());
                            }
                            regex_automaton_assumptions[re].push_back(new_aut);
                            TRACE("str", tout << "add new automaton for " << mk_pp(re, m) << ": no assumptions" << std::endl;);
                            find_automaton_initial_bounds(str_in_re, aut);
                        } else {
                            // TODO check negation?
                            // TODO construct a partial automaton for R to the given lower bound?
                            if (false) {

                            } else {
                                regex_inc_counter(regex_fail_count, str_in_re);
                            }
                        }
                        continue;
                    }
                } else { // !lower_bound_exists
                    // no bounds information
                    // check for existing automata;
                    // try to construct an automaton if we don't have one yet
                    // and doing so without bounds is not difficult
                    bool existingAutomata = (regex_automaton_assumptions.contains(re) && !regex_automaton_assumptions[re].empty());
                    bool failureThresholdExceeded = (regex_get_counter(regex_fail_count, str_in_re) >= m_params.m_RegexAutomata_FailedAutomatonThreshold);
                    if (!existingAutomata) {
                        unsigned expected_complexity = estimate_regex_complexity(re);
                        if (expected_complexity <= m_params.m_RegexAutomata_DifficultyThreshold
                                || failureThresholdExceeded) {
                            eautomaton * aut = m_mk_aut(re);
                            if (aut == nullptr) {
                                TRACE("str", tout << "ERROR: symbolic automaton construction failed, likely due to non-constant term in regex" << std::endl;);
                                return false;
                            }
                            aut->compress();
                            regex_automata.push_back(aut);
                            regex_automaton_under_assumptions new_aut(re, aut, true);
                            if (!regex_automaton_assumptions.contains(re)) {
                                regex_automaton_assumptions.insert(re, svector<regex_automaton_under_assumptions>());
                            }
                            regex_automaton_assumptions[re].push_back(new_aut);
                            TRACE("str", tout << "add new automaton for " << mk_pp(re, m) << ": no assumptions" << std::endl;);
                            find_automaton_initial_bounds(str_in_re, aut);
                        } else {
                            regex_inc_counter(regex_fail_count, str_in_re);
                        }
                    } else {
                        regex_inc_counter(regex_fail_count, str_in_re);
                    }
                }
            }
        } // foreach (entry in regex_terms)

        for (auto entry : regex_terms_by_string) {
            // TODO do we need to check equivalence classes of strings here?

            expr* str = entry.m_key;
            ptr_vector<expr> str_in_re_terms = entry.m_value;

            svector<regex_automaton_under_assumptions> intersect_constraints;
            // we may find empty intersection before checking every constraint;
            // this vector keeps track of which ones actually take part in intersection
            svector<regex_automaton_under_assumptions> used_intersect_constraints;

            // choose an automaton/assumption for each assigned (str.in.re)
            // that's consistent with the current length information
            for (auto str_in_re_term : str_in_re_terms) {
                expr * _unused = nullptr;
                expr * re = nullptr;
                SASSERT(u.str.is_in_re(str_in_re_term));
                u.str.is_in_re(str_in_re_term, _unused, re);

                rational exact_len;
                bool has_exact_len = get_len_value(str, exact_len);

                rational lb, ub;
                bool has_lower_bound = lower_bound(mk_strlen(str), lb);
                bool has_upper_bound = upper_bound(mk_strlen(str), ub);

                if (regex_automaton_assumptions.contains(re) &&
                                                !regex_automaton_assumptions[re].empty()){
                    for (auto aut : regex_automaton_assumptions[re]) {
                        rational aut_ub;
                        bool assume_ub = aut.get_upper_bound(aut_ub);
                        rational aut_lb;
                        bool assume_lb = aut.get_lower_bound(aut_lb);
                        bool consistent = true;

                        if (assume_ub) {
                            // check consistency of assumed upper bound
                            if (has_exact_len) {
                                if (exact_len > aut_ub) {
                                    consistent = false;
                                }
                            } else {
                                if (has_upper_bound && ub > aut_ub) {
                                    consistent = false;
                                }
                            }
                        }

                        if (assume_lb) {
                            // check consistency of assumed lower bound
                            if (has_exact_len) {
                                if (exact_len < aut_lb) {
                                    consistent = false;
                                }
                            } else {
                                if (has_lower_bound && lb < aut_lb) {
                                    consistent = false;
                                }
                            }
                        }

                        if (consistent) {
                            intersect_constraints.push_back(aut);
                            break;
                        }
                    }
                }
            } // foreach(term in str_in_re_terms)

            eautomaton * aut_inter = nullptr;
            CTRACE("str", !intersect_constraints.empty(), tout << "check intersection of automata constraints for " << mk_pp(str, m) << std::endl;);
            for (auto aut : intersect_constraints) {
                TRACE("str",
                      {
                          unsigned v = regex_get_counter(regex_length_attempt_count, aut.get_regex_term());
                          tout << "length attempt count of " << mk_pp(aut.get_regex_term(), m) << " is " << v
                               << ", threshold is " << m_params.m_RegexAutomata_LengthAttemptThreshold << std::endl;
                      });

                if (regex_get_counter(regex_length_attempt_count, aut.get_regex_term()) >= m_params.m_RegexAutomata_LengthAttemptThreshold) {
                    unsigned intersectionDifficulty = 0;
                    if (aut_inter != nullptr) {
                        intersectionDifficulty = estimate_automata_intersection_difficulty(aut_inter, aut.get_automaton());
                    }
                    TRACE("str", tout << "intersection difficulty is " << intersectionDifficulty << std::endl;);
                    if (intersectionDifficulty <= m_params.m_RegexAutomata_IntersectionDifficultyThreshold
                            || regex_get_counter(regex_intersection_fail_count, aut.get_regex_term()) >= m_params.m_RegexAutomata_FailedIntersectionThreshold) {

                        expr * str_in_re_term(u.re.mk_in_re(str, aut.get_regex_term()));
                        lbool current_assignment = ctx.get_assignment(str_in_re_term);
                        // if the assignment is consistent with our assumption, use the automaton directly;
                        // otherwise, complement it (and save that automaton for next time)
                        // TODO we should cache these intermediate results
                        // TODO do we need to push the intermediates into a vector for deletion anyway?
                        if ( (current_assignment == l_true && aut.get_polarity())
                                || (current_assignment == l_false && !aut.get_polarity())) {
                            if (aut_inter == nullptr) {
                                aut_inter = aut.get_automaton();
                            } else {
                                aut_inter = m_mk_aut.mk_product(aut_inter, aut.get_automaton());
                                m_automata.push_back(aut_inter);
                            }
                        } else {
                            // need to complement first
                            expr_ref rc(u.re.mk_complement(aut.get_regex_term()), m);
                            eautomaton * aut_c = m_mk_aut(rc);
                            if (aut_c == nullptr) {
                                TRACE("str", tout << "ERROR: symbolic automaton construction failed, likely due to non-constant term in regex" << std::endl;);
                                return false;
                            }
                            regex_automata.push_back(aut_c);
                            // TODO is there any way to build a complement automaton from an existing one?
                            // this discards length information
                            if (aut_inter == nullptr) {
                                aut_inter = aut_c;
                            } else {
                                aut_inter = m_mk_aut.mk_product(aut_inter, aut_c);
                                m_automata.push_back(aut_inter);
                            }
                        }
                        used_intersect_constraints.push_back(aut);
                        if (aut_inter->is_empty()) {
                            break;
                        }
                    } else {
                        // failed intersection
                        regex_inc_counter(regex_intersection_fail_count, aut.get_regex_term());
                    }
                }
            } // foreach(entry in intersect_constraints)
            if (aut_inter != nullptr) {
                aut_inter->compress();
            }
            TRACE("str", tout << "intersected " << used_intersect_constraints.size() << " constraints" << std::endl;);

            expr_ref_vector conflict_terms(m);
            expr_ref conflict_lhs(m);
            for (auto aut : used_intersect_constraints) {
                expr * str_in_re_term(u.re.mk_in_re(str, aut.get_regex_term()));
                lbool current_assignment = ctx.get_assignment(str_in_re_term);
                if (current_assignment == l_true) {
                    conflict_terms.push_back(str_in_re_term);
                } else if (current_assignment == l_false) {
                    conflict_terms.push_back(m.mk_not(str_in_re_term));
                }
                // add length assumptions, if any
                rational ub;
                if (aut.get_upper_bound(ub)) {
                    expr_ref ub_term(m_autil.mk_le(mk_strlen(str), m_autil.mk_numeral(ub, true)), m);
                    conflict_terms.push_back(ub_term);
                }
                rational lb;
                if (aut.get_lower_bound(lb)) {
                    expr_ref lb_term(m_autil.mk_ge(mk_strlen(str), m_autil.mk_numeral(lb, true)), m);
                    conflict_terms.push_back(lb_term);
                }
            }
            conflict_lhs = mk_and(conflict_terms);
            TRACE("str", tout << "conflict lhs: " << mk_pp(conflict_lhs, m) << std::endl;);

            if (used_intersect_constraints.size() > 1 && aut_inter != nullptr) {
                // check whether the intersection is only the empty string
                unsigned initial_state = aut_inter->init();
                if (aut_inter->final_states().size() == 1 && aut_inter->is_final_state(initial_state)) {
                    // initial state is final and it is the only final state
                    // if there are no moves from the initial state,
                    // the only solution is the empty string
                    if (aut_inter->get_moves_from(initial_state).empty()) {
                        TRACE("str", tout << "product automaton only accepts empty string" << std::endl;);
                        expr_ref rhs1(ctx.mk_eq_atom(str, mk_string("")), m);
                        expr_ref rhs2(ctx.mk_eq_atom(mk_strlen(str), m_autil.mk_numeral(rational::zero(), true)), m);
                        expr_ref rhs(m.mk_and(rhs1, rhs2), m);
                        assert_implication(conflict_lhs, rhs);
                    }
                }
            }

            if (aut_inter != nullptr && aut_inter->is_empty()) {
                TRACE("str", tout << "product automaton is empty; asserting conflict clause" << std::endl;);
                expr_ref conflict_clause(m.mk_not(mk_and(conflict_terms)), m);
                assert_axiom(conflict_clause);
                add_persisted_axiom(conflict_clause);
            }
        } // foreach (entry in regex_terms_by_string)
        return true;
    }

    unsigned theory_str::estimate_regex_complexity(expr * re) {
        ENSURE(u.is_re(re));
        expr * sub1;
        expr * sub2;
        unsigned lo, hi;
        if (u.re.is_to_re(re, sub1)) {
            if (!u.str.is_string(sub1))
                throw default_exception("regular expressions must be built from string literals");
            zstring str;
            u.str.is_string(sub1, str);
            return str.length();
        } else if (u.re.is_complement(re, sub1)) {
            return estimate_regex_complexity_under_complement(sub1);
        } else if (u.re.is_concat(re, sub1, sub2)) {
            unsigned cx1 = estimate_regex_complexity(sub1);
            unsigned cx2 = estimate_regex_complexity(sub2);
            return _qadd(cx1, cx2);
        } else if (u.re.is_union(re, sub1, sub2)) {
            unsigned cx1 = estimate_regex_complexity(sub1);
            unsigned cx2 = estimate_regex_complexity(sub2);
            return _qadd(cx1, cx2);
        } else if (u.re.is_star(re, sub1) || u.re.is_plus(re, sub1)) {
            unsigned cx = estimate_regex_complexity(sub1);
            return _qmul(2, cx);
        } else if (u.re.is_loop(re, sub1, lo, hi) || u.re.is_loop(re, sub1, lo)) {
            unsigned cx = estimate_regex_complexity(sub1);
            return _qadd(lo, cx);
        } else if (u.re.is_range(re, sub1, sub2)) {
            SASSERT(u.str.is_string(sub1));
            SASSERT(u.str.is_string(sub2));
            zstring str1, str2;
            u.str.is_string(sub1, str1);
            u.str.is_string(sub2, str2);
            if (str1.length() == 1 && str2.length() == 1) {
                return 1 + str2[0] - str1[0];
            } else {
                return 1;
            }
        } else if (u.re.is_full_char(re) || u.re.is_full_seq(re)) {
            return 1;
        } else {
            TRACE("str", tout << "WARNING: unknown regex term " << mk_pp(re, get_manager()) << std::endl;);
            return 1;
        }
    }

    unsigned theory_str::estimate_regex_complexity_under_complement(expr * re) {
        ENSURE(u.is_re(re));
        expr * sub1;
        expr * sub2;
        zstring str;
        unsigned lo, hi;
        if (u.re.is_to_re(re, sub1) && u.str.is_string(sub1)) {
            return str.length();
        } else if (u.re.is_complement(re, sub1)) {
            // Why don't we return the regular complexity here?
            // We could, but this might be called from under another complemented subexpression.
            // It's better to give a worst-case complexity.
            return estimate_regex_complexity_under_complement(sub1);
        } else if (u.re.is_concat(re, sub1, sub2)) {
            unsigned cx1 = estimate_regex_complexity_under_complement(sub1);
            unsigned cx2 = estimate_regex_complexity_under_complement(sub2);
            return _qadd(_qmul(2, cx1), cx2);
        } else if (u.re.is_union(re, sub1, sub2)) {
            unsigned cx1 = estimate_regex_complexity_under_complement(sub1);
            unsigned cx2 = estimate_regex_complexity_under_complement(sub2);
            return _qmul(cx1, cx2);
        } else if (u.re.is_star(re, sub1) || u.re.is_plus(re, sub1) || u.re.is_loop(re, sub1, lo, hi) || u.re.is_loop(re, sub1, lo)) {
            unsigned cx = estimate_regex_complexity_under_complement(sub1);
            return _qmul(2, cx);
        } else if (u.re.is_range(re, sub1, sub2)) {
            SASSERT(u.str.is_string(sub1));
            SASSERT(u.str.is_string(sub2));
            zstring str1, str2;
            u.str.is_string(sub1, str1);
            u.str.is_string(sub2, str2);
            SASSERT(str1.length() == 1);
            SASSERT(str2.length() == 1);
            return 1 + str2[0] - str1[0];
        } else if (u.re.is_full_char(re) || u.re.is_full_seq(re)) {
            return 1;
        } else {
            TRACE("str", tout << "WARNING: unknown regex term " << mk_pp(re, get_manager()) << std::endl;);
            return 1;
        }
    }

    unsigned theory_str::estimate_automata_intersection_difficulty(eautomaton * aut1, eautomaton * aut2) {
        ENSURE(aut1 != nullptr);
        ENSURE(aut2 != nullptr);
        return _qmul(aut1->num_states(), aut2->num_states());
    }

    // Check whether a regex translates well to a linear set of length constraints.
    bool theory_str::check_regex_length_linearity(expr * re) {
        return check_regex_length_linearity_helper(re, false);
    }

    bool theory_str::check_regex_length_linearity_helper(expr * re, bool already_star) {
        expr * sub1;
        expr * sub2;
        unsigned lo, hi;
        if (u.re.is_to_re(re)) {
            return true;
        } else if (u.re.is_concat(re, sub1, sub2)) {
            return check_regex_length_linearity_helper(sub1, already_star) && check_regex_length_linearity_helper(sub2, already_star);
        } else if (u.re.is_union(re, sub1, sub2)) {
            return check_regex_length_linearity_helper(sub1, already_star) && check_regex_length_linearity_helper(sub2, already_star);
        } else if (u.re.is_star(re, sub1) || u.re.is_plus(re, sub1)) {
            if (already_star) {
                return false;
            } else {
                return check_regex_length_linearity_helper(sub1, true);
            }
        } else if (u.re.is_range(re)) {
            return true;
        } else if (u.re.is_full_char(re)) {
            return true;
        } else if (u.re.is_full_seq(re)) {
            return true;
        } else if (u.re.is_complement(re)) {
            // TODO can we do better?
            return false;
        } else if (u.re.is_intersection(re)) {
            return false;
        } else if (u.re.is_loop(re, sub1, lo, hi) || u.re.is_loop(re, sub1, lo)) {
            return check_regex_length_linearity_helper(sub1, already_star);
        } else {
            TRACE("str", tout << "WARNING: unknown regex term " << mk_pp(re, get_manager()) << std::endl;);
            return false;
        }
    }

    // note: returns an empty set `lens` if something went wrong
    void theory_str::check_subterm_lengths(expr * re, integer_set & lens) {
        expr * sub1;
        expr * sub2;
        unsigned lo, hi;
        if (u.re.is_to_re(re, sub1)) {
            SASSERT(u.str.is_string(sub1));
            zstring str;
            u.str.is_string(sub1, str);
            lens.insert(str.length());
        } else if (u.re.is_concat(re, sub1, sub2)) {
            integer_set lens_1, lens_2;
            check_subterm_lengths(sub1, lens_1);
            check_subterm_lengths(sub2, lens_2);
            if (lens_1.empty() || lens_2.empty()) {
                lens.reset();
            } else {
                // take all pairwise lengths
                for (integer_set::iterator it1 = lens_1.begin(); it1 != lens_1.end(); ++it1) {
                    for(integer_set::iterator it2 = lens_2.begin(); it2 != lens_2.end(); ++it2) {
                        int l1 = *it1;
                        int l2 = *it2;
                        lens.insert(l1 + l2);
                    }
                }
            }
        } else if (u.re.is_union(re, sub1, sub2)) {
            integer_set lens_1, lens_2;
            check_subterm_lengths(sub1, lens_1);
            check_subterm_lengths(sub2, lens_2);
            if (lens_1.empty() || lens_2.empty()) {
                lens.reset();
            } else {
                // take all possibilities from either side
                for (integer_set::iterator it1 = lens_1.begin(); it1 != lens_1.end(); ++it1) {
                    lens.insert(*it1);
                }
                for (integer_set::iterator it2 = lens_2.begin(); it2 != lens_2.end(); ++it2) {
                    lens.insert(*it2);
                }
            }
        } else if (u.re.is_star(re, sub1) || u.re.is_plus(re, sub1)) {
            // this is bad -- term generation requires this not to appear
            lens.reset();
        } else if (u.re.is_range(re, sub1, sub2)) {
            SASSERT(u.str.is_string(sub1));
            SASSERT(u.str.is_string(sub2));
            zstring str1, str2;
            u.str.is_string(sub1, str1);
            u.str.is_string(sub2, str2);
            // re.range is a language of singleton strings if both of its arguments are;
            // otherwise it is the empty language
            if (str1.length() == 1 && str2.length() == 1) {
                lens.insert(1);
            } else {
                lens.insert(0);
            }
        } else if (u.re.is_full_char(re)) {
            lens.insert(1);
        } else if (u.re.is_full_seq(re)) {
            lens.reset();
        } else if (u.re.is_complement(re)) {
            lens.reset();
        } else if (u.re.is_loop(re, sub1, lo, hi)) {
            integer_set lens_1;
            check_subterm_lengths(sub1, lens_1);
            for (unsigned i = lo; i <= hi; ++i) {
                for (auto j : lens_1) {
                    lens.insert(i * j);
                }
            }
        } else {
            TRACE("str", tout << "WARNING: unknown regex term " << mk_pp(re, get_manager()) << std::endl;);
            lens.reset();
        }
    }

    /*
     * Infer all length constraints implied by the given regular expression `re`
     * in order to constrain `lenVar` (which must be of sort Int).
     * This assumes that `re` appears in a positive context.
     * Returns a Boolean formula expressing the appropriate constraints over `lenVar`.
     * In some cases, the returned formula requires one or more free integer variables to be created.
     * These variables are returned in the reference parameter `freeVariables`.
     * Extra assertions should be made for these free variables constraining them to be non-negative.
     */
    expr_ref theory_str::infer_all_regex_lengths(expr * lenVar, expr * re, expr_ref_vector & freeVariables) {
        ENSURE(u.is_re(re));
        expr * sub1;
        expr * sub2;
        unsigned lo, hi;
        if (u.re.is_to_re(re, sub1)) {
            if (!u.str.is_string(sub1))
                throw default_exception("regular expressions must be built from string literals");
            zstring str;
            u.str.is_string(sub1, str);
            rational strlen(str.length());
            expr_ref retval(ctx.mk_eq_atom(lenVar, m_autil.mk_numeral(strlen, true)), m);
            return retval;
        } else if (u.re.is_union(re, sub1, sub2)) {
            expr_ref r1 = infer_all_regex_lengths(lenVar, sub1, freeVariables);
            expr_ref r2 = infer_all_regex_lengths(lenVar, sub2, freeVariables);
            expr_ref retval(m.mk_or(r1, r2), m);
            return retval;
        } else if (u.re.is_concat(re, sub1, sub2)) {
            expr * v1 = mk_int_var("rlen1");
            expr * v2 = mk_int_var("rlen2");
            freeVariables.push_back(v1);
            freeVariables.push_back(v2);
            expr_ref r1 = infer_all_regex_lengths(v1, sub1, freeVariables);
            expr_ref r2 = infer_all_regex_lengths(v2, sub2, freeVariables);
            expr_ref_vector finalResult(m);
            finalResult.push_back(ctx.mk_eq_atom(lenVar, m_autil.mk_add(v1, v2)));
            finalResult.push_back(r1);
            finalResult.push_back(r2);
            expr_ref retval(mk_and(finalResult), m);
            return retval;
        } else if (u.re.is_star(re, sub1) || u.re.is_plus(re, sub1)) {
            // stars are generated as a linear combination of all possible subterm lengths;
            // this requires that there are no stars under this one
            /*
                expr * v = mk_int_var("rlen");
                expr * n = mk_int_var("rstar");
                freeVariables.push_back(v);
                freeVariables.push_back(n);
                expr_ref rsub = infer_all_regex_lengths(v, sub1, freeVariables);
                expr_ref_vector finalResult(m);
                finalResult.push_back(rsub);
                finalResult.push_back(ctx.mk_eq_atom(lenVar, m_autil.mk_mul(v, n)));
                expr_ref retval(mk_and(finalResult), m);
                return retval;
             */
            integer_set subterm_lens;
            check_subterm_lengths(sub1, subterm_lens);
            if (subterm_lens.empty()) {
                // somehow generation was impossible
                expr_ref retval(m_autil.mk_ge(lenVar, m_autil.mk_numeral(rational::zero(), true)), m);
                return retval;
            } else {
                TRACE("str", tout << "subterm lengths:";
                for(integer_set::iterator it = subterm_lens.begin(); it != subterm_lens.end(); ++it) {
                    tout << " " << *it;
                }
                tout << std::endl;);
                expr_ref_vector sum_terms(m);
                for (integer_set::iterator it = subterm_lens.begin(); it != subterm_lens.end(); ++it) {
                    rational lenOption(*it);
                    expr * n = mk_int_var("rstar");
                    freeVariables.push_back(n);
                    expr_ref term(m_autil.mk_mul(m_autil.mk_numeral(lenOption, true), n), m);
                    expr_ref term2(term, m);
                    if (u.re.is_plus(re)) {
                        // n effectively starts at 1
                        term2 = m_autil.mk_add(m_autil.mk_numeral(lenOption, true), term);
                    }
                    sum_terms.push_back(term2);
                }
                expr_ref retval(ctx.mk_eq_atom(lenVar, m_autil.mk_add_simplify(sum_terms)), m);
                return retval;
            }
        } else if (u.re.is_loop(re, sub1, lo, hi)) {
            expr * v1 = mk_int_var("rlen");
            freeVariables.push_back(v1);
            expr_ref r1 = infer_all_regex_lengths(v1, sub1, freeVariables);
            expr_ref_vector v1_choices(m);
            for (unsigned i = lo; i <= hi; ++i) {
                rational rI(i);
                expr_ref v1_i(ctx.mk_eq_atom(lenVar, m_autil.mk_mul(m_autil.mk_numeral(rI, true), v1)), m);
                v1_choices.push_back(v1_i);
            }
            expr_ref_vector finalResult(m);
            finalResult.push_back(r1);
            finalResult.push_back(mk_or(v1_choices));
            expr_ref retval(mk_and(finalResult), m);
            SASSERT(retval);
            return retval;
        } else if (u.re.is_range(re, sub1, sub2)) {
            SASSERT(u.str.is_string(sub1));
            SASSERT(u.str.is_string(sub2));
            zstring str1, str2;
            u.str.is_string(sub1, str1);
            u.str.is_string(sub2, str2);
            SASSERT(str1.length() == 1);
            SASSERT(str2.length() == 1);
            expr_ref retval(ctx.mk_eq_atom(lenVar, m_autil.mk_numeral(rational::one(), true)), m);
            return retval;
        } else if (u.re.is_full_char(re)) {
            expr_ref retval(ctx.mk_eq_atom(lenVar, m_autil.mk_numeral(rational::one(), true)), m);
            return retval;
        } else if (u.re.is_full_seq(re)) {
            // match any unbounded string
            expr_ref retval(m_autil.mk_ge(lenVar, m_autil.mk_numeral(rational::zero(), true)), m);
            return retval;
        } else if (u.re.is_complement(re)) {
            // skip complement for now, in general this is difficult to predict
            expr_ref retval(m_autil.mk_ge(lenVar, m_autil.mk_numeral(rational::zero(), true)), m);
            return retval;
        } else {
            TRACE("str", tout << "WARNING: unknown regex term " << mk_pp(re, m) << std::endl;);
            expr_ref retval(m_autil.mk_ge(lenVar, m_autil.mk_numeral(rational::zero(), true)), m);
            return retval;
        }
    }

    /*
     * Assert initial lower and upper bounds for the positive constraint (str in re) corresponding
     * to the automaton `aut`.
     * This asserts a constraint of the form:
     *   str_in_re --> (len(str) ?= 0 OR len(str) >= lb) AND len(str) <= ub
     * where the upper bound clause is omitted if the upper bound doesn't exist
     * and the equality with 0 is based on whether solutions of length 0 are allowed.
     */
    void theory_str::find_automaton_initial_bounds(expr * str_in_re, eautomaton * aut) {
        ENSURE(aut != nullptr);

        expr_ref_vector rhs(m);
        expr * str = nullptr;
        expr * re = nullptr;
        u.str.is_in_re(str_in_re, str, re);
        expr_ref strlen(mk_strlen(str), m);

        // lower bound first
        rational nonzero_lower_bound;
        bool zero_sol_exists = refine_automaton_lower_bound(aut, rational::zero(), nonzero_lower_bound);
        if (zero_sol_exists) {
            regex_last_lower_bound.insert(str, rational::zero());
            // solution at 0
            if (!nonzero_lower_bound.is_minus_one()) {
                expr_ref rhs1(ctx.mk_eq_atom(strlen, m_autil.mk_numeral(rational::zero(), true)), m);
                expr_ref rhs2(m_autil.mk_ge(strlen, m_autil.mk_numeral(nonzero_lower_bound, true)), m);
                rhs.push_back(m.mk_or(rhs1, rhs2));
            } else {
                // length of solution can ONLY be 0
                expr_ref rhs1(ctx.mk_eq_atom(strlen, m_autil.mk_numeral(rational::zero(), true)), m);
                rhs.push_back(rhs1);
            }
        } else {
            // no solution at 0
            if (!nonzero_lower_bound.is_minus_one()) {
                regex_last_lower_bound.insert(str, nonzero_lower_bound);
                expr_ref rhs2(m_autil.mk_ge(strlen, m_autil.mk_numeral(nonzero_lower_bound, true)), m);
                rhs.push_back(rhs2);
            } else {
                // probably no solutions at all; just assume that 0 is a (safe) lower bound
                regex_last_lower_bound.insert(str, rational::zero());
                rhs.reset();
            }
        }
        // TODO upper bound check

        if (!rhs.empty()) {
            expr_ref lhs(str_in_re, m);
            expr_ref _rhs(mk_and(rhs), m);
            assert_implication(lhs, _rhs);
        }
    }

    /*
     * Refine the lower bound on the length of a solution to a given automaton.
     * The method returns TRUE if a solution of length `current_lower_bound` exists,
     * and FALSE otherwise. In addition, the reference parameter `refined_lower_bound`
     * is assigned the length of the shortest solution longer than `current_lower_bound`
     * if it exists, or -1 otherwise.
     */
    bool theory_str::refine_automaton_lower_bound(eautomaton * aut, rational current_lower_bound, rational & refined_lower_bound) {
        ENSURE(aut != nullptr);

        if (aut->final_states().empty()) {
            // no solutions at all
            refined_lower_bound = rational::minus_one();
            return false;
        }

        // from here we assume that there is a final state reachable from the initial state

        unsigned_vector search_queue;
        // populate search_queue with all states reachable from the epsilon-closure of start state
        aut->get_epsilon_closure(aut->init(), search_queue);

        unsigned search_depth = 0;
        hashtable<unsigned, unsigned_hash, default_eq<unsigned>> next_states;
        unsigned_vector next_search_queue;

        bool found_solution_at_lower_bound = false;

        while (!search_queue.empty()) {
            // if we are at the lower bound, check for final states
            if (search_depth == current_lower_bound.get_unsigned()) {
                for (unsigned_vector::iterator it = search_queue.begin(); it != search_queue.end(); ++it) {
                    unsigned state = *it;
                    if (aut->is_final_state(state)) {
                        found_solution_at_lower_bound = true;
                        break;
                    }
                }
                // end phase 1
                break;
            }
            next_states.reset();
            next_search_queue.clear();
            // move one step along all states
            for (unsigned_vector::iterator it = search_queue.begin(); it != search_queue.end(); ++it) {
                unsigned src = *it;
                eautomaton::moves next_moves;
                aut->get_moves_from(src, next_moves, true);
                for (eautomaton::moves::iterator move_it = next_moves.begin();
                        move_it != next_moves.end(); ++move_it) {
                    unsigned dst = move_it->dst();
                    if (!next_states.contains(dst)) {
                        next_states.insert(dst);
                        next_search_queue.push_back(dst);
                    }
                }
            }
            search_queue.clear();
            search_queue.append(next_search_queue);
            search_depth += 1;
        } // !search_queue.empty()

        // if we got here before reaching the lower bound,
        // there aren't any solutions at or above it, so stop
        if (search_depth < current_lower_bound.get_unsigned()) {
            refined_lower_bound = rational::minus_one();
            return false;
        }

        // phase 2: continue exploring the automaton above the lower bound
        SASSERT(search_depth == current_lower_bound.get_unsigned());

        while (!search_queue.empty()) {
            if (search_depth > current_lower_bound.get_unsigned()) {
                // check if we have found a solution above the lower bound
                for (unsigned_vector::iterator it = search_queue.begin(); it != search_queue.end(); ++it) {
                    unsigned state = *it;
                    if (aut->is_final_state(state)) {
                        // this is a solution at a depth higher than the lower bound
                        refined_lower_bound = rational(search_depth);
                        return found_solution_at_lower_bound;
                    }
                }
            }
            next_states.reset();
            next_search_queue.clear();
            // move one step along all states
            for (unsigned_vector::iterator it = search_queue.begin(); it != search_queue.end(); ++it) {
                unsigned src = *it;
                eautomaton::moves next_moves;
                aut->get_moves_from(src, next_moves, true);
                for (eautomaton::moves::iterator move_it = next_moves.begin();
                        move_it != next_moves.end(); ++move_it) {
                    unsigned dst = move_it->dst();
                    if (!next_states.contains(dst)) {
                        next_states.insert(dst);
                        next_search_queue.push_back(dst);
                    }
                }
            }
            search_queue.clear();
            search_queue.append(next_search_queue);
            search_depth += 1;
        }
        // if we reached this point, we explored the whole automaton and didn't find any
        // solutions above the lower bound
        refined_lower_bound = rational::minus_one();
        return found_solution_at_lower_bound;
    }

    /*
     * Refine the upper bound on the length of a solution to a given automaton.
     * The method returns TRUE if a solution of length `current_upper_bound` exists,
     * and FALSE otherwise. In addition, the reference parameter `refined_upper_bound`
     * is assigned the length of the longest solution shorter than `current_upper_bound`,
     * if a shorter solution exists, or -1 otherwise.
     */
    bool theory_str::refine_automaton_upper_bound(eautomaton * aut, rational current_upper_bound, rational & refined_upper_bound) {
        ENSURE(aut != nullptr);

        if (aut->final_states().empty()) {
            // no solutions at all!
            refined_upper_bound = rational::minus_one();
            return false;
        }

        // from here we assume there is a final state reachable from the initial state
        unsigned_vector search_queue;
        // populate search queue with all states reachable from the epsilon-closure of the start state
        aut->get_epsilon_closure(aut->init(), search_queue);

        rational last_solution_depth = rational::minus_one();
        bool found_solution_at_upper_bound = false;

        unsigned search_depth = 0;
        hashtable<unsigned, unsigned_hash, default_eq<unsigned> > next_states;
        unsigned_vector next_search_queue;

        while(!search_queue.empty()) {
            // see if any of the current states are final
            for (unsigned_vector::iterator it = search_queue.begin(); it != search_queue.end(); ++it) {
                unsigned src = *it;
                if (aut->is_final_state(src)) {
                    if (search_depth == current_upper_bound.get_unsigned()) {
                        found_solution_at_upper_bound = true;
                    } else {
                        last_solution_depth = rational(search_depth);
                    }
                    break;
                }
            }

            if (search_depth == current_upper_bound.get_unsigned()) {
                break;
            }

            next_states.reset();
            next_search_queue.clear();
            // move one step along all states
            for (unsigned_vector::iterator it = search_queue.begin(); it != search_queue.end(); ++it) {
                unsigned src = *it;
                eautomaton::moves next_moves;
                aut->get_moves_from(src, next_moves, true);
                for (eautomaton::moves::iterator moves_it = next_moves.begin();
                        moves_it != next_moves.end(); ++moves_it) {
                    unsigned dst = moves_it->dst();
                    if (!next_states.contains(dst)) {
                        next_states.insert(dst);
                        next_search_queue.push_back(dst);
                    }
                }
            }
            search_queue.clear();
            search_queue.append(next_search_queue);
            search_depth += 1;
        } //!search_queue.empty()

        refined_upper_bound = last_solution_depth;
        return found_solution_at_upper_bound;
    }

    void theory_str::aut_path_add_next(u_map<expr*>& next, expr_ref_vector& trail, unsigned idx, expr* cond) {
        expr* acc;
        if (!get_manager().is_true(cond) && next.find(idx, acc)) {
            expr* args[2] = { cond, acc };
            cond = mk_or(get_manager(), 2, args);
        }
        trail.push_back(cond);
        next.insert(idx, cond);
    }

    expr_ref theory_str::aut_path_rewrite_constraint(expr * cond, expr * ch_var) {

        expr_ref retval(m);

        unsigned char_val = 0;

        expr * lhs;
        expr * rhs;

        if (u.is_const_char(cond, char_val)) {
            SASSERT(char_val < 256);
            TRACE("str", tout << "rewrite character constant " << char_val << std::endl;);
            zstring str_const(char_val);
            retval = u.str.mk_string(str_const);
            return retval;
        } else if (is_var(cond)) {
            TRACE("str", tout << "substitute var" << std::endl;);
            retval = ch_var;
            return retval;
        } else if (m.is_eq(cond, lhs, rhs)) {
            // handle this specially because the sort of the equality will change
            expr_ref new_lhs(aut_path_rewrite_constraint(lhs, ch_var), m);
            SASSERT(new_lhs);
            expr_ref new_rhs(aut_path_rewrite_constraint(rhs, ch_var), m);
            SASSERT(new_rhs);
            retval = ctx.mk_eq_atom(new_lhs, new_rhs);
            return retval;
        } else if (m.is_bool(cond)) {
            TRACE("str", tout << "rewrite boolean term " << mk_pp(cond, m) << std::endl;);
            app * a_cond = to_app(cond);
            expr_ref_vector rewritten_args(m);
            for (unsigned i = 0; i < a_cond->get_num_args(); ++i) {
                expr * argI = a_cond->get_arg(i);
                expr_ref new_arg(aut_path_rewrite_constraint(argI, ch_var), m);
                SASSERT(new_arg);
                rewritten_args.push_back(new_arg);
            }
            retval = m.mk_app(a_cond->get_decl(), rewritten_args.data());
            TRACE("str", tout << "final rewritten term is " << mk_pp(retval, m) << std::endl;);
            return retval;
        } else {
            TRACE("str", tout << "ERROR: unrecognized automaton path constraint " << mk_pp(cond, m) << ", cannot translate" << std::endl;);
            retval = nullptr;
            return retval;
        }
    }

    /*
     * Create finite path constraints for the string variable `str` with respect to the automaton `aut`.
     * The returned expression is the right-hand side of a constraint of the form
     * (str in re) AND (|str| = len) AND (any applicable length assumptions on aut) -> (rhs AND character constraints).
     * The character constraints, which are (str = c0 . c1 . (...) . cn) and (|c0| = 1, ...),
     * are returned in `characterConstraints`.
     */
    expr_ref theory_str::generate_regex_path_constraints(expr * stringTerm, eautomaton * aut, rational lenVal, expr_ref & characterConstraints) {
        ENSURE(aut != nullptr);

        if (lenVal.is_zero()) {
            // if any state in the epsilon-closure of the start state is accepting,
            // then the empty string is in this language
            unsigned_vector states;
            bool has_final = false;
            aut->get_epsilon_closure(aut->init(), states);
            for (unsigned i = 0; i < states.size() && !has_final; ++i) {
                has_final = aut->is_final_state(states[i]);
            }
            if (has_final) {
                // empty string is OK, assert axiom
                expr_ref rhs(ctx.mk_eq_atom(stringTerm, mk_string("")), m);
                SASSERT(rhs);
                //regex_automata_assertions.insert(stringTerm, final_axiom);
                //m_trail_stack.push(insert_obj_map<theory_str, expr, expr* >(regex_automata_assertions, stringTerm) );
                return rhs;
            } else {
                // negate -- the empty string isn't in the language
                //expr_ref conflict(m.mk_not(mk_and(toplevel_lhs)), m);
                //assert_axiom(conflict);
                expr_ref conflict(m.mk_false(), m);
                return conflict;
            }
        } // lenVal.is_zero()

        expr_ref_vector pathChars(m);
        expr_ref_vector pathChars_len_constraints(m);

        // reuse character terms over the same string
        if (string_chars.contains(stringTerm)) {
            // find out whether we have enough characters already
            ptr_vector<expr> old_chars;
            string_chars.find(stringTerm, old_chars);
            if (old_chars.size() < lenVal.get_unsigned()) {
                for (unsigned i = old_chars.size(); i < lenVal.get_unsigned(); ++i) {
                    std::stringstream ss;
                    ss << "ch" << i;
                    expr_ref ch(mk_str_var(ss.str()), m);
                    m_trail.push_back(ch);
                    old_chars.push_back(ch);
                }
            }
            string_chars.insert(stringTerm, old_chars);
            // now we're guaranteed to have at least the right number of characters in old_chars
            for (unsigned i = 0; i < lenVal.get_unsigned(); ++i) {
                expr_ref ch(old_chars.get(i), m);
                refresh_theory_var(ch);
                pathChars.push_back(ch);
                pathChars_len_constraints.push_back(ctx.mk_eq_atom(mk_strlen(ch), m_autil.mk_numeral(rational::one(), true)));
            }
        } else {
            ptr_vector<expr> new_chars;
            for (unsigned i = 0; i < lenVal.get_unsigned(); ++i) {
                std::stringstream ss;
                ss << "ch" << i;
                expr_ref ch(mk_str_var(ss.str()), m);
                pathChars.push_back(ch);
                pathChars_len_constraints.push_back(ctx.mk_eq_atom(mk_strlen(ch), m_autil.mk_numeral(rational::one(), true)));
                new_chars.push_back(ch);
            }
            string_chars.insert(stringTerm, new_chars);
        }

        // modification of code in seq_rewriter::mk_str_in_regexp()
        expr_ref_vector trail(m);
        u_map<expr*> maps[2];
        bool select_map = false;
        expr_ref ch(m), cond(m);
        eautomaton::moves mvs;
        maps[0].insert(aut->init(), m.mk_true());
        // is_accepted(a, aut) & some state in frontier is final.
        for (unsigned i = 0; i < lenVal.get_unsigned(); ++i) {
            u_map<expr*>& frontier = maps[select_map];
            u_map<expr*>& next = maps[!select_map];
            select_map = !select_map;
            ch = pathChars.get(i);
            next.reset();
            u_map<expr*>::iterator it = frontier.begin(), end = frontier.end();
            for (; it != end; ++it) {
                mvs.reset();
                unsigned state = it->m_key;
                expr*    acc  = it->m_value;
                aut->get_moves_from(state, mvs, false);
                for (unsigned j = 0; j < mvs.size(); ++j) {
                    eautomaton::move const& mv = mvs[j];
                    SASSERT(mv.t());
                    if (mv.t()->is_char() && m.is_value(mv.t()->get_char())) {
                        // change this to a string constraint
                        expr_ref cond_rhs = aut_path_rewrite_constraint(mv.t()->get_char(), ch);
                        SASSERT(cond_rhs);
                        cond = ctx.mk_eq_atom(ch, cond_rhs);
                        SASSERT(cond);
                        expr * args[2] = {cond, acc};
                        cond = mk_and(m, 2, args);
                        aut_path_add_next(next, trail, mv.dst(), cond);
                    } else if (mv.t()->is_range()) {
                        expr_ref range_lo(mv.t()->get_lo(), m);
                        expr_ref range_hi(mv.t()->get_hi(), m);

                        unsigned lo_val, hi_val;

                        if (u.is_const_char(range_lo, lo_val) && u.is_const_char(range_hi, hi_val)) {
                            TRACE("str", tout << "make range predicate from " << lo_val << " to " << hi_val << std::endl;);
                            expr_ref cond_rhs(m);
                            expr_ref_vector cond_rhs_terms(m);
                            for (unsigned i = lo_val; i <= hi_val; ++i) {
                                zstring str_const(i);
                                expr_ref str_expr(u.str.mk_string(str_const), m);
                                cond_rhs_terms.push_back(ctx.mk_eq_atom(ch, str_expr));
                            }
                            cond_rhs = mk_or(cond_rhs_terms);
                            SASSERT(cond_rhs);
                            expr * args[2] = {cond_rhs, acc};
                            cond = mk_and(m, 2, args);
                            aut_path_add_next(next, trail, mv.dst(), cond);
                        } else {
                            TRACE("str", tout << "warning: non-bitvectors in automaton range predicate" << std::endl;);
                            UNREACHABLE();
                        }
                    } else if (mv.t()->is_pred()) {
                        // rewrite this constraint over string terms
                        expr_ref cond_rhs = aut_path_rewrite_constraint(mv.t()->get_pred(), ch);
                        SASSERT(cond_rhs);

                        if (m.is_false(cond_rhs)) {
                            continue;
                        } else if (m.is_true(cond_rhs)) {
                            aut_path_add_next(next, trail, mv.dst(), acc);
                            continue;
                        }
                        expr * args[2] = {cond_rhs, acc};
                        cond = mk_and(m, 2, args);
                        aut_path_add_next(next, trail, mv.dst(), cond);
                    }
                }
            }
        }
        u_map<expr*> const& frontier = maps[select_map];
        u_map<expr*>::iterator it = frontier.begin(), end = frontier.end();
        expr_ref_vector ors(m);
        for (; it != end; ++it) {
            unsigned_vector states;
            bool has_final = false;
            aut->get_epsilon_closure(it->m_key, states);
            for (unsigned i = 0; i < states.size() && !has_final; ++i) {
                has_final = aut->is_final_state(states[i]);
            }
            if (has_final) {
                ors.push_back(it->m_value);
            }
        }
        expr_ref result(mk_or(ors));
        TRACE("str", tout << "regex path constraint: " << mk_pp(result, m) << "\n";);

        expr_ref concat_rhs(m);
        if (pathChars.size() == 1) {
            concat_rhs = ctx.mk_eq_atom(stringTerm, pathChars.get(0));
        } else {
            expr_ref acc(pathChars.get(0), m);
            for (unsigned i = 1; i < pathChars.size(); ++i) {
                acc = mk_concat(acc, pathChars.get(i));
            }
            concat_rhs = ctx.mk_eq_atom(stringTerm, acc);
        }

        //expr_ref toplevel_rhs(m.mk_and(result, mk_and(pathChars_len_constraints), concat_rhs), m);
        characterConstraints = m.mk_and(mk_and(pathChars_len_constraints), concat_rhs);
        //expr_ref final_axiom(rewrite_implication(mk_and(toplevel_lhs), toplevel_rhs), m);
        //regex_automata_assertions.insert(stringTerm, final_axiom);
        //m_trail_stack.push(insert_obj_map<theory_str, expr, expr* >(regex_automata_assertions, stringTerm) );
        return result;
    }

    void theory_str::regex_inc_counter(obj_map<expr, unsigned> & counter_map, expr * key) {
        unsigned old_v;
        if (counter_map.find(key, old_v)) {
            unsigned new_v = old_v += 1;
            counter_map.insert(key, new_v);
        } else {
            counter_map.insert(key, 1);
        }
    }

    unsigned theory_str::regex_get_counter(obj_map<expr, unsigned> & counter_map, expr * key) {
        unsigned v;
        if (counter_map.find(key, v)) {
            return v;
        } else {
            counter_map.insert(key, 0);
            return 0;
        }
    }

}; /* namespace smt */
