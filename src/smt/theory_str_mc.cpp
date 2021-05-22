/*++
  Module Name:

  theory_str_mc.cpp

  Abstract:

  Model Construction for String Theory Plugin

  Author:

  Murphy Berzish and Yunhui Zheng

  Revision History:

  --*/
#include "ast/ast_smt2_pp.h"
#include "smt/smt_context.h"
#include "smt/theory_str.h"
#include "smt/smt_model_generator.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include<list>
#include<algorithm>
#include "smt/theory_seq_empty.h"
#include "smt/theory_arith.h"
#include "ast/ast_util.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/expr_replacer.h"
#include "smt_kernel.h"
#include "model/model_smt2_pp.h"

namespace smt {

    /*
     * Use the current model in the arithmetic solver to get the length of a term.
     * Returns true if this could be done, placing result in 'termLen', or false otherwise.
     * Works like get_len_value() except uses arithmetic solver model instead of EQCs.
     */
    bool theory_str::fixed_length_get_len_value(expr * e, rational & val) {
        ast_manager & m = get_manager();

        rational val1;
        expr_ref len(m), len_val(m);
        expr* e1 = nullptr, *e2 = nullptr;
        expr_ref_vector todo(m);
        todo.push_back(e);
        val.reset();
        while (!todo.empty()) {
            expr* c = todo.back();
            todo.pop_back();
            zstring tmp;
            if (u.str.is_concat(c, e1, e2)) {
                todo.push_back(e1);
                todo.push_back(e2);
            }
            else if (u.str.is_string(c, tmp)) {
                unsigned int sl = tmp.length();
                val += rational(sl);
            }
            else {
                len = mk_strlen(c);
                arith_value v(get_manager());
                v.init(&get_context());
                if (v.get_value(len, val1)) {
                    val += val1;
                } else {
                    return false;
                }
            }
        }
        return val.is_int();
    }


    bool theory_str::fixed_length_reduce_suffix(smt::kernel & subsolver, expr_ref f, expr_ref & cex) {
        ast_manager & m = get_manager();

        ast_manager & sub_m = subsolver.m();

        expr * full = nullptr;
        expr * suff = nullptr;
        VERIFY(u.str.is_suffix(f, suff, full));

        expr_ref haystack(full, m);
        expr_ref needle(suff, m);

        expr_ref_vector full_chars(m), suff_chars(m);

        if (!fixed_length_reduce_string_term(subsolver, haystack, full_chars, cex)
                || !fixed_length_reduce_string_term(subsolver, needle, suff_chars, cex)) {
            return false;
        }

        if (suff_chars.size() == 0) {
            // all strings endwith the empty one
            return true;
        }

        if (full_chars.size() == 0 && suff_chars.size() > 0) {
            // the empty string doesn't "endwith" any non-empty string
            cex = m.mk_or(m.mk_not(f), ctx.mk_eq_atom(mk_strlen(suff), mk_int(0)),
                    m_autil.mk_ge(mk_strlen(full), mk_int(0)));
            th_rewriter m_rw(m);
            m_rw(cex);
            return false;
        }

        if (full_chars.size() < suff_chars.size()) {
            // a string can't endwith a longer one
            // X startswith Y -> len(X) >= len(Y)
            expr_ref minus_one(m_autil.mk_numeral(rational::minus_one(), true), m);
            expr_ref zero(m_autil.mk_numeral(rational::zero(), true), m);
            expr_ref lens(m_autil.mk_add(mk_strlen(full), m_autil.mk_mul(minus_one, mk_strlen(suff))), m);
            cex = m.mk_or(m.mk_not(f), m_autil.mk_ge(lens, zero));
            th_rewriter m_rw(m);
            m_rw(cex);
            return false;
        }

        expr_ref_vector branch(sub_m);
        for (unsigned j = 0; j < suff_chars.size(); ++j) {
            // full[j] == suff[j]
            expr_ref cLHS(full_chars.get(full_chars.size() - j - 1), sub_m);
            expr_ref cRHS(suff_chars.get(suff_chars.size() - j - 1), sub_m);
            expr_ref _e(sub_m.mk_eq(cLHS, cRHS), sub_m);
            branch.push_back(_e);
        }

        expr_ref final_diseq(mk_and(branch), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        TRACE("str_fl", tout << "inserting into fixed_lesson" <<std::endl;);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(PFUN, f, f));

        return true;
    }

    bool theory_str::fixed_length_reduce_negative_suffix(smt::kernel & subsolver, expr_ref f, expr_ref & cex) {
        ast_manager & m = get_manager();

        ast_manager & sub_m = subsolver.m();

        expr * full = nullptr;
        expr * suff = nullptr;
        VERIFY(u.str.is_suffix(f, suff, full));

        expr_ref haystack(full, m);
        expr_ref needle(suff, m);

        expr_ref_vector full_chars(m), suff_chars(m);
        if (!fixed_length_reduce_string_term(subsolver, haystack, full_chars, cex)
                || !fixed_length_reduce_string_term(subsolver, needle, suff_chars, cex)) {
            return false;
        }

        if (suff_chars.size() == 0) {
            // all strings endwith the empty one
            cex = m.mk_or(m.mk_not(f), m.mk_not(ctx.mk_eq_atom(mk_strlen(suff), mk_int(0))));
            th_rewriter m_rw(m);
            m_rw(cex);
            return false;
        }

        if (full_chars.size() == 0 && suff_chars.size() > 0) {
            // the empty string doesn't "endwith" any non-empty string
            return true;
        }

        if (full_chars.size() < suff_chars.size()) {
            // a string can't endwith a longer one
            // X startswith Y -> len(X) >= len(Y)
            return true;
        }

        expr_ref_vector branch(sub_m);
        for (unsigned j = 0; j < suff_chars.size(); ++j) {
            // full[j] == suff[j]
            expr_ref cLHS(full_chars.get(full_chars.size() - j - 1), sub_m);
            expr_ref cRHS(suff_chars.get(suff_chars.size() - j - 1), sub_m);
            expr_ref _e(sub_m.mk_eq(cLHS, cRHS), sub_m);
            branch.push_back(_e);
        }

        expr_ref final_diseq(mk_not(sub_m, mk_and(branch)), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        TRACE("str_fl", tout << "inserting into fixed_lesson" <<std::endl;);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(NFUN, f, f));

        return true;
    }

    bool theory_str::fixed_length_reduce_prefix(smt::kernel & subsolver, expr_ref f, expr_ref & cex) {
        ast_manager & m = get_manager();

        ast_manager & sub_m = subsolver.m();

        expr * full = nullptr;
        expr * pref = nullptr;
        VERIFY(u.str.is_prefix(f, pref, full));

        expr_ref haystack(full, m);
        expr_ref needle(pref, m);

        expr_ref_vector full_chars(m), pref_chars(m);
        if (!fixed_length_reduce_string_term(subsolver, haystack, full_chars, cex)
                || !fixed_length_reduce_string_term(subsolver, needle, pref_chars, cex)) {
            return false;
        }


        if (pref_chars.size() == 0) {
            // all strings startwith the empty one
            return true;
        }

        if (full_chars.size() == 0 && pref_chars.size() > 0) {
            // the empty string doesn't "stratwith" any non-empty string
            cex = m.mk_or(m.mk_not(f), ctx.mk_eq_atom(mk_strlen(pref), mk_int(0)),
                    m_autil.mk_ge(mk_strlen(full), mk_int(0)));
            th_rewriter m_rw(m);
            m_rw(cex);
            return false;
        }

        if (full_chars.size() < pref_chars.size()) {
            // a string can't startwith a longer one
            // X startswith Y -> len(X) >= len(Y)
            expr_ref minus_one(m_autil.mk_numeral(rational::minus_one(), true), m);
            expr_ref zero(m_autil.mk_numeral(rational::zero(), true), m);
            expr_ref lens(m_autil.mk_add(mk_strlen(full), m_autil.mk_mul(minus_one, mk_strlen(pref))), m);
            cex = m.mk_or(m.mk_not(f), m_autil.mk_ge(lens, zero));
            th_rewriter m_rw(m);
            m_rw(cex);
            return false;
        }

        expr_ref_vector branch(m);
        for (unsigned j = 0; j < pref_chars.size(); ++j) {
            // full[j] == pref[j]
            expr_ref cLHS(full_chars.get(j), sub_m);
            expr_ref cRHS(pref_chars.get(j), sub_m);
            expr_ref _e(sub_m.mk_eq(cLHS, cRHS), sub_m);
            branch.push_back(_e);
        }

        expr_ref final_diseq(mk_and(branch), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        TRACE("str_fl", tout << "inserting into fixed_lesson" <<std::endl;);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(PFUN, f, f));

        return true;
    }

    bool theory_str::fixed_length_reduce_negative_prefix(smt::kernel & subsolver, expr_ref f, expr_ref & cex) {
        ast_manager & m = get_manager();

        ast_manager & sub_m = subsolver.m();

        expr * pref = nullptr, *full = nullptr;
        VERIFY(u.str.is_prefix(f, pref, full));

        expr_ref haystack(full, m);
        expr_ref needle(pref, m);

        expr_ref_vector full_chars(m), pref_chars(m);
        if (!fixed_length_reduce_string_term(subsolver, haystack, full_chars, cex)
                || !fixed_length_reduce_string_term(subsolver, needle, pref_chars, cex)) {
            return false;
        }

        if (pref_chars.size() == 0) {
            // all strings startwith the empty one
            cex = m.mk_or(m.mk_not(f), m.mk_not(ctx.mk_eq_atom(mk_strlen(pref), mk_int(0))));
            th_rewriter m_rw(m);
            m_rw(cex);
            return false;
        }

        if (full_chars.size() == 0 && pref_chars.size() > 0) {
            // the empty string doesn't "stratwith" any non-empty string
            return true;
        }

        if (full_chars.size() < pref_chars.size()) {
            // a string can't startwith a longer one
            // X startswith Y -> len(X) >= len(Y)
            return true;
        }

        expr_ref_vector branch(m);
        for (unsigned j = 0; j < pref_chars.size(); ++j) {
            // full[j] == pref[j]
            expr_ref cLHS(full_chars.get(j), sub_m);
            expr_ref cRHS(pref_chars.get(j), sub_m);
            expr_ref _e(sub_m.mk_eq(cLHS, cRHS), sub_m);
            branch.push_back(_e);
        }

        expr_ref final_diseq(mk_not(sub_m, mk_and(branch)), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        TRACE("str_fl", tout << "inserting into fixed_lesson" <<std::endl;);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(NFUN, f, f));

        return true;
    }

    bool theory_str::fixed_length_reduce_contains(smt::kernel & subsolver, expr_ref f, expr_ref & cex) {
        ast_manager & m = get_manager();

        ast_manager & sub_m = subsolver.m();

        expr * full = nullptr;
        expr * small = nullptr;
        VERIFY(u.str.is_contains(f, full, small));

        expr_ref haystack(full, m);
        expr_ref needle(small, m);

        expr_ref_vector haystack_chars(m), needle_chars(m);
        if (!fixed_length_reduce_string_term(subsolver, haystack, haystack_chars, cex)
                || !fixed_length_reduce_string_term(subsolver, needle, needle_chars, cex)) {
            return false;
        }

        if (needle_chars.size() == 0) {
            // all strings "contain" the empty one
            return true;
        }

        if (haystack_chars.size() == 0 && needle_chars.size() > 0) {
            // the empty string doesn't "contain" any non-empty string
            cex = m.mk_or(m.mk_not(f), ctx.mk_eq_atom(mk_strlen(needle), mk_int(0)),
                    m_autil.mk_ge(mk_strlen(haystack), mk_int(0)));
            th_rewriter m_rw(m);
            m_rw(cex);
            return false;
        }

        if (needle_chars.size() > haystack_chars.size()) {
            // a string can't contain a longer one
            // X contains Y -> len(X) >= len(Y)
            expr_ref minus_one(m_autil.mk_numeral(rational::minus_one(), true), m);
            expr_ref zero(m_autil.mk_numeral(rational::zero(), true), m);
            expr_ref lens(m_autil.mk_add(mk_strlen(haystack), m_autil.mk_mul(minus_one, mk_strlen(needle))), m);
            cex = m.mk_or(m.mk_not(f), m_autil.mk_ge(lens, zero));
            th_rewriter m_rw(m);
            m_rw(cex);
            return false;
        }
        // find all positions at which `needle` could occur in `haystack`
        expr_ref_vector branches(m);
        for (unsigned i = 0; i <= (haystack_chars.size() - needle_chars.size()); ++i) {
            // i defines the offset into haystack_chars
            expr_ref_vector branch(m);
            for (unsigned j = 0; j < needle_chars.size(); ++j) {
                // needle[j] == haystack[i+j]
                ENSURE(i+j < haystack_chars.size());
                expr_ref cLHS(needle_chars.get(j), sub_m);
                expr_ref cRHS(haystack_chars.get(i+j), sub_m);
                expr_ref _e(sub_m.mk_eq(cLHS, cRHS), sub_m);
                branch.push_back(_e);
            }
            branches.push_back(mk_and(branch));
        }

        expr_ref final_diseq(mk_or(branches), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        TRACE("str_fl", tout << "inserting into fixed_lesson" <<std::endl;);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(PFUN, f, f));

        return true;
    }

    bool theory_str::fixed_length_reduce_negative_contains(smt::kernel & subsolver, expr_ref f, expr_ref & cex) {
        ast_manager & m = get_manager();

        ast_manager & sub_m = subsolver.m();

        expr * small = nullptr, *full = nullptr;
        VERIFY(u.str.is_contains(f, full, small));

        expr_ref haystack(full, m);
        expr_ref needle(small, m);

        expr_ref_vector haystack_chars(m), needle_chars(m);
        if (!fixed_length_reduce_string_term(subsolver, haystack, haystack_chars, cex)
                || !fixed_length_reduce_string_term(subsolver, needle, needle_chars, cex)) {
            return false;
        }

        if (needle_chars.size() == 0) {
            // all strings "contain" the empty one
            cex = m.mk_or(m.mk_not(f), m.mk_not(ctx.mk_eq_atom(mk_strlen(needle), mk_int(0))));
            ctx.get_rewriter()(cex);
            return false;
        }

        if (haystack_chars.size() == 0 && needle_chars.size() > 0) {
            // the empty string doesn't "contain" any non-empty string
            return true;
        }

        if (needle_chars.size() > haystack_chars.size()) {
            // a string can't contain a longer one
            // X contains Y -> len(X) >= len(Y)
            return true;
        }


        // find all positions at which `needle` could occur in `haystack`
        expr_ref_vector branches(m);
        for (unsigned i = 0; i <= (haystack_chars.size() - needle_chars.size()); ++i) {
            // i defines the offset into haystack_chars
            expr_ref_vector branch(m);
            for (unsigned j = 0; j < needle_chars.size(); ++j) {
                // needle[j] == haystack[i+j]
                ENSURE(i+j < haystack_chars.size());
                expr_ref cLHS(needle_chars.get(j), sub_m);
                expr_ref cRHS(haystack_chars.get(i+j), sub_m);
                expr_ref _e(sub_m.mk_eq(cLHS, cRHS), sub_m);
                branch.push_back(_e);
            }
            branches.push_back(mk_and(branch));
        }

        expr_ref final_diseq(mk_not(sub_m, mk_or(branches)), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        TRACE("str_fl", tout << "inserting into fixed_lesson" <<std::endl;);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(NFUN, f, f));

        return true;
    }

    static inline void add_next(u_map<expr*>& next, expr_ref_vector& trail, unsigned idx, expr* cond, ast_manager & m) {
        expr* acc;
        if (!m.is_true(cond) && next.find(idx, acc)) {
            expr* args[2] = { cond, acc };
            cond = mk_or(m, 2, args);
        }
        trail.push_back(cond);
        next.insert(idx, cond);

    }

    bool theory_str::fixed_length_reduce_regex_membership(smt::kernel & subsolver, expr_ref f, expr_ref & cex, bool polarity) {
        ast_manager & m = get_manager();

        ast_manager & sub_m = subsolver.m();

        expr * str = nullptr, *re = nullptr;
        VERIFY(u.str.is_in_re(f, str, re));

        // TODO reuse some of the automaton framework from theory_str_regex
        eautomaton * aut = m_mk_aut(re);
        aut->compress();

        expr_ref_vector str_chars(m);
        if (!fixed_length_reduce_string_term(subsolver, str, str_chars, cex)) {
            return false;
        }

        if (str_chars.empty()) {
            // check 0-length solution
            bool zero_solution = false;
            unsigned initial_state = aut->init();
            if (aut->is_final_state(initial_state)) {
                zero_solution = true;
            } else {
                unsigned_vector eps_states;
                aut->get_epsilon_closure(initial_state, eps_states);
                for (unsigned state : eps_states) {
                    if (aut->is_final_state(state)) {
                        zero_solution = true;
                        break;
                    }
                }
            }
            if (!zero_solution && polarity) {
                TRACE("str_fl", tout << "contradiction: regex has no zero-length solutions, but our string must be a solution" << std::endl;);
                cex = m.mk_or(m.mk_not(f), m.mk_not(ctx.mk_eq_atom(mk_strlen(str), mk_int(0))));
                ctx.get_rewriter()(cex);
                return false;
            } else if (zero_solution && !polarity) {
                TRACE("str_fl", tout << "contradiction: regex has zero-length solutions, but our string must not be a solution" << std::endl;);
                cex = m.mk_or(f, m.mk_not(ctx.mk_eq_atom(mk_strlen(str), mk_int(0))));
                ctx.get_rewriter()(cex);
                return false;
            } else {
                TRACE("str_fl", tout << "regex constraint satisfied without asserting constraints to subsolver" << std::endl;);
                return true;
            }
        } else {
            expr_ref_vector trail(m);
            u_map<expr*> maps[2];
            bool select_map = false;
            expr_ref cond(m);
            eautomaton::moves mvs;
            maps[0].insert(aut->init(), m.mk_true());
            // is_accepted(a, aut) & some state in frontier is final.

            for (auto& ch : str_chars) {
                u_map<expr*>& frontier = maps[select_map];
                u_map<expr*>& next = maps[!select_map];
                select_map = !select_map;
                next.reset();
                u_map<expr*>::iterator it = frontier.begin(), end = frontier.end();
                for (; it != end; ++it) {
                    mvs.reset();
                    unsigned state = it->m_key;
                    expr*    acc  = it->m_value;
                    aut->get_moves_from(state, mvs, false);
                    for (eautomaton::move& mv : mvs) {
                        SASSERT(mv.t());
                        if (mv.t()->is_char() && m.is_value(mv.t()->get_char()) && m.is_value(ch)) {
                            if (mv.t()->get_char() == ch) {
                                add_next(next, trail, mv.dst(), acc, sub_m);
                            }
                            else {
                                continue;
                            }
                        }
                        else {
                            cond = mv.t()->accept(ch);
                            if (m.is_false(cond)) {
                                continue;
                            }
                            if (m.is_true(cond)) {
                                add_next(next, trail, mv.dst(), acc, sub_m);
                                continue;
                            }
                            expr* args[2] = { cond, acc };
                            cond = mk_and(m, 2, args);
                            add_next(next, trail, mv.dst(), cond, sub_m);
                        }
                    }
                }
            }
            u_map<expr*> const& frontier = maps[select_map];
            expr_ref_vector ors(sub_m);
            for (auto const& kv : frontier) {
                unsigned_vector states;
                bool has_final = false;
                aut->get_epsilon_closure(kv.m_key, states);
                for (unsigned i = 0; i < states.size() && !has_final; ++i) {
                    has_final = aut->is_final_state(states[i]);
                }
                if (has_final) {
                    ors.push_back(kv.m_value);
                }
            }
            expr_ref result(mk_or(ors), sub_m);
            th_rewriter rw(sub_m);
            rw(result);
            TRACE("str_fl", tout << "regex path constraint: " << mk_pp(result, sub_m) << std::endl;);

            if (sub_m.is_false(result)) {
                // There are no solutions of that length in the automaton.
                // If the membership constraint is true, we assert a conflict clause.
                // If the membership constraint is false, we ignore the constraint.
                if (polarity) {
                    // Decompose `str` into its components if it is a concatenation of terms.
                    // This fixes cases where the length of S in (S in RE) might be correct
                    // if the lengths of components of S are assigned in a different way.
                    expr_ref_vector str_terms(m);
                    expr_ref_vector str_terms_eq_len(m);
                    str_terms.push_back(str);
                    while (!str_terms.empty()) {
                        expr* str_term = str_terms.back();
                        str_terms.pop_back();
                        expr* arg0;
                        expr* arg1;
                        if (u.str.is_concat(str_term, arg0, arg1)) {
                            str_terms.push_back(arg0);
                            str_terms.push_back(arg1);
                        } else {
                            rational termLen;
                            if (fixed_length_get_len_value(str_term, termLen)) {
                                str_terms_eq_len.push_back(ctx.mk_eq_atom(mk_strlen(str_term), mk_int(termLen)));
                            } else {
                                // this is strange, since we knew the length of `str` in order to get here
                                cex = expr_ref(m_autil.mk_ge(mk_strlen(str_term), mk_int(0)), m);
                                return false;
                            }
                        }
                    }

                    cex = m.mk_or(m.mk_not(f), m.mk_not(mk_and(str_terms_eq_len)));
                    ctx.get_rewriter()(cex);
                    return false;
                } else {
                    TRACE("str_fl", tout << "regex constraint satisfied without asserting constraints to subsolver" << std::endl;);
                    return true;
                }
            } else {
                if (polarity) {
                    fixed_length_assumptions.push_back(result);
                    fixed_length_lesson.insert(result, std::make_tuple(PFUN, f, f));
                } else {
                    fixed_length_assumptions.push_back(sub_m.mk_not(result));
                    fixed_length_lesson.insert(sub_m.mk_not(result), std::make_tuple(NFUN, f, f));
                }
                return true;
            }
        }
    }

    /*
     * Expressions in the vector eqc_chars exist only in the subsolver.
     * If this method returns false, a conflict clause is returned in cex;
     * this conflict clause exists in the main solver.
     */
    bool theory_str::fixed_length_reduce_string_term(smt::kernel & subsolver, expr * term,
            expr_ref_vector & eqc_chars, expr_ref & cex) {
        ast_manager & m = get_manager();

        ast_manager & sub_m = subsolver.m();

        expr * arg0;
        expr * arg1;
        expr * arg2;

        zstring strConst;
        if (u.str.is_string(term, strConst)) {
            for (unsigned i = 0; i < strConst.length(); ++i) {
                expr_ref chTerm(u.mk_char(strConst[i]), m);
                eqc_chars.push_back(chTerm);
                fixed_length_subterm_trail.push_back(chTerm);
            }
        } else if (to_app(term)->get_num_args() == 0 && !u.str.is_string(term)) {
            // this is a variable; get its length and create/reuse character terms
            expr_ref_vector * chars = nullptr;
            if (!var_to_char_subterm_map.find(term, chars)) {
                rational varLen_value;
                bool var_hasLen = fixed_length_get_len_value(term, varLen_value);
                if (!var_hasLen || varLen_value.is_neg()) {
                    TRACE("str_fl", tout << "variable " << mk_pp(term, m) << " has no length assignment or impossible length assignment - asserting conflict axiom" << std::endl;);
                    cex = expr_ref(m_autil.mk_ge(mk_strlen(term), mk_int(0)), m);
                    return false;
                }
                TRACE("str_fl", tout << "creating character terms for variable " << mk_pp(term, m) << ", length = " << varLen_value << std::endl;);
                chars = alloc(expr_ref_vector, m);
                for (rational i = rational::zero(); i < varLen_value; ++i) {
                    // TODO we can probably name these better for the sake of debugging
                    expr_ref ch(mk_fresh_const("char", u.mk_char_sort()), m);
                    chars->push_back(ch);
                    fixed_length_subterm_trail.push_back(ch);
                }
                var_to_char_subterm_map.insert(term, chars);
                fixed_length_used_len_terms.insert(term, varLen_value);
            }
            for (auto c : *chars) {
                eqc_chars.push_back(c);
            }
        } else if (u.str.is_concat(term, arg0, arg1)) {
            expr_ref first(arg0, sub_m);
            expr_ref second(arg1, sub_m);
            expr_ref_vector chars0(m), chars1(m);
            if (!fixed_length_reduce_string_term(subsolver, first, chars0, cex)
                    || !fixed_length_reduce_string_term(subsolver, second, chars1, cex)) {
                return false;
            }
            eqc_chars.append(chars0);
            eqc_chars.append(chars1);
        } else if (u.str.is_extract(term, arg0, arg1, arg2)) {
            // (str.substr Base Pos Len)
            expr_ref first(arg0, sub_m);
            expr_ref second(arg1, sub_m);
            expr_ref third(arg2, sub_m);
            expr_ref_vector base_chars(m);
            if (!fixed_length_reduce_string_term(subsolver, first, base_chars, cex)) {
                return false;
            }
            arith_value v(m);
            v.init(&get_context());
            rational pos, len;
            bool pos_exists = v.get_value(arg1, pos);
            bool len_exists = v.get_value(arg2, len);
            if (!pos_exists) {
                cex = expr_ref(m.mk_or(m_autil.mk_ge(arg1, mk_int(0)), m_autil.mk_le(arg1, mk_int(0))), m);
                return false;
            }
            if (!len_exists) {
                cex = expr_ref(m.mk_or(m_autil.mk_ge(arg2, mk_int(0)), m_autil.mk_le(arg2, mk_int(0))), m);
                return false;
            }
            TRACE("str_fl", tout << "reduce substring term: base=" << mk_pp(term, m) << " (length="<<base_chars.size()<<"), pos=" << pos.to_string() << ", len=" << len.to_string() << std::endl;);
            // Case 1: pos < 0 or pos >= strlen(base) or len < 0
            // ==> (Substr ...) = ""
            if (pos.is_neg() || pos >= rational(base_chars.size()) || len.is_neg()) {
                eqc_chars.reset();
                return true;
            }
            else if (!pos.is_unsigned() || !len.is_unsigned()) {
                return false;
            } else {
                unsigned _pos = pos.get_unsigned();
                unsigned _len = len.get_unsigned();
                if (_pos + _len < _pos) 
                    return false;
                if (_pos + _len >= base_chars.size()) {
                    // take as many characters as possible up to the end of base_chars
                    for (unsigned i = _pos; i < base_chars.size(); ++i) {
                        eqc_chars.push_back(base_chars.get(i));
                    }
                } else {
                    for (unsigned i = _pos; i < _pos + _len; ++i) {
                        eqc_chars.push_back(base_chars.get(i));
                    }
                }
            }
        } else if (u.str.is_at(term, arg0, arg1)) {
            // (str.at Base Pos)
            expr_ref base(arg0, sub_m);
            expr_ref pos(arg1, sub_m);
            expr_ref_vector base_chars(m);
            if (!fixed_length_reduce_string_term(subsolver, base, base_chars, cex)) {
                return false;
            }
            arith_value v(m);
            v.init(&get_context());
            rational pos_value;
            bool pos_exists = v.get_value(pos, pos_value);
            if (!pos_exists) {
                cex = m.mk_or(m_autil.mk_ge(pos, mk_int(0)), m_autil.mk_le(pos, mk_int(0)));
                return false;
            }
            TRACE("str_fl", tout << "reduce str.at: base=" << mk_pp(base, m) << ", pos=" << pos_value.to_string() << std::endl;);
            if (pos_value.is_neg() || pos_value >= rational(base_chars.size())) {
                // return the empty string
                eqc_chars.reset();
            }
            else if (!pos_value.is_unsigned()) {
                return false;
            } else {
                eqc_chars.push_back(base_chars.get(pos_value.get_unsigned()));
            }
            return true;
        } else if (u.str.is_itos(term, arg0)) {
            expr_ref i(arg0, m);
            arith_value v(m);
            v.init(&get_context());
            rational iValue;
            bool iValue_exists = v.get_value(i, iValue);
            if (!iValue_exists) {
                cex = expr_ref(m.mk_or(m_autil.mk_ge(arg0, mk_int(0)), m_autil.mk_le(arg0, mk_int(0))), m);
                return false;
            }
            rational termLen;
            bool termLen_exists = v.get_value(mk_strlen(term), termLen);
            if(!termLen_exists) {
                cex = expr_ref(m.mk_or(m_autil.mk_ge(mk_strlen(term), mk_int(0)), m_autil.mk_le(mk_strlen(term), mk_int(0))), m);
                return false;
            }
            TRACE("str_fl", tout << "reduce int.to.str: n=" << iValue << std::endl;);
            if (iValue.is_neg()) {
                if (!termLen.is_zero()) {
                    // conflict
                    cex = expr_ref(m.mk_not(m.mk_and(m_autil.mk_le(arg0, mk_int(-1)), m.mk_not(mk_strlen(term)))), m);
                    return false;
                }
                // return the empty string
                eqc_chars.reset();
                return true;
            } else {
                if (termLen != iValue.get_num_decimal()) {
                    // conflict
                    cex = expr_ref(m.mk_not(m.mk_and(get_context().mk_eq_atom(mk_strlen(term), mk_int(termLen)), get_context().mk_eq_atom(arg0, mk_int(iValue)))), m);
                    return false;
                }
                // convert iValue to a constant
                zstring iValue_str(iValue.to_string());
                for (unsigned idx = 0; idx < iValue_str.length(); ++idx) {
                    expr_ref chTerm(u.mk_char(iValue_str[idx]), m);
                    eqc_chars.push_back(chTerm);
                }
                return true;
            }
        } else {
            TRACE("str_fl", tout << "string term " << mk_pp(term, m) << " handled as uninterpreted function" << std::endl;);
            expr_ref_vector *chars = nullptr;
            if (!uninterpreted_to_char_subterm_map.find(term, chars)) {
                rational ufLen_value;
                bool uf_hasLen = fixed_length_get_len_value(term, ufLen_value);
                if (!uf_hasLen || ufLen_value.is_neg()) {
                    TRACE("str_fl", tout << "uninterpreted function " << mk_pp(term, m) << " has no length assignment or impossible length assignment - asserting conflict axiom" << std::endl;);
                    cex = expr_ref(m_autil.mk_ge(mk_strlen(term), mk_int(0)), m);
                    return false;
                }
                TRACE("str_fl", tout << "creating character terms for uninterpreted function " << mk_pp(term, m) << ", length = " << ufLen_value << std::endl;);
                chars = alloc(expr_ref_vector, m);
                for (rational i = rational::zero(); i < ufLen_value; ++i) {
                    expr_ref ch(mk_fresh_const("char", u.mk_char_sort()), m);
                    chars->push_back(ch);
                    fixed_length_subterm_trail.push_back(ch);
                }
                uninterpreted_to_char_subterm_map.insert(term, chars);
                fixed_length_used_len_terms.insert(term, ufLen_value);
            }
            for (auto c : *chars) {
                eqc_chars.push_back(c);
            }
        }
        return true;
    }

    bool theory_str::fixed_length_reduce_eq(smt::kernel & subsolver, expr_ref lhs, expr_ref rhs, expr_ref & cex) {
        ast_manager & m = get_manager();

        ast_manager & sub_m = subsolver.m();

        expr_ref_vector lhs_chars(m), rhs_chars(m);

        if (!fixed_length_reduce_string_term(subsolver, lhs, lhs_chars, cex)
                || !fixed_length_reduce_string_term(subsolver, rhs, rhs_chars, cex)) {
            return false;
        }

        if (lhs_chars.size() != rhs_chars.size()) {
            TRACE("str_fl", tout << "length information inconsistent: " << mk_pp(lhs, m) << " has " << lhs_chars.size() <<
                    " chars, " << mk_pp(rhs, m) << " has " << rhs_chars.size() << " chars" << std::endl;);
            // equal strings ought to have equal lengths
            cex = m.mk_or(m.mk_not(ctx.mk_eq_atom(lhs, rhs)), ctx.mk_eq_atom(mk_strlen(lhs), mk_strlen(rhs)));
            return false;
        }
        for (unsigned i = 0; i < lhs_chars.size(); ++i) {
            expr_ref cLHS(lhs_chars.get(i), sub_m);
            expr_ref cRHS(rhs_chars.get(i), sub_m);
            expr_ref _e(sub_m.mk_eq(cLHS, cRHS), sub_m);
            fixed_length_assumptions.push_back(_e);
            TRACE("str_fl", tout << "inserting into fixed_lesson" <<std::endl;);
            fixed_length_lesson.insert(_e, std::make_tuple(rational(i), lhs, rhs));
        }
        return true;
    }

    bool theory_str::fixed_length_reduce_diseq(smt::kernel & subsolver, expr_ref lhs, expr_ref rhs, expr_ref & cex) {
        ast_manager & m = get_manager();

        ast_manager & sub_m = subsolver.m();

        // we do generation before this check to make sure that
        // variables which only appear in disequalities show up in the model
        rational lhsLen, rhsLen;
        bool lhsLen_exists = fixed_length_get_len_value(lhs, lhsLen);
        bool rhsLen_exists = fixed_length_get_len_value(rhs, rhsLen);

        if (!lhsLen_exists) {
            cex = m_autil.mk_ge(mk_strlen(lhs), mk_int(0));
            return false;
        }

        if (!rhsLen_exists) {
            cex = m_autil.mk_ge(mk_strlen(rhs), mk_int(0));
            return false;
        }

        expr_ref_vector lhs_chars(m), rhs_chars(m);
        if (!fixed_length_reduce_string_term(subsolver, lhs, lhs_chars, cex)
                || !fixed_length_reduce_string_term(subsolver, rhs, rhs_chars, cex)) {
            return false;
        }

        if (lhsLen != rhsLen) {
            TRACE("str", tout << "skip disequality: len(lhs) = " << lhsLen << ", len(rhs) = " << rhsLen << std::endl;);
            return true;
        }

        SASSERT(lhs_chars.size() == rhs_chars.size());
        expr_ref_vector diseqs(m);
        for (unsigned i = 0; i < lhs_chars.size(); ++i) {
            expr_ref cLHS(lhs_chars.get(i), sub_m);
            expr_ref cRHS(rhs_chars.get(i), sub_m);
            diseqs.push_back(sub_m.mk_not(sub_m.mk_eq(cLHS, cRHS)));
        }

        expr_ref final_diseq(mk_or(diseqs), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        TRACE("str_fl", tout << "inserting into fixed_lesson" <<std::endl;);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(NEQ, lhs, rhs));

        return true;
    }

    lbool theory_str::fixed_length_model_construction(expr_ref_vector formulas, expr_ref_vector &precondition,
            expr_ref_vector& free_variables,
            obj_map<expr, zstring> &model, expr_ref_vector &cex) {

        ast_manager & m = get_manager();

        TRACE("str",
            ast_manager & m = get_manager();
            tout << "dumping all formulas:" << std::endl;
            for (expr_ref_vector::iterator i = formulas.begin(); i != formulas.end(); ++i) {
                expr * ex = *i;
                tout << mk_pp(ex, m) << (ctx.is_relevant(ex) ? "" : " (NOT REL)") << std::endl;
            }
        );

        fixed_length_subterm_trail.reset();
        fixed_length_used_len_terms.reset();
        fixed_length_assumptions.reset();

        for (auto& kv: var_to_char_subterm_map) dealloc(kv.m_value);
        var_to_char_subterm_map.reset();
        for (auto& kv: uninterpreted_to_char_subterm_map) dealloc(kv.m_value);
        uninterpreted_to_char_subterm_map.reset();
        fixed_length_lesson.reset();

        // All reduced Boolean formulas in the current assignment
        expr_ref_vector fixed_length_reduced_boolean_formulas(m);

        // Boolean formulas on which to apply abstraction refinement.
        expr_ref_vector abstracted_boolean_formulas(m);

        smt_params subsolver_params;
        subsolver_params.m_string_solver = symbol("char");
        smt::kernel subsolver(m, subsolver_params);
        subsolver.set_logic(symbol("QF_S"));
        sort * str_sort = u.str.mk_string_sort();
        sort * bool_sort = m.mk_bool_sort();

        for (expr * var : free_variables) {
            TRACE("str_fl", tout << "initialize free variable " << mk_pp(var, m) << std::endl;);
            rational var_lenVal;
            if (!fixed_length_get_len_value(var, var_lenVal)) {
                TRACE("str_fl", tout << "free variable " << mk_pp(var, m) << " has no length assignment" << std::endl;);
                expr_ref var_len_assertion(m_autil.mk_ge(mk_strlen(var), mk_int(0)), m);
                assert_axiom(var_len_assertion);
                add_persisted_axiom(var_len_assertion);
                return l_undef;
            }
            expr_ref_vector var_chars(m);
            expr_ref str_counterexample(m);
            if (!fixed_length_reduce_string_term(subsolver, var, var_chars, str_counterexample)) {
                TRACE("str_fl", tout << "free variable " << mk_pp(var, m) << " caused a conflict; asserting and continuing" << std::endl;);
                assert_axiom(str_counterexample);
                return l_undef;
            }
        }

        for (expr * f : formulas) {
            if (!get_context().is_relevant(f)) {
                expr * subformula = nullptr;
                if (m.is_not(f, subformula)) {
                    if (!get_context().is_relevant(subformula)) {
                        TRACE("str_fl", tout << "skip reducing formula " << mk_pp(f, m) << ", not relevant (and neither is its subformula)" << std::endl;);
                        continue;
                    } else {
                        TRACE("str_fl", tout << "considering formula " << mk_pp(f, m) << ", its subformula is relevant but it is not" << std::endl;);
                    }
                } else {
                    TRACE("str_fl", tout << "skip reducing formula " << mk_pp(f, m) << ", not relevant" << std::endl;);
                    continue;
                }
            }
            // reduce string formulas only. ignore others
            sort * fSort = f->get_sort();
            if (fSort == bool_sort && !is_quantifier(f)) {
                // extracted terms
                expr * subterm;
                expr * lhs;
                expr * rhs;
                if (m.is_eq(f, lhs, rhs)) {
                    sort * lhs_sort = lhs->get_sort();
                    if (lhs_sort == str_sort) {
                        TRACE("str_fl", tout << "reduce string equality: " << mk_pp(lhs, m) << " == " << mk_pp(rhs, m) << std::endl;);
                        expr_ref cex(m);
                        expr_ref left(lhs, m);
                        expr_ref right(rhs, m);
                        if (!fixed_length_reduce_eq(subsolver, left, right, cex)) {
                            // missing a side condition. assert it and return unknown
                            assert_axiom(cex);
                            add_persisted_axiom(cex);
                            return l_undef;
                        }
                        fixed_length_reduced_boolean_formulas.push_back(f);
                    } else {
                        TRACE("str_fl", tout << "skip reducing formula " << mk_pp(f, m) << ", not an equality over strings" << std::endl;);
                    }
                } else if (u.str.is_in_re(f)) {
                    TRACE("str_fl", tout << "reduce regex membership: " << mk_pp(f, m) << std::endl;);
                    expr_ref cex_clause(m);
                    expr_ref re(f, m);
                    if (!fixed_length_reduce_regex_membership(subsolver, re, cex_clause, true)) {
                        assert_axiom(cex_clause);
                        add_persisted_axiom(cex_clause);
                        return l_undef;
                    }
                    fixed_length_reduced_boolean_formulas.push_back(f);
                } else if (u.str.is_contains(f)) {
                    // TODO in some cases (e.g. len(haystack) is only slightly greater than len(needle))
                    // we might be okay to assert the full disjunction because there are very few disjuncts
                    if (m_params.m_FixedLengthRefinement) {
                        TRACE("str_fl", tout << "abstracting out positive contains: " << mk_pp(f, m) << std::endl;);
                        abstracted_boolean_formulas.push_back(f);
                    } else {
                        TRACE("str_fl", tout << "reduce positive contains: " << mk_pp(f, m) << std::endl;);
                        expr_ref cex(m);
                        expr_ref cont(f, m);
                        if (!fixed_length_reduce_contains(subsolver, cont, cex)) {
                            assert_axiom(cex);
                            add_persisted_axiom(cex);
                            return l_undef;
                        }
                        fixed_length_reduced_boolean_formulas.push_back(f);
                    }
                } else if (u.str.is_prefix(f)) {
                    TRACE("str_fl", tout << "reduce positive prefix: " << mk_pp(f, m) << std::endl;);
                    expr_ref cex(m);
                    expr_ref pref(f, m);
                    if (!fixed_length_reduce_prefix(subsolver, pref, cex)) {
                        assert_axiom(cex);
                        add_persisted_axiom(cex);
                        return l_undef;
                    }
                    fixed_length_reduced_boolean_formulas.push_back(f);
                } else if (u.str.is_suffix(f)) {
                    TRACE("str_fl", tout << "reduce positive suffix: " << mk_pp(f, m) << std::endl;);
                    expr_ref cex(m);
                    expr_ref suf(f, m);
                    if (!fixed_length_reduce_suffix(subsolver, suf, cex)) {
                        assert_axiom(cex);
                        add_persisted_axiom(cex);
                        return l_undef;
                    }
                    fixed_length_reduced_boolean_formulas.push_back(f);
                }else if (m.is_not(f, subterm)) {
                    // if subterm is a string formula such as an equality, reduce it as a disequality
                    if (m.is_eq(subterm, lhs, rhs)) {
                        sort * lhs_sort = lhs->get_sort();
                        if (lhs_sort == str_sort) {
                            TRACE("str_fl", tout << "reduce string disequality: " << mk_pp(lhs, m) << " != " << mk_pp(rhs, m) << std::endl;);
                            expr_ref cex(m);
                            expr_ref left(lhs, m);
                            expr_ref right(rhs, m);
                            if (!fixed_length_reduce_diseq(subsolver, left, right, cex)) {
                                // missing a side condition. assert it and return unknown
                                assert_axiom(cex);
                                add_persisted_axiom(cex);
                                return l_undef;
                            }
                            fixed_length_reduced_boolean_formulas.push_back(f);
                        }
                    } else if (u.str.is_in_re(subterm)) {
                        TRACE("str_fl", tout << "reduce negative regex membership: " << mk_pp(f, m) << std::endl;);
                        expr_ref cex_clause(m);
                        expr_ref re(subterm, m);
                        if (!fixed_length_reduce_regex_membership(subsolver, re, cex_clause, false)) {
                            assert_axiom(cex_clause);
                            add_persisted_axiom(cex_clause);
                            return l_undef;
                        }
                        fixed_length_reduced_boolean_formulas.push_back(f);
                    } else if (u.str.is_contains(subterm)) {
                        TRACE("str_fl", tout << "reduce negative contains: " << mk_pp(subterm, m) << std::endl;);
                        expr_ref cex(m);
                        expr_ref cont(subterm, m);
                        if (!fixed_length_reduce_negative_contains(subsolver, cont, cex)) {
                            assert_axiom(cex);
                            add_persisted_axiom(cex);
                            return l_undef;
                        }
                        fixed_length_reduced_boolean_formulas.push_back(f);
                    } else if (u.str.is_prefix(subterm)) {
                        TRACE("str_fl", tout << "reduce negative prefix: " << mk_pp(subterm, m) << std::endl;);
                        expr_ref cex(m);
                        expr_ref pref(subterm, m);
                        if (!fixed_length_reduce_negative_prefix(subsolver, pref, cex)) {
                            assert_axiom(cex);
                            add_persisted_axiom(cex);
                            return l_undef;
                        }
                        fixed_length_reduced_boolean_formulas.push_back(f);
                    } else if (u.str.is_suffix(subterm)) {
                        TRACE("str_fl", tout << "reduce negative suffix: " << mk_pp(subterm, m) << std::endl;);
                        expr_ref cex(m);
                        expr_ref suf(subterm, m);
                        if (!fixed_length_reduce_negative_suffix(subsolver, suf, cex)) {
                            assert_axiom(cex);
                            add_persisted_axiom(cex);
                            return l_undef;
                        }
                        fixed_length_reduced_boolean_formulas.push_back(f);
                    } else {
                        TRACE("str_fl", tout << "skip reducing formula " << mk_pp(f, m) << ", not a boolean formula we handle" << std::endl;);
                    }
                } else {
                    TRACE("str_fl", tout << "skip reducing formula " << mk_pp(f, m) << ", not a boolean formula we handle" << std::endl;);
                    continue;
                }
            } else {
                TRACE("str_fl", tout << "skip reducing formula " << mk_pp(f, m) << ", not relevant to strings" << std::endl;);
                continue;
            }
        }

        // Check consistency of all string-integer conversion terms wrt. integer theory before we solve,
        // possibly generating additional constraints for the bit-vector solver.
        {
            arith_value v(get_manager());
            v.init(&get_context());
            for (auto e : string_int_conversion_terms) {
                TRACE("str_fl", tout << "pre-run check str-int term " << mk_pp(e, get_manager()) << std::endl;);
                expr* _arg;
                if (u.str.is_stoi(e, _arg)) {
                    expr_ref arg(_arg, m);
                    rational slen;
                    if (!fixed_length_get_len_value(arg, slen)) {
                        expr_ref stoi_cex(m_autil.mk_ge(mk_strlen(arg), mk_int(0)), m);
                        assert_axiom(stoi_cex);
                        add_persisted_axiom(stoi_cex);
                        return l_undef;
                    }
                    TRACE("str_fl", tout << "length of term is " << slen << std::endl;);

                    rational ival;
                    if (v.get_value(e, ival)) {
                        TRACE("str_fl", tout << "integer theory assigns " << ival << " to " << mk_pp(e, get_manager()) << std::endl;);
                        // if ival is non-negative, because we know the length of arg, we can add a character constraint for arg
                        if (ival.is_nonneg()) {
                            zstring ival_str(ival.to_string());
                            zstring padding;
                            for (rational i = rational::zero(); i < slen - rational(ival_str.length()); ++i) {
                                padding = padding + zstring("0");
                            }
                            zstring arg_val = padding + ival_str;
                            expr_ref stoi_cex(m);
                            expr_ref arg_char_expr(mk_string(arg_val), m);
                            
                            // Add (e == ival) as a precondition.
                            precondition.push_back(m.mk_eq(e, mk_int(ival)));
                            // Assert (arg == arg_chars) in the subsolver.
                            if (!fixed_length_reduce_eq(subsolver, arg, arg_char_expr, stoi_cex)) {
                                // Counterexample: (str.to_int S) == ival AND len(S) == slen cannot both be true.
                                stoi_cex = expr_ref(m.mk_not(m.mk_and(
                                    m.mk_eq(e, mk_int(ival)), 
                                    m.mk_eq(mk_strlen(arg), mk_int(slen))
                                )), m);
                                assert_axiom(stoi_cex);
                                add_persisted_axiom(stoi_cex);

                                return l_undef;
                            }

                            fixed_length_reduced_boolean_formulas.push_back(m.mk_eq(e, mk_int(ival)));
                        }
                    } else {
                        TRACE("str_fl", tout << "integer theory has no assignment for " << mk_pp(e, get_manager()) << std::endl;);
                        // consistency needs to be checked after the string is assigned
                    }
                } else if (u.str.is_to_code(e, _arg)) {
                    expr_ref arg(_arg, m);
                    rational ival;
                    if (v.get_value(e, ival)) {
                        TRACE("str_fl", tout << "integer theory assigns " << ival << " to " << mk_pp(e, m) << std::endl;);
                        if (ival >= rational::zero() && ival <= rational(u.max_char())) {
                            zstring ival_str(ival.get_unsigned());
                            expr_ref arg_char_expr(mk_string(ival_str), m);
                            expr_ref stoi_cex(m);
                            // Add (e == ival) as a precondition
                            precondition.push_back(m.mk_eq(e, mk_int(ival)));
                            if (!fixed_length_reduce_eq(subsolver, arg, arg_char_expr, stoi_cex)) {
                                // Counterexample: (str.to_code arg) == ival AND arg == arg_char_expr cannot both be true.
                                stoi_cex = expr_ref(m.mk_not(m.mk_and(m.mk_eq(e, mk_int(ival)), m.mk_eq(arg, arg_char_expr))), m);
                                assert_axiom(stoi_cex);
                                add_persisted_axiom(stoi_cex);
                                return l_undef;
                            }
                            fixed_length_reduced_boolean_formulas.push_back(m.mk_eq(e, mk_int(ival)));
                        }
                    } else {
                        TRACE("str_fl", tout << "integer theory has no assignment for " << mk_pp(e, m) << std::endl;);
                        // consistency needs to be checked after the string is assigned
                    }
                } else if (u.str.is_itos(e, _arg)) {
                    expr_ref arg(_arg, m);
                    rational slen;
                    if (!fixed_length_get_len_value(e, slen)) {
                        expr_ref stoi_cex(m_autil.mk_ge(mk_strlen(e), mk_int(0)), m);
                        assert_axiom(stoi_cex);
                        add_persisted_axiom(stoi_cex);
                        return l_undef;
                    }
                    TRACE("str_fl", tout << "length of term is " << slen << std::endl;);
                    rational ival;
                    if (v.get_value(arg, ival)) {
                        TRACE("str_fl", tout << "integer theory assigns " << ival << " to " << mk_pp(arg, get_manager()) << std::endl;);
                        zstring ival_str;
                        if (ival.is_neg()) {
                            // e must be the empty string, i.e. have length 0
                            ival_str = zstring("");
                        } else {
                            // e must be equal to the string representation of ival
                            ival_str = zstring(ival.to_string());
                        }
                        // Add (arg == ival) as a precondition.
                        precondition.push_back(m.mk_eq(arg, mk_int(ival)));
                        // Assert (e == ival_str) in the subsolver.
                        expr_ref itos_cex(m);
                        expr_ref _e(e, m);
                        expr_ref arg_char_expr(mk_string(ival_str), m);
                        if (!fixed_length_reduce_eq(subsolver, _e, arg_char_expr, itos_cex)) {
                            // Counterexample: N in (str.from_int N) == ival AND len(str.from_int N) == slen cannot both be true.
                            itos_cex = expr_ref(m.mk_not(m.mk_and(
                                m.mk_eq(arg, mk_int(ival)), 
                                m.mk_eq(mk_strlen(e), mk_int(slen))
                            )), m);
                            assert_axiom(itos_cex);
                            add_persisted_axiom(itos_cex);
                            return l_undef;
                        }
                        fixed_length_reduced_boolean_formulas.push_back(m.mk_eq(arg, mk_int(ival)));
                    } else {
                        TRACE("str_fl", tout << "integer theory has no assignment for " << mk_pp(arg, get_manager()) << std::endl;);
                        // consistency needs to be checked after the string is assigned
                    }
                } else if (u.str.is_from_code(e, _arg)) {
                    expr_ref arg(_arg, m);
                    rational ival;
                    if (v.get_value(arg, ival)) {
                        TRACE("str_fl", tout << "integer theory assigns " << ival << " to " << mk_pp(arg, m) << std::endl;);
                        if (ival >= rational::zero() && ival <= rational(u.max_char())) {
                            zstring ival_str(ival.get_unsigned());
                            expr_ref arg_char_expr(mk_string(ival_str), m);
                            expr_ref itos_cex(m);
                            // Add (arg == ival) as a precondition
                            precondition.push_back(m.mk_eq(arg, mk_int(ival)));
                            expr_ref _e(e, m);
                            if (!fixed_length_reduce_eq(subsolver, _e, arg_char_expr, itos_cex)) {
                                // Counterexample: (str.from_code arg) == arg_char AND arg == ival cannot both be true.
                                itos_cex = expr_ref(m.mk_not(m.mk_and(m.mk_eq(arg, mk_int(ival)), m.mk_eq(e, arg_char_expr))), m);
                                assert_axiom(itos_cex);
                                add_persisted_axiom(itos_cex);
                                return l_undef;
                            }
                            fixed_length_reduced_boolean_formulas.push_back(m.mk_eq(e, mk_int(ival)));
                        }
                    } else {
                        TRACE("str_fl", tout << "integer theory has no assignment for " << mk_pp(arg, m) << std::endl;);
                        // consistency needs to be checked after the string is assigned
                    }
                }
            }
        }

        for (auto e : fixed_length_used_len_terms) {
            expr * var = &e.get_key();
            rational val = e.get_value();
            precondition.push_back(m.mk_eq(u.str.mk_length(var), mk_int(val)));
        }

        TRACE("str_fl",
              tout << "formulas asserted to subsolver:" << std::endl;
              for (auto e : fixed_length_assumptions) {
                  tout << mk_pp(e, subsolver.m()) << std::endl;
              }
              tout << "variable to character mappings:" << std::endl;
              for (auto &entry : var_to_char_subterm_map) {
                  tout << mk_pp(entry.m_key, get_manager()) << ":";
                  for (auto e : *entry.m_value) {
                      tout << " " << mk_pp(e, subsolver.m());
                  }
                  tout << std::endl;
              }
              tout << "reduced boolean formulas:" << std::endl;
              for (expr* e : fixed_length_reduced_boolean_formulas) {
                  tout << mk_pp(e, m) << std::endl;
              }
              );
        
        TRACE("str_fl", tout << "calling subsolver" << std::endl;);

        lbool subproblem_status = subsolver.check(fixed_length_assumptions);

        if (subproblem_status == l_true) {
            TRACE("str_fl", tout << "subsolver found SAT; reconstructing model" << std::endl;);
            model_ref subModel;
            subsolver.get_model(subModel);

            expr_substitution subst(m);

            //model_smt2_pp(std::cout, m, *subModel, 2);
            for (auto entry : var_to_char_subterm_map) {
                svector<unsigned> assignment;
                expr * var = entry.m_key;
                for (expr * chExpr : *(entry.m_value)) {
                    expr_ref chAssignment(subModel->get_const_interp(to_app(chExpr)->get_decl()), m);
                    unsigned n = 0;
                    if (chAssignment != nullptr && u.is_const_char(chAssignment, n)) {
                        assignment.push_back(n);
                    } else {
                        assignment.push_back((unsigned)'?');
                    }
                }
                zstring strValue(assignment.size(), assignment.data());
                model.insert(var, strValue);
                subst.insert(var, mk_string(strValue));
            }
            TRACE("str_fl",
                for (auto entry : model) {
                    tout << mk_pp(entry.m_key, m) << " = " << entry.m_value << std::endl;
                }
            );
            for (auto entry : uninterpreted_to_char_subterm_map) {
                svector<unsigned> assignment;
                expr * var = entry.m_key;
                for (expr * chExpr : *(entry.m_value)) {
                    expr_ref chAssignment(subModel->get_const_interp(to_app(chExpr)->get_decl()), m);
                    unsigned n = 0;
                    if (chAssignment != nullptr && u.is_const_char(chAssignment, n)) {
                        assignment.push_back(n);
                    } else {
                        assignment.push_back((unsigned)'?');
                    }
                }
                zstring strValue(assignment.size(), assignment.data());
                model.insert(var, strValue);
                subst.insert(var, mk_string(strValue));
            }

            // Check consistency of string-integer conversion terms after the search.
            {
                scoped_ptr<expr_replacer> replacer = mk_default_expr_replacer(m, false);
                replacer->set_substitution(&subst);
                th_rewriter rw(m);
                arith_value v(get_manager());
                v.init(&get_context());
                for (auto e : string_int_conversion_terms) {
                    TRACE("str_fl", tout << "post-run check str-int term " << mk_pp(e, get_manager()) << std::endl;);
                    expr* _arg;
                    if (u.str.is_stoi(e, _arg)) {
                        expr_ref arg(_arg, m);
                        rational ival;
                        if (v.get_value(e, ival)) {
                            expr_ref arg_subst(arg, m);
                            (*replacer)(arg, arg_subst);
                            rw(arg_subst);
                            TRACE("str_fl", tout << "ival = " << ival << ", string arg evaluates to " << mk_pp(arg_subst, m) << std::endl;);

                            zstring arg_zstr;
                            if (u.str.is_string(arg_subst, arg_zstr)) {
                                rational arg_value;
                                if (string_integer_conversion_valid(arg_zstr, arg_value)) {
                                    if (ival != arg_value) {
                                        // contradiction
                                        expr_ref cex(m.mk_not(m.mk_and(ctx.mk_eq_atom(arg, mk_string(arg_zstr)), ctx.mk_eq_atom(e, mk_int(ival)))), m);
                                        assert_axiom(cex);
                                        return l_undef;
                                    }
                                } else {
                                    if (!ival.is_minus_one()) {
                                        expr_ref cex(m.mk_not(m.mk_and(ctx.mk_eq_atom(arg, mk_string(arg_zstr)), ctx.mk_eq_atom(e, mk_int(ival)))), m);
                                        assert_axiom(cex);
                                        return l_undef;
                                    }
                                }
                            }
                        }
                    } else if (u.str.is_to_code(e, _arg)) {
                        expr_ref arg(_arg, m);
                        rational ival;
                        if (v.get_value(e, ival)) {
                            expr_ref arg_subst(arg, m);
                            (*replacer)(arg, arg_subst);
                            rw(arg_subst);
                            TRACE("str_fl", tout << "ival = " << ival << ", string arg evaluates to " << mk_pp(arg_subst, m) << std::endl;);
                            zstring arg_zstr;
                            if (u.str.is_string(arg_subst, arg_zstr)) {
                                if (ival >= rational::zero() && ival <= rational(u.max_char())) {
                                    // check that arg_subst has length 1 and that the codepoints are the same
                                    if (arg_zstr.length() != 1 || rational(arg_zstr[0]) != ival) {
                                        // contradiction
                                        expr_ref cex(m.mk_not(m.mk_and(ctx.mk_eq_atom(arg, mk_string(arg_zstr)), ctx.mk_eq_atom(e, mk_int(ival)))), m);
                                        assert_axiom(cex);
                                        return l_undef;
                                    }
                                } else {
                                    // arg_subst must not be a singleton char
                                    if (arg_zstr.length() == 1) {
                                        // contradiction
                                        expr_ref cex(m.mk_not(m.mk_and(ctx.mk_eq_atom(arg, mk_string(arg_zstr)), ctx.mk_eq_atom(e, mk_int(ival)))), m);
                                        assert_axiom(cex);
                                        return l_undef;
                                    }
                                }
                            }
                        }
                    } else if (u.str.is_itos(e, _arg)) {
                        expr_ref arg(_arg, m);
                        rational ival;
                        if (v.get_value(arg, ival)) {
                            expr_ref e_subst(e, m);
                            (*replacer)(e, e_subst);
                            rw(e_subst);
                            TRACE("str_fl", tout << "ival = " << ival << ", string arg evaluates to " << mk_pp(e_subst, m) << std::endl;);

                            zstring e_zstr;
                            if (u.str.is_string(e_subst, e_zstr)) {
                                // if arg is negative, e must be empty
                                // if arg is non-negative, e must be valid AND cannot contain leading zeroes

                                if (ival.is_neg()) {
                                    if (!e_zstr.empty()) {
                                        // contradiction
                                        expr_ref cex(ctx.mk_eq_atom(m_autil.mk_le(arg, mk_int(-1)), ctx.mk_eq_atom(e, mk_string(""))), m);
                                        assert_axiom(cex);
                                        return l_undef;
                                    }
                                } else {
                                    rational e_value;
                                    if (string_integer_conversion_valid(e_zstr, e_value)) {
                                        // e contains leading zeroes if its first character is 0 but converted to something other than 0
                                        if (e_zstr[0] == '0' && !e_value.is_zero()) {
                                            // contradiction
                                            expr_ref cex(m.mk_not(m.mk_and(ctx.mk_eq_atom(arg, mk_int(ival)), ctx.mk_eq_atom(e, mk_string(e_zstr)))), m);
                                            assert_axiom(cex);
                                            return l_undef;
                                        }
                                    } else {
                                        // contradiction
                                        expr_ref cex(m.mk_not(m.mk_and(ctx.mk_eq_atom(arg, mk_int(ival)), ctx.mk_eq_atom(e, mk_string(e_zstr)))), m);
                                        assert_axiom(cex);
                                        return l_undef;
                                    }
                                }
                            }
                        }
                    } else if (u.str.is_from_code(e, _arg)) {
                        expr_ref arg(_arg, m);
                        rational ival;
                        if (v.get_value(arg, ival)) {
                            expr_ref e_subst(e, m);
                            (*replacer)(e, e_subst);
                            rw(e_subst);
                            TRACE("str_fl", tout << "ival = " << ival << ", string arg evaluates to " << mk_pp(e_subst, m) << std::endl;);
                            zstring e_zstr;
                            if (u.str.is_string(e_subst, e_zstr)) {
                                // if arg is out of range, e must be empty
                                // if arg is in range, e must be valid
                                if (ival <= rational::zero() || ival >= rational(u.max_char())) {
                                    if (!e_zstr.empty()) {
                                        // contradiction
                                        expr_ref cex(ctx.mk_eq_atom(
                                            m.mk_or(m_autil.mk_le(arg, mk_int(0)), m_autil.mk_ge(arg, mk_int(u.max_char() + 1))),
                                            ctx.mk_eq_atom(e, mk_string(""))
                                        ), m);
                                        assert_axiom(cex);
                                        return l_undef;
                                    }
                                } else {
                                    if (e_zstr.length() != 1 || e_zstr[0] != ival.get_unsigned()) {
                                        // contradiction
                                        expr_ref premise(ctx.mk_eq_atom(arg, mk_int(ival)), m);
                                        expr_ref conclusion(ctx.mk_eq_atom(e, mk_string(zstring(ival.get_unsigned()))), m);
                                        expr_ref cex(rewrite_implication(premise, conclusion), m);
                                        assert_axiom(cex);
                                        return l_undef;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // TODO insert length values into substitution table as well?
            if (m_params.m_FixedLengthRefinement) {
                scoped_ptr<expr_replacer> replacer = mk_default_expr_replacer(m, false);
                replacer->set_substitution(&subst);
                th_rewriter rw(m);
                if (!abstracted_boolean_formulas.empty()) {
                    for (auto f : abstracted_boolean_formulas) {
                        TRACE("str_fl", tout << "refinement of boolean formula: " << mk_pp(f, m) << std::endl;);
                        expr_ref f_new(m);
                        (*replacer)(f, f_new);
                        rw(f_new);
                        TRACE("str_fl", tout << "after substitution and simplification, evaluates to: " << mk_pp(f_new, m) << std::endl;);
                        // now there are three cases, depending on what f_new evaluates to:
                        // true -> OK, do nothing
                        // false -> refine abstraction by generating conflict clause
                        // anything else -> error, probably our substitution was incomplete
                        if (m.is_true(f_new)) {
                            // do nothing
                        } else if (m.is_false(f_new)) {
                            expr * needle = nullptr, *haystack = nullptr;
                            if (u.str.is_contains(f, haystack, needle)) {
                                expr_ref haystack_assignment(m);
                                expr_ref needle_assignment(m);
                                (*replacer)(haystack, haystack_assignment);
                                (*replacer)(needle, needle_assignment);
                                cex.push_back(f);
                                cex.push_back(ctx.mk_eq_atom(haystack, haystack_assignment));
                                cex.push_back(ctx.mk_eq_atom(needle, needle_assignment));
                                return l_false;
                            } else {
                                TRACE("str_fl", tout << "error: unhandled refinement term " << mk_pp(f, m) << std::endl;);
                                NOT_IMPLEMENTED_YET();
                            }
                        } else {
                            NOT_IMPLEMENTED_YET();
                        }
                    }
                }
            }

            return l_true;
        } else if (subproblem_status == l_false) {
            if (m_params.m_FixedLengthNaiveCounterexamples) {
                TRACE("str_fl", tout << "subsolver found UNSAT; constructing length counterexample" << std::endl;);
                for (auto e : fixed_length_used_len_terms) {
                    expr * var = &e.get_key();
                    rational val = e.get_value();
                    cex.push_back(m.mk_eq(u.str.mk_length(var), mk_int(val)));
                }
                for (auto e : fixed_length_reduced_boolean_formulas) {
                    cex.push_back(e);
                }
                return l_false;
            } else {
                TRACE("str_fl", tout << "subsolver found UNSAT; reconstructing unsat core" << std::endl;);
                TRACE("str_fl", tout << "unsat core has size " << subsolver.get_unsat_core_size() << std::endl;);
                bool negate_pre = false;
                for (unsigned i = 0; i < subsolver.get_unsat_core_size(); ++i) {
                    TRACE("str", tout << "entry " << i << " = " << mk_pp(subsolver.get_unsat_core_expr(i), m) << std::endl;);
                    rational index;
                    expr* lhs;
                    expr* rhs;
                    TRACE("str_fl", tout << fixed_length_lesson.size() << std::endl;);
                    std::tie(index, lhs, rhs) = fixed_length_lesson.find(subsolver.get_unsat_core_expr(i));
                    TRACE("str_fl", tout << "lesson: " << mk_pp(lhs, m) << " == " << mk_pp(rhs, m) << " at index " << index << std::endl;);
                    cex.push_back(refine(lhs, rhs, index));
                    if (index < rational(0)) {
                        negate_pre = true;
                    }
                }
                if (negate_pre || subsolver.get_unsat_core_size() == 0){
                    for (auto ex : precondition) {
                        cex.push_back(ex);
                    }
                }
                return l_false;
            }
        } else { // l_undef
            TRACE("str_fl", tout << "WARNING: subsolver found UNKNOWN" << std::endl;);
            return l_undef;
        }
    }

}; // namespace smt
