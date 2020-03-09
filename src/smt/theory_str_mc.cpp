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

    inline zstring int_to_string(int i) {
        std::stringstream ss;
        ss << i;
        std::string str = ss.str();
        return zstring(str.c_str());
    }

    inline std::string longlong_to_string(long long i) {
        std::stringstream ss;
        ss << i;
        return ss.str();
    }

    /*
     * Use the current model in the arithmetic solver to get the length of a term.
     * Returns true if this could be done, placing result in 'termLen', or false otherwise.
     * Works like get_len_value() except uses arithmetic solver model instead of EQCs.
     */
    bool theory_str::fixed_length_get_len_value(expr * e, rational & val) {
        ast_manager & m = get_manager();

        rational val1;
        expr_ref len(m), len_val(m);
        expr* e1, *e2;
        expr_ref_vector todo(m);
        todo.push_back(e);
        val.reset();
        while (!todo.empty()) {
            expr* c = todo.back();
            todo.pop_back();
            if (u.str.is_concat(to_app(c))) {
                e1 = to_app(c)->get_arg(0);
                e2 = to_app(c)->get_arg(1);
                todo.push_back(e1);
                todo.push_back(e2);
            }
            else if (u.str.is_string(to_app(c))) {
                zstring tmp;
                u.str.is_string(to_app(c), tmp);
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
        context & ctx = get_context();

        ast_manager & sub_m = subsolver.m();
        context & sub_ctx = subsolver.get_context();

        expr * full;
        expr * suff;
        u.str.is_suffix(f, suff, full);

        expr_ref haystack(full, m);
        expr_ref needle(suff, m);

        ptr_vector<expr> full_chars, suff_chars;

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
            expr_ref _e(sub_ctx.mk_eq_atom(cLHS, cRHS), sub_m);
            branch.push_back(_e);
        }

        expr_ref final_diseq(mk_and(branch), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(rational(-2), f, f));

        return true;
    }

    bool theory_str::fixed_length_reduce_negative_suffix(smt::kernel & subsolver, expr_ref f, expr_ref & cex) {
        ast_manager & m = get_manager();
        context & ctx = get_context();

        ast_manager & sub_m = subsolver.m();
        context & sub_ctx = subsolver.get_context();

        expr * full;
        expr * suff;
        u.str.is_suffix(f, suff, full);

        expr_ref haystack(full, m);
        expr_ref needle(suff, m);

        ptr_vector<expr> full_chars, suff_chars;
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
            expr_ref _e(sub_ctx.mk_eq_atom(cLHS, cRHS), sub_m);
            branch.push_back(_e);
        }

        expr_ref final_diseq(mk_not(sub_m, mk_and(branch)), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(rational(-3), f, f));

        return true;
    }

    bool theory_str::fixed_length_reduce_prefix(smt::kernel & subsolver, expr_ref f, expr_ref & cex) {
        ast_manager & m = get_manager();
        context & ctx = get_context();

        ast_manager & sub_m = subsolver.m();
        context & sub_ctx = subsolver.get_context();

        expr * full;
        expr * pref;
        u.str.is_prefix(f, pref, full);

        expr_ref haystack(full, m);
        expr_ref needle(pref, m);

        ptr_vector<expr> full_chars, pref_chars;
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
            expr_ref _e(sub_ctx.mk_eq_atom(cLHS, cRHS), sub_m);
            branch.push_back(_e);
        }

        expr_ref final_diseq(mk_and(branch), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(rational(-2), f, f));

        return true;
    }

    bool theory_str::fixed_length_reduce_negative_prefix(smt::kernel & subsolver, expr_ref f, expr_ref & cex) {
        ast_manager & m = get_manager();
        context & ctx = get_context();

        ast_manager & sub_m = subsolver.m();
        context & sub_ctx = subsolver.get_context();

        expr * pref = nullptr, *full = nullptr;
        VERIFY(u.str.is_prefix(f, pref, full));

        expr_ref haystack(full, m);
        expr_ref needle(pref, m);

        ptr_vector<expr> full_chars, pref_chars;
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
            expr_ref _e(sub_ctx.mk_eq_atom(cLHS, cRHS), sub_m);
            branch.push_back(_e);
        }

        expr_ref final_diseq(mk_not(sub_m, mk_and(branch)), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(rational(-3), f, f));

        return true;
    }

    bool theory_str::fixed_length_reduce_contains(smt::kernel & subsolver, expr_ref f, expr_ref & cex) {
        ast_manager & m = get_manager();
        context & ctx = get_context();

        ast_manager & sub_m = subsolver.m();
        context & sub_ctx = subsolver.get_context();

        expr * full;
        expr * small;
        u.str.is_contains(f, full, small);

        expr_ref haystack(full, m);
        expr_ref needle(small, m);

        ptr_vector<expr> haystack_chars, needle_chars;
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
                expr_ref _e(sub_ctx.mk_eq_atom(cLHS, cRHS), sub_m);
                branch.push_back(_e);
            }
            branches.push_back(mk_and(branch));
        }

        expr_ref final_diseq(mk_or(branches), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(rational(-2), f, f));

        return true;
    }

    bool theory_str::fixed_length_reduce_negative_contains(smt::kernel & subsolver, expr_ref f, expr_ref & cex) {
        ast_manager & m = get_manager();
        context & ctx = get_context();

        ast_manager & sub_m = subsolver.m();
        context & sub_ctx = subsolver.get_context();

        expr * small = nullptr, *full = nullptr;
        VERIFY(u.str.is_contains(f, full, small));

        expr_ref haystack(full, m);
        expr_ref needle(small, m);

        ptr_vector<expr> haystack_chars, needle_chars;
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
                expr_ref _e(sub_ctx.mk_eq_atom(cLHS, cRHS), sub_m);
                branch.push_back(_e);
            }
            branches.push_back(mk_and(branch));
        }

        expr_ref final_diseq(mk_not(sub_m, mk_or(branches)), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(rational(-3), f, f));

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
        context & ctx = get_context();

        ast_manager & sub_m = subsolver.m();
        context & sub_ctx = subsolver.get_context();

        expr * str;
        expr * re;
        u.str.is_in_re(f, str, re);

        // TODO reuse some of the automaton framework from theory_str_regex
        eautomaton * aut = m_mk_aut(re);
        aut->compress();

        ptr_vector<expr> str_chars;
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
            sub_ctx.get_rewriter()(result);
            TRACE("str_fl", tout << "regex path constraint: " << mk_pp(result, sub_m) << std::endl;);

            if (sub_m.is_false(result)) {
                // There are no solutions of that length in the automaton.
                // If the membership constraint is true, we assert a conflict clause.
                // If the membership constraint is false, we ignore the constraint.
                if (polarity) {
                    cex = m.mk_or(m.mk_not(f), m.mk_not(ctx.mk_eq_atom(mk_strlen(str), mk_int(str_chars.size()))));
                    ctx.get_rewriter()(cex);
                    return false;
                } else {
                    TRACE("str_fl", tout << "regex constraint satisfied without asserting constraints to subsolver" << std::endl;);
                    return true;
                }
            } else {
                // TODO fixed_length_lesson?
                if (polarity) {
                    fixed_length_assumptions.push_back(result);
                } else {
                    fixed_length_assumptions.push_back(sub_m.mk_not(result));
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
            ptr_vector<expr> & eqc_chars, expr_ref & cex) {
        ast_manager & m = get_manager();

        ast_manager & sub_m = subsolver.m();

        bv_util bv(m);
        sort * bv8_sort = bv.mk_sort(8);

        expr * arg0;
        expr * arg1;
        expr * arg2;

        zstring strConst;
        if (u.str.is_string(term, strConst)) {
            for (unsigned i = 0; i < strConst.length(); ++i) {
                expr_ref chTerm(bitvector_character_constants.get(strConst[i]), m);
                eqc_chars.push_back(chTerm);
            }
        } else if (to_app(term)->get_num_args() == 0 && !u.str.is_string(term)) {
            // this is a variable; get its length and create/reuse character terms
            if (!var_to_char_subterm_map.contains(term)) {
                rational varLen_value;
                bool var_hasLen = fixed_length_get_len_value(term, varLen_value);
                if (!var_hasLen || varLen_value.is_neg()) {
                    TRACE("str_fl", tout << "variable " << mk_pp(term, m) << " has no length assignment or impossible length assignment - asserting conflict axiom" << std::endl;);
                    cex = expr_ref(m_autil.mk_ge(mk_strlen(term), mk_int(0)), m);
                    return false;
                }
                TRACE("str_fl", tout << "creating character terms for variable " << mk_pp(term, m) << ", length = " << varLen_value << std::endl;);
                ptr_vector<expr> new_chars;
                for (unsigned i = 0; i < varLen_value.get_unsigned(); ++i) {
                    // TODO we can probably name these better for the sake of debugging
                    expr_ref ch(mk_fresh_const("char", bv8_sort), m);
                    new_chars.push_back(ch);
                    fixed_length_subterm_trail.push_back(ch);
                }
                var_to_char_subterm_map.insert(term, new_chars);
                fixed_length_used_len_terms.insert(term, varLen_value.get_unsigned());
            }
            var_to_char_subterm_map.find(term, eqc_chars);
        } else if (u.str.is_concat(term, arg0, arg1)) {
            expr_ref first(arg0, sub_m);
            expr_ref second(arg1, sub_m);
            ptr_vector<expr> chars0, chars1;
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
            ptr_vector<expr> base_chars;
            if (!fixed_length_reduce_string_term(subsolver, first, base_chars, cex)) {
                return false;
            }
            arith_value v(m);
            v.init(&get_context());
            rational pos, len;
            bool pos_exists = v.get_value(arg1, pos);
            bool len_exists = v.get_value(arg2, len);
            ENSURE(pos_exists);
            ENSURE(len_exists);
            TRACE("str_fl", tout << "reduce substring term: base=" << mk_pp(term, m) << " (length="<<base_chars.size()<<"), pos=" << pos.to_string() << ", len=" << len.to_string() << std::endl;);
            // Case 1: pos < 0 or pos >= strlen(base) or len < 0
            // ==> (Substr ...) = ""
            if (pos.is_neg() || pos >= rational(base_chars.size()) || len.is_neg()) {
                eqc_chars.reset();
                return true;
            } else {
                if (pos + len >= rational(base_chars.size())) {
                    // take as many characters as possible up to the end of base_chars
                    for (unsigned i = pos.get_unsigned(); i < base_chars.size(); ++i) {
                        eqc_chars.push_back(base_chars.get(i));
                    }
                } else {
                    for (unsigned i = pos.get_unsigned(); i < pos.get_unsigned() + len.get_unsigned(); ++i) {
                        eqc_chars.push_back(base_chars.get(i));
                    }
                }
            }
        } else if (u.str.is_at(term, arg0, arg1)) {
            // (str.at Base Pos)
            expr_ref base(arg0, sub_m);
            expr_ref pos(arg1, sub_m);
            ptr_vector<expr> base_chars;
            if (!fixed_length_reduce_string_term(subsolver, base, base_chars, cex)) {
                return false;
            }
            arith_value v(m);
            v.init(&get_context());
            rational pos_value;
            bool pos_exists = v.get_value(pos, pos_value);
            ENSURE(pos_exists);
            TRACE("str_fl", tout << "reduce str.at: base=" << mk_pp(base, m) << ", pos=" << pos_value.to_string() << std::endl;);
            if (pos_value.is_neg() || pos_value >= rational(base_chars.size())) {
                // return the empty string
                eqc_chars.reset();
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
                if (termLen.get_unsigned() != iValue.to_string().length()) {
                    // conflict
                    cex = expr_ref(m.mk_not(m.mk_and(get_context().mk_eq_atom(mk_strlen(term), mk_int(termLen)), get_context().mk_eq_atom(arg0, mk_int(iValue)))), m);
                    return false;
                }
                // convert iValue to a constant
                zstring iValue_str = zstring(iValue.to_string().c_str());
                for (unsigned idx = 0; idx < iValue_str.length(); ++idx) {
                    expr_ref chTerm(bitvector_character_constants.get(iValue_str[idx]), sub_m);
                    eqc_chars.push_back(chTerm);
                }
                return true;
            }
        } else {
            TRACE("str_fl", tout << "string term " << mk_pp(term, m) << " handled as uninterpreted function" << std::endl;);
            if (!uninterpreted_to_char_subterm_map.contains(term)) {
                rational ufLen_value;
                bool uf_hasLen = fixed_length_get_len_value(term, ufLen_value);
                if (!uf_hasLen || ufLen_value.is_neg()) {
                    TRACE("str_fl", tout << "uninterpreted function " << mk_pp(term, m) << " has no length assignment or impossible length assignment - asserting conflict axiom" << std::endl;);
                    cex = expr_ref(m_autil.mk_ge(mk_strlen(term), mk_int(0)), m);
                    return false;
                }
                TRACE("str_fl", tout << "creating character terms for uninterpreted function " << mk_pp(term, m) << ", length = " << ufLen_value << std::endl;);
                ptr_vector<expr> new_chars;
                for (unsigned i = 0; i < ufLen_value.get_unsigned(); ++i) {
                    expr_ref ch(mk_fresh_const("char", bv8_sort), m);
                    new_chars.push_back(ch);
                    fixed_length_subterm_trail.push_back(ch);
                }
                uninterpreted_to_char_subterm_map.insert(term, new_chars);
                fixed_length_used_len_terms.insert(term, ufLen_value.get_unsigned());
            }
            uninterpreted_to_char_subterm_map.find(term, eqc_chars);
        }
        return true;
    }

    bool theory_str::fixed_length_reduce_eq(smt::kernel & subsolver, expr_ref lhs, expr_ref rhs, expr_ref & cex) {
        ast_manager & m = get_manager();
        context & ctx = get_context();

        ast_manager & sub_m = subsolver.m();
        context & sub_ctx = subsolver.get_context();

        ptr_vector<expr> lhs_chars, rhs_chars;

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
            expr_ref _e(sub_ctx.mk_eq_atom(cLHS, cRHS), sub_m);
            fixed_length_assumptions.push_back(_e);
            fixed_length_lesson.insert(_e, std::make_tuple(rational(i), lhs, rhs));
        }
        // fixed_length_used_len_terms.push_back(get_context().mk_eq_atom(lhs, rhs));
        return true;
    }

    bool theory_str::fixed_length_reduce_diseq(smt::kernel & subsolver, expr_ref lhs, expr_ref rhs, expr_ref & cex) {
        ast_manager & m = get_manager();

        ast_manager & sub_m = subsolver.m();
        context & sub_ctx = subsolver.get_context();

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

        ptr_vector<expr> lhs_chars, rhs_chars;
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
            diseqs.push_back(sub_m.mk_not(sub_ctx.mk_eq_atom(cLHS, cRHS)));
        }

        expr_ref final_diseq(mk_or(diseqs), sub_m);
        fixed_length_assumptions.push_back(final_diseq);
        fixed_length_lesson.insert(final_diseq, std::make_tuple(rational(-1), lhs, rhs));

        return true;
    }

    lbool theory_str::fixed_length_model_construction(expr_ref_vector formulas, expr_ref_vector &precondition,
            expr_ref_vector& free_variables,
            obj_map<expr, zstring> &model, expr_ref_vector &cex) {

        ast_manager & m = get_manager();

        if (bitvector_character_constants.empty()) {
            bv_util bv(m);
            sort * bv8_sort = bv.mk_sort(8);
            for (unsigned i = 0; i < 256; ++i) {
                rational ch(i);
                expr_ref chTerm(bv.mk_numeral(ch, bv8_sort), m);
                bitvector_character_constants.push_back(chTerm);
                fixed_length_subterm_trail.push_back(chTerm);
            }
        }

        TRACE("str",
            ast_manager & m = get_manager();
            context & ctx = get_context();
            tout << "dumping all formulas:" << std::endl;
            for (expr_ref_vector::iterator i = formulas.begin(); i != formulas.end(); ++i) {
                expr * ex = *i;
                tout << mk_pp(ex, m) << (ctx.is_relevant(ex) ? "" : " (NOT REL)") << std::endl;
            }
        );

        fixed_length_subterm_trail.reset();
        fixed_length_used_len_terms.reset();
        fixed_length_assumptions.reset();
        var_to_char_subterm_map.reset();
        uninterpreted_to_char_subterm_map.reset();
        fixed_length_lesson.reset();

        // Boolean formulas on which to apply abstraction refinement.
        expr_ref_vector abstracted_boolean_formulas(m);

        smt_params subsolver_params;
        smt::kernel subsolver(m, subsolver_params);
        subsolver.set_logic(symbol("QF_BV"));

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
            ptr_vector<expr> var_chars;
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
            sort * fSort = m.get_sort(f);
            if (fSort == bool_sort && !is_quantifier(f)) {
                // extracted terms
                expr * subterm;
                expr * lhs;
                expr * rhs;
                if (m.is_eq(f, lhs, rhs)) {
                    sort * lhs_sort = m.get_sort(lhs);
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
                } else if (u.str.is_suffix(f)) {
                    TRACE("str_fl", tout << "reduce positive suffix: " << mk_pp(f, m) << std::endl;);
                    expr_ref cex(m);
                    expr_ref suf(f, m);
                    if (!fixed_length_reduce_suffix(subsolver, suf, cex)) {
                        assert_axiom(cex);
                        add_persisted_axiom(cex);
                        return l_undef;
                    }
                }else if (m.is_not(f, subterm)) {
                    // if subterm is a string formula such as an equality, reduce it as a disequality
                    if (m.is_eq(subterm, lhs, rhs)) {
                        sort * lhs_sort = m.get_sort(lhs);
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
                    } else if (u.str.is_contains(subterm)) {
                        TRACE("str_fl", tout << "reduce negative contains: " << mk_pp(subterm, m) << std::endl;);
                        expr_ref cex(m);
                        expr_ref cont(subterm, m);
                        if (!fixed_length_reduce_negative_contains(subsolver, cont, cex)) {
                            assert_axiom(cex);
                            add_persisted_axiom(cex);
                            return l_undef;
                        }
                    } else if (u.str.is_prefix(subterm)) {
                        TRACE("str_fl", tout << "reduce negative prefix: " << mk_pp(subterm, m) << std::endl;);
                        expr_ref cex(m);
                        expr_ref pref(subterm, m);
                        if (!fixed_length_reduce_negative_prefix(subsolver, pref, cex)) {
                            assert_axiom(cex);
                            add_persisted_axiom(cex);
                            return l_undef;
                        }
                    } else if (u.str.is_suffix(subterm)) {
                        TRACE("str_fl", tout << "reduce negative suffix: " << mk_pp(subterm, m) << std::endl;);
                        expr_ref cex(m);
                        expr_ref suf(subterm, m);
                        if (!fixed_length_reduce_negative_suffix(subsolver, suf, cex)) {
                            assert_axiom(cex);
                            add_persisted_axiom(cex);
                            return l_undef;
                        }
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

        for (auto e : fixed_length_used_len_terms) {
            expr * var = &e.get_key();
            precondition.push_back(m.mk_eq(u.str.mk_length(var), mk_int(e.get_value())));
        }

        TRACE("str_fl",
            tout << "formulas asserted to bitvector subsolver:" << std::endl;
            for (auto e : fixed_length_assumptions) {
                tout << mk_pp(e, subsolver.m()) << std::endl;
            }
            tout << "variable to character mappings:" << std::endl;
            for (auto &entry : var_to_char_subterm_map) {
                tout << mk_pp(entry.m_key, get_manager()) << ":";
                for (auto e : entry.m_value) {
                    tout << " " << mk_pp(e, subsolver.m());
                }
                tout << std::endl;
            }
        );

        TRACE("str_fl", tout << "calling subsolver" << std::endl;);

        lbool subproblem_status = subsolver.check(fixed_length_assumptions);

        if (subproblem_status == l_true) {
            bv_util bv(m);
            TRACE("str_fl", tout << "subsolver found SAT; reconstructing model" << std::endl;);
            model_ref subModel;
            subsolver.get_model(subModel);

            expr_substitution subst(m);

            //model_smt2_pp(std::cout, m, *subModel, 2);
            for (auto entry : var_to_char_subterm_map) {
                svector<unsigned> assignment;
                expr * var = entry.m_key;
                ptr_vector<expr> char_subterms(entry.m_value);
                for (expr * chExpr : char_subterms) {
                    expr_ref chAssignment(subModel->get_const_interp(to_app(chExpr)->get_decl()), m);
                    rational n;
                    if (chAssignment != nullptr && bv.is_numeral(chAssignment, n)) {
                        assignment.push_back(n.get_unsigned());
                    } else {
                        assignment.push_back((unsigned)'?');
                    }
                }
                zstring strValue(assignment.size(), assignment.c_ptr());
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
                ptr_vector<expr> char_subterms(entry.m_value);
                for (expr * chExpr : char_subterms) {
                    expr_ref chAssignment(subModel->get_const_interp(to_app(chExpr)->get_decl()), m);
                    rational n;
                    if (chAssignment != nullptr && bv.is_numeral(chAssignment, n)) {
                        assignment.push_back(n.get_unsigned());
                    } else {
                        assignment.push_back((unsigned)'?');
                    }
                }
                zstring strValue(assignment.size(), assignment.c_ptr());
                model.insert(var, strValue);
                subst.insert(var, mk_string(strValue));
            }
            // TODO insert length values into substitution table as well?
            if (m_params.m_FixedLengthRefinement) {
                scoped_ptr<expr_replacer> replacer = mk_default_expr_replacer(m);
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
                            context & ctx = get_context();
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
                    cex.push_back(m.mk_eq(u.str.mk_length(var), mk_int(e.get_value())));
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
                    std::tie(index, lhs, rhs) = fixed_length_lesson.find(subsolver.get_unsat_core_expr(i));
                    TRACE("str_fl", tout << "lesson: " << mk_pp(lhs, m) << " == " << mk_pp(rhs, m) << " at index " << index << std::endl;);
                    cex.push_back(refine(lhs, rhs, index));
                    if (index < rational(0)) {
                        negate_pre = true;
                    }
                }
                if (negate_pre){
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

    expr * theory_str::gen_len_test_options(expr * freeVar, expr * indicator, int tries) {
        ast_manager & m = get_manager();
        context & ctx = get_context();

        expr_ref freeVarLen(mk_strlen(freeVar), m);
        SASSERT(freeVarLen);

        {
            rational freeVar_len_value;
            if (get_len_value(freeVar, freeVar_len_value)) {
                TRACE("str", tout << "special case: length of freeVar is known to be " << freeVar_len_value << std::endl;);
                expr_ref concreteOption(ctx.mk_eq_atom(indicator, mk_string(freeVar_len_value.to_string().c_str()) ), m);
                expr_ref concreteValue(ctx.mk_eq_atom(
                        ctx.mk_eq_atom(indicator, mk_string(freeVar_len_value.to_string().c_str()) ),
                        ctx.mk_eq_atom(freeVarLen, m_autil.mk_numeral(freeVar_len_value, true))), m);
                expr_ref finalAxiom(m.mk_and(concreteOption, concreteValue), m);
                SASSERT(finalAxiom);
                m_trail.push_back(finalAxiom);
                return finalAxiom;
            }
        }

        expr_ref_vector orList(m);
        expr_ref_vector andList(m);

        int distance = 3;
        int l = (tries - 1) * distance;
        int h = tries * distance;

        TRACE("str",
              tout << "building andList and orList" << std::endl;
              if (m_params.m_AggressiveLengthTesting) {
                  tout << "note: aggressive length testing is active" << std::endl;
              }
              );

        // experimental theory-aware case split support
        literal_vector case_split_literals;

        for (int i = l; i < h; ++i) {
            expr_ref str_indicator(m);
            if (m_params.m_UseFastLengthTesterCache) {
                rational ri(i);
                expr * lookup_val;
                if(lengthTesterCache.find(ri, lookup_val)) {
                    str_indicator = expr_ref(lookup_val, m);
                } else {
                    // no match; create and insert
                    zstring i_str = int_to_string(i);
                    expr_ref new_val(mk_string(i_str), m);
                    lengthTesterCache.insert(ri, new_val);
                    m_trail.push_back(new_val);
                    str_indicator = expr_ref(new_val, m);
                }
            } else {
                zstring i_str = int_to_string(i);
                str_indicator = expr_ref(mk_string(i_str), m);
            }
            expr_ref or_expr(ctx.mk_eq_atom(indicator, str_indicator), m);
            orList.push_back(or_expr);

            double priority;
            // give high priority to small lengths if this is available
            if (i <= 5) {
                priority = 0.3;
            } else {
                // prioritize over "more"
                priority = 0.2;
            }
            add_theory_aware_branching_info(or_expr, priority, l_true);

            if (m_params.m_AggressiveLengthTesting) {
                literal l = mk_eq(indicator, str_indicator, false);
                ctx.mark_as_relevant(l);
                ctx.force_phase(l);
            }

            case_split_literals.insert(mk_eq(freeVarLen, mk_int(i), false));

            expr_ref and_expr(ctx.mk_eq_atom(orList.get(orList.size() - 1), m.mk_eq(freeVarLen, mk_int(i))), m);
            andList.push_back(and_expr);
        }

        expr_ref more_option(ctx.mk_eq_atom(indicator, mk_string("more")), m);
        orList.push_back(more_option);
        // decrease priority of this option
        add_theory_aware_branching_info(more_option, -0.1, l_true);
        if (m_params.m_AggressiveLengthTesting) {
            literal l = mk_eq(indicator, mk_string("more"), false);
            ctx.mark_as_relevant(l);
            ctx.force_phase(~l);
        }

        andList.push_back(ctx.mk_eq_atom(orList.get(orList.size() - 1), m_autil.mk_ge(freeVarLen, mk_int(h))));

        /*
          { // more experimental theory case split support
          expr_ref tmp(m_autil.mk_ge(freeVarLen, mk_int(h)), m);
          ctx.internalize(m_autil.mk_ge(freeVarLen, mk_int(h)), false);
          case_split_literals.push_back(ctx.get_literal(tmp));
          ctx.mk_th_case_split(case_split_literals.size(), case_split_literals.c_ptr());
          }
        */

        expr_ref_vector or_items(m);
        expr_ref_vector and_items(m);

        for (unsigned i = 0; i < orList.size(); ++i) {
            or_items.push_back(orList.get(i));
        }

        and_items.push_back(mk_or(or_items));
        for(unsigned i = 0; i < andList.size(); ++i) {
            and_items.push_back(andList.get(i));
        }

        TRACE("str", tout << "check: " << mk_pp(mk_and(and_items), m) << std::endl;);

        expr_ref lenTestAssert = mk_and(and_items);
        SASSERT(lenTestAssert);
        TRACE("str", tout << "crash avoidance lenTestAssert: " << mk_pp(lenTestAssert, m) << std::endl;);

        int testerCount = tries - 1;
        if (testerCount > 0) {
            expr_ref_vector and_items_LHS(m);
            expr_ref moreAst(mk_string("more"), m);
            for (int i = 0; i < testerCount; ++i) {
                expr * indicator = fvar_lenTester_map[freeVar][i];
                if (internal_variable_set.find(indicator) == internal_variable_set.end()) {
                    TRACE("str", tout << "indicator " << mk_pp(indicator, m) << " out of scope; continuing" << std::endl;);
                    continue;
                } else {
                    TRACE("str", tout << "indicator " << mk_pp(indicator, m) << " in scope" << std::endl;);
                    and_items_LHS.push_back(ctx.mk_eq_atom(indicator, moreAst));
                }
            }
            expr_ref assertL(mk_and(and_items_LHS), m);
            SASSERT(assertL);
            expr * finalAxiom = m.mk_or(m.mk_not(assertL), lenTestAssert.get());
            SASSERT(finalAxiom != nullptr);
            TRACE("str", tout << "crash avoidance finalAxiom: " << mk_pp(finalAxiom, m) << std::endl;);
            return finalAxiom;
        } else {
            TRACE("str", tout << "crash avoidance lenTestAssert.get(): " << mk_pp(lenTestAssert.get(), m) << std::endl;);
            m_trail.push_back(lenTestAssert.get());
            return lenTestAssert.get();
        }
    }

    /*
    * The return value indicates whether we covered the search space.
    *   - If the next encoding is valid, return false
    *   - Otherwise, return true
    */
   bool theory_str::get_next_val_encode(int_vector & base, int_vector & next) {
       SASSERT(charSetSize > 0);

       TRACE("str", tout << "base vector: [ ";
             for (unsigned i = 0; i < base.size(); ++i) {
                 tout << base[i] << " ";
             }
             tout << "]" << std::endl;
             );

       int s = 0;
       int carry = 0;
       next.reset();

       for (int i = 0; i < (int) base.size(); i++) {
           if (i == 0) {
               s = base[i] + 1;
               carry = s / charSetSize;
               s = s % charSetSize;
               next.push_back(s);
           } else {
               s = base[i] + carry;
               carry = s / charSetSize;
               s = s % charSetSize;
               next.push_back(s);
           }
       }
       if (next[next.size() - 1] > 0) {
           next.reset();
           return true;
       } else {
           return false;
       }
   }

   expr* theory_str::gen_val_options(expr * freeVar, expr * len_indicator, expr * val_indicator,
                                      zstring lenStr, int tries) {
       ast_manager & m = get_manager();
       context & ctx = get_context();

       int distance = 32;

       // ----------------------------------------------------------------------------------------
       // generate value options encoding
       // encoding is a vector of size (len + 1)
       // e.g, len = 2,
       //      encoding {1, 2, 0} means the value option is "charSet[2]"."charSet[1]"
       //      the last item in the encoding indicates whether the whole space is covered
       //      for example, if the charSet = {a, b}. All valid encodings are
       //        {0, 0, 0}, {1, 0, 0}, {0, 1, 0}, {1, 1, 0}
       //      if add 1 to the last one, we get
       //        {0, 0, 1}
       //      the last item "1" shows this is not a valid encoding, and we have covered all space
       // ----------------------------------------------------------------------------------------
       int len = atoi(lenStr.encode().c_str());
       bool coverAll = false;
       vector<int_vector, true, size_t> options;
       int_vector base;

       TRACE("str", tout
             << "freeVar = " << mk_ismt2_pp(freeVar, m) << std::endl
             << "len_indicator = " << mk_ismt2_pp(len_indicator, m) << std::endl
             << "val_indicator = " << mk_ismt2_pp(val_indicator, m) << std::endl
             << "lenstr = " << lenStr << "\n"
             << "tries = " << tries << "\n";
             if (m_params.m_AggressiveValueTesting) {
                 tout << "note: aggressive value testing is enabled" << std::endl;
             }
             );

       if (tries == 0) {
           base = int_vector(len + 1, 0);
           coverAll = false;
       } else {
           expr * lastestValIndi = fvar_valueTester_map[freeVar][len][tries - 1].second;
           TRACE("str", tout << "last value tester = " << mk_ismt2_pp(lastestValIndi, m) << std::endl;);
           coverAll = get_next_val_encode(val_range_map[lastestValIndi], base);
       }

       size_t l = (tries) * distance;
       size_t h = l;
       for (int i = 0; i < distance; i++) {
           if (coverAll)
               break;
           options.push_back(base);
           h++;
           coverAll = get_next_val_encode(options[options.size() - 1], base);
       }
       val_range_map.insert(val_indicator, options[options.size() - 1]);

       TRACE("str",
             tout << "value tester encoding " << "{" << std::endl;
             int_vector vec = val_range_map[val_indicator];

             for (int_vector::iterator it = vec.begin(); it != vec.end(); ++it) {
                 tout << *it << std::endl;
             }
             tout << "}" << std::endl;
             );

       // ----------------------------------------------------------------------------------------

       expr_ref_vector orList(m), andList(m);

       for (size_t i = l; i < h; i++) {
           orList.push_back(m.mk_eq(val_indicator, mk_string(longlong_to_string(i).c_str()) ));
           if (m_params.m_AggressiveValueTesting) {
               literal lit = mk_eq(val_indicator, mk_string(longlong_to_string(i).c_str()), false);
               ctx.mark_as_relevant(lit);
               ctx.force_phase(lit);
           }

           zstring aStr = gen_val_string(len, options[i - l]);
           expr * strAst;
           if (m_params.m_UseFastValueTesterCache) {
               if (!valueTesterCache.find(aStr, strAst)) {
                   strAst = mk_string(aStr);
                   valueTesterCache.insert(aStr, strAst);
                   m_trail.push_back(strAst);
               }
           } else {
               strAst = mk_string(aStr);
           }
           andList.push_back(m.mk_eq(orList[orList.size() - 1].get(), m.mk_eq(freeVar, strAst)));
       }
       if (!coverAll) {
           orList.push_back(m.mk_eq(val_indicator, mk_string("more")));
           if (m_params.m_AggressiveValueTesting) {
               literal l = mk_eq(val_indicator, mk_string("more"), false);
               ctx.mark_as_relevant(l);
               ctx.force_phase(~l);
           }
       }

       andList.push_back(mk_or(orList));
       expr_ref valTestAssert = mk_and(andList);

       // ---------------------------------------
       // If the new value tester is $$_val_x_16_i
       // Should add ($$_len_x_j = 16) /\ ($$_val_x_16_i = "more")
       // ---------------------------------------
       andList.reset();
       andList.push_back(m.mk_eq(len_indicator, mk_string(lenStr)));
       for (int i = 0; i < tries; i++) {
           expr * vTester = fvar_valueTester_map[freeVar][len][i].second;
           if (vTester != val_indicator)
               andList.push_back(m.mk_eq(vTester, mk_string("more")));
       }
       expr_ref assertL = mk_and(andList);
       // (assertL => valTestAssert) <=> (!assertL OR valTestAssert)
       return m.mk_or(m.mk_not(assertL), valTestAssert);
   }

    // -----------------------------------------------------------------------------------------------------
    // True branch will be taken in final_check:
    //   - When we discover a variable is "free" for the first time
    //     lenTesterInCbEq = NULL
    //     lenTesterValue = ""
    // False branch will be taken when invoked by new_eq_eh().
    //   - After we set up length tester for a "free" var in final_check,
    //     when the tester is assigned to some value (e.g. "more" or "4"),
    //     lenTesterInCbEq != NULL, and its value will be passed by lenTesterValue
    // The difference is that in new_eq_eh(), lenTesterInCbEq and its value have NOT been put into a same eqc
    // -----------------------------------------------------------------------------------------------------
    expr * theory_str::gen_len_val_options_for_free_var(expr * freeVar, expr * lenTesterInCbEq, zstring lenTesterValue) {

        ast_manager & m = get_manager();

        TRACE("str", tout << "gen for free var " << mk_ismt2_pp(freeVar, m) << std::endl;);

        if (m_params.m_UseBinarySearch) {
            TRACE("str", tout << "using binary search heuristic" << std::endl;);
            return binary_search_length_test(freeVar, lenTesterInCbEq, lenTesterValue);
        } else {
            bool map_effectively_empty = false;
            if (!fvar_len_count_map.contains(freeVar)) {
                TRACE("str", tout << "fvar_len_count_map is empty" << std::endl;);
                map_effectively_empty = true;
            }

            if (!map_effectively_empty) {
                // check whether any entries correspond to variables that went out of scope;
                // if every entry is out of scope then the map counts as being empty

                // assume empty and find a counterexample
                map_effectively_empty = true;
                if (fvar_lenTester_map.contains(freeVar)) {
                    for (expr * indicator : fvar_lenTester_map[freeVar]) {
                        if (internal_variable_set.find(indicator) != internal_variable_set.end()) {
                            TRACE("str", tout <<"found active internal variable " << mk_ismt2_pp(indicator, m)
                                    << " in fvar_lenTester_map[freeVar]" << std::endl;);
                            map_effectively_empty = false;
                            break;
                        }
                    }
                }
                CTRACE("str", map_effectively_empty, tout << "all variables in fvar_lenTester_map[freeVar] out of scope" << std::endl;);
            }

            if (map_effectively_empty) {
                // no length assertions for this free variable have ever been added.
                TRACE("str", tout << "no length assertions yet" << std::endl;);

                fvar_len_count_map.insert(freeVar, 1);
                unsigned int testNum = fvar_len_count_map[freeVar];

                expr_ref indicator(mk_internal_lenTest_var(freeVar, testNum), m);
                SASSERT(indicator);

                // since the map is "effectively empty", we can remove those variables that have left scope...
                if (!fvar_lenTester_map.contains(freeVar)) {
                    fvar_lenTester_map.insert(freeVar, ptr_vector<expr>());
                }
                fvar_lenTester_map[freeVar].shrink(0);
                fvar_lenTester_map[freeVar].push_back(indicator);
                lenTester_fvar_map.insert(indicator, freeVar);

                expr * lenTestAssert = gen_len_test_options(freeVar, indicator, testNum);
                SASSERT(lenTestAssert != nullptr);
                return lenTestAssert;
            } else {
                TRACE("str", tout << "found previous in-scope length assertions" << std::endl;);

                expr * effectiveLenInd = nullptr;
                zstring effectiveLenIndiStr("");
                int lenTesterCount;
                if (fvar_lenTester_map.contains(freeVar)) {
                    lenTesterCount = fvar_lenTester_map[freeVar].size();
                } else {
                    lenTesterCount = 0;
                }

                TRACE("str",
                        tout << lenTesterCount << " length testers in fvar_lenTester_map[" << mk_pp(freeVar, m) << "]:" << std::endl;
                for (int i = 0; i < lenTesterCount; ++i) {
                    expr * len_indicator = fvar_lenTester_map[freeVar][i];
                    tout << mk_pp(len_indicator, m) << ": ";
                    bool effectiveInScope = (internal_variable_set.find(len_indicator) != internal_variable_set.end());
                    tout << (effectiveInScope ? "in scope" : "NOT in scope");
                    tout << std::endl;
                }
                );

                int i = 0;
                for (; i < lenTesterCount; ++i) {
                    expr * len_indicator_pre = fvar_lenTester_map[freeVar][i];
                    // check whether this is in scope as well
                    if (internal_variable_set.find(len_indicator_pre) == internal_variable_set.end()) {
                        TRACE("str", tout << "length indicator " << mk_pp(len_indicator_pre, m) << " not in scope" << std::endl;);
                        continue;
                    }

                    bool indicatorHasEqcValue = false;
                    expr * len_indicator_value = get_eqc_value(len_indicator_pre, indicatorHasEqcValue);
                    TRACE("str", tout << "length indicator " << mk_ismt2_pp(len_indicator_pre, m) <<
                            " = " << mk_ismt2_pp(len_indicator_value, m) << std::endl;);
                    if (indicatorHasEqcValue) {
                        zstring len_pIndiStr;
                        u.str.is_string(len_indicator_value, len_pIndiStr);
                        if (len_pIndiStr != "more") {
                            effectiveLenInd = len_indicator_pre;
                            effectiveLenIndiStr = len_pIndiStr;
                            break;
                        }
                    } else {
                        if (lenTesterInCbEq != len_indicator_pre) {
                            TRACE("str", tout << "WARNING: length indicator " << mk_ismt2_pp(len_indicator_pre, m)
                                    << " does not have an equivalence class value."
                                    << " i = " << i << ", lenTesterCount = " << lenTesterCount << std::endl;);
                            if (i > 0) {
                                effectiveLenInd = fvar_lenTester_map[freeVar][i - 1];
                                bool effectiveHasEqcValue;
                                expr * effective_eqc_value = get_eqc_value(effectiveLenInd, effectiveHasEqcValue);
                                bool effectiveInScope = (internal_variable_set.find(effectiveLenInd) != internal_variable_set.end());
                                TRACE("str", tout << "checking effective length indicator " << mk_pp(effectiveLenInd, m) << ": "
                                        << (effectiveInScope ? "in scope" : "NOT in scope") << ", ";
                                if (effectiveHasEqcValue) {
                                    tout << "~= " << mk_pp(effective_eqc_value, m);
                                } else {
                                    tout << "no eqc string constant";
                                }
                                tout << std::endl;); (void)effectiveInScope;
                                if (effectiveLenInd == lenTesterInCbEq) {
                                    effectiveLenIndiStr = lenTesterValue;
                                } else {
                                    if (effectiveHasEqcValue) {
                                        u.str.is_string(effective_eqc_value, effectiveLenIndiStr);
                                    } else {
                                        NOT_IMPLEMENTED_YET();
                                    }
                                }
                            }
                            break;
                        }
                        // lenTesterInCbEq == len_indicator_pre
                        else {
                            if (lenTesterValue != "more") {
                                effectiveLenInd = len_indicator_pre;
                                effectiveLenIndiStr = lenTesterValue;
                                break;
                            }
                        }
                    } // !indicatorHasEqcValue
                } // for (i : [0..lenTesterCount-1])
                if (effectiveLenIndiStr == "more" || effectiveLenIndiStr == "") {
                    TRACE("str", tout << "length is not fixed; generating length tester options for free var" << std::endl;);
                    expr_ref indicator(m);
                    unsigned int testNum = 0;

                    TRACE("str", tout << "effectiveLenIndiStr = " << effectiveLenIndiStr
                            << ", i = " << i << ", lenTesterCount = " << lenTesterCount << "\n";);

                    if (i == lenTesterCount) {
                        fvar_len_count_map[freeVar] = fvar_len_count_map[freeVar] + 1;
                        testNum = fvar_len_count_map[freeVar];
                        indicator = mk_internal_lenTest_var(freeVar, testNum);
                        fvar_lenTester_map[freeVar].push_back(indicator);
                        lenTester_fvar_map.insert(indicator, freeVar);
                    } else {
                        indicator = fvar_lenTester_map[freeVar][i];
                        refresh_theory_var(indicator);
                        testNum = i + 1;
                    }
                    expr * lenTestAssert = gen_len_test_options(freeVar, indicator, testNum);
                    SASSERT(lenTestAssert != nullptr);
                    return lenTestAssert;
                } else {
                    // if we are performing automata-based reasoning and the term associated with
                    // this length tester is in any way constrained by regex terms,
                    // do not perform value testing -- this term is not a free variable.
                    if (m_params.m_RegexAutomata) {
                        std::map<std::pair<expr*, zstring>, expr*>::iterator it = regex_in_bool_map.begin();
                        for (; it != regex_in_bool_map.end(); ++it) {
                            expr * re = it->second;
                            expr * re_str = to_app(re)->get_arg(0);
                            // recursive descent through all subterms of re_str to see if any of them are
                            // - the same as freeVar
                            // - in the same EQC as freeVar
                            if (term_appears_as_subterm(freeVar, re_str)) {
                                TRACE("str", tout << "prevent value testing on free var " << mk_pp(freeVar, m) << " as it belongs to one or more regex constraints." << std::endl;);
                                return nullptr;
                            }
                        }
                    }

                    TRACE("str", tout << "length is fixed; generating models for free var" << std::endl;);
                    // length is fixed
                    expr * valueAssert = gen_free_var_options(freeVar, effectiveLenInd, effectiveLenIndiStr, nullptr, zstring(""));
                    return valueAssert;
                }
            } // fVarLenCountMap.find(...)

        } // !UseBinarySearch
    }

    expr * theory_str::gen_free_var_options(expr * freeVar, expr * len_indicator,
            zstring len_valueStr, expr * valTesterInCbEq, zstring valTesterValueStr) {
        ast_manager & m = get_manager();

        int len = atoi(len_valueStr.encode().c_str());

        // check whether any value tester is actually in scope
        TRACE("str", tout << "checking scope of previous value testers" << std::endl;);
        bool map_effectively_empty = true;
        if (fvar_valueTester_map.contains(freeVar) &&
                fvar_valueTester_map[freeVar].find(len) != fvar_valueTester_map[freeVar].end()) {
            // there's *something* in the map, but check its scope
            for (auto const& entry : fvar_valueTester_map[freeVar][len]) {
                expr * aTester = entry.second;
                if (!internal_variable_set.contains(aTester)) {
                    TRACE("str", tout << mk_pp(aTester, m) << " out of scope" << std::endl;);
                } else {
                    TRACE("str", tout << mk_pp(aTester, m) << " in scope" << std::endl;);
                    map_effectively_empty = false;
                    break;
                }
            }
        }

        if (map_effectively_empty) {
            TRACE("str", tout << "no previous value testers, or none of them were in scope" << std::endl;);
            int tries = 0;
            expr * val_indicator = mk_internal_valTest_var(freeVar, len, tries);
            valueTester_fvar_map.insert(val_indicator, freeVar);
            if (!fvar_valueTester_map.contains(freeVar)) {
                fvar_valueTester_map.insert(freeVar, std::map<int, svector<std::pair<int, expr*> > >());
            }
            fvar_valueTester_map[freeVar][len].push_back(std::make_pair(sLevel, val_indicator));
            print_value_tester_list(fvar_valueTester_map[freeVar][len]);
            return gen_val_options(freeVar, len_indicator, val_indicator, len_valueStr, tries);
        } else {
            TRACE("str", tout << "checking previous value testers" << std::endl;);
            print_value_tester_list(fvar_valueTester_map[freeVar][len]);

            // go through all previous value testers
            // If some doesn't have an eqc value, add its assertion again.
            int testerTotal = fvar_valueTester_map[freeVar][len].size();
            int i = 0;
            for (; i < testerTotal; i++) {
                expr * aTester = fvar_valueTester_map[freeVar][len][i].second;

                // it's probably worth checking scope here, actually
                if (!internal_variable_set.contains(aTester)) {
                    TRACE("str", tout << "value tester " << mk_pp(aTester, m) << " out of scope, skipping" << std::endl;);
                    continue;
                }

                if (aTester == valTesterInCbEq) {
                    break;
                }

                bool anEqcHasValue = false;
                get_eqc_value(aTester, anEqcHasValue);
                if (!anEqcHasValue) {
                    TRACE("str", tout << "value tester " << mk_ismt2_pp(aTester, m)
                            << " doesn't have an equivalence class value." << std::endl;);
                    refresh_theory_var(aTester);

                    expr_ref makeupAssert(gen_val_options(freeVar, len_indicator, aTester, len_valueStr, i), m);

                    TRACE("str", tout << "var: " << mk_ismt2_pp(freeVar, m) << std::endl
                            << mk_ismt2_pp(makeupAssert, m) << std::endl;);
                    assert_axiom(makeupAssert);
                } else {
                    // TRACE("str", tout << "value tester " << mk_ismt2_pp(aTester, m)
                    //      << " == " << mk_ismt2_pp(aTester_eqc_value, m) << std::endl;);
                }
            }

            if (valTesterValueStr == "more") {
                expr * valTester = nullptr;
                if (i + 1 < testerTotal) {
                    valTester = fvar_valueTester_map[freeVar][len][i + 1].second;
                    refresh_theory_var(valTester);
                } else {
                    valTester = mk_internal_valTest_var(freeVar, len, i + 1);
                    valueTester_fvar_map.insert(valTester, freeVar);
                    fvar_valueTester_map[freeVar][len].push_back(std::make_pair(sLevel, valTester));
                    print_value_tester_list(fvar_valueTester_map[freeVar][len]);
                }
                return gen_val_options(freeVar, len_indicator, valTester, len_valueStr, i + 1);
            }

            return nullptr;
        }
    }

    void theory_str::process_free_var(std::map<expr*, int> & freeVar_map) {
        context & ctx = get_context();

        obj_hashtable<expr> eqcRepSet;
        obj_hashtable<expr> leafVarSet;
        std::map<int, obj_hashtable<expr> > aloneVars;

        for (auto const& kv : freeVar_map) {
            expr * freeVar = kv.first;
            // skip all regular expression vars
            if (regex_variable_set.contains(freeVar)) {
                continue;
            }

            // Iterate the EQC of freeVar, its eqc variable should not be in the eqcRepSet.
            // If found, have to filter it out
            std::set<expr*> eqVarSet;
            get_var_in_eqc(freeVar, eqVarSet);
            bool duplicated = false;
            expr * dupVar = nullptr;
            for (expr* eq : eqVarSet) {
                if (eqcRepSet.contains(eq)) {
                    duplicated = true;
                    dupVar = eq;
                    break;
                }
            }
            if (duplicated && dupVar != nullptr) {
                TRACE("str", tout << "Duplicated free variable found:" << mk_pp(freeVar, get_manager())
                        << " = " << mk_ismt2_pp(dupVar, get_manager()) << " (SKIP)" << std::endl;);
                continue;
            } else {
                eqcRepSet.insert(freeVar);
            }
        }

        for (expr * freeVar : eqcRepSet) {
            // has length constraint initially
            bool standAlone = !input_var_in_len.contains(freeVar);
            // iterate parents
            if (standAlone) {
                // I hope this works!
                if (!ctx.e_internalized(freeVar)) {
                    ctx.internalize(freeVar, false);
                }
                enode * e_freeVar = ctx.get_enode(freeVar);
                enode_vector::iterator it = e_freeVar->begin_parents();
                for (; it != e_freeVar->end_parents(); ++it) {
                    expr * parentAst = (*it)->get_owner();
                    if (u.str.is_concat(to_app(parentAst))) {
                        standAlone = false;
                        break;
                    }
                }
            }

            if (standAlone) {
                rational len_value;
                bool len_value_exists = get_len_value(freeVar, len_value);
                if (len_value_exists) {
                    leafVarSet.insert(freeVar);
                } else {
                    aloneVars[-1].insert(freeVar);
                }
            } else {
                leafVarSet.insert(freeVar);
            }
        }

        for (expr* lv : leafVarSet) {
            expr * toAssert = gen_len_val_options_for_free_var(lv, nullptr, "");
            // gen_len_val_options_for_free_var() can legally return NULL,
            // as methods that it calls may assert their own axioms instead.
            if (toAssert) assert_axiom(toAssert);

        }

        for (auto const& kv : aloneVars) {
            for (expr* av : kv.second) {
                expr * toAssert = gen_len_val_options_for_free_var(av, nullptr, "");
                // same deal with returning a NULL axiom here
                if (toAssert) assert_axiom(toAssert);
            }
        }
    }

    bool theory_str::free_var_attempt(expr * nn1, expr * nn2) {
        zstring nn2_str;
        if (internal_lenTest_vars.contains(nn1) && u.str.is_string(nn2, nn2_str)) {
            TRACE("str", tout << "acting on equivalence between length tester var " << mk_pp(nn1, get_manager())
                  << " and constant " << mk_pp(nn2, get_manager()) << std::endl;);
            more_len_tests(nn1, nn2_str);
            return true;
        } else if (internal_valTest_vars.contains(nn1) && u.str.is_string(nn2, nn2_str)) {
            if (nn2_str == "more") {
                TRACE("str", tout << "acting on equivalence between value var " << mk_pp(nn1, get_manager())
                      << " and constant " << mk_pp(nn2, get_manager()) << std::endl;);
                more_value_tests(nn1, nn2_str);
            }
            return true;
        } else if (internal_unrollTest_vars.contains(nn1)) {
            return true;
        } else {
            return false;
        }
    }

    void theory_str::more_len_tests(expr * lenTester, zstring lenTesterValue) {
        ast_manager & m = get_manager();
        if (lenTester_fvar_map.contains(lenTester)) {
            expr * fVar = lenTester_fvar_map[lenTester];
            expr_ref toAssert(gen_len_val_options_for_free_var(fVar, lenTester, lenTesterValue), m);
            TRACE("str", tout << "asserting more length tests for free variable " << mk_ismt2_pp(fVar, m) << std::endl;);
            if (toAssert) {
                assert_axiom(toAssert);
            }
        }
    }

    void theory_str::more_value_tests(expr * valTester, zstring valTesterValue) {
        ast_manager & m = get_manager(); (void)m;

        expr * fVar = valueTester_fvar_map[valTester];
        if (m_params.m_UseBinarySearch) {
            if (!binary_search_len_tester_stack.contains(fVar) || binary_search_len_tester_stack[fVar].empty()) {
                TRACE("str", tout << "WARNING: no active length testers for " << mk_pp(fVar, m) << std::endl;);
                NOT_IMPLEMENTED_YET();
            }
            expr * effectiveLenInd = binary_search_len_tester_stack[fVar].back();
            bool hasEqcValue;
            expr * len_indicator_value = get_eqc_value(effectiveLenInd, hasEqcValue);
            if (!hasEqcValue) {
                TRACE("str", tout << "WARNING: length tester " << mk_pp(effectiveLenInd, m) << " at top of stack for " << mk_pp(fVar, m) << " has no EQC value" << std::endl;);
            } else {
                // safety check
                zstring effectiveLenIndiStr;
                u.str.is_string(len_indicator_value, effectiveLenIndiStr);
                if (effectiveLenIndiStr == "more" || effectiveLenIndiStr == "less") {
                    TRACE("str", tout << "ERROR: illegal state -- requesting 'more value tests' but a length tester is not yet concrete!" << std::endl;);
                    UNREACHABLE();
                }
                expr * valueAssert = gen_free_var_options(fVar, effectiveLenInd, effectiveLenIndiStr, valTester, valTesterValue);
                TRACE("str", tout << "asserting more value tests for free variable " << mk_ismt2_pp(fVar, m) << std::endl;);
                if (valueAssert != nullptr) {
                    assert_axiom(valueAssert);
                }
            }
        } else {
            int lenTesterCount;
            if (fvar_lenTester_map.contains(fVar)) {
                lenTesterCount = fvar_lenTester_map[fVar].size();
            } else {
                lenTesterCount = 0;
            }

            expr * effectiveLenInd = nullptr;
            zstring effectiveLenIndiStr = "";
            for (int i = 0; i < lenTesterCount; ++i) {
                expr * len_indicator_pre = fvar_lenTester_map[fVar][i];
                bool indicatorHasEqcValue = false;
                expr * len_indicator_value = get_eqc_value(len_indicator_pre, indicatorHasEqcValue);
                if (indicatorHasEqcValue) {
                    zstring len_pIndiStr;
                    u.str.is_string(len_indicator_value, len_pIndiStr);
                    if (len_pIndiStr != "more") {
                        effectiveLenInd = len_indicator_pre;
                        effectiveLenIndiStr = len_pIndiStr;
                        break;
                    }
                }
            }
            expr * valueAssert = gen_free_var_options(fVar, effectiveLenInd, effectiveLenIndiStr, valTester, valTesterValue);
            TRACE("str", tout << "asserting more value tests for free variable " << mk_ismt2_pp(fVar, m) << std::endl;);
            if (valueAssert != nullptr) {
                assert_axiom(valueAssert);
            }
        }
    }


    // Return an expression of the form
    // (tester = "less" | tester = "N" | tester = "more") &
    //   (tester = "less" iff len(freeVar) < N) & (tester = "more" iff len(freeVar) > N) & (tester = "N" iff len(freeVar) = N))
    expr_ref theory_str::binary_search_case_split(expr * freeVar, expr * tester, binary_search_info & bounds, literal_vector & case_split) {
        context & ctx = get_context();
        ast_manager & m = get_manager();
        rational N = bounds.midPoint;
        rational N_minus_one = N - rational::one();
        rational N_plus_one = N + rational::one();
        expr_ref lenFreeVar(mk_strlen(freeVar), m);

        TRACE("str", tout << "create case split for free var " << mk_pp(freeVar, m)
                << " over " << mk_pp(tester, m) << " with midpoint " << N << std::endl;);

        expr_ref_vector combinedCaseSplit(m);
        expr_ref_vector testerCases(m);

        expr_ref caseLess(ctx.mk_eq_atom(tester, mk_string("less")), m);
        testerCases.push_back(caseLess);
        combinedCaseSplit.push_back(ctx.mk_eq_atom(caseLess, m_autil.mk_le(lenFreeVar, m_autil.mk_numeral(N_minus_one, true) )));

        expr_ref caseMore(ctx.mk_eq_atom(tester, mk_string("more")), m);
        testerCases.push_back(caseMore);
        combinedCaseSplit.push_back(ctx.mk_eq_atom(caseMore, m_autil.mk_ge(lenFreeVar, m_autil.mk_numeral(N_plus_one, true) )));

        expr_ref caseEq(ctx.mk_eq_atom(tester, mk_string(N.to_string().c_str())), m);
        testerCases.push_back(caseEq);
        combinedCaseSplit.push_back(ctx.mk_eq_atom(caseEq, ctx.mk_eq_atom(lenFreeVar, m_autil.mk_numeral(N, true))));

        combinedCaseSplit.push_back(mk_or(testerCases));

        // force internalization on all terms in testerCases so we can extract literals
        for (unsigned i = 0; i < testerCases.size(); ++i) {
            expr * testerCase = testerCases.get(i);
            if (!ctx.b_internalized(testerCase)) {
                ctx.internalize(testerCase, false);
            }
            literal l = ctx.get_literal(testerCase);
            case_split.push_back(l);
        }

        expr_ref final_term(mk_and(combinedCaseSplit), m);
        SASSERT(final_term);
        TRACE("str", tout << "final term: " << mk_pp(final_term, m) << std::endl;);
        return final_term;
    }

    expr * theory_str::binary_search_length_test(expr * freeVar, expr * previousLenTester, zstring previousLenTesterValue) {
        ast_manager & m = get_manager();

        if (binary_search_len_tester_stack.contains(freeVar) && !binary_search_len_tester_stack[freeVar].empty()) {
            TRACE("str", tout << "checking existing length testers for " << mk_pp(freeVar, m) << std::endl;
            for (ptr_vector<expr>::const_iterator it = binary_search_len_tester_stack[freeVar].begin();
                    it != binary_search_len_tester_stack[freeVar].end(); ++it) {
                expr * tester = *it;
                tout << mk_pp(tester, m) << ": ";
                if (binary_search_len_tester_info.contains(tester)) {
                    binary_search_info & bounds = binary_search_len_tester_info[tester];
                    tout << "[" << bounds.lowerBound << " | " << bounds.midPoint << " | " << bounds.upperBound << "]!" << bounds.windowSize;
                } else {
                    tout << "[WARNING: no bounds info available]";
                }
                bool hasEqcValue;
                expr * testerEqcValue = get_eqc_value(tester, hasEqcValue);
                if (hasEqcValue) {
                    tout << " = " << mk_pp(testerEqcValue, m);
                } else {
                    tout << " [no eqc value]";
                }
                tout << std::endl;
            }
            );
            expr * lastTester = binary_search_len_tester_stack[freeVar].back();
            bool lastTesterHasEqcValue;
            expr * lastTesterValue = get_eqc_value(lastTester, lastTesterHasEqcValue);
            zstring lastTesterConstant;
            if (!lastTesterHasEqcValue) {
                TRACE("str", tout << "length tester " << mk_pp(lastTester, m) << " at top of stack doesn't have an EQC value yet" << std::endl;);
                // check previousLenTester
                if (previousLenTester == lastTester) {
                    lastTesterConstant = previousLenTesterValue;
                    TRACE("str", tout << "invoked with previousLenTester info matching top of stack" << std::endl;);
                } else {
                    TRACE("str", tout << "WARNING: unexpected reordering of length testers!" << std::endl;);
                    UNREACHABLE(); return nullptr;
                }
            } else {
                u.str.is_string(lastTesterValue, lastTesterConstant);
            }
            TRACE("str", tout << "last length tester is assigned \"" << lastTesterConstant << "\"" << "\n";);
            if (lastTesterConstant == "more" || lastTesterConstant == "less") {
                // use the previous bounds info to generate a new midpoint
                binary_search_info lastBounds;
                if (!binary_search_len_tester_info.find(lastTester, lastBounds)) {
                    // unexpected
                    TRACE("str", tout << "WARNING: no bounds information available for last tester!" << std::endl;);
                    UNREACHABLE();
                }
                TRACE("str", tout << "last bounds are [" << lastBounds.lowerBound << " | " << lastBounds.midPoint << " | " << lastBounds.upperBound << "]!" << lastBounds.windowSize << std::endl;);
                binary_search_info newBounds;
                expr * newTester = nullptr;
                if (lastTesterConstant == "more") {
                    // special case: if the midpoint, upper bound, and window size are all equal,
                    // we double the window size and adjust the bounds
                    if (lastBounds.midPoint == lastBounds.upperBound && lastBounds.upperBound == lastBounds.windowSize) {
                        TRACE("str", tout << "search hit window size; expanding" << std::endl;);
                        newBounds.lowerBound = lastBounds.windowSize + rational::one();
                        newBounds.windowSize = lastBounds.windowSize * rational(2);
                        newBounds.upperBound = newBounds.windowSize;
                        newBounds.calculate_midpoint();
                    } else if (false) {
                        // handle the case where the midpoint can't be increased further
                        // (e.g. a window like [50 | 50 | 50]!64 and we don't answer "50")
                    } else {
                        // general case
                        newBounds.lowerBound = lastBounds.midPoint + rational::one();
                        newBounds.windowSize = lastBounds.windowSize;
                        newBounds.upperBound = lastBounds.upperBound;
                        newBounds.calculate_midpoint();
                    }
                    if (!binary_search_next_var_high.find(lastTester, newTester)) {
                        newTester = mk_internal_lenTest_var(freeVar, newBounds.midPoint.get_int32());
                        binary_search_next_var_high.insert(lastTester, newTester);
                    }
                    refresh_theory_var(newTester);
                } else if (lastTesterConstant == "less") {
                    if (false) {
                        // handle the case where the midpoint can't be decreased further
                        // (e.g. a window like [0 | 0 | 0]!64 and we don't answer "0"
                    } else {
                        // general case
                        newBounds.upperBound = lastBounds.midPoint - rational::one();
                        newBounds.windowSize = lastBounds.windowSize;
                        newBounds.lowerBound = lastBounds.lowerBound;
                        newBounds.calculate_midpoint();
                    }
                    if (!binary_search_next_var_low.find(lastTester, newTester)) {
                        newTester = mk_internal_lenTest_var(freeVar, newBounds.midPoint.get_int32());
                        binary_search_next_var_low.insert(lastTester, newTester);
                    }
                    refresh_theory_var(newTester);
                }
                TRACE("str", tout << "new bounds are [" << newBounds.lowerBound << " | " << newBounds.midPoint << " | " << newBounds.upperBound << "]!" << newBounds.windowSize << std::endl;);
                binary_search_len_tester_stack[freeVar].push_back(newTester);
                m_trail_stack.push(binary_search_trail<theory_str>(binary_search_len_tester_stack, freeVar));
                binary_search_len_tester_info.insert(newTester, newBounds);
                m_trail_stack.push(insert_obj_map<theory_str, expr, binary_search_info>(binary_search_len_tester_info, newTester));

                literal_vector case_split_literals;
                expr_ref next_case_split(binary_search_case_split(freeVar, newTester, newBounds, case_split_literals));
                m_trail.push_back(next_case_split);
                // ctx.mk_th_case_split(case_split_literals.size(), case_split_literals.c_ptr());
                return next_case_split;
            } else { // lastTesterConstant is a concrete value
                TRACE("str", tout << "length is fixed; generating models for free var" << std::endl;);
                // defensive check that this length did not converge on a negative value.
                binary_search_info lastBounds;
                if (!binary_search_len_tester_info.find(lastTester, lastBounds)) {
                    // unexpected
                    TRACE("str", tout << "WARNING: no bounds information available for last tester!" << std::endl;);
                    UNREACHABLE();
                }
                if (lastBounds.midPoint.is_neg()) {
                    TRACE("str", tout << "WARNING: length search converged on a negative value. Negating this constraint." << std::endl;);
                    expr_ref axiom(m_autil.mk_ge(mk_strlen(freeVar), m_autil.mk_numeral(rational::zero(), true)), m);
                    return axiom;
                }
                // length is fixed
                expr * valueAssert = gen_free_var_options(freeVar, lastTester, lastTesterConstant, nullptr, zstring(""));
                return valueAssert;
            }
        } else {
            // no length testers yet
            TRACE("str", tout << "no length testers for " << mk_pp(freeVar, m) << std::endl;);
            binary_search_len_tester_stack.insert(freeVar, ptr_vector<expr>());

            expr * firstTester;
            rational lowerBound(0);
            rational upperBound(m_params.m_BinarySearchInitialUpperBound);
            rational windowSize(upperBound);
            rational midPoint(floor(upperBound / rational(2)));
            if (!binary_search_starting_len_tester.find(freeVar, firstTester)) {
                firstTester = mk_internal_lenTest_var(freeVar, midPoint.get_int32());
                binary_search_starting_len_tester.insert(freeVar, firstTester);
            }
            refresh_theory_var(firstTester);

            {
                rational freeVar_len_value;
                if (get_len_value(freeVar, freeVar_len_value)) {
                    TRACE("str", tout << "special case: length of freeVar is known to be " << freeVar_len_value << std::endl;);
                    midPoint = freeVar_len_value;
                    upperBound = midPoint * 2;
                    windowSize = upperBound;
                }
            }

            binary_search_len_tester_stack[freeVar].push_back(firstTester);
            m_trail_stack.push(binary_search_trail<theory_str>(binary_search_len_tester_stack, freeVar));
            binary_search_info new_info(lowerBound, midPoint, upperBound, windowSize);
            binary_search_len_tester_info.insert(firstTester, new_info);
            m_trail_stack.push(insert_obj_map<theory_str, expr, binary_search_info>(binary_search_len_tester_info, firstTester));

            literal_vector case_split_literals;
            expr_ref initial_case_split(binary_search_case_split(freeVar, firstTester, new_info, case_split_literals));
            m_trail.push_back(initial_case_split);
            // ctx.mk_th_case_split(case_split_literals.size(), case_split_literals.c_ptr());
            return initial_case_split;
        }
    }

    static int computeGCD(int x, int y) {
        if (x == 0) {
            return y;
        }
        while (y != 0) {
            if (x > y) {
                x = x - y;
            } else {
                y = y - x;
            }
        }
        return x;
    }

    static int computeLCM(int a, int b) {
        int temp = computeGCD(a, b);
        return temp ? (a / temp * b) : 0;
    }

    static zstring get_unrolled_string(zstring core, int count) {
        zstring res("");
        for (int i = 0; i < count; i++) {
            res = res + core;
        }
        return res;
    }

    expr * theory_str::gen_assign_unroll_Str2Reg(expr * n, std::set<expr*> & unrolls) {
        context & ctx = get_context();
        ast_manager & mgr = get_manager();

        int lcm = 1;
        int coreValueCount = 0;
        expr * oneUnroll = nullptr;
        zstring oneCoreStr("");
        for (std::set<expr*>::iterator itor = unrolls.begin(); itor != unrolls.end(); itor++) {
            expr * str2RegFunc = to_app(*itor)->get_arg(0);
            expr * coreVal = to_app(str2RegFunc)->get_arg(0);
            zstring coreStr;
            u.str.is_string(coreVal, coreStr);
            if (oneUnroll == nullptr) {
                oneUnroll = *itor;
                oneCoreStr = coreStr;
            }
            coreValueCount++;
            int core1Len = coreStr.length();
            lcm = computeLCM(lcm, core1Len);
        }
        //
        bool canHaveNonEmptyAssign = true;
        expr_ref_vector litems(mgr);
        zstring lcmStr = get_unrolled_string(oneCoreStr, (lcm / oneCoreStr.length()));
        for (std::set<expr*>::iterator itor = unrolls.begin(); itor != unrolls.end(); itor++) {
            expr * str2RegFunc = to_app(*itor)->get_arg(0);
            expr * coreVal = to_app(str2RegFunc)->get_arg(0);
            zstring coreStr;
            u.str.is_string(coreVal, coreStr);
            unsigned int core1Len = coreStr.length();
            zstring uStr = get_unrolled_string(coreStr, (lcm / core1Len));
            if (uStr != lcmStr) {
                canHaveNonEmptyAssign = false;
            }
            litems.push_back(ctx.mk_eq_atom(n, *itor));
        }

        if (canHaveNonEmptyAssign) {
            return gen_unroll_conditional_options(n, unrolls, lcmStr);
        } else {
            expr_ref implyL(mk_and(litems), mgr);
            expr_ref implyR(ctx.mk_eq_atom(n, mk_string("")), mgr);
            // want to return (implyL -> implyR)
            expr * final_axiom = rewrite_implication(implyL, implyR);
            return final_axiom;
        }
    }

    expr * theory_str::gen_unroll_conditional_options(expr * var, std::set<expr*> & unrolls, zstring lcmStr) {
        context & ctx = get_context();
        ast_manager & mgr = get_manager();

        int dist = opt_LCMUnrollStep;
        expr_ref_vector litems(mgr);
        expr_ref moreAst(mk_string("more"), mgr);
        for (expr * e : unrolls) {
            expr_ref item(ctx.mk_eq_atom(var, e), mgr);
            TRACE("str", tout << "considering unroll " << mk_pp(item, mgr) << std::endl;);
            litems.push_back(item);
        }

        // handle out-of-scope entries in unroll_tries_map

        ptr_vector<expr> outOfScopeTesters;

        for (expr * tester : unroll_tries_map[var][unrolls]) {
            bool inScope = internal_unrollTest_vars.contains(tester);
            TRACE("str", tout << "unroll test var " << mk_pp(tester, mgr)
                    << (inScope ? " in scope" : " out of scope")
                    << std::endl;);
            if (!inScope) {
                outOfScopeTesters.push_back(tester);
            }
        }

        for (expr* e : outOfScopeTesters) {
            unroll_tries_map[var][unrolls].erase(e);
        }

        if (unroll_tries_map[var][unrolls].empty()) {
            unroll_tries_map[var][unrolls].push_back(mk_unroll_test_var());
        }

        int tries = unroll_tries_map[var][unrolls].size();
        for (int i = 0; i < tries; i++) {
            expr * tester = unroll_tries_map[var][unrolls][i];
            // TESTING
            refresh_theory_var(tester);
            bool testerHasValue = false;
            expr * testerVal = get_eqc_value(tester, testerHasValue);
            if (!testerHasValue) {
                // generate make-up assertion
                int l = i * dist;
                int h = (i + 1) * dist;
                expr_ref lImp(mk_and(litems), mgr);
                expr_ref rImp(gen_unroll_assign(var, lcmStr, tester, l, h), mgr);

                SASSERT(lImp);
                TRACE("str", tout << "lImp = " << mk_pp(lImp, mgr) << std::endl;);
                SASSERT(rImp);
                TRACE("str", tout << "rImp = " << mk_pp(rImp, mgr) << std::endl;);

                expr_ref toAssert(mgr.mk_or(mgr.mk_not(lImp), rImp), mgr);
                SASSERT(toAssert);
                TRACE("str", tout << "Making up assignments for variable which is equal to unbounded Unroll" << std::endl;);
                m_trail.push_back(toAssert);
                return toAssert;

                // note: this is how the code looks in Z3str2's strRegex.cpp:genUnrollConditionalOptions.
                // the return is in the same place

                // insert [tester = "more"] to litems so that the implyL for next tester is correct
                litems.push_back(ctx.mk_eq_atom(tester, moreAst));
            } else {
                zstring testerStr;
                u.str.is_string(testerVal, testerStr);
                TRACE("str", tout << "Tester [" << mk_pp(tester, mgr) << "] = " << testerStr << "\n";);
                if (testerStr == "more") {
                    litems.push_back(ctx.mk_eq_atom(tester, moreAst));
                }
            }
        }
        expr * tester = mk_unroll_test_var();
        unroll_tries_map[var][unrolls].push_back(tester);
        int l = tries * dist;
        int h = (tries + 1) * dist;
        expr_ref lImp(mk_and(litems), mgr);
        expr_ref rImp(gen_unroll_assign(var, lcmStr, tester, l, h), mgr);
        SASSERT(lImp);
        SASSERT(rImp);
        expr_ref toAssert(mgr.mk_or(mgr.mk_not(lImp), rImp), mgr);
        SASSERT(toAssert);
        TRACE("str", tout << "Generating assignment for variable which is equal to unbounded Unroll" << std::endl;);
        m_trail.push_back(toAssert);
        return toAssert;
    }

    expr * theory_str::gen_unroll_assign(expr * var, zstring lcmStr, expr * testerVar, int l, int h) {
        context & ctx = get_context();
        ast_manager & mgr = get_manager();

        TRACE("str", tout << "entry: var = " << mk_pp(var, mgr) << ", lcmStr = " << lcmStr
                << ", l = " << l << ", h = " << h << "\n";);

        if (m_params.m_AggressiveUnrollTesting) {
            TRACE("str", tout << "note: aggressive unroll testing is active" << std::endl;);
        }

        expr_ref_vector orItems(mgr);
        expr_ref_vector andItems(mgr);

        for (int i = l; i < h; i++) {
            zstring iStr = int_to_string(i);
            expr_ref testerEqAst(ctx.mk_eq_atom(testerVar, mk_string(iStr)), mgr);
            TRACE("str", tout << "testerEqAst = " << mk_pp(testerEqAst, mgr) << std::endl;);
            if (m_params.m_AggressiveUnrollTesting) {
                literal l = mk_eq(testerVar, mk_string(iStr), false);
                ctx.mark_as_relevant(l);
                ctx.force_phase(l);
            }

            orItems.push_back(testerEqAst);
            zstring unrollStrInstance = get_unrolled_string(lcmStr, i);

            expr_ref x1(ctx.mk_eq_atom(testerEqAst, ctx.mk_eq_atom(var, mk_string(unrollStrInstance))), mgr);
            TRACE("str", tout << "x1 = " << mk_pp(x1, mgr) << std::endl;);
            andItems.push_back(x1);

            expr_ref x2(ctx.mk_eq_atom(testerEqAst, ctx.mk_eq_atom(mk_strlen(var), mk_int(i * lcmStr.length()))), mgr);
            TRACE("str", tout << "x2 = " << mk_pp(x2, mgr) << std::endl;);
            andItems.push_back(x2);
        }
        expr_ref testerEqMore(ctx.mk_eq_atom(testerVar, mk_string("more")), mgr);
        TRACE("str", tout << "testerEqMore = " << mk_pp(testerEqMore, mgr) << std::endl;);
        if (m_params.m_AggressiveUnrollTesting) {
            literal l = mk_eq(testerVar, mk_string("more"), false);
            ctx.mark_as_relevant(l);
            ctx.force_phase(~l);
        }

        orItems.push_back(testerEqMore);
        int nextLowerLenBound = h * lcmStr.length();
        expr_ref more2(ctx.mk_eq_atom(testerEqMore,
                //Z3_mk_ge(mk_length(t, var), mk_int(ctx, nextLowerLenBound))
                m_autil.mk_ge(m_autil.mk_add(mk_strlen(var), mk_int(-1 * nextLowerLenBound)), mk_int(0))
        ), mgr);
        TRACE("str", tout << "more2 = " << mk_pp(more2, mgr) << std::endl;);
        andItems.push_back(more2);

        expr_ref finalOR(mgr.mk_or(orItems.size(), orItems.c_ptr()), mgr);
        TRACE("str", tout << "finalOR = " << mk_pp(finalOR, mgr) << std::endl;);
        andItems.push_back(mk_or(orItems));

        expr_ref finalAND(mgr.mk_and(andItems.size(), andItems.c_ptr()), mgr);
        TRACE("str", tout << "finalAND = " << mk_pp(finalAND, mgr) << std::endl;);

        // doing the following avoids a segmentation fault
        m_trail.push_back(finalAND);
        return finalAND;
    }

    void theory_str::print_value_tester_list(svector<std::pair<int, expr*> > & testerList) {
            TRACE("str",
                  int ss = testerList.size();
                  tout << "valueTesterList = {";
                  for (int i = 0; i < ss; ++i) {
                      if (i % 4 == 0) {
                          tout << std::endl;
                      }
                      tout << "(" << testerList[i].first << ", ";
                      tout << mk_pp(testerList[i].second, get_manager());
                      tout << "), ";
                  }
                  tout << std::endl << "}" << std::endl;
                  );
        }

        zstring theory_str::gen_val_string(int len, int_vector & encoding) {
            SASSERT(charSetSize > 0);
            SASSERT(!char_set.empty());

            std::string re(len, char_set[0]);
            for (int i = 0; i < (int) encoding.size() - 1; i++) {
                int idx = encoding[i];
                re[len - 1 - i] = char_set[idx];
            }
            return zstring(re.c_str());
        }

        void theory_str::reduce_virtual_regex_in(expr * var, expr * regex, expr_ref_vector & items) {
            context & ctx = get_context();
            ast_manager & mgr = get_manager();

            TRACE("str", tout << "reduce regex " << mk_pp(regex, mgr) << " with respect to variable " << mk_pp(var, mgr) << std::endl;);

            app * regexFuncDecl = to_app(regex);
            if (u.re.is_to_re(regexFuncDecl)) {
                // ---------------------------------------------------------
                // var \in Str2Reg(s1)
                //   ==>
                // var = s1 /\ length(var) = length(s1)
                // ---------------------------------------------------------
                expr * strInside = to_app(regex)->get_arg(0);
                items.push_back(ctx.mk_eq_atom(var, strInside));
                items.push_back(ctx.mk_eq_atom(mk_strlen(var), mk_strlen(strInside)));
                return;
            }
            // RegexUnion
            else if (u.re.is_union(regexFuncDecl)) {
                // ---------------------------------------------------------
                // var \in RegexUnion(r1, r2)
                //   ==>
                // (var = newVar1 \/ var = newVar2)
                // (var = newVar1 --> length(var) = length(newVar1)) /\ (var = newVar2 --> length(var) = length(newVar2))
                //  /\ (newVar1 \in r1) /\  (newVar2 \in r2)
                // ---------------------------------------------------------
                expr_ref newVar1(mk_regex_rep_var(), mgr);
                expr_ref newVar2(mk_regex_rep_var(), mgr);
                items.push_back(mgr.mk_or(ctx.mk_eq_atom(var, newVar1), ctx.mk_eq_atom(var, newVar2)));
                items.push_back(mgr.mk_or(
                        mgr.mk_not(ctx.mk_eq_atom(var, newVar1)),
                        ctx.mk_eq_atom(mk_strlen(var), mk_strlen(newVar1))));
                items.push_back(mgr.mk_or(
                        mgr.mk_not(ctx.mk_eq_atom(var, newVar2)),
                        ctx.mk_eq_atom(mk_strlen(var), mk_strlen(newVar2))));

                expr * regArg1 = to_app(regex)->get_arg(0);
                reduce_virtual_regex_in(newVar1, regArg1, items);

                expr * regArg2 = to_app(regex)->get_arg(1);
                reduce_virtual_regex_in(newVar2, regArg2, items);

                return;
            }
            // RegexConcat
            else if (u.re.is_concat(regexFuncDecl)) {
                // ---------------------------------------------------------
                // var \in RegexConcat(r1, r2)
                //   ==>
                //    (var = newVar1 . newVar2) /\ (length(var) = length(vewVar1 . newVar2) )
                // /\ (newVar1 \in r1) /\  (newVar2 \in r2)
                // ---------------------------------------------------------
                expr_ref newVar1(mk_regex_rep_var(), mgr);
                expr_ref newVar2(mk_regex_rep_var(), mgr);
                expr_ref concatAst(mk_concat(newVar1, newVar2), mgr);
                items.push_back(ctx.mk_eq_atom(var, concatAst));
                items.push_back(ctx.mk_eq_atom(mk_strlen(var),
                        m_autil.mk_add(mk_strlen(newVar1), mk_strlen(newVar2))));

                expr * regArg1 = to_app(regex)->get_arg(0);
                reduce_virtual_regex_in(newVar1, regArg1, items);
                expr * regArg2 = to_app(regex)->get_arg(1);
                reduce_virtual_regex_in(newVar2, regArg2, items);
                return;
            }
            // Unroll
            else if (u.re.is_star(regexFuncDecl)) {
                // ---------------------------------------------------------
                // var \in Star(r1)
                //   ==>
                // var = unroll(r1, t1) /\ |var| = |unroll(r1, t1)|
                // ---------------------------------------------------------
                expr * regArg = to_app(regex)->get_arg(0);
                expr_ref unrollCnt(mk_unroll_bound_var(), mgr);
                expr_ref unrollFunc(mk_unroll(regArg, unrollCnt), mgr);
                items.push_back(ctx.mk_eq_atom(var, unrollFunc));
                items.push_back(ctx.mk_eq_atom(mk_strlen(var), mk_strlen(unrollFunc)));
                return;
            }
            // re.range
            else if (u.re.is_range(regexFuncDecl)) {
                // var in range("a", "z")
                // ==>
                // (var = "a" or var = "b" or ... or var = "z")
                expr_ref lo(regexFuncDecl->get_arg(0), mgr);
                expr_ref hi(regexFuncDecl->get_arg(1), mgr);
                zstring str_lo, str_hi;
                SASSERT(u.str.is_string(lo));
                SASSERT(u.str.is_string(hi));
                u.str.is_string(lo, str_lo);
                u.str.is_string(hi, str_hi);
                SASSERT(str_lo.length() == 1);
                SASSERT(str_hi.length() == 1);
                unsigned int c1 = str_lo[0];
                unsigned int c2 = str_hi[0];
                if (c1 > c2) {
                    // exchange
                    unsigned int tmp = c1;
                    c1 = c2;
                    c2 = tmp;
                }
                expr_ref_vector range_cases(mgr);
                for (unsigned int ch = c1; ch <= c2; ++ch) {
                    zstring s_ch(ch);
                    expr_ref rhs(ctx.mk_eq_atom(var, u.str.mk_string(s_ch)), mgr);
                    range_cases.push_back(rhs);
                }
                expr_ref rhs(mk_or(range_cases), mgr);
                SASSERT(rhs);
                assert_axiom(rhs);
                return;
            } else {
                get_manager().raise_exception("unrecognized regex operator");
                UNREACHABLE();
            }
        }

        void theory_str::gen_assign_unroll_reg(std::set<expr*> & unrolls) {
            context & ctx = get_context();
            ast_manager & mgr = get_manager();

            expr_ref_vector items(mgr);
            for (std::set<expr*>::iterator itor = unrolls.begin(); itor != unrolls.end(); itor++) {
                expr * unrFunc = *itor;
                TRACE("str", tout << "generating assignment for unroll " << mk_pp(unrFunc, mgr) << std::endl;);

                expr * regexInUnr = to_app(unrFunc)->get_arg(0);
                expr * cntInUnr = to_app(unrFunc)->get_arg(1);
                items.reset();

                rational low, high;
                bool low_exists = lower_bound(cntInUnr, low); (void)low_exists;
                bool high_exists = upper_bound(cntInUnr, high); (void)high_exists;

                TRACE("str",
                        tout << "unroll " << mk_pp(unrFunc, mgr) << std::endl;
                rational unrLenValue;
                bool unrLenValue_exists = get_len_value(unrFunc, unrLenValue);
                tout << "unroll length: " << (unrLenValue_exists ? unrLenValue.to_string() : "?") << std::endl;
                rational cntInUnrValue;
                bool cntHasValue = get_arith_value(cntInUnr, cntInUnrValue);
                tout << "unroll count: " << (cntHasValue ? cntInUnrValue.to_string() : "?")
                              << " low = "
                              << (low_exists ? low.to_string() : "?")
                              << " high = "
                              << (high_exists ? high.to_string() : "?")
                              << std::endl;
                );

                expr_ref toAssert(mgr);
                if (low.is_neg()) {
                    toAssert = m_autil.mk_ge(cntInUnr, mk_int(0));
                } else {
                    if (!unroll_var_map.contains(unrFunc)) {

                        expr_ref newVar1(mk_regex_rep_var(), mgr);
                        expr_ref newVar2(mk_regex_rep_var(), mgr);
                        expr_ref concatAst(mk_concat(newVar1, newVar2), mgr);
                        expr_ref newCnt(mk_unroll_bound_var(), mgr);
                        expr_ref newUnrollFunc(mk_unroll(regexInUnr, newCnt), mgr);

                        // unroll(r1, t1) = newVar1 . newVar2
                        items.push_back(ctx.mk_eq_atom(unrFunc, concatAst));
                        items.push_back(ctx.mk_eq_atom(mk_strlen(unrFunc), m_autil.mk_add(mk_strlen(newVar1), mk_strlen(newVar2))));
                        // mk_strlen(unrFunc) >= mk_strlen(newVar{1,2})
                        items.push_back(m_autil.mk_ge(m_autil.mk_add(mk_strlen(unrFunc), m_autil.mk_mul(mk_int(-1), mk_strlen(newVar1))), mk_int(0)));
                        items.push_back(m_autil.mk_ge(m_autil.mk_add(mk_strlen(unrFunc), m_autil.mk_mul(mk_int(-1), mk_strlen(newVar2))), mk_int(0)));
                        // newVar1 \in r1
                        reduce_virtual_regex_in(newVar1, regexInUnr, items);
                        items.push_back(ctx.mk_eq_atom(cntInUnr, m_autil.mk_add(newCnt, mk_int(1))));
                        items.push_back(ctx.mk_eq_atom(newVar2, newUnrollFunc));
                        items.push_back(ctx.mk_eq_atom(mk_strlen(newVar2), mk_strlen(newUnrollFunc)));
                        toAssert = ctx.mk_eq_atom(
                                m_autil.mk_ge(cntInUnr, mk_int(1)),
                                mk_and(items));

                        // option 0
                        expr_ref op0(ctx.mk_eq_atom(cntInUnr, mk_int(0)), mgr);
                        expr_ref ast1(ctx.mk_eq_atom(unrFunc, mk_string("")), mgr);
                        expr_ref ast2(ctx.mk_eq_atom(mk_strlen(unrFunc), mk_int(0)), mgr);
                        expr_ref and1(mgr.mk_and(ast1, ast2), mgr);

                        // put together
                        toAssert = mgr.mk_and(ctx.mk_eq_atom(op0, and1), toAssert);

                        unroll_var_map.insert(unrFunc, toAssert);
                    }
                    else {
                        toAssert = unroll_var_map[unrFunc];
                    }
                }
                m_trail.push_back(toAssert);
                assert_axiom(toAssert);
            }
        }


}; // namespace smt
