/*++
Copyright (c) 2017 Microsoft Corporation and Arie Gurfinkel

Module Name:

    spacer_quant_generalizer.cpp

Abstract:

    Quantified lemma generalizer.

Author:


    Yakir Vizel
    Arie Gurfinkel

Revision History:

--*/


#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_manager.h"
#include "ast/expr_abstract.h"
#include "ast/rewriter/var_subst.h"
#include "ast/for_each_expr.h"
#include "ast/factor_equivs.h"
#include "muz/spacer/spacer_term_graph.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/substitution/matcher.h"
#include "ast/expr_functors.h"

#include "muz/spacer/spacer_sem_matcher.h"

using namespace spacer;

namespace {
struct index_lt_proc : public std::binary_function<app*, app *, bool> {
    arith_util m_arith;
    index_lt_proc(ast_manager &m) : m_arith(m) {}
    bool operator() (app *a, app *b) {
        // XXX This order is a bit strange.
        // XXX It does the job in our current application, but only because
        // XXX we assume that we only compare expressions of the form (B + k),
        // XXX where B is fixed and k is a number.
        // XXX Might be better to specialize just for that specific use case.
        rational val1, val2;
        bool is_num1 = m_arith.is_numeral(a, val1);
        bool is_num2 = m_arith.is_numeral(b, val2);

        if (is_num1 && is_num2) {
            return val1 < val2;
        }
        else if (is_num1 != is_num2) {
            return is_num1;
        }

        is_num1 = false;
        is_num2 = false;
        // compare the first numeric argument of a to first numeric argument of b
        // if available
        for (unsigned i = 0, sz = a->get_num_args(); !is_num1 && i < sz; ++i) {
            is_num1 = m_arith.is_numeral (a->get_arg(i), val1);
        }
        for (unsigned i = 0, sz = b->get_num_args(); !is_num2 && i < sz; ++i) {
            is_num2 = m_arith.is_numeral(b->get_arg(i), val2);
        }

        if (is_num1 && is_num2) {
            return val1 < val2;
        }
        else if (is_num1 != is_num2) {
            return is_num1;
        }
        else {
            return a->get_id() < b->get_id();
        }

    }
};

}

namespace spacer {

lemma_quantifier_generalizer::lemma_quantifier_generalizer(context &ctx) :
    lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m) {}

void lemma_quantifier_generalizer::collect_statistics(statistics &st) const
{
    st.update("time.spacer.solve.reach.gen.quant", m_st.watch.get_seconds());
    st.update("quantifier gen", m_st.count);
    st.update("quantifier gen failures", m_st.num_failures);
}

// XXX What does this do?
void lemma_quantifier_generalizer::find_candidates(
    expr *e, app_ref_vector &candidates)
{
    if (!contains_selects(e, m)) return;

    app_ref_vector indices(m);
    get_select_indices(e, indices, m);

    app_ref_vector extra(m);
    expr_sparse_mark marked_args;

    // Make sure not to try and quantify already-quantified indices
    for (unsigned idx=0, sz = indices.size(); idx < sz; idx++) {
        // skip expressions that already contain a quantified variable
        if (has_zk_const(indices.get(idx))) {
            continue;
        }

        app *index = indices.get(idx);
        TRACE ("spacer_qgen",
               tout << "Candidate: "<< mk_pp(index, m)
               << " in " << mk_pp(e, m) << "\n";);
        extra.push_back(index);
        // XXX expand one level of arguments. Might want to go deeper.
        for (unsigned j = 0, asz = index->get_num_args(); j < asz; j++) {
            expr *arg = index->get_arg(j);
            if (!is_app(arg) || marked_args.is_marked(arg)) {continue;}
            marked_args.mark(arg);
            candidates.push_back (to_app(arg));
        }
    }

    std::sort(candidates.c_ptr(), candidates.c_ptr() + candidates.size(),
              index_lt_proc(m));
    // keep actual select indecies in the order found at the back of
    // candidate list

    // XXX this corresponds to current implementation. Probably should
    // XXX be sorted together with the rest of candidates
    candidates.append(extra);
}

/* subs are the variables that might appear in the patterns */
void lemma_quantifier_generalizer::generate_patterns(
    expr_ref_vector const &cube, app_ref_vector const &candidates,
    var_ref_vector &subs, expr_ref_vector &patterns, unsigned offset)
{
    if (candidates.empty()) return;

    expr_safe_replace ses(m);

    // Setup substitution
    for (unsigned i=0; i < candidates.size(); i++) {
        expr *cand = candidates.get(i);
        var *var = m.mk_var(i+offset, get_sort(cand));
        ses.insert(cand, var);
        rational val;
        if (m_arith.is_numeral(cand, val)) {
            bool is_int = val.is_int();
            ses.insert(
                m_arith.mk_numeral(rational(val+1), is_int),
                m_arith.mk_add(var, m_arith.mk_numeral(rational(1), is_int)));
            ses.insert(
                m_arith.mk_numeral(rational(-1*(val+1)), is_int),
                m_arith.mk_add(m_arith.mk_sub(m_arith.mk_numeral(rational(0), is_int),var), m_arith.mk_numeral(rational(-1), is_int)));
        }
        subs.push_back(var);
    }

    // Generate patterns

    // for every literal
    for (unsigned j=0; j < cube.size(); j++) {
        // abstract terms by variables
        expr_ref pat(m);
        ses(cube.get(j), pat);

        if (pat.get() != cube.get(j)) {
            // if abstraction is not identity
            TRACE("spacer_qgen",
                  tout << "Pattern is: " << mk_pp(pat, m) << "\n";);

            // store the pattern
            patterns.push_back(pat);
        }
    }
}

void lemma_quantifier_generalizer::find_matching_expressions(
    expr_ref_vector const &cube,
    var_ref_vector const &subs, expr_ref_vector &patterns,
    vector<expr_ref_vector> &idx_instances,
    vector<bool> &dirty)
{
    idx_instances.resize(subs.size(), expr_ref_vector(m));
    // -- for every pattern
    for (unsigned p = 0; p < patterns.size(); p++) {
        expr *pattern = patterns.get(p);
        // -- for every literal
        for (unsigned j = 0; j < cube.size(); j++) {
            if (dirty[j] || !is_app(cube.get(j))) continue;
            app *lit = to_app(cube.get(j));

            sem_matcher match(m);
            bool pos;
            substitution v_sub(m);

            // allocate space for the largest variable in the pattern
            unsigned max_idx = 0;
            for (var* v : subs) {max_idx = std::max(max_idx, v->get_idx());}
            v_sub.reserve(2, max_idx + 1);

            if (!match(pattern, lit, v_sub, pos)) {
                continue;
            }
            // expect positive matches only
            if (!pos) {continue;}

            dirty[j] = true;
            for (unsigned v = 0; v < subs.size(); v++) {
                expr_offset idx;
                if (v_sub.find(subs.get(v), 0, idx)) {
                    TRACE ("spacer_qgen", tout << "INSTANCE IS: " << mk_pp(idx.get_expr(), m) << "\n";);
                    idx_instances[v].push_back(idx.get_expr());
                }
            }
        }
    }
}


void lemma_quantifier_generalizer::find_guards(
    expr_ref_vector const &indices,
    expr_ref &lower, expr_ref &upper)
{
    if (indices.empty()) return;

    auto minmax = std::minmax_element((app * *) indices.c_ptr(),
                                      (app * *) indices.c_ptr() + indices.size(),
                                      index_lt_proc(m));
    lower = *minmax.first;
    upper = *minmax.second;
}

void lemma_quantifier_generalizer::add_lower_bounds(
    var_ref_vector const &subs,
    app_ref_vector const &zks,
    vector<expr_ref_vector> const &idx_instances,
    expr_ref_vector &cube)
{
    for (unsigned v = 0; v < subs.size(); v++) {
        var *var = subs.get(v);
        if (idx_instances[v].empty()) continue;
        TRACE("spacer_qgen",
              tout << "Finding lower bounds for " << mk_pp(var, m) << "\n";);
        expr_ref low(m);
        expr_ref up(m);
        find_guards(idx_instances[v], low, up);
        cube.push_back(m_arith.mk_ge(zks.get(var->get_idx()), low));
    }
}

/// returns true if expression e contains a sub-expression of the form (select A idx) where
/// idx contains exactly one skolem from zks. Returns idx and the skolem
bool lemma_quantifier_generalizer::match_sk_idx(expr *e, app_ref_vector const &zks, expr *&idx, app *&sk) {
    if (zks.size() != 1) return false;
    contains_app has_zk(m, zks.get(0));

    if (!contains_selects(e, m)) return false;
    app_ref_vector indicies(m);
    get_select_indices(e, indicies, m);
    if (indicies.size() > 2) return false;

    unsigned i=0;
    if (indicies.size() == 1) {
        if (!has_zk(indicies.get(0))) return false;
    }
    else {
        if (has_zk(indicies.get(0)) && !has_zk(indicies.get(1)))
            i = 0;
        else if (!has_zk(indicies.get(0)) && has_zk(indicies.get(1)))
            i = 1;
        else if (!has_zk(indicies.get(0)) && !has_zk(indicies.get(1)))
            return false;
    }

    idx = indicies.get(i);
    sk = zks.get(0);
    return true;
}

expr* times_minus_one(expr *e, arith_util &arith) {
    expr *r;
    if (arith.is_times_minus_one (e, r)) { return r; }

    return arith.mk_mul(arith.mk_numeral(rational(-1), arith.is_int(get_sort(e))), e);
}

/** Attempts to rewrite a cube so that quantified variable appears as
    a top level argument of select-term

    Find sub-expression of the form (select A (+ sk!0 t)) and replaces
    (+ sk!0 t) --> sk!0 and sk!0 --> (+ sk!0 (* (- 1) t))

    Current implementation is an ugly hack for one special case
*/
void lemma_quantifier_generalizer::cleanup(expr_ref_vector &cube, app_ref_vector const &zks, expr_ref &bind) {
    if (zks.size() != 1) return;

    arith_util arith(m);
    expr *idx = nullptr;
    app *sk = nullptr;
    expr_ref rep(m);

    for (expr *e : cube) {
        if (match_sk_idx(e, zks, idx, sk)) {
            CTRACE("spacer_qgen", idx != sk,
                   tout << "Possible cleanup of " << mk_pp(idx, m) << " in "
                   << mk_pp(e, m) << " on " << mk_pp(sk, m) << "\n";);

            if (!arith.is_add(idx)) continue;
            app *a = to_app(idx);
            bool found = false;
            expr_ref_vector kids(m);
            expr_ref_vector kids_bind(m);
            for (unsigned i = 0, sz = a->get_num_args(); i < sz; ++i) {
                if (a->get_arg(i) == sk) {
                    found = true;
                    kids.push_back(a->get_arg(i));
                    kids_bind.push_back(bind);
                }
                else {
                    kids.push_back (times_minus_one(a->get_arg(i), arith));
                    kids_bind.push_back (times_minus_one(a->get_arg(i), arith));
                }
            }
            if (!found) continue;

            rep = arith.mk_add(kids.size(), kids.c_ptr());
            bind = arith.mk_add(kids_bind.size(), kids_bind.c_ptr());
            TRACE("spacer_qgen",
                  tout << "replace " << mk_pp(idx, m) << " with " << mk_pp(rep, m) << "\n";);
            break;
        }
    }

    if (rep) {
        expr_safe_replace rw(m);
        rw.insert(sk, rep);
        rw.insert(idx, sk);
        rw(cube);
        TRACE("spacer_qgen",
              tout << "Cleaned cube to: " << mk_and(cube) << "\n";);
    }
}

void lemma_quantifier_generalizer::generalize_pattern_lits(expr_ref_vector &pats) {
    // generalize pattern literals using 'x=t' --> 'x>=t'
    for (unsigned i = 0, sz = pats.size(); i < sz; ++i) {
        expr *e1, *e2;
        expr *p = pats.get(i);
        if (m.is_eq(p, e1, e2) && (is_var(e1) || is_var(e2))) {
            if (m_arith.is_numeral(e1)) {
                p = m_arith.mk_ge(e2, e1);
            }
            else if (m_arith.is_numeral(e2)) {
                p = m_arith.mk_ge(e1, e2);
            }
        }
        if (p != pats.get(i)) {
            pats.set(i, p);
        }
    }
}
void lemma_quantifier_generalizer::operator()(lemma_ref &lemma) {
    if (lemma->get_cube().empty()) return;
    if (!lemma->has_pob()) return;

    m_st.count++;
    scoped_watch _w_(m_st.watch);

    expr_ref_vector cube(m);
    cube.append(lemma->get_cube());

    TRACE("spacer_qgen",
          tout << "initial cube: " << mk_and(lemma->get_cube()) << "\n";);
    if (true) {
        // -- re-normalize the cube
        expr_ref c(m);
        c = mk_and(cube);
        normalize(c, c, true, true);
        cube.reset();
        flatten_and(c, cube);
        TRACE("spacer_qgen",
              tout << "normalized cube:\n" << mk_and(cube) << "\n";);
    }

    app_ref_vector skolems(m);
    lemma->get_pob()->get_skolems(skolems);
    int offset = skolems.size();

    // for every literal
    for (unsigned i=0; i < cube.size(); i++) {
        expr *r = cube.get(i);

        // generate candidates
        app_ref_vector candidates(m);
        find_candidates(r, candidates);
        if (candidates.empty()) continue;


        // for every candidate
        for (unsigned arg=0, sz = candidates.size(); arg < sz; arg++) {
            app_ref_vector cand(m);
            cand.push_back(to_app(candidates.get(arg)));
            var_ref_vector subs(m);
            expr_ref_vector patterns(m);
            // generate patterns for a candidate
            generate_patterns(cube, cand, subs, patterns, offset);

            // Currently, only support one variable per pattern
            SASSERT(subs.size() == cand.size());
            SASSERT(cand.size() == 1);

            // Find matching expressions
            vector<bool> dirty;
            dirty.resize(cube.size(), false);
            vector<expr_ref_vector> idx_instances;
            find_matching_expressions(cube, subs, patterns, idx_instances, dirty);

            expr_ref_vector new_cube(m);

            // move all unmatched expressions to the new cube
            for (unsigned c=0; c < cube.size(); c++) {
                if (dirty[c] == false) {
                    new_cube.push_back(cube.get(c));
                }
            }

            // everything moved, nothing left
            if (new_cube.size() == cube.size()) continue;

            // -- generalize equality in patterns
            generalize_pattern_lits(patterns);

            // ground quantified patterns in skolems
            expr_ref gnd(m);
            app_ref_vector zks(m);
            ground_expr(mk_and(patterns), gnd, zks);
            flatten_and(gnd, new_cube);

            // compute lower bounds for quantified variables
            add_lower_bounds(subs, zks, idx_instances, new_cube);

            TRACE("spacer_qgen",
                  tout << "New CUBE is: " << mk_pp(mk_and(new_cube),m) << "\n";);

            // check if the result is a lemma
            unsigned uses_level = 0;
            unsigned weakness = lemma->weakness();
            pred_transformer &pt = lemma->get_pob()->pt();
            if (pt.check_inductive(lemma->level(), new_cube, uses_level, weakness)) {
                TRACE("spacer_qgen",
                      tout << "Quantifier Generalization Succeeded!\n"
                      << "New CUBE is: " << mk_pp(mk_and(new_cube),m) << "\n";);
                SASSERT(zks.size() >= offset);
                SASSERT(cand.size() == 1);

                // lift quantified variables to top of select
                expr_ref bind(m);
                bind = cand.get(0);
                cleanup(new_cube, zks, bind);

                // XXX better do that check before changing bind in cleanup()
                // XXX Or not because substitution might introduce _n variable into bind
                if (m_ctx.get_manager().is_n_formula(bind))
                    // XXX this creates an instance, but not necessarily the needed one

                    // XXX This is sound because any instance of
                    // XXX universal quantifier is sound

                    // XXX needs better long term solution. leave
                    // comment here for the future
                    m_ctx.get_manager().formula_n2o(bind, bind, 0);

                lemma->update_cube(lemma->get_pob(), new_cube);
                lemma->set_level(uses_level);

                SASSERT(offset + 1 == zks.size());
                // XXX Assumes that offset + 1 == zks.size();
                for (unsigned sk=offset; sk < zks.size(); sk++)
                    lemma->add_skolem(zks.get(sk), to_app(bind));
                return;
            }
            else {
                ++m_st.num_failures;
            }
        }
    }
}



}
