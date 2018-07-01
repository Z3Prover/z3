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
#include "ast/rewriter/factor_equivs.h"
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


    struct has_nlira_functor {
        struct found{};

        ast_manager &m;
        arith_util   u;

        has_nlira_functor(ast_manager &_m) : m(_m), u(m) {}

        void operator()(var *) {}
        void operator()(quantifier *) {}
        void operator()(app *n) {
            family_id fid = n->get_family_id();
            if (fid != u.get_family_id()) return;

            switch(n->get_decl_kind()) {
            case OP_MUL:
                if (n->get_num_args() != 2)
                    throw found();
                if (!u.is_numeral(n->get_arg(0)) && !u.is_numeral(n->get_arg(1)))
                    throw found();
                return;
            case OP_IDIV: case OP_DIV: case OP_REM: case OP_MOD:
                if (!u.is_numeral(n->get_arg(1)))
                    throw found();
                return;
            default:
                return;
            }
            return;
        }
    };

    bool has_nlira(expr_ref_vector &v) {
        has_nlira_functor fn(v.m());
        expr_fast_mark1 visited;
        try {
            for (expr *e : v)
                quick_for_each_expr(fn, visited, e);
        }
        catch (has_nlira_functor::found ) {
            return true;
        }
        return false;
    }
}

namespace spacer {

lemma_quantifier_generalizer::lemma_quantifier_generalizer(context &ctx,
                                                           bool normalize_cube) :
    lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m), m_cube(m),
    m_normalize_cube(normalize_cube), m_offset(0) {}

void lemma_quantifier_generalizer::collect_statistics(statistics &st) const
{
    st.update("time.spacer.solve.reach.gen.quant", m_st.watch.get_seconds());
    st.update("quantifier gen", m_st.count);
    st.update("quantifier gen failures", m_st.num_failures);
}

/**
   Finds candidates terms to be existentially abstracted.
   A term t is a candidate if
    (a) t is ground

    (b) t appears in an expression of the form (select A t) for some array A

    (c) t appears in an expression of the form (select A (+ t v))
        where v is ground

   The goal is to pick candidates that might result in a lemma in the
   essentially uninterpreted fragment of FOL or its extensions.
 */
void lemma_quantifier_generalizer::find_candidates(expr *e,
                                                   app_ref_vector &candidates) {
    if (!contains_selects(e, m)) return;

    app_ref_vector indices(m);
    get_select_indices(e, indices);

    app_ref_vector extra(m);
    expr_sparse_mark marked_args;

    // Make sure not to try and quantify already-quantified indices
    for (unsigned idx=0, sz = indices.size(); idx < sz; idx++) {
        // skip expressions that already contain a quantified variable
        if (has_zk_const(indices.get(idx))) {
            continue;
        }

        app *index = indices.get(idx);
        TRACE ("spacer_qgen", tout << "Candidate: "<< mk_pp(index, m)
               << " in " << mk_pp(e, m) << "\n";);
        extra.push_back(index);
        if (m_arith.is_add(index)) {
            for (expr * arg : *index) {
                if (!is_app(arg) || marked_args.is_marked(arg)) {continue;}
                marked_args.mark(arg);
                candidates.push_back (to_app(arg));
            }
        }
    }

    std::sort(candidates.c_ptr(), candidates.c_ptr() + candidates.size(),
              index_lt_proc(m));
    // keep actual select indecies in the order found at the back of
    // candidate list. There is no particular reason for this order
    candidates.append(extra);
}


/// returns true if expression e contains a sub-expression of the form (select A idx) where
/// idx contains exactly one skolem from zks. Returns idx and the skolem
bool lemma_quantifier_generalizer::match_sk_idx(expr *e, app_ref_vector const &zks, expr *&idx, app *&sk) {
    if (zks.size() != 1) return false;
    contains_app has_zk(m, zks.get(0));

    if (!contains_selects(e, m)) return false;
    app_ref_vector indicies(m);
    get_select_indices(e, indicies);
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

namespace {
expr* times_minus_one(expr *e, arith_util &arith) {
    expr *r;
    if (arith.is_times_minus_one (e, r)) { return r; }

    return arith.mk_mul(arith.mk_numeral(rational(-1), arith.is_int(get_sort(e))), e);
}
}

/** Attempts to rewrite a cube so that quantified variable appears as
    a top level argument of select-term

    Find sub-expression of the form (select A (+ sk!0 t)) and replaces
    (+ sk!0 t) --> sk!0 and sk!0 --> (+ sk!0 (* (- 1) t))


    rewrites bind to  (+ bsk!0 t) where bsk!0 is the original binding for sk!0

    Current implementation is an ugly hack for one special
    case. Should be rewritten based on an equality solver from qe
*/
void lemma_quantifier_generalizer::cleanup(expr_ref_vector &cube,
                                           app_ref_vector const &zks,
                                           expr_ref &bind) {
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
            for (expr* arg : *a) {
                if (arg == sk) {
                    found = true;
                    kids.push_back(arg);
                    kids_bind.push_back(bind);
                }
                else {
                    kids.push_back(times_minus_one(arg, arith));
                    kids_bind.push_back(arg);
                }
            }
            if (!found) continue;

            rep = arith.mk_add(kids.size(), kids.c_ptr());
            bind = arith.mk_add(kids_bind.size(), kids_bind.c_ptr());
            TRACE("spacer_qgen",
                  tout << "replace " << mk_pp(idx, m) << " with " << mk_pp(rep, m) << "\n"
                  << "bind is: " << bind << "\n";);
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

/**
   Create an abstract cube by abstracting a given term with a given variable.
   On return,
   gnd_cube contains all ground literals from m_cube
   abs_cube contains all newly quantified literals from m_cube
   lb contains an expression determining the lower bound on the variable
   ub contains an expression determining the upper bound on the variable

   Conjunction of gnd_cube and abs_cube is the new quantified cube

   lb and ub are null if no bound was found
 */
void lemma_quantifier_generalizer::mk_abs_cube(lemma_ref &lemma, app *term,
                                               var *var,
                                               expr_ref_vector &gnd_cube,
                                               expr_ref_vector &abs_cube,
                                               expr *&lb, expr *&ub,
                                               unsigned &stride) {

    // create an abstraction function that maps candidate term to variables
    expr_safe_replace sub(m);
    // term -> var
    sub.insert(term, var);
    rational val;
    if (m_arith.is_numeral(term, val)) {
        bool is_int = val.is_int();
        expr_ref minus_one(m);
        minus_one = m_arith.mk_numeral(rational(-1), is_int);

        // term+1 -> var+1  if term is a number
        sub.insert(
            m_arith.mk_numeral(val + 1, is_int),
            m_arith.mk_add(var, m_arith.mk_numeral(rational(1), is_int)));
        // -term-1 -> -1*var + -1  if term is a number
        sub.insert(
            m_arith.mk_numeral(-1*val + -1, is_int),
            m_arith.mk_add (m_arith.mk_mul (minus_one, var), minus_one));
    }

    lb = nullptr;
    ub = nullptr;

    for (expr *lit : m_cube) {
        expr_ref abs_lit(m);
        sub(lit, abs_lit);
        if (lit == abs_lit) {gnd_cube.push_back(lit);}
        else {
            expr *e1, *e2;
            // generalize v=num into v>=num
            if (m.is_eq(abs_lit, e1, e2) && (e1 == var || e2 == var)) {
                if (m_arith.is_numeral(e1)) {
                    abs_lit = m_arith.mk_ge(var, e1);
                } else if (m_arith.is_numeral(e2)) {
                    abs_lit = m_arith.mk_ge(var, e2);
                }
            }
            abs_cube.push_back(abs_lit);
            if (contains_selects(abs_lit, m)) {
                expr_ref_vector pob_cube(m);
                flatten_and(lemma->get_pob()->post(), pob_cube);
                find_stride(pob_cube, abs_lit, stride);
            }

            if (!lb && is_lb(var, abs_lit)) {
                lb = abs_lit;
            }
            else if (!ub && is_ub(var, abs_lit)) {
                ub = abs_lit;
            }
        }
    }
}

// -- returns true if e is an upper bound for var
bool lemma_quantifier_generalizer::is_ub(var *var, expr *e) {
    expr *e1, *e2;
    // var <= e2
    if ((m_arith.is_le (e, e1, e2) || m_arith.is_lt(e, e1, e2)) && var == e1) {
        return true;
    }
    // e1 >= var
    if ((m_arith.is_ge(e, e1, e2) || m_arith.is_gt(e, e1, e2)) && var == e2) {
        return true;
    }

    // t <= -1*var
    if ((m_arith.is_le (e, e1, e2) || m_arith.is_lt(e, e1, e2))
        && m_arith.is_times_minus_one(e2, e2) && e2 == var) {
        return true;
    }
    // -1*var >= t
    if ((m_arith.is_ge(e, e1, e2) || m_arith.is_gt(e, e1, e2)) &&
        m_arith.is_times_minus_one(e1, e1) && e1 == var) {
        return true;
    }
    // ! (var >= e2)
    if (m.is_not (e, e1) && is_lb(var, e1)) {
        return true;
    }
    // var + t1 <= t2
    if ((m_arith.is_le(e, e1, e2) || m_arith.is_lt(e, e1, e2)) &&
        m_arith.is_add(e1)) {
        app *a = to_app(e1);
        for (expr* arg : *a) {
            if (arg == var) return true;
        }
    }
    // t1 <= t2 + -1*var
    if ((m_arith.is_le(e, e1, e2) || m_arith.is_lt(e, e1, e2)) &&
        m_arith.is_add(e2)) {
        app *a = to_app(e2);
        for (expr* arg : *a) {
            if (m_arith.is_times_minus_one(arg, arg) && arg == var)
                return true;
        }
    }
    // t1 >= t2 + var
    if ((m_arith.is_ge(e, e1, e2) || m_arith.is_gt(e, e1, e2)) &&
        m_arith.is_add(e2)) {
        app *a = to_app(e2);
        for (expr * arg : *a) {
            if (arg == var) return true;
        }
    }
    // -1*var + t1 >= t2
    if ((m_arith.is_ge(e, e1, e2) || m_arith.is_gt(e, e1, e2)) &&
        m_arith.is_add(e1)) {
        app *a = to_app(e1);
        for (expr * arg : *a) {
            if (m_arith.is_times_minus_one(arg, arg) && arg == var)
                return true;
        }
    }
    return false;
}

// -- returns true if e is a lower bound for var
bool lemma_quantifier_generalizer::is_lb(var *var, expr *e) {
    expr *e1, *e2;
    // var >= e2
    if ((m_arith.is_ge (e, e1, e2) || m_arith.is_gt(e, e1, e2)) && var == e1) {
        return true;
    }
    // e1 <= var
    if ((m_arith.is_le(e, e1, e2) || m_arith.is_lt(e, e1, e2)) && var == e2) {
        return true;
    }
    // t >= -1*var
    if ((m_arith.is_ge (e, e1, e2) || m_arith.is_gt(e, e1, e2))
        && m_arith.is_times_minus_one(e2, e2) && e2 == var) {
        return true;
    }
    // -1*var <= t
    if ((m_arith.is_le(e, e1, e2) || m_arith.is_lt(e, e1, e2)) &&
        m_arith.is_times_minus_one(e1, e1) && e1 == var) {
        return true;
    }
    // ! (var <= e2)
    if (m.is_not (e, e1) && is_ub(var, e1)) {
        return true;
    }
    // var + t1 >= t2
    if ((m_arith.is_ge(e, e1, e2) || m_arith.is_gt(e, e1, e2)) &&
        m_arith.is_add(e1)) {
        app *a = to_app(e1);
        for (expr * arg : *a) {
            if (arg == var) return true;
        }
    }
    // t1 >= t2 + -1*var
    if ((m_arith.is_ge(e, e1, e2) || m_arith.is_gt(e, e1, e2)) &&
        m_arith.is_add(e2)) {
        app *a = to_app(e2);
        for (expr * arg : *a) {
            if (m_arith.is_times_minus_one(arg, arg) && arg == var)
                return true;
        }
    }
    // t1 <= t2 + var
    if ((m_arith.is_le(e, e1, e2) || m_arith.is_lt(e, e1, e2)) &&
        m_arith.is_add(e2)) {
        app *a = to_app(e2);
        for (expr * arg : *a) {
            if (arg == var) return true;
        }
    }
    // -1*var + t1 <= t2
    if ((m_arith.is_le(e, e1, e2) || m_arith.is_lt(e, e1, e2)) &&
        m_arith.is_add(e1)) {
        app *a = to_app(e1);
        for (expr * arg : *a) {
            if (m_arith.is_times_minus_one(arg, arg) && arg == var)
                return true;
        }
    }

    return false;
}

bool lemma_quantifier_generalizer::generalize (lemma_ref &lemma, app *term) {

    expr *lb = nullptr, *ub = nullptr;
    unsigned stride = 1;
    expr_ref_vector gnd_cube(m);
    expr_ref_vector abs_cube(m);

    var_ref var(m);
    var = m.mk_var (m_offset, get_sort(term));

    mk_abs_cube(lemma, term, var, gnd_cube, abs_cube, lb, ub, stride);
    if (abs_cube.empty()) {return false;}
    if (has_nlira(abs_cube)) {
        TRACE("spacer_qgen",
              tout << "non-linear expression: " << abs_cube << "\n";);
        return false;
    }

    TRACE("spacer_qgen",
          tout << "abs_cube is: " << mk_and(abs_cube) << "\n";
          tout << "term: " << mk_pp(term, m) << "\n";
          tout << "lb = ";
          if (lb) tout << mk_pp(lb, m); else tout << "none";
          tout << "\n";
          tout << "ub = ";
          if (ub) tout << mk_pp(ub, m); else tout << "none";
          tout << "\n";);

    if (!lb && !ub)
        return false;

    // -- guess lower or upper bound if missing
    if (!lb) {
        abs_cube.push_back (m_arith.mk_ge (var, term));
        lb = abs_cube.back();
    }
    if (!ub) {
        abs_cube.push_back (m_arith.mk_le(var, term));
        ub = abs_cube.back();
    }

    rational init;
    expr_ref constant(m);
    if (is_var(to_app(lb)->get_arg(0)))
        constant = to_app(lb)->get_arg(1);
    else
        constant = to_app(lb)->get_arg(0);

    if (stride > 1 && m_arith.is_numeral(constant, init)) {
        unsigned mod = init.get_unsigned() % stride;
        TRACE("spacer_qgen",
              tout << "mod=" << mod << " init=" << init << " stride=" << stride << "\n";
              tout.flush(););
        abs_cube.push_back
            (m.mk_eq(m_arith.mk_mod(var,
                                    m_arith.mk_numeral(rational(stride), true)),
                     m_arith.mk_numeral(rational(mod), true)));}

    // skolemize
    expr_ref gnd(m);
    app_ref_vector zks(m);
    ground_expr(mk_and(abs_cube), gnd, zks);
    flatten_and(gnd, gnd_cube);

    TRACE("spacer_qgen",
          tout << "New CUBE is: " << gnd_cube << "\n";);

    // check if the result is a true lemma
    unsigned uses_level = 0;
    pred_transformer &pt = lemma->get_pob()->pt();
    if (pt.check_inductive(lemma->level(), gnd_cube, uses_level, lemma->weakness())) {
        TRACE("spacer_qgen",
              tout << "Quantifier Generalization Succeeded!\n"
              << "New CUBE is: " << gnd_cube << "\n";);
        SASSERT(zks.size() >= static_cast<unsigned>(m_offset));

        // lift quantified variables to top of select
        expr_ref ext_bind(m);
        ext_bind = term;
        cleanup(gnd_cube, zks, ext_bind);

        // XXX better do that check before changing bind in cleanup()
        // XXX Or not because substitution might introduce _n variable into bind
        if (m_ctx.get_manager().is_n_formula(ext_bind)) {
            // XXX this creates an instance, but not necessarily the needed one

            // XXX This is sound because any instance of
            // XXX universal quantifier is sound

            // XXX needs better long term solution. leave
            // comment here for the future
            m_ctx.get_manager().formula_n2o(ext_bind, ext_bind, 0);
        }

        lemma->update_cube(lemma->get_pob(), gnd_cube);
        lemma->set_level(uses_level);

        SASSERT(var->get_idx() < zks.size());
        SASSERT(is_app(ext_bind));
        lemma->add_skolem(zks.get(var->get_idx()), to_app(ext_bind));
        return true;
    }

    return false;
}

bool lemma_quantifier_generalizer::find_stride(expr_ref_vector &cube,
                                               expr_ref &pattern,
                                               unsigned &stride) {
    expr_ref tmp(m);
    tmp = mk_and(cube);
    normalize(tmp, tmp, false, true);
    cube.reset();
    flatten_and(tmp, cube);

    app_ref_vector indices(m);
    get_select_indices(pattern, indices);

    CTRACE("spacer_qgen", indices.empty(),
           tout << "Found no select indices in: " << pattern << "\n";);

    // TBD: handle multi-dimensional arrays and literals with multiple
    // select terms
    if (indices.size() != 1) return false;

    app *p_index = indices.get(0);

    unsigned_vector instances;
    for (expr* lit : cube) {

        if (!contains_selects(lit, m))
            continue;

        indices.reset();
        get_select_indices(lit, indices);

        // TBD: handle multi-dimensional arrays
        if (indices.size() != 1)
            continue;

        app *candidate = indices.get(0);

        unsigned size = p_index->get_num_args();
        unsigned matched = 0;
        for (unsigned p = 0; p < size; p++) {
            expr *arg = p_index->get_arg(p);
            if (is_var(arg)) {
                rational val;
                if (p < candidate->get_num_args() &&
                    m_arith.is_numeral(candidate->get_arg(p), val) &&
                    val.is_unsigned()) {
                    instances.push_back(val.get_unsigned());
                }
            }
            else {
                for (expr* cand : *candidate) {
                    if (cand == arg) {
                        matched++;
                        break;
                    }
                }
            }
        }

        if (matched < size - 1)
            continue;

        if (candidate->get_num_args() == matched)
            instances.push_back(0);

        TRACE("spacer_qgen",
              tout << "Match succeeded!\n";);
    }

    if (instances.size() <= 1)
        return false;

    std::sort(instances.begin(), instances.end());

    stride = instances[1]-instances[0];
    TRACE("spacer_qgen", tout << "Index Stride is: " << stride << "\n";);

    return true;
}

void lemma_quantifier_generalizer::operator()(lemma_ref &lemma) {
    if (lemma->get_cube().empty()) return;
    if (!lemma->has_pob()) return;

    m_st.count++;
    scoped_watch _w_(m_st.watch);

    TRACE("spacer_qgen",
          tout << "initial cube: " << mk_and(lemma->get_cube()) << "\n";);

    // setup the cube
    m_cube.reset();
    m_cube.append(lemma->get_cube());

    if (m_normalize_cube) {
        // -- re-normalize the cube
        expr_ref c(m);
        c = mk_and(m_cube);
        normalize(c, c, false, true);
        m_cube.reset();
        flatten_and(c, m_cube);
        TRACE("spacer_qgen",
              tout << "normalized cube:\n" << mk_and(m_cube) << "\n";);
    }

    // first unused free variable
    m_offset = lemma->get_pob()->get_free_vars_size();

    // for every literal, find a candidate term to abstract
    for (unsigned i=0; i < m_cube.size(); i++) {
        expr *r = m_cube.get(i);

        // generate candidates for abstraction
        app_ref_vector candidates(m);
        find_candidates(r, candidates);
        if (candidates.empty()) continue;

        // for every candidate
        for (unsigned arg=0, sz = candidates.size(); arg < sz; arg++) {
            if (generalize (lemma, candidates.get(arg))) {
                return;
            }
            else {
                ++m_st.num_failures;
            }
        }
    }
}



}
