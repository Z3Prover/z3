/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_farkas_learner.cpp

Abstract:

    Provides abstract interface and some implementations of algorithms
    for strenghtening lemmas

Author:

    Krystof Hoder (t-khoder) 2011-11-1.

Revision History:
// TODO: what to write here
--*/

//TODO: reorder, delete unnecessary includes
#include "ast/ast_smt2_pp.h"
#include "ast/array_decl_plugin.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/dl_decl_plugin.h"
#include "ast/for_each_expr.h"
#include "muz/base/dl_util.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "muz/spacer/spacer_util.h"
#include "muz/spacer/spacer_farkas_learner.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/ast_ll_pp.h"
#include "ast/proofs/proof_utils.h"
#include "ast/reg_decl_plugins.h"
#include "smt/smt_farkas_util.h"

namespace spacer {

class collect_pure_proc {
    func_decl_set& m_symbs;
public:
    collect_pure_proc(func_decl_set& s): m_symbs(s) {}

    void operator()(app* a)
    {
        if (a->get_family_id() == null_family_id) {
            m_symbs.insert(a->get_decl());
        }
    }
    void operator()(var*) {}
    void operator()(quantifier*) {}
};

void farkas_learner::combine_constraints(unsigned n, app * const * lits, rational const * coeffs, expr_ref& res)
{
    ast_manager& m = res.get_manager();
    smt::farkas_util res_c(m);
    res_c.set_split_literals(m_split_literals);
    for (unsigned i = 0; i < n; ++i) {
        res_c.add(coeffs[i], lits[i]);
    }
    res = res_c.get();
}

// every uninterpreted symbol is in symbs
class is_pure_expr_proc {
    func_decl_set const& m_symbs;
    array_util           m_au;
public:
    struct non_pure {};

    is_pure_expr_proc(func_decl_set const& s, ast_manager& m):
        m_symbs(s),
        m_au(m)
    {}

    void operator()(app* a)
    {
        if (a->get_family_id() == null_family_id) {
            if (!m_symbs.contains(a->get_decl())) {
                throw non_pure();
            }
        } else if (a->get_family_id() == m_au.get_family_id() &&
                   a->is_app_of(a->get_family_id(), OP_ARRAY_EXT)) {
            throw non_pure();
        }
    }
    void operator()(var*) {}
    void operator()(quantifier*) {}
};

bool farkas_learner::is_pure_expr(func_decl_set const& symbs, expr* e, ast_manager& m) const
{
    is_pure_expr_proc proc(symbs, m);
    try {
        for_each_expr(proc, e);
    } catch (const is_pure_expr_proc::non_pure &) {
        return false;
    }
    return true;
};


/**
   Revised version of Farkas strengthener.
   1. Mark B-pure nodes as derivations that depend only on B.
   2. Collect B-influenced nodes
   3. (optional) Permute B-pure units over resolution steps to narrow dependencies on B.
   4. Weaken B-pure units for resolution with Farkas Clauses.
   5. Add B-pure units elsewhere.

   Rules:
   - hypothesis h |- h

                H |- false
   - lemma      ----------
                 |- not H

                Th |- L \/ C   H |- not L
   - th-lemma   -------------------------
                       H  |- C

     Note: C is false for theory axioms, C is unit literal for propagation.

   - rewrite        |- t = s

                    H |- t = s
   - monotonicity   ----------------
                   H |- f(t) = f(s)

                    H |- t = s H' |- s = u
   - trans          ----------------------
                        H, H' |- t = u

                    H |- C \/ L  H' |- not L
   - unit_resolve   ------------------------
                            H, H' |- C

                    H |- a ~ b   H' |- a
   - mp             --------------------
                         H, H' |- b

   - def-axiom       |- C

   - asserted        |- f

   Mark nodes by:
      - Hypotheses
      - Dependency on bs
      - Dependency on A

   A node is unit derivable from bs if:
      - It has no hypotheses.
      - It depends on bs.
      - It does not depend on A.

   NB: currently unit derivable is not symmetric: A clause can be
   unit derivable, but a unit literal with hypotheses is not.
   This is clearly wrong, because hypotheses are just additional literals
   in a clausal version.

   NB: the routine is not interpolating, though an interpolating variant would
   be preferable because then we can also use it for model propagation.

   We collect the unit derivable nodes from bs.
   These are the weakenings of bs, besides the
   units under Farkas.

*/

#define INSERT(_x_) if (!lemma_set.contains(_x_)) { lemma_set.insert(_x_); lemmas.push_back(_x_); }

void farkas_learner::get_lemmas(proof* root, expr_set const& bs, expr_ref_vector& lemmas)
{
    ast_manager& m = lemmas.get_manager();
    bool_rewriter brwr(m);
    func_decl_set Bsymbs;
    collect_pure_proc collect_proc(Bsymbs);
    expr_set::iterator it = bs.begin(), end = bs.end();
    for (; it != end; ++it) {
        for_each_expr(collect_proc, *it);
    }

    proof_ref pr(root, m);
    proof_utils::reduce_hypotheses(pr);
    proof_utils::permute_unit_resolution(pr);
    IF_VERBOSE(3, verbose_stream() << "Reduced proof:\n" << mk_ismt2_pp(pr, m) << "\n";);

    ptr_vector<expr_set> hyprefs;
    obj_map<expr, expr_set*> hypmap;
    obj_hashtable<expr> lemma_set;
    ast_mark b_depend, a_depend, visited, b_closed;
    expr_set* empty_set = alloc(expr_set);
    hyprefs.push_back(empty_set);
    ptr_vector<proof> todo;
    TRACE("spacer_verbose", tout << mk_pp(pr, m) << "\n";);
    todo.push_back(pr);
    while (!todo.empty()) {
        proof* p = todo.back();
        SASSERT(m.is_proof(p));
        if (visited.is_marked(p)) {
            todo.pop_back();
            continue;
        }
        bool all_visit = true;
        for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
            expr* arg = p->get_arg(i);
            SASSERT(m.is_proof(arg));
            if (!visited.is_marked(arg)) {
                all_visit = false;
                todo.push_back(to_app(arg));
            }
        }
        if (!all_visit) {
            continue;
        }
        visited.mark(p, true);
        todo.pop_back();

        // retrieve hypotheses and dependencies on A, bs.
        bool b_dep = false, a_dep = false;
        expr_set* hyps = empty_set;
        for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
            expr* arg = p->get_arg(i);
            a_dep = a_dep || a_depend.is_marked(arg);
            b_dep = b_dep || b_depend.is_marked(arg);
            expr_set* hyps2 = hypmap.find(arg);
            if (hyps != hyps2 && !hyps2->empty()) {
                if (hyps->empty()) {
                    hyps = hyps2;
                } else {
                    expr_set* hyps3 = alloc(expr_set);
                    set_union(*hyps3, *hyps);
                    set_union(*hyps3, *hyps2);
                    hyps = hyps3;
                    hyprefs.push_back(hyps);
                }
            }
        }
        hypmap.insert(p, hyps);
        a_depend.mark(p, a_dep);
        b_depend.mark(p, b_dep);

#define IS_B_PURE(_p) (b_depend.is_marked(_p) && !a_depend.is_marked(_p) && hypmap.find(_p)->empty())


        // Add lemmas that depend on bs, have no hypotheses, don't depend on A.
        if ((!hyps->empty() || a_depend.is_marked(p)) &&
                b_depend.is_marked(p) && !is_farkas_lemma(m, p)) {
            for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
                app* arg = to_app(p->get_arg(i));
                if (IS_B_PURE(arg)) {
                    expr* fact = m.get_fact(arg);
                    if (is_pure_expr(Bsymbs, fact, m)) {
                        TRACE("farkas_learner2",
                              tout << "Add: " << mk_pp(m.get_fact(arg), m) << "\n";
                              tout << mk_pp(arg, m) << "\n";
                             );
                        INSERT(fact);
                    } else {
                        get_asserted(p, bs, b_closed, lemma_set, lemmas);
                        b_closed.mark(p, true);
                    }
                }
            }
        }

        switch (p->get_decl_kind()) {
        case PR_ASSERTED:
            if (bs.contains(m.get_fact(p))) {
                b_depend.mark(p, true);
            } else {
                a_depend.mark(p, true);
            }
            break;
        case PR_HYPOTHESIS: {
            SASSERT(hyps == empty_set);
            hyps = alloc(expr_set);
            hyps->insert(m.get_fact(p));
            hyprefs.push_back(hyps);
            hypmap.insert(p, hyps);
            break;
        }
        case PR_DEF_AXIOM: {
            if (!is_pure_expr(Bsymbs, m.get_fact(p), m)) {
                a_depend.mark(p, true);
            }
            break;
        }
        case PR_LEMMA: {
            expr_set* hyps2 = alloc(expr_set);
            hyprefs.push_back(hyps2);
            set_union(*hyps2, *hyps);
            hyps = hyps2;
            expr* fml = m.get_fact(p);
            hyps->remove(fml);
            if (m.is_or(fml)) {
                for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
                    expr* f = to_app(fml)->get_arg(i);
                    expr_ref hyp(m);
                    brwr.mk_not(f, hyp);
                    hyps->remove(hyp);
                }
            }
            hypmap.insert(p, hyps);
            break;
        }
        case PR_TH_LEMMA: {
            if (!is_farkas_lemma(m, p)) { break; }

            SASSERT(m.has_fact(p));
            unsigned prem_cnt = m.get_num_parents(p);
            func_decl * d = p->get_decl();
            SASSERT(d->get_num_parameters() >= prem_cnt + 2);
            SASSERT(d->get_parameter(0).get_symbol() == "arith");
            SASSERT(d->get_parameter(1).get_symbol() == "farkas");
            parameter const* params = d->get_parameters() + 2;

            app_ref_vector lits(m);
            expr_ref tmp(m);
            unsigned num_b_pures = 0;
            rational coef;
            vector<rational> coeffs;

            TRACE("farkas_learner2",
            for (unsigned i = 0; i < prem_cnt; ++i) {
            VERIFY(params[i].is_rational(coef));
                proof* prem = to_app(p->get_arg(i));
                bool b_pure = IS_B_PURE(prem);
                tout << (b_pure ? "B" : "A") << " " << coef << " " << mk_pp(m.get_fact(prem), m) << "\n";
            }
            tout << mk_pp(m.get_fact(p), m) << "\n";
                 );

            // NB. Taking 'abs' of coefficients is a workaround.
            // The Farkas coefficient extraction in arith_core must be wrong.
            // The coefficients would be always positive relative to the theory lemma.

            for (unsigned i = 0; i < prem_cnt; ++i) {
                expr * prem_e = p->get_arg(i);
                SASSERT(is_app(prem_e));
                proof * prem = to_app(prem_e);

                if (IS_B_PURE(prem)) {
                    ++num_b_pures;
                } else {
                    VERIFY(params[i].is_rational(coef));
                    lits.push_back(to_app(m.get_fact(prem)));
                    coeffs.push_back(abs(coef));
                }
            }
            params += prem_cnt;
            if (prem_cnt + 2 < d->get_num_parameters()) {
                unsigned num_args = 1;
                expr* fact = m.get_fact(p);
                expr* const* args = &fact;
                if (m.is_or(fact)) {
                    app* _or = to_app(fact);
                    num_args = _or->get_num_args();
                    args = _or->get_args();
                }
                SASSERT(prem_cnt + 2 + num_args == d->get_num_parameters());
                for (unsigned i = 0; i < num_args; ++i) {
                    expr* prem_e = args[i];
                    brwr.mk_not(prem_e, tmp);
                    VERIFY(params[i].is_rational(coef));
                    SASSERT(is_app(tmp));
                    lits.push_back(to_app(tmp));
                    coeffs.push_back(abs(coef));
                }

            }
            SASSERT(coeffs.size() == lits.size());
            if (num_b_pures > 0) {
                expr_ref res(m);
                combine_constraints(coeffs.size(), lits.data(), coeffs.data(), res);
                TRACE("farkas_learner2", tout << "Add: " << mk_pp(res, m) << "\n";);
                INSERT(res);
                b_closed.mark(p, true);
            }
        }
        default:
            break;
        }
    }

    std::for_each(hyprefs.begin(), hyprefs.end(), delete_proc<expr_set>());
    simplify_bounds(lemmas);
}

void farkas_learner::get_asserted(proof* p0, expr_set const& bs, ast_mark& b_closed, obj_hashtable<expr>& lemma_set, expr_ref_vector& lemmas)
{
    ast_manager& m = lemmas.get_manager();
    ast_mark visited;
    proof* p = p0;
    ptr_vector<proof> todo;
    todo.push_back(p);

    while (!todo.empty()) {
        p = todo.back();
        todo.pop_back();
        if (visited.is_marked(p) || b_closed.is_marked(p)) {
            continue;
        }
        visited.mark(p, true);
        for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
            expr* arg = p->get_arg(i);
            SASSERT(m.is_proof(arg));
            todo.push_back(to_app(arg));
        }
        if (p->get_decl_kind() == PR_ASSERTED &&
                bs.contains(m.get_fact(p))) {
            expr* fact = m.get_fact(p);
            TRACE("farkas_learner2",
                  tout << mk_ll_pp(p0, m) << "\n";
                  tout << "Add: " << mk_pp(p, m) << "\n";);
            INSERT(fact);
            b_closed.mark(p, true);
        }
    }
}


bool farkas_learner::is_farkas_lemma(ast_manager& m, expr* e)
{
    app * a;
    func_decl* d;
    symbol sym;
    return
        is_app(e) &&
        (a = to_app(e), d = a->get_decl(), true) &&
        PR_TH_LEMMA == a->get_decl_kind() &&
        d->get_num_parameters() >= 2 &&
        d->get_parameter(0).is_symbol(sym) && sym == "arith" &&
        d->get_parameter(1).is_symbol(sym) && sym == "farkas" &&
        d->get_num_parameters() >= m.get_num_parents(to_app(e)) + 2;
}
}
