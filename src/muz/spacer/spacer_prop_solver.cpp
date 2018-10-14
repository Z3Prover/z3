/**
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_prop_solver.cpp

Abstract:

    SAT solver abstraction for SPACER.

Author:

    Arie Gurfinkel
    Anvesh Komuravelli

Revision History:

--*/

#include "ast/ast_smt2_pp.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/bv_decl_plugin.h"

#include "ast/rewriter/expr_replacer.h"

#include "smt/params/smt_params.h"

#include "model/model.h"
#include "model/model_pp.h"

#include "muz/base/dl_util.h"

#include "muz/spacer/spacer_util.h"
#include "muz/spacer/spacer_farkas_learner.h"
#include "muz/spacer/spacer_prop_solver.h"

#include "model/model_evaluator.h"
#include "muz/base/fp_params.hpp"

namespace spacer {

prop_solver::prop_solver(ast_manager &m,
                         solver *solver0, solver *solver1,
                         fp_params const& p, symbol const& name) :
    m(m),
    m_name(name),
    m_ctx(nullptr),
    m_pos_level_atoms(m),
    m_neg_level_atoms(m),
    m_core(nullptr),
    m_subset_based_core(false),
    m_uses_level(infty_level()),
    m_delta_level(false),
    m_in_level(false),
    m_use_push_bg(p.spacer_keep_proxy())
{

    m_random.set_seed(p.spacer_random_seed());
    m_solvers[0] = solver0;
    m_solvers[1] = solver1;

    m_contexts[0] = alloc(spacer::iuc_solver, *(m_solvers[0]),
                          p.spacer_iuc(),
                          p.spacer_iuc_arith(),
                          p.spacer_iuc_print_farkas_stats(),
                          p.spacer_iuc_old_hyp_reducer(),
                          p.spacer_iuc_split_farkas_literals());
    m_contexts[1] = alloc(spacer::iuc_solver, *(m_solvers[1]),
                          p.spacer_iuc(),
                          p.spacer_iuc_arith(),
                          p.spacer_iuc_print_farkas_stats(),
                          p.spacer_iuc_old_hyp_reducer(),
                          p.spacer_iuc_split_farkas_literals());
}

void prop_solver::add_level()
{
    unsigned idx = level_cnt();
    std::stringstream name;
    name << m_name << "#level_" << idx;
    func_decl * lev_pred = m.mk_fresh_func_decl(name.str().c_str(), 0, nullptr, m.mk_bool_sort());
    m_level_preds.push_back(lev_pred);

    app_ref pos_la(m.mk_const(lev_pred), m);
    app_ref neg_la(m.mk_not(pos_la.get()), m);

    m_pos_level_atoms.push_back(pos_la);
    m_neg_level_atoms.push_back(neg_la);

    m_level_atoms_set.insert(pos_la.get());
    m_level_atoms_set.insert(neg_la.get());
}

void prop_solver::ensure_level(unsigned lvl)
{
    if (is_infty_level(lvl)) return;
    while (lvl >= level_cnt()) {
        add_level();
    }
}

unsigned prop_solver::level_cnt() const
{
    return m_level_preds.size();
}

void prop_solver::assert_level_atoms(unsigned level)
{
    unsigned lev_cnt = level_cnt();
    for (unsigned i = 0; i < lev_cnt; i++) {
        bool active = m_delta_level ? i == level : i >= level;
        app * lev_atom =
            active ? m_neg_level_atoms.get(i) : m_pos_level_atoms.get(i);
        m_ctx->push_bg(lev_atom);
    }
}

void prop_solver::assert_expr(expr * form)
{
    SASSERT(!m_in_level);
    m_contexts[0]->assert_expr(form);
    m_contexts[1]->assert_expr(form);
    IF_VERBOSE(21, verbose_stream() << "$ asserted " << mk_pp(form, m) << "\n";);
    TRACE("spacer", tout << "add_formula: " << mk_pp(form, m) << "\n";);
}

void prop_solver::assert_expr(expr * form, unsigned level)
{
    if (is_infty_level(level)) {assert_expr(form);return;}

    ensure_level(level);
    app * lev_atom = m_pos_level_atoms[level].get();
    app_ref lform(m.mk_or(form, lev_atom), m);
    assert_expr(lform);
}


/// Local model guided maxsmt
lbool prop_solver::mss(expr_ref_vector &hard, expr_ref_vector &soft) {
    // replace expressions by assumption literals
    iuc_solver::scoped_mk_proxy _p_(*m_ctx, hard);
    unsigned hard_sz = hard.size();

    lbool res = m_ctx->check_sat(hard.size(), hard.c_ptr());
    // bail out if hard constraints are not sat, or if there are no
    // soft constraints
    if (res != l_true || soft.empty()) {return res;}

    // the main loop

    model_ref mdl;
    m_ctx->get_model(mdl);

    // don't proxy soft literals. Assume that they are propositional.
    hard.append(soft);
    soft.reset();


    // hard is divided into 4 regions
    //            x < hard_sz      ---> hard constraints
    // hard_sz <= x < i            ---> sat soft constraints
    //       i <= x < j            ---> backbones (unsat soft constraints)
    //       j <= x < hard.size()  ---> unprocessed soft constraints
    unsigned i, j;
    i = hard_sz;
    j = hard_sz;

    while (j < hard.size()) {
        model_evaluator mev(*mdl);

        // move all true soft constraints to [hard_sz, i)
        for (unsigned k = j; k < hard.size(); ++k) {
            expr_ref e(m);
            e = hard.get(k);
            if (!mev.is_false(e) /* true or unset */) {
                expr_ref tmp(m);
                tmp = hard.get(i);
                hard[i] = e;
                if (i < j) {
                    // tmp is a backbone, put it at j
                    if (j == k) {hard[j] = tmp;}
                    else /* j < k */ {
                        e = hard.get(j);
                        hard[j] = tmp;
                        hard[k] = e;
                    }
                    j++;
                }
                else {
                    // there are no backbone literals
                    hard[k] = tmp;
                    j++;
                }
                i++;
            }
        }

        // done with the model. Reset to avoid confusion in debugging
        mdl.reset();

        // -- grow the set of backbone literals
        for (;j < hard.size(); ++j) {
            res = m_ctx->check_sat(j+1, hard.c_ptr());
            if (res == l_false) {
                // -- flip non-true literal to be false
                hard[j] = mk_not(m, hard.get(j));
            }
            else if (res == l_true) {
                // -- get the model for the next iteration of the outer loop
                m_ctx->get_model(mdl);
                break;
            }
            else if (res == l_undef) {
                // -- conservatively bail out
                hard.resize(hard_sz);
                return l_undef;
            }
        }
    }

    // move sat soft constraints to the output vector
    for (unsigned k = i; k < j; ++k) { soft.push_back(hard.get(k)); }
    // cleanup hard constraints
    hard.resize(hard_sz);
    return l_true;
}

/// Poor man's maxsat. No guarantees of maximum solution
/// Runs maxsat loop on m_ctx Returns l_false if hard is unsat,
/// otherwise reduces soft such that hard & soft is sat.
lbool prop_solver::maxsmt(expr_ref_vector &hard, expr_ref_vector &soft,
                          vector<expr_ref_vector> const & clauses)
{
    // replace expressions by assumption literals
    iuc_solver::scoped_mk_proxy _p_(*m_ctx, hard);
    unsigned hard_sz = hard.size();
    // assume soft constraints are propositional literals (no need to proxy)
    hard.append(soft);

    lbool res = m_ctx->check_sat_cc(hard, clauses);
    // if hard constraints alone are unsat or there are no soft
    // constraints, we are done
    if (res != l_false || soft.empty()) { return res; }

    // clear soft constraints, we will recompute them later
    soft.reset();

    expr_ref saved(m);
    expr_ref_vector core(m);
    m_ctx->get_unsat_core(core);

    // while there are soft constraints
    while (hard.size() > hard_sz) {
        bool found = false;
        // look for a soft constraint that is in the unsat core
        for (unsigned i = hard_sz, sz = hard.size(); i < sz; ++i)
            if (core.contains(hard.get(i))) {
                found = true;
                // AG: not sure why we are saving it
                saved = hard.get(i);
                hard[i] = hard.back();
                hard.pop_back();
                break;
            }
        // if no soft constraints in the core, return this should
        // not happen because it implies that hard alone is unsat
        // and that is taken care of earlier
        if (!found) {
            hard.resize(hard_sz);
            return l_false;
        }

        // check that the NEW constraints became sat
        res = m_ctx->check_sat_cc(hard, clauses);
        if (res != l_false) { break; }
        // still unsat, update the core and repeat
        core.reset();
        m_ctx->get_unsat_core(core);
    }

    // update soft with found soft constraints
    if (res == l_true) {
        for (unsigned i = hard_sz, sz = hard.size(); i < sz; ++i)
        { soft.push_back(hard.get(i)); }
    }
    // revert hard back to the right size
    // proxies are undone on exit via scoped_mk_proxy
    hard.resize(hard_sz);
    return res;
}

lbool prop_solver::internal_check_assumptions(expr_ref_vector &hard_atoms,
                                              expr_ref_vector &soft_atoms,
                                              vector<expr_ref_vector> const & clauses)
{
    // XXX Turn model generation if m_model != 0
    SASSERT(m_ctx);

    params_ref p;
    if (m_model != nullptr) {
        p.set_bool("produce_models", true);
        m_ctx->updt_params(p);
    }

    if (m_in_level) { assert_level_atoms(m_current_level); }
    lbool result = maxsmt(hard_atoms, soft_atoms, clauses);
    if (result != l_false && m_model) { m_ctx->get_model(*m_model); }

    SASSERT(result != l_false || soft_atoms.empty());

    /// compute level used in the core
    // XXX this is a poor approximation because the core will get minimized further
    if (result == l_false) {
        ptr_vector<expr> core;
        m_ctx->get_full_unsat_core(core);
        unsigned core_size = core.size();
        m_uses_level = infty_level();

        for (unsigned i = 0; i < core_size; ++i) {
            if (m_level_atoms_set.contains(core[i])) {
                unsigned sz = std::min(m_uses_level, m_neg_level_atoms.size());
                for (unsigned j = 0; j < sz; ++j)
                    if (m_neg_level_atoms [j].get() == core[i]) {
                        m_uses_level = j;
                        break;
                    }
                SASSERT(!is_infty_level(m_uses_level));
            }
        }
    }

    if (result == l_false && m_core && m.proofs_enabled() && !m_subset_based_core) {
        TRACE("spacer", tout << "Using IUC core\n";);
        m_core->reset();
        m_ctx->get_iuc(*m_core);
    } else if (result == l_false && m_core) {
        m_core->reset();
        m_ctx->get_unsat_core(*m_core);
        // manually undo proxies because maxsmt() call above manually adds proxies
        // AG: don't think this is needed. maxsmt() undoes the proxies already
        m_ctx->undo_proxies(*m_core);
    }

    if (m_model != nullptr) {
        p.set_bool("produce_models", false);
        m_ctx->updt_params(p);
    }

    return result;
}



lbool prop_solver::check_assumptions(const expr_ref_vector & _hard,
                                     expr_ref_vector& soft,
                                     const expr_ref_vector &clause,
                                     unsigned num_bg, expr * const * bg,
                                     unsigned solver_id)
{
    expr_ref cls(m);
    // current clients expect that flattening of HARD  is
    // done implicitly during check_assumptions
    expr_ref_vector hard(m);
    hard.append(_hard.size(), _hard.c_ptr());
    flatten_and(hard);

    shuffle(hard.size(), hard.c_ptr(), m_random);

    m_ctx = m_contexts [solver_id == 0 ? 0 : 0 /* 1 */].get();

    // can be disabled if use_push_bg == true
    // solver::scoped_push _s_(*m_ctx);
    if (!m_use_push_bg) {m_ctx->push();}
    iuc_solver::scoped_bg _b_(*m_ctx);

    for (unsigned i = 0; i < num_bg; ++i)
        if (m_use_push_bg) { m_ctx->push_bg(bg [i]); }
        else { m_ctx->assert_expr(bg[i]); }

    unsigned soft_sz = soft.size();
    (void) soft_sz;
    vector<expr_ref_vector> clauses;
    if (!clause.empty()) clauses.push_back(clause);
    lbool res = internal_check_assumptions(hard, soft, clauses);
    if (!m_use_push_bg) { m_ctx->pop(1); }

    TRACE("psolve_verbose",
          tout << "sat: " << mk_pp(mk_and(hard), m) << "\n"
          << mk_pp(mk_and(soft), m) << "\n";
          for (unsigned i = 0; i < num_bg; ++i)
          tout << "bg" << i << ": " << mk_pp(bg[i], m) << "\n";
          tout << "res: " << res << "\n";);
    CTRACE("psolve", m_core,
           tout << "core is: " << mk_pp(mk_and(*m_core), m) << "\n";);

    SASSERT(soft_sz >= soft.size());

    // -- reset all parameters
    m_core = nullptr;
    m_model = nullptr;
    m_subset_based_core = false;
    return res;
}

void prop_solver::collect_statistics(statistics& st) const
{
    m_contexts[0]->collect_statistics(st);
    m_contexts[1]->collect_statistics(st);
}

void prop_solver::reset_statistics()
{
}




}
