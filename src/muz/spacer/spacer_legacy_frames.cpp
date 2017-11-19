/*
  Copyright (c) 2017 Arie Gurfinkel

  Legacy implementations of frames. To be removed.
 */
#include <sstream>
#include <iomanip>

#include "muz/spacer/spacer_context.h"
#include "muz/base/dl_util.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/var_subst.h"
#include "util/util.h"
#include "muz/spacer/spacer_prop_solver.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "ast/for_each_expr.h"
#include "muz/base/dl_rule_set.h"
#include "smt/tactic/unit_subsumption_tactic.h"
#include "model/model_smt2_pp.h"
#include "muz/transforms/dl_mk_rule_inliner.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_util.h"
#include "ast/proofs/proof_checker.h"
#include "smt/smt_value_sort.h"
#include "ast/proofs/proof_utils.h"
#include "ast/scoped_proof.h"
#include "muz/spacer/spacer_qe_project.h"
#include "tactic/core/blast_term_ite_tactic.h"

#include "util/timeit.h"
#include "util/luby.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/expr_abstract.h"
#include "ast/factor_equivs.h"


namespace spacer {
// ------------------
// legacy_frames
void pred_transformer::legacy_frames::simplify_formulas(tactic& tac,
        expr_ref_vector& v)
{
    ast_manager &m = m_pt.get_ast_manager();
    goal_ref g(alloc(goal, m, false, false, false));
    for (unsigned j = 0; j < v.size(); ++j) { g->assert_expr(v[j].get()); }
    goal_ref_buffer result;
    tac(g, result);
    SASSERT(result.size() == 1);
    goal* r = result[0];
    v.reset();
    for (unsigned j = 0; j < r->size(); ++j) { v.push_back(r->form(j)); }
}

void pred_transformer::legacy_frames::simplify_formulas()
{
    ast_manager &m = m_pt.get_ast_manager();
    tactic_ref us = mk_unit_subsumption_tactic(m);
    simplify_formulas(*us, m_invariants);
    for (unsigned i = 0; i < m_levels.size(); ++i) {
        simplify_formulas(*us, m_levels[i]);
    }
}

void pred_transformer::legacy_frames::get_frame_geq_lemmas(unsigned lvl,
        expr_ref_vector &out)
{
    get_frame_lemmas(infty_level(), out);
    for (unsigned i = lvl, sz = m_levels.size(); i < sz; ++i)
    { get_frame_lemmas(i, out); }
}

bool pred_transformer::legacy_frames::propagate_to_next_level(unsigned src_level)
{

    ast_manager &m = m_pt.get_ast_manager();
    (void) m;
    if (m_levels.size() <= src_level) { return true; }
    if (m_levels [src_level].empty()) { return true; }

    unsigned tgt_level = next_level(src_level);
    m_pt.ensure_level(next_level(tgt_level));

    TRACE("spacer",
          tout << "propagating " << src_level << " to " << tgt_level;
          tout << " for relation " << m_pt.head()->get_name() << "\n";);

    for (unsigned i = 0; i < m_levels[src_level].size();) {
        expr_ref_vector &src = m_levels[src_level];
        expr * curr = src[i].get();
        unsigned stored_lvl;
        VERIFY(m_prop2level.find(curr, stored_lvl));
        SASSERT(stored_lvl >= src_level);
        unsigned solver_level;
        if (stored_lvl > src_level) {
            TRACE("spacer", tout << "at level: " << stored_lvl << " " << mk_pp(curr, m) << "\n";);
            src[i] = src.back();
            src.pop_back();
        } else if (m_pt.is_invariant(tgt_level, curr, solver_level)) {
            // -- might invalidate src reference
            add_lemma(curr, solver_level);
            TRACE("spacer", tout << "is invariant: " << pp_level(solver_level) << " " << mk_pp(curr, m) << "\n";);
            // shadow higher-level src
            expr_ref_vector &src = m_levels[src_level];
            src[i] = src.back();
            src.pop_back();
            ++m_pt.m_stats.m_num_propagations;
        } else {
            TRACE("spacer", tout << "not propagated: " << mk_pp(curr, m) << "\n";);
            ++i;
        }
    }

    CTRACE("spacer", m_levels[src_level].empty(),
           tout << "Fully propagated level "
           << src_level << " of " << m_pt.head()->get_name() << "\n";);

    return m_levels[src_level].empty();
}

bool pred_transformer::legacy_frames::add_lemma(expr * lemma, unsigned lvl)
{
    if (is_infty_level(lvl)) {
        if (!m_invariants.contains(lemma)) {
            m_invariants.push_back(lemma);
            m_prop2level.insert(lemma, lvl);
        //m_pt.add_lemma_core (lemma, lvl);
        return true;
    }
    return false;
    }

    unsigned old_level;
    if (!m_prop2level.find(lemma, old_level) || old_level < lvl) {
        m_levels[lvl].push_back(lemma);
        m_prop2level.insert(lemma, lvl);
        //m_pt.add_lemma_core (lemma, lvl);
        return true;
    }
    return false;
}

void  pred_transformer::legacy_frames::propagate_to_infinity(unsigned level)
{
    TRACE("spacer", tout << "propagating to oo from lvl " << level
          << " of " << m_pt.m_head->get_name() << "\n";);

    if (m_levels.empty()) { return; }

    for (unsigned i = m_levels.size(); i > level; --i) {
        expr_ref_vector &lemmas = m_levels [i - 1];
        for (unsigned j = 0; j < lemmas.size(); ++j)
        { add_lemma(lemmas.get(j), infty_level()); }
        lemmas.reset();
    }
}

void pred_transformer::legacy_frames::inherit_frames(legacy_frames& other)
{

    SASSERT(m_pt.m_head == other.m_pt.m_head);
    obj_map<expr, unsigned>::iterator it  = other.m_prop2level.begin();
    obj_map<expr, unsigned>::iterator end = other.m_prop2level.end();
    for (; it != end; ++it) { add_lemma(it->m_key, it->m_value); }
}
}
