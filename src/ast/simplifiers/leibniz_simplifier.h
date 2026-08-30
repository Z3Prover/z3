/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    leibniz_simplifier.h

Abstract:

    Synthesize Leibniz-equality style predicate instantiations for
    universally quantified predicate variables.

    Many higher-order TPTP/THF problems state properties using Leibniz
    equality: "for all predicates P, if P(a) then P(b)" is used to derive
    "a = b" (by instantiating P with (\y. y = a) or (\y. y = b)), or dually,
    a hypothesis "a = b" is used together with a universally quantified
    predicate application "P(a)" to derive "P(b)" by instantiating the
    quantifier defining P's use with a substitution witness.

    Ordinary E-matching cannot discover such instantiations because the
    witness predicate (\y. y = t) never literally occurs in the input; it
    must be synthesized. This simplifier looks for a syntactic pattern
    that is common in TPTP/THF benchmarks:

        ![Xp : T > $o, ...] : ( ... (Xp @ s) ... => ... (Xp @ t) ... )

    i.e., a universally quantified variable of predicate sort T > $o that
    is applied (via array select, THF's application encoding) to at least
    two distinct sub-terms s, t of sort T appearing in the body. For each
    such quantifier we add, as additional (sound, since it is merely an
    instance of the original quantifier) axioms, the instantiations of the
    quantifier where Xp is replaced by each of the synthesized Leibniz
    witnesses (\y. y = s) and (\y. y = t) for every pair of distinct
    argument terms (s, t) found. This turns a higher-order reasoning step
    into ordinary ground/first-order reasoning that the SMT core can
    complete via congruence and E-matching on the remaining quantifiers.

Author:

    Nikolaj Bjorner (nbjorner) 2024

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/array_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"

class leibniz_simplifier : public dependent_expr_simplifier {

    struct stats {
        unsigned m_num_instances = 0;
        void reset() { m_num_instances = 0; }
    };

    struct config {
        // maximum number of distinct witness terms to collect per candidate
        // predicate variable (bounds the combinatorial blowup: instances
        // added is at most this many per quantified predicate variable).
        unsigned m_max_witnesses = 4;
        // maximum number of quantified formulas to scan for the pattern.
        unsigned m_max_quantifiers = 512;
    };

    array_util   m_array;
    th_rewriter  m_rewriter;
    stats        m_stats;
    config       m_config;
    expr_mark    m_processed; // quantifiers already instantiated; avoid reprocessing on repeated reduce() passes

    // collect ground/ambient sub-terms of sort `dom` that appear as the
    // argument of an application (select) of the bound variable at de Bruijn
    // index `didx` (i.e., candidates for Leibniz witnesses), within `n`.
    void collect_witnesses(expr* n, unsigned didx, sort* dom, ptr_vector<expr>& witnesses, expr_mark& seen);

    // try to find, for quantifier q, predicate-sorted bound variables that
    // are applied to distinct witness terms in the body; for each, add
    // instantiated (Leibniz-witness-substituted) versions of q as new axioms.
    void try_instantiate(quantifier* q, dependent_expr const& de);

public:
    leibniz_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_array(m),
        m_rewriter(m) {
        updt_params(p);
    }

    char const* name() const override { return "leibniz-instantiation"; }

    void reduce() override;

    void collect_statistics(statistics& st) const override {
        st.update("leibniz-instances", m_stats.m_num_instances);
    }

    void reset_statistics() override { m_stats.reset(); }

    void updt_params(params_ref const& p) override {
        m_rewriter.updt_params(p);
        m_config.m_max_witnesses = p.get_uint("leibniz_max_witnesses", m_config.m_max_witnesses);
    }

    void collect_param_descrs(param_descrs& r) override {
        th_rewriter::get_param_descrs(r);
        r.insert("leibniz_max_witnesses", CPK_UINT, "max number of Leibniz-equality witness terms to synthesize per quantified predicate variable", "4");
    }
};

/*
  ADD_SIMPLIFIER("leibniz-instantiation", "synthesize and add Leibniz-equality style predicate instantiations for quantified predicate variables applied to distinct argument terms.", "alloc(leibniz_simplifier, m, p, s)")
 */
