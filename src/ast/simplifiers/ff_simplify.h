/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_simplify.h

Abstract:

    Simplifiers for prime-field ("QF_FF") goals:

    - ff_disjunctive_simplifier rewrites disjunctive Boolean field domains
      `(a=b) or (c=d)` as the polynomial equation `(a-b)*(c-d)=0`, when doing
      so does not hide a univariate Boolean-domain candidate.
    - ff_zero_test_simplifier derives Boolean zero-test indicator
      definitions from `x*z=0`-shaped equations.
    - ff_wire_simplifier eliminates acyclic "wire" definitions `x = t`
      (definitions whose right-hand side does not (transitively) mention
      `x`), substituting `x` by `t` and recording the elimination on the
      model reconstruction trail.

    ff_basic_simplifier composes the above together with the generic
    simplify/propagate-values/solve-eqs simplifiers into the "ff-simplify"
    preprocessing pipeline used ahead of the QF_FF decision procedures
    (ff-solve, ff-sat, ff-unique). It preserves compact theory atoms for
    lazy Boolean search by skipping simplification entirely when a goal
    contains a Boolean uninterpreted constant anywhere (the algebraic
    decision procedures normalize circuits on their own), and declines to
    run when proofs are requested (QF_FF certificates are not supported in
    v1).

Author:

    Romain Soulat

--*/
#pragma once

#include "util/stopwatch.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/simplifiers/then_simplifier.h"

class ff_disjunctive_simplifier : public dependent_expr_simplifier {
    params_ref m_params;

public:
    ff_disjunctive_simplifier(ast_manager &m, params_ref const &p, dependent_expr_state &s);
    char const *name() const override { return "ff-disjunctive"; }
    void reduce() override;
    void updt_params(params_ref const &p) override;
    void collect_param_descrs(param_descrs &r) override;
};

class ff_zero_test_simplifier : public dependent_expr_simplifier {
    unsigned m_added = 0;

public:
    ff_zero_test_simplifier(ast_manager &m, dependent_expr_state &s) : dependent_expr_simplifier(m, s) {}
    char const *name() const override { return "ff-zero-test"; }
    void reduce() override;
    void collect_statistics(statistics &st) const override;
    void reset_statistics() override { m_added = 0; }
};

class ff_wire_simplifier : public dependent_expr_simplifier {
    unsigned  m_eliminated = 0;
    stopwatch m_elapsed;

public:
    ff_wire_simplifier(ast_manager &m, dependent_expr_state &s) : dependent_expr_simplifier(m, s) {}
    char const *name() const override { return "ff-wires"; }
    void reduce() override;
    void collect_statistics(statistics &st) const override;
    void reset_statistics() override {
        m_eliminated = 0;
        m_elapsed.reset();
    }
};

class ff_basic_simplifier : public dependent_expr_simplifier {
    params_ref                  m_params;
    scoped_ptr<then_simplifier> m_impl;
    stopwatch                   m_elapsed;
    unsigned                    m_boolean_skips = 0;

    bool skip_boolean_goal();

public:
    ff_basic_simplifier(ast_manager &m, params_ref const &p, dependent_expr_state &s);
    char const *name() const override { return "ff-simplify"; }
    bool supports_proofs() const override { return true; }
    void reduce() override;
    void collect_statistics(statistics &st) const override;
    void reset_statistics() override;
    void updt_params(params_ref const &p) override;
    void collect_param_descrs(param_descrs &r) override;
};

Z3_ADD_SIMPLIFIER(ff_disjunctive, "ff-disjunctive", "rewrite disjunctive Boolean field domains as polynomial equations.",
                  alloc(ff_disjunctive_simplifier, m, p, s));
Z3_ADD_SIMPLIFIER(ff_zero_test, "ff-zero-test", "derive Boolean zero-test indicators for prime-field goals.",
                  alloc(ff_zero_test_simplifier, m, s));
Z3_ADD_SIMPLIFIER(ff_wires, "ff-wires", "eliminate acyclic wire definitions in prime-field goals.",
                  alloc(ff_wire_simplifier, m, s));
Z3_ADD_SIMPLIFIER(ff_simplify, "ff-simplify", "simplify prime-field goals ahead of QF_FF decision procedures.",
                  alloc(ff_basic_simplifier, m, p, s));
