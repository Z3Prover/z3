/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    cofactor_term_ite_tactic.h

Abstract:

    Wrap cofactor_elim_term_ite as a tactic.

Author:

    Leonardo de Moura (leonardo) 2012-02-20.

Tactic Documentation:

## Tactic cofactor-term-ite

### Short Description
Eliminate (ground) term if-then-else's using cofactors.
It hoists nested if-then-else expressions inside terms into the top level of the formula.

### Notes

* does not support proofs, does not support cores

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "tactic/core/cofactor_elim_term_ite.h"

class cofactor_term_ite_simplifier : public dependent_expr_simplifier {
    params_ref             m_params;
    cofactor_elim_term_ite m_elim_ite;

public:
    cofactor_term_ite_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s)
        : dependent_expr_simplifier(m, s), m_params(p), m_elim_ite(m, p) {}

    char const* name() const override { return "cofactor-term-ite"; }

    void updt_params(params_ref const& p) override {
        m_params.append(p);
        m_elim_ite.updt_params(m_params);
    }

    void collect_param_descrs(param_descrs& r) override {
        m_elim_ite.collect_param_descrs(r);
    }

    bool supports_proofs() const override { return false; }

    void reduce() override {
        expr_ref new_fml(m);
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            m_elim_ite(d.fml(), new_fml);
            if (new_fml != d.fml())
                m_fmls.update(idx, dependent_expr(m, new_fml, nullptr, d.dep()));
        }
    }
};

inline dependent_expr_simplifier* mk_cofactor_term_ite_simplifier(
        ast_manager& m, params_ref const& p, dependent_expr_state& s) {
    return alloc(cofactor_term_ite_simplifier, m, p, s);
}

inline tactic* mk_cofactor_term_ite_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p, mk_cofactor_term_ite_simplifier);
}

/*
  ADD_TACTIC("cofactor-term-ite", "eliminate term if-then-else using cofactors.", "mk_cofactor_term_ite_tactic(m, p)")
  ADD_SIMPLIFIER("cofactor-term-ite", "eliminate term if-then-else using cofactors.", "mk_cofactor_term_ite_simplifier(m, p, s)")
*/

