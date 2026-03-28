/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    nnf_simplifier.h

Abstract:

    NNF simplifier

Author:

    Nikolaj Bjorner (nbjorner) 2024-01-01

--*/
#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/normal_forms/nnf.h"
#include "ast/normal_forms/defined_names.h"

class nnf_simplifier : public dependent_expr_simplifier {
    params_ref   m_params;

public:
    nnf_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s)
        : dependent_expr_simplifier(m, s), m_params(p) {}

    char const* name() const override { return "nnf"; }

    bool supports_proofs() const override { return true; }

    void updt_params(params_ref const& p) override { m_params.append(p); }

    void collect_param_descrs(param_descrs& r) override { nnf::get_param_descrs(r); }

    void reduce() override {
        defined_names dnames(m);
        nnf local_nnf(m, dnames, m_params);

        expr_ref_vector  defs(m);
        proof_ref_vector def_prs(m);
        expr_ref         new_curr(m);
        proof_ref        new_pr(m);

        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            local_nnf(d.fml(), defs, def_prs, new_curr, new_pr);
            m_fmls.update(idx, dependent_expr(m, new_curr, mp(d.pr(), new_pr), d.dep()));
        }

        for (unsigned i = 0; i < defs.size(); ++i)
            m_fmls.add(dependent_expr(m, defs.get(i), def_prs.get(i), nullptr));

        unsigned num_extra_names = dnames.get_num_names();
        for (unsigned i = 0; i < num_extra_names; ++i)
            m_fmls.model_trail().hide(dnames.get_name_decl(i));
    }
};
