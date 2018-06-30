/*++
Copyright (c) 2018 Arie Gurfinkel

Module Name:

    dl_mk_elim_term_ite.h

Abstract:

   Remove term-ite expressions from the rules

Author:

    Arie Gurfinkel (agurfinkel)

Revision History:

--*/
#pragma once

#include "muz/base/dl_context.h"
#include "muz/base/dl_rule_set.h"
#include "muz/base/dl_rule_transformer.h"
#include "tactic/equiv_proof_converter.h"

namespace datalog {
    class mk_elim_term_ite : public rule_transformer::plugin {
        context &m_ctx;
        ast_manager &m;
        rule_manager &rm;

        expr_ref_vector m_ground;

        bool elim(rule &r, rule_set &new_rules);
        expr_ref ground(expr_ref &e);
    public:
        mk_elim_term_ite(context &ctx, unsigned priority);
        ~mk_elim_term_ite() override;
        rule_set * operator()(const rule_set &source) override;
    };
}
