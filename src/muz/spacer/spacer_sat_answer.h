/*++
Copyright (c) 2018 Arie Gurfinkel

Module Name:

    spacer_sat_answer.h

Abstract:

  Compute refutation proof for CHC

Author:

    Arie Gurfinkel

Revision History:

--*/

#pragma once

#include "muz/spacer/spacer_context.h"
#include "ast/ast.h"
#include "util/obj_hashtable.h"
#include "model/model.h"
#include "solver/solver.h"

namespace spacer {

class ground_sat_answer_op {
    const context &m_ctx;
    ast_manager &m;
    const manager &m_pm;

    expr_ref_vector m_pinned;
    obj_map<expr, proof*> m_cache;

    ref<solver> m_solver;

    struct frame;

    proof *mk_proof_step(frame &fr);
    void mk_children(frame &fr, vector<frame> &todo);
    void mk_child_subst_from_model(func_decl *pred, unsigned i,
                                   model_ref &mdl, expr_ref_vector &subst);

public:
    ground_sat_answer_op(const context &ctx);

    proof_ref operator() (pred_transformer &query);
};
}

