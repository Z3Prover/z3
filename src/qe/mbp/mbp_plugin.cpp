/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_mbp.cpp

Abstract:

    Model-based projection utilities

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-29

Revision History:


--*/

#include "ast/rewriter/expr_safe_replace.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/occurs.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/expr_functors.h"
#include "ast/for_each_expr.h"
#include "ast/scoped_proof.h"
#include "qe/mbp/mbp_plugin.h"
#include "model/model_pp.h"
#include "model/model_evaluator.h"


using namespace mbp;

struct noop_op_proc {
    void operator()(expr*) {}
};


void project_plugin::mark_rec(expr_mark& visited, expr* e) {
    for_each_expr_proc<noop_op_proc> fe;    
    for_each_expr(fe, visited, e);
}

void project_plugin::mark_rec(expr_mark& visited, expr_ref_vector const& es) {
    for (unsigned i = 0; i < es.size(); ++i) {
        mark_rec(visited, es[i]);
    }
}

/**
   \brief return two terms that are equal in the model.
   The distinct term t is false in model, so there 
   are at least two arguments of t that are equal in the model.
*/
expr_ref project_plugin::pick_equality(ast_manager& m, model& model, expr* t) {
    SASSERT(m.is_distinct(t));
    expr_ref val(m);
    expr_ref_vector vals(m);
    obj_map<expr, expr*> val2expr;
    app* alit = to_app(t);
    if (alit->get_num_args() == 2) {
        return expr_ref(m.mk_eq(alit->get_arg(0), alit->get_arg(1)), m);
    }
    for (expr * e1 : *alit) {
        expr *e2;
        val = model(e1);
        TRACE("qe", tout << mk_pp(e1, m) << " |-> " << val << "\n";);
        if (val2expr.find(val, e2)) {
            return expr_ref(m.mk_eq(e1, e2), m);
        }
        val2expr.insert(val, e1);
        vals.push_back(val);
    }
    for (unsigned i = 0; i < alit->get_num_args(); ++i) {
        for (unsigned j = i + 1; j < alit->get_num_args(); ++j) {
            expr* e1 = alit->get_arg(i);
            expr* e2 = alit->get_arg(j);
            val = m.mk_eq(e1, e2);
            if (!model.is_false(val))
                return expr_ref(m.mk_eq(e1, e2), m);
        }
    }
    UNREACHABLE();
    return expr_ref(nullptr, m);
}


void project_plugin::erase(expr_ref_vector& lits, unsigned& i) {
    lits[i] = lits.back();
    lits.pop_back();
    --i;
}

void project_plugin::push_back(expr_ref_vector& lits, expr* e) {
    if (lits.get_manager().is_true(e)) return;
    lits.push_back(e);
}
