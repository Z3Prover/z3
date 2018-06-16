/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_evaluator.h

Abstract:

    Evaluate expressions in a given model.

Author:

    Leonardo de Moura (leonardo) 2011-04-30.

Revision History:

--*/
#ifndef MODEL_EVALUATOR_H_
#define MODEL_EVALUATOR_H_

#include "ast/ast.h"
#include "ast/rewriter/rewriter_types.h"
#include "util/params.h"

class model;
class model_core;

typedef rewriter_exception model_evaluator_exception;

class model_evaluator {
    struct imp;
    imp *  m_imp;
public:
    model_evaluator(model_core & m, params_ref const & p = params_ref());
    ~model_evaluator();

    ast_manager & m () const;
    void set_model_completion(bool f);
    bool get_model_completion() const; 
    void set_expand_array_equalities(bool f);

    void updt_params(params_ref const & p);
    static void get_param_descrs(param_descrs & r);

    void operator()(expr * t, expr_ref & r);
    expr_ref operator()(expr* t);
    expr_ref_vector operator()(expr_ref_vector const& ts);

    // exception safe
    bool eval(expr* t, expr_ref& r, bool model_completion = true);
    bool eval(expr_ref_vector const& ts, expr_ref& r, bool model_completion = true);

    bool is_true(expr * t);
    bool is_false(expr * t);
    bool is_true(expr_ref_vector const& ts);

    /**
     * best effort evaluator of extensional array equality.
     */
    expr_ref eval_array_eq(app* e, expr* arg1, expr* arg2);

    void cleanup(params_ref const & p = params_ref());
    void reset(params_ref const & p = params_ref());
    void reset(model_core& model, params_ref const & p = params_ref());

    unsigned get_num_steps() const;
};

#endif
