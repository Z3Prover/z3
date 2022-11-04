/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    model_reconstruction_trail.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-3.
    
--*/


#include "ast/simplifiers/model_reconstruction_trail.h"
#include "ast/converters/generic_model_converter.h"


void model_reconstruction_trail::replay(dependent_expr const& d, vector<dependent_expr>& added) {
    // accumulate a set of dependent exprs, updating m_trail to exclude loose 
    // substitutions that use variables from the dependent expressions.
    ast_mark free_vars;
    auto [f, dep] = d;
    for (expr* t : subterms::all(expr_ref(f, m))) 
        free_vars.mark(t);
    
    NOT_IMPLEMENTED_YET();
}

/**
 * retrieve the current model converter corresponding to chaining substitutions from the trail.
 */
model_converter_ref model_reconstruction_trail::get_model_converter() {
    model_converter_ref mc = alloc(generic_model_converter, m, "dependent-expr-model");
    // walk the trail from the back.
    // add substitutions from the back to the generic model converter
    // after they have been normalized using a global replace that replaces 
    // substituted variables by their terms.
    NOT_IMPLEMENTED_YET();
    return mc;

}

