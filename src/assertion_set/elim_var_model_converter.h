/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    elim_var_model_converter.h

Abstract:

    Model converter that introduces eliminated variables in a model.

Author:

    Leonardo (leonardo) 2011-05-05

Notes:

--*/
#ifndef _ELIM_VAR_MODEL_CONVERTER_H_
#define _ELIM_VAR_MODEL_CONVERTER_H_

#include"ast.h"
#include"model_converter.h"

class model_evaluator;

class elim_var_model_converter : public model_converter {
    func_decl_ref_vector  m_vars;
    expr_ref_vector       m_defs;
    model_evaluator *     m_eval;
    struct set_eval;
public:    
    elim_var_model_converter(ast_manager & m):m_vars(m), m_defs(m), m_eval(0) {
    }
    
    virtual ~elim_var_model_converter();
    
    ast_manager & m() const { return m_vars.get_manager(); }
    
    virtual void operator()(model_ref & md);

    virtual void cancel();

    virtual void display(std::ostream & out);

    // register a variable that was eliminated
    void insert(func_decl * v, expr * def) {
        m_vars.push_back(v);
        m_defs.push_back(def);
    }

    virtual model_converter * translate(ast_translation & translator);
};


#endif
