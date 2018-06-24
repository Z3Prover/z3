/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    extension_model_converter.h

Abstract:

    Model converter that introduces new interpretations into a model.
    It used to be called elim_var_model_converter

Author:

    Leonardo (leonardo) 2011-10-21

Notes:

--*/
#ifndef EXTENSION_MODEL_CONVERTER_H_
#define EXTENSION_MODEL_CONVERTER_H_

#include "ast/ast.h"
#include "tactic/model_converter.h"


class extension_model_converter : public model_converter {
    func_decl_ref_vector  m_vars;
    expr_ref_vector       m_defs;
public:
    extension_model_converter(ast_manager & m):m_vars(m), m_defs(m) {
    }

    ~extension_model_converter() override;

    ast_manager & m() const { return m_vars.get_manager(); }

    void operator()(model_ref & md) override;

    void display(std::ostream & out) override;

    // register a variable that was eliminated
    void insert(func_decl * v, expr * def);

    model_converter * translate(ast_translation & translator) override;
};


#endif
