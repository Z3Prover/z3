/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    filter_model_converter.h

Abstract:

    Filter decls from a model

Author:

    Leonardo (leonardo) 2011-05-06

Notes:

--*/
#ifndef FILTER_MODEL_CONVERTER_H_
#define FILTER_MODEL_CONVERTER_H_

#include "tactic/model_converter.h"

class filter_model_converter : public model_converter {
    func_decl_ref_vector  m_decls;
public:
    filter_model_converter(ast_manager & m):m_decls(m) {}
    
    ~filter_model_converter() override;
    
    ast_manager & m() const { return m_decls.get_manager(); }
    
    void operator()(model_ref & md, unsigned goal_idx) override;

    virtual void operator()(svector<symbol> & labels, unsigned goal_idx);
    
    void operator()(model_ref & md) override { operator()(md, 0); } // TODO: delete

    void cancel() override {}

    void display(std::ostream & out) override;

    void insert(func_decl * d) {
        m_decls.push_back(d);
    }

    model_converter * translate(ast_translation & translator) override;
};

typedef ref<filter_model_converter> filter_model_converter_ref;

#endif
