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

#include"model_converter.h"

class filter_model_converter : public model_converter {
    func_decl_ref_vector  m_decls;
public:
    filter_model_converter(ast_manager & m):m_decls(m) {}
    
    virtual ~filter_model_converter();
    
    ast_manager & m() const { return m_decls.get_manager(); }
    
    virtual void operator()(model_ref & md, unsigned goal_idx);

    virtual void operator()(svector<symbol> & labels, unsigned goal_idx);
    
    virtual void operator()(model_ref & md) { operator()(md, 0); } // TODO: delete

    virtual void cancel() {}

    virtual void display(std::ostream & out);

    void insert(func_decl * d) {
        m_decls.push_back(d);
    }

    virtual model_converter * translate(ast_translation & translator);
};

typedef ref<filter_model_converter> filter_model_converter_ref;

#endif
