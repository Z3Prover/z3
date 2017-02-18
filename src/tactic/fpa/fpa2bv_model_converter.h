/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa2bv_model_converter.h

Abstract:

    Model conversion for fpa2bv_converter

Author:

    Christoph (cwinter) 2012-02-09

Notes:

--*/
#ifndef FPA2BV_MODEL_CONVERTER_H_
#define FPA2BV_MODEL_CONVERTER_H_

#include"fpa2bv_converter.h"
#include"model_converter.h"
#include"bv2fpa_converter.h"

class fpa2bv_model_converter : public model_converter {
    ast_manager & m;
    bv2fpa_converter * m_bv2fp;
    
public:
    fpa2bv_model_converter(ast_manager & m, fpa2bv_converter & conv):
        m(m),
        m_bv2fp(alloc(bv2fpa_converter, m, conv)) {
    }

    virtual ~fpa2bv_model_converter() {
        dealloc(m_bv2fp);
    }

    virtual void operator()(model_ref & md, unsigned goal_idx) {
        SASSERT(goal_idx == 0);
        model * new_model = alloc(model, m);
        convert(md.get(), new_model);
        md = new_model;
    }

    virtual void operator()(model_ref & md) {
        operator()(md, 0);
    }

    void display(std::ostream & out);

    virtual model_converter * translate(ast_translation & translator);

protected:
    fpa2bv_model_converter(ast_manager & m) : 
        m(m),
        m_bv2fp(0) {}
    
    void convert(model_core * mc, model * float_mdl);
};


model_converter * mk_fpa2bv_model_converter(ast_manager & m, fpa2bv_converter & conv);

#endif
