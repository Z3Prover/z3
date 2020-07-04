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
#pragma once

#include "ast/fpa/fpa2bv_converter.h"
#include "tactic/model_converter.h"
#include "ast/fpa/bv2fpa_converter.h"

class fpa2bv_model_converter : public model_converter {
    ast_manager & m;
    bv2fpa_converter * m_bv2fp;

public:
    fpa2bv_model_converter(ast_manager & m, fpa2bv_converter & conv):
        m(m),
        m_bv2fp(alloc(bv2fpa_converter, m, conv)) {
    }

    ~fpa2bv_model_converter() override {
        dealloc(m_bv2fp);
    }

    void operator()(model_ref & md) override {
        model_ref new_model = alloc(model, m);
        convert(md.get(), new_model.get());
        md = new_model;
    }

    void display(std::ostream & out) override;

    model_converter * translate(ast_translation & translator) override;

protected:
    fpa2bv_model_converter(ast_manager & m) :
        m(m),
        m_bv2fp(nullptr) {}

    void convert(model_core * mc, model * float_mdl);
};


model_converter * mk_fpa2bv_model_converter(ast_manager & m, fpa2bv_converter & conv);

