/*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  lackr_model_converter_lazy.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include "ackermannization/lackr_model_converter_lazy.h"
#include "model/model_evaluator.h"
#include "ast/ast_smt2_pp.h"
#include "ackermannization/ackr_info.h"
#include "ackermannization/lackr_model_constructor.h"

class lackr_model_converter_lazy : public model_converter {
public:
    lackr_model_converter_lazy(ast_manager & m,
        const lackr_model_constructor_ref& lmc)
        : m(m)
        , model_constructor(lmc)
    { }

    ~lackr_model_converter_lazy() override { }

    void operator()(model_ref & md, unsigned goal_idx) override {
        SASSERT(goal_idx == 0);
        SASSERT(md.get() == 0 || (!md->get_num_constants() && !md->get_num_functions()));
        SASSERT(model_constructor.get());
        model * new_model = alloc(model, m);
        md = new_model;
        model_constructor->make_model(md);
    }

    void operator()(model_ref & md) override {
        operator()(md, 0);
    }

    //void display(std::ostream & out);

    model_converter * translate(ast_translation & translator) override {
        NOT_IMPLEMENTED_YET();
    }
protected:
    ast_manager&                       m;
    const lackr_model_constructor_ref  model_constructor;
};

model_converter * mk_lackr_model_converter_lazy(ast_manager & m,
    const lackr_model_constructor_ref&  model_constructor) {
    return alloc(lackr_model_converter_lazy, m, model_constructor);
}
