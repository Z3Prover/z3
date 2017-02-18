/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    filter_model_converter.cpp

Abstract:

    Filter decls from a model

Author:

    Leonardo (leonardo) 2011-05-06

Notes:

--*/
#include"filter_model_converter.h"
#include"model_v2_pp.h"

filter_model_converter::~filter_model_converter() {
}

void filter_model_converter::operator()(model_ref & old_model, unsigned goal_idx) {
    TRACE("filter_mc", tout << "before filter_model_converter\n"; model_v2_pp(tout, *old_model); display(tout););
    ast_fast_mark1 fs;
    unsigned num = m_decls.size();
    for (unsigned i = 0; i < num; i++) 
        fs.mark(m_decls.get(i));
    model * new_model = alloc(model, m());
    num = old_model->get_num_constants();
    for (unsigned i = 0; i < num; i++) {
        func_decl * f = old_model->get_constant(i);
        if (fs.is_marked(f))
            continue;
        expr * fi     = old_model->get_const_interp(f);
        new_model->register_decl(f, fi);
    }
    num = old_model->get_num_functions();
    for (unsigned i = 0; i < num; i++) {
        func_decl * f = old_model->get_function(i);
        if (fs.is_marked(f))
            continue;
        func_interp * fi = old_model->get_func_interp(f);
        SASSERT(fi);
        new_model->register_decl(f, fi->copy());
    }
    new_model->copy_usort_interps(*old_model);
    old_model = new_model;
    TRACE("filter_mc", tout << "after filter_model_converter\n"; model_v2_pp(tout, *old_model););
}

void filter_model_converter::operator()(svector<symbol> & labels, unsigned goal_idx) {
}

void filter_model_converter::display(std::ostream & out) {
    out << "(filter-model-converter";
    for (unsigned i = 0; i < m_decls.size(); i++) {
        out << " " << m_decls.get(i)->get_name();
    }
    out << ")" << std::endl;
}

model_converter * filter_model_converter::translate(ast_translation & translator) {
    filter_model_converter * res = alloc(filter_model_converter, translator.to());
    for (unsigned i = 0; i < m_decls.size(); i++)
        res->m_decls.push_back(translator(m_decls[i].get()));
    return res;
}
