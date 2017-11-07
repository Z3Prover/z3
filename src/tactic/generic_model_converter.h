/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    generic_model_converter.h

Abstract:

    Generic model converter that hides and adds entries.
    It subsumes filter_model_converter and extension_model_converter.

Author:

    Nikolaj Bjorner (nbjorner) 2017-10-29

Notes:

--*/
#ifndef GENERIC_MODEL_CONVERTER_H_
#define GENERIC_MODEL_CONVERTER_H_

#include "tactic/model_converter.h"

class generic_model_converter : public model_converter {
    enum instruction { HIDE, ADD };
    struct entry {
        func_decl_ref m_f;
        expr_ref      m_def;
        instruction   m_instruction;
        entry(func_decl* f, expr* d, ast_manager& m, instruction i):
            m_f(f, m), m_def(d, m), m_instruction(i) {}
    };
    ast_manager& m;
    vector<entry> m_entries;
public:
    generic_model_converter(ast_manager & m): m(m) {}
    
    virtual ~generic_model_converter() { }
    
    void hide(func_decl * f) { m_entries.push_back(entry(f, 0, m, HIDE)); }

    void add(func_decl * d, expr* e) { m_entries.push_back(entry(d, e, m, ADD)); }
    
    virtual void operator()(model_ref & md, unsigned goal_idx);

    virtual void operator()(svector<symbol> & labels, unsigned goal_idx) {}
    
    virtual void operator()(model_ref & md) { operator()(md, 0); } 

    virtual void cancel() {}

    virtual void display(std::ostream & out);

    virtual model_converter * translate(ast_translation & translator);

    virtual void collect(ast_pp_util& visitor);
};

typedef ref<generic_model_converter> generic_model_converter_ref;

#endif
