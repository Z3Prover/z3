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

        entry& operator=(entry const& other) {
            m_f = other.m_f;
            m_def = other.m_def;
            m_instruction = other.m_instruction;
            return *this;
        }
    };
    ast_manager& m;
    std::string  m_orig;
    vector<entry> m_entries;
    obj_map<func_decl, unsigned> m_first_idx;

    expr_ref simplify_def(entry const& e);

public:
    generic_model_converter(ast_manager & m, char const* orig) : m(m), m_orig(orig) {}
    
    virtual ~generic_model_converter();
    
    void hide(expr* e) { SASSERT(is_app(e) && to_app(e)->get_num_args() == 0); hide(to_app(e)->get_decl()); }

    void hide(func_decl * f) { m_entries.push_back(entry(f, 0, m, HIDE)); }

    void add(func_decl * d, expr* e);

    void add(expr * d, expr* e) { SASSERT(is_app(d) && to_app(d)->get_num_args() == 0); add(to_app(d)->get_decl(), e); }
    
    void operator()(labels_vec & labels) override {}
    
    void operator()(model_ref & md) override;

    void cancel() override {}

    void display(std::ostream & out) override;

    model_converter * translate(ast_translation & translator) override;

    void collect(ast_pp_util& visitor) override;

    void operator()(expr_ref& fml) override; 

    void get_units(obj_map<expr, bool>& units) override;
};

typedef ref<generic_model_converter> generic_model_converter_ref;

#endif
