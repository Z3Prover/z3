/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    horn_subsume_model_converter.h

Abstract:

    Model converter for redundant Horn clauses.

Author:

    Nikolaj Bjorner (nbjorner) 2012-9-16

Revision History:

    
Notes:


Subsumption transformation (remove Horn clause):

    P(x) :- Body(x,y)      Rules
    ----------------------------
    Rules
 
    
    Model converter: 

       P(x) := P(x) or (exists y. Body(x,y))

--*/

#ifndef HORN_SUBSUME_MODEL_CONVERTER_H_
#define HORN_SUBSUME_MODEL_CONVERTER_H_

#include "tactic/model_converter.h"
#include "ast/rewriter/th_rewriter.h"

class horn_subsume_model_converter : public model_converter {
    ast_manager&    m;
    func_decl_ref_vector m_funcs;
    expr_ref_vector      m_bodies;
    th_rewriter          m_rewrite;
    app_ref_vector       m_delay_head;
    expr_ref_vector      m_delay_body;

    void add_default_false_interpretation(expr* e, model_ref& md);

    struct add_default_proc {
        ast_manager& m;
        model_ref& m_md;
        add_default_proc(ast_manager& m, model_ref& md): m(m), m_md(md) {}
        void operator()(app* n);
        void operator()(expr* n) {}
    };

public:

    horn_subsume_model_converter(ast_manager& m): 
        m(m), m_funcs(m), m_bodies(m), m_rewrite(m), m_delay_head(m), m_delay_body(m) {}

    bool mk_horn(expr* clause, func_decl_ref& pred, expr_ref& body);

    bool mk_horn(app* head, expr* body, func_decl_ref& pred, expr_ref& body_res);

    void insert(app* head, expr* body);

    void insert(app* head, unsigned sz, expr* const* body);

    void insert(func_decl* p, expr* body) { m_funcs.push_back(p); m_bodies.push_back(body); }
    
    void operator()(model_ref& _m) override;

    void operator()(expr_ref& fml) override;

    model_converter * translate(ast_translation & translator) override;

    ast_manager& get_manager() { return m; }

    void display(std::ostream & out) override {}

    void get_units(obj_map<expr, bool>& units) override { units.reset(); }

};

#endif
