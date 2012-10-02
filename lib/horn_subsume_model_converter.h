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

#ifndef _HORN_SUBSUME_MODEL_CONVERTER_H_
#define _HORN_SUBSUME_MODEL_CONVERTER_H_

#include "model_converter.h"

class horn_subsume_model_converter : public model_converter {
    ast_manager&    m;
    func_decl_ref_vector m_funcs;
    expr_ref_vector      m_bodies;

public:

    horn_subsume_model_converter(ast_manager& m): m(m), m_funcs(m), m_bodies(m) {}

    bool mk_horn(expr* clause, func_decl_ref& pred, expr_ref& body) const;

    bool mk_horn(app* head, expr* body, func_decl_ref& pred, expr_ref& body_res) const;

    void insert(app* head, expr* body);

    void insert(app* head, unsigned sz, expr* const* body);

    void insert(func_decl* p, expr* body) { m_funcs.push_back(p); m_bodies.push_back(body); }
    
    virtual void operator()(model_ref& m);

    virtual model_converter * translate(ast_translation & translator);

    ast_manager& get_manager() { return m; }

};

#endif
