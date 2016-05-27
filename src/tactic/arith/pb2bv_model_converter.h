/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    pb2bv_model_converter.h

Abstract:

    Model converter for the pb2bv tactic.

Author:

    Christoph (cwinter) 2012-02-15

Notes:

--*/
#ifndef PB2BV_MODEL_CONVERTER_H_
#define PB2BV_MODEL_CONVERTER_H_

#include"model_converter.h"
#include"bound_manager.h"

class pb2bv_model_converter : public model_converter {
    typedef std::pair<func_decl *, func_decl *> func_decl_pair;
    
    ast_manager &             m;    
    svector<func_decl_pair>   m_c2bit;
public:
    pb2bv_model_converter(ast_manager & _m);
    pb2bv_model_converter(ast_manager & _m, obj_map<func_decl, expr*> const & c2bit, bound_manager const & bm);
    virtual ~pb2bv_model_converter();
    virtual void operator()(model_ref & md);
    virtual void operator()(model_ref & md, unsigned goal_idx);
    virtual void display(std::ostream & out);
    virtual model_converter * translate(ast_translation & translator);
};

#endif
