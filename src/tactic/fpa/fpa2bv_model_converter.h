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

class fpa2bv_model_converter : public model_converter {
    ast_manager               & m;
    obj_map<func_decl, expr*>   m_const2bv;
    obj_map<func_decl, expr*>   m_rm_const2bv;
    obj_map<func_decl, func_decl*>  m_uf2bvuf;

public:
    fpa2bv_model_converter(ast_manager & m, obj_map<func_decl, expr*> const & const2bv,
                           obj_map<func_decl, expr*> const & rm_const2bv,
                           obj_map<func_decl, func_decl*> const & uf2bvuf) :
                           m(m) {
        // Just create a copy?
        for (obj_map<func_decl, expr*>::iterator it = const2bv.begin();
             it != const2bv.end();
             it++)
        {
            m_const2bv.insert(it->m_key, it->m_value);
            m.inc_ref(it->m_key);
            m.inc_ref(it->m_value);
        }
        for (obj_map<func_decl, expr*>::iterator it = rm_const2bv.begin();
             it != rm_const2bv.end();
             it++)
        {
            m_rm_const2bv.insert(it->m_key, it->m_value);
            m.inc_ref(it->m_key);
            m.inc_ref(it->m_value);
        }
        for (obj_map<func_decl, func_decl*>::iterator it = uf2bvuf.begin();
             it != uf2bvuf.end();
             it++)
        {
            m_uf2bvuf.insert(it->m_key, it->m_value);
            m.inc_ref(it->m_key);
            m.inc_ref(it->m_value);
        }
    }

    virtual ~fpa2bv_model_converter() {
        dec_ref_map_key_values(m, m_const2bv);
        dec_ref_map_key_values(m, m_rm_const2bv);
        dec_ref_map_key_values(m, m_uf2bvuf);
    }

    virtual void operator()(model_ref & md, unsigned goal_idx) {
        SASSERT(goal_idx == 0);
        model * new_model = alloc(model, m);
        obj_hashtable<func_decl> bits;
        convert(md.get(), new_model);
        md = new_model;
    }

    virtual void operator()(model_ref & md) {
        operator()(md, 0);
    }

    void display(std::ostream & out);

    virtual model_converter * translate(ast_translation & translator);

protected:
    fpa2bv_model_converter(ast_manager & m) : m(m) { }

    void convert(model * bv_mdl, model * float_mdl);
    expr_ref convert_bv2fp(sort * s, expr * sgn, expr * exp, expr * sig) const;
    expr_ref convert_bv2fp(model * bv_mdl, sort * s, expr * bv) const;
    expr_ref convert_bv2rm(expr * eval_v) const;
    expr_ref convert_bv2rm(model * bv_mdl, func_decl * var, expr * val) const;
};


model_converter * mk_fpa2bv_model_converter(ast_manager & m,
                                            obj_map<func_decl, expr*> const & const2bv,
                                            obj_map<func_decl, expr*> const & rm_const2bv,
                                            obj_map<func_decl, func_decl*> const & uf2bvuf);

#endif