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

#include"th_rewriter.h"
#include"fpa2bv_converter.h"
#include"model_converter.h"

class fpa2bv_model_converter : public model_converter {
    ast_manager & m;
    fpa_util      m_fpa_util;
    bv_util       m_bv_util;
    th_rewriter   m_th_rw;
    
    obj_map<func_decl, expr*>   m_const2bv;
    obj_map<func_decl, expr*>   m_rm_const2bv;
    obj_map<func_decl, func_decl*>  m_uf2bvuf;
    obj_map<func_decl, std::pair<app*, app*> > m_specials;

public:
    fpa2bv_model_converter(ast_manager & m, fpa2bv_converter const & conv) : 
        m(m),
        m_fpa_util(m),
        m_bv_util(m),
        m_th_rw(m) {
        for (obj_map<func_decl, expr*>::iterator it = conv.m_const2bv.begin();
             it != conv.m_const2bv.end();
             it++)
        {
            m_const2bv.insert(it->m_key, it->m_value);
            m.inc_ref(it->m_key);
            m.inc_ref(it->m_value);
        }
        for (obj_map<func_decl, expr*>::iterator it = conv.m_rm_const2bv.begin();
             it != conv.m_rm_const2bv.end();
             it++)
        {
            m_rm_const2bv.insert(it->m_key, it->m_value);
            m.inc_ref(it->m_key);
            m.inc_ref(it->m_value);
        }
        for (obj_map<func_decl, func_decl*>::iterator it = conv.m_uf2bvuf.begin();
             it != conv.m_uf2bvuf.end();
             it++)
        {
            m_uf2bvuf.insert(it->m_key, it->m_value);
            m.inc_ref(it->m_key);
            m.inc_ref(it->m_value);
        }
        for (obj_map<func_decl, std::pair<app*, app*> >::iterator it = conv.m_min_max_specials.begin();
             it != conv.m_min_max_specials.end();
             it++) {
            m_specials.insert(it->m_key, it->m_value);
            m.inc_ref(it->m_key);
            m.inc_ref(it->m_value.first);
            m.inc_ref(it->m_value.second);
        }
    }

    virtual ~fpa2bv_model_converter() {
        dec_ref_map_key_values(m, m_const2bv);
        dec_ref_map_key_values(m, m_rm_const2bv);
        dec_ref_map_key_values(m, m_uf2bvuf);
        for (obj_map<func_decl, std::pair<app*, app*> >::iterator it = m_specials.begin();
             it != m_specials.end();
             it++) {
            m.dec_ref(it->m_key);
            m.dec_ref(it->m_value.first);
            m.dec_ref(it->m_value.second);
        }
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
    fpa2bv_model_converter(ast_manager & m) : 
        m(m),
        m_fpa_util(m),
        m_bv_util(m),
        m_th_rw(m) {}

    void convert(model * bv_mdl, model * float_mdl);
    expr_ref convert_bv2fp(sort * s, expr * sgn, expr * exp, expr * sig);
    expr_ref convert_bv2fp(model * bv_mdl, sort * s, expr * bv);
    expr_ref convert_bv2rm(expr * eval_v);
    expr_ref convert_bv2rm(model * bv_mdl, expr * val);

    func_interp * convert_func_interp(func_decl * f, func_decl * bv_f, model * bv_mdl);
    expr_ref rebuild_floats(model * bv_mdl, sort * s, expr * e);
        
    class array_model {
    public:
        func_decl * new_float_fd;
        func_interp * new_float_fi;
        func_decl * bv_fd;
        expr_ref result;
        array_model(ast_manager & m) : new_float_fd(0), new_float_fi(0), bv_fd(0), result(m) {}
    };

    array_model convert_array_func_interp(func_decl * f, func_decl * bv_f, model * bv_mdl);
};


model_converter * mk_fpa2bv_model_converter(ast_manager & m, fpa2bv_converter const & conv);

#endif
