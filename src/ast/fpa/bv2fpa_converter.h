/*++
    Copyright (c) 2016 Microsoft Corporation

Module Name:

    bv2fpa_converter.h

Abstract:

    Model conversion for fpa2bv_converter

Author:

    Christoph (cwinter) 2016-10-15

Notes:

--*/
#ifndef BV2FPA_CONVERTER_H_
#define BV2FPA_CONVERTER_H_

#include"fpa_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"th_rewriter.h"
#include"model_core.h"
#include"fpa2bv_converter.h"


class bv2fpa_converter {
    ast_manager & m;
    fpa_util      m_fpa_util;
    bv_util       m_bv_util;
    th_rewriter   m_th_rw;

    obj_map<func_decl, expr*>   m_const2bv;
    obj_map<func_decl, expr*>   m_rm_const2bv;
    obj_map<func_decl, func_decl*>  m_uf2bvuf;
    obj_map<func_decl, std::pair<app*, app*> > m_specials;

public:
    bv2fpa_converter(ast_manager & m);
    bv2fpa_converter(ast_manager & m, fpa2bv_converter & conv);
    virtual ~bv2fpa_converter();

    void display(std::ostream & out);
    bv2fpa_converter * translate(ast_translation & translator);

    expr_ref convert_bv2fp(sort * s, expr * sgn, expr * exp, expr * sig);
    expr_ref convert_bv2fp(model_core * mc, sort * s, app * bv);
    expr_ref convert_bv2rm(expr * eval_v);
    expr_ref convert_bv2rm(model_core * mc, app * val);

    void convert(model_core * mc, model_core * float_mdl);
    void convert_consts(model_core * mc, model_core * target_model, obj_hashtable<func_decl> & seen);
    void convert_rm_consts(model_core * mc, model_core * target_model, obj_hashtable<func_decl> & seen);
    void convert_min_max_specials(model_core * mc, model_core * target_model, obj_hashtable<func_decl> & seen);
    void convert_uf2bvuf(model_core * mc, model_core * target_model, obj_hashtable<func_decl> & seen);

    func_interp * convert_func_interp(model_core * mc, func_decl * f, func_decl * bv_f);
    expr_ref rebuild_floats(model_core * mc, sort * s, app * e);

    class array_model {
    public:
        func_decl * new_float_fd;
        func_interp * new_float_fi;
        func_decl * bv_fd;
        expr_ref result;
        array_model(ast_manager & m) : new_float_fd(0), new_float_fi(0), bv_fd(0), result(m) {}
    };

    array_model convert_array_func_interp(model_core * mc, func_decl * f, func_decl * bv_f);
};

#endif