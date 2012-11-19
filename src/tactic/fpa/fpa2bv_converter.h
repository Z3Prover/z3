/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa2bv_converter.h

Abstract:

    Conversion routines for Floating Point -> Bit-Vector

Author:

    Christoph (cwinter) 2012-02-09

Notes:

--*/
#ifndef _FPA2BV_CONVERTER_
#define _FPA2BV_CONVERTER_

#include"ast.h"
#include"obj_hashtable.h"
#include"ref_util.h"
#include"float_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"model_converter.h"
#include"basic_simplifier_plugin.h"

typedef enum { BV_RM_TIES_TO_AWAY=0, BV_RM_TIES_TO_EVEN=1, BV_RM_TO_NEGATIVE=2, BV_RM_TO_POSITIVE=3, BV_RM_TO_ZERO=4 } BV_RM_VAL;

class fpa2bv_model_converter;

class fpa2bv_converter {
    ast_manager              & m;
    basic_simplifier_plugin    m_simp;
    float_util                 m_util;
	mpf_manager				 & m_mpf_manager;
	unsynch_mpz_manager      & m_mpz_manager;
    bv_util                    m_bv_util;    
    float_decl_plugin        * m_plugin;

    obj_map<func_decl, expr*>  m_const2bv;
	obj_map<func_decl, expr*>  m_rm_const2bv;
    
public:
    fpa2bv_converter(ast_manager & m);    
    ~fpa2bv_converter();

    float_util & fu() { return m_util; }

    bool is_float(sort * s) { return m_util.is_float(s); }
    bool is_float(expr * e) { return is_app(e) && m_util.is_float(to_app(e)->get_decl()->get_range()); }
    bool is_float_family(func_decl * f) { return f->get_family_id() == m_util.get_family_id(); }
	bool is_rm_sort(sort * s) { return m_util.is_rm(s); }

    void mk_triple(expr * sign, expr * significand, expr * exponent, expr_ref & result) {
		SASSERT(m_bv_util.is_bv(sign) && m_bv_util.get_bv_size(sign) == 1);
		SASSERT(m_bv_util.is_bv(significand));
		SASSERT(m_bv_util.is_bv(exponent));
        result = m.mk_app(m_util.get_family_id(), OP_TO_FLOAT, sign, significand, exponent);
    }

    void mk_eq(expr * a, expr * b, expr_ref & result);
    void mk_ite(expr * c, expr * t, expr * f, expr_ref & result);

	void mk_rounding_mode(func_decl * f, expr_ref & result);
    void mk_value(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_const(func_decl * f, expr_ref & result);
	void mk_rm_const(func_decl * f, expr_ref & result);

    void mk_plus_inf(func_decl * f, expr_ref & result);
    void mk_minus_inf(func_decl * f, expr_ref & result);
    void mk_nan(func_decl * f, expr_ref & result);
    void mk_nzero(func_decl *f, expr_ref & result);
    void mk_pzero(func_decl *f, expr_ref & result);

    void mk_add(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_sub(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_uminus(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_mul(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_div(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_remainder(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_abs(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_min(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_max(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_fusedma(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_sqrt(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_round_to_integral(func_decl * f, unsigned num, expr * const * args, expr_ref & result);

    void mk_float_eq(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_lt(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_gt(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_le(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_ge(func_decl * f, unsigned num, expr * const * args, expr_ref & result);

    void mk_is_zero(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_nzero(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_pzero(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_sign_minus(func_decl * f, unsigned num, expr * const * args, expr_ref & result);

    void mk_to_float(func_decl * f, unsigned num, expr * const * args, expr_ref & result);

    fpa2bv_model_converter * mk_model_converter();

    void dbg_decouple(const char * prefix, expr_ref & e);
    expr_ref_vector extra_assertions;

protected:
    void split(expr * e, expr * & sgn, expr * & sig, expr * & exp) const;

    void mk_is_nan(expr * e, expr_ref & result);
    void mk_is_inf(expr * e, expr_ref & result);
    void mk_is_pinf(expr * e, expr_ref & result);
    void mk_is_ninf(expr * e, expr_ref & result);
    void mk_is_pos(expr * e, expr_ref & result);
    void mk_is_neg(expr * e, expr_ref & result);
    void mk_is_zero(expr * e, expr_ref & result);
    void mk_is_nzero(expr * e, expr_ref & result);
    void mk_is_pzero(expr * e, expr_ref & result);
    void mk_is_denormal(expr * e, expr_ref & result);
    void mk_is_normal(expr * e, expr_ref & result);

	void mk_is_rm(expr * e, BV_RM_VAL rm, expr_ref & result);

    void mk_top_exp(unsigned sz, expr_ref & result);
    void mk_bot_exp(unsigned sz, expr_ref & result);
	void mk_min_exp(unsigned ebits, expr_ref & result);
    void mk_max_exp(unsigned ebits, expr_ref & result);

    void mk_leading_zeros(expr * e, unsigned max_bits, expr_ref & result);

    void mk_bias(expr * e, expr_ref & result);
    void mk_unbias(expr * e, expr_ref & result);

    void unpack(expr * e, expr_ref & sgn, expr_ref & sig, expr_ref & exp, bool normalize);
    void round(sort * s, expr_ref & rm, expr_ref & sgn, expr_ref & sig, expr_ref & exp, expr_ref & result);	    

    void add_core(unsigned sbits, unsigned ebits, expr_ref & rm,
        expr_ref & c_sgn, expr_ref & c_sig, expr_ref & c_exp, expr_ref & d_sgn, expr_ref & d_sig, expr_ref & d_exp,
        expr_ref & res_sgn, expr_ref & res_sig, expr_ref & res_exp);
};


class fpa2bv_model_converter : public model_converter {
    ast_manager               & m;
    obj_map<func_decl, expr*>   m_const2bv;
	obj_map<func_decl, expr*>   m_rm_const2bv;

public:
    fpa2bv_model_converter(ast_manager & m, obj_map<func_decl, expr*> & const2bv,
		                                    obj_map<func_decl, expr*> & rm_const2bv) : 
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
      }

    virtual ~fpa2bv_model_converter() {
        dec_ref_map_key_values(m, m_const2bv);
		dec_ref_map_key_values(m, m_rm_const2bv);
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
};

#endif
