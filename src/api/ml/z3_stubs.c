/* File generated from z3.idl */

#include <stddef.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
#ifdef Custom_tag
#include <caml/custom.h>
#include <caml/bigarray.h>
#endif
#include <caml/camlidlruntime.h>


#include "z3.h"

#define xstr(s) str(s)
#define str(s) #s
#pragma warning(disable:4090)

void check_error_code (Z3_context c);

Z3_context last_ctx;


  
  value caml_final_register (value f, value v);

  void register_finalizer(value** closure, char* name, Z3_context ctx, value v)
  {
    if (*closure == NULL) {
      *closure = caml_named_value(name);
      if (*closure == NULL) {
        Z3_set_error(ctx, Z3_INTERNAL_FATAL);
        return;
      }
    }
    caml_final_register(**closure, v);
  }

  value c2ml_Z3_context (Z3_context* c)
  {
    static value* finalize_Z3_context_closure = NULL;
    value v;
    v = caml_alloc_small(1, Abstract_tag);
    Field(v, 0) = (value) *c;
    register_finalizer(&finalize_Z3_context_closure, "finalize_Z3_context",
                       (Z3_context) *c, v);
    return v;
  }

  void ml2c_Z3_context (value v, Z3_context* c)
  {
    *c = (Z3_context) Field(v, 0);
    last_ctx = *c;
  }

  value finalize_Z3_context (value v)
  {
    Z3_context c;
    c = (Z3_context) Field(v, 0);
    Z3_del_context(c);
    return Val_unit;
  }
  
#define camlidl_ml2c_z3_Z3_context(v,c,ctx) ml2c_Z3_context(v,c)

#define camlidl_c2ml_z3_Z3_context(c,ctx) c2ml_Z3_context(c)

void camlidl_ml2c_z3_Z3_symbol(value _v1, Z3_symbol * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_symbol *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_symbol(Z3_symbol * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_symbol) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_symbol *) Bp_val(_v1)) = *_c2;
  return _v1;
}


typedef struct _Z3_ast_context {
  Z3_ast ast;
  Z3_context ctx;
} Z3_ast_context;

void ml2c_Z3_ast (value v, Z3_ast* c)
{
  *c = ((Z3_ast_context*) Data_custom_val(v))->ast;
}

static int compare_Z3_ast (value v1, value v2)
{
  Z3_ast_context* ac1;
  Z3_ast_context* ac2;
  unsigned int id1, id2;
  ac1 = Data_custom_val(v1);
  ac2 = Data_custom_val(v2);
  id1 = Z3_get_ast_id(ac1->ctx, ac1->ast);
  check_error_code(ac1->ctx);
  id2 = Z3_get_ast_id(ac2->ctx, ac2->ast);
  check_error_code(ac2->ctx);
  return id2 - id1;
}

static intnat hash_Z3_ast (value v)
{
  Z3_ast_context* ac;
  unsigned int hash;
  ac = Data_custom_val(v);
  hash = Z3_get_ast_hash(ac->ctx, ac->ast);
  check_error_code(ac->ctx);
  return hash;
}


  value finalize_Z3_ast (value v)
  {
    Z3_ast_context* ac;
    ac = Data_custom_val(v);
    Z3_dec_ref(ac->ctx, ac->ast);
    check_error_code(ac->ctx);
    return Val_unit;
  }

  static struct custom_operations cops_Z3_ast = {
    NULL,
    custom_finalize_default,
    compare_Z3_ast,
    hash_Z3_ast,
    custom_serialize_default,
    custom_deserialize_default
  };

  value c2ml_Z3_ast (Z3_ast* c)
  {
    static value* finalize_Z3_ast_closure = NULL;
    value v;
    Z3_ast_context* ac;
    check_error_code(last_ctx);
    v = caml_alloc_custom(&cops_Z3_ast, sizeof(Z3_ast_context), 0, 1);
    ac = Data_custom_val(v);
    ac->ast = *c;
    ac->ctx = last_ctx;
    register_finalizer(&finalize_Z3_ast_closure, "finalize_Z3_ast",
                       (Z3_context) *c, v);
    Z3_inc_ref(last_ctx, *c);
    return v;
  }
  
#define camlidl_ml2c_z3_Z3_ast(v,c,ctx) ml2c_Z3_ast(v,c)

#define camlidl_c2ml_z3_Z3_ast(c,ctx) c2ml_Z3_ast(c)

#define DEFINE_SUBAST_OPS(T) void ml2c_ ## T (value v, T * a) { ml2c_Z3_ast(v, (Z3_ast*) a); } value c2ml_ ## T (T * a) { return c2ml_Z3_ast((Z3_ast*) a); } 
DEFINE_SUBAST_OPS(Z3_sort)
#define camlidl_ml2c_z3_Z3_sort(v,c,ctx) ml2c_Z3_sort(v,c)

#define camlidl_c2ml_z3_Z3_sort(c,ctx) c2ml_Z3_sort(c)

DEFINE_SUBAST_OPS(Z3_func_decl)
#define camlidl_ml2c_z3_Z3_func_decl(v,c,ctx) ml2c_Z3_func_decl(v,c)

#define camlidl_c2ml_z3_Z3_func_decl(c,ctx) c2ml_Z3_func_decl(c)

DEFINE_SUBAST_OPS(Z3_app)
#define camlidl_ml2c_z3_Z3_app(v,c,ctx) ml2c_Z3_app(v,c)

#define camlidl_c2ml_z3_Z3_app(c,ctx) c2ml_Z3_app(c)

DEFINE_SUBAST_OPS(Z3_pattern)
#define camlidl_ml2c_z3_Z3_pattern(v,c,ctx) ml2c_Z3_pattern(v,c)

#define camlidl_c2ml_z3_Z3_pattern(c,ctx) c2ml_Z3_pattern(c)

#define DEFINE_RC_OPS(T) value c2ml_ ## T (T * c) { static value* finalize_ ## T ## _closure = NULL; value v; check_error_code(last_ctx); v = caml_alloc_small(2, Abstract_tag); Field(v, 0) = (value) *c; Field(v, 1) = (value) last_ctx; register_finalizer(&finalize_ ## T ## _closure, xstr(finalize_ ## T), (Z3_context) *c, v); T ## _inc_ref(last_ctx, *c); return v; } void ml2c_ ## T (value v, T * c) { *c = (T) Field(v, 0); } value finalize_ ## T (value v) { Z3_context c; c = (Z3_context) Field(v, 1); T ## _dec_ref(c, (T) Field(v, 0)); check_error_code(c); return Val_unit; } 
DEFINE_RC_OPS(Z3_params)
#define camlidl_ml2c_z3_Z3_params(v,c,ctx) ml2c_Z3_params(v,c)

#define camlidl_c2ml_z3_Z3_params(c,ctx) c2ml_Z3_params(c)

DEFINE_RC_OPS(Z3_param_descrs)
#define camlidl_ml2c_z3_Z3_param_descrs(v,c,ctx) ml2c_Z3_param_descrs(v,c)

#define camlidl_c2ml_z3_Z3_param_descrs(c,ctx) c2ml_Z3_param_descrs(c)

DEFINE_RC_OPS(Z3_model)
#define camlidl_ml2c_z3_Z3_model(v,c,ctx) ml2c_Z3_model(v,c)

#define camlidl_c2ml_z3_Z3_model(c,ctx) c2ml_Z3_model(c)

DEFINE_RC_OPS(Z3_func_interp)
#define camlidl_ml2c_z3_Z3_func_interp(v,c,ctx) ml2c_Z3_func_interp(v,c)

#define camlidl_c2ml_z3_Z3_func_interp(c,ctx) c2ml_Z3_func_interp(c)

DEFINE_RC_OPS(Z3_func_entry)
#define camlidl_ml2c_z3_Z3_func_entry(v,c,ctx) ml2c_Z3_func_entry(v,c)

#define camlidl_c2ml_z3_Z3_func_entry(c,ctx) c2ml_Z3_func_entry(c)

DEFINE_RC_OPS(Z3_fixedpoint)
#define camlidl_ml2c_z3_Z3_fixedpoint(v,c,ctx) ml2c_Z3_fixedpoint(v,c)

#define camlidl_c2ml_z3_Z3_fixedpoint(c,ctx) c2ml_Z3_fixedpoint(c)

DEFINE_RC_OPS(Z3_ast_vector)
#define camlidl_ml2c_z3_Z3_ast_vector(v,c,ctx) ml2c_Z3_ast_vector(v,c)

#define camlidl_c2ml_z3_Z3_ast_vector(c,ctx) c2ml_Z3_ast_vector(c)

DEFINE_RC_OPS(Z3_ast_map)
#define camlidl_ml2c_z3_Z3_ast_map(v,c,ctx) ml2c_Z3_ast_map(v,c)

#define camlidl_c2ml_z3_Z3_ast_map(c,ctx) c2ml_Z3_ast_map(c)

DEFINE_RC_OPS(Z3_goal)
#define camlidl_ml2c_z3_Z3_goal(v,c,ctx) ml2c_Z3_goal(v,c)

#define camlidl_c2ml_z3_Z3_goal(c,ctx) c2ml_Z3_goal(c)

DEFINE_RC_OPS(Z3_tactic)
#define camlidl_ml2c_z3_Z3_tactic(v,c,ctx) ml2c_Z3_tactic(v,c)

#define camlidl_c2ml_z3_Z3_tactic(c,ctx) c2ml_Z3_tactic(c)

DEFINE_RC_OPS(Z3_probe)
#define camlidl_ml2c_z3_Z3_probe(v,c,ctx) ml2c_Z3_probe(v,c)

#define camlidl_c2ml_z3_Z3_probe(c,ctx) c2ml_Z3_probe(c)

DEFINE_RC_OPS(Z3_apply_result)
#define camlidl_ml2c_z3_Z3_apply_result(v,c,ctx) ml2c_Z3_apply_result(v,c)

#define camlidl_c2ml_z3_Z3_apply_result(c,ctx) c2ml_Z3_apply_result(c)

DEFINE_RC_OPS(Z3_solver)
#define camlidl_ml2c_z3_Z3_solver(v,c,ctx) ml2c_Z3_solver(v,c)

#define camlidl_c2ml_z3_Z3_solver(c,ctx) c2ml_Z3_solver(c)

DEFINE_RC_OPS(Z3_stats)
#define camlidl_ml2c_z3_Z3_stats(v,c,ctx) ml2c_Z3_stats(v,c)

#define camlidl_c2ml_z3_Z3_stats(c,ctx) c2ml_Z3_stats(c)

#define DEFINE_OPT_OPS(T) void ml2c_ ## T ## _opt (value v, T* c) { struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL }; camlidl_ctx _ctx = &_ctxs; if (v != Val_int(0)) { camlidl_ml2c_z3_ ## T(Field(v, 0), c, _ctx); } else { *c = NULL; } } value c2ml_ ## T ## _opt (T* c) { struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL }; camlidl_ctx _ctx = &_ctxs; value v; value a; if (*c) { a = camlidl_c2ml_z3_ ## T(c, _ctx); Begin_root(a) v = caml_alloc_small(1, 0); Field(v, 0) = a; End_roots(); } else { v = Val_int(0); } return v; }

DEFINE_OPT_OPS(Z3_ast)
#define camlidl_ml2c_z3_Z3_ast_opt(v,c,ctx) ml2c_Z3_ast_opt(v,c)

#define camlidl_c2ml_z3_Z3_ast_opt(c,ctx) c2ml_Z3_ast_opt(c)

DEFINE_OPT_OPS(Z3_sort)
#define camlidl_ml2c_z3_Z3_sort_opt(v,c,ctx) ml2c_Z3_sort_opt(v,c)

#define camlidl_c2ml_z3_Z3_sort_opt(c,ctx) c2ml_Z3_sort_opt(c)

DEFINE_OPT_OPS(Z3_func_interp)
#define camlidl_ml2c_z3_Z3_func_interp_opt(v,c,ctx) ml2c_Z3_func_interp_opt(v,c)

#define camlidl_c2ml_z3_Z3_func_interp_opt(c,ctx) c2ml_Z3_func_interp_opt(c)

void camlidl_ml2c_z3_Z3_constructor(value _v1, Z3_constructor * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_constructor *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_constructor(Z3_constructor * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_constructor) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_constructor *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_constructor_list(value _v1, Z3_constructor_list * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_constructor_list *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_constructor_list(Z3_constructor_list * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_constructor_list) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_constructor_list *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_string(value _v1, Z3_string * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_malloc_string(_v1, _ctx);
}

value camlidl_c2ml_z3_Z3_string(Z3_string * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = copy_string((*_c2));
  return _v1;
}

int camlidl_transl_table_z3_enum_1[3] = {
  Z3_L_FALSE,
  Z3_L_UNDEF,
  Z3_L_TRUE,
};

void camlidl_ml2c_z3_Z3_lbool(value _v1, Z3_lbool * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_1[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_lbool(Z3_lbool * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case Z3_L_FALSE: _v1 = Val_int(0); break;
  case Z3_L_UNDEF: _v1 = Val_int(1); break;
  case Z3_L_TRUE: _v1 = Val_int(2); break;
  default: invalid_argument("typedef Z3_lbool: bad enum  value");
  }
  return _v1;
}

int camlidl_transl_table_z3_enum_2[2] = {
  Z3_INT_SYMBOL,
  Z3_STRING_SYMBOL,
};

void camlidl_ml2c_z3_Z3_symbol_kind(value _v1, Z3_symbol_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_2[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_symbol_kind(Z3_symbol_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case Z3_INT_SYMBOL: _v1 = Val_int(0); break;
  case Z3_STRING_SYMBOL: _v1 = Val_int(1); break;
  default: invalid_argument("typedef Z3_symbol_kind: bad enum  value");
  }
  return _v1;
}

int camlidl_transl_table_z3_enum_3[7] = {
  Z3_PARAMETER_INT,
  Z3_PARAMETER_DOUBLE,
  Z3_PARAMETER_RATIONAL,
  Z3_PARAMETER_SYMBOL,
  Z3_PARAMETER_SORT,
  Z3_PARAMETER_AST,
  Z3_PARAMETER_FUNC_DECL,
};

void camlidl_ml2c_z3_Z3_parameter_kind(value _v1, Z3_parameter_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_3[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_parameter_kind(Z3_parameter_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3_enum_3, 7, "typedef Z3_parameter_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3_enum_4[10] = {
  Z3_UNINTERPRETED_SORT,
  Z3_BOOL_SORT,
  Z3_INT_SORT,
  Z3_REAL_SORT,
  Z3_BV_SORT,
  Z3_ARRAY_SORT,
  Z3_DATATYPE_SORT,
  Z3_RELATION_SORT,
  Z3_FINITE_DOMAIN_SORT,
  Z3_UNKNOWN_SORT,
};

void camlidl_ml2c_z3_Z3_sort_kind(value _v1, Z3_sort_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_4[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_sort_kind(Z3_sort_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3_enum_4, 10, "typedef Z3_sort_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3_enum_5[7] = {
  Z3_NUMERAL_AST,
  Z3_APP_AST,
  Z3_VAR_AST,
  Z3_QUANTIFIER_AST,
  Z3_SORT_AST,
  Z3_FUNC_DECL_AST,
  Z3_UNKNOWN_AST,
};

void camlidl_ml2c_z3_Z3_ast_kind(value _v1, Z3_ast_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_5[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_ast_kind(Z3_ast_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3_enum_5, 7, "typedef Z3_ast_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3_enum_6[152] = {
  Z3_OP_TRUE,
  Z3_OP_FALSE,
  Z3_OP_EQ,
  Z3_OP_DISTINCT,
  Z3_OP_ITE,
  Z3_OP_AND,
  Z3_OP_OR,
  Z3_OP_IFF,
  Z3_OP_XOR,
  Z3_OP_NOT,
  Z3_OP_IMPLIES,
  Z3_OP_OEQ,
  Z3_OP_ANUM,
  Z3_OP_AGNUM,
  Z3_OP_LE,
  Z3_OP_GE,
  Z3_OP_LT,
  Z3_OP_GT,
  Z3_OP_ADD,
  Z3_OP_SUB,
  Z3_OP_UMINUS,
  Z3_OP_MUL,
  Z3_OP_DIV,
  Z3_OP_IDIV,
  Z3_OP_REM,
  Z3_OP_MOD,
  Z3_OP_TO_REAL,
  Z3_OP_TO_INT,
  Z3_OP_IS_INT,
  Z3_OP_POWER,
  Z3_OP_STORE,
  Z3_OP_SELECT,
  Z3_OP_CONST_ARRAY,
  Z3_OP_ARRAY_MAP,
  Z3_OP_ARRAY_DEFAULT,
  Z3_OP_SET_UNION,
  Z3_OP_SET_INTERSECT,
  Z3_OP_SET_DIFFERENCE,
  Z3_OP_SET_COMPLEMENT,
  Z3_OP_SET_SUBSET,
  Z3_OP_AS_ARRAY,
  Z3_OP_BNUM,
  Z3_OP_BIT1,
  Z3_OP_BIT0,
  Z3_OP_BNEG,
  Z3_OP_BADD,
  Z3_OP_BSUB,
  Z3_OP_BMUL,
  Z3_OP_BSDIV,
  Z3_OP_BUDIV,
  Z3_OP_BSREM,
  Z3_OP_BUREM,
  Z3_OP_BSMOD,
  Z3_OP_BSDIV0,
  Z3_OP_BUDIV0,
  Z3_OP_BSREM0,
  Z3_OP_BUREM0,
  Z3_OP_BSMOD0,
  Z3_OP_ULEQ,
  Z3_OP_SLEQ,
  Z3_OP_UGEQ,
  Z3_OP_SGEQ,
  Z3_OP_ULT,
  Z3_OP_SLT,
  Z3_OP_UGT,
  Z3_OP_SGT,
  Z3_OP_BAND,
  Z3_OP_BOR,
  Z3_OP_BNOT,
  Z3_OP_BXOR,
  Z3_OP_BNAND,
  Z3_OP_BNOR,
  Z3_OP_BXNOR,
  Z3_OP_CONCAT,
  Z3_OP_SIGN_EXT,
  Z3_OP_ZERO_EXT,
  Z3_OP_EXTRACT,
  Z3_OP_REPEAT,
  Z3_OP_BREDOR,
  Z3_OP_BREDAND,
  Z3_OP_BCOMP,
  Z3_OP_BSHL,
  Z3_OP_BLSHR,
  Z3_OP_BASHR,
  Z3_OP_ROTATE_LEFT,
  Z3_OP_ROTATE_RIGHT,
  Z3_OP_EXT_ROTATE_LEFT,
  Z3_OP_EXT_ROTATE_RIGHT,
  Z3_OP_INT2BV,
  Z3_OP_BV2INT,
  Z3_OP_CARRY,
  Z3_OP_XOR3,
  Z3_OP_PR_UNDEF,
  Z3_OP_PR_TRUE,
  Z3_OP_PR_ASSERTED,
  Z3_OP_PR_GOAL,
  Z3_OP_PR_MODUS_PONENS,
  Z3_OP_PR_REFLEXIVITY,
  Z3_OP_PR_SYMMETRY,
  Z3_OP_PR_TRANSITIVITY,
  Z3_OP_PR_TRANSITIVITY_STAR,
  Z3_OP_PR_MONOTONICITY,
  Z3_OP_PR_QUANT_INTRO,
  Z3_OP_PR_DISTRIBUTIVITY,
  Z3_OP_PR_AND_ELIM,
  Z3_OP_PR_NOT_OR_ELIM,
  Z3_OP_PR_REWRITE,
  Z3_OP_PR_REWRITE_STAR,
  Z3_OP_PR_PULL_QUANT,
  Z3_OP_PR_PULL_QUANT_STAR,
  Z3_OP_PR_PUSH_QUANT,
  Z3_OP_PR_ELIM_UNUSED_VARS,
  Z3_OP_PR_DER,
  Z3_OP_PR_QUANT_INST,
  Z3_OP_PR_HYPOTHESIS,
  Z3_OP_PR_LEMMA,
  Z3_OP_PR_UNIT_RESOLUTION,
  Z3_OP_PR_IFF_TRUE,
  Z3_OP_PR_IFF_FALSE,
  Z3_OP_PR_COMMUTATIVITY,
  Z3_OP_PR_DEF_AXIOM,
  Z3_OP_PR_DEF_INTRO,
  Z3_OP_PR_APPLY_DEF,
  Z3_OP_PR_IFF_OEQ,
  Z3_OP_PR_NNF_POS,
  Z3_OP_PR_NNF_NEG,
  Z3_OP_PR_NNF_STAR,
  Z3_OP_PR_CNF_STAR,
  Z3_OP_PR_SKOLEMIZE,
  Z3_OP_PR_MODUS_PONENS_OEQ,
  Z3_OP_PR_TH_LEMMA,
  Z3_OP_PR_HYPER_RESOLVE,
  Z3_OP_RA_STORE,
  Z3_OP_RA_EMPTY,
  Z3_OP_RA_IS_EMPTY,
  Z3_OP_RA_JOIN,
  Z3_OP_RA_UNION,
  Z3_OP_RA_WIDEN,
  Z3_OP_RA_PROJECT,
  Z3_OP_RA_FILTER,
  Z3_OP_RA_NEGATION_FILTER,
  Z3_OP_RA_RENAME,
  Z3_OP_RA_COMPLEMENT,
  Z3_OP_RA_SELECT,
  Z3_OP_RA_CLONE,
  Z3_OP_FD_LT,
  Z3_OP_LABEL,
  Z3_OP_LABEL_LIT,
  Z3_OP_DT_CONSTRUCTOR,
  Z3_OP_DT_RECOGNISER,
  Z3_OP_DT_ACCESSOR,
  Z3_OP_UNINTERPRETED,
};

void camlidl_ml2c_z3_Z3_decl_kind(value _v1, Z3_decl_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_6[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_decl_kind(Z3_decl_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3_enum_6, 152, "typedef Z3_decl_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3_enum_7[7] = {
  Z3_PK_UINT,
  Z3_PK_BOOL,
  Z3_PK_DOUBLE,
  Z3_PK_SYMBOL,
  Z3_PK_STRING,
  Z3_PK_OTHER,
  Z3_PK_INVALID,
};

void camlidl_ml2c_z3_Z3_param_kind(value _v1, Z3_param_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_7[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_param_kind(Z3_param_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3_enum_7, 7, "typedef Z3_param_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3_enum_8[4] = {
  Z3_PRINT_SMTLIB_FULL,
  Z3_PRINT_LOW_LEVEL,
  Z3_PRINT_SMTLIB_COMPLIANT,
  Z3_PRINT_SMTLIB2_COMPLIANT,
};

void camlidl_ml2c_z3_Z3_ast_print_mode(value _v1, Z3_ast_print_mode * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_8[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_ast_print_mode(Z3_ast_print_mode * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case Z3_PRINT_SMTLIB_FULL: _v1 = Val_int(0); break;
  case Z3_PRINT_LOW_LEVEL: _v1 = Val_int(1); break;
  case Z3_PRINT_SMTLIB_COMPLIANT: _v1 = Val_int(2); break;
  case Z3_PRINT_SMTLIB2_COMPLIANT: _v1 = Val_int(3); break;
  default: invalid_argument("typedef Z3_ast_print_mode: bad enum  value");
  }
  return _v1;
}

int camlidl_transl_table_z3_enum_9[13] = {
  Z3_OK,
  Z3_SORT_ERROR,
  Z3_IOB,
  Z3_INVALID_ARG,
  Z3_PARSER_ERROR,
  Z3_NO_PARSER,
  Z3_INVALID_PATTERN,
  Z3_MEMOUT_FAIL,
  Z3_FILE_ACCESS_ERROR,
  Z3_INTERNAL_FATAL,
  Z3_INVALID_USAGE,
  Z3_DEC_REF_ERROR,
  Z3_EXCEPTION,
};

void camlidl_ml2c_z3_Z3_error_code(value _v1, Z3_error_code * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_9[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_error_code(Z3_error_code * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3_enum_9, 13, "typedef Z3_error_code: bad enum  value");
  return _v1;
}


value camlidl_c2ml_z3_Z3_error_code(Z3_error_code * _c2, camlidl_ctx _ctx);


void check_error_code (Z3_context c)
{
  static struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  value* exn_tag = NULL;
  value ctx_err[2];
  Z3_error_code e;
  e = Z3_get_error_code(c);
  if (e != Z3_OK) {
    ctx_err[0] = c2ml_Z3_context(&c);
    ctx_err[1] = camlidl_c2ml_z3_Z3_error_code(&e, &_ctxs);
    exn_tag = caml_named_value("Z3.Error");
    if (*exn_tag == 0) {
      fprintf(stderr, "Z3.Error not found");
      exit(1);
    }
    caml_raise_with_args(*exn_tag, 2, ctx_err);
  }
}


void* error_handler_static = NULL;

int camlidl_transl_table_z3_enum_10[4] = {
  Z3_GOAL_PRECISE,
  Z3_GOAL_UNDER,
  Z3_GOAL_OVER,
  Z3_GOAL_UNDER_OVER,
};

void camlidl_ml2c_z3_Z3_goal_prec(value _v1, Z3_goal_prec * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_10[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_goal_prec(Z3_goal_prec * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case Z3_GOAL_PRECISE: _v1 = Val_int(0); break;
  case Z3_GOAL_UNDER: _v1 = Val_int(1); break;
  case Z3_GOAL_OVER: _v1 = Val_int(2); break;
  case Z3_GOAL_UNDER_OVER: _v1 = Val_int(3); break;
  default: invalid_argument("typedef Z3_goal_prec: bad enum  value");
  }
  return _v1;
}


value caml_z3_mk_context(value key_val_list)
{
  CAMLparam1( key_val_list );
  CAMLlocal4( item, vkey, vval, _vres );
  char * ckey;
  char * cval;
  Z3_config cfg;
  Z3_context _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;

  cfg = Z3_mk_config();

  while (key_val_list != Val_emptylist)
  {
    item = Field(key_val_list, 0);
    vkey = Field(item, 0);
    vval = Field(item, 1);
    ckey = camlidl_malloc_string(vkey, _ctx);
    cval = camlidl_malloc_string(vval, _ctx);
    Z3_set_param_value(cfg, ckey, cval);
    key_val_list = Field(key_val_list, 1);
  }

  _res = Z3_mk_context_rc(cfg);
  Z3_del_config(cfg);
  _vres = camlidl_c2ml_z3_Z3_context(&_res, _ctx);
  camlidl_free(_ctx);
  Z3_set_error_handler(_res, error_handler_static);
  CAMLreturn(_vres);
}

value camlidl_z3_Z3_update_param_value(
	value _v_c,
	value _v_param_id,
	value _v_param_value)
{
  Z3_context c; /*in*/
  Z3_string param_id; /*in*/
  Z3_string param_value; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_param_id, &param_id, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_param_value, &param_value, _ctx);
  Z3_update_param_value(c, param_id, param_value);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_get_param_value(
	value _v_c,
	value _v_param_id)
{
  Z3_context c; /*in*/
  Z3_string param_id; /*in*/
  Z3_string *param_value; /*out*/
  Z3_string _c1;
  value _v2;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_param_id, &param_id, _ctx);
  param_value = &_c1;
  Z3_get_param_value(c, param_id, param_value);
  if (param_value == NULL) {
    _vres = Val_int(0);
  } else {
    _v2 = camlidl_c2ml_z3_Z3_string(&*param_value, _ctx);
    Begin_root(_v2)
      _vres = camlidl_alloc_small(1, 0);
      Field(_vres, 0) = _v2;
    End_roots();
  }
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_interrupt(
	value _v_c)
{
  Z3_context c; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  Z3_interrupt(c);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_mk_params(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_params _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_params(c);
  _vres = camlidl_c2ml_z3_Z3_params(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_params_set_bool(
	value _v_c,
	value _v_p,
	value _v_k,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_params p; /*in*/
  Z3_symbol k; /*in*/
  int v; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_params(_v_p, &p, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_k, &k, _ctx);
  v = Int_val(_v_v);
  Z3_params_set_bool(c, p, k, v);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_params_set_uint(
	value _v_c,
	value _v_p,
	value _v_k,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_params p; /*in*/
  Z3_symbol k; /*in*/
  unsigned int v; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_params(_v_p, &p, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_k, &k, _ctx);
  v = Int_val(_v_v);
  Z3_params_set_uint(c, p, k, v);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_params_set_double(
	value _v_c,
	value _v_p,
	value _v_k,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_params p; /*in*/
  Z3_symbol k; /*in*/
  double v; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_params(_v_p, &p, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_k, &k, _ctx);
  v = Double_val(_v_v);
  Z3_params_set_double(c, p, k, v);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_params_set_symbol(
	value _v_c,
	value _v_p,
	value _v_k,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_params p; /*in*/
  Z3_symbol k; /*in*/
  Z3_symbol v; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_params(_v_p, &p, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_k, &k, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_v, &v, _ctx);
  Z3_params_set_symbol(c, p, k, v);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_params_to_string(
	value _v_c,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_params p; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_params(_v_p, &p, _ctx);
  _res = Z3_params_to_string(c, p);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_params_validate(
	value _v_c,
	value _v_p,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_params p; /*in*/
  Z3_param_descrs d; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_params(_v_p, &p, _ctx);
  camlidl_ml2c_z3_Z3_param_descrs(_v_d, &d, _ctx);
  Z3_params_validate(c, p, d);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_param_descrs_get_kind(
	value _v_c,
	value _v_p,
	value _v_n)
{
  Z3_context c; /*in*/
  Z3_param_descrs p; /*in*/
  Z3_symbol n; /*in*/
  Z3_param_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_param_descrs(_v_p, &p, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_n, &n, _ctx);
  _res = Z3_param_descrs_get_kind(c, p, n);
  _vres = camlidl_c2ml_z3_Z3_param_kind(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_param_descrs_size(
	value _v_c,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_param_descrs p; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_param_descrs(_v_p, &p, _ctx);
  _res = Z3_param_descrs_size(c, p);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_param_descrs_get_name(
	value _v_c,
	value _v_p,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_param_descrs p; /*in*/
  unsigned int i; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_param_descrs(_v_p, &p, _ctx);
  i = Int_val(_v_i);
  _res = Z3_param_descrs_get_name(c, p, i);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_param_descrs_to_string(
	value _v_c,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_param_descrs p; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_param_descrs(_v_p, &p, _ctx);
  _res = Z3_param_descrs_to_string(c, p);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_int_symbol(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  int i; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_mk_int_symbol(c, i);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_string_symbol(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_string s; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_s, &s, _ctx);
  _res = Z3_mk_string_symbol(c, s);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_uninterpreted_sort(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_mk_uninterpreted_sort(c, s);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bool_sort(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_bool_sort(c);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_int_sort(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_int_sort(c);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_real_sort(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_real_sort(c);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bv_sort(
	value _v_c,
	value _v_sz)
{
  Z3_context c; /*in*/
  unsigned int sz; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  sz = Int_val(_v_sz);
  _res = Z3_mk_bv_sort(c, sz);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_finite_domain_sort(
	value _v_c,
	value _v_name,
	value _v_size)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  __int64 size; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_name, &name, _ctx);
  size = Int64_val(_v_size);
  _res = Z3_mk_finite_domain_sort(c, name, size);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_array_sort(
	value _v_c,
	value _v_domain,
	value _v_range)
{
  Z3_context c; /*in*/
  Z3_sort domain; /*in*/
  Z3_sort range; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_domain, &domain, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_range, &range, _ctx);
  _res = Z3_mk_array_sort(c, domain, range);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_tuple_sort(
	value _v_c,
	value _v_mk_tuple_name,
	value _v_field_names,
	value _v_field_sorts)
{
  Z3_context c; /*in*/
  Z3_symbol mk_tuple_name; /*in*/
  unsigned int num_fields; /*in*/
  Z3_symbol const *field_names; /*in*/
  Z3_sort const *field_sorts; /*in*/
  Z3_func_decl *mk_tuple_decl; /*out*/
  Z3_func_decl *proj_decl; /*out*/
  Z3_sort _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  Z3_func_decl _c7;
  mlsize_t _c8;
  value _v9;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_mk_tuple_name, &mk_tuple_name, _ctx);
  _c1 = Wosize_val(_v_field_names);
  field_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_field_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &field_names[_c2], _ctx);
  }
  num_fields = _c1;
  _c4 = Wosize_val(_v_field_sorts);
  field_sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_field_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &field_sorts[_c5], _ctx);
  }
  num_fields = _c4;
  mk_tuple_decl = &_c7;
  proj_decl = camlidl_malloc(num_fields * sizeof(Z3_func_decl ), _ctx);
  _res = Z3_mk_tuple_sort(c, mk_tuple_name, num_fields, field_names, field_sorts, mk_tuple_decl, proj_decl);
  Begin_roots_block(_vres, 3)
    _vres[0] = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
    _vres[1] = camlidl_c2ml_z3_Z3_func_decl(&*mk_tuple_decl, _ctx);
    _vres[2] = camlidl_alloc(num_fields, 0);
    Begin_root(_vres[2])
      for (_c8 = 0; _c8 < num_fields; _c8++) {
        _v9 = camlidl_c2ml_z3_Z3_func_decl(&proj_decl[_c8], _ctx);
        modify(&Field(_vres[2], _c8), _v9);
      }
    End_roots()
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vresult;
}

value camlidl_z3_Z3_mk_enumeration_sort(
	value _v_c,
	value _v_name,
	value _v_enum_names)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  unsigned int n; /*in*/
  Z3_symbol const *enum_names; /*in*/
  Z3_func_decl *enum_consts; /*out*/
  Z3_func_decl *enum_testers; /*out*/
  Z3_sort _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  value _v5;
  mlsize_t _c6;
  value _v7;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_name, &name, _ctx);
  _c1 = Wosize_val(_v_enum_names);
  enum_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_enum_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &enum_names[_c2], _ctx);
  }
  n = _c1;
  enum_consts = camlidl_malloc(n * sizeof(Z3_func_decl ), _ctx);
  enum_testers = camlidl_malloc(n * sizeof(Z3_func_decl ), _ctx);
  _res = Z3_mk_enumeration_sort(c, name, n, enum_names, enum_consts, enum_testers);
  Begin_roots_block(_vres, 3)
    _vres[0] = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
    _vres[1] = camlidl_alloc(n, 0);
    Begin_root(_vres[1])
      for (_c4 = 0; _c4 < n; _c4++) {
        _v5 = camlidl_c2ml_z3_Z3_func_decl(&enum_consts[_c4], _ctx);
        modify(&Field(_vres[1], _c4), _v5);
      }
    End_roots()
    _vres[2] = camlidl_alloc(n, 0);
    Begin_root(_vres[2])
      for (_c6 = 0; _c6 < n; _c6++) {
        _v7 = camlidl_c2ml_z3_Z3_func_decl(&enum_testers[_c6], _ctx);
        modify(&Field(_vres[2], _c6), _v7);
      }
    End_roots()
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vresult;
}

value camlidl_z3_Z3_mk_list_sort(
	value _v_c,
	value _v_name,
	value _v_elem_sort)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  Z3_sort elem_sort; /*in*/
  Z3_func_decl *nil_decl; /*out*/
  Z3_func_decl *is_nil_decl; /*out*/
  Z3_func_decl *cons_decl; /*out*/
  Z3_func_decl *is_cons_decl; /*out*/
  Z3_func_decl *head_decl; /*out*/
  Z3_func_decl *tail_decl; /*out*/
  Z3_sort _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  Z3_func_decl _c1;
  Z3_func_decl _c2;
  Z3_func_decl _c3;
  Z3_func_decl _c4;
  Z3_func_decl _c5;
  Z3_func_decl _c6;
  value _vresult;
  value _vres[7] = { 0, 0, 0, 0, 0, 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_name, &name, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_elem_sort, &elem_sort, _ctx);
  nil_decl = &_c1;
  is_nil_decl = &_c2;
  cons_decl = &_c3;
  is_cons_decl = &_c4;
  head_decl = &_c5;
  tail_decl = &_c6;
  _res = Z3_mk_list_sort(c, name, elem_sort, nil_decl, is_nil_decl, cons_decl, is_cons_decl, head_decl, tail_decl);
  Begin_roots_block(_vres, 7)
    _vres[0] = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
    _vres[1] = camlidl_c2ml_z3_Z3_func_decl(&*nil_decl, _ctx);
    _vres[2] = camlidl_c2ml_z3_Z3_func_decl(&*is_nil_decl, _ctx);
    _vres[3] = camlidl_c2ml_z3_Z3_func_decl(&*cons_decl, _ctx);
    _vres[4] = camlidl_c2ml_z3_Z3_func_decl(&*is_cons_decl, _ctx);
    _vres[5] = camlidl_c2ml_z3_Z3_func_decl(&*head_decl, _ctx);
    _vres[6] = camlidl_c2ml_z3_Z3_func_decl(&*tail_decl, _ctx);
    _vresult = camlidl_alloc_small(7, 0);
    { mlsize_t _c7;
      for (_c7 = 0; _c7 < 7; _c7++) Field(_vresult, _c7) = _vres[_c7];
    }
  End_roots()
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vresult;
}

value camlidl_z3_Z3_mk_constructor(
	value _v_c,
	value _v_name,
	value _v_recognizer,
	value _v_field_names,
	value _v_sorts,
	value _v_sort_refs)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  Z3_symbol recognizer; /*in*/
  unsigned int num_fields; /*in*/
  Z3_symbol const *field_names; /*in*/
  Z3_sort_opt const *sorts; /*in*/
  unsigned int *sort_refs; /*in*/
  Z3_constructor _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_name, &name, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_recognizer, &recognizer, _ctx);
  _c1 = Wosize_val(_v_field_names);
  field_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_field_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &field_names[_c2], _ctx);
  }
  num_fields = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort_opt const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort_opt(_v6, &sorts[_c5], _ctx);
  }
  num_fields = _c4;
  _c7 = Wosize_val(_v_sort_refs);
  sort_refs = camlidl_malloc(_c7 * sizeof(unsigned int ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_sort_refs, _c8);
    sort_refs[_c8] = Int_val(_v9);
  }
  num_fields = _c7;
  _res = Z3_mk_constructor(c, name, recognizer, num_fields, field_names, sorts, sort_refs);
  _vres = camlidl_c2ml_z3_Z3_constructor(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_constructor_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_constructor(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_del_constructor(
	value _v_c,
	value _v_constr)
{
  Z3_context c; /*in*/
  Z3_constructor constr; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_constructor(_v_constr, &constr, _ctx);
  Z3_del_constructor(c, constr);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_mk_datatype(
	value _v_c,
	value _v_name,
	value _v_constructors)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  unsigned int num_constructors; /*in*/
  Z3_constructor *constructors; /*in,out*/
  Z3_sort _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  value _v5;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_name, &name, _ctx);
  _c1 = Wosize_val(_v_constructors);
  constructors = camlidl_malloc(_c1 * sizeof(Z3_constructor ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_constructors, _c2);
    camlidl_ml2c_z3_Z3_constructor(_v3, &constructors[_c2], _ctx);
  }
  num_constructors = _c1;
  _res = Z3_mk_datatype(c, name, num_constructors, constructors);
  Begin_roots_block(_vres, 2)
    _vres[0] = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
    _vres[1] = camlidl_alloc(num_constructors, 0);
    Begin_root(_vres[1])
      for (_c4 = 0; _c4 < num_constructors; _c4++) {
        _v5 = camlidl_c2ml_z3_Z3_constructor(&constructors[_c4], _ctx);
        modify(&Field(_vres[1], _c4), _v5);
      }
    End_roots()
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vresult;
}

value camlidl_z3_Z3_mk_constructor_list(
	value _v_c,
	value _v_constructors)
{
  Z3_context c; /*in*/
  unsigned int num_constructors; /*in*/
  Z3_constructor const *constructors; /*in*/
  Z3_constructor_list _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_constructors);
  constructors = camlidl_malloc(_c1 * sizeof(Z3_constructor const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_constructors, _c2);
    camlidl_ml2c_z3_Z3_constructor(_v3, &constructors[_c2], _ctx);
  }
  num_constructors = _c1;
  _res = Z3_mk_constructor_list(c, num_constructors, constructors);
  _vres = camlidl_c2ml_z3_Z3_constructor_list(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_del_constructor_list(
	value _v_c,
	value _v_clist)
{
  Z3_context c; /*in*/
  Z3_constructor_list clist; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_constructor_list(_v_clist, &clist, _ctx);
  Z3_del_constructor_list(c, clist);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_mk_datatypes(
	value _v_c,
	value _v_sort_names,
	value _v_constructor_lists)
{
  Z3_context c; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol const *sort_names; /*in*/
  Z3_sort *sorts; /*out*/
  Z3_constructor_list *constructor_lists; /*in,out*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  value _v8;
  mlsize_t _c9;
  value _v10;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_constructor_lists);
  constructor_lists = camlidl_malloc(_c4 * sizeof(Z3_constructor_list ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_constructor_lists, _c5);
    camlidl_ml2c_z3_Z3_constructor_list(_v6, &constructor_lists[_c5], _ctx);
  }
  num_sorts = _c4;
  sorts = camlidl_malloc(num_sorts * sizeof(Z3_sort ), _ctx);
  Z3_mk_datatypes(c, num_sorts, sort_names, sorts, constructor_lists);
  Begin_roots_block(_vres, 2)
    _vres[0] = camlidl_alloc(num_sorts, 0);
    Begin_root(_vres[0])
      for (_c7 = 0; _c7 < num_sorts; _c7++) {
        _v8 = camlidl_c2ml_z3_Z3_sort(&sorts[_c7], _ctx);
        modify(&Field(_vres[0], _c7), _v8);
      }
    End_roots()
    _vres[1] = camlidl_alloc(num_sorts, 0);
    Begin_root(_vres[1])
      for (_c9 = 0; _c9 < num_sorts; _c9++) {
        _v10 = camlidl_c2ml_z3_Z3_constructor_list(&constructor_lists[_c9], _ctx);
        modify(&Field(_vres[1], _c9), _v10);
      }
    End_roots()
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vresult;
}

value camlidl_z3_Z3_query_constructor(
	value _v_c,
	value _v_constr,
	value _v_num_fields)
{
  Z3_context c; /*in*/
  Z3_constructor constr; /*in*/
  unsigned int num_fields; /*in*/
  Z3_func_decl *constructor; /*out*/
  Z3_func_decl *tester; /*out*/
  Z3_func_decl *accessors; /*out*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  Z3_func_decl _c1;
  Z3_func_decl _c2;
  mlsize_t _c3;
  value _v4;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_constructor(_v_constr, &constr, _ctx);
  num_fields = Int_val(_v_num_fields);
  constructor = &_c1;
  tester = &_c2;
  accessors = camlidl_malloc(num_fields * sizeof(Z3_func_decl ), _ctx);
  Z3_query_constructor(c, constr, num_fields, constructor, tester, accessors);
  Begin_roots_block(_vres, 3)
    _vres[0] = camlidl_c2ml_z3_Z3_func_decl(&*constructor, _ctx);
    _vres[1] = camlidl_c2ml_z3_Z3_func_decl(&*tester, _ctx);
    _vres[2] = camlidl_alloc(num_fields, 0);
    Begin_root(_vres[2])
      for (_c3 = 0; _c3 < num_fields; _c3++) {
        _v4 = camlidl_c2ml_z3_Z3_func_decl(&accessors[_c3], _ctx);
        modify(&Field(_vres[2], _c3), _v4);
      }
    End_roots()
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vresult;
}

value camlidl_z3_Z3_mk_func_decl(
	value _v_c,
	value _v_s,
	value _v_domain,
	value _v_range)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  unsigned int domain_size; /*in*/
  Z3_sort const *domain; /*in*/
  Z3_sort range; /*in*/
  Z3_func_decl _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_domain);
  domain = camlidl_malloc(_c1 * sizeof(Z3_sort const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_domain, _c2);
    camlidl_ml2c_z3_Z3_sort(_v3, &domain[_c2], _ctx);
  }
  domain_size = _c1;
  camlidl_ml2c_z3_Z3_sort(_v_range, &range, _ctx);
  _res = Z3_mk_func_decl(c, s, domain_size, domain, range);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_app(
	value _v_c,
	value _v_d,
	value _v_args)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_app(c, d, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_const(
	value _v_c,
	value _v_s,
	value _v_ty)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_const(c, s, ty);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_fresh_func_decl(
	value _v_c,
	value _v_prefix,
	value _v_domain,
	value _v_range)
{
  Z3_context c; /*in*/
  Z3_string prefix; /*in*/
  unsigned int domain_size; /*in*/
  Z3_sort const *domain; /*in*/
  Z3_sort range; /*in*/
  Z3_func_decl _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_prefix, &prefix, _ctx);
  _c1 = Wosize_val(_v_domain);
  domain = camlidl_malloc(_c1 * sizeof(Z3_sort const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_domain, _c2);
    camlidl_ml2c_z3_Z3_sort(_v3, &domain[_c2], _ctx);
  }
  domain_size = _c1;
  camlidl_ml2c_z3_Z3_sort(_v_range, &range, _ctx);
  _res = Z3_mk_fresh_func_decl(c, prefix, domain_size, domain, range);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_fresh_const(
	value _v_c,
	value _v_prefix,
	value _v_ty)
{
  Z3_context c; /*in*/
  Z3_string prefix; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_prefix, &prefix, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_fresh_const(c, prefix, ty);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_true(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_true(c);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_false(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_false(c);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_eq(
	value _v_c,
	value _v_l,
	value _v_r)
{
  Z3_context c; /*in*/
  Z3_ast l; /*in*/
  Z3_ast r; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_l, &l, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_r, &r, _ctx);
  _res = Z3_mk_eq(c, l, r);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_distinct(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_distinct(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_not(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_mk_not(c, a);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_ite(
	value _v_c,
	value _v_t1,
	value _v_t2,
	value _v_t3)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast t3; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t3, &t3, _ctx);
  _res = Z3_mk_ite(c, t1, t2, t3);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_iff(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_iff(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_implies(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_implies(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_xor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_xor(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_and(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_and(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_or(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_or(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_add(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_add(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_mul(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_mul(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_sub(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_sub(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_unary_minus(
	value _v_c,
	value _v_arg)
{
  Z3_context c; /*in*/
  Z3_ast arg; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg, &arg, _ctx);
  _res = Z3_mk_unary_minus(c, arg);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_div(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_div(c, arg1, arg2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_mod(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_mod(c, arg1, arg2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_rem(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_rem(c, arg1, arg2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_power(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_power(c, arg1, arg2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_lt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_lt(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_le(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_le(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_gt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_gt(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_ge(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_ge(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_int2real(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_int2real(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_real2int(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_real2int(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_is_int(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_is_int(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvnot(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvnot(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvredand(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvredand(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvredor(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvredor(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvand(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvand(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvor(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvxor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvxor(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvnand(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvnand(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvnor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvnor(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvxnor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvxnor(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvneg(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvneg(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvadd(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvadd(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvsub(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsub(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvmul(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvmul(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvudiv(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvudiv(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvsdiv(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsdiv(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvurem(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvurem(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvsrem(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsrem(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvsmod(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsmod(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvult(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvult(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvslt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvslt(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvule(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvule(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvsle(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsle(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvuge(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvuge(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvsge(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsge(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvugt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvugt(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvsgt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsgt(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_concat(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_concat(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_extract(
	value _v_c,
	value _v_high,
	value _v_low,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int high; /*in*/
  unsigned int low; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  high = Int_val(_v_high);
  low = Int_val(_v_low);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_extract(c, high, low, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_sign_ext(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_sign_ext(c, i, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_zero_ext(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_zero_ext(c, i, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_repeat(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_repeat(c, i, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvshl(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvshl(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvlshr(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvlshr(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvashr(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvashr(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_rotate_left(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_rotate_left(c, i, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_rotate_right(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_rotate_right(c, i, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_ext_rotate_left(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_ext_rotate_left(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_ext_rotate_right(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_ext_rotate_right(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_int2bv(
	value _v_c,
	value _v_n,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int n; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  n = Int_val(_v_n);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_int2bv(c, n, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bv2int(
	value _v_c,
	value _v_t1,
	value _v_is_signed)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  int is_signed; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  is_signed = Int_val(_v_is_signed);
  _res = Z3_mk_bv2int(c, t1, is_signed);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvadd_no_overflow(
	value _v_c,
	value _v_t1,
	value _v_t2,
	value _v_is_signed)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  int is_signed; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  is_signed = Int_val(_v_is_signed);
  _res = Z3_mk_bvadd_no_overflow(c, t1, t2, is_signed);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvadd_no_underflow(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvadd_no_underflow(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvsub_no_overflow(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsub_no_overflow(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvsub_no_underflow(
	value _v_c,
	value _v_t1,
	value _v_t2,
	value _v_is_signed)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  int is_signed; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  is_signed = Int_val(_v_is_signed);
  _res = Z3_mk_bvsub_no_underflow(c, t1, t2, is_signed);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvsdiv_no_overflow(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsdiv_no_overflow(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvneg_no_overflow(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvneg_no_overflow(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvmul_no_overflow(
	value _v_c,
	value _v_t1,
	value _v_t2,
	value _v_is_signed)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  int is_signed; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  is_signed = Int_val(_v_is_signed);
  _res = Z3_mk_bvmul_no_overflow(c, t1, t2, is_signed);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bvmul_no_underflow(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvmul_no_underflow(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_select(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_i, &i, _ctx);
  _res = Z3_mk_select(c, a, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_store(
	value _v_c,
	value _v_a,
	value _v_i,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast i; /*in*/
  Z3_ast v; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_i, &i, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_v, &v, _ctx);
  _res = Z3_mk_store(c, a, i, v);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_const_array(
	value _v_c,
	value _v_domain,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_sort domain; /*in*/
  Z3_ast v; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_domain, &domain, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_v, &v, _ctx);
  _res = Z3_mk_const_array(c, domain, v);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_map(
	value _v_c,
	value _v_f,
	value _v_n,
	value _v_args)
{
  Z3_context c; /*in*/
  Z3_func_decl f; /*in*/
  unsigned int n; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  Z3_ast _c1;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f, &f, _ctx);
  n = Int_val(_v_n);
  args = &_c1;
  camlidl_ml2c_z3_Z3_ast(_v_args, &_c1, _ctx);
  _res = Z3_mk_map(c, f, n, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_array_default(
	value _v_c,
	value _v_array)
{
  Z3_context c; /*in*/
  Z3_ast array; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_array, &array, _ctx);
  _res = Z3_mk_array_default(c, array);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_set_sort(
	value _v_c,
	value _v_ty)
{
  Z3_context c; /*in*/
  Z3_sort ty; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_set_sort(c, ty);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_empty_set(
	value _v_c,
	value _v_domain)
{
  Z3_context c; /*in*/
  Z3_sort domain; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_domain, &domain, _ctx);
  _res = Z3_mk_empty_set(c, domain);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_full_set(
	value _v_c,
	value _v_domain)
{
  Z3_context c; /*in*/
  Z3_sort domain; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_domain, &domain, _ctx);
  _res = Z3_mk_full_set(c, domain);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_set_add(
	value _v_c,
	value _v_set,
	value _v_elem)
{
  Z3_context c; /*in*/
  Z3_ast set; /*in*/
  Z3_ast elem; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_set, &set, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_elem, &elem, _ctx);
  _res = Z3_mk_set_add(c, set, elem);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_set_del(
	value _v_c,
	value _v_set,
	value _v_elem)
{
  Z3_context c; /*in*/
  Z3_ast set; /*in*/
  Z3_ast elem; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_set, &set, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_elem, &elem, _ctx);
  _res = Z3_mk_set_del(c, set, elem);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_set_union(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_set_union(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_set_intersect(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_set_intersect(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_set_difference(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_set_difference(c, arg1, arg2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_set_complement(
	value _v_c,
	value _v_arg)
{
  Z3_context c; /*in*/
  Z3_ast arg; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg, &arg, _ctx);
  _res = Z3_mk_set_complement(c, arg);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_set_member(
	value _v_c,
	value _v_elem,
	value _v_set)
{
  Z3_context c; /*in*/
  Z3_ast elem; /*in*/
  Z3_ast set; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_elem, &elem, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_set, &set, _ctx);
  _res = Z3_mk_set_member(c, elem, set);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_set_subset(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_set_subset(c, arg1, arg2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_numeral(
	value _v_c,
	value _v_numeral,
	value _v_ty)
{
  Z3_context c; /*in*/
  Z3_string numeral; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_numeral, &numeral, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_numeral(c, numeral, ty);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_real(
	value _v_c,
	value _v_num,
	value _v_den)
{
  Z3_context c; /*in*/
  int num; /*in*/
  int den; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  num = Int_val(_v_num);
  den = Int_val(_v_den);
  _res = Z3_mk_real(c, num, den);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_int(
	value _v_c,
	value _v_v,
	value _v_ty)
{
  Z3_context c; /*in*/
  int v; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  v = Int_val(_v_v);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_int(c, v, ty);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_int64(
	value _v_c,
	value _v_v,
	value _v_ty)
{
  Z3_context c; /*in*/
  __int64 v; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  v = Int64_val(_v_v);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_int64(c, v, ty);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_pattern(
	value _v_c,
	value _v_terms)
{
  Z3_context c; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_ast const *terms; /*in*/
  Z3_pattern _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_terms);
  terms = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_terms, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &terms[_c2], _ctx);
  }
  num_patterns = _c1;
  _res = Z3_mk_pattern(c, num_patterns, terms);
  _vres = camlidl_c2ml_z3_Z3_pattern(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_bound(
	value _v_c,
	value _v_index,
	value _v_ty)
{
  Z3_context c; /*in*/
  unsigned int index; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  index = Int_val(_v_index);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_bound(c, index, ty);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_forall(
	value _v_c,
	value _v_weight,
	value _v_patterns,
	value _v_sorts,
	value _v_decl_names,
	value _v_body)
{
  Z3_context c; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_decls; /*in*/
  Z3_sort const *sorts; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c1 * sizeof(Z3_pattern const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_patterns, _c2);
    camlidl_ml2c_z3_Z3_pattern(_v3, &patterns[_c2], _ctx);
  }
  num_patterns = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_decls = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_forall(c, weight, num_patterns, patterns, num_decls, sorts, decl_names, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_forall_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_forall(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_mk_exists(
	value _v_c,
	value _v_weight,
	value _v_patterns,
	value _v_sorts,
	value _v_decl_names,
	value _v_body)
{
  Z3_context c; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_decls; /*in*/
  Z3_sort const *sorts; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c1 * sizeof(Z3_pattern const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_patterns, _c2);
    camlidl_ml2c_z3_Z3_pattern(_v3, &patterns[_c2], _ctx);
  }
  num_patterns = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_decls = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_exists(c, weight, num_patterns, patterns, num_decls, sorts, decl_names, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_exists_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_exists(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_mk_quantifier(
	value _v_c,
	value _v_is_forall,
	value _v_weight,
	value _v_patterns,
	value _v_sorts,
	value _v_decl_names,
	value _v_body)
{
  Z3_context c; /*in*/
  int is_forall; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_decls; /*in*/
  Z3_sort const *sorts; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  is_forall = Int_val(_v_is_forall);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c1 * sizeof(Z3_pattern const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_patterns, _c2);
    camlidl_ml2c_z3_Z3_pattern(_v3, &patterns[_c2], _ctx);
  }
  num_patterns = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_decls = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_quantifier(c, is_forall, weight, num_patterns, patterns, num_decls, sorts, decl_names, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_quantifier_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_quantifier(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6]);
}

value camlidl_z3_Z3_mk_quantifier_ex(
	value _v_c,
	value _v_is_forall,
	value _v_weight,
	value _v_quantifier_id,
	value _v_skolem_id,
	value _v_patterns,
	value _v_no_patterns,
	value _v_sorts,
	value _v_decl_names,
	value _v_body)
{
  Z3_context c; /*in*/
  int is_forall; /*in*/
  unsigned int weight; /*in*/
  Z3_symbol quantifier_id; /*in*/
  Z3_symbol skolem_id; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_no_patterns; /*in*/
  Z3_ast const *no_patterns; /*in*/
  unsigned int num_decls; /*in*/
  Z3_sort const *sorts; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  is_forall = Int_val(_v_is_forall);
  weight = Int_val(_v_weight);
  camlidl_ml2c_z3_Z3_symbol(_v_quantifier_id, &quantifier_id, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_skolem_id, &skolem_id, _ctx);
  _c1 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c1 * sizeof(Z3_pattern const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_patterns, _c2);
    camlidl_ml2c_z3_Z3_pattern(_v3, &patterns[_c2], _ctx);
  }
  num_patterns = _c1;
  _c4 = Wosize_val(_v_no_patterns);
  no_patterns = camlidl_malloc(_c4 * sizeof(Z3_ast const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_no_patterns, _c5);
    camlidl_ml2c_z3_Z3_ast(_v6, &no_patterns[_c5], _ctx);
  }
  num_no_patterns = _c4;
  _c7 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c7 * sizeof(Z3_sort const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_sorts, _c8);
    camlidl_ml2c_z3_Z3_sort(_v9, &sorts[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c10 * sizeof(Z3_symbol const ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decl_names, _c11);
    camlidl_ml2c_z3_Z3_symbol(_v12, &decl_names[_c11], _ctx);
  }
  num_decls = _c10;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_quantifier_ex(c, is_forall, weight, quantifier_id, skolem_id, num_patterns, patterns, num_no_patterns, no_patterns, num_decls, sorts, decl_names, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_quantifier_ex_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_quantifier_ex(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7], argv[8], argv[9]);
}

value camlidl_z3_Z3_mk_forall_const(
	value _v_c,
	value _v_weight,
	value _v_bound,
	value _v_patterns,
	value _v_body)
{
  Z3_context c; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_bound; /*in*/
  Z3_app const *bound; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_bound);
  bound = camlidl_malloc(_c1 * sizeof(Z3_app const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bound, _c2);
    camlidl_ml2c_z3_Z3_app(_v3, &bound[_c2], _ctx);
  }
  num_bound = _c1;
  _c4 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c4 * sizeof(Z3_pattern const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_patterns, _c5);
    camlidl_ml2c_z3_Z3_pattern(_v6, &patterns[_c5], _ctx);
  }
  num_patterns = _c4;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_forall_const(c, weight, num_bound, bound, num_patterns, patterns, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_exists_const(
	value _v_c,
	value _v_weight,
	value _v_bound,
	value _v_patterns,
	value _v_body)
{
  Z3_context c; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_bound; /*in*/
  Z3_app const *bound; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_bound);
  bound = camlidl_malloc(_c1 * sizeof(Z3_app const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bound, _c2);
    camlidl_ml2c_z3_Z3_app(_v3, &bound[_c2], _ctx);
  }
  num_bound = _c1;
  _c4 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c4 * sizeof(Z3_pattern const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_patterns, _c5);
    camlidl_ml2c_z3_Z3_pattern(_v6, &patterns[_c5], _ctx);
  }
  num_patterns = _c4;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_exists_const(c, weight, num_bound, bound, num_patterns, patterns, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_quantifier_const(
	value _v_c,
	value _v_is_forall,
	value _v_weight,
	value _v_bound,
	value _v_patterns,
	value _v_body)
{
  Z3_context c; /*in*/
  int is_forall; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_bound; /*in*/
  Z3_app const *bound; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  is_forall = Int_val(_v_is_forall);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_bound);
  bound = camlidl_malloc(_c1 * sizeof(Z3_app const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bound, _c2);
    camlidl_ml2c_z3_Z3_app(_v3, &bound[_c2], _ctx);
  }
  num_bound = _c1;
  _c4 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c4 * sizeof(Z3_pattern const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_patterns, _c5);
    camlidl_ml2c_z3_Z3_pattern(_v6, &patterns[_c5], _ctx);
  }
  num_patterns = _c4;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_quantifier_const(c, is_forall, weight, num_bound, bound, num_patterns, patterns, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_quantifier_const_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_quantifier_const(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_mk_quantifier_const_ex(
	value _v_c,
	value _v_is_forall,
	value _v_weight,
	value _v_quantifier_id,
	value _v_skolem_id,
	value _v_bound,
	value _v_patterns,
	value _v_no_patterns,
	value _v_body)
{
  Z3_context c; /*in*/
  int is_forall; /*in*/
  unsigned int weight; /*in*/
  Z3_symbol quantifier_id; /*in*/
  Z3_symbol skolem_id; /*in*/
  unsigned int num_bound; /*in*/
  Z3_app const *bound; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_no_patterns; /*in*/
  Z3_ast const *no_patterns; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  is_forall = Int_val(_v_is_forall);
  weight = Int_val(_v_weight);
  camlidl_ml2c_z3_Z3_symbol(_v_quantifier_id, &quantifier_id, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_skolem_id, &skolem_id, _ctx);
  _c1 = Wosize_val(_v_bound);
  bound = camlidl_malloc(_c1 * sizeof(Z3_app const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bound, _c2);
    camlidl_ml2c_z3_Z3_app(_v3, &bound[_c2], _ctx);
  }
  num_bound = _c1;
  _c4 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c4 * sizeof(Z3_pattern const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_patterns, _c5);
    camlidl_ml2c_z3_Z3_pattern(_v6, &patterns[_c5], _ctx);
  }
  num_patterns = _c4;
  _c7 = Wosize_val(_v_no_patterns);
  no_patterns = camlidl_malloc(_c7 * sizeof(Z3_ast const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_no_patterns, _c8);
    camlidl_ml2c_z3_Z3_ast(_v9, &no_patterns[_c8], _ctx);
  }
  num_no_patterns = _c7;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_quantifier_const_ex(c, is_forall, weight, quantifier_id, skolem_id, num_bound, bound, num_patterns, patterns, num_no_patterns, no_patterns, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_quantifier_const_ex_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_quantifier_const_ex(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7], argv[8]);
}

value camlidl_z3_Z3_get_symbol_kind(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  Z3_symbol_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_get_symbol_kind(c, s);
  _vres = camlidl_c2ml_z3_Z3_symbol_kind(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_symbol_int(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_get_symbol_int(c, s);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_symbol_string(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_get_symbol_string(c, s);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_sort_name(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_sort d; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_d, &d, _ctx);
  _res = Z3_get_sort_name(c, d);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_sort_id(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_get_sort_id(c, s);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_sort_to_ast(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_sort_to_ast(c, s);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_is_eq_sort(
	value _v_c,
	value _v_s1,
	value _v_s2)
{
  Z3_context c; /*in*/
  Z3_sort s1; /*in*/
  Z3_sort s2; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s1, &s1, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s2, &s2, _ctx);
  _res = Z3_is_eq_sort(c, s1, s2);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_sort_kind(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  Z3_sort_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_sort_kind(c, t);
  _vres = camlidl_c2ml_z3_Z3_sort_kind(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_bv_sort_size(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_bv_sort_size(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_finite_domain_sort_size(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  __int64 *r; /*out*/
  __int64 _c1;
  value _v2;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  r = &_c1;
  Z3_get_finite_domain_sort_size(c, s, r);
  if (r == NULL) {
    _vres = Val_int(0);
  } else {
    _v2 = copy_int64(*r);
    Begin_root(_v2)
      _vres = camlidl_alloc_small(1, 0);
      Field(_vres, 0) = _v2;
    End_roots();
  }
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_array_sort_domain(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_array_sort_domain(c, t);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_array_sort_range(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_array_sort_range(c, t);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_tuple_sort_mk_decl(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_tuple_sort_mk_decl(c, t);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_tuple_sort_num_fields(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_tuple_sort_num_fields(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_tuple_sort_field_decl(
	value _v_c,
	value _v_t,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int i; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_tuple_sort_field_decl(c, t, i);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_datatype_sort_num_constructors(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_datatype_sort_num_constructors(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_datatype_sort_constructor(
	value _v_c,
	value _v_t,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int idx; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_datatype_sort_constructor(c, t, idx);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_datatype_sort_recognizer(
	value _v_c,
	value _v_t,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int idx; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_datatype_sort_recognizer(c, t, idx);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_datatype_sort_constructor_accessor(
	value _v_c,
	value _v_t,
	value _v_idx_c,
	value _v_idx_a)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int idx_c; /*in*/
  unsigned int idx_a; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  idx_c = Int_val(_v_idx_c);
  idx_a = Int_val(_v_idx_a);
  _res = Z3_get_datatype_sort_constructor_accessor(c, t, idx_c, idx_a);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_relation_arity(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_get_relation_arity(c, s);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_relation_column(
	value _v_c,
	value _v_s,
	value _v_col)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  unsigned int col; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  col = Int_val(_v_col);
  _res = Z3_get_relation_column(c, s, col);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_func_decl_to_ast(
	value _v_c,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_func_decl f; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f, &f, _ctx);
  _res = Z3_func_decl_to_ast(c, f);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_is_eq_func_decl(
	value _v_c,
	value _v_f1,
	value _v_f2)
{
  Z3_context c; /*in*/
  Z3_func_decl f1; /*in*/
  Z3_func_decl f2; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f1, &f1, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f2, &f2, _ctx);
  _res = Z3_is_eq_func_decl(c, f1, f2);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_func_decl_id(
	value _v_c,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_func_decl f; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f, &f, _ctx);
  _res = Z3_get_func_decl_id(c, f);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_decl_name(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_decl_name(c, d);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_decl_kind(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  Z3_decl_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_decl_kind(c, d);
  _vres = camlidl_c2ml_z3_Z3_decl_kind(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_domain_size(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_domain_size(c, d);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_arity(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_arity(c, d);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_domain(
	value _v_c,
	value _v_d,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int i; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_domain(c, d, i);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_range(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_range(c, d);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_decl_num_parameters(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_decl_num_parameters(c, d);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_decl_parameter_kind(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_parameter_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_parameter_kind(c, d, idx);
  _vres = camlidl_c2ml_z3_Z3_parameter_kind(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_decl_int_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_int_parameter(c, d, idx);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_decl_double_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  double _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_double_parameter(c, d, idx);
  _vres = copy_double(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_decl_symbol_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_symbol_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_decl_sort_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_sort_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_decl_ast_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_ast_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_decl_func_decl_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_func_decl_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_decl_rational_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_rational_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_app_to_ast(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_app a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_app(_v_a, &a, _ctx);
  _res = Z3_app_to_ast(c, a);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_app_decl(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_app a; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_app(_v_a, &a, _ctx);
  _res = Z3_get_app_decl(c, a);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_app_num_args(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_app a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_app(_v_a, &a, _ctx);
  _res = Z3_get_app_num_args(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_app_arg(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_app a; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_app(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_app_arg(c, a, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_is_eq_ast(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_is_eq_ast(c, t1, t2);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_ast_id(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_ast t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t, &t, _ctx);
  _res = Z3_get_ast_id(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_ast_hash(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_ast_hash(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_sort(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_sort(c, a);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_is_well_sorted(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_ast t; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t, &t, _ctx);
  _res = Z3_is_well_sorted(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_bool_value(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_lbool _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_bool_value(c, a);
  _vres = camlidl_c2ml_z3_Z3_lbool(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_ast_kind(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_ast_kind(c, a);
  _vres = camlidl_c2ml_z3_Z3_ast_kind(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_is_app(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_is_app(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_is_numeral_ast(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_is_numeral_ast(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_is_algebraic_number(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_is_algebraic_number(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_to_app(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_app _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_to_app(c, a);
  _vres = camlidl_c2ml_z3_Z3_app(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_to_func_decl(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_to_func_decl(c, a);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_numeral_string(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_numeral_string(c, a);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_numeral_decimal_string(
	value _v_c,
	value _v_a,
	value _v_precision)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int precision; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  precision = Int_val(_v_precision);
  _res = Z3_get_numeral_decimal_string(c, a, precision);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_numerator(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_numerator(c, a);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_denominator(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_denominator(c, a);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_numeral_small(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  __int64 *num; /*out*/
  __int64 *den; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  __int64 _c1;
  __int64 _c2;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  num = &_c1;
  den = &_c2;
  _res = Z3_get_numeral_small(c, a, num, den);
  Begin_roots_block(_vres, 3)
    _vres[0] = Val_int(_res);
    _vres[1] = copy_int64(*num);
    _vres[2] = copy_int64(*den);
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vresult;
}

value camlidl_z3_Z3_get_numeral_int(
	value _v_c,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast v; /*in*/
  int *i; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  int _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_v, &v, _ctx);
  i = &_c1;
  _res = Z3_get_numeral_int(c, v, i);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = Val_int(*i);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vresult;
}

value camlidl_z3_Z3_get_numeral_int64(
	value _v_c,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast v; /*in*/
  __int64 *i; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  __int64 _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_v, &v, _ctx);
  i = &_c1;
  _res = Z3_get_numeral_int64(c, v, i);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = copy_int64(*i);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vresult;
}

value camlidl_z3_Z3_get_numeral_rational_int64(
	value _v_c,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast v; /*in*/
  __int64 *num; /*out*/
  __int64 *den; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  __int64 _c1;
  __int64 _c2;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_v, &v, _ctx);
  num = &_c1;
  den = &_c2;
  _res = Z3_get_numeral_rational_int64(c, v, num, den);
  Begin_roots_block(_vres, 3)
    _vres[0] = Val_int(_res);
    _vres[1] = copy_int64(*num);
    _vres[2] = copy_int64(*den);
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vresult;
}

value camlidl_z3_Z3_get_algebraic_number_lower(
	value _v_c,
	value _v_a,
	value _v_precision)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int precision; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  precision = Int_val(_v_precision);
  _res = Z3_get_algebraic_number_lower(c, a, precision);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_algebraic_number_upper(
	value _v_c,
	value _v_a,
	value _v_precision)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int precision; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  precision = Int_val(_v_precision);
  _res = Z3_get_algebraic_number_upper(c, a, precision);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_pattern_to_ast(
	value _v_c,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_pattern p; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_pattern(_v_p, &p, _ctx);
  _res = Z3_pattern_to_ast(c, p);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_pattern_num_terms(
	value _v_c,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_pattern p; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_pattern(_v_p, &p, _ctx);
  _res = Z3_get_pattern_num_terms(c, p);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_pattern(
	value _v_c,
	value _v_p,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_pattern p; /*in*/
  unsigned int idx; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_pattern(_v_p, &p, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_pattern(c, p, idx);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_index_value(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_index_value(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_is_quantifier_forall(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_is_quantifier_forall(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_weight(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_weight(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_num_patterns(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_num_patterns(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_pattern_ast(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int i; /*in*/
  Z3_pattern _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_quantifier_pattern_ast(c, a, i);
  _vres = camlidl_c2ml_z3_Z3_pattern(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_num_no_patterns(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_num_no_patterns(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_no_pattern_ast(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_quantifier_no_pattern_ast(c, a, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_num_bound(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_num_bound(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_bound_name(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int i; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_quantifier_bound_name(c, a, i);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_bound_sort(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int i; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_quantifier_bound_sort(c, a, i);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_body(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_body(c, a);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_simplify(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_simplify(c, a);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_simplify_ex(
	value _v_c,
	value _v_a,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_params p; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  camlidl_ml2c_z3_Z3_params(_v_p, &p, _ctx);
  _res = Z3_simplify_ex(c, a, p);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_simplify_get_help(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_simplify_get_help(c);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_simplify_get_param_descrs(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_param_descrs _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_simplify_get_param_descrs(c);
  _vres = camlidl_c2ml_z3_Z3_param_descrs(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_update_term(
	value _v_c,
	value _v_a,
	value _v_args)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_update_term(c, a, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_substitute(
	value _v_c,
	value _v_a,
	value _v_from,
	value _v_to)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int num_exprs; /*in*/
  Z3_ast const *from; /*in*/
  Z3_ast const *to; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _c1 = Wosize_val(_v_from);
  from = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_from, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &from[_c2], _ctx);
  }
  num_exprs = _c1;
  _c4 = Wosize_val(_v_to);
  to = camlidl_malloc(_c4 * sizeof(Z3_ast const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_to, _c5);
    camlidl_ml2c_z3_Z3_ast(_v6, &to[_c5], _ctx);
  }
  num_exprs = _c4;
  _res = Z3_substitute(c, a, num_exprs, from, to);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_substitute_vars(
	value _v_c,
	value _v_a,
	value _v_to)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int num_exprs; /*in*/
  Z3_ast const *to; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _c1 = Wosize_val(_v_to);
  to = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_to, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &to[_c2], _ctx);
  }
  num_exprs = _c1;
  _res = Z3_substitute_vars(c, a, num_exprs, to);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_translate(
	value _v_source,
	value _v_a,
	value _v_target)
{
  Z3_context source; /*in*/
  Z3_ast a; /*in*/
  Z3_context target; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_source, &source, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  camlidl_ml2c_z3_Z3_context(_v_target, &target, _ctx);
  _res = Z3_translate(source, a, target);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(source);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_model_eval(
	value _v_c,
	value _v_m,
	value _v_t,
	value _v_model_completion)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_ast t; /*in*/
  int model_completion; /*in*/
  Z3_ast *v; /*out*/
  Z3_ast _c1;
  value _v2;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t, &t, _ctx);
  model_completion = Int_val(_v_model_completion);
  v = &_c1;
  Z3_model_eval(c, m, t, model_completion, v);
  if (v == NULL) {
    _vres = Val_int(0);
  } else {
    _v2 = camlidl_c2ml_z3_Z3_ast(&*v, _ctx);
    Begin_root(_v2)
      _vres = camlidl_alloc_small(1, 0);
      Field(_vres, 0) = _v2;
    End_roots();
  }
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_model_get_const_interp(
	value _v_c,
	value _v_m,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_func_decl a; /*in*/
  Z3_ast_opt _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_a, &a, _ctx);
  _res = Z3_model_get_const_interp(c, m, a);
  _vres = camlidl_c2ml_z3_Z3_ast_opt(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_model_get_func_interp(
	value _v_c,
	value _v_m,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_func_decl f; /*in*/
  Z3_func_interp_opt _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f, &f, _ctx);
  _res = Z3_model_get_func_interp(c, m, f);
  _vres = camlidl_c2ml_z3_Z3_func_interp_opt(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_model_get_num_consts(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  _res = Z3_model_get_num_consts(c, m);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_model_get_const_decl(
	value _v_c,
	value _v_m,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  _res = Z3_model_get_const_decl(c, m, i);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_model_get_num_funcs(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  _res = Z3_model_get_num_funcs(c, m);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_model_get_func_decl(
	value _v_c,
	value _v_m,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  _res = Z3_model_get_func_decl(c, m, i);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_model_get_num_sorts(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  _res = Z3_model_get_num_sorts(c, m);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_model_get_sort(
	value _v_c,
	value _v_m,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  _res = Z3_model_get_sort(c, m, i);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_model_get_sort_universe(
	value _v_c,
	value _v_m,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_sort s; /*in*/
  Z3_ast_vector _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_model_get_sort_universe(c, m, s);
  _vres = camlidl_c2ml_z3_Z3_ast_vector(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_is_as_array(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_is_as_array(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_as_array_func_decl(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_as_array_func_decl(c, a);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_func_interp_get_num_entries(
	value _v_c,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_func_interp f; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_interp(_v_f, &f, _ctx);
  _res = Z3_func_interp_get_num_entries(c, f);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_func_interp_get_entry(
	value _v_c,
	value _v_f,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_func_interp f; /*in*/
  unsigned int i; /*in*/
  Z3_func_entry _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_interp(_v_f, &f, _ctx);
  i = Int_val(_v_i);
  _res = Z3_func_interp_get_entry(c, f, i);
  _vres = camlidl_c2ml_z3_Z3_func_entry(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_func_interp_get_else(
	value _v_c,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_func_interp f; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_interp(_v_f, &f, _ctx);
  _res = Z3_func_interp_get_else(c, f);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_func_interp_get_arity(
	value _v_c,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_func_interp f; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_interp(_v_f, &f, _ctx);
  _res = Z3_func_interp_get_arity(c, f);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_func_entry_get_value(
	value _v_c,
	value _v_e)
{
  Z3_context c; /*in*/
  Z3_func_entry e; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_entry(_v_e, &e, _ctx);
  _res = Z3_func_entry_get_value(c, e);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_func_entry_get_num_args(
	value _v_c,
	value _v_e)
{
  Z3_context c; /*in*/
  Z3_func_entry e; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_entry(_v_e, &e, _ctx);
  _res = Z3_func_entry_get_num_args(c, e);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_func_entry_get_arg(
	value _v_c,
	value _v_e,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_func_entry e; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_entry(_v_e, &e, _ctx);
  i = Int_val(_v_i);
  _res = Z3_func_entry_get_arg(c, e, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_open_log(
	value _v_filename)
{
  Z3_string filename; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_string(_v_filename, &filename, _ctx);
  _res = Z3_open_log(filename);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_append_log(
	value _v_string)
{
  Z3_string string; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_string(_v_string, &string, _ctx);
  Z3_append_log(string);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_close_log(value _unit)
{
  Z3_close_log();
  return Val_unit;
}

value camlidl_z3_Z3_toggle_warning_messages(
	value _v_enabled)
{
  int enabled; /*in*/
  enabled = Int_val(_v_enabled);
  Z3_toggle_warning_messages(enabled);
  return Val_unit;
}

value camlidl_z3_Z3_set_ast_print_mode(
	value _v_c,
	value _v_mode)
{
  Z3_context c; /*in*/
  Z3_ast_print_mode mode; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_print_mode(_v_mode, &mode, _ctx);
  Z3_set_ast_print_mode(c, mode);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_ast_to_string(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_ast_to_string(c, a);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_pattern_to_string(
	value _v_c,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_pattern p; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_pattern(_v_p, &p, _ctx);
  _res = Z3_pattern_to_string(c, p);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_sort_to_string(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_sort_to_string(c, s);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_func_decl_to_string(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_func_decl_to_string(c, d);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_model_to_string(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  _res = Z3_model_to_string(c, m);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_benchmark_to_smtlib_string(
	value _v_c,
	value _v_name,
	value _v_logic,
	value _v_status,
	value _v_attributes,
	value _v_assumptions,
	value _v_formula)
{
  Z3_context c; /*in*/
  Z3_string name; /*in*/
  Z3_string logic; /*in*/
  Z3_string status; /*in*/
  Z3_string attributes; /*in*/
  unsigned int num_assumptions; /*in*/
  Z3_ast const *assumptions; /*in*/
  Z3_ast formula; /*in*/
  Z3_string _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_name, &name, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_logic, &logic, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_status, &status, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_attributes, &attributes, _ctx);
  _c1 = Wosize_val(_v_assumptions);
  assumptions = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_assumptions, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &assumptions[_c2], _ctx);
  }
  num_assumptions = _c1;
  camlidl_ml2c_z3_Z3_ast(_v_formula, &formula, _ctx);
  _res = Z3_benchmark_to_smtlib_string(c, name, logic, status, attributes, num_assumptions, assumptions, formula);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_benchmark_to_smtlib_string_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_benchmark_to_smtlib_string(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6]);
}

value camlidl_z3_Z3_parse_smtlib2_string(
	value _v_c,
	value _v_str,
	value _v_sort_names,
	value _v_sorts,
	value _v_decl_names,
	value _v_decls)
{
  Z3_context c; /*in*/
  Z3_string str; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol const *sort_names; /*in*/
  Z3_sort const *sorts; /*in*/
  unsigned int num_decls; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_func_decl const *decls; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_str, &str, _ctx);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_sorts = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decls);
  decls = camlidl_malloc(_c10 * sizeof(Z3_func_decl const ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decls, _c11);
    camlidl_ml2c_z3_Z3_func_decl(_v12, &decls[_c11], _ctx);
  }
  num_decls = _c10;
  _res = Z3_parse_smtlib2_string(c, str, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_parse_smtlib2_string_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_parse_smtlib2_string(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_parse_smtlib2_file(
	value _v_c,
	value _v_file_name,
	value _v_sort_names,
	value _v_sorts,
	value _v_decl_names,
	value _v_decls)
{
  Z3_context c; /*in*/
  Z3_string file_name; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol const *sort_names; /*in*/
  Z3_sort const *sorts; /*in*/
  unsigned int num_decls; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_func_decl const *decls; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_file_name, &file_name, _ctx);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_sorts = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decls);
  decls = camlidl_malloc(_c10 * sizeof(Z3_func_decl const ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decls, _c11);
    camlidl_ml2c_z3_Z3_func_decl(_v12, &decls[_c11], _ctx);
  }
  num_decls = _c10;
  _res = Z3_parse_smtlib2_file(c, file_name, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_parse_smtlib2_file_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_parse_smtlib2_file(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_parse_smtlib_string(
	value _v_c,
	value _v_str,
	value _v_sort_names,
	value _v_sorts,
	value _v_decl_names,
	value _v_decls)
{
  Z3_context c; /*in*/
  Z3_string str; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol const *sort_names; /*in*/
  Z3_sort const *sorts; /*in*/
  unsigned int num_decls; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_func_decl const *decls; /*in*/
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_str, &str, _ctx);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_sorts = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decls);
  decls = camlidl_malloc(_c10 * sizeof(Z3_func_decl const ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decls, _c11);
    camlidl_ml2c_z3_Z3_func_decl(_v12, &decls[_c11], _ctx);
  }
  num_decls = _c10;
  Z3_parse_smtlib_string(c, str, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_parse_smtlib_string_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_parse_smtlib_string(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_parse_smtlib_file(
	value _v_c,
	value _v_file_name,
	value _v_sort_names,
	value _v_sorts,
	value _v_decl_names,
	value _v_decls)
{
  Z3_context c; /*in*/
  Z3_string file_name; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol const *sort_names; /*in*/
  Z3_sort const *sorts; /*in*/
  unsigned int num_decls; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_func_decl const *decls; /*in*/
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_file_name, &file_name, _ctx);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_sorts = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decls);
  decls = camlidl_malloc(_c10 * sizeof(Z3_func_decl const ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decls, _c11);
    camlidl_ml2c_z3_Z3_func_decl(_v12, &decls[_c11], _ctx);
  }
  num_decls = _c10;
  Z3_parse_smtlib_file(c, file_name, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_parse_smtlib_file_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_parse_smtlib_file(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_get_smtlib_num_formulas(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_num_formulas(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_formula(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_smtlib_formula(c, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_num_assumptions(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_num_assumptions(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_assumption(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_smtlib_assumption(c, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_num_decls(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_num_decls(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_decl(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_smtlib_decl(c, i);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_num_sorts(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_num_sorts(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_sort(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_smtlib_sort(c, i);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_error(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_error(c);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}
/*
value camlidl_z3_Z3_parse_z3_string(
	value _v_c,
	value _v_str)
{
  Z3_context c; /*in
  Z3_string str; /*in
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_str, &str, _ctx);
  _res = Z3_parse_z3_string(c, str);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence 
check_error_code(c);
  /* end user-supplied deallocation sequence 
  return _vres;
}

value camlidl_z3_Z3_parse_z3_file(
	value _v_c,
	value _v_file_name)
{
  Z3_context c; /*in
  Z3_string file_name; /*in
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_file_name, &file_name, _ctx);
  _res = Z3_parse_z3_file(c, file_name);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence 
check_error_code(c);
  /* end user-supplied deallocation sequence 
  return _vres;
}
*/
value camlidl_z3_Z3_set_error(
	value _v_c,
	value _v_e)
{
  Z3_context c; /*in*/
  Z3_error_code e; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_error_code(_v_e, &e, _ctx);
  Z3_set_error(c, e);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_get_error_msg_ex(
	value _v_c,
	value _v_err)
{
  Z3_context c; /*in*/
  Z3_error_code err; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_error_code(_v_err, &err, _ctx);
  _res = Z3_get_error_msg_ex(c, err);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_version(value _unit)
{
  unsigned int *major; /*out*/
  unsigned int *minor; /*out*/
  unsigned int *build_number; /*out*/
  unsigned int *revision_number; /*out*/
  unsigned int _c1;
  unsigned int _c2;
  unsigned int _c3;
  unsigned int _c4;
  value _vresult;
  value _vres[4] = { 0, 0, 0, 0, };

  major = &_c1;
  minor = &_c2;
  build_number = &_c3;
  revision_number = &_c4;
  Z3_get_version(major, minor, build_number, revision_number);
  Begin_roots_block(_vres, 4)
    _vres[0] = Val_int(*major);
    _vres[1] = Val_int(*minor);
    _vres[2] = Val_int(*build_number);
    _vres[3] = Val_int(*revision_number);
    _vresult = camlidl_alloc_small(4, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
    Field(_vresult, 3) = _vres[3];
  End_roots()
  return _vresult;
}

value camlidl_z3_Z3_mk_fixedpoint(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_fixedpoint _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_fixedpoint(c);
  _vres = camlidl_c2ml_z3_Z3_fixedpoint(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_fixedpoint_add_rule(
	value _v_c,
	value _v_d,
	value _v_rule,
	value _v_name)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  Z3_ast rule; /*in*/
  Z3_symbol name; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_rule, &rule, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_name, &name, _ctx);
  Z3_fixedpoint_add_rule(c, d, rule, name);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_fixedpoint_add_fact(
	value _v_c,
	value _v_d,
	value _v_r,
	value _v_args)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  Z3_func_decl r; /*in*/
  unsigned int num_args; /*in*/
  unsigned int *args; /*in*/
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_r, &r, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(unsigned int ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    args[_c2] = Int_val(_v3);
  }
  num_args = _c1;
  Z3_fixedpoint_add_fact(c, d, r, num_args, args);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_fixedpoint_assert(
	value _v_c,
	value _v_d,
	value _v_axiom)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  Z3_ast axiom; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_axiom, &axiom, _ctx);
  Z3_fixedpoint_assert(c, d, axiom);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_fixedpoint_query(
	value _v_c,
	value _v_d,
	value _v_query)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  Z3_ast query; /*in*/
  Z3_lbool _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_query, &query, _ctx);
  _res = Z3_fixedpoint_query(c, d, query);
  _vres = camlidl_c2ml_z3_Z3_lbool(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_fixedpoint_query_relations(
	value _v_c,
	value _v_d,
	value _v_relations)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  unsigned int num_relations; /*in*/
  Z3_func_decl const *relations; /*in*/
  Z3_lbool _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  _c1 = Wosize_val(_v_relations);
  relations = camlidl_malloc(_c1 * sizeof(Z3_func_decl const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_relations, _c2);
    camlidl_ml2c_z3_Z3_func_decl(_v3, &relations[_c2], _ctx);
  }
  num_relations = _c1;
  _res = Z3_fixedpoint_query_relations(c, d, num_relations, relations);
  _vres = camlidl_c2ml_z3_Z3_lbool(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_fixedpoint_get_answer(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  _res = Z3_fixedpoint_get_answer(c, d);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_fixedpoint_get_reason_unknown(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  _res = Z3_fixedpoint_get_reason_unknown(c, d);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_fixedpoint_update_rule(
	value _v_c,
	value _v_d,
	value _v_a,
	value _v_name)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  Z3_ast a; /*in*/
  Z3_symbol name; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_name, &name, _ctx);
  Z3_fixedpoint_update_rule(c, d, a, name);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_fixedpoint_get_num_levels(
	value _v_c,
	value _v_d,
	value _v_pred)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  Z3_func_decl pred; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_pred, &pred, _ctx);
  _res = Z3_fixedpoint_get_num_levels(c, d, pred);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_fixedpoint_get_cover_delta(
	value _v_c,
	value _v_d,
	value _v_level,
	value _v_pred)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  int level; /*in*/
  Z3_func_decl pred; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  level = Int_val(_v_level);
  camlidl_ml2c_z3_Z3_func_decl(_v_pred, &pred, _ctx);
  _res = Z3_fixedpoint_get_cover_delta(c, d, level, pred);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_fixedpoint_add_cover(
	value _v_c,
	value _v_d,
	value _v_level,
	value _v_pred,
	value _v_property)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  int level; /*in*/
  Z3_func_decl pred; /*in*/
  Z3_ast property; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  level = Int_val(_v_level);
  camlidl_ml2c_z3_Z3_func_decl(_v_pred, &pred, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_property, &property, _ctx);
  Z3_fixedpoint_add_cover(c, d, level, pred, property);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_fixedpoint_get_statistics(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  Z3_stats _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  _res = Z3_fixedpoint_get_statistics(c, d);
  _vres = camlidl_c2ml_z3_Z3_stats(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_fixedpoint_register_relation(
	value _v_c,
	value _v_d,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  Z3_func_decl f; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f, &f, _ctx);
  Z3_fixedpoint_register_relation(c, d, f);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_fixedpoint_set_predicate_representation(
	value _v_c,
	value _v_d,
	value _v_f,
	value _v_relation_kinds)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  Z3_func_decl f; /*in*/
  unsigned int num_relations; /*in*/
  Z3_symbol const *relation_kinds; /*in*/
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f, &f, _ctx);
  _c1 = Wosize_val(_v_relation_kinds);
  relation_kinds = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_relation_kinds, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &relation_kinds[_c2], _ctx);
  }
  num_relations = _c1;
  Z3_fixedpoint_set_predicate_representation(c, d, f, num_relations, relation_kinds);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_fixedpoint_simplify_rules(
	value _v_c,
	value _v_f,
	value _v_rules,
	value _v_outputs)
{
  Z3_context c; /*in*/
  Z3_fixedpoint f; /*in*/
  unsigned int num_rules; /*in*/
  Z3_ast *rules; /*in*/
  unsigned int num_outputs; /*in*/
  Z3_func_decl *outputs; /*in*/
  Z3_ast_vector _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_f, &f, _ctx);
  _c1 = Wosize_val(_v_rules);
  rules = camlidl_malloc(_c1 * sizeof(Z3_ast ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_rules, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &rules[_c2], _ctx);
  }
  num_rules = _c1;
  _c4 = Wosize_val(_v_outputs);
  outputs = camlidl_malloc(_c4 * sizeof(Z3_func_decl ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_outputs, _c5);
    camlidl_ml2c_z3_Z3_func_decl(_v6, &outputs[_c5], _ctx);
  }
  num_outputs = _c4;
  // _res = Z3_fixedpoint_simplify_rules(c, f, num_rules, rules, num_outputs, outputs);
  _vres = camlidl_c2ml_z3_Z3_ast_vector(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_fixedpoint_set_params(
	value _v_c,
	value _v_f,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_fixedpoint f; /*in*/
  Z3_params p; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_f, &f, _ctx);
  camlidl_ml2c_z3_Z3_params(_v_p, &p, _ctx);
  Z3_fixedpoint_set_params(c, f, p);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_fixedpoint_get_help(
	value _v_c,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_fixedpoint f; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_f, &f, _ctx);
  _res = Z3_fixedpoint_get_help(c, f);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_fixedpoint_get_param_descrs(
	value _v_c,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_fixedpoint f; /*in*/
  Z3_param_descrs _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_f, &f, _ctx);
  _res = Z3_fixedpoint_get_param_descrs(c, f);
  _vres = camlidl_c2ml_z3_Z3_param_descrs(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_fixedpoint_to_string(
	value _v_c,
	value _v_f,
	value _v_queries)
{
  Z3_context c; /*in*/
  Z3_fixedpoint f; /*in*/
  unsigned int num_queries; /*in*/
  Z3_ast *queries; /*in*/
  Z3_string _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_f, &f, _ctx);
  _c1 = Wosize_val(_v_queries);
  queries = camlidl_malloc(_c1 * sizeof(Z3_ast ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_queries, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &queries[_c2], _ctx);
  }
  num_queries = _c1;
  _res = Z3_fixedpoint_to_string(c, f, num_queries, queries);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_fixedpoint_push(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  Z3_fixedpoint_push(c, d);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_fixedpoint_pop(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_fixedpoint d; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_fixedpoint(_v_d, &d, _ctx);
  Z3_fixedpoint_pop(c, d);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_mk_ast_vector(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_ast_vector _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_ast_vector(c);
  _vres = camlidl_c2ml_z3_Z3_ast_vector(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_ast_vector_size(
	value _v_c,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast_vector v; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_vector(_v_v, &v, _ctx);
  _res = Z3_ast_vector_size(c, v);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_ast_vector_get(
	value _v_c,
	value _v_v,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast_vector v; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_vector(_v_v, &v, _ctx);
  i = Int_val(_v_i);
  _res = Z3_ast_vector_get(c, v, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_ast_vector_set(
	value _v_c,
	value _v_v,
	value _v_i,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast_vector v; /*in*/
  unsigned int i; /*in*/
  Z3_ast a; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_vector(_v_v, &v, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  Z3_ast_vector_set(c, v, i, a);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_ast_vector_resize(
	value _v_c,
	value _v_v,
	value _v_n)
{
  Z3_context c; /*in*/
  Z3_ast_vector v; /*in*/
  unsigned int n; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_vector(_v_v, &v, _ctx);
  n = Int_val(_v_n);
  Z3_ast_vector_resize(c, v, n);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_ast_vector_push(
	value _v_c,
	value _v_v,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast_vector v; /*in*/
  Z3_ast a; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_vector(_v_v, &v, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  Z3_ast_vector_push(c, v, a);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_ast_vector_translate(
	value _v_s,
	value _v_v,
	value _v_t)
{
  Z3_context s; /*in*/
  Z3_ast_vector v; /*in*/
  Z3_context t; /*in*/
  Z3_ast_vector _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_s, &s, _ctx);
  camlidl_ml2c_z3_Z3_ast_vector(_v_v, &v, _ctx);
  camlidl_ml2c_z3_Z3_context(_v_t, &t, _ctx);
  _res = Z3_ast_vector_translate(s, v, t);
  _vres = camlidl_c2ml_z3_Z3_ast_vector(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(s);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_ast_vector_to_string(
	value _v_c,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast_vector v; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_vector(_v_v, &v, _ctx);
  _res = Z3_ast_vector_to_string(c, v);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_ast_map(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_ast_map _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_ast_map(c);
  _vres = camlidl_c2ml_z3_Z3_ast_map(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_ast_map_contains(
	value _v_c,
	value _v_m,
	value _v_k)
{
  Z3_context c; /*in*/
  Z3_ast_map m; /*in*/
  Z3_ast k; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_map(_v_m, &m, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_k, &k, _ctx);
  _res = Z3_ast_map_contains(c, m, k);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_ast_map_find(
	value _v_c,
	value _v_m,
	value _v_k)
{
  Z3_context c; /*in*/
  Z3_ast_map m; /*in*/
  Z3_ast k; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_map(_v_m, &m, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_k, &k, _ctx);
  _res = Z3_ast_map_find(c, m, k);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_ast_map_insert(
	value _v_c,
	value _v_m,
	value _v_k,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast_map m; /*in*/
  Z3_ast k; /*in*/
  Z3_ast v; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_map(_v_m, &m, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_k, &k, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_v, &v, _ctx);
  Z3_ast_map_insert(c, m, k, v);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_ast_map_erase(
	value _v_c,
	value _v_m,
	value _v_k)
{
  Z3_context c; /*in*/
  Z3_ast_map m; /*in*/
  Z3_ast k; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_map(_v_m, &m, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_k, &k, _ctx);
  Z3_ast_map_erase(c, m, k);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_ast_map_reset(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_ast_map m; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_map(_v_m, &m, _ctx);
  Z3_ast_map_reset(c, m);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_ast_map_size(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_ast_map m; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_map(_v_m, &m, _ctx);
  _res = Z3_ast_map_size(c, m);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_ast_map_keys(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_ast_map m; /*in*/
  Z3_ast_vector _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_map(_v_m, &m, _ctx);
  _res = Z3_ast_map_keys(c, m);
  _vres = camlidl_c2ml_z3_Z3_ast_vector(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_ast_map_to_string(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_ast_map m; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_map(_v_m, &m, _ctx);
  _res = Z3_ast_map_to_string(c, m);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_goal(
	value _v_c,
	value _v_models,
	value _v_unsat_cores,
	value _v_proofs)
{
  Z3_context c; /*in*/
  int models; /*in*/
  int unsat_cores; /*in*/
  int proofs; /*in*/
  Z3_goal _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  models = Int_val(_v_models);
  unsat_cores = Int_val(_v_unsat_cores);
  proofs = Int_val(_v_proofs);
  _res = Z3_mk_goal(c, models, unsat_cores, proofs);
  _vres = camlidl_c2ml_z3_Z3_goal(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_goal_precision(
	value _v_c,
	value _v_g)
{
  Z3_context c; /*in*/
  Z3_goal g; /*in*/
  Z3_goal_prec _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  _res = Z3_goal_precision(c, g);
  _vres = camlidl_c2ml_z3_Z3_goal_prec(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_goal_assert(
	value _v_c,
	value _v_g,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_goal g; /*in*/
  Z3_ast a; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  Z3_goal_assert(c, g, a);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_goal_inconsistent(
	value _v_c,
	value _v_g)
{
  Z3_context c; /*in*/
  Z3_goal g; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  _res = Z3_goal_inconsistent(c, g);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_goal_depth(
	value _v_c,
	value _v_g)
{
  Z3_context c; /*in*/
  Z3_goal g; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  _res = Z3_goal_depth(c, g);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_goal_reset(
	value _v_c,
	value _v_g)
{
  Z3_context c; /*in*/
  Z3_goal g; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  Z3_goal_reset(c, g);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_goal_size(
	value _v_c,
	value _v_g)
{
  Z3_context c; /*in*/
  Z3_goal g; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  _res = Z3_goal_size(c, g);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_goal_formula(
	value _v_c,
	value _v_g,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_goal g; /*in*/
  unsigned int idx; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_goal_formula(c, g, idx);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_goal_num_exprs(
	value _v_c,
	value _v_g)
{
  Z3_context c; /*in*/
  Z3_goal g; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  _res = Z3_goal_num_exprs(c, g);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_goal_is_decided_sat(
	value _v_c,
	value _v_g)
{
  Z3_context c; /*in*/
  Z3_goal g; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  _res = Z3_goal_is_decided_sat(c, g);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_goal_is_decided_unsat(
	value _v_c,
	value _v_g)
{
  Z3_context c; /*in*/
  Z3_goal g; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  _res = Z3_goal_is_decided_unsat(c, g);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_goal_translate(
	value _v_source,
	value _v_g,
	value _v_target)
{
  Z3_context source; /*in*/
  Z3_goal g; /*in*/
  Z3_context target; /*in*/
  Z3_goal _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_source, &source, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  camlidl_ml2c_z3_Z3_context(_v_target, &target, _ctx);
  _res = Z3_goal_translate(source, g, target);
  _vres = camlidl_c2ml_z3_Z3_goal(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(source);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_goal_to_string(
	value _v_c,
	value _v_g)
{
  Z3_context c; /*in*/
  Z3_goal g; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  _res = Z3_goal_to_string(c, g);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_tactic(
	value _v_c,
	value _v_name)
{
  Z3_context c; /*in*/
  Z3_string name; /*in*/
  Z3_tactic _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_name, &name, _ctx);
  _res = Z3_mk_tactic(c, name);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_probe(
	value _v_c,
	value _v_name)
{
  Z3_context c; /*in*/
  Z3_string name; /*in*/
  Z3_probe _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_name, &name, _ctx);
  _res = Z3_mk_probe(c, name);
  _vres = camlidl_c2ml_z3_Z3_probe(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_and_then(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_tactic t1; /*in*/
  Z3_tactic t2; /*in*/
  Z3_tactic _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t2, &t2, _ctx);
  _res = Z3_tactic_and_then(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_or_else(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_tactic t1; /*in*/
  Z3_tactic t2; /*in*/
  Z3_tactic _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t2, &t2, _ctx);
  _res = Z3_tactic_or_else(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_par_or(
	value _v_c,
	value _v_ts)
{
  Z3_context c; /*in*/
  unsigned int num; /*in*/
  Z3_tactic const *ts; /*in*/
  Z3_tactic _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_ts);
  ts = camlidl_malloc(_c1 * sizeof(Z3_tactic const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_ts, _c2);
    camlidl_ml2c_z3_Z3_tactic(_v3, &ts[_c2], _ctx);
  }
  num = _c1;
  _res = Z3_tactic_par_or(c, num, ts);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_par_and_then(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_tactic t1; /*in*/
  Z3_tactic t2; /*in*/
  Z3_tactic _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t2, &t2, _ctx);
  _res = Z3_tactic_par_and_then(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_try_for(
	value _v_c,
	value _v_t,
	value _v_ms)
{
  Z3_context c; /*in*/
  Z3_tactic t; /*in*/
  unsigned int ms; /*in*/
  Z3_tactic _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t, &t, _ctx);
  ms = Int_val(_v_ms);
  _res = Z3_tactic_try_for(c, t, ms);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_when(
	value _v_c,
	value _v_p,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_probe p; /*in*/
  Z3_tactic t; /*in*/
  Z3_tactic _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p, &p, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t, &t, _ctx);
  _res = Z3_tactic_when(c, p, t);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_cond(
	value _v_c,
	value _v_p,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_probe p; /*in*/
  Z3_tactic t1; /*in*/
  Z3_tactic t2; /*in*/
  Z3_tactic _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p, &p, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t2, &t2, _ctx);
  _res = Z3_tactic_cond(c, p, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_repeat(
	value _v_c,
	value _v_t,
	value _v_max)
{
  Z3_context c; /*in*/
  Z3_tactic t; /*in*/
  unsigned int max; /*in*/
  Z3_tactic _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t, &t, _ctx);
  max = Int_val(_v_max);
  _res = Z3_tactic_repeat(c, t, max);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_skip(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_tactic _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_tactic_skip(c);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_fail(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_tactic _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_tactic_fail(c);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_fail_if(
	value _v_c,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_probe p; /*in*/
  Z3_tactic _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p, &p, _ctx);
  _res = Z3_tactic_fail_if(c, p);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_fail_if_not_decided(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_tactic _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_tactic_fail_if_not_decided(c);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_using_params(
	value _v_c,
	value _v_t,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_tactic t; /*in*/
  Z3_params p; /*in*/
  Z3_tactic _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_params(_v_p, &p, _ctx);
  _res = Z3_tactic_using_params(c, t, p);
  _vres = camlidl_c2ml_z3_Z3_tactic(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_probe_const(
	value _v_x,
	value _v_val)
{
  Z3_context x; /*in*/
  double val; /*in*/
  Z3_probe _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_x, &x, _ctx);
  val = Double_val(_v_val);
  _res = Z3_probe_const(x, val);
  _vres = camlidl_c2ml_z3_Z3_probe(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(x);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_probe_lt(
	value _v_x,
	value _v_p1,
	value _v_p2)
{
  Z3_context x; /*in*/
  Z3_probe p1; /*in*/
  Z3_probe p2; /*in*/
  Z3_probe _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_x, &x, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p1, &p1, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p2, &p2, _ctx);
  _res = Z3_probe_lt(x, p1, p2);
  _vres = camlidl_c2ml_z3_Z3_probe(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(x);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_probe_gt(
	value _v_x,
	value _v_p1,
	value _v_p2)
{
  Z3_context x; /*in*/
  Z3_probe p1; /*in*/
  Z3_probe p2; /*in*/
  Z3_probe _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_x, &x, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p1, &p1, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p2, &p2, _ctx);
  _res = Z3_probe_gt(x, p1, p2);
  _vres = camlidl_c2ml_z3_Z3_probe(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(x);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_probe_le(
	value _v_x,
	value _v_p1,
	value _v_p2)
{
  Z3_context x; /*in*/
  Z3_probe p1; /*in*/
  Z3_probe p2; /*in*/
  Z3_probe _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_x, &x, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p1, &p1, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p2, &p2, _ctx);
  _res = Z3_probe_le(x, p1, p2);
  _vres = camlidl_c2ml_z3_Z3_probe(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(x);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_probe_ge(
	value _v_x,
	value _v_p1,
	value _v_p2)
{
  Z3_context x; /*in*/
  Z3_probe p1; /*in*/
  Z3_probe p2; /*in*/
  Z3_probe _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_x, &x, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p1, &p1, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p2, &p2, _ctx);
  _res = Z3_probe_ge(x, p1, p2);
  _vres = camlidl_c2ml_z3_Z3_probe(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(x);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_probe_eq(
	value _v_x,
	value _v_p1,
	value _v_p2)
{
  Z3_context x; /*in*/
  Z3_probe p1; /*in*/
  Z3_probe p2; /*in*/
  Z3_probe _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_x, &x, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p1, &p1, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p2, &p2, _ctx);
  _res = Z3_probe_eq(x, p1, p2);
  _vres = camlidl_c2ml_z3_Z3_probe(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(x);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_probe_and(
	value _v_x,
	value _v_p1,
	value _v_p2)
{
  Z3_context x; /*in*/
  Z3_probe p1; /*in*/
  Z3_probe p2; /*in*/
  Z3_probe _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_x, &x, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p1, &p1, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p2, &p2, _ctx);
  _res = Z3_probe_and(x, p1, p2);
  _vres = camlidl_c2ml_z3_Z3_probe(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(x);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_probe_or(
	value _v_x,
	value _v_p1,
	value _v_p2)
{
  Z3_context x; /*in*/
  Z3_probe p1; /*in*/
  Z3_probe p2; /*in*/
  Z3_probe _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_x, &x, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p1, &p1, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p2, &p2, _ctx);
  _res = Z3_probe_or(x, p1, p2);
  _vres = camlidl_c2ml_z3_Z3_probe(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(x);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_probe_not(
	value _v_x,
	value _v_p)
{
  Z3_context x; /*in*/
  Z3_probe p; /*in*/
  Z3_probe _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_x, &x, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p, &p, _ctx);
  _res = Z3_probe_not(x, p);
  _vres = camlidl_c2ml_z3_Z3_probe(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(x);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_num_tactics(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_num_tactics(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_tactic_name(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_tactic_name(c, i);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_num_probes(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_num_probes(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_probe_name(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_probe_name(c, i);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_get_help(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_tactic t; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t, &t, _ctx);
  _res = Z3_tactic_get_help(c, t);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_get_param_descrs(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_tactic t; /*in*/
  Z3_param_descrs _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t, &t, _ctx);
  _res = Z3_tactic_get_param_descrs(c, t);
  _vres = camlidl_c2ml_z3_Z3_param_descrs(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_get_descr(
	value _v_c,
	value _v_name)
{
  Z3_context c; /*in*/
  Z3_string name; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_name, &name, _ctx);
  _res = Z3_tactic_get_descr(c, name);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_probe_get_descr(
	value _v_c,
	value _v_name)
{
  Z3_context c; /*in*/
  Z3_string name; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_string(_v_name, &name, _ctx);
  _res = Z3_probe_get_descr(c, name);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_probe_apply(
	value _v_c,
	value _v_p,
	value _v_g)
{
  Z3_context c; /*in*/
  Z3_probe p; /*in*/
  Z3_goal g; /*in*/
  double _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_probe(_v_p, &p, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  _res = Z3_probe_apply(c, p, g);
  _vres = copy_double(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_apply(
	value _v_c,
	value _v_t,
	value _v_g)
{
  Z3_context c; /*in*/
  Z3_tactic t; /*in*/
  Z3_goal g; /*in*/
  Z3_apply_result _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  _res = Z3_tactic_apply(c, t, g);
  _vres = camlidl_c2ml_z3_Z3_apply_result(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_tactic_apply_ex(
	value _v_c,
	value _v_t,
	value _v_g,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_tactic t; /*in*/
  Z3_goal g; /*in*/
  Z3_params p; /*in*/
  Z3_apply_result _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_goal(_v_g, &g, _ctx);
  camlidl_ml2c_z3_Z3_params(_v_p, &p, _ctx);
  _res = Z3_tactic_apply_ex(c, t, g, p);
  _vres = camlidl_c2ml_z3_Z3_apply_result(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_apply_result_to_string(
	value _v_c,
	value _v_r)
{
  Z3_context c; /*in*/
  Z3_apply_result r; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_apply_result(_v_r, &r, _ctx);
  _res = Z3_apply_result_to_string(c, r);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_apply_result_get_num_subgoals(
	value _v_c,
	value _v_r)
{
  Z3_context c; /*in*/
  Z3_apply_result r; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_apply_result(_v_r, &r, _ctx);
  _res = Z3_apply_result_get_num_subgoals(c, r);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_apply_result_get_subgoal(
	value _v_c,
	value _v_r,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_apply_result r; /*in*/
  unsigned int i; /*in*/
  Z3_goal _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_apply_result(_v_r, &r, _ctx);
  i = Int_val(_v_i);
  _res = Z3_apply_result_get_subgoal(c, r, i);
  _vres = camlidl_c2ml_z3_Z3_goal(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_apply_result_convert_model(
	value _v_c,
	value _v_r,
	value _v_i,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_apply_result r; /*in*/
  unsigned int i; /*in*/
  Z3_model m; /*in*/
  Z3_model _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_apply_result(_v_r, &r, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  _res = Z3_apply_result_convert_model(c, r, i, m);
  _vres = camlidl_c2ml_z3_Z3_model(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_solver(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_solver _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_solver(c);
  _vres = camlidl_c2ml_z3_Z3_solver(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_simple_solver(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_solver _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_simple_solver(c);
  _vres = camlidl_c2ml_z3_Z3_solver(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_solver_for_logic(
	value _v_c,
	value _v_logic)
{
  Z3_context c; /*in*/
  Z3_symbol logic; /*in*/
  Z3_solver _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_logic, &logic, _ctx);
  _res = Z3_mk_solver_for_logic(c, logic);
  _vres = camlidl_c2ml_z3_Z3_solver(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_solver_from_tactic(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_tactic t; /*in*/
  Z3_solver _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_tactic(_v_t, &t, _ctx);
  _res = Z3_mk_solver_from_tactic(c, t);
  _vres = camlidl_c2ml_z3_Z3_solver(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_solver_get_help(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  _res = Z3_solver_get_help(c, s);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_solver_get_param_descrs(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  Z3_param_descrs _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  _res = Z3_solver_get_param_descrs(c, s);
  _vres = camlidl_c2ml_z3_Z3_param_descrs(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_solver_set_params(
	value _v_c,
	value _v_s,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  Z3_params p; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  camlidl_ml2c_z3_Z3_params(_v_p, &p, _ctx);
  Z3_solver_set_params(c, s, p);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_solver_push(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  Z3_solver_push(c, s);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_solver_pop(
	value _v_c,
	value _v_s,
	value _v_n)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  unsigned int n; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  n = Int_val(_v_n);
  Z3_solver_pop(c, s, n);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_solver_reset(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  Z3_solver_reset(c, s);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_solver_get_num_scopes(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  _res = Z3_solver_get_num_scopes(c, s);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_solver_assert(
	value _v_c,
	value _v_s,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  Z3_ast a; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  Z3_solver_assert(c, s, a);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return Val_unit;
}

value camlidl_z3_Z3_solver_get_assertions(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  Z3_ast_vector _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  _res = Z3_solver_get_assertions(c, s);
  _vres = camlidl_c2ml_z3_Z3_ast_vector(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_solver_check(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  Z3_lbool _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  _res = Z3_solver_check(c, s);
  _vres = camlidl_c2ml_z3_Z3_lbool(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_solver_check_assumptions(
	value _v_c,
	value _v_s,
	value _v_assumptions)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  unsigned int num_assumptions; /*in*/
  Z3_ast const *assumptions; /*in*/
  Z3_lbool _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_assumptions);
  assumptions = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_assumptions, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &assumptions[_c2], _ctx);
  }
  num_assumptions = _c1;
  _res = Z3_solver_check_assumptions(c, s, num_assumptions, assumptions);
  _vres = camlidl_c2ml_z3_Z3_lbool(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_solver_get_model(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  Z3_model _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  _res = Z3_solver_get_model(c, s);
  _vres = camlidl_c2ml_z3_Z3_model(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_solver_get_proof(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  _res = Z3_solver_get_proof(c, s);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_solver_get_unsat_core(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  Z3_ast_vector _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  _res = Z3_solver_get_unsat_core(c, s);
  _vres = camlidl_c2ml_z3_Z3_ast_vector(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_solver_get_reason_unknown(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  _res = Z3_solver_get_reason_unknown(c, s);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_solver_get_statistics(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  Z3_stats _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  _res = Z3_solver_get_statistics(c, s);
  _vres = camlidl_c2ml_z3_Z3_stats(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_solver_to_string(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  _res = Z3_solver_to_string(c, s);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_stats_to_string(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_stats s; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_stats(_v_s, &s, _ctx);
  _res = Z3_stats_to_string(c, s);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_stats_size(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_stats s; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_stats(_v_s, &s, _ctx);
  _res = Z3_stats_size(c, s);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_stats_get_key(
	value _v_c,
	value _v_s,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_stats s; /*in*/
  unsigned int idx; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_stats(_v_s, &s, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_stats_get_key(c, s, idx);
  _vres = camlidl_c2ml_z3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_stats_is_uint(
	value _v_c,
	value _v_s,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_stats s; /*in*/
  unsigned int idx; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_stats(_v_s, &s, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_stats_is_uint(c, s, idx);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_stats_is_double(
	value _v_c,
	value _v_s,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_stats s; /*in*/
  unsigned int idx; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_stats(_v_s, &s, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_stats_is_double(c, s, idx);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_stats_get_uint_value(
	value _v_c,
	value _v_s,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_stats s; /*in*/
  unsigned int idx; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_stats(_v_s, &s, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_stats_get_uint_value(c, s, idx);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_stats_get_double_value(
	value _v_c,
	value _v_s,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_stats s; /*in*/
  unsigned int idx; /*in*/
  double _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_stats(_v_s, &s, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_stats_get_double_value(c, s, idx);
  _vres = copy_double(_res);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_get_implied_equalities(
	value _v_c,
	value _v_s,
	value _v_terms)
{
  Z3_context c; /*in*/
  Z3_solver s; /*in*/
  unsigned int num_terms; /*in*/
  Z3_ast const *terms; /*in*/
  unsigned int *class_ids; /*out*/
  Z3_lbool _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  value _v5;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_solver(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_terms);
  terms = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_terms, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &terms[_c2], _ctx);
  }
  num_terms = _c1;
  class_ids = camlidl_malloc(num_terms * sizeof(unsigned int ), _ctx);
  _res = Z3_get_implied_equalities(c, s, num_terms, terms, class_ids);
  Begin_roots_block(_vres, 2)
    _vres[0] = camlidl_c2ml_z3_Z3_lbool(&_res, _ctx);
    _vres[1] = camlidl_alloc(num_terms, 0);
    for (_c4 = 0; _c4 < num_terms; _c4++) {
      _v5 = Val_int(class_ids[_c4]);
      modify(&Field(_vres[1], _c4), _v5);
    }
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
check_error_code(c);
  /* end user-supplied deallocation sequence */
  return _vresult;
}

void camlidl_ml2c_z3V3_Z3_symbol(value _v1, Z3_symbol * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_symbol *) Bp_val(_v1));
}

value camlidl_c2ml_z3V3_Z3_symbol(Z3_symbol * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_symbol) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_symbol *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3V3_Z3_literals(value _v1, Z3_literals * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_literals *) Bp_val(_v1));
}

value camlidl_c2ml_z3V3_Z3_literals(Z3_literals * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_literals) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_literals *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3V3_Z3_theory(value _v1, Z3_theory * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_theory *) Bp_val(_v1));
}

value camlidl_c2ml_z3V3_Z3_theory(Z3_theory * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_theory) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_theory *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3V3_Z3_config(value _v1, Z3_config * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_config *) Bp_val(_v1));
}

value camlidl_c2ml_z3V3_Z3_config(Z3_config * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_config) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_config *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3V3_Z3_context(value _v1, Z3_context * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_context *) Bp_val(_v1));
}

value camlidl_c2ml_z3V3_Z3_context(Z3_context * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_context) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_context *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3V3_Z3_sort(value _v1, Z3_sort * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_sort *) Bp_val(_v1));
}

value camlidl_c2ml_z3V3_Z3_sort(Z3_sort * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_sort) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_sort *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3V3_Z3_func_decl(value _v1, Z3_func_decl * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_func_decl *) Bp_val(_v1));
}

value camlidl_c2ml_z3V3_Z3_func_decl(Z3_func_decl * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_func_decl) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_func_decl *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3V3_Z3_ast(value _v1, Z3_ast * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_ast *) Bp_val(_v1));
}

value camlidl_c2ml_z3V3_Z3_ast(Z3_ast * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_ast) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_ast *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3V3_Z3_app(value _v1, Z3_app * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_app *) Bp_val(_v1));
}

value camlidl_c2ml_z3V3_Z3_app(Z3_app * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_app) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_app *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3V3_Z3_pattern(value _v1, Z3_pattern * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_pattern *) Bp_val(_v1));
}

value camlidl_c2ml_z3V3_Z3_pattern(Z3_pattern * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_pattern) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_pattern *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3V3_Z3_model(value _v1, Z3_model * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_model *) Bp_val(_v1));
}

value camlidl_c2ml_z3V3_Z3_model(Z3_model * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_model) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_model *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3V3_Z3_constructor(value _v1, Z3_constructor * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_constructor *) Bp_val(_v1));
}

value camlidl_c2ml_z3V3_Z3_constructor(Z3_constructor * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_constructor) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_constructor *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3V3_Z3_constructor_list(value _v1, Z3_constructor_list * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_constructor_list *) Bp_val(_v1));
}

value camlidl_c2ml_z3V3_Z3_constructor_list(Z3_constructor_list * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_constructor_list) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_constructor_list *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3V3_Z3_string(value _v1, Z3_string * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_malloc_string(_v1, _ctx);
}

value camlidl_c2ml_z3V3_Z3_string(Z3_string * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = copy_string((*_c2));
  return _v1;
}

int camlidl_transl_table_z3V3_enum_1[3] = {
  Z3_L_FALSE,
  Z3_L_UNDEF,
  Z3_L_TRUE,
};

void camlidl_ml2c_z3V3_Z3_lbool(value _v1, Z3_lbool * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3V3_enum_1[Int_val(_v1)];
}

value camlidl_c2ml_z3V3_Z3_lbool(Z3_lbool * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case Z3_L_FALSE: _v1 = Val_int(0); break;
  case Z3_L_UNDEF: _v1 = Val_int(1); break;
  case Z3_L_TRUE: _v1 = Val_int(2); break;
  default: invalid_argument("typedef Z3_lbool: bad enum  value");
  }
  return _v1;
}

int camlidl_transl_table_z3V3_enum_2[2] = {
  Z3_INT_SYMBOL,
  Z3_STRING_SYMBOL,
};

void camlidl_ml2c_z3V3_Z3_symbol_kind(value _v1, Z3_symbol_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3V3_enum_2[Int_val(_v1)];
}

value camlidl_c2ml_z3V3_Z3_symbol_kind(Z3_symbol_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case Z3_INT_SYMBOL: _v1 = Val_int(0); break;
  case Z3_STRING_SYMBOL: _v1 = Val_int(1); break;
  default: invalid_argument("typedef Z3_symbol_kind: bad enum  value");
  }
  return _v1;
}

int camlidl_transl_table_z3V3_enum_3[7] = {
  Z3_PARAMETER_INT,
  Z3_PARAMETER_DOUBLE,
  Z3_PARAMETER_RATIONAL,
  Z3_PARAMETER_SYMBOL,
  Z3_PARAMETER_SORT,
  Z3_PARAMETER_AST,
  Z3_PARAMETER_FUNC_DECL,
};

void camlidl_ml2c_z3V3_Z3_parameter_kind(value _v1, Z3_parameter_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3V3_enum_3[Int_val(_v1)];
}

value camlidl_c2ml_z3V3_Z3_parameter_kind(Z3_parameter_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3V3_enum_3, 7, "typedef Z3_parameter_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3V3_enum_4[10] = {
  Z3_UNINTERPRETED_SORT,
  Z3_BOOL_SORT,
  Z3_INT_SORT,
  Z3_REAL_SORT,
  Z3_BV_SORT,
  Z3_ARRAY_SORT,
  Z3_DATATYPE_SORT,
  Z3_RELATION_SORT,
  Z3_FINITE_DOMAIN_SORT,
  Z3_UNKNOWN_SORT,
};

void camlidl_ml2c_z3V3_Z3_sort_kind(value _v1, Z3_sort_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3V3_enum_4[Int_val(_v1)];
}

value camlidl_c2ml_z3V3_Z3_sort_kind(Z3_sort_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3V3_enum_4, 10, "typedef Z3_sort_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3V3_enum_5[7] = {
  Z3_NUMERAL_AST,
  Z3_APP_AST,
  Z3_VAR_AST,
  Z3_QUANTIFIER_AST,
  Z3_SORT_AST,
  Z3_FUNC_DECL_AST,
  Z3_UNKNOWN_AST,
};

void camlidl_ml2c_z3V3_Z3_ast_kind(value _v1, Z3_ast_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3V3_enum_5[Int_val(_v1)];
}

value camlidl_c2ml_z3V3_Z3_ast_kind(Z3_ast_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3V3_enum_5, 7, "typedef Z3_ast_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3V3_enum_6[152] = {
  Z3_OP_TRUE,
  Z3_OP_FALSE,
  Z3_OP_EQ,
  Z3_OP_DISTINCT,
  Z3_OP_ITE,
  Z3_OP_AND,
  Z3_OP_OR,
  Z3_OP_IFF,
  Z3_OP_XOR,
  Z3_OP_NOT,
  Z3_OP_IMPLIES,
  Z3_OP_OEQ,
  Z3_OP_ANUM,
  Z3_OP_AGNUM,
  Z3_OP_LE,
  Z3_OP_GE,
  Z3_OP_LT,
  Z3_OP_GT,
  Z3_OP_ADD,
  Z3_OP_SUB,
  Z3_OP_UMINUS,
  Z3_OP_MUL,
  Z3_OP_DIV,
  Z3_OP_IDIV,
  Z3_OP_REM,
  Z3_OP_MOD,
  Z3_OP_TO_REAL,
  Z3_OP_TO_INT,
  Z3_OP_IS_INT,
  Z3_OP_POWER,
  Z3_OP_STORE,
  Z3_OP_SELECT,
  Z3_OP_CONST_ARRAY,
  Z3_OP_ARRAY_MAP,
  Z3_OP_ARRAY_DEFAULT,
  Z3_OP_SET_UNION,
  Z3_OP_SET_INTERSECT,
  Z3_OP_SET_DIFFERENCE,
  Z3_OP_SET_COMPLEMENT,
  Z3_OP_SET_SUBSET,
  Z3_OP_AS_ARRAY,
  Z3_OP_BNUM,
  Z3_OP_BIT1,
  Z3_OP_BIT0,
  Z3_OP_BNEG,
  Z3_OP_BADD,
  Z3_OP_BSUB,
  Z3_OP_BMUL,
  Z3_OP_BSDIV,
  Z3_OP_BUDIV,
  Z3_OP_BSREM,
  Z3_OP_BUREM,
  Z3_OP_BSMOD,
  Z3_OP_BSDIV0,
  Z3_OP_BUDIV0,
  Z3_OP_BSREM0,
  Z3_OP_BUREM0,
  Z3_OP_BSMOD0,
  Z3_OP_ULEQ,
  Z3_OP_SLEQ,
  Z3_OP_UGEQ,
  Z3_OP_SGEQ,
  Z3_OP_ULT,
  Z3_OP_SLT,
  Z3_OP_UGT,
  Z3_OP_SGT,
  Z3_OP_BAND,
  Z3_OP_BOR,
  Z3_OP_BNOT,
  Z3_OP_BXOR,
  Z3_OP_BNAND,
  Z3_OP_BNOR,
  Z3_OP_BXNOR,
  Z3_OP_CONCAT,
  Z3_OP_SIGN_EXT,
  Z3_OP_ZERO_EXT,
  Z3_OP_EXTRACT,
  Z3_OP_REPEAT,
  Z3_OP_BREDOR,
  Z3_OP_BREDAND,
  Z3_OP_BCOMP,
  Z3_OP_BSHL,
  Z3_OP_BLSHR,
  Z3_OP_BASHR,
  Z3_OP_ROTATE_LEFT,
  Z3_OP_ROTATE_RIGHT,
  Z3_OP_EXT_ROTATE_LEFT,
  Z3_OP_EXT_ROTATE_RIGHT,
  Z3_OP_INT2BV,
  Z3_OP_BV2INT,
  Z3_OP_CARRY,
  Z3_OP_XOR3,
  Z3_OP_PR_UNDEF,
  Z3_OP_PR_TRUE,
  Z3_OP_PR_ASSERTED,
  Z3_OP_PR_GOAL,
  Z3_OP_PR_MODUS_PONENS,
  Z3_OP_PR_REFLEXIVITY,
  Z3_OP_PR_SYMMETRY,
  Z3_OP_PR_TRANSITIVITY,
  Z3_OP_PR_TRANSITIVITY_STAR,
  Z3_OP_PR_MONOTONICITY,
  Z3_OP_PR_QUANT_INTRO,
  Z3_OP_PR_DISTRIBUTIVITY,
  Z3_OP_PR_AND_ELIM,
  Z3_OP_PR_NOT_OR_ELIM,
  Z3_OP_PR_REWRITE,
  Z3_OP_PR_REWRITE_STAR,
  Z3_OP_PR_PULL_QUANT,
  Z3_OP_PR_PULL_QUANT_STAR,
  Z3_OP_PR_PUSH_QUANT,
  Z3_OP_PR_ELIM_UNUSED_VARS,
  Z3_OP_PR_DER,
  Z3_OP_PR_QUANT_INST,
  Z3_OP_PR_HYPOTHESIS,
  Z3_OP_PR_LEMMA,
  Z3_OP_PR_UNIT_RESOLUTION,
  Z3_OP_PR_IFF_TRUE,
  Z3_OP_PR_IFF_FALSE,
  Z3_OP_PR_COMMUTATIVITY,
  Z3_OP_PR_DEF_AXIOM,
  Z3_OP_PR_DEF_INTRO,
  Z3_OP_PR_APPLY_DEF,
  Z3_OP_PR_IFF_OEQ,
  Z3_OP_PR_NNF_POS,
  Z3_OP_PR_NNF_NEG,
  Z3_OP_PR_NNF_STAR,
  Z3_OP_PR_CNF_STAR,
  Z3_OP_PR_SKOLEMIZE,
  Z3_OP_PR_MODUS_PONENS_OEQ,
  Z3_OP_PR_TH_LEMMA,
  Z3_OP_PR_HYPER_RESOLVE,
  Z3_OP_RA_STORE,
  Z3_OP_RA_EMPTY,
  Z3_OP_RA_IS_EMPTY,
  Z3_OP_RA_JOIN,
  Z3_OP_RA_UNION,
  Z3_OP_RA_WIDEN,
  Z3_OP_RA_PROJECT,
  Z3_OP_RA_FILTER,
  Z3_OP_RA_NEGATION_FILTER,
  Z3_OP_RA_RENAME,
  Z3_OP_RA_COMPLEMENT,
  Z3_OP_RA_SELECT,
  Z3_OP_RA_CLONE,
  Z3_OP_FD_LT,
  Z3_OP_LABEL,
  Z3_OP_LABEL_LIT,
  Z3_OP_DT_CONSTRUCTOR,
  Z3_OP_DT_RECOGNISER,
  Z3_OP_DT_ACCESSOR,
  Z3_OP_UNINTERPRETED,
};

void camlidl_ml2c_z3V3_Z3_decl_kind(value _v1, Z3_decl_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3V3_enum_6[Int_val(_v1)];
}

value camlidl_c2ml_z3V3_Z3_decl_kind(Z3_decl_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3V3_enum_6, 152, "typedef Z3_decl_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3V3_enum_7[7] = {
  Z3_PK_UINT,
  Z3_PK_BOOL,
  Z3_PK_DOUBLE,
  Z3_PK_SYMBOL,
  Z3_PK_STRING,
  Z3_PK_OTHER,
  Z3_PK_INVALID,
};

void camlidl_ml2c_z3V3_Z3_param_kind(value _v1, Z3_param_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3V3_enum_7[Int_val(_v1)];
}

value camlidl_c2ml_z3V3_Z3_param_kind(Z3_param_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3V3_enum_7, 7, "typedef Z3_param_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3V3_enum_8[8] = {
  Z3_NO_FAILURE,
  Z3_UNKNOWN,
  Z3_TIMEOUT,
  Z3_MEMOUT_WATERMARK,
  Z3_CANCELED,
  Z3_NUM_CONFLICTS,
  Z3_THEORY,
  Z3_QUANTIFIERS,
};

void camlidl_ml2c_z3V3_Z3_search_failure(value _v1, Z3_search_failure * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3V3_enum_8[Int_val(_v1)];
}

value camlidl_c2ml_z3V3_Z3_search_failure(Z3_search_failure * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3V3_enum_8, 8, "typedef Z3_search_failure: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3V3_enum_9[4] = {
  Z3_PRINT_SMTLIB_FULL,
  Z3_PRINT_LOW_LEVEL,
  Z3_PRINT_SMTLIB_COMPLIANT,
  Z3_PRINT_SMTLIB2_COMPLIANT,
};

void camlidl_ml2c_z3V3_Z3_ast_print_mode(value _v1, Z3_ast_print_mode * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3V3_enum_9[Int_val(_v1)];
}

value camlidl_c2ml_z3V3_Z3_ast_print_mode(Z3_ast_print_mode * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case Z3_PRINT_SMTLIB_FULL: _v1 = Val_int(0); break;
  case Z3_PRINT_LOW_LEVEL: _v1 = Val_int(1); break;
  case Z3_PRINT_SMTLIB_COMPLIANT: _v1 = Val_int(2); break;
  case Z3_PRINT_SMTLIB2_COMPLIANT: _v1 = Val_int(3); break;
  default: invalid_argument("typedef Z3_ast_print_mode: bad enum  value");
  }
  return _v1;
}

value camlidl_z3V3_Z3_mk_config(value _unit)
{
  Z3_config _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  _res = Z3_mk_config();
  _vres = camlidl_c2ml_z3V3_Z3_config(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_del_config(
	value _v_c)
{
  Z3_config c; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_config(_v_c, &c, _ctx);
  Z3_del_config(c);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_set_param_value(
	value _v_c,
	value _v_param_id,
	value _v_param_value)
{
  Z3_config c; /*in*/
  Z3_string param_id; /*in*/
  Z3_string param_value; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_config(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_param_id, &param_id, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_param_value, &param_value, _ctx);
  Z3_set_param_value(c, param_id, param_value);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_mk_context(
	value _v_c)
{
  Z3_config c; /*in*/
  Z3_context _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_config(_v_c, &c, _ctx);
  _res = Z3_mk_context(c);
  _vres = camlidl_c2ml_z3V3_Z3_context(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
Z3_set_error_handler(_res, caml_z3_error_handler);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3V3_Z3_del_context(
	value _v_c)
{
  Z3_context c; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  Z3_del_context(c);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_update_param_value(
	value _v_c,
	value _v_param_id,
	value _v_param_value)
{
  Z3_context c; /*in*/
  Z3_string param_id; /*in*/
  Z3_string param_value; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_param_id, &param_id, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_param_value, &param_value, _ctx);
  Z3_update_param_value(c, param_id, param_value);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_get_param_value(
	value _v_c,
	value _v_param_id)
{
  Z3_context c; /*in*/
  Z3_string param_id; /*in*/
  Z3_string *param_value; /*out*/
  Z3_string _c1;
  value _v2;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_param_id, &param_id, _ctx);
  param_value = &_c1;
  Z3_get_param_value(c, param_id, param_value);
  if (param_value == NULL) {
    _vres = Val_int(0);
  } else {
    _v2 = camlidl_c2ml_z3V3_Z3_string(&*param_value, _ctx);
    Begin_root(_v2)
      _vres = camlidl_alloc_small(1, 0);
      Field(_vres, 0) = _v2;
    End_roots();
  }
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_int_symbol(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  int i; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_mk_int_symbol(c, i);
  _vres = camlidl_c2ml_z3V3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_string_symbol(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_string s; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_s, &s, _ctx);
  _res = Z3_mk_string_symbol(c, s);
  _vres = camlidl_c2ml_z3V3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_uninterpreted_sort(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_mk_uninterpreted_sort(c, s);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bool_sort(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_bool_sort(c);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_int_sort(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_int_sort(c);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_real_sort(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_real_sort(c);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bv_sort(
	value _v_c,
	value _v_sz)
{
  Z3_context c; /*in*/
  unsigned int sz; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  sz = Int_val(_v_sz);
  _res = Z3_mk_bv_sort(c, sz);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_finite_domain_sort(
	value _v_c,
	value _v_name,
	value _v_size)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  __int64 size; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_name, &name, _ctx);
  size = Int64_val(_v_size);
  _res = Z3_mk_finite_domain_sort(c, name, size);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_array_sort(
	value _v_c,
	value _v_domain,
	value _v_range)
{
  Z3_context c; /*in*/
  Z3_sort domain; /*in*/
  Z3_sort range; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_domain, &domain, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_range, &range, _ctx);
  _res = Z3_mk_array_sort(c, domain, range);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_tuple_sort(
	value _v_c,
	value _v_mk_tuple_name,
	value _v_field_names,
	value _v_field_sorts)
{
  Z3_context c; /*in*/
  Z3_symbol mk_tuple_name; /*in*/
  unsigned int num_fields; /*in*/
  Z3_symbol const *field_names; /*in*/
  Z3_sort const *field_sorts; /*in*/
  Z3_func_decl *mk_tuple_decl; /*out*/
  Z3_func_decl *proj_decl; /*out*/
  Z3_sort _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  Z3_func_decl _c7;
  mlsize_t _c8;
  value _v9;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_mk_tuple_name, &mk_tuple_name, _ctx);
  _c1 = Wosize_val(_v_field_names);
  field_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_field_names, _c2);
    camlidl_ml2c_z3V3_Z3_symbol(_v3, &field_names[_c2], _ctx);
  }
  num_fields = _c1;
  _c4 = Wosize_val(_v_field_sorts);
  field_sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_field_sorts, _c5);
    camlidl_ml2c_z3V3_Z3_sort(_v6, &field_sorts[_c5], _ctx);
  }
  num_fields = _c4;
  mk_tuple_decl = &_c7;
  proj_decl = camlidl_malloc(num_fields * sizeof(Z3_func_decl ), _ctx);
  _res = Z3_mk_tuple_sort(c, mk_tuple_name, num_fields, field_names, field_sorts, mk_tuple_decl, proj_decl);
  Begin_roots_block(_vres, 3)
    _vres[0] = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
    _vres[1] = camlidl_c2ml_z3V3_Z3_func_decl(&*mk_tuple_decl, _ctx);
    _vres[2] = camlidl_alloc(num_fields, 0);
    Begin_root(_vres[2])
      for (_c8 = 0; _c8 < num_fields; _c8++) {
        _v9 = camlidl_c2ml_z3V3_Z3_func_decl(&proj_decl[_c8], _ctx);
        modify(&Field(_vres[2], _c8), _v9);
      }
    End_roots()
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_mk_enumeration_sort(
	value _v_c,
	value _v_name,
	value _v_enum_names)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  unsigned int n; /*in*/
  Z3_symbol const *enum_names; /*in*/
  Z3_func_decl *enum_consts; /*out*/
  Z3_func_decl *enum_testers; /*out*/
  Z3_sort _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  value _v5;
  mlsize_t _c6;
  value _v7;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_name, &name, _ctx);
  _c1 = Wosize_val(_v_enum_names);
  enum_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_enum_names, _c2);
    camlidl_ml2c_z3V3_Z3_symbol(_v3, &enum_names[_c2], _ctx);
  }
  n = _c1;
  enum_consts = camlidl_malloc(n * sizeof(Z3_func_decl ), _ctx);
  enum_testers = camlidl_malloc(n * sizeof(Z3_func_decl ), _ctx);
  _res = Z3_mk_enumeration_sort(c, name, n, enum_names, enum_consts, enum_testers);
  Begin_roots_block(_vres, 3)
    _vres[0] = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
    _vres[1] = camlidl_alloc(n, 0);
    Begin_root(_vres[1])
      for (_c4 = 0; _c4 < n; _c4++) {
        _v5 = camlidl_c2ml_z3V3_Z3_func_decl(&enum_consts[_c4], _ctx);
        modify(&Field(_vres[1], _c4), _v5);
      }
    End_roots()
    _vres[2] = camlidl_alloc(n, 0);
    Begin_root(_vres[2])
      for (_c6 = 0; _c6 < n; _c6++) {
        _v7 = camlidl_c2ml_z3V3_Z3_func_decl(&enum_testers[_c6], _ctx);
        modify(&Field(_vres[2], _c6), _v7);
      }
    End_roots()
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_mk_list_sort(
	value _v_c,
	value _v_name,
	value _v_elem_sort)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  Z3_sort elem_sort; /*in*/
  Z3_func_decl *nil_decl; /*out*/
  Z3_func_decl *is_nil_decl; /*out*/
  Z3_func_decl *cons_decl; /*out*/
  Z3_func_decl *is_cons_decl; /*out*/
  Z3_func_decl *head_decl; /*out*/
  Z3_func_decl *tail_decl; /*out*/
  Z3_sort _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  Z3_func_decl _c1;
  Z3_func_decl _c2;
  Z3_func_decl _c3;
  Z3_func_decl _c4;
  Z3_func_decl _c5;
  Z3_func_decl _c6;
  value _vresult;
  value _vres[7] = { 0, 0, 0, 0, 0, 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_name, &name, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_elem_sort, &elem_sort, _ctx);
  nil_decl = &_c1;
  is_nil_decl = &_c2;
  cons_decl = &_c3;
  is_cons_decl = &_c4;
  head_decl = &_c5;
  tail_decl = &_c6;
  _res = Z3_mk_list_sort(c, name, elem_sort, nil_decl, is_nil_decl, cons_decl, is_cons_decl, head_decl, tail_decl);
  Begin_roots_block(_vres, 7)
    _vres[0] = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
    _vres[1] = camlidl_c2ml_z3V3_Z3_func_decl(&*nil_decl, _ctx);
    _vres[2] = camlidl_c2ml_z3V3_Z3_func_decl(&*is_nil_decl, _ctx);
    _vres[3] = camlidl_c2ml_z3V3_Z3_func_decl(&*cons_decl, _ctx);
    _vres[4] = camlidl_c2ml_z3V3_Z3_func_decl(&*is_cons_decl, _ctx);
    _vres[5] = camlidl_c2ml_z3V3_Z3_func_decl(&*head_decl, _ctx);
    _vres[6] = camlidl_c2ml_z3V3_Z3_func_decl(&*tail_decl, _ctx);
    _vresult = camlidl_alloc_small(7, 0);
    { mlsize_t _c7;
      for (_c7 = 0; _c7 < 7; _c7++) Field(_vresult, _c7) = _vres[_c7];
    }
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_mk_constructor(
	value _v_c,
	value _v_name,
	value _v_recognizer,
	value _v_field_names,
	value _v_sorts,
	value _v_sort_refs)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  Z3_symbol recognizer; /*in*/
  unsigned int num_fields; /*in*/
  Z3_symbol const *field_names; /*in*/
  Z3_sort const *sorts; /*in*/
  unsigned int *sort_refs; /*in*/
  Z3_constructor _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_name, &name, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_recognizer, &recognizer, _ctx);
  _c1 = Wosize_val(_v_field_names);
  field_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_field_names, _c2);
    camlidl_ml2c_z3V3_Z3_symbol(_v3, &field_names[_c2], _ctx);
  }
  num_fields = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3V3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_fields = _c4;
  _c7 = Wosize_val(_v_sort_refs);
  sort_refs = camlidl_malloc(_c7 * sizeof(unsigned int ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_sort_refs, _c8);
    sort_refs[_c8] = Int_val(_v9);
  }
  num_fields = _c7;
  _res = Z3_mk_constructor(c, name, recognizer, num_fields, field_names, sorts, sort_refs);
  _vres = camlidl_c2ml_z3V3_Z3_constructor(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_constructor_bytecode(value * argv, int argn)
{
  return camlidl_z3V3_Z3_mk_constructor(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3V3_Z3_del_constructor(
	value _v_c,
	value _v_constr)
{
  Z3_context c; /*in*/
  Z3_constructor constr; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_constructor(_v_constr, &constr, _ctx);
  Z3_del_constructor(c, constr);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_mk_datatype(
	value _v_c,
	value _v_name,
	value _v_constructors)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  unsigned int num_constructors; /*in*/
  Z3_constructor *constructors; /*in,out*/
  Z3_sort _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  value _v5;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_name, &name, _ctx);
  _c1 = Wosize_val(_v_constructors);
  constructors = camlidl_malloc(_c1 * sizeof(Z3_constructor ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_constructors, _c2);
    camlidl_ml2c_z3V3_Z3_constructor(_v3, &constructors[_c2], _ctx);
  }
  num_constructors = _c1;
  _res = Z3_mk_datatype(c, name, num_constructors, constructors);
  Begin_roots_block(_vres, 2)
    _vres[0] = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
    _vres[1] = camlidl_alloc(num_constructors, 0);
    Begin_root(_vres[1])
      for (_c4 = 0; _c4 < num_constructors; _c4++) {
        _v5 = camlidl_c2ml_z3V3_Z3_constructor(&constructors[_c4], _ctx);
        modify(&Field(_vres[1], _c4), _v5);
      }
    End_roots()
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_mk_constructor_list(
	value _v_c,
	value _v_constructors)
{
  Z3_context c; /*in*/
  unsigned int num_constructors; /*in*/
  Z3_constructor const *constructors; /*in*/
  Z3_constructor_list _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_constructors);
  constructors = camlidl_malloc(_c1 * sizeof(Z3_constructor const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_constructors, _c2);
    camlidl_ml2c_z3V3_Z3_constructor(_v3, &constructors[_c2], _ctx);
  }
  num_constructors = _c1;
  _res = Z3_mk_constructor_list(c, num_constructors, constructors);
  _vres = camlidl_c2ml_z3V3_Z3_constructor_list(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_del_constructor_list(
	value _v_c,
	value _v_clist)
{
  Z3_context c; /*in*/
  Z3_constructor_list clist; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_constructor_list(_v_clist, &clist, _ctx);
  Z3_del_constructor_list(c, clist);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_mk_datatypes(
	value _v_c,
	value _v_sort_names,
	value _v_constructor_lists)
{
  Z3_context c; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol const *sort_names; /*in*/
  Z3_sort *sorts; /*out*/
  Z3_constructor_list *constructor_lists; /*in,out*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  value _v8;
  mlsize_t _c9;
  value _v10;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3V3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_constructor_lists);
  constructor_lists = camlidl_malloc(_c4 * sizeof(Z3_constructor_list ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_constructor_lists, _c5);
    camlidl_ml2c_z3V3_Z3_constructor_list(_v6, &constructor_lists[_c5], _ctx);
  }
  num_sorts = _c4;
  sorts = camlidl_malloc(num_sorts * sizeof(Z3_sort ), _ctx);
  Z3_mk_datatypes(c, num_sorts, sort_names, sorts, constructor_lists);
  Begin_roots_block(_vres, 2)
    _vres[0] = camlidl_alloc(num_sorts, 0);
    Begin_root(_vres[0])
      for (_c7 = 0; _c7 < num_sorts; _c7++) {
        _v8 = camlidl_c2ml_z3V3_Z3_sort(&sorts[_c7], _ctx);
        modify(&Field(_vres[0], _c7), _v8);
      }
    End_roots()
    _vres[1] = camlidl_alloc(num_sorts, 0);
    Begin_root(_vres[1])
      for (_c9 = 0; _c9 < num_sorts; _c9++) {
        _v10 = camlidl_c2ml_z3V3_Z3_constructor_list(&constructor_lists[_c9], _ctx);
        modify(&Field(_vres[1], _c9), _v10);
      }
    End_roots()
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_query_constructor(
	value _v_c,
	value _v_constr,
	value _v_num_fields)
{
  Z3_context c; /*in*/
  Z3_constructor constr; /*in*/
  unsigned int num_fields; /*in*/
  Z3_func_decl *constructor; /*out*/
  Z3_func_decl *tester; /*out*/
  Z3_func_decl *accessors; /*out*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  Z3_func_decl _c1;
  Z3_func_decl _c2;
  mlsize_t _c3;
  value _v4;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_constructor(_v_constr, &constr, _ctx);
  num_fields = Int_val(_v_num_fields);
  constructor = &_c1;
  tester = &_c2;
  accessors = camlidl_malloc(num_fields * sizeof(Z3_func_decl ), _ctx);
  Z3_query_constructor(c, constr, num_fields, constructor, tester, accessors);
  Begin_roots_block(_vres, 3)
    _vres[0] = camlidl_c2ml_z3V3_Z3_func_decl(&*constructor, _ctx);
    _vres[1] = camlidl_c2ml_z3V3_Z3_func_decl(&*tester, _ctx);
    _vres[2] = camlidl_alloc(num_fields, 0);
    Begin_root(_vres[2])
      for (_c3 = 0; _c3 < num_fields; _c3++) {
        _v4 = camlidl_c2ml_z3V3_Z3_func_decl(&accessors[_c3], _ctx);
        modify(&Field(_vres[2], _c3), _v4);
      }
    End_roots()
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_mk_func_decl(
	value _v_c,
	value _v_s,
	value _v_domain,
	value _v_range)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  unsigned int domain_size; /*in*/
  Z3_sort const *domain; /*in*/
  Z3_sort range; /*in*/
  Z3_func_decl _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_domain);
  domain = camlidl_malloc(_c1 * sizeof(Z3_sort const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_domain, _c2);
    camlidl_ml2c_z3V3_Z3_sort(_v3, &domain[_c2], _ctx);
  }
  domain_size = _c1;
  camlidl_ml2c_z3V3_Z3_sort(_v_range, &range, _ctx);
  _res = Z3_mk_func_decl(c, s, domain_size, domain, range);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_app(
	value _v_c,
	value _v_d,
	value _v_args)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_app(c, d, num_args, args);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_const(
	value _v_c,
	value _v_s,
	value _v_ty)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_s, &s, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_const(c, s, ty);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_fresh_func_decl(
	value _v_c,
	value _v_prefix,
	value _v_domain,
	value _v_range)
{
  Z3_context c; /*in*/
  Z3_string prefix; /*in*/
  unsigned int domain_size; /*in*/
  Z3_sort const *domain; /*in*/
  Z3_sort range; /*in*/
  Z3_func_decl _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_prefix, &prefix, _ctx);
  _c1 = Wosize_val(_v_domain);
  domain = camlidl_malloc(_c1 * sizeof(Z3_sort const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_domain, _c2);
    camlidl_ml2c_z3V3_Z3_sort(_v3, &domain[_c2], _ctx);
  }
  domain_size = _c1;
  camlidl_ml2c_z3V3_Z3_sort(_v_range, &range, _ctx);
  _res = Z3_mk_fresh_func_decl(c, prefix, domain_size, domain, range);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_fresh_const(
	value _v_c,
	value _v_prefix,
	value _v_ty)
{
  Z3_context c; /*in*/
  Z3_string prefix; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_prefix, &prefix, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_fresh_const(c, prefix, ty);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_true(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_true(c);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_false(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_false(c);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_eq(
	value _v_c,
	value _v_l,
	value _v_r)
{
  Z3_context c; /*in*/
  Z3_ast l; /*in*/
  Z3_ast r; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_l, &l, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_r, &r, _ctx);
  _res = Z3_mk_eq(c, l, r);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_distinct(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_distinct(c, num_args, args);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_not(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_mk_not(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_ite(
	value _v_c,
	value _v_t1,
	value _v_t2,
	value _v_t3)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast t3; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t3, &t3, _ctx);
  _res = Z3_mk_ite(c, t1, t2, t3);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_iff(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_iff(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_implies(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_implies(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_xor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_xor(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_and(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_and(c, num_args, args);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_or(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_or(c, num_args, args);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_add(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_add(c, num_args, args);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_mul(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_mul(c, num_args, args);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_sub(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_sub(c, num_args, args);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_unary_minus(
	value _v_c,
	value _v_arg)
{
  Z3_context c; /*in*/
  Z3_ast arg; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg, &arg, _ctx);
  _res = Z3_mk_unary_minus(c, arg);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_div(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_div(c, arg1, arg2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_mod(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_mod(c, arg1, arg2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_rem(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_rem(c, arg1, arg2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_power(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_power(c, arg1, arg2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_lt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_lt(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_le(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_le(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_gt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_gt(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_ge(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_ge(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_int2real(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_int2real(c, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_real2int(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_real2int(c, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_is_int(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_is_int(c, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvnot(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvnot(c, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvredand(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvredand(c, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvredor(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvredor(c, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvand(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvand(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvor(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvxor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvxor(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvnand(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvnand(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvnor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvnor(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvxnor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvxnor(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvneg(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvneg(c, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvadd(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvadd(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvsub(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsub(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvmul(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvmul(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvudiv(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvudiv(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvsdiv(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsdiv(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvurem(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvurem(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvsrem(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsrem(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvsmod(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsmod(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvult(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvult(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvslt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvslt(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvule(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvule(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvsle(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsle(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvuge(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvuge(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvsge(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsge(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvugt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvugt(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvsgt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsgt(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_concat(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_concat(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_extract(
	value _v_c,
	value _v_high,
	value _v_low,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int high; /*in*/
  unsigned int low; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  high = Int_val(_v_high);
  low = Int_val(_v_low);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_extract(c, high, low, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_sign_ext(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_sign_ext(c, i, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_zero_ext(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_zero_ext(c, i, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_repeat(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_repeat(c, i, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvshl(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvshl(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvlshr(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvlshr(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvashr(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvashr(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_rotate_left(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_rotate_left(c, i, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_rotate_right(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_rotate_right(c, i, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_ext_rotate_left(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_ext_rotate_left(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_ext_rotate_right(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_ext_rotate_right(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_int2bv(
	value _v_c,
	value _v_n,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int n; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  n = Int_val(_v_n);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_int2bv(c, n, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bv2int(
	value _v_c,
	value _v_t1,
	value _v_is_signed)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  int is_signed; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  is_signed = Int_val(_v_is_signed);
  _res = Z3_mk_bv2int(c, t1, is_signed);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvadd_no_overflow(
	value _v_c,
	value _v_t1,
	value _v_t2,
	value _v_is_signed)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  int is_signed; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  is_signed = Int_val(_v_is_signed);
  _res = Z3_mk_bvadd_no_overflow(c, t1, t2, is_signed);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvadd_no_underflow(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvadd_no_underflow(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvsub_no_overflow(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsub_no_overflow(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvsub_no_underflow(
	value _v_c,
	value _v_t1,
	value _v_t2,
	value _v_is_signed)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  int is_signed; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  is_signed = Int_val(_v_is_signed);
  _res = Z3_mk_bvsub_no_underflow(c, t1, t2, is_signed);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvsdiv_no_overflow(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsdiv_no_overflow(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvneg_no_overflow(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvneg_no_overflow(c, t1);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvmul_no_overflow(
	value _v_c,
	value _v_t1,
	value _v_t2,
	value _v_is_signed)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  int is_signed; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  is_signed = Int_val(_v_is_signed);
  _res = Z3_mk_bvmul_no_overflow(c, t1, t2, is_signed);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bvmul_no_underflow(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvmul_no_underflow(c, t1, t2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_select(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_i, &i, _ctx);
  _res = Z3_mk_select(c, a, i);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_store(
	value _v_c,
	value _v_a,
	value _v_i,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast i; /*in*/
  Z3_ast v; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_i, &i, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_v, &v, _ctx);
  _res = Z3_mk_store(c, a, i, v);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_const_array(
	value _v_c,
	value _v_domain,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_sort domain; /*in*/
  Z3_ast v; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_domain, &domain, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_v, &v, _ctx);
  _res = Z3_mk_const_array(c, domain, v);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_map(
	value _v_c,
	value _v_f,
	value _v_n,
	value _v_args)
{
  Z3_context c; /*in*/
  Z3_func_decl f; /*in*/
  unsigned int n; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  Z3_ast _c1;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_f, &f, _ctx);
  n = Int_val(_v_n);
  args = &_c1;
  camlidl_ml2c_z3V3_Z3_ast(_v_args, &_c1, _ctx);
  _res = Z3_mk_map(c, f, n, args);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_array_default(
	value _v_c,
	value _v_array)
{
  Z3_context c; /*in*/
  Z3_ast array; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_array, &array, _ctx);
  _res = Z3_mk_array_default(c, array);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_set_sort(
	value _v_c,
	value _v_ty)
{
  Z3_context c; /*in*/
  Z3_sort ty; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_set_sort(c, ty);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_empty_set(
	value _v_c,
	value _v_domain)
{
  Z3_context c; /*in*/
  Z3_sort domain; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_domain, &domain, _ctx);
  _res = Z3_mk_empty_set(c, domain);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_full_set(
	value _v_c,
	value _v_domain)
{
  Z3_context c; /*in*/
  Z3_sort domain; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_domain, &domain, _ctx);
  _res = Z3_mk_full_set(c, domain);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_set_add(
	value _v_c,
	value _v_set,
	value _v_elem)
{
  Z3_context c; /*in*/
  Z3_ast set; /*in*/
  Z3_ast elem; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_set, &set, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_elem, &elem, _ctx);
  _res = Z3_mk_set_add(c, set, elem);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_set_del(
	value _v_c,
	value _v_set,
	value _v_elem)
{
  Z3_context c; /*in*/
  Z3_ast set; /*in*/
  Z3_ast elem; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_set, &set, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_elem, &elem, _ctx);
  _res = Z3_mk_set_del(c, set, elem);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_set_union(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_set_union(c, num_args, args);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_set_intersect(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_set_intersect(c, num_args, args);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_set_difference(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_set_difference(c, arg1, arg2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_set_complement(
	value _v_c,
	value _v_arg)
{
  Z3_context c; /*in*/
  Z3_ast arg; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg, &arg, _ctx);
  _res = Z3_mk_set_complement(c, arg);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_set_member(
	value _v_c,
	value _v_elem,
	value _v_set)
{
  Z3_context c; /*in*/
  Z3_ast elem; /*in*/
  Z3_ast set; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_elem, &elem, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_set, &set, _ctx);
  _res = Z3_mk_set_member(c, elem, set);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_set_subset(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_set_subset(c, arg1, arg2);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_numeral(
	value _v_c,
	value _v_numeral,
	value _v_ty)
{
  Z3_context c; /*in*/
  Z3_string numeral; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_numeral, &numeral, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_numeral(c, numeral, ty);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_real(
	value _v_c,
	value _v_num,
	value _v_den)
{
  Z3_context c; /*in*/
  int num; /*in*/
  int den; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  num = Int_val(_v_num);
  den = Int_val(_v_den);
  _res = Z3_mk_real(c, num, den);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_int(
	value _v_c,
	value _v_v,
	value _v_ty)
{
  Z3_context c; /*in*/
  int v; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  v = Int_val(_v_v);
  camlidl_ml2c_z3V3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_int(c, v, ty);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_int64(
	value _v_c,
	value _v_v,
	value _v_ty)
{
  Z3_context c; /*in*/
  __int64 v; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  v = Int64_val(_v_v);
  camlidl_ml2c_z3V3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_int64(c, v, ty);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_pattern(
	value _v_c,
	value _v_terms)
{
  Z3_context c; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_ast const *terms; /*in*/
  Z3_pattern _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_terms);
  terms = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_terms, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &terms[_c2], _ctx);
  }
  num_patterns = _c1;
  _res = Z3_mk_pattern(c, num_patterns, terms);
  _vres = camlidl_c2ml_z3V3_Z3_pattern(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_bound(
	value _v_c,
	value _v_index,
	value _v_ty)
{
  Z3_context c; /*in*/
  unsigned int index; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  index = Int_val(_v_index);
  camlidl_ml2c_z3V3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_bound(c, index, ty);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_forall(
	value _v_c,
	value _v_weight,
	value _v_patterns,
	value _v_sorts,
	value _v_decl_names,
	value _v_body)
{
  Z3_context c; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_decls; /*in*/
  Z3_sort const *sorts; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c1 * sizeof(Z3_pattern const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_patterns, _c2);
    camlidl_ml2c_z3V3_Z3_pattern(_v3, &patterns[_c2], _ctx);
  }
  num_patterns = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3V3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_decls = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3V3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  camlidl_ml2c_z3V3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_forall(c, weight, num_patterns, patterns, num_decls, sorts, decl_names, body);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_forall_bytecode(value * argv, int argn)
{
  return camlidl_z3V3_Z3_mk_forall(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3V3_Z3_mk_exists(
	value _v_c,
	value _v_weight,
	value _v_patterns,
	value _v_sorts,
	value _v_decl_names,
	value _v_body)
{
  Z3_context c; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_decls; /*in*/
  Z3_sort const *sorts; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c1 * sizeof(Z3_pattern const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_patterns, _c2);
    camlidl_ml2c_z3V3_Z3_pattern(_v3, &patterns[_c2], _ctx);
  }
  num_patterns = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3V3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_decls = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3V3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  camlidl_ml2c_z3V3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_exists(c, weight, num_patterns, patterns, num_decls, sorts, decl_names, body);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_exists_bytecode(value * argv, int argn)
{
  return camlidl_z3V3_Z3_mk_exists(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3V3_Z3_mk_quantifier(
	value _v_c,
	value _v_is_forall,
	value _v_weight,
	value _v_patterns,
	value _v_sorts,
	value _v_decl_names,
	value _v_body)
{
  Z3_context c; /*in*/
  int is_forall; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_decls; /*in*/
  Z3_sort const *sorts; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  is_forall = Int_val(_v_is_forall);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c1 * sizeof(Z3_pattern const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_patterns, _c2);
    camlidl_ml2c_z3V3_Z3_pattern(_v3, &patterns[_c2], _ctx);
  }
  num_patterns = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3V3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_decls = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3V3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  camlidl_ml2c_z3V3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_quantifier(c, is_forall, weight, num_patterns, patterns, num_decls, sorts, decl_names, body);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_quantifier_bytecode(value * argv, int argn)
{
  return camlidl_z3V3_Z3_mk_quantifier(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6]);
}

value camlidl_z3V3_Z3_mk_quantifier_ex(
	value _v_c,
	value _v_is_forall,
	value _v_weight,
	value _v_quantifier_id,
	value _v_skolem_id,
	value _v_patterns,
	value _v_no_patterns,
	value _v_sorts,
	value _v_decl_names,
	value _v_body)
{
  Z3_context c; /*in*/
  int is_forall; /*in*/
  unsigned int weight; /*in*/
  Z3_symbol quantifier_id; /*in*/
  Z3_symbol skolem_id; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_no_patterns; /*in*/
  Z3_ast const *no_patterns; /*in*/
  unsigned int num_decls; /*in*/
  Z3_sort const *sorts; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  is_forall = Int_val(_v_is_forall);
  weight = Int_val(_v_weight);
  camlidl_ml2c_z3V3_Z3_symbol(_v_quantifier_id, &quantifier_id, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_skolem_id, &skolem_id, _ctx);
  _c1 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c1 * sizeof(Z3_pattern const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_patterns, _c2);
    camlidl_ml2c_z3V3_Z3_pattern(_v3, &patterns[_c2], _ctx);
  }
  num_patterns = _c1;
  _c4 = Wosize_val(_v_no_patterns);
  no_patterns = camlidl_malloc(_c4 * sizeof(Z3_ast const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_no_patterns, _c5);
    camlidl_ml2c_z3V3_Z3_ast(_v6, &no_patterns[_c5], _ctx);
  }
  num_no_patterns = _c4;
  _c7 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c7 * sizeof(Z3_sort const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_sorts, _c8);
    camlidl_ml2c_z3V3_Z3_sort(_v9, &sorts[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c10 * sizeof(Z3_symbol const ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decl_names, _c11);
    camlidl_ml2c_z3V3_Z3_symbol(_v12, &decl_names[_c11], _ctx);
  }
  num_decls = _c10;
  camlidl_ml2c_z3V3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_quantifier_ex(c, is_forall, weight, quantifier_id, skolem_id, num_patterns, patterns, num_no_patterns, no_patterns, num_decls, sorts, decl_names, body);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_quantifier_ex_bytecode(value * argv, int argn)
{
  return camlidl_z3V3_Z3_mk_quantifier_ex(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7], argv[8], argv[9]);
}

value camlidl_z3V3_Z3_mk_forall_const(
	value _v_c,
	value _v_weight,
	value _v_bound,
	value _v_patterns,
	value _v_body)
{
  Z3_context c; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_bound; /*in*/
  Z3_app const *bound; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_bound);
  bound = camlidl_malloc(_c1 * sizeof(Z3_app const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bound, _c2);
    camlidl_ml2c_z3V3_Z3_app(_v3, &bound[_c2], _ctx);
  }
  num_bound = _c1;
  _c4 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c4 * sizeof(Z3_pattern const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_patterns, _c5);
    camlidl_ml2c_z3V3_Z3_pattern(_v6, &patterns[_c5], _ctx);
  }
  num_patterns = _c4;
  camlidl_ml2c_z3V3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_forall_const(c, weight, num_bound, bound, num_patterns, patterns, body);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_exists_const(
	value _v_c,
	value _v_weight,
	value _v_bound,
	value _v_patterns,
	value _v_body)
{
  Z3_context c; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_bound; /*in*/
  Z3_app const *bound; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_bound);
  bound = camlidl_malloc(_c1 * sizeof(Z3_app const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bound, _c2);
    camlidl_ml2c_z3V3_Z3_app(_v3, &bound[_c2], _ctx);
  }
  num_bound = _c1;
  _c4 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c4 * sizeof(Z3_pattern const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_patterns, _c5);
    camlidl_ml2c_z3V3_Z3_pattern(_v6, &patterns[_c5], _ctx);
  }
  num_patterns = _c4;
  camlidl_ml2c_z3V3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_exists_const(c, weight, num_bound, bound, num_patterns, patterns, body);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_quantifier_const(
	value _v_c,
	value _v_is_forall,
	value _v_weight,
	value _v_bound,
	value _v_patterns,
	value _v_body)
{
  Z3_context c; /*in*/
  int is_forall; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_bound; /*in*/
  Z3_app const *bound; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  is_forall = Int_val(_v_is_forall);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_bound);
  bound = camlidl_malloc(_c1 * sizeof(Z3_app const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bound, _c2);
    camlidl_ml2c_z3V3_Z3_app(_v3, &bound[_c2], _ctx);
  }
  num_bound = _c1;
  _c4 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c4 * sizeof(Z3_pattern const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_patterns, _c5);
    camlidl_ml2c_z3V3_Z3_pattern(_v6, &patterns[_c5], _ctx);
  }
  num_patterns = _c4;
  camlidl_ml2c_z3V3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_quantifier_const(c, is_forall, weight, num_bound, bound, num_patterns, patterns, body);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_quantifier_const_bytecode(value * argv, int argn)
{
  return camlidl_z3V3_Z3_mk_quantifier_const(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3V3_Z3_mk_quantifier_const_ex(
	value _v_c,
	value _v_is_forall,
	value _v_weight,
	value _v_quantifier_id,
	value _v_skolem_id,
	value _v_bound,
	value _v_patterns,
	value _v_no_patterns,
	value _v_body)
{
  Z3_context c; /*in*/
  int is_forall; /*in*/
  unsigned int weight; /*in*/
  Z3_symbol quantifier_id; /*in*/
  Z3_symbol skolem_id; /*in*/
  unsigned int num_bound; /*in*/
  Z3_app const *bound; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_no_patterns; /*in*/
  Z3_ast const *no_patterns; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  is_forall = Int_val(_v_is_forall);
  weight = Int_val(_v_weight);
  camlidl_ml2c_z3V3_Z3_symbol(_v_quantifier_id, &quantifier_id, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_skolem_id, &skolem_id, _ctx);
  _c1 = Wosize_val(_v_bound);
  bound = camlidl_malloc(_c1 * sizeof(Z3_app const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bound, _c2);
    camlidl_ml2c_z3V3_Z3_app(_v3, &bound[_c2], _ctx);
  }
  num_bound = _c1;
  _c4 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c4 * sizeof(Z3_pattern const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_patterns, _c5);
    camlidl_ml2c_z3V3_Z3_pattern(_v6, &patterns[_c5], _ctx);
  }
  num_patterns = _c4;
  _c7 = Wosize_val(_v_no_patterns);
  no_patterns = camlidl_malloc(_c7 * sizeof(Z3_ast const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_no_patterns, _c8);
    camlidl_ml2c_z3V3_Z3_ast(_v9, &no_patterns[_c8], _ctx);
  }
  num_no_patterns = _c7;
  camlidl_ml2c_z3V3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_quantifier_const_ex(c, is_forall, weight, quantifier_id, skolem_id, num_bound, bound, num_patterns, patterns, num_no_patterns, no_patterns, body);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_quantifier_const_ex_bytecode(value * argv, int argn)
{
  return camlidl_z3V3_Z3_mk_quantifier_const_ex(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7], argv[8]);
}

value camlidl_z3V3_Z3_get_symbol_kind(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  Z3_symbol_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_get_symbol_kind(c, s);
  _vres = camlidl_c2ml_z3V3_Z3_symbol_kind(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_symbol_int(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_get_symbol_int(c, s);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_symbol_string(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_get_symbol_string(c, s);
  _vres = camlidl_c2ml_z3V3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_sort_name(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_sort d; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_d, &d, _ctx);
  _res = Z3_get_sort_name(c, d);
  _vres = camlidl_c2ml_z3V3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_sort_id(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_get_sort_id(c, s);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_sort_to_ast(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_sort_to_ast(c, s);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_is_eq_sort(
	value _v_c,
	value _v_s1,
	value _v_s2)
{
  Z3_context c; /*in*/
  Z3_sort s1; /*in*/
  Z3_sort s2; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_s1, &s1, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_s2, &s2, _ctx);
  _res = Z3_is_eq_sort(c, s1, s2);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_sort_kind(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  Z3_sort_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_sort_kind(c, t);
  _vres = camlidl_c2ml_z3V3_Z3_sort_kind(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_bv_sort_size(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_bv_sort_size(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_finite_domain_sort_size(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  __int64 *r; /*out*/
  __int64 _c1;
  value _v2;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_s, &s, _ctx);
  r = &_c1;
  Z3_get_finite_domain_sort_size(c, s, r);
  if (r == NULL) {
    _vres = Val_int(0);
  } else {
    _v2 = copy_int64(*r);
    Begin_root(_v2)
      _vres = camlidl_alloc_small(1, 0);
      Field(_vres, 0) = _v2;
    End_roots();
  }
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_array_sort_domain(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_array_sort_domain(c, t);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_array_sort_range(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_array_sort_range(c, t);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_tuple_sort_mk_decl(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_tuple_sort_mk_decl(c, t);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_tuple_sort_num_fields(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_tuple_sort_num_fields(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_tuple_sort_field_decl(
	value _v_c,
	value _v_t,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int i; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_t, &t, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_tuple_sort_field_decl(c, t, i);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_datatype_sort_num_constructors(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_datatype_sort_num_constructors(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_datatype_sort_constructor(
	value _v_c,
	value _v_t,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int idx; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_t, &t, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_datatype_sort_constructor(c, t, idx);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_datatype_sort_recognizer(
	value _v_c,
	value _v_t,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int idx; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_t, &t, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_datatype_sort_recognizer(c, t, idx);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_datatype_sort_constructor_accessor(
	value _v_c,
	value _v_t,
	value _v_idx_c,
	value _v_idx_a)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int idx_c; /*in*/
  unsigned int idx_a; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_t, &t, _ctx);
  idx_c = Int_val(_v_idx_c);
  idx_a = Int_val(_v_idx_a);
  _res = Z3_get_datatype_sort_constructor_accessor(c, t, idx_c, idx_a);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_relation_arity(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_get_relation_arity(c, s);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_relation_column(
	value _v_c,
	value _v_s,
	value _v_col)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  unsigned int col; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_s, &s, _ctx);
  col = Int_val(_v_col);
  _res = Z3_get_relation_column(c, s, col);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_func_decl_to_ast(
	value _v_c,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_func_decl f; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_f, &f, _ctx);
  _res = Z3_func_decl_to_ast(c, f);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_is_eq_func_decl(
	value _v_c,
	value _v_f1,
	value _v_f2)
{
  Z3_context c; /*in*/
  Z3_func_decl f1; /*in*/
  Z3_func_decl f2; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_f1, &f1, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_f2, &f2, _ctx);
  _res = Z3_is_eq_func_decl(c, f1, f2);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_func_decl_id(
	value _v_c,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_func_decl f; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_f, &f, _ctx);
  _res = Z3_get_func_decl_id(c, f);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_decl_name(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_decl_name(c, d);
  _vres = camlidl_c2ml_z3V3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_decl_kind(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  Z3_decl_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_decl_kind(c, d);
  _vres = camlidl_c2ml_z3V3_Z3_decl_kind(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_domain_size(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_domain_size(c, d);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_arity(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_arity(c, d);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_domain(
	value _v_c,
	value _v_d,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int i; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_domain(c, d, i);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_range(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_range(c, d);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_decl_num_parameters(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_decl_num_parameters(c, d);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_decl_parameter_kind(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_parameter_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_parameter_kind(c, d, idx);
  _vres = camlidl_c2ml_z3V3_Z3_parameter_kind(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_decl_int_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_int_parameter(c, d, idx);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_decl_double_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  double _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_double_parameter(c, d, idx);
  _vres = copy_double(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_decl_symbol_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_symbol_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3V3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_decl_sort_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_sort_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_decl_ast_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_ast_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_decl_func_decl_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_func_decl_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_decl_rational_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_rational_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3V3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_app_to_ast(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_app a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_app(_v_a, &a, _ctx);
  _res = Z3_app_to_ast(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_app_decl(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_app a; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_app(_v_a, &a, _ctx);
  _res = Z3_get_app_decl(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_app_num_args(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_app a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_app(_v_a, &a, _ctx);
  _res = Z3_get_app_num_args(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_app_arg(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_app a; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_app(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_app_arg(c, a, i);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_is_eq_ast(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_is_eq_ast(c, t1, t2);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_ast_id(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_ast t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t, &t, _ctx);
  _res = Z3_get_ast_id(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_ast_hash(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_ast_hash(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_sort(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_sort(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_is_well_sorted(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_ast t; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t, &t, _ctx);
  _res = Z3_is_well_sorted(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_bool_value(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_lbool _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_bool_value(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_lbool(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_ast_kind(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_ast_kind(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_ast_kind(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_is_app(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_is_app(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_is_numeral_ast(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_is_numeral_ast(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_is_algebraic_number(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_is_algebraic_number(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_to_app(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_app _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_to_app(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_app(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_to_func_decl(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_to_func_decl(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_numeral_string(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_numeral_string(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_numeral_decimal_string(
	value _v_c,
	value _v_a,
	value _v_precision)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int precision; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  precision = Int_val(_v_precision);
  _res = Z3_get_numeral_decimal_string(c, a, precision);
  _vres = camlidl_c2ml_z3V3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_numerator(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_numerator(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_denominator(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_denominator(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_numeral_small(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  __int64 *num; /*out*/
  __int64 *den; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  __int64 _c1;
  __int64 _c2;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  num = &_c1;
  den = &_c2;
  _res = Z3_get_numeral_small(c, a, num, den);
  Begin_roots_block(_vres, 3)
    _vres[0] = Val_int(_res);
    _vres[1] = copy_int64(*num);
    _vres[2] = copy_int64(*den);
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_get_numeral_int(
	value _v_c,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast v; /*in*/
  int *i; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  int _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_v, &v, _ctx);
  i = &_c1;
  _res = Z3_get_numeral_int(c, v, i);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = Val_int(*i);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_get_numeral_int64(
	value _v_c,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast v; /*in*/
  __int64 *i; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  __int64 _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_v, &v, _ctx);
  i = &_c1;
  _res = Z3_get_numeral_int64(c, v, i);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = copy_int64(*i);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_get_numeral_rational_int64(
	value _v_c,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast v; /*in*/
  __int64 *num; /*out*/
  __int64 *den; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  __int64 _c1;
  __int64 _c2;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_v, &v, _ctx);
  num = &_c1;
  den = &_c2;
  _res = Z3_get_numeral_rational_int64(c, v, num, den);
  Begin_roots_block(_vres, 3)
    _vres[0] = Val_int(_res);
    _vres[1] = copy_int64(*num);
    _vres[2] = copy_int64(*den);
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_get_algebraic_number_lower(
	value _v_c,
	value _v_a,
	value _v_precision)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int precision; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  precision = Int_val(_v_precision);
  _res = Z3_get_algebraic_number_lower(c, a, precision);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_algebraic_number_upper(
	value _v_c,
	value _v_a,
	value _v_precision)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int precision; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  precision = Int_val(_v_precision);
  _res = Z3_get_algebraic_number_upper(c, a, precision);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_pattern_to_ast(
	value _v_c,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_pattern p; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_pattern(_v_p, &p, _ctx);
  _res = Z3_pattern_to_ast(c, p);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_pattern_num_terms(
	value _v_c,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_pattern p; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_pattern(_v_p, &p, _ctx);
  _res = Z3_get_pattern_num_terms(c, p);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_pattern(
	value _v_c,
	value _v_p,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_pattern p; /*in*/
  unsigned int idx; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_pattern(_v_p, &p, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_pattern(c, p, idx);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_index_value(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_index_value(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_is_quantifier_forall(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_is_quantifier_forall(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_quantifier_weight(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_weight(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_quantifier_num_patterns(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_num_patterns(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_quantifier_pattern_ast(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int i; /*in*/
  Z3_pattern _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_quantifier_pattern_ast(c, a, i);
  _vres = camlidl_c2ml_z3V3_Z3_pattern(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_quantifier_num_no_patterns(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_num_no_patterns(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_quantifier_no_pattern_ast(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_quantifier_no_pattern_ast(c, a, i);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_quantifier_num_bound(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_num_bound(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_quantifier_bound_name(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int i; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_quantifier_bound_name(c, a, i);
  _vres = camlidl_c2ml_z3V3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_quantifier_bound_sort(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int i; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_quantifier_bound_sort(c, a, i);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_quantifier_body(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_body(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_simplify(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_simplify(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_update_term(
	value _v_c,
	value _v_a,
	value _v_args)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_update_term(c, a, num_args, args);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_substitute(
	value _v_c,
	value _v_a,
	value _v_from,
	value _v_to)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int num_exprs; /*in*/
  Z3_ast const *from; /*in*/
  Z3_ast const *to; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _c1 = Wosize_val(_v_from);
  from = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_from, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &from[_c2], _ctx);
  }
  num_exprs = _c1;
  _c4 = Wosize_val(_v_to);
  to = camlidl_malloc(_c4 * sizeof(Z3_ast const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_to, _c5);
    camlidl_ml2c_z3V3_Z3_ast(_v6, &to[_c5], _ctx);
  }
  num_exprs = _c4;
  _res = Z3_substitute(c, a, num_exprs, from, to);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_substitute_vars(
	value _v_c,
	value _v_a,
	value _v_to)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int num_exprs; /*in*/
  Z3_ast const *to; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _c1 = Wosize_val(_v_to);
  to = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_to, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &to[_c2], _ctx);
  }
  num_exprs = _c1;
  _res = Z3_substitute_vars(c, a, num_exprs, to);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_open_log(
	value _v_filename)
{
  Z3_string filename; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_string(_v_filename, &filename, _ctx);
  _res = Z3_open_log(filename);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_append_log(
	value _v_string)
{
  Z3_string string; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_string(_v_string, &string, _ctx);
  Z3_append_log(string);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_close_log(value _unit)
{
  Z3_close_log();
  return Val_unit;
}

value camlidl_z3V3_Z3_toggle_warning_messages(
	value _v_enabled)
{
  int enabled; /*in*/
  enabled = Int_val(_v_enabled);
  Z3_toggle_warning_messages(enabled);
  return Val_unit;
}

value camlidl_z3V3_Z3_set_ast_print_mode(
	value _v_c,
	value _v_mode)
{
  Z3_context c; /*in*/
  Z3_ast_print_mode mode; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast_print_mode(_v_mode, &mode, _ctx);
  Z3_set_ast_print_mode(c, mode);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_ast_to_string(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_ast_to_string(c, a);
  _vres = camlidl_c2ml_z3V3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_pattern_to_string(
	value _v_c,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_pattern p; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_pattern(_v_p, &p, _ctx);
  _res = Z3_pattern_to_string(c, p);
  _vres = camlidl_c2ml_z3V3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_sort_to_string(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_sort_to_string(c, s);
  _vres = camlidl_c2ml_z3V3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_func_decl_to_string(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_func_decl_to_string(c, d);
  _vres = camlidl_c2ml_z3V3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_model_to_string(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  _res = Z3_model_to_string(c, m);
  _vres = camlidl_c2ml_z3V3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_benchmark_to_smtlib_string(
	value _v_c,
	value _v_name,
	value _v_logic,
	value _v_status,
	value _v_attributes,
	value _v_assumptions,
	value _v_formula)
{
  Z3_context c; /*in*/
  Z3_string name; /*in*/
  Z3_string logic; /*in*/
  Z3_string status; /*in*/
  Z3_string attributes; /*in*/
  unsigned int num_assumptions; /*in*/
  Z3_ast const *assumptions; /*in*/
  Z3_ast formula; /*in*/
  Z3_string _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_name, &name, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_logic, &logic, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_status, &status, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_attributes, &attributes, _ctx);
  _c1 = Wosize_val(_v_assumptions);
  assumptions = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_assumptions, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &assumptions[_c2], _ctx);
  }
  num_assumptions = _c1;
  camlidl_ml2c_z3V3_Z3_ast(_v_formula, &formula, _ctx);
  _res = Z3_benchmark_to_smtlib_string(c, name, logic, status, attributes, num_assumptions, assumptions, formula);
  _vres = camlidl_c2ml_z3V3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_benchmark_to_smtlib_string_bytecode(value * argv, int argn)
{
  return camlidl_z3V3_Z3_benchmark_to_smtlib_string(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6]);
}

value camlidl_z3V3_Z3_parse_smtlib2_string(
	value _v_c,
	value _v_str,
	value _v_sort_names,
	value _v_sorts,
	value _v_decl_names,
	value _v_decls)
{
  Z3_context c; /*in*/
  Z3_string str; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol const *sort_names; /*in*/
  Z3_sort const *sorts; /*in*/
  unsigned int num_decls; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_func_decl const *decls; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_str, &str, _ctx);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3V3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3V3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_sorts = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3V3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decls);
  decls = camlidl_malloc(_c10 * sizeof(Z3_func_decl const ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decls, _c11);
    camlidl_ml2c_z3V3_Z3_func_decl(_v12, &decls[_c11], _ctx);
  }
  num_decls = _c10;
  _res = Z3_parse_smtlib2_string(c, str, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_parse_smtlib2_string_bytecode(value * argv, int argn)
{
  return camlidl_z3V3_Z3_parse_smtlib2_string(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3V3_Z3_parse_smtlib2_file(
	value _v_c,
	value _v_file_name,
	value _v_sort_names,
	value _v_sorts,
	value _v_decl_names,
	value _v_decls)
{
  Z3_context c; /*in*/
  Z3_string file_name; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol const *sort_names; /*in*/
  Z3_sort const *sorts; /*in*/
  unsigned int num_decls; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_func_decl const *decls; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_file_name, &file_name, _ctx);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3V3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3V3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_sorts = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3V3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decls);
  decls = camlidl_malloc(_c10 * sizeof(Z3_func_decl const ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decls, _c11);
    camlidl_ml2c_z3V3_Z3_func_decl(_v12, &decls[_c11], _ctx);
  }
  num_decls = _c10;
  _res = Z3_parse_smtlib2_file(c, file_name, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_parse_smtlib2_file_bytecode(value * argv, int argn)
{
  return camlidl_z3V3_Z3_parse_smtlib2_file(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3V3_Z3_parse_smtlib_string(
	value _v_c,
	value _v_str,
	value _v_sort_names,
	value _v_sorts,
	value _v_decl_names,
	value _v_decls)
{
  Z3_context c; /*in*/
  Z3_string str; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol const *sort_names; /*in*/
  Z3_sort const *sorts; /*in*/
  unsigned int num_decls; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_func_decl const *decls; /*in*/
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_str, &str, _ctx);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3V3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3V3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_sorts = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3V3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decls);
  decls = camlidl_malloc(_c10 * sizeof(Z3_func_decl const ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decls, _c11);
    camlidl_ml2c_z3V3_Z3_func_decl(_v12, &decls[_c11], _ctx);
  }
  num_decls = _c10;
  Z3_parse_smtlib_string(c, str, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_parse_smtlib_string_bytecode(value * argv, int argn)
{
  return camlidl_z3V3_Z3_parse_smtlib_string(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3V3_Z3_parse_smtlib_file(
	value _v_c,
	value _v_file_name,
	value _v_sort_names,
	value _v_sorts,
	value _v_decl_names,
	value _v_decls)
{
  Z3_context c; /*in*/
  Z3_string file_name; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol const *sort_names; /*in*/
  Z3_sort const *sorts; /*in*/
  unsigned int num_decls; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_func_decl const *decls; /*in*/
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_file_name, &file_name, _ctx);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3V3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3V3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_sorts = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3V3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decls);
  decls = camlidl_malloc(_c10 * sizeof(Z3_func_decl const ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decls, _c11);
    camlidl_ml2c_z3V3_Z3_func_decl(_v12, &decls[_c11], _ctx);
  }
  num_decls = _c10;
  Z3_parse_smtlib_file(c, file_name, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_parse_smtlib_file_bytecode(value * argv, int argn)
{
  return camlidl_z3V3_Z3_parse_smtlib_file(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3V3_Z3_get_smtlib_num_formulas(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_num_formulas(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_smtlib_formula(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_smtlib_formula(c, i);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_smtlib_num_assumptions(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_num_assumptions(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_smtlib_assumption(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_smtlib_assumption(c, i);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_smtlib_num_decls(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_num_decls(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_smtlib_decl(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_smtlib_decl(c, i);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_smtlib_num_sorts(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_num_sorts(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_smtlib_sort(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_smtlib_sort(c, i);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_smtlib_error(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_error(c);
  _vres = camlidl_c2ml_z3V3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}
/*
value camlidl_z3_Z3_parse_z3V3_string(
	value _v_c,
	value _v_str)
{
  Z3_context c; /*in
  Z3_string str; /*in
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_str, &str, _ctx);
  _res = Z3_parse_z3_string(c, str);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_parse_z3V3_file(
	value _v_c,
	value _v_file_name)
{
  Z3_context c; /*in
  Z3_string file_name; /*in
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_file_name, &file_name, _ctx);
  _res = Z3_parse_z3_file(c, file_name);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}
*/
value camlidl_z3V3_Z3_get_version(value _unit)
{
  unsigned int *major; /*out*/
  unsigned int *minor; /*out*/
  unsigned int *build_number; /*out*/
  unsigned int *revision_number; /*out*/
  unsigned int _c1;
  unsigned int _c2;
  unsigned int _c3;
  unsigned int _c4;
  value _vresult;
  value _vres[4] = { 0, 0, 0, 0, };

  major = &_c1;
  minor = &_c2;
  build_number = &_c3;
  revision_number = &_c4;
  Z3_get_version(major, minor, build_number, revision_number);
  Begin_roots_block(_vres, 4)
    _vres[0] = Val_int(*major);
    _vres[1] = Val_int(*minor);
    _vres[2] = Val_int(*build_number);
    _vres[3] = Val_int(*revision_number);
    _vresult = camlidl_alloc_small(4, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
    Field(_vresult, 3) = _vres[3];
  End_roots()
  return _vresult;
}

value camlidl_z3V3_Z3_reset_memory(value _unit)
{
  Z3_reset_memory();
  return Val_unit;
}

value camlidl_z3V3_Z3_theory_mk_sort(
	value _v_c,
	value _v_t,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_theory t; /*in*/
  Z3_symbol s; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_theory_mk_sort(c, t, s);
  _vres = camlidl_c2ml_z3V3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_mk_value(
	value _v_c,
	value _v_t,
	value _v_n,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_theory t; /*in*/
  Z3_symbol n; /*in*/
  Z3_sort s; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_n, &n, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_theory_mk_value(c, t, n, s);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_mk_constant(
	value _v_c,
	value _v_t,
	value _v_n,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_theory t; /*in*/
  Z3_symbol n; /*in*/
  Z3_sort s; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_n, &n, _ctx);
  camlidl_ml2c_z3V3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_theory_mk_constant(c, t, n, s);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_mk_func_decl(
	value _v_c,
	value _v_t,
	value _v_n,
	value _v_domain,
	value _v_range)
{
  Z3_context c; /*in*/
  Z3_theory t; /*in*/
  Z3_symbol n; /*in*/
  unsigned int domain_size; /*in*/
  Z3_sort const *domain; /*in*/
  Z3_sort range; /*in*/
  Z3_func_decl _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_n, &n, _ctx);
  _c1 = Wosize_val(_v_domain);
  domain = camlidl_malloc(_c1 * sizeof(Z3_sort const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_domain, _c2);
    camlidl_ml2c_z3V3_Z3_sort(_v3, &domain[_c2], _ctx);
  }
  domain_size = _c1;
  camlidl_ml2c_z3V3_Z3_sort(_v_range, &range, _ctx);
  _res = Z3_theory_mk_func_decl(c, t, n, domain_size, domain, range);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_get_context(
	value _v_t)
{
  Z3_theory t; /*in*/
  Z3_context _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  _res = Z3_theory_get_context(t);
  _vres = camlidl_c2ml_z3V3_Z3_context(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_assert_axiom(
	value _v_t,
	value _v_ax)
{
  Z3_theory t; /*in*/
  Z3_ast ax; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_ax, &ax, _ctx);
  Z3_theory_assert_axiom(t, ax);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_theory_assume_eq(
	value _v_t,
	value _v_lhs,
	value _v_rhs)
{
  Z3_theory t; /*in*/
  Z3_ast lhs; /*in*/
  Z3_ast rhs; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_lhs, &lhs, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_rhs, &rhs, _ctx);
  Z3_theory_assume_eq(t, lhs, rhs);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_theory_enable_axiom_simplification(
	value _v_t,
	value _v_flag)
{
  Z3_theory t; /*in*/
  int flag; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  flag = Int_val(_v_flag);
  Z3_theory_enable_axiom_simplification(t, flag);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_theory_get_eqc_root(
	value _v_t,
	value _v_n)
{
  Z3_theory t; /*in*/
  Z3_ast n; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_n, &n, _ctx);
  _res = Z3_theory_get_eqc_root(t, n);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_get_eqc_next(
	value _v_t,
	value _v_n)
{
  Z3_theory t; /*in*/
  Z3_ast n; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_n, &n, _ctx);
  _res = Z3_theory_get_eqc_next(t, n);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_get_num_parents(
	value _v_t,
	value _v_n)
{
  Z3_theory t; /*in*/
  Z3_ast n; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_n, &n, _ctx);
  _res = Z3_theory_get_num_parents(t, n);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_get_parent(
	value _v_t,
	value _v_n,
	value _v_i)
{
  Z3_theory t; /*in*/
  Z3_ast n; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_n, &n, _ctx);
  i = Int_val(_v_i);
  _res = Z3_theory_get_parent(t, n, i);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_is_value(
	value _v_t,
	value _v_n)
{
  Z3_theory t; /*in*/
  Z3_ast n; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_n, &n, _ctx);
  _res = Z3_theory_is_value(t, n);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_is_decl(
	value _v_t,
	value _v_d)
{
  Z3_theory t; /*in*/
  Z3_func_decl d; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_theory_is_decl(t, d);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_get_num_elems(
	value _v_t)
{
  Z3_theory t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  _res = Z3_theory_get_num_elems(t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_get_elem(
	value _v_t,
	value _v_i)
{
  Z3_theory t; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  i = Int_val(_v_i);
  _res = Z3_theory_get_elem(t, i);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_get_num_apps(
	value _v_t)
{
  Z3_theory t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  _res = Z3_theory_get_num_apps(t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_theory_get_app(
	value _v_t,
	value _v_i)
{
  Z3_theory t; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_theory(_v_t, &t, _ctx);
  i = Int_val(_v_i);
  _res = Z3_theory_get_app(t, i);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_injective_function(
	value _v_c,
	value _v_s,
	value _v_domain,
	value _v_range)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  unsigned int domain_size; /*in*/
  Z3_sort const *domain; /*in*/
  Z3_sort range; /*in*/
  Z3_func_decl _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_domain);
  domain = camlidl_malloc(_c1 * sizeof(Z3_sort const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_domain, _c2);
    camlidl_ml2c_z3V3_Z3_sort(_v3, &domain[_c2], _ctx);
  }
  domain_size = _c1;
  camlidl_ml2c_z3V3_Z3_sort(_v_range, &range, _ctx);
  _res = Z3_mk_injective_function(c, s, domain_size, domain, range);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_set_logic(
	value _v_c,
	value _v_logic)
{
  Z3_context c; /*in*/
  Z3_string logic; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_string(_v_logic, &logic, _ctx);
  _res = Z3_set_logic(c, logic);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_push(
	value _v_c)
{
  Z3_context c; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  Z3_push(c);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_pop(
	value _v_c,
	value _v_num_scopes)
{
  Z3_context c; /*in*/
  unsigned int num_scopes; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  num_scopes = Int_val(_v_num_scopes);
  Z3_pop(c, num_scopes);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_get_num_scopes(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_num_scopes(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_persist_ast(
	value _v_c,
	value _v_a,
	value _v_num_scopes)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int num_scopes; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  num_scopes = Int_val(_v_num_scopes);
  Z3_persist_ast(c, a, num_scopes);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_assert_cnstr(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_a, &a, _ctx);
  Z3_assert_cnstr(c, a);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_check_and_get_model(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_model *m; /*out*/
  Z3_lbool _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  Z3_model _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  m = &_c1;
  _res = Z3_check_and_get_model(c, m);
  Begin_roots_block(_vres, 2)
    _vres[0] = camlidl_c2ml_z3V3_Z3_lbool(&_res, _ctx);
    _vres[1] = camlidl_c2ml_z3V3_Z3_model(&*m, _ctx);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_check(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_lbool _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_check(c);
  _vres = camlidl_c2ml_z3V3_Z3_lbool(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_check_assumptions(
	value _v_c,
	value _v_assumptions,
	value _v_core_size,
	value _v_core)
{
  Z3_context c; /*in*/
  unsigned int num_assumptions; /*in*/
  Z3_ast const *assumptions; /*in*/
  Z3_model *m; /*out*/
  Z3_ast *proof; /*out*/
  unsigned int *core_size; /*in,out*/
  Z3_ast *core; /*in,out*/
  Z3_lbool _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  unsigned int _c4;
  mlsize_t _c5;
  mlsize_t _c6;
  value _v7;
  Z3_model _c8;
  Z3_ast _c9;
  mlsize_t _c10;
  value _v11;
  value _vresult;
  value _vres[5] = { 0, 0, 0, 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_assumptions);
  assumptions = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_assumptions, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &assumptions[_c2], _ctx);
  }
  num_assumptions = _c1;
  core_size = &_c4;
  _c4 = Int_val(_v_core_size);
  _c5 = Wosize_val(_v_core);
  core = camlidl_malloc(_c5 * sizeof(Z3_ast ), _ctx);
  for (_c6 = 0; _c6 < _c5; _c6++) {
    _v7 = Field(_v_core, _c6);
    camlidl_ml2c_z3V3_Z3_ast(_v7, &core[_c6], _ctx);
  }
  num_assumptions = _c5;
  m = &_c8;
  proof = &_c9;
  _res = Z3_check_assumptions(c, num_assumptions, assumptions, m, proof, core_size, core);
  Begin_roots_block(_vres, 5)
    _vres[0] = camlidl_c2ml_z3V3_Z3_lbool(&_res, _ctx);
    _vres[1] = camlidl_c2ml_z3V3_Z3_model(&*m, _ctx);
    _vres[2] = camlidl_c2ml_z3V3_Z3_ast(&*proof, _ctx);
    _vres[3] = Val_int(*core_size);
    _vres[4] = camlidl_alloc(num_assumptions, 0);
    Begin_root(_vres[4])
      for (_c10 = 0; _c10 < num_assumptions; _c10++) {
        _v11 = camlidl_c2ml_z3V3_Z3_ast(&core[_c10], _ctx);
        modify(&Field(_vres[4], _c10), _v11);
      }
    End_roots()
    _vresult = camlidl_alloc_small(5, 0);
    { mlsize_t _c12;
      for (_c12 = 0; _c12 < 5; _c12++) Field(_vresult, _c12) = _vres[_c12];
    }
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_del_model(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  Z3_del_model(c, m);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_soft_check_cancel(
	value _v_c)
{
  Z3_context c; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  Z3_soft_check_cancel(c);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_get_search_failure(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_search_failure _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_search_failure(c);
  _vres = camlidl_c2ml_z3V3_Z3_search_failure(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_mk_label(
	value _v_c,
	value _v_s,
	value _v_is_pos,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  int is_pos; /*in*/
  Z3_ast f; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_symbol(_v_s, &s, _ctx);
  is_pos = Int_val(_v_is_pos);
  camlidl_ml2c_z3V3_Z3_ast(_v_f, &f, _ctx);
  _res = Z3_mk_label(c, s, is_pos, f);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_relevant_labels(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_literals _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_relevant_labels(c);
  _vres = camlidl_c2ml_z3V3_Z3_literals(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_relevant_literals(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_literals _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_relevant_literals(c);
  _vres = camlidl_c2ml_z3V3_Z3_literals(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_guessed_literals(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_literals _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_guessed_literals(c);
  _vres = camlidl_c2ml_z3V3_Z3_literals(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_del_literals(
	value _v_c,
	value _v_lbls)
{
  Z3_context c; /*in*/
  Z3_literals lbls; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_literals(_v_lbls, &lbls, _ctx);
  Z3_del_literals(c, lbls);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_get_num_literals(
	value _v_c,
	value _v_lbls)
{
  Z3_context c; /*in*/
  Z3_literals lbls; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_literals(_v_lbls, &lbls, _ctx);
  _res = Z3_get_num_literals(c, lbls);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_label_symbol(
	value _v_c,
	value _v_lbls,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_literals lbls; /*in*/
  unsigned int idx; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_literals(_v_lbls, &lbls, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_label_symbol(c, lbls, idx);
  _vres = camlidl_c2ml_z3V3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_literal(
	value _v_c,
	value _v_lbls,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_literals lbls; /*in*/
  unsigned int idx; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_literals(_v_lbls, &lbls, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_literal(c, lbls, idx);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_disable_literal(
	value _v_c,
	value _v_lbls,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_literals lbls; /*in*/
  unsigned int idx; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_literals(_v_lbls, &lbls, _ctx);
  idx = Int_val(_v_idx);
  Z3_disable_literal(c, lbls, idx);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_block_literals(
	value _v_c,
	value _v_lbls)
{
  Z3_context c; /*in*/
  Z3_literals lbls; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_literals(_v_lbls, &lbls, _ctx);
  Z3_block_literals(c, lbls);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3V3_Z3_get_model_num_constants(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  _res = Z3_get_model_num_constants(c, m);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_model_constant(
	value _v_c,
	value _v_m,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_model_constant(c, m, i);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_model_num_funcs(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  _res = Z3_get_model_num_funcs(c, m);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_model_func_decl(
	value _v_c,
	value _v_m,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_model_func_decl(c, m, i);
  _vres = camlidl_c2ml_z3V3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_eval_func_decl(
	value _v_c,
	value _v_m,
	value _v_decl)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_func_decl decl; /*in*/
  Z3_ast *v; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  Z3_ast _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_decl, &decl, _ctx);
  v = &_c1;
  _res = Z3_eval_func_decl(c, m, decl, v);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = camlidl_c2ml_z3V3_Z3_ast(&*v, _ctx);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_is_array_value(
	value _v_c,
	value _v_m,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_ast v; /*in*/
  unsigned int *num_entries; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  unsigned int _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_v, &v, _ctx);
  num_entries = &_c1;
  _res = Z3_is_array_value(c, m, v, num_entries);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = Val_int(*num_entries);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_get_array_value(
	value _v_c,
	value _v_m,
	value _v_v,
	value _v_indices,
	value _v_values)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_ast v; /*in*/
  unsigned int num_entries; /*in*/
  Z3_ast *indices; /*in,out*/
  Z3_ast *values; /*in,out*/
  Z3_ast *else_value; /*out*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  Z3_ast _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  value _v11;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_v, &v, _ctx);
  _c1 = Wosize_val(_v_indices);
  indices = camlidl_malloc(_c1 * sizeof(Z3_ast ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_indices, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &indices[_c2], _ctx);
  }
  num_entries = _c1;
  _c4 = Wosize_val(_v_values);
  values = camlidl_malloc(_c4 * sizeof(Z3_ast ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_values, _c5);
    camlidl_ml2c_z3V3_Z3_ast(_v6, &values[_c5], _ctx);
  }
  num_entries = _c4;
  else_value = &_c7;
  Z3_get_array_value(c, m, v, num_entries, indices, values, else_value);
  Begin_roots_block(_vres, 3)
    _vres[0] = camlidl_alloc(num_entries, 0);
    Begin_root(_vres[0])
      for (_c8 = 0; _c8 < num_entries; _c8++) {
        _v9 = camlidl_c2ml_z3V3_Z3_ast(&indices[_c8], _ctx);
        modify(&Field(_vres[0], _c8), _v9);
      }
    End_roots()
    _vres[1] = camlidl_alloc(num_entries, 0);
    Begin_root(_vres[1])
      for (_c10 = 0; _c10 < num_entries; _c10++) {
        _v11 = camlidl_c2ml_z3V3_Z3_ast(&values[_c10], _ctx);
        modify(&Field(_vres[1], _c10), _v11);
      }
    End_roots()
    _vres[2] = camlidl_c2ml_z3V3_Z3_ast(&*else_value, _ctx);
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_get_model_func_else(
	value _v_c,
	value _v_m,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_model_func_else(c, m, i);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_model_func_num_entries(
	value _v_c,
	value _v_m,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_model_func_num_entries(c, m, i);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_model_func_entry_num_args(
	value _v_c,
	value _v_m,
	value _v_i,
	value _v_j)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  unsigned int j; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  j = Int_val(_v_j);
  _res = Z3_get_model_func_entry_num_args(c, m, i, j);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_model_func_entry_arg(
	value _v_c,
	value _v_m,
	value _v_i,
	value _v_j,
	value _v_k)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  unsigned int j; /*in*/
  unsigned int k; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  j = Int_val(_v_j);
  k = Int_val(_v_k);
  _res = Z3_get_model_func_entry_arg(c, m, i, j, k);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_model_func_entry_value(
	value _v_c,
	value _v_m,
	value _v_i,
	value _v_j)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  unsigned int j; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  j = Int_val(_v_j);
  _res = Z3_get_model_func_entry_value(c, m, i, j);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_eval(
	value _v_c,
	value _v_m,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_ast t; /*in*/
  Z3_ast *v; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  Z3_ast _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3V3_Z3_ast(_v_t, &t, _ctx);
  v = &_c1;
  _res = Z3_eval(c, m, t, v);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = camlidl_c2ml_z3V3_Z3_ast(&*v, _ctx);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_eval_decl(
	value _v_c,
	value _v_m,
	value _v_d,
	value _v_args)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast *v; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  Z3_ast _c4;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3V3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3V3_Z3_func_decl(_v_d, &d, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3V3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  v = &_c4;
  _res = Z3_eval_decl(c, m, d, num_args, args, v);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = camlidl_c2ml_z3V3_Z3_ast(&*v, _ctx);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3V3_Z3_context_to_string(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_context_to_string(c);
  _vres = camlidl_c2ml_z3V3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_statistics_to_string(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_string _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_statistics_to_string(c);
  _vres = camlidl_c2ml_z3V3_Z3_string(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3V3_Z3_get_context_assignment(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3V3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_context_assignment(c);
  _vres = camlidl_c2ml_z3V3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

