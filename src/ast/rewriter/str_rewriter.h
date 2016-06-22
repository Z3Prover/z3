/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    str_rewriter.h

Abstract:

    AST rewriting rules for string terms.

Author:

    Murphy Berzish

Notes:

--*/

#include"str_decl_plugin.h"
#include"arith_decl_plugin.h"
#include"rewriter_types.h"
#include"params.h"

class str_rewriter {
    str_util m_strutil;
    arith_util m_autil;

public:
    str_rewriter(ast_manager & m, params_ref const & p = params_ref()) :
        m_strutil(m), m_autil(m) {
    }

    ast_manager & m() const { return m_strutil.get_manager(); }
    family_id get_fid() const { return m_strutil.get_family_id(); }

    void updt_params(params_ref const & p) {}
    static void get_param_descrs(param_descrs & r) {}

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_eq_core(expr * lhs, expr * rhs, expr_ref & result);

    br_status mk_str_CharAt(expr * arg0, expr * arg1, expr_ref & result);
    br_status mk_str_StartsWith(expr * haystack, expr * needle, expr_ref & result);
    br_status mk_str_EndsWith(expr * haystack, expr * needle, expr_ref & result);
    br_status mk_str_Contains(expr * haystack, expr * needle, expr_ref & result);
    br_status mk_str_Indexof(expr * haystack, expr * needle, expr_ref & result);
    br_status mk_str_Indexof2(expr * arg0, expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_str_LastIndexof(expr * haystack, expr * needle, expr_ref & result);
    br_status mk_str_Replace(expr * base, expr * source, expr * target, expr_ref & result);

    br_status mk_re_Str2Reg(expr * str, expr_ref & result);
    br_status mk_re_RegexIn(expr * str, expr * re, expr_ref & result);

    bool reduce_eq(expr * l, expr * r, expr_ref_vector & lhs, expr_ref_vector & rhs, bool & change);
    bool reduce_eq(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_vector& lhs, expr_ref_vector& rhs, bool& change);

};
