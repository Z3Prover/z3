/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    seq_rewriter.h

Abstract:

    Basic rewriting rules for sequences constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2015-12-5

Notes:

--*/
#ifndef SEQ_REWRITER_H_
#define SEQ_REWRITER_H_

#include"seq_decl_plugin.h"
#include"arith_decl_plugin.h"
#include"rewriter_types.h"
#include"params.h"
#include"lbool.h"


/**
   \brief Cheap rewrite rules for seq constraints
*/
class seq_rewriter {
    seq_util       m_util;
    arith_util     m_autil;
    ptr_vector<expr> m_es;

    br_status mk_str_concat(expr* a, expr* b, expr_ref& result);
    br_status mk_str_length(expr* a, expr_ref& result);
    br_status mk_str_substr(expr* a, expr* b, expr* c, expr_ref& result);
    br_status mk_str_strctn(expr* a, expr* b, expr_ref& result);
    br_status mk_str_charat(expr* a, expr* b, expr_ref& result);
    br_status mk_str_stridof(expr* a, expr* b, expr* c, expr_ref& result);
    br_status mk_str_strrepl(expr* a, expr* b, expr* c, expr_ref& result);
    br_status mk_str_prefix(expr* a, expr* b, expr_ref& result);
    br_status mk_str_suffix(expr* a, expr* b, expr_ref& result);
    br_status mk_str_itos(expr* a, expr_ref& result);
    br_status mk_str_stoi(expr* a, expr_ref& result);
    br_status mk_str_in_regexp(expr* a, expr* b, expr_ref& result);
    br_status mk_str_to_regexp(expr* a, expr_ref& result);
    br_status mk_re_concat(expr* a, expr* b, expr_ref& result);
    br_status mk_re_union(expr* a, expr* b, expr_ref& result);
    br_status mk_re_star(expr* a, expr_ref& result);
    br_status mk_re_plus(expr* a, expr_ref& result);
    br_status mk_re_opt(expr* a, expr_ref& result);

public:    
    seq_rewriter(ast_manager & m, params_ref const & p = params_ref()):
        m_util(m), m_autil(m) {
    }
    ast_manager & m() const { return m_util.get_manager(); }
    family_id get_fid() const { return m_util.get_family_id(); }

    void updt_params(params_ref const & p) {}
    static void get_param_descrs(param_descrs & r) {}

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

};

#endif
