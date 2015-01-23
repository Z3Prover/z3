/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    mk_simplified_app.cpp

Abstract:

    Functor for creating new simplified applications

Author:

    Leonardo (leonardo) 2011-06-06

Notes:

--*/
#include"mk_simplified_app.h"
#include"bool_rewriter.h"
#include"arith_rewriter.h"
#include"bv_rewriter.h"
#include"datatype_rewriter.h"
#include"array_rewriter.h"
#include"fpa_rewriter.h"

struct mk_simplified_app::imp {
    ast_manager &         m;
    bool_rewriter         m_b_rw;
    arith_rewriter        m_a_rw;
    bv_rewriter           m_bv_rw;
    array_rewriter        m_ar_rw;
    datatype_rewriter     m_dt_rw;
    fpa_rewriter          m_f_rw;

    imp(ast_manager & _m, params_ref const & p):
        m(_m),
        m_b_rw(m, p),
        m_a_rw(m, p),
        m_bv_rw(m, p),
        m_ar_rw(m, p),
        m_dt_rw(m),
        m_f_rw(m, p) {
    }
        
    br_status mk_core(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
        family_id fid = f->get_family_id();
        if (fid == null_family_id)
            return BR_FAILED;
        br_status st = BR_FAILED;
        if (fid == m_b_rw.get_fid()) {
            decl_kind k = f->get_decl_kind();
            if (k == OP_EQ) {
                // theory dispatch for =
                SASSERT(num == 2);
                family_id s_fid = m.get_sort(args[0])->get_family_id();
                if (s_fid == m_a_rw.get_fid())
                    st = m_a_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_bv_rw.get_fid())
                    st = m_bv_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_dt_rw.get_fid())
                    st = m_dt_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_f_rw.get_fid())
                    st = m_f_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_ar_rw.get_fid())
                    st = m_ar_rw.mk_eq_core(args[0], args[1], result);
                
                if (st != BR_FAILED)
                    return st;
            }
            return m_b_rw.mk_app_core(f, num, args, result);
        }
        if (fid == m_a_rw.get_fid())
            return m_a_rw.mk_app_core(f, num, args, result);
        if (fid == m_bv_rw.get_fid())
            return m_bv_rw.mk_app_core(f, num, args, result);
        if (fid == m_ar_rw.get_fid())
            return m_ar_rw.mk_app_core(f, num, args, result);
        if (fid == m_dt_rw.get_fid())
            return m_dt_rw.mk_app_core(f, num, args, result);
        if (fid == m_f_rw.get_fid())
            return m_f_rw.mk_app_core(f, num, args, result);
        return BR_FAILED;
    }
};


mk_simplified_app::mk_simplified_app(ast_manager & m, params_ref const & p):
    m_imp(alloc(imp, m, p)) {
}

mk_simplified_app::~mk_simplified_app() {
    dealloc(m_imp);
}

br_status mk_simplified_app::mk_core(func_decl * decl, unsigned num, expr * const * args, expr_ref & result) {
    return m_imp->mk_core(decl, num, args, result);
}

void mk_simplified_app::operator()(func_decl * decl, unsigned num, expr * const * args, expr_ref & result) {
    result = 0;
    mk_core(decl, num, args, result);
    if (!result) 
        result = m_imp->m.mk_app(decl, num, args);
    // TODO: if the result of mk_core is different from BR_FAILED, then the
    // result is not really simplified.
}
