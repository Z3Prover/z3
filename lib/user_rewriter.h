/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    user_rewriter.h

Abstract:

    Rewriter for applying user-defined rewrite routine.

Author:

    Nikolaj (nbjorner) 2012-01-08

Notes:

--*/
#ifndef _USER_REWRITER_H_
#define _USER_REWRITER_H_

#include "ast.h"
#include "rewriter.h"


class user_rewriter : public default_rewriter_cfg {
public:
    typedef bool fn(void* context, expr* expr_in, expr** expr_out, proof** proof_out);
private:
    ast_manager&                    m;
    rewriter_tpl<user_rewriter>     m_rw;
    void*                           m_ctx;
    fn*                             m_rewriter;
    bool                            m_rec;

public:
    user_rewriter(ast_manager & m): m(m), m_rw(m, m.proofs_enabled(), *this), m_rewriter(0), m_rec(false) {}
    ~user_rewriter() {}

    void set_rewriter(void * ctx, fn* rw) { m_ctx = ctx; m_rewriter = rw; }
    bool enabled() { return m_rewriter != 0; }

    void operator()(expr_ref& term) { expr_ref tmp(m); (*this)(tmp, term); }
    void operator()(expr * t, expr_ref & result) { proof_ref pr(m); (*this)(t, result, pr); }
    void operator()(expr * t, expr_ref & result, proof_ref & result_pr) { m_rw(t, result, result_pr); }

    void cancel() { set_cancel(true); }
    void reset_cancel() { set_cancel(false); }
    void set_cancel(bool f) { m_rw.set_cancel(f); }
    void cleanup() { if (!m_rec) { m_rec = true; m_rw.cleanup();  m_rec = false; } }
    void reset() { if (!m_rec) { m_rec = true; m_rw.reset(); m_rec = false; } }

    bool get_subst(expr* s, expr*& t, proof*& t_pr) {
        return enabled() && m_rewriter(m_ctx, s, &t, &t_pr);
    }
};

#endif
