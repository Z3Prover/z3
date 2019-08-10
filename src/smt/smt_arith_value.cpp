/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    smt_arith_value.cpp

Abstract:

    Utility to extract arithmetic values from context.

Author:

    Nikolaj Bjorner (nbjorner) 2018-12-08.

Revision History:

--*/

#include "ast/ast_pp.h"
#include "smt/smt_arith_value.h"

namespace smt {

    arith_value::arith_value(ast_manager& m): 
        m_ctx(nullptr), m(m), a(m) {}

    void arith_value::init(context* ctx) {
        m_ctx = ctx;
        family_id afid = a.get_family_id();
        theory* th = m_ctx->get_theory(afid);
        m_tha = dynamic_cast<theory_mi_arith*>(th);
        m_thi = dynamic_cast<theory_i_arith*>(th);
        m_thr = dynamic_cast<theory_lra*>(th);
    }

    bool arith_value::get_lo_equiv(expr* e, rational& lo, bool& is_strict) {
        if (!m_ctx->e_internalized(e)) return false;
        is_strict = false;
        enode* next = m_ctx->get_enode(e), *n = next;
        bool found = false;
        bool is_strict1; 
        rational lo1;
        do {
            if ((m_tha && m_tha->get_lower(next, lo1, is_strict1)) ||
                (m_thi && m_thi->get_lower(next, lo1, is_strict1)) ||
                (m_thr && m_thr->get_lower(next, lo1, is_strict1))) {
                if (!found || lo1 > lo || (lo == lo1 && is_strict1)) lo = lo1, is_strict = is_strict1;
                found = true;
            }
            next = next->get_next();
        }
        while (n != next);
        CTRACE("arith_value", !found, tout << "value not found for " << mk_pp(e, m_ctx->get_manager()) << "\n";);
        return found;
    }

    bool arith_value::get_up_equiv(expr* e, rational& up, bool& is_strict) {
        if (!m_ctx->e_internalized(e)) return false;
        is_strict = false;
        enode* next = m_ctx->get_enode(e), *n = next;
        bool found = false, is_strict1;
        rational up1;
        do {
            if ((m_tha && m_tha->get_upper(next, up1, is_strict1)) ||
                (m_thi && m_thi->get_upper(next, up1, is_strict1)) ||
                (m_thr && m_thr->get_upper(next, up1, is_strict1))) {
                if (!found || up1 < up || (up1 == up && is_strict1)) up = up1, is_strict = is_strict1;
                found = true;
            }
            next = next->get_next();
        }
        while (n != next);
        CTRACE("arith_value", !found, tout << "value not found for " << mk_pp(e, m_ctx->get_manager()) << "\n";);
        return found;
    }

    bool arith_value::get_up(expr* e, rational& up, bool& is_strict) const {
        if (!m_ctx->e_internalized(e)) return false;
        is_strict = false;
        enode* n = m_ctx->get_enode(e);
        if (m_tha) return m_tha->get_upper(n, up, is_strict);
        if (m_thi) return m_thi->get_upper(n, up, is_strict);
        if (m_thr) return m_thr->get_upper(n, up, is_strict);
        TRACE("arith_value", tout << "value not found for " << mk_pp(e, m_ctx->get_manager()) << "\n";);
        return false;
    }

    bool arith_value::get_lo(expr* e, rational& up, bool& is_strict) const {
        if (!m_ctx->e_internalized(e)) return false;
        is_strict = false;
        enode* n = m_ctx->get_enode(e);
        if (m_tha) return m_tha->get_lower(n, up, is_strict);
        if (m_thi) return m_thi->get_lower(n, up, is_strict);
        if (m_thr) return m_thr->get_lower(n, up, is_strict);
        TRACE("arith_value", tout << "value not found for " << mk_pp(e, m_ctx->get_manager()) << "\n";);
        return false;
    }

    bool arith_value::get_value(expr* e, rational& val) const {
        if (!m_ctx->e_internalized(e)) return false;
        expr_ref _val(m);
        enode* n = m_ctx->get_enode(e);
        if (m_tha && m_tha->get_value(n, _val) && a.is_numeral(_val, val)) return true;
        if (m_thi && m_thi->get_value(n, _val) && a.is_numeral(_val, val)) return true;
        if (m_thr && m_thr->get_value(n, val)) return true;
        TRACE("arith_value", tout << "value not found for " << mk_pp(e, m_ctx->get_manager()) << "\n";);
        return false;
    }


    bool arith_value::get_value_equiv(expr* e, rational& val) const {
        if (!m_ctx->e_internalized(e)) return false;
        expr_ref _val(m);
        enode* next = m_ctx->get_enode(e), *n = next;
        do { 
            e = next->get_owner();
            if (m_tha && m_tha->get_value(next, _val) && a.is_numeral(_val, val)) return true;
            if (m_thi && m_thi->get_value(next, _val) && a.is_numeral(_val, val)) return true;
            if (m_thr && m_thr->get_value(next, val)) return true;
            next = next->get_next();
        }
        while (next != n);
        TRACE("arith_value", tout << "value not found for " << mk_pp(e, m_ctx->get_manager()) << "\n";);
        return false;
    }

    final_check_status arith_value::final_check() {
        family_id afid = a.get_family_id();
        theory * th = m_ctx->get_theory(afid);
        return th->final_check_eh();
    }
};
