
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
#pragma once;

#include "smt/smt_arith_value.h"
#include "smt/theory_lra.h"
#include "smt/theory_arith.h"

namespace smt {

    arith_value::arith_value(context& ctx): 
        m_ctx(ctx), m(ctx.get_manager()), a(m) {}

    bool arith_value::get_lo(expr* e, rational& lo, bool& is_strict) {
        if (!m_ctx.e_internalized(e)) return false;
        family_id afid = a.get_family_id();
        is_strict = false;
        enode* next = m_ctx.get_enode(e), *n = next;
        bool found = false;
        bool is_strict1; 
        rational lo1;
        theory* th = m_ctx.get_theory(afid);
        theory_mi_arith* tha = dynamic_cast<theory_mi_arith*>(th);
        theory_i_arith*  thi = dynamic_cast<theory_i_arith*>(th);
        theory_lra*      thr = dynamic_cast<theory_lra*>(th);
        do {
            if ((tha && tha->get_lower(next, lo1, is_strict1)) ||
                (thi && thi->get_lower(next, lo1, is_strict1)) ||
                (thr && thr->get_lower(next, lo1, is_strict1))) {
                if (!found || lo1 > lo || (lo == lo1 && is_strict1)) lo = lo1, is_strict = is_strict1;
                found = true;
            }
            next = next->get_next();
        }
        while (n != next);
        return found;
    }

    bool arith_value::get_up(expr* e, rational& up, bool& is_strict) {
        if (!m_ctx.e_internalized(e)) return false;
        family_id afid = a.get_family_id();
        is_strict = false;
        enode* next = m_ctx.get_enode(e), *n = next;
        bool found = false, is_strict1;
        rational up1;
        theory* th = m_ctx.get_theory(afid);
        theory_mi_arith* tha = dynamic_cast<theory_mi_arith*>(th);
        theory_i_arith*  thi = dynamic_cast<theory_i_arith*>(th);
        theory_lra*      thr = dynamic_cast<theory_lra*>(th);
        do {
            if ((tha && tha->get_upper(next, up1, is_strict1)) ||
                (thi && thi->get_upper(next, up1, is_strict1)) ||
                (thr && thr->get_upper(next, up1, is_strict1))) {
                if (!found || up1 < up || (up1 == up && is_strict1)) up = up1, is_strict = is_strict1;
                found = true;
            }
            next = next->get_next();
        }
        while (n != next);
        return found;
    }

    bool arith_value::get_value(expr* e, rational& val) {
        if (!m_ctx.e_internalized(e)) return false;
        expr_ref _val(m);
        enode* next = m_ctx.get_enode(e), *n = next;
        family_id afid = a.get_family_id();
        theory* th = m_ctx.get_theory(afid);
        theory_mi_arith* tha = dynamic_cast<theory_mi_arith*>(th);
        theory_i_arith* thi = dynamic_cast<theory_i_arith*>(th);
        theory_lra* thr = dynamic_cast<theory_lra*>(th);           
        do { 
            e = next->get_owner();
            if (tha && tha->get_value(next, _val) && a.is_numeral(_val, val)) return true;
            if (thi && thi->get_value(next, _val) && a.is_numeral(_val, val)) return true;
            if (thr && thr->get_value(next, val)) return true;
            next = next->get_next();
        }
        while (next != n);
        return false;
    }
};
