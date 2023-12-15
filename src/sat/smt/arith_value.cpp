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
#include "sat/smt/arith_value.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_solver.h"

namespace arith {

    arith_value::arith_value(euf::solver& s) :
        s(s), m(s.get_manager()), a(m) {}

    void arith_value::init() {
        if (!as)
            as = dynamic_cast<arith::solver*>(s.fid2solver(a.get_family_id()));
    }

    bool arith_value::get_value(expr* e, rational& val) {
        auto n = s.get_enode(e);
        expr_ref _val(m);
        init();
        return n && as->get_value(n, _val) && a.is_numeral(_val, val);
    }

#if 0
    bool arith_value::get_lo_equiv(expr* e, rational& lo, bool& is_strict) {
        if (!s.get_enode(e))
            return false;
        init();
        is_strict = false;
        bool found = false;
        bool is_strict1;
        rational lo1;
        for (auto sib : euf::enode_class(s.get_enode(e))) {
            if (!as->get_lower(sib, lo1, is_strict1))
                continue;
            if (!found || lo1 > lo || lo == lo1 && is_strict1)
                lo = lo1, is_strict = is_strict1;
            found = true;
        }
        CTRACE("arith_value", !found, tout << "value not found for " << mk_pp(e, m) << "\n";);
        return found;
    }

    bool arith_value::get_up_equiv(expr* e, rational& hi, bool& is_strict) {
        if (!s.get_enode(e))
            return false;
        init();
        is_strict = false;
        bool found = false;
        bool is_strict1;
        rational hi1;
        for (auto sib : euf::enode_class(s.get_enode(e))) {
            if (!as->get_upper(sib, hi1, is_strict1))
                continue;
            if (!found || hi1 < hi || hi == hi1 && is_strict1)
                hi = hi1, is_strict = is_strict1;
            found = true;
        }
        CTRACE("arith_value", !found, tout << "value not found for " << mk_pp(e, m) << "\n";);
        return found;
    }

    bool arith_value::get_up(expr* e, rational& up, bool& is_strict) const {
        init();
        enode* n = s.get_enode(e);
        is_strict = false;
        return n && as->get_upper(n, up, is_strict);
    }

    bool arith_value::get_lo(expr* e, rational& lo, bool& is_strict) const {
        init();
        enode* n = s.get_enode(e);
        is_strict = false;
        return n && as->get_lower(n, lo, is_strict);
    }

#endif


#if 0


    bool arith_value::get_value_equiv(expr* e, rational& val) const {
        if (!m_ctx->e_internalized(e)) return false;
        expr_ref _val(m);
        enode* next = m_ctx->get_enode(e), * n = next;
        do {
            e = next->get_expr();
            if (m_tha && m_tha->get_value(next, _val) && a.is_numeral(_val, val)) return true;
            if (m_thi && m_thi->get_value(next, _val) && a.is_numeral(_val, val)) return true;
            if (m_thr && m_thr->get_value(next, val)) return true;
            next = next->get_next();
        } while (next != n);
        TRACE("arith_value", tout << "value not found for " << mk_pp(e, m_ctx->get_manager()) << "\n";);
        return false;
    }

    expr_ref arith_value::get_lo(expr* e) const {
        rational lo;
        bool s = false;
        if ((a.is_int_real(e) || b.is_bv(e)) && get_lo(e, lo, s) && !s) {
            return expr_ref(a.mk_numeral(lo, e->get_sort()), m);
        }
        return expr_ref(e, m);
    }

    expr_ref arith_value::get_up(expr* e) const {
        rational up;
        bool s = false;
        if ((a.is_int_real(e) || b.is_bv(e)) && get_up(e, up, s) && !s) {
            return expr_ref(a.mk_numeral(up, e->get_sort()), m);
        }
        return expr_ref(e, m);
    }

    expr_ref arith_value::get_fixed(expr* e) const {
        rational lo, up;
        bool s = false;
        if (a.is_int_real(e) && get_lo(e, lo, s) && !s && get_up(e, up, s) && !s && lo == up) {
            return expr_ref(a.mk_numeral(lo, e->get_sort()), m);
        }
        return expr_ref(e, m);
    }

#endif

};
