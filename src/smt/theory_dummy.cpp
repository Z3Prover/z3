/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_dummy.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-12-30.

Revision History:

--*/

#include "smt/smt_context.h"
#include "smt/theory_dummy.h"

namespace smt {

    void theory_dummy::found_theory_expr() {
        if (!m_theory_exprs) {
            get_context().push_trail(value_trail<context, bool>(m_theory_exprs));
            m_theory_exprs = true;
        }
    }

    theory_dummy::theory_dummy(family_id fid, char const * name):
        theory(fid),
        m_theory_exprs(false),
        m_name(name) {
    }

    bool theory_dummy::internalize_atom(app * atom, bool gate_ctx) {
        found_theory_expr();
        return false;
    }

    bool theory_dummy::internalize_term(app * term) {
        found_theory_expr();
        return false;
    }

    void theory_dummy::new_eq_eh(theory_var v1, theory_var v2) {
        UNREACHABLE();
    }

    bool theory_dummy::use_diseqs() const {
        return false; 
    }

    void theory_dummy::new_diseq_eh(theory_var v1, theory_var v2) {
        UNREACHABLE();
    }

    void theory_dummy::reset_eh() {
        m_theory_exprs = true;
        theory::reset_eh();
    }

    final_check_status theory_dummy::final_check_eh() {
        return m_theory_exprs ? FC_GIVEUP : FC_DONE;
    }

    char const * theory_dummy::get_name() const { 
        return m_name; 
    }

};
