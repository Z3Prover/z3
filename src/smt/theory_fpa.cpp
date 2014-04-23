/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    theory_fpa.cpp

Abstract:

    Floating-Point Theory Plugin

Author:

    Christoph (cwinter) 2014-04-23

Revision History:

--*/
#include"ast_smt2_pp.h"
#include"smt_context.h"
#include"theory_fpa.h"

namespace smt {

    theory_fpa::theory_fpa(ast_manager & m) : 
        theory(m.mk_family_id("float")), 
        m_converter(m), 
        m_rw(m, m_converter, params_ref()) 
    {
    }

    bool theory_fpa::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("fpa", tout << "internalizing atom: " << mk_ismt2_pp(atom, get_manager()) << "\n";);
        SASSERT(atom->get_family_id() == get_family_id());

        ast_manager & m = get_manager();
        context & ctx = get_context();
        
        expr_ref res(m);
        m_rw(atom, res);
        SASSERT(res.get() != atom);
        ctx.internalize(res, gate_ctx);
        return true;
    }

    void theory_fpa::new_eq_eh(theory_var, theory_var) {
        NOT_IMPLEMENTED_YET();
    }

    void theory_fpa::new_diseq_eh(theory_var, theory_var) {
        NOT_IMPLEMENTED_YET();
    }

    void theory_fpa::push_scope_eh() {
        NOT_IMPLEMENTED_YET();
    }

    void theory_fpa::pop_scope_eh(unsigned num_scopes) {
        NOT_IMPLEMENTED_YET();
    }
};
