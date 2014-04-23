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
#include"theory_fpa.h"

namespace smt {

    bool theory_fpa::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("bv", tout << "internalizing atom: " << mk_ismt2_pp(atom, get_manager()) << "\n";);
        SASSERT(atom->get_family_id() == get_family_id());
        NOT_IMPLEMENTED_YET();
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
