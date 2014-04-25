/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    theory_fpa.h

Abstract:

    Floating-Point Theory Plugin

Author:

    Christoph (cwinter) 2014-04-23

Revision History:

--*/
#ifndef _THEORY_FPA_H_
#define _THEORY_FPA_H_

#include"smt_theory.h"
#include"fpa2bv_converter.h"

namespace smt {
    class theory_fpa : public theory {
        fpa2bv_converter m_converter;

        virtual final_check_status final_check_eh() { return FC_DONE; }
        virtual bool internalize_atom(app*, bool);
        virtual bool internalize_term(app*) { return internalize_atom(0, false); }
        virtual void new_eq_eh(theory_var, theory_var);
        virtual void new_diseq_eh(theory_var, theory_var);
        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);
        virtual theory* mk_fresh(context*) { return alloc(theory_fpa, get_manager()); }
        virtual char const * get_name() const { return "fpa"; }
    public:
        theory_fpa(ast_manager& m) : theory(m.mk_family_id("fpa")), m_converter(m) {}
    };

};

#endif /* _THEORY_FPA_H_ */

