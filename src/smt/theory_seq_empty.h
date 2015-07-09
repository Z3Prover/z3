/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    theory_seq_empty.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2011-14-11

Revision History:

--*/
#ifndef THEORY_SEQ_EMPTY_H_
#define THEORY_SEQ_EMPTY_H_

#include "smt_theory.h"

namespace smt {
    class theory_seq_empty : public theory {
        bool m_used;
        virtual final_check_status final_check_eh() { return m_used?FC_GIVEUP:FC_DONE; }
        virtual bool internalize_atom(app*, bool) { if (!m_used) { get_context().push_trail(value_trail<context,bool>(m_used)); m_used = true; } return false; }
        virtual bool internalize_term(app*) { return internalize_atom(0,false);  }
        virtual void new_eq_eh(theory_var, theory_var) { }
        virtual void new_diseq_eh(theory_var, theory_var) {}
        virtual theory* mk_fresh(context*) { return alloc(theory_seq_empty, get_manager()); }
        virtual char const * get_name() const { return "seq-empty"; }
    public:
        theory_seq_empty(ast_manager& m):theory(m.mk_family_id("seq")), m_used(false) {}
    };

};

#endif /* THEORY_SEQ_EMPTY_H_ */

