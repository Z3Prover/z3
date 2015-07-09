/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_no_arith.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-12-30.

Revision History:

--*/
#ifndef THEORY_DUMMY_H_
#define THEORY_DUMMY_H_

#include"smt_theory.h"

namespace smt {

    /**
       \brief Do nothing theory. Tracks whether theory expressions were internalized.
       When theory expressions were internalized, it returns FC_GIVEUP in the final_check_eh.
    */
    class theory_dummy : public theory {
        bool         m_theory_exprs;
        char const * m_name;
        void found_theory_expr();

    protected:
        virtual bool internalize_atom(app * atom, bool gate_ctx);
        virtual bool internalize_term(app * term);
        virtual void new_eq_eh(theory_var v1, theory_var v2);
        virtual bool use_diseqs() const;
        virtual void new_diseq_eh(theory_var v1, theory_var v2);
        virtual void reset_eh();
        virtual final_check_status final_check_eh();
        virtual bool build_models() const { 
            return false;
        }

    public:
        theory_dummy(family_id fid, char const * name);
        virtual ~theory_dummy() {}

        virtual theory * mk_fresh(context * new_ctx) { return alloc(theory_dummy, get_family_id(), m_name); }

        virtual char const * get_name() const;
    };
};

#endif /* THEORY_DUMMY_H_ */

