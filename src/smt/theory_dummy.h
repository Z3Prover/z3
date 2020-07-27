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
#pragma once

#include "smt/smt_theory.h"

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
        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        void new_eq_eh(theory_var v1, theory_var v2) override;
        bool use_diseqs() const override;
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        void reset_eh() override;
        final_check_status final_check_eh() override;
        bool build_models() const override {
            return false;
        }
        void display(std::ostream& out) const override {}

    public:
        theory_dummy(context& ctx, family_id fid, char const * name);
        ~theory_dummy() override {}

        theory * mk_fresh(context * new_ctx) override { return alloc(theory_dummy, *new_ctx, get_family_id(), m_name); }

        char const * get_name() const override;
    };
};


