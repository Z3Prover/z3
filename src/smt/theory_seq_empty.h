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
#pragma once

#include "ast/seq_decl_plugin.h"
#include "model/seq_factory.h"
#include "smt/smt_theory.h"
#include "smt/smt_model_generator.h"

namespace smt {

    class theory_seq_empty : public theory {
        bool m_used;
        final_check_status final_check_eh() override { return m_used?FC_GIVEUP:FC_DONE; }
        bool internalize_atom(app*, bool) override { if (!m_used) { get_context().push_trail(value_trail<bool>(m_used)); m_used = true; } return false; }
        bool internalize_term(app*) override { return internalize_atom(nullptr,false);  }
        void new_eq_eh(theory_var, theory_var) override { }
        void new_diseq_eh(theory_var, theory_var) override {}
        theory* mk_fresh(context* new_ctx) override { return alloc(theory_seq_empty, *new_ctx); }
        char const * get_name() const override { return "seq-empty"; }
        void display(std::ostream& out) const override {}
    public:
        theory_seq_empty(context& ctx):theory(ctx, ctx.get_manager().mk_family_id("seq")), m_used(false) {}
        void init_model(model_generator & mg) override {
            mg.register_factory(alloc(seq_factory, get_manager(), get_family_id(), mg.get_model()));
        }

    };

};


