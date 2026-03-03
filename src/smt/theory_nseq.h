/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_nseq.h

Abstract:

    ZIPT string solver theory for Z3.
    Implements theory_nseq, a theory plugin for string/sequence constraints
    using the Nielsen transformation graph (Nielsen graph).

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_sgraph.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "smt/seq/seq_nielsen.h"
#include "smt/nseq_state.h"
#include "smt/nseq_regex.h"
#include "smt/nseq_model.h"

namespace smt {

    class theory_nseq : public theory {
        seq_util       m_seq;
        arith_util     m_autil;
        seq_rewriter   m_rewriter;
        euf::egraph    m_egraph;  // private egraph (not shared with smt context)
        euf::sgraph    m_sgraph;  // private sgraph
        seq::nielsen_graph m_nielsen;
        nseq_state     m_state;

        // statistics
        unsigned m_num_conflicts        = 0;
        unsigned m_num_nodes_explored   = 0;
        unsigned m_num_depth_increases  = 0;

        // map from context enode to private sgraph snode
        obj_map<expr, euf::snode*> m_expr2snode;

        // required virtual methods
        bool internalize_atom(app* a, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        void new_eq_eh(theory_var v1, theory_var v2) override;
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        theory* mk_fresh(context* ctx) override;
        void display(std::ostream& out) const override;

        // optional overrides
        bool can_propagate() override { return false; }
        void propagate() override {}
        final_check_status final_check_eh(unsigned) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void init_model(model_generator& mg) override;
        void collect_statistics(::statistics& st) const override;

        char const* get_name() const override { return "nseq"; }

        // private helpers
        void populate_nielsen_graph();
        euf::snode* get_snode(expr* e);

    public:
        theory_nseq(context& ctx);
    };

}
