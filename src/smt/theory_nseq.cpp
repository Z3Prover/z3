/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_nseq.cpp

Abstract:

    ZIPT string solver theory for Z3.
    Implementation of theory_nseq.

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#include "smt/theory_nseq.h"
#include "smt/smt_context.h"
#include "util/statistics.h"

namespace smt {

    theory_nseq::theory_nseq(context& ctx) :
        theory(ctx, ctx.get_manager().mk_family_id("seq")),
        m_seq(ctx.get_manager()),
        m_autil(ctx.get_manager()),
        m_rewriter(ctx.get_manager()),
        m_egraph(ctx.get_manager()),
        m_sgraph(ctx.get_manager(), m_egraph),
        m_nielsen(m_sgraph),
        m_state(m_sgraph)
    {}

    // -----------------------------------------------------------------------
    // Internalization
    // -----------------------------------------------------------------------

    bool theory_nseq::internalize_atom(app* atom, bool /*gate_ctx*/) {
        return internalize_term(atom);
    }

    bool theory_nseq::internalize_term(app* term) {
        context& ctx = get_context();
        ast_manager& m = get_manager();

        // ensure children are internalized first
        for (expr* arg : *term) {
            if (is_app(arg) && m_seq.is_seq(arg)) {
                ctx.internalize(arg, false);
            }
        }

        if (!ctx.e_internalized(term)) {
            ctx.mk_enode(term, false, m.is_bool(term), true);
        }

        enode* en = ctx.get_enode(term);
        if (!is_attached_to_var(en)) {
            theory_var v = mk_var(en);
            (void)v;
        }

        // register in our private sgraph
        get_snode(term);
        return true;
    }

    // -----------------------------------------------------------------------
    // Equality / disequality notifications
    // -----------------------------------------------------------------------

    void theory_nseq::new_eq_eh(theory_var v1, theory_var v2) {
        expr* e1 = get_enode(v1)->get_expr();
        expr* e2 = get_enode(v2)->get_expr();
        if (!m_seq.is_seq(e1) || !m_seq.is_seq(e2))
            return;
        euf::snode* s1 = get_snode(e1);
        euf::snode* s2 = get_snode(e2);
        if (s1 && s2)
            m_state.add_str_eq(s1, s2);
    }

    void theory_nseq::new_diseq_eh(theory_var /*v1*/, theory_var /*v2*/) {
        // not handled in this initial skeleton
    }

    // -----------------------------------------------------------------------
    // Scope management
    // -----------------------------------------------------------------------

    void theory_nseq::push_scope_eh() {
        theory::push_scope_eh();
        m_state.push();
        m_sgraph.push();
    }

    void theory_nseq::pop_scope_eh(unsigned num_scopes) {
        theory::pop_scope_eh(num_scopes);
        m_state.pop(num_scopes);
        m_sgraph.pop(num_scopes);
    }

    // -----------------------------------------------------------------------
    // Final check: build Nielsen graph and search
    // -----------------------------------------------------------------------

    void theory_nseq::populate_nielsen_graph() {
        m_nielsen.reset();
        seq::nielsen_node* root = m_nielsen.mk_node();
        m_nielsen.set_root(root);
        for (auto const& eq : m_state.str_eqs())
            root->add_str_eq(eq);
        for (auto const& mem : m_state.str_mems())
            root->add_str_mem(mem);
    }

    final_check_status theory_nseq::final_check_eh(unsigned /*final_check_round*/) {
        if (m_state.empty())
            return FC_DONE;
        // For now, give up if there are string constraints.
        // The full search will be wired in once the Nielsen algorithms are complete.
        populate_nielsen_graph();
        ++m_num_nodes_explored;
        return FC_GIVEUP;
    }

    // -----------------------------------------------------------------------
    // Model generation
    // -----------------------------------------------------------------------

    void theory_nseq::init_model(model_generator& /*mg*/) {
        // stub – no model assignment for now
    }

    // -----------------------------------------------------------------------
    // Statistics / display
    // -----------------------------------------------------------------------

    void theory_nseq::collect_statistics(::statistics& st) const {
        st.update("nseq conflicts",       m_num_conflicts);
        st.update("nseq nodes explored",  m_num_nodes_explored);
        st.update("nseq depth increases", m_num_depth_increases);
    }

    void theory_nseq::display(std::ostream& out) const {
        out << "theory_nseq\n";
        out << "  str_eqs: " << m_state.str_eqs().size() << "\n";
        out << "  str_mems: " << m_state.str_mems().size() << "\n";
    }

    // -----------------------------------------------------------------------
    // Factory / clone
    // -----------------------------------------------------------------------

    theory* theory_nseq::mk_fresh(context* ctx) {
        return alloc(theory_nseq, *ctx);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    euf::snode* theory_nseq::get_snode(expr* e) {
        euf::snode* s = m_sgraph.find(e);
        if (!s)
            s = m_sgraph.mk(e);
        return s;
    }

}
