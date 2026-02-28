/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    theory_nseq.cpp

Abstract:

    Theory solver for strings based on Nielsen transformations
    and lazy regex membership (ZIPT algorithm).

Author:

    Clemens Eisenhofer
    Nikolaj Bjorner (nbjorner) 2025-2-28

--*/

#include "smt/theory_nseq.h"
#include "smt/smt_context.h"

namespace smt {

    theory_nseq::theory_nseq(context& ctx)
        : theory(ctx, ctx.get_manager().mk_family_id("seq")),
          m_util(ctx.get_manager()),
          m_autil(ctx.get_manager()),
          m_seq_rewrite(ctx.get_manager()),
          m_rewrite(ctx.get_manager()),
          m_sk(ctx.get_manager(), m_rewrite),
          m_arith_value(ctx.get_manager()),
          m_has_seq(false) {
    }

    theory_nseq::~theory_nseq() {
    }

    void theory_nseq::init() {
    }

    final_check_status theory_nseq::final_check_eh(unsigned) {
        if (m_has_seq)
            return FC_GIVEUP;
        return FC_DONE;
    }

    bool theory_nseq::internalize_atom(app* atom, bool) {
        if (!m_has_seq) {
            get_context().push_trail(value_trail<bool>(m_has_seq));
            m_has_seq = true;
        }
        return false;
    }

    bool theory_nseq::internalize_term(app* term) {
        if (!m_has_seq) {
            get_context().push_trail(value_trail<bool>(m_has_seq));
            m_has_seq = true;
        }
        return false;
    }

    void theory_nseq::internalize_eq_eh(app* atom, bool_var v) {
    }

    void theory_nseq::new_eq_eh(theory_var v1, theory_var v2) {
    }

    void theory_nseq::new_diseq_eh(theory_var v1, theory_var v2) {
    }

    void theory_nseq::assign_eh(bool_var v, bool is_true) {
    }

    bool theory_nseq::can_propagate() {
        return false;
    }

    void theory_nseq::propagate() {
    }

    void theory_nseq::push_scope_eh() {
        theory::push_scope_eh();
    }

    void theory_nseq::pop_scope_eh(unsigned num_scopes) {
        theory::pop_scope_eh(num_scopes);
    }

    void theory_nseq::restart_eh() {
    }

    void theory_nseq::relevant_eh(app* n) {
    }

    theory_var theory_nseq::mk_var(enode* n) {
        return theory::mk_var(n);
    }

    void theory_nseq::apply_sort_cnstr(enode* n, sort* s) {
    }

    void theory_nseq::display(std::ostream& out) const {
        out << "theory_nseq\n";
    }

    void theory_nseq::collect_statistics(::statistics& st) const {
    }

    model_value_proc* theory_nseq::mk_value(enode* n, model_generator& mg) {
        return nullptr;
    }

    void theory_nseq::init_model(model_generator& mg) {
        mg.register_factory(alloc(seq_factory, get_manager(), get_family_id(), mg.get_model()));
    }

    void theory_nseq::finalize_model(model_generator& mg) {
    }
}
