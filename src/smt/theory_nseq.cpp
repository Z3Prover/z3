/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_nseq.cpp

Abstract:

    Implementation of theory_nseq: see theory_nseq.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "smt/theory_nseq.h"
#include "smt/seq_nseq_ambient_context.h"
#include "smt/smt_context.h"
#include "util/trail.h"

namespace smt {

    theory_nseq::theory_nseq(context& ctx) :
        theory(ctx, ctx.get_manager().mk_family_id("seq")),
        m_seq(m),
        m_autil(m),
        m_rewriter(m),
        m_arith_value(m),
        m_live(m_rewriter),
        m_root(m_tree.mk_root()),
        m_solver(m, m_autil, m_tree.dep_mgr())
    {
        m_eq_id = m_tree.register_facet<seq::eq_facet>(*m_root, m, m_seq, m_tree.dep_mgr());
        m_deq_id = m_tree.register_facet<seq::deq_facet>(*m_root, m, m_seq, m_tree.dep_mgr());
        m_arith_id = m_tree.register_facet<seq::solver_facet>(*m_root, m, m_seq, m_solver);
        m_pow_id = m_tree.register_facet<seq::power_facet>(*m_root, m, m_seq, m_autil, m_tree.dep_mgr());
        m_mem_id = m_tree.register_facet<seq::mem_facet>(*m_root, m, m_seq, m_tree.dep_mgr());
        m_nc_id = m_tree.register_facet<seq::ncontains_facet>(*m_root, m, m_seq, m_tree.dep_mgr());

        m_ambient = alloc(seq::theory_nseq_ambient_context, *this);
        m_ambient->set_eq_id(m_eq_id);
        m_ambient->set_deq_id(m_deq_id);
        m_ambient->set_arith_id(m_arith_id);
        m_ambient->set_pow_id(m_pow_id);
        m_ambient->set_mem_id(m_mem_id);
        m_ambient->set_ncontains_id(m_nc_id);
        m_tree.set_ambient_context(m_ambient.get());

        // deterministic propagation plugins (order among these does not
        // matter: the engine iterates every propagation plugin to
        // fixpoint before ever consulting a split plugin). Each plugin
        // is heap-allocated and handed to `m_tree`, which owns it from
        // here on (stored in its own `scoped_ptr_vector`, deallocated
        // with the tree) - see stx_search_tree.h's
        // `add_propagation_plugin`/`add_split_plugin`.
        m_tree.add_propagation_plugin(alloc(seq::eq_propagation, m, m_seq));
        m_tree.add_propagation_plugin(alloc(seq::deq_propagation, m, m_seq));
        m_tree.add_propagation_plugin(alloc(seq::arith_propagation, m, m_seq));
        m_tree.add_propagation_plugin(alloc(seq::power_propagation, m, m_seq, m_autil));
        m_tree.add_propagation_plugin(alloc(seq::mem_propagation, m, m_seq, m_rewriter, m_live));
        m_tree.add_propagation_plugin(alloc(seq::mem_bounds_propagation, m, m_seq, m_autil, m_tree.trail()));
        m_tree.add_propagation_plugin(alloc(seq::ncontains_propagation, m, m_seq, m_autil));

        // split plugins: registration order mirrors the priority order of
        // the c3 branch's nielsen_graph::generate_extensions (see
        // theory_nseq.h's module comment for the mapping table).
        m_tree.add_split_plugin(alloc(seq::eq_approx_split, m, m_seq, m_rewriter));
        m_tree.add_split_plugin(alloc(seq::mem_parikh_split, m, m_seq));
        m_tree.add_split_plugin(alloc(seq::power_num_cmp, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_split_elim, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_fine_wilf, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_var_peel, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::eq_split, m, m_seq));
        m_tree.add_split_plugin(alloc(seq::mem_monadic_split, m, m_seq, m_rewriter, m_tree.trail()));
        m_tree.add_split_plugin(alloc(seq::power_gpower_intro, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::word_eq_split, m, m_seq));
        m_tree.add_split_plugin(alloc(seq::power_split, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_var_decompose, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_var_peel_mem, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::deq_split, m, m_seq));

        m_tree.set_max_search_depth(30);
    }

    void theory_nseq::init() {
        m_arith_value.init(&get_context());
    }

    // -----------------------------------------------------------------------
    // Internalization
    // -----------------------------------------------------------------------

    bool theory_nseq::internalize_atom(app* atom, bool /*gate_ctx*/) {
        if (m_seq.str.is_in_re(atom)) {
            expr* str_arg = atom->get_arg(0);
            mk_var(ensure_enode(str_arg));
            if (!ctx.e_internalized(atom->get_arg(1)))
                ctx.internalize(atom->get_arg(1), false);
            if (!ctx.b_internalized(atom)) {
                bool_var bv = ctx.mk_bool_var(atom);
                ctx.set_var_theory(bv, get_id());
                ctx.mark_as_relevant(bv);
            }
            return true;
        }
        return internalize_term(atom);
    }

    theory_var theory_nseq::mk_var(enode* n) {
        expr* o = n->get_expr();
        if (!m_seq.is_seq(o) && !m_seq.is_re(o))
            return null_theory_var;
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        theory_var v = theory::mk_var(n);
        get_context().attach_th_var(n, this, v);
        get_context().mark_as_relevant(n);
        return v;
    }

    bool theory_nseq::internalize_term(app* term) {
        for (auto arg : *term)
            mk_var(ensure_enode(arg));

        if (ctx.e_internalized(term)) {
            mk_var(ctx.get_enode(term));
            return true;
        }

        if (m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.mark_as_relevant(bv);
        }

        enode* en = ctx.e_internalized(term) ? ctx.get_enode(term) : ctx.mk_enode(term, false, m.is_bool(term), true);
        mk_var(en);
        return true;
    }

    void theory_nseq::apply_sort_cnstr(enode* n, sort* /*s*/) {
        mk_var(n);
    }

    // -----------------------------------------------------------------------
    // Equality / disequality notifications
    // -----------------------------------------------------------------------

    void theory_nseq::new_eq_eh(theory_var v1, theory_var v2) {
        enode* n1 = get_enode(v1);
        enode* n2 = get_enode(v2);
        expr* e1 = n1->get_expr();
        expr* e2 = n2->get_expr();
        if (!m_seq.is_seq(e1))
            return;
        enqueue(eq_item{n1, n2});
    }

    void theory_nseq::new_diseq_eh(theory_var v1, theory_var v2) {
        enode* n1 = get_enode(v1);
        enode* n2 = get_enode(v2);
        expr* e1 = n1->get_expr();
        if (!m_seq.is_seq(e1))
            return;
        expr* e2 = n2->get_expr();
        literal lit = mk_eq(e1, e2, false);
        enqueue(deq_item{n1, n2, lit});
    }

    // -----------------------------------------------------------------------
    // Boolean assignment notification: str.in_re
    // -----------------------------------------------------------------------

    void theory_nseq::assign_eh(bool_var v, bool is_true) {
        expr* e = ctx.bool_var2expr(v);
        literal lit(v, !is_true);
        expr* s = nullptr, *re = nullptr;
        if (m_seq.str.is_in_re(e, s, re)) {
            enode* n1 = ensure_enode(s);
            enode* n2 = ensure_enode(re);
            enqueue(mem_item{n1, n2, lit, is_true});
        }
    }

    // -----------------------------------------------------------------------
    // Pending-assertion queue
    // -----------------------------------------------------------------------

    void theory_nseq::enqueue(prop_item const& item) {
        ctx.push_trail(restore_vector(m_prop_queue));
        m_prop_queue.push_back(item);
    }

    unsigned theory_nseq::mk_dep(assumption const& a) {
        unsigned idx = m_assumptions.size();
        m_assumptions.push_back(a);
        return idx;
    }

    void theory_nseq::populate_tree() {
        for (; m_prop_qhead < m_prop_queue.size(); ++m_prop_qhead) {
            prop_item const& item = m_prop_queue[m_prop_qhead];
            if (std::holds_alternative<eq_item>(item)) {
                auto const& eq = std::get<eq_item>(item);
                unsigned idx = mk_dep(assumption(eq.n1, eq.n2));
                seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
                expr_ref_vector lhs = m_ambient->purify(eq.n1->get_expr());
                expr_ref_vector rhs = m_ambient->purify(eq.n2->get_expr());
                m_root->facet_as<seq::eq_facet>(m_eq_id).add_equation(lhs, rhs, dep);
            }
            else if (std::holds_alternative<deq_item>(item)) {
                auto const& deq = std::get<deq_item>(item);
                unsigned idx = mk_dep(assumption(~deq.lit));
                seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
                expr_ref_vector lhs = m_ambient->purify(deq.n1->get_expr());
                expr_ref_vector rhs = m_ambient->purify(deq.n2->get_expr());
                m_root->facet_as<seq::deq_facet>(m_deq_id).add_disequation(lhs, rhs, dep);
            }
            else {
                auto const& mem = std::get<mem_item>(item);
                unsigned idx = mk_dep(assumption(mem.positive ? mem.lit : ~mem.lit));
                seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
                expr* re = mem.positive ? mem.re->get_expr() : m_seq.re.mk_complement(mem.re->get_expr());
                seq::view v = seq::view::membership(re);
                expr_ref_vector ts = m_ambient->purify(mem.s->get_expr());
                m_root->facet_as<seq::mem_facet>(m_mem_id).add(seq::str_mem(m, ts, v, dep));
            }
        }
    }

    void theory_nseq::report_conflict(seq::eq_tree::dep_tracker dep) {
        vector<unsigned, false> idxs;
        m_tree.dep_mgr().linearize(dep, idxs);
        enode_pair_vector eqs;
        literal_vector lits;
        for (unsigned idx : idxs) {
            assumption const& a = m_assumptions[idx];
            if (a.lit != null_literal)
                lits.push_back(a.lit);
            else
                eqs.push_back({a.n1, a.n2});
        }
        literal_vector clause;
        for (literal lit : lits)
            clause.push_back(~lit);
        for (auto const& p : eqs)
            clause.push_back(~mk_eq(p.first->get_expr(), p.second->get_expr(), false));
        for (literal lit : clause)
            ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), clause.size(), clause.data());
        ++m_num_conflicts;
    }

    final_check_status theory_nseq::final_check_eh(unsigned) {
        ++m_num_final_checks;
        populate_tree();
        stx::search_result res = m_tree.solve();
        switch (res) {
        case stx::search_result::sat:
            // Model construction is deferred: report done without a model.
            return FC_DONE;
        case stx::search_result::unsat: {
            seq::eq_tree::dep_tracker dep = m_root->conflict_dep();
            if (dep) {
                report_conflict(dep);
                return FC_CONTINUE;
            }
            // No precise dependency recorded: fall back to a giveup rather
            // than asserting an unjustified conflict.
            return FC_GIVEUP;
        }
        default:
            return FC_GIVEUP;
        }
    }

    void theory_nseq::push_scope_eh() {
        theory::push_scope_eh();
    }

    void theory_nseq::pop_scope_eh(unsigned num_scopes) {
        theory::pop_scope_eh(num_scopes);
    }

    theory* theory_nseq::mk_fresh(context* new_ctx) {
        return alloc(theory_nseq, *new_ctx);
    }

    void theory_nseq::display(std::ostream& out) const {
        out << "theory_nseq: " << m_num_final_checks << " final checks, " << m_num_conflicts << " conflicts\n";
        m_tree.display(out);
    }

    void theory_nseq::collect_statistics(::statistics& st) const {
        st.update("nseq final checks", m_num_final_checks);
        st.update("nseq conflicts", m_num_conflicts);
        m_tree.collect_statistics(st);
    }

    bool theory_nseq::get_num_value(expr* e, rational& val) const {
        return m_arith_value.get_value_equiv(e, val) && val.is_int();
    }

    bool theory_nseq::lower_bound(expr* e, rational& lo) const {
        if (!m_autil.is_int(e))
            return false;
        bool is_strict = true;
        return m_arith_value.get_lo(e, lo, is_strict) && !is_strict && lo.is_int();
    }

    bool theory_nseq::upper_bound(expr* e, rational& hi) const {
        if (!m_autil.is_int(e))
            return false;
        bool is_strict = true;
        return m_arith_value.get_up(e, hi, is_strict) && !is_strict && hi.is_int();
    }

}
