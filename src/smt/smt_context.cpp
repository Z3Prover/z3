/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_context.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

--*/
#include<math.h>
#include "smt/smt_context.h"
#include "util/luby.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "util/warning.h"
#include "smt/smt_quick_checker.h"
#include "ast/proofs/proof_checker.h"
#include "ast/ast_util.h"
#include "smt/uses_theory.h"
#include "model/model.h"
#include "smt/smt_for_each_relevant_expr.h"
#include "util/timeit.h"
#include "ast/well_sorted.h"
#include "util/union_find.h"
#include "smt/smt_model_generator.h"
#include "smt/smt_model_checker.h"
#include "smt/smt_model_finder.h"
#include "model/model_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_translation.h"

namespace smt {

    context::context(ast_manager & m, smt_params & p, params_ref const & _p):
        m_manager(m),
        m_fparams(p),
        m_params(_p),
        m_setup(*this, p),
        m_asserted_formulas(m, p, _p),
        m_qmanager(alloc(quantifier_manager, *this, p, _p)),
        m_model_generator(alloc(model_generator, m)),
        m_relevancy_propagator(mk_relevancy_propagator(*this)),
        m_random(p.m_random_seed),
        m_flushing(false),
        m_lemma_id(0),
        m_progress_callback(nullptr),
        m_next_progress_sample(0),
        m_fingerprints(m, m_region),
        m_b_internalized_stack(m),
        m_e_internalized_stack(m),
        m_final_check_idx(0),
        m_cg_table(m),
        m_dyn_ack_manager(*this, p),
        m_is_diseq_tmp(nullptr),
        m_units_to_reassert(m_manager),
        m_qhead(0),
        m_simp_qhead(0),
        m_simp_counter(0),
        m_bvar_inc(1.0),
        m_phase_cache_on(true),
        m_phase_counter(0),
        m_phase_default(false),
        m_conflict(null_b_justification),
        m_not_l(null_literal),
        m_conflict_resolution(mk_conflict_resolution(m, *this, m_dyn_ack_manager, p, m_assigned_literals, m_watches)),
        m_unsat_proof(m),
        m_unknown("unknown"),
        m_unsat_core(m),
#ifdef Z3DEBUG
        m_trail_enabled(true),
#endif
        m_scope_lvl(0),
        m_base_lvl(0),
        m_search_lvl(0),
        m_generation(0),
        m_last_search_result(l_undef),
        m_last_search_failure(UNKNOWN),
        m_searching(false) {

        SASSERT(m_scope_lvl == 0);
        SASSERT(m_base_lvl == 0);
        SASSERT(m_search_lvl == 0);

        m_case_split_queue = mk_case_split_queue(*this, p);

        init();

        if (!relevancy())
            m_fparams.m_relevancy_lemma = false;

        m_model_generator->set_context(this);
    }

    literal context::translate_literal(
        literal lit, context& src_ctx, context& dst_ctx,
        vector<bool_var> b2v, ast_translation& tr) {
        ast_manager& dst_m = dst_ctx.get_manager();
        ast_manager& src_m = src_ctx.get_manager();
        expr_ref dst_f(dst_m);

        SASSERT(lit != false_literal && lit != true_literal);
        bool_var v = b2v.get(lit.var(), null_bool_var);
        if (v == null_bool_var) {
            expr* e = src_ctx.m_bool_var2expr.get(lit.var(), 0);
            SASSERT(e);
            dst_f = tr(e);
            v = dst_ctx.get_bool_var_of_id_option(dst_f->get_id());
            if (v != null_bool_var) {
            }
            else if (src_m.is_not(e) || src_m.is_and(e) || src_m.is_or(e) ||
                     src_m.is_iff(e) || src_m.is_ite(e)) {
                v = dst_ctx.mk_bool_var(dst_f);
            }
            else {
                dst_ctx.internalize_formula(dst_f, false);
                v = dst_ctx.get_bool_var(dst_f);
            }
            b2v.setx(lit.var(), v, null_bool_var);
        }
        return literal(v, lit.sign());
    }

    bool context::get_cancel_flag() {
        return !m_manager.limit().inc();
    }

    void context::updt_params(params_ref const& p) {
        m_params.append(p);
        m_asserted_formulas.updt_params(p);
    }

    void context::copy(context& src_ctx, context& dst_ctx) {
        ast_manager& dst_m = dst_ctx.get_manager();
        ast_manager& src_m = src_ctx.get_manager();
        src_ctx.pop_to_base_lvl();

        if (src_ctx.m_base_lvl > 0) {
            throw default_exception("Cloning contexts within a user-scope is not allowed");
        }
        SASSERT(src_ctx.m_base_lvl == 0);

        ast_translation tr(src_m, dst_m, false);

        dst_ctx.set_logic(src_ctx.m_setup.get_logic());
        dst_ctx.copy_plugins(src_ctx, dst_ctx);

        asserted_formulas& src_af = src_ctx.m_asserted_formulas;
        asserted_formulas& dst_af = dst_ctx.m_asserted_formulas;

        // Copy asserted formulas.
        for (unsigned i = 0; i < src_af.get_num_formulas(); ++i) {
            expr_ref fml(dst_m);
            proof_ref pr(dst_m);
            proof* pr_src = src_af.get_formula_proof(i);
            fml = tr(src_af.get_formula(i));
            if (pr_src) {
                pr = tr(pr_src);
            }
            dst_af.assert_expr(fml, pr);
        }

        if (!src_ctx.m_setup.already_configured()) {
            return;
        }
        dst_ctx.setup_context(dst_ctx.m_fparams.m_auto_config);
        dst_ctx.internalize_assertions();

        vector<bool_var> b2v;

#define TRANSLATE(_lit) translate_literal(_lit, src_ctx, dst_ctx, b2v, tr)

        for (unsigned i = 0; i < src_ctx.m_assigned_literals.size(); ++i) {
            literal lit;
            lit = TRANSLATE(src_ctx.m_assigned_literals[i]);
            dst_ctx.mk_clause(1, &lit, nullptr, CLS_AUX, nullptr);
        }
#if 0
        literal_vector lits;
        expr_ref_vector cls(src_m);
        for (unsigned i = 0; i < src_ctx.m_lemmas.size(); ++i) {
            lits.reset();
            cls.reset();
            clause& src_cls = *src_ctx.m_lemmas[i];
            unsigned sz = src_cls.get_num_literals();
            for (unsigned j = 0; j < sz; ++j) {
                literal lit = TRANSLATE(src_cls.get_literal(j));
                lits.push_back(lit);
            }
            dst_ctx.mk_clause(lits.size(), lits.c_ptr(), 0, src_cls.get_kind(), 0);
        }
        vector<watch_list>::const_iterator it  = src_ctx.m_watches.begin();
        vector<watch_list>::const_iterator end = src_ctx.m_watches.end();
        literal ls[2];
        for (unsigned l_idx = 0; it != end; ++it, ++l_idx) {
            literal l1 = to_literal(l_idx);
            literal neg_l1 = ~l1;
            watch_list const & wl = *it;
            literal const * it2  = wl.begin();
            literal const * end2 = wl.end();
            for (; it2 != end2; ++it2) {
                literal l2 = *it2;
                if (l1.index() < l2.index()) {
                    ls[0] = TRANSLATE(neg_l1);
                    ls[1] = TRANSLATE(l2);
                    dst_ctx.mk_clause(2, ls, 0, CLS_AUX, 0);
                }
            }
        }
#endif

        TRACE("smt_context",
              src_ctx.display(tout);
              dst_ctx.display(tout););
    }


    context::~context() {
        flush();
    }

    void context::copy_plugins(context& src, context& dst) {
        // copy theory plugins
        for (theory* old_th : src.m_theory_set) {
            theory * new_th = old_th->mk_fresh(&dst);
            dst.register_plugin(new_th);
        }
    }

    context * context::mk_fresh(symbol const * l, smt_params * p, params_ref const& pa) {
        context * new_ctx = alloc(context, m_manager, p ? *p : m_fparams, pa);
        new_ctx->set_logic(l == nullptr ? m_setup.get_logic() : *l);
        copy_plugins(*this, *new_ctx);
        return new_ctx;
    }

    void context::init() {
        app * t       = m_manager.mk_true();
        mk_bool_var(t);
        SASSERT(get_bool_var(t) == true_bool_var);
        SASSERT(true_literal.var() == true_bool_var);
        m_assignment[true_literal.index()]     = l_true;
        m_assignment[false_literal.index()]    = l_false;
        if (m_manager.proofs_enabled()) {
            proof * pr = m_manager.mk_true_proof();

            set_justification(true_bool_var, m_bdata[true_bool_var], b_justification(mk_justification(justification_proof_wrapper(*this, pr))));
        }
        else {
            m_bdata[true_bool_var].set_axiom();
        }
        m_true_enode  = mk_enode(t, true, true, false);
        // internalizer is marking enodes as interpreted whenever the associated ast is a value and a constant.
        // m_true_enode->mark_as_interpreted();
        app * f       = m_manager.mk_false();
        m_false_enode = mk_enode(f, true, true, false);
        // m_false_enode->mark_as_interpreted();
    }

    void context::set_progress_callback(progress_callback *cb)
    {
        m_progress_callback = cb;
    }

    /**
       \brief This method should be used to create equality atoms during the search.
       See comments in theory::mk_eq_atom
    */
    app * context::mk_eq_atom(expr * lhs, expr * rhs) {
        family_id fid = m_manager.get_sort(lhs)->get_family_id();
        theory * th   = get_theory(fid);
        if (th)
            return th->mk_eq_atom(lhs, rhs);
        if (lhs->get_id() > rhs->get_id())
            std::swap(lhs, rhs);
        return m_manager.mk_eq(lhs, rhs);
    }

    void context::set_justification(bool_var v, bool_var_data& d, b_justification const& j) {
        SASSERT(validate_justification(v, d, j));
        d.set_justification(j);
    }

    void context::assign_core(literal l, b_justification j, bool decision) {
        TRACE("assign_core", tout << (decision?"decision: ":"propagating: ") << l << " ";
              display_literal_verbose(tout, l); tout << " level: " << m_scope_lvl << "\n";
              display(tout, j););
        m_assigned_literals.push_back(l);
        m_assignment[l.index()]    = l_true;
        m_assignment[(~l).index()] = l_false;
        bool_var_data & d          = get_bdata(l.var());
        set_justification(l.var(), d, j);
        d.m_scope_lvl              = m_scope_lvl;
        if (m_fparams.m_restart_adaptive && d.m_phase_available) {
            m_agility             *= m_fparams.m_agility_factor;
            if (!decision && d.m_phase == l.sign())
                m_agility         += (1.0 - m_fparams.m_agility_factor);
        }
        d.m_phase_available        = true;
        d.m_phase                  = !l.sign();
        TRACE("phase_selection", tout << "saving phase, is_pos: " << d.m_phase << " l: " << l << "\n";);

        TRACE("relevancy",
              tout << "is_atom: " << d.is_atom() << " is relevant: " << is_relevant_core(l) << "\n";);
        if (d.is_atom() && (m_fparams.m_relevancy_lvl == 0 || (m_fparams.m_relevancy_lvl == 1 && !d.is_quantifier()) || is_relevant_core(l)))
            m_atom_propagation_queue.push_back(l);

        if (m_manager.has_trace_stream())
            trace_assign(l, j, decision);
        m_case_split_queue->assign_lit_eh(l);

        // a unit is asserted at search level. Mark it as relevant.
        // this addresses bug... where a literal becomes fixed to true (false)
        // as a conflict gets assigned misses relevancy (and quantifier instantiation).
        //
        if (false && !decision && relevancy() && at_search_level() && !is_relevant_core(l)) {
            mark_as_relevant(l);
        }
    }

    bool context::bcp() {
        SASSERT(!inconsistent());
        while (m_qhead < m_assigned_literals.size()) {
            if (get_cancel_flag()) {
                return true;
            }
            literal l      = m_assigned_literals[m_qhead];
            SASSERT(get_assignment(l) == l_true);
            m_qhead++;
            m_simp_counter--;
            literal not_l  = ~l;
            SASSERT(get_assignment(not_l) == l_false);
            watch_list & w = m_watches[l.index()];
            if (binary_clause_opt_enabled()) {
                // binary clause propagation
                b_justification js(l);
                literal * it  = w.begin_literals();
                literal * end = w.end_literals();
                for(; it != end; ++it) {
                    literal l = *it;
                    switch (get_assignment(l)) {
                    case l_false:
                        m_stats.m_num_bin_propagations++;
                        set_conflict(js, ~l);
                        return false;
                    case l_undef:
                        m_stats.m_num_bin_propagations++;
                        assign_core(l, js);
                        break;
                    case l_true:
                        break;
                    }
                }
            }

            // non-binary clause propagation
            watch_list::clause_iterator it  = w.begin_clause();
            watch_list::clause_iterator it2 = it;
            watch_list::clause_iterator end = w.end_clause();
            for(; it != end; ++it) {
                clause * cls = *it;
                CTRACE("bcp_bug", cls->get_literal(0) != not_l && cls->get_literal(1) != not_l, display_clause_detail(tout, cls);
                       tout << "not_l: "; display_literal(tout, not_l); tout << " " << not_l << "\n";);
                SASSERT(cls->get_literal(0) == not_l || cls->get_literal(1) == not_l);
                if (cls->get_literal(0) == not_l) {
                    cls->set_literal(0, cls->get_literal(1));
                    cls->set_literal(1, not_l);
                }

                SASSERT(cls->get_literal(1) == not_l);

                literal first_lit     = cls->get_literal(0);
                lbool   first_lit_val = get_assignment(first_lit);

                if (first_lit_val == l_true) {
                    *it2 = *it; // clause is already satisfied, keep it
                    it2++;
                }
                else {
                    literal * it3  = cls->begin() + 2;
                    literal * end3 = cls->end();
                    for(; it3 != end3; ++it3) {
                        if (get_assignment(*it3) != l_false) {
                            // swap literal *it3 with literal at position 0
                            // the negation of literal *it3 will watch clause cls.
                            m_watches[(~(*it3)).index()].insert_clause(cls);
                            cls->set_literal(1, *it3);
                            *it3   = not_l;
                            goto found_watch;
                        }
                    }
                    // did not find watch...
                    if (first_lit_val == l_false) {
                        // CONFLICT
                        // copy remaining watches
                        while (it < end) {
                            *it2 = *it;
                            it2++;
                            it++;
                        }
                        SASSERT(it2 <= end);
                        w.set_end_clause(it2);
                        SASSERT(is_empty_clause(cls));
                        set_conflict(b_justification(cls));
                        return false;
                    }
                    else {
                        // PROPAGATION
                        SASSERT(first_lit_val == l_undef);
                        SASSERT(get_assignment(first_lit) == l_undef);
                        SASSERT(is_unit_clause(cls));
                        *it2 = *it;
                        it2++; // keep clause
                        m_stats.m_num_propagations++;
                        // It is safe to call assign_core instead of assign because first_lit is unassigned
                        assign_core(first_lit, b_justification(cls));
                        if (m_fparams.m_relevancy_lemma && cls->is_lemma()) {
                            expr * e = bool_var2expr(first_lit.var());
                            // IMPORTANT: this kind of propagation asserts negative literals of the form (= A1 A2) where
                            // A1 and A2 are array terms. So, it may be interesting to disable it for array eqs.
                            //if (!(m_manager.is_eq(e) && m_manager.get_sort(to_app(e)->get_arg(0))->get_family_id() == m_manager.get_family_id("array")))
                            mark_as_relevant(e);
                        }
                    }
                found_watch:;
                }
            }
            SASSERT(it2 <= end);
            w.set_end_clause(it2);
        }
        return true;
    }

    /**
       \brief Push a new equality for theory th, into the theory equality propagation queue.
    */
    void context::push_new_th_eq(theory_id th, theory_var lhs, theory_var rhs) {
        SASSERT(lhs != rhs);
        SASSERT(lhs != null_theory_var);
        SASSERT(rhs != null_theory_var);
        SASSERT(th != null_theory_id);
        SASSERT(get_theory(th)->get_enode(lhs) != get_theory(th)->get_enode(rhs));
        m_th_eq_propagation_queue.push_back(new_th_eq(th, lhs, rhs));
    }

    /**
       \brief Push a new disequality for theory th, into the theory disequality propagation queue.
    */
    void context::push_new_th_diseq(theory_id th, theory_var lhs, theory_var rhs) {
        SASSERT(lhs != rhs);
        SASSERT(lhs != null_theory_var);
        SASSERT(rhs != null_theory_var);
        SASSERT(th != null_theory_id);
        theory * t = get_theory(th);
        if (t->get_enode(lhs)->is_interpreted() && t->get_enode(rhs)->is_interpreted())
            return;
        TRACE("add_diseq",
              tout << "#" << t->get_enode(lhs)->get_owner_id() << " != "
              << "#" << t->get_enode(rhs)->get_owner_id() << "\n";);

        m_th_diseq_propagation_queue.push_back(new_th_eq(th, lhs, rhs));
    }

    class add_eq_trail : public trail<context> {
        enode * m_r1;
        enode * m_n1;
        unsigned m_r2_num_parents;
    public:
        add_eq_trail(enode * r1, enode * n1, unsigned r2_num_parents):
            m_r1(r1),
            m_n1(n1),
            m_r2_num_parents(r2_num_parents) {
        }

        void undo(context & ctx) override {
            ctx.undo_add_eq(m_r1, m_n1, m_r2_num_parents);
        }
    };

    /**
       \brief Add the equality n1 = n2 with justification js into the logical context.
    */
    void context::add_eq(enode * n1, enode * n2, eq_justification js) {
        unsigned old_trail_size = m_trail_stack.size();
        scoped_suspend_rlimit _suspend_cancel(m_manager.limit());

        try {
            TRACE("add_eq", tout << "assigning: #" << n1->get_owner_id() << " = #" << n2->get_owner_id() << "\n";);
            TRACE("add_eq_detail", tout << "assigning\n" << mk_pp(n1->get_owner(), m_manager) << "\n" << mk_pp(n2->get_owner(), m_manager) << "\n";
                  tout << "kind: " << js.get_kind() << "\n";);

            m_stats.m_num_add_eq++;
            enode * r1 = n1->get_root();
            enode * r2 = n2->get_root();

            if (r1 == r2) {
                TRACE("add_eq", tout << "redundant constraint.\n";);
                return;
            }

            if (r1->is_interpreted() && r2->is_interpreted()) {
                TRACE("add_eq", tout << "interpreted roots conflict.\n";);
                set_conflict(mk_justification(eq_conflict_justification(n1, n2, js)));
                return;
            }

            // Swap r1 and r2:
            //  1. if the "equivalence" class of r1 is bigger than the equivalence class of r2
            //  OR
            //  2. r1 is interpreted but r2 is not.
            //
            // The second condition is used to enforce the invariant that if a class contain
            // an interepreted enode then the root is also interpreted.
            if ((r1->get_class_size() > r2->get_class_size() && !r2->is_interpreted()) || r1->is_interpreted()) {
                SASSERT(!r2->is_interpreted());
                std::swap(n1, n2);
                std::swap(r1, r2);
            }

            TRACE("add_eq", tout << "merging: #" << r1->get_owner_id() << " #" << r2->get_owner_id() <<
                  " n1: #" << n1->get_owner_id() << "\n";);

            // It is necessary to propagate relevancy to other elements of
            // the equivalence class. This is nessary to enforce the invariant
            // in the field m_parent of the enode class.
            if (is_relevant(r1)) { // && !m_manager.is_eq(r1->get_owner())) !is_eq HACK
                // NOTE for !is_eq HACK... the !is_eq HACK does not propagate relevancy when two
                // equality enodes are congruent. I tested this optimization because in V1
                // relevancy is not propagated for congruent equalities.
                // This occurs in V2, because we use the congruence table to propagate disequalities
                // efficiently.
                // I disabled this optimization HACK because it breaks invariants in the rest of the code.
                // To use it, I need to go over the code and analyze all affected places.
                mark_as_relevant(r2);
            }
            else if (is_relevant(r2)) { // && !m_manager.is_eq(r2->get_owner())) { // !is_eq HACK
                mark_as_relevant(r1);
            }

            TRACE("add_eq", tout << "to trail\n";);

            push_trail(add_eq_trail(r1, n1, r2->get_num_parents()));

            TRACE("add_eq", tout << "qmanager add_eq\n";);
            m_qmanager->add_eq_eh(r1, r2);

            TRACE("add_eq", tout << "merge theory_vars\n";);
            merge_theory_vars(n2, n1, js);

            // 'Proof' tree
            // n1 -> ... -> r1
            // n2 -> ... -> r2
            SASSERT(n1->trans_reaches(r1));
            invert_trans(n1);
            n1->m_trans.m_target        = n2;
            n1->m_trans.m_justification = js;
            n1->m_proof_logged_status   = smt::logged_status::NOT_LOGGED;
            SASSERT(r1->trans_reaches(n1));
            // ---------------
            // r1 -> ..  -> n1 -> n2 -> ... -> r2


#if 0
            {
                static unsigned counter      = 0;
                static unsigned num_adds     = 0;
                static unsigned num_bad_adds = 0;
                num_adds++;
                if (r1->get_class_size() <= r2->get_class_size() &&
                    r1->m_parents.size() > r2->m_parents.size()) {
                    num_bad_adds++;
                }
                if (num_adds % 100000 == 0) {
                    verbose_stream() << "[add-eq]: " << num_bad_adds << " " << num_adds << " "
                                     << static_cast<double>(num_bad_adds)/static_cast<double>(num_adds) << "\n";
                }
            }
#endif


            TRACE("add_eq", tout << "remove_parents_from_cg_table\n";);
            remove_parents_from_cg_table(r1);

            enode * curr = r1;
            do {
                curr->m_root = r2;
                curr = curr->m_next;
            }
            while(curr != r1);

            SASSERT(r1->get_root() == r2);

            TRACE("add_eq", tout << "reinsert_parents_into_cg_table\n";);
            reinsert_parents_into_cg_table(r1, r2, n1, n2, js);

            TRACE("add_eq", tout << "propagate_bool_enode_assignment\n";);
            if (n2->is_bool())
                propagate_bool_enode_assignment(r1, r2, n1, n2);

            // Merge "equivalence" classes
            std::swap(r1->m_next, r2->m_next);

            // Update "equivalence" class size
            r2->m_class_size += r1->m_class_size;

            CASSERT("add_eq", check_invariant());
        }
        catch (...) {
            // Restore trail size since procedure was interrupted in the middle.
            // If the add_eq_trail remains on the trail stack, then Z3 may crash when the destructor is invoked.
            TRACE("add_eq", tout << "add_eq interrupted. This is unsafe " << m_manager.limit().get_cancel_flag() << "\n";);
            m_trail_stack.shrink(old_trail_size);
            throw;
        }
    }

    /**
       \brief When merging to equivalence classes, the parents of the smallest one (that are congruence roots),
       must be removed from the congruence table since their hash code will change.
    */
    void context::remove_parents_from_cg_table(enode * r1) {
        // Remove parents from the congruence table
        for (enode * parent : enode::parents(r1)) {
#if 0
            {
                static unsigned num_eqs = 0;
                static unsigned num_parents = 0;
                static unsigned counter = 0;
                if (parent->is_eq())
                    num_eqs++;
                num_parents++;
                if (num_parents % 100000 == 0) {
                    verbose_stream() << "[remove-cg] " << num_eqs << " " << num_parents << " "
                              << static_cast<double>(num_eqs)/static_cast<double>(num_parents) << "\n";
                }
            }
#endif
            SASSERT(parent->is_marked() || !parent->is_cgc_enabled() ||
                    (!parent->is_true_eq() && parent->is_cgr() == m_cg_table.contains_ptr(parent)) ||
                    (parent->is_true_eq() && !m_cg_table.contains_ptr(parent)));
            if (!parent->is_marked() && parent->is_cgr() && !parent->is_true_eq()) {
                TRACE("add_eq_parents", tout << "add_eq removing: #" << parent->get_owner_id() << "\n";);
                SASSERT(!parent->is_cgc_enabled() || m_cg_table.contains_ptr(parent));
                parent->set_mark();
                if (parent->is_cgc_enabled()) {
                    m_cg_table.erase(parent);
                    SASSERT(!m_cg_table.contains_ptr(parent));
                }
            }
        }
    }

    /**
       \brief Reinsert the parents of r1 that were removed from the
       cg_table at remove_parents_from_cg_table. Some of these parents will
       become congruent to other enodes, and a new equality will be propagated.
       Moreover, this method is also used for doing equality propagation.

       The parents of r1 that remain as congruence roots are copied to the
       r2->m_parents.

       The n1, n2, js arguments are used to implement dynamic ackermanization.
       js is a justification for n1 and n2 being equal, and the equality n1 = n2 is
       the one that implied r1 = r2.
    */
    void context::reinsert_parents_into_cg_table(enode * r1, enode * r2, enode * n1, enode * n2, eq_justification js) {
        enode_vector & r2_parents  = r2->m_parents;
        for (enode * parent : enode::parents(r1)) {
            if (!parent->is_marked())
                continue;
            parent->unset_mark();
            if (parent->is_eq()) {
                SASSERT(parent->get_num_args() == 2);
                TRACE("add_eq_bug", tout << "visiting: #" << parent->get_owner_id() << "\n";);
                enode * lhs = parent->get_arg(0);
                enode * rhs = parent->get_arg(1);
                if (lhs->get_root() == rhs->get_root()) {
                    SASSERT(parent->is_true_eq());
                    unsigned expr_id = parent->get_owner_id();
                    bool_var v = get_bool_var_of_id(expr_id);
                    lbool val  = get_assignment(v);
                    if (val != l_true) {
                        if (val == l_false && js.get_kind() == eq_justification::CONGRUENCE)
                            m_dyn_ack_manager.cg_conflict_eh(n1->get_owner(), n2->get_owner());

                        assign(literal(v), mk_justification(eq_propagation_justification(lhs, rhs)));
                    }
                    // It is not necessary to reinsert the equality to the congruence table
                    continue;
                }
            }
            if (parent->is_cgc_enabled()) {
                enode_bool_pair pair = m_cg_table.insert(parent);
                enode * parent_prime = pair.first;
                if (parent_prime == parent) {
                    TRACE("add_eq_parents", tout << "add_eq reinserting: #" << parent->get_owner_id() << "\n";);
                    SASSERT(parent);
                    SASSERT(parent->is_cgr());
                    SASSERT(m_cg_table.contains_ptr(parent));
                    r2_parents.push_back(parent);
                    continue;
                }
                parent->m_cg = parent_prime;
                SASSERT(!m_cg_table.contains_ptr(parent));
                if (parent_prime->m_root != parent->m_root) {
                    bool used_commutativity = pair.second;
                    TRACE("cg", tout << "found new congruence: #" << parent->get_owner_id() << " = #" << parent_prime->get_owner_id()
                          << " used_commutativity: " << used_commutativity << "\n";);
                    push_new_congruence(parent, parent_prime, used_commutativity);
                }
            }
            else {
                // If congruence closure is not enabled for parent, then I just copy it
                // to r2_parents
                r2_parents.push_back(parent);
            }
        }
    }

    /**
       \brief A transitivity 'proof' branch is represented by
       the following sequence starting at n and ending
       at n->get_root.

       N1      = n
       N_{i+1} = N_i->m_trans.m_target
       and, there is an k such that N_k = n->get_root()

       This method will invert this branch.
    */
    void context::invert_trans(enode * n) {
        enode * curr                      = n->m_trans.m_target;
        enode * prev                      = n;
        eq_justification js               = n->m_trans.m_justification;
        prev->m_trans.m_target            = nullptr;
        prev->m_trans.m_justification     = null_eq_justification;
        prev->m_proof_logged_status       = smt::logged_status::NOT_LOGGED;
        while (curr != nullptr) {
            SASSERT(prev->trans_reaches(n));
            enode * new_curr              = curr->m_trans.m_target;
            eq_justification new_js       = curr->m_trans.m_justification;
            curr->m_trans.m_target        = prev;
            curr->m_trans.m_justification = js;
            curr->m_proof_logged_status   = smt::logged_status::NOT_LOGGED;
            prev                          = curr;
            js                            = new_js;
            curr                          = new_curr;
        }
    }

    /**
       \brief Given that r is the root of n, and r contains a theory variable
       for theory th_id, this method returns a theory variable that is 'closer'
       to n in the 'proof branch' n -> ... -> r.

       This method is used to improve the quality of the conflict clauses produced
       by the logical context.

       Consider the following example:

       - Consider the following sequence of equalities:
       n1 = n2 = n3 = n4 = n5 = n6

       - Now, assume that n1 is the root of the equivalence class
       after each merge. So, the 'proof' branch will have the following
       shape:

       n1 <- n2 <- n3 <- n4 <- n5 <- n6

       - Assuming that all nodes are attached to theory variable, then the following
       sequence of equalities is sent to the theory if the method get_closest_var is not used:

       n1 = n2, n1 = n3, n1 = n4, n1 = n5, n1 = n6

       - This sequence is bad, and bad justifications may be produced by theory.
       For example, assume the following arithmetic constraint

       n5 < n6

       For the arithmetic module, the best justification will be:
       n1 = n5, n1 = n6 and n5 < n6

       This justification contains unnecessary 'junk' to justify that n5 = n6.
       That is, it proves n5 = n6 using the proofs for n1 = n5 and n1 = n6.

       When the method get_closest_var is used in the communication with theories,
       the logical context will send the natural sequence of equalities to the theories:

       n1 = n2 = n3 = n4 = n5 = n6
    */
    theory_var context::get_closest_var(enode * n, theory_id th_id) {
        if (th_id == null_theory_id)
            return null_theory_var;
        while (n != nullptr) {
            theory_var v = n->get_th_var(th_id);
            if (v != null_theory_var)
                return v;
            n = n->m_trans.m_target;
        }
        return null_theory_var;
    }

    /**
       \brief Merge the theory variables of n2->get_root() and n1->get_root(), the result is stored in n2->get_root().
       New th_var equalities are propagated to the theories.

       \remark In most cases, an enode is attached to at most one theory var.
    */
    void context::merge_theory_vars(enode * n2, enode * n1, eq_justification js) {
        enode * r2 = n2->get_root();
        enode * r1 = n1->get_root();
        if (!r1->has_th_vars() && !r2->has_th_vars()) {
            TRACE("merge_theory_vars", tout << "Neither have theory vars #" << n1->get_owner()->get_id() << " #" << n2->get_owner()->get_id() << "\n";);
            return;
        }

        theory_id from_th = null_theory_id;

        if (js.get_kind() == eq_justification::JUSTIFICATION)
            from_th = js.get_justification()->get_from_theory();

        if (r2->m_th_var_list.get_next() == nullptr && r1->m_th_var_list.get_next() == nullptr) {
            // Common case: r2 and r1 have at most one theory var.
            theory_id  t2 = r2->m_th_var_list.get_th_id();
            theory_id  t1 = r1->m_th_var_list.get_th_id();
            // verbose_stream() << "[merge_theory_vars] t2: " << t2 << ", t1: " << t1 << "\n";
            theory_var v2 = m_fparams.m_new_core2th_eq ? get_closest_var(n2, t2) : r2->m_th_var_list.get_th_var();
            theory_var v1 = m_fparams.m_new_core2th_eq ? get_closest_var(n1, t1) : r1->m_th_var_list.get_th_var();
            TRACE("merge_theory_vars",
                  tout << "v2: " << v2 << " #" << r2->get_owner_id() << ", v1: " << v1 << " #" << r1->get_owner_id()
                  << ", t2: " << t2 << ", t1: " << t1 << "\n";);
            if (v2 != null_theory_var && v1 != null_theory_var) {
                if (t1 == t2) {
                    // only send the equality to the theory, if the equality was not propagated by it.
                    if (t1 != from_th)
                        push_new_th_eq(t1, v2, v1);
                }
                else {
                    // uncommon case: r2 will have two theory_vars attached to it.
                    r2->add_th_var(v1, t1, m_region);
                    push_new_th_diseqs(r2, v1, get_theory(t1));
                    push_new_th_diseqs(r1, v2, get_theory(t2));
                }
            }
            else if (v1 == null_theory_var && v2 != null_theory_var) {
                push_new_th_diseqs(r1, v2, get_theory(t2));
            }
            else if (v1 != null_theory_var && v2 == null_theory_var) {
                r2->m_th_var_list.set_th_var(v1);
                r2->m_th_var_list.set_th_id(t1);
                TRACE("merge_theory_vars", tout << "push_new_th_diseqs v1: " << v1 << ", t1: " << t1 << "\n";);
                push_new_th_diseqs(r2, v1, get_theory(t1));
            }
        }
        else {
            // r1 and/or r2 have more than one theory variable.
            TRACE("merge_theory_vars",
                  tout << "#" << r1->get_owner_id() << " == #" << r2->get_owner_id() << "\n";);


            theory_var_list * l2 = r2->get_th_var_list();
            while (l2) {
                theory_id  t2 = l2->get_th_id();
                theory_var v2 = m_fparams.m_new_core2th_eq ? get_closest_var(n2, t2) : l2->get_th_var();
                SASSERT(v2 != null_theory_var);
                SASSERT(t2 != null_theory_id);
                theory_var v1 = m_fparams.m_new_core2th_eq ? get_closest_var(n1, t2) : r1->get_th_var(t2);

                if (v1 != null_theory_var) {
                    // only send the equality to the theory, if the equality was not propagated by it.
                    if (t2 != from_th)
                        push_new_th_eq(t2, v2, v1);
                }
                else {
                    push_new_th_diseqs(r1, v2, get_theory(t2));
                }
                l2 = l2->get_next();
            }

            theory_var_list * l1 = r1->get_th_var_list();
            while (l1) {
                theory_id  t1 = l1->get_th_id();
                theory_var v1 = m_fparams.m_new_core2th_eq ? get_closest_var(n1, t1) : l1->get_th_var();
                SASSERT(v1 != null_theory_var);
                SASSERT(t1 != null_theory_id);
                theory_var v2 = r2->get_th_var(t1);
                if (v2 == null_theory_var) {
                    r2->add_th_var(v1, t1, m_region);
                    push_new_th_diseqs(r2, v1, get_theory(t1));
                }
                l1 = l1->get_next();
            }
        }
    }

    /**
       \brief Propagate the boolean assignment when two equivalence classes are merged.
    */
    void context::propagate_bool_enode_assignment(enode * r1, enode * r2, enode * n1, enode * n2) {
        SASSERT(n1->is_bool());
        SASSERT(n2->is_bool());
        SASSERT(r1->is_bool());
        SASSERT(r2->is_bool());
        if (r2 == m_false_enode || r2 == m_true_enode) {
            bool sign = r2 == m_false_enode;
            enode * curr = r1;
            do {
                SASSERT(curr != m_false_enode);
                bool_var v = enode2bool_var(curr);
                literal l(v, sign);
                if (get_assignment(l) != l_true)
                    assign(l, mk_justification(eq_root_propagation_justification(curr)));
                curr = curr->m_next;
            }
            while(curr != r1);
        }
        else {
            bool_var v1 = enode2bool_var(n1);
            bool_var v2 = enode2bool_var(n2);
            lbool val1  = get_assignment(v1);
            lbool val2  = get_assignment(v2);
            if (val1 != val2) {
                if (val2 == l_undef)
                    propagate_bool_enode_assignment_core(n1, n2);
                else
                    propagate_bool_enode_assignment_core(n2, n1);
            }
        }
    }

    /**
       \brief source and target are boolean enodes, they were proved to be equal,
       and the boolean variable associated with source is assigned. Then,
       copy the assignment to the boolean variables associated with target.
    */
    void context::propagate_bool_enode_assignment_core(enode * source, enode * target) {
        SASSERT(source->is_bool());
        SASSERT(target->is_bool());
        SASSERT(source->get_root() == target->get_root());
        bool_var v_source = enode2bool_var(source);
        lbool    val      = get_assignment(v_source);
        SASSERT(val != l_undef);
        bool     sign     = val == l_false;
        enode * first = target;
        do {
            bool_var v2 = enode2bool_var(target);
            lbool val2  = get_assignment(v2);
            if (val2 != val) {
                if (val2 != l_undef && congruent(source, target) && source->get_num_args() > 0)
                    m_dyn_ack_manager.cg_conflict_eh(source->get_owner(), target->get_owner());
                assign(literal(v2, sign), mk_justification(mp_iff_justification(source, target)));
            }
            target = target->get_next();
        }
        while (first != target);
    }

    void context::undo_add_eq(enode * r1, enode * n1, unsigned r2_num_parents) {
        enode * r2 = r1->get_root();
        TRACE("add_eq", tout << "undo_add_eq #" << r1->get_owner_id() << " #" << r2->get_owner_id() << "\n";);

        // restore r2 class size
        r2->m_class_size -= r1->m_class_size;

        // unmerge "equivalence" classes
        std::swap(r1->m_next, r2->m_next);

        // remove the parents of r1 that remained as congruence roots
        enode_vector::iterator it  = r2->begin_parents();
        enode_vector::iterator end = r2->end_parents();
        it += r2_num_parents;
        for (; it != end; ++it) {
            enode * parent = *it;
            if (parent->is_cgc_enabled()) {
                TRACE("add_eq_parents", tout << "removing: #" << parent->get_owner_id() << "\n";);
                CTRACE("add_eq", !parent->is_cgr() || !m_cg_table.contains_ptr(parent),
                       tout << "old num_parents: " << r2_num_parents << ", num_parents: " << r2->m_parents.size() << ", parent: #" <<
                       parent->get_owner_id() << ", parents: \n";
                       for (unsigned i = 0; i < r2->m_parents.size(); i++) {
                           tout << "#" << r2->m_parents[i]->get_owner_id() << " ";
                       }
                       display(tout););
                SASSERT(parent->is_cgr());
                SASSERT(m_cg_table.contains_ptr(parent));
                m_cg_table.erase(parent);
            }
        }

        enode * curr = r1;
        do {
            curr->m_root = r1;
            curr = curr->m_next;
        }
        while(curr != r1);

        // restore parents of r2
        r2->m_parents.shrink(r2_num_parents);

        // try to reinsert parents of r1 that are not cgr
        for (enode * parent : enode::parents(r1)) {
            TRACE("add_eq_parents", tout << "visiting: #" << parent->get_owner_id() << "\n";);
            if (parent->is_cgc_enabled()) {
                enode * cg     = parent->m_cg;
                if (!parent->is_true_eq() &&
                    (parent == cg || // parent was root of the congruence class before and after the merge
                     !congruent(parent, cg) // parent was root of the congruence class before but not after the merge
                     )) {
                    TRACE("add_eq_parents", tout << "trying to reinsert\n";);
                    m_cg_table.insert(parent);
                    parent->m_cg         = parent;
                }
            }
        }

        // restore theory vars
        if (r2->m_th_var_list.get_next() == nullptr) {
            // common case: r2 has at most one variable
            theory_var v2 = r2->m_th_var_list.get_th_var();
            if (v2 != null_theory_var) {
                theory_id  t2 = r2->m_th_var_list.get_th_id();
                if (get_theory(t2)->get_enode(v2)->get_root() != r2) {
                    SASSERT(get_theory(t2)->get_enode(v2)->get_root() == r1);
                    r2->m_th_var_list.set_th_var(null_theory_var); //remove variable from r2
                    r2->m_th_var_list.set_th_id(null_theory_id);
                }
            }
        }
        else {
            restore_theory_vars(r2, r1);
        }

        // 'Proof' tree
        // r1 -> ..  -> n1 -> n2 -> ... -> r2
        SASSERT(r1->trans_reaches(r2));
        SASSERT(r1->trans_reaches(n1));
        n1->m_trans.m_target        = nullptr;
        n1->m_trans.m_justification = null_eq_justification;
        n1->m_proof_logged_status   = smt::logged_status::NOT_LOGGED;
        invert_trans(r1);
        // ---------------
        // n1 -> ... -> r1
        // n2 -> ... -> r2
        SASSERT(n1->trans_reaches(r1));
        SASSERT(r1->m_trans.m_target == 0);

        CASSERT("add_eq", check_invariant());
    }

    /**
       \brief Auxiliary method for undo_add_eq.
       It restores the theory variables of a given root enode.
       This method deletes any theory variable v2 of r2 (for a theory t2)
       whenever:

       get_theory(t2)->get_enode(v2)->get_root() != r2

       That is, v2 is not equivalent to r2 anymore.
    */
    void context::restore_theory_vars(enode * r2, enode * r1) {
        SASSERT(r2->get_root() == r2);
        theory_var_list * new_l2  = nullptr;
        theory_var_list * l2      = r2->get_th_var_list();
        while (l2) {
            theory_var v2 = l2->get_th_var();
            theory_id t2  = l2->get_th_id();

            if (get_theory(t2)->get_enode(v2)->get_root() != r2) {
                SASSERT(get_theory(t2)->get_enode(v2)->get_root() == r1);
                l2 = l2->get_next();
            }
            else {
                if (new_l2) {
                    new_l2->set_next(l2);
                    new_l2 = l2;
                }
                else {
                    r2->m_th_var_list = *l2;
                    new_l2 = &(r2->m_th_var_list);
                }
                l2 = l2->get_next();
            }
        }

        if (new_l2) {
            new_l2->set_next(nullptr);
        }
        else {
            r2->m_th_var_list.set_th_var(null_theory_var);
            r2->m_th_var_list.set_next(nullptr);
        }
    }

    /**
       \brief This method is invoked when a new disequality is asserted.
       The disequality is propagated to the theories.
    */
    bool context::add_diseq(enode * n1, enode * n2) {
        enode * r1 = n1->get_root();
        enode * r2 = n2->get_root();
        TRACE("add_diseq", tout << "assigning: #" << n1->get_owner_id() << " != #" << n2->get_owner_id() << "\n";
              tout << mk_ll_pp(n1->get_owner(), m_manager) << " != ";
              tout << mk_ll_pp(n2->get_owner(), m_manager) << "\n";
              tout << mk_ll_pp(r1->get_owner(), m_manager) << " != ";
              tout << mk_ll_pp(r2->get_owner(), m_manager) << "\n";
              );

#ifdef Z3DEBUG
        push_trail(push_back_trail<context, enode_pair, false>(m_diseq_vector));
        m_diseq_vector.push_back(enode_pair(n1, n2));
#endif

        if (r1 == r2) {
            TRACE("add_diseq_inconsistent", tout << "add_diseq #" << n1->get_owner_id() << " #" << n2->get_owner_id() << " inconsistency, scope_lvl: " << m_scope_lvl << "\n";);
            //return false;

            theory_id  t1 = r1->m_th_var_list.get_th_id();
            if (t1 == null_theory_id) return false;
            return get_theory(t1)->use_diseqs();
        }

        // Propagate disequalities to theories
        if (r1->m_th_var_list.get_next() == nullptr && r2->m_th_var_list.get_next() == nullptr) {
            // common case: r2 and r1 have at most one theory var.
            theory_id  t1 = r1->m_th_var_list.get_th_id();
            theory_var v1 = m_fparams.m_new_core2th_eq ? get_closest_var(n1, t1) : r1->m_th_var_list.get_th_var();
            theory_var v2 = m_fparams.m_new_core2th_eq ? get_closest_var(n2, t1) : r2->m_th_var_list.get_th_var();
            TRACE("add_diseq", tout << "one theory diseq\n";
                  tout << v1 << " != " << v2 << "\n";
                  tout << "th1: " << t1 << " th2: " << r2->m_th_var_list.get_th_id() << "\n";
                  );
            if (t1 != null_theory_id && v1 != null_theory_var && v2 != null_theory_var &&
                t1 == r2->m_th_var_list.get_th_id()) {
                if (get_theory(t1)->use_diseqs())
                    push_new_th_diseq(t1, v1, v2);
            }
        }
        else {
            theory_var_list * l1 = r1->get_th_var_list();
            while (l1) {
                theory_id  t1 = l1->get_th_id();
                theory_var v1 = m_fparams.m_new_core2th_eq ? get_closest_var(n1, t1) : l1->get_th_var();
                theory * th   = get_theory(t1);
                TRACE("add_diseq", tout << m_manager.get_family_name(t1) << "\n";);
                if (th->use_diseqs()) {
                    theory_var v2 = m_fparams.m_new_core2th_eq ? get_closest_var(n2, t1) : r2->get_th_var(t1);
                    if (v2 != null_theory_var)
                        push_new_th_diseq(t1, v1, v2);
                }
                l1 = l1->get_next();
            }
        }
        return true;
    }

    /**
       \brief Return true if n1 and n2 are known to be disequal in the logical
       context.
    */
    bool context::is_diseq(enode * n1, enode * n2) const {
        SASSERT(m_manager.get_sort(n1->get_owner()) == m_manager.get_sort(n2->get_owner()));
        context * _this = const_cast<context*>(this);
        if (!m_is_diseq_tmp) {
            app * eq       = m_manager.mk_eq(n1->get_owner(), n2->get_owner());
            m_manager.inc_ref(eq);
            _this->m_is_diseq_tmp = enode::mk_dummy(m_manager, m_app2enode, eq);
        }
        else if (m_manager.get_sort(m_is_diseq_tmp->get_owner()->get_arg(0)) != m_manager.get_sort(n1->get_owner())) {
            m_manager.dec_ref(m_is_diseq_tmp->get_owner());
            app * eq = m_manager.mk_eq(n1->get_owner(), n2->get_owner());
            m_manager.inc_ref(eq);
            m_is_diseq_tmp->m_func_decl_id = UINT_MAX;
            m_is_diseq_tmp->m_owner = eq;
        }
        m_is_diseq_tmp->m_args[0] = n1;
        m_is_diseq_tmp->m_args[1] = n2;
        SASSERT(m_is_diseq_tmp->get_num_args() == 2);
        enode * r = m_cg_table.find(m_is_diseq_tmp);
        SASSERT((r != 0) == m_cg_table.contains(m_is_diseq_tmp));
        TRACE("is_diseq", tout << "r: " << r << "\n";);
        if (r) {
            SASSERT(r->is_eq());
            literal l = enode2literal(r->get_root());
            // SASSERT(result == is_diseq_slow(n1, n2));
            return l == false_literal || (is_relevant(l) && get_assignment(l) == l_false);
        }
        CTRACE("is_diseq_bug", is_diseq_slow(n1, n2), tout << "#" << n1->get_owner_id() << " #" << n2->get_owner_id() << "\n";);
        return false;
    }

    /**
       \brief Slow version of is_diseq
    */
    bool context::is_diseq_slow(enode * n1, enode * n2) const {
        if (n1->get_num_parents() > n2->get_num_parents())
            std::swap(n1, n2);
        for (enode * parent : enode::parents(n1)) {
            if (parent->is_eq() && is_relevant(parent->get_owner()) && get_assignment(enode2bool_var(parent)) == l_false &&
                ((parent->get_arg(0)->get_root() == n1->get_root() && parent->get_arg(1)->get_root() == n2->get_root()) ||
                 (parent->get_arg(1)->get_root() == n1->get_root() && parent->get_arg(0)->get_root() == n2->get_root()))) {
                TRACE("is_diseq_bug", tout << "parent: #" << parent->get_owner_id() << ", parent->root: #" <<
                      parent->get_root()->get_owner_id() << " assignment(parent): " << get_assignment(enode2bool_var(parent)) <<
                      " args: #" << parent->get_arg(0)->get_owner_id() << " #" << parent->get_arg(1)->get_owner_id() << "\n";);
                return true;
            }
        }
        return false;
    }

#define SMALL_NUM_PARENTS 3

    bool context::is_ext_diseq(enode * n1, enode * n2, unsigned depth) {
        enode * r1 = n1->get_root();
        enode * r2 = n2->get_root();
        if (r1 == r2)
            return false;
        if (r1->is_interpreted() && r2->is_interpreted())
            return true;
        if (is_diseq(n1, n2))
            return true;
        if (r1->get_num_parents() > r2->get_num_parents()) {
            std::swap(n1, n2);
            std::swap(r1, r2);
        }
        if (depth == 0)
            return false;
        if (r1->get_num_parents() < SMALL_NUM_PARENTS) {
            TRACE("is_ext_diseq", tout << mk_bounded_pp(n1->get_owner(), m_manager) << " " << mk_bounded_pp(n2->get_owner(), m_manager) << " " << depth << "\n";);
            for (enode * p1 : enode::parents(r1)) {
                if (!is_relevant(p1))
                    continue;
                if (p1->is_eq())
                    continue;
                if (!p1->is_cgr())
                    continue;
                func_decl * f     = p1->get_decl();
                TRACE("is_ext_diseq", tout << "p1: " << mk_bounded_pp(p1->get_owner(), m_manager) << "\n";);
                unsigned num_args = p1->get_num_args();
                for (enode * p2 : enode::parents(r2)) {
                    if (!is_relevant(p2))
                        continue;
                    if (p2->is_eq())
                        continue;
                    if (!p2->is_cgr())
                        continue;
                    TRACE("is_ext_diseq", tout << "p2: " << mk_bounded_pp(p2->get_owner(), m_manager) << "\n";);
                    if (p1->get_root() != p2->get_root() && p2->get_decl() == f && p2->get_num_args() == num_args) {
                        unsigned j = 0;
                        for (j = 0; j < num_args; j++) {
                            enode * arg1 = p1->get_arg(j)->get_root();
                            enode * arg2 = p2->get_arg(j)->get_root();
                            if (arg1 == arg2)
                                continue;
                            if ((arg1 == r1 || arg1 == r2) &&
                                (arg2 == r1 || arg2 == r2))
                                continue;
                            break;
                        }
                        if (j == num_args) {
                            TRACE("is_ext_diseq", tout << "found parents: " << mk_bounded_pp(p1->get_owner(), m_manager) << " " << mk_bounded_pp(p2->get_owner(), m_manager) << "\n";);
                            if (is_ext_diseq(p1, p2, depth - 1))
                                return true;
                        }
                    }
                }
            }
        }
        else {
            if (depth >= m_almost_cg_tables.size()) {
                unsigned old_sz = m_almost_cg_tables.size();
                m_almost_cg_tables.resize(depth+1);
                for (unsigned i = old_sz; i < depth + 1; i++)
                    m_almost_cg_tables[i] = alloc(almost_cg_table);
            }
            almost_cg_table & table = *(m_almost_cg_tables[depth]);
            table.reset(r1, r2);
            for (enode * p1 : enode::parents(r1)) {
                if (!is_relevant(p1))
                    continue;
                if (p1->is_eq())
                    continue;
                if (!p1->is_cgr())
                    continue;
                table.insert(p1);
            }
            if (table.empty())
                return false;
            for (enode * p2 : enode::parents(r2)) {
                if (!is_relevant(p2))
                    continue;
                if (p2->is_eq())
                    continue;
                if (!p2->is_cgr())
                    continue;
                list<enode*> * ps = table.find(p2);
                if (ps) {
                    while (ps) {
                        enode * p1 = ps->head();
                        if (p1->get_root() != p2->get_root() && is_ext_diseq(p1, p2, depth - 1))
                            return true;
                        ps = ps->tail();
                    }
                }
            }
        }
        return false;
    }

    /**
       \brief Return an enode n congruent to (f args). If there is no such enode in the E-graph, then return 0.
     */
    enode * context::get_enode_eq_to(func_decl * f, unsigned num_args, enode * const * args) {
        enode * tmp = m_tmp_enode.set(f, num_args, args);
        enode * r   = m_cg_table.find(tmp);
#ifdef Z3DEBUG
        if (r != 0) {
            SASSERT(r->get_owner()->get_decl() == f);
            SASSERT(r->get_num_args() == num_args);
            if (r->is_commutative()) {
                // TODO
            }
            else {
                for (unsigned i = 0; i < num_args; i++) {
                    expr * arg   = r->get_owner()->get_arg(i);
                    SASSERT(e_internalized(arg));
                    enode * _arg = get_enode(arg);
                    CTRACE("eq_to_bug", args[i]->get_root() != _arg->get_root(),
                           tout << "#" << args[i]->get_owner_id() << " #" << args[i]->get_root()->get_owner_id()
                           << " #" << _arg->get_owner_id() << " #" << _arg->get_root()->get_owner_id() << "\n";
                           tout << "#" << r->get_owner_id() << "\n";
                           display(tout););
                    SASSERT(args[i]->get_root() == _arg->get_root());
                }
            }
        }
#endif
        return r;
    }

    /**
       \brief Process the equality propagation queue.

       \remark The method assign_eq adds a new entry on this queue.
    */
    bool context::propagate_eqs() {
        TRACE("add_eq", tout << m_eq_propagation_queue.size() << "\n";);
        for (unsigned i = 0; i < m_eq_propagation_queue.size() && !get_cancel_flag(); i++) {
            new_eq & entry = m_eq_propagation_queue[i];
            add_eq(entry.m_lhs, entry.m_rhs, entry.m_justification);
            if (inconsistent())
                return false;
        }
        m_eq_propagation_queue.reset();
        return true;
    }

    /**
       \brief Process equalities, theory atoms, etc.
    */
    bool context::propagate_atoms() {
        SASSERT(!inconsistent());
        for (unsigned i = 0; i < m_atom_propagation_queue.size() && !get_cancel_flag(); i++) {
            SASSERT(!inconsistent());
            literal  l = m_atom_propagation_queue[i];
            bool_var v = l.var();
            bool_var_data & d = get_bdata(v);
            lbool val  = get_assignment(v);
            TRACE("propagate_atoms", tout << "propagating atom, #" << bool_var2expr(v)->get_id() << ", is_enode(): " << d.is_enode()
                  << " tag: " << (d.is_eq()?"eq":"") << (d.is_theory_atom()?"th":"") << (d.is_quantifier()?"q":"") << " " << l << "\n";);
            SASSERT(val != l_undef);
            if (d.is_enode())
                propagate_bool_var_enode(v);
            if (inconsistent())
                return false;
            if (d.is_eq()) {
                app * n   = to_app(m_bool_var2expr[v]);
                SASSERT(m_manager.is_eq(n));
                expr * lhs = n->get_arg(0);
                expr * rhs = n->get_arg(1);
                if (val == l_true) {
                    add_eq(get_enode(lhs), get_enode(rhs), eq_justification(l));
                }
                else {
                    TRACE("add_diseq", display_eq_detail(tout, bool_var2enode(v)););
                    if (!add_diseq(get_enode(lhs), get_enode(rhs)) && !inconsistent()) {
                        literal n_eq = literal(l.var(), true);
                        set_conflict(b_justification(mk_justification(eq_propagation_justification(get_enode(lhs), get_enode(rhs)))), n_eq);
                    }
                }
            }
            else if (d.is_theory_atom()) {
                theory * th = m_theories.get_plugin(d.get_theory());
                SASSERT(th);
                th->assign_eh(v, val == l_true);
            }
            else if (d.is_quantifier()) {
                // Remark: when RELEVANCY_LEMMA is true, a quantifier can be asserted to false and marked as relevant.
                // This happens when a quantifier is part of a lemma (conflict-clause), and this conflict clause
                // becomes an unit-clause and the remaining literal is the negation of a quantifier.
                CTRACE("assign_quantifier_bug", get_assignment(v) != l_true,
                       tout << "#" << bool_var2expr(v)->get_id() << " val: " << get_assignment(v) << "\n";
                       tout << mk_pp(bool_var2expr(v), m_manager) << "\n";
                       display(tout););
                SASSERT(is_quantifier(m_bool_var2expr[v]));
                if (get_assignment(v) == l_true) {
                    // All universal quantifiers have positive polarity in the input formula.
                    // So, we can ignore quantifiers assigned to false.
                    assign_quantifier(to_quantifier(m_bool_var2expr[v]));
                }
            }
            if (inconsistent())
                return false;
        }
        m_atom_propagation_queue.reset();
        return true;
    }

    class set_var_theory_trail : public trail<context> {
        bool_var m_var;
    public:
        set_var_theory_trail(bool_var v):m_var(v) {}
        void undo(context & ctx) override {
            bool_var_data & d = ctx.m_bdata[m_var];
            d.reset_notify_theory();
        }
    };

    void context::set_var_theory(bool_var v, theory_id tid) {
        SASSERT(get_var_theory(v) == null_theory_var);
        SASSERT(tid > 0 && tid <= 255);
        SASSERT(get_intern_level(v) <= m_scope_lvl);
        if (m_scope_lvl > get_intern_level(v))
            push_trail(set_var_theory_trail(v));
        bool_var_data & d = m_bdata[v];
        d.set_notify_theory(tid);
    }

    /**
       \brief Propagate the truth value assigned to v, to the enode
       associated with v.  Let n be the enode associated with v. Then,
       this method merges n = true_term (n = false_term) if v was
       assigned to true (false).
    */
    void context::propagate_bool_var_enode(bool_var v) {
        SASSERT(get_assignment(v) != l_undef);
        SASSERT(get_bdata(v).is_enode());
        lbool val  = get_assignment(v);
        TRACE("propagate_bool_var_enode_bug", tout << "var: " << v << " #" << bool_var2expr(v)->get_id() << "\n";);
        SASSERT(v < static_cast<int>(m_b_internalized_stack.size()));
        enode * n  = bool_var2enode(v);
        CTRACE("mk_bool_var", !n, tout << "No enode for " << v << "\n";);
        bool sign  = val == l_false;
        if (n->merge_tf())
            add_eq(n, sign ? m_false_enode : m_true_enode, eq_justification(literal(v, sign)));
        enode * r = n->get_root();
        if (r == m_true_enode || r == m_false_enode)
            return;
        // Move truth value to other elements of the equivalence class if:
        //   1) n is the root of the equivalence class
        //   2) n is not the root, but the variable associated with the root is unassigned.
        if (n == r ||
            !is_relevant(r) || // <<<< added to fix propagation bug.
            get_assignment(enode2bool_var(r)) != val) {
            enode * first = n;
            n = n->get_next();
            while (n != first) {
                bool_var v2 = enode2bool_var(n);
                if (get_assignment(v2) != val)
                    assign(literal(v2, sign), mk_justification(mp_iff_justification(first, n)));
                n = n->get_next();
            }
        }
    }

    /**
       \brief Traverse the disequalities of r's equivalence class, and
       propagate them to the theory.
    */
    void context::push_new_th_diseqs(enode * r, theory_var v, theory * th) {
        if (!th->use_diseqs()) {
            TRACE("push_new_th_diseqs", tout << m_manager.get_family_name(th->get_id()) << " not using diseqs\n";);
            return;
        }
        TRACE("push_new_th_diseqs", tout << "#" << r->get_owner_id() << " v" << v << "\n";);
        theory_id th_id = th->get_id();
        for (enode * parent : r->get_parents()) {
            CTRACE("parent_bug", parent == 0, tout << "#" << r->get_owner_id() << ", num_parents: " << r->get_num_parents() << "\n"; display(tout););
            if (parent->is_eq()) {
                bool_var bv = get_bool_var_of_id(parent->get_owner_id());
                if (get_assignment(bv) == l_false) {
                    enode * lhs = parent->get_arg(0);
                    enode * rhs = parent->get_arg(1);
                    TRACE("push_new_th_diseqs",
                          tout << "#" << parent->get_owner_id() << " ";
                           tout << "lhs: #" << lhs->get_owner_id() << ", rhs: #" << rhs->get_owner_id() <<
                           ", lhs->root: #" << lhs->get_root()->get_owner_id() << ", rhs->root: #" << rhs->get_root()->get_owner_id() <<
                           ", r: #" << r->get_owner_id() << ", r->root: #" << r->get_root()->get_owner_id() << "\n";
                          );
                    CTRACE("push_new_th_diseqs", lhs->get_root() != r->get_root() && rhs->get_root() != r->get_root(),
                           tout << "lhs: #" << lhs->get_owner_id() << ", rhs: #" << rhs->get_owner_id() <<
                           ", lhs->root: #" << lhs->get_root()->get_owner_id() << ", rhs->root: #" << rhs->get_root()->get_owner_id() <<
                           ", r: #" << r->get_owner_id() << ", r->root: #" << r->get_root()->get_owner_id() << "\n";
                          display(tout););
                    SASSERT(lhs->get_root() == r->get_root() || rhs->get_root() == r->get_root());
                    if (rhs->get_root() == r->get_root())
                        std::swap(lhs, rhs);
                    enode * rhs_root   = rhs->get_root();
                    theory_var rhs_var = m_fparams.m_new_core2th_eq ? get_closest_var(rhs, th_id) : rhs_root->get_th_var(th_id);
                    if (m_fparams.m_new_core2th_eq) {
                        theory_var _v = get_closest_var(lhs, th_id);
                        if (_v != null_theory_var)
                            v = _v;
                    }
                    if (rhs_var != null_theory_var && v != rhs_var /* if v == rhs_var then the context will detect the inconsistency. */)
                        push_new_th_diseq(th_id, v, rhs_var);
                }
            }
        }
    }

    /**
       \brief Return the truth assignment for an expression
       that is attached to a boolean variable.

       \pre The expression must be attached to a boolean variable.
    */
    inline lbool context::get_assignment_core(expr * n) const {
        CTRACE("get_assignment_bug", !b_internalized(n), tout << "n:\n" << mk_pp(n, m_manager) << "\n"; display(tout););
        SASSERT(b_internalized(n));
        unsigned id  = n->get_id();
        bool_var var = get_bool_var_of_id(id);
        SASSERT(var != null_bool_var);
        return get_assignment(var);
    }

    /**
       \brief Return the truth assignment for an expression.
       If the expression is a not-application, then its child
       is inspected instead.
    */
    lbool context::get_assignment(expr * n) const {
        if (m_manager.is_false(n))
            return l_false;
        expr* arg = nullptr;
        if (m_manager.is_not(n, arg))
            return ~get_assignment_core(arg);
        return get_assignment_core(n);
    }

    lbool context::find_assignment(expr * n) const {
        if (m_manager.is_false(n))
            return l_false;
        expr* arg = nullptr;
        if (m_manager.is_not(n, arg)) {
            if (b_internalized(arg))
                return ~get_assignment_core(arg);
            return l_undef;
        }
        if (b_internalized(n))
            return get_assignment(n);
        return l_undef;
    }

    /**
       \brief Return the assignment of a 'boolean' enode.
       If the enode is not boolean, then return l_undef.
    */
    lbool context::get_assignment(enode * n) const {
        expr * owner = n->get_owner();
        if (!m_manager.is_bool(owner))
            return l_undef;
        if (n == m_false_enode)
            return l_false;
        bool_var v = get_bool_var_of_id(owner->get_id());
        CTRACE("missing_propagation", v == null_bool_var, tout << mk_pp(owner, m_manager) << "\n";);
        return get_assignment(v);
    }

    /**
       \brief Return set of assigned literals as expressions.
    */
    void context::get_assignments(expr_ref_vector& assignments) {
        for (literal lit : m_assigned_literals) {
            expr_ref e(m_manager);
            literal2expr(lit, e);
            assignments.push_back(std::move(e));
        }
    }

    void context::relevant_eh(expr * n) {
        if (b_internalized(n)) {
            bool_var v        = get_bool_var(n);
            bool_var_data & d = get_bdata(v);
            SASSERT(relevancy());
            // Quantifiers are only asserted when marked as relevant.
            // Other atoms are only asserted when marked as relevant if m_relevancy_lvl >= 2
            if (d.is_atom() && (d.is_quantifier() || m_fparams.m_relevancy_lvl >= 2)) {
                lbool val  = get_assignment(v);
                if (val != l_undef)
                    m_atom_propagation_queue.push_back(literal(v, val == l_false));
            }
        }
        TRACE("propagate_relevancy", tout << "marking as relevant:\n" << mk_bounded_pp(n, m_manager) << " " << m_scope_lvl << "\n";);
#ifndef SMTCOMP
        m_case_split_queue->relevant_eh(n);
#endif

        if (is_app(n)) {
            if (e_internalized(n)) {
                SASSERT(relevancy());
                enode * e = get_enode(n);
                m_qmanager->relevant_eh(e);
            }

            theory * propagated_th = nullptr;
            family_id fid = to_app(n)->get_family_id();
            if (fid != m_manager.get_basic_family_id()) {
                theory * th = get_theory(fid);
                if (th != nullptr) {
                    th->relevant_eh(to_app(n));
                    propagated_th = th; // <<< mark that relevancy_eh was already invoked for theory th.
                }
            }

            if (e_internalized(n)) {
                enode *           e = get_enode(n);
                theory_var_list * l = e->get_th_var_list();
                while (l) {
                    theory_id  th_id = l->get_th_id();
                    theory *   th    = get_theory(th_id);
                    // I don't want to invoke relevant_eh twice for the same n.
                    if (th != propagated_th)
                        th->relevant_eh(to_app(n));
                    l = l->get_next();
                }
            }
        }
    }

    /**
       \brief Propagate relevancy using the queue of new assigned literals
       located at [qhead, m_assigned_literals.size()).
    */
    void context::propagate_relevancy(unsigned qhead) {
        if (!relevancy())
            return;
        unsigned sz = m_assigned_literals.size();
        while (qhead < sz) {
            literal l      = m_assigned_literals[qhead];
            SASSERT(get_assignment(l) == l_true);
            qhead++;
            bool_var var   = l.var();
            expr * n       = m_bool_var2expr[var];
            m_relevancy_propagator->assign_eh(n, !l.sign());
        }
        m_relevancy_propagator->propagate();
    }

    bool context::propagate_theories() {
        for (theory * t : m_theory_set) {
            t->propagate();
            if (inconsistent())
                return false;
        }
        return true;
    }

    void context::propagate_th_eqs() {
        for (unsigned i = 0; i < m_th_eq_propagation_queue.size() && !inconsistent(); i++) {
            new_th_eq curr = m_th_eq_propagation_queue[i];
            theory * th = get_theory(curr.m_th_id);
            SASSERT(th);
            th->new_eq_eh(curr.m_lhs, curr.m_rhs);
#ifdef Z3DEBUG
            push_trail(push_back_trail<context, new_th_eq, false>(m_propagated_th_eqs));
            m_propagated_th_eqs.push_back(curr);
#endif
        }
        m_th_eq_propagation_queue.reset();
    }

    void context::propagate_th_diseqs() {
        for (unsigned i = 0; i < m_th_diseq_propagation_queue.size() && !inconsistent(); i++) {
            new_th_eq curr = m_th_diseq_propagation_queue[i];
            theory * th = get_theory(curr.m_th_id);
            SASSERT(th);
            th->new_diseq_eh(curr.m_lhs, curr.m_rhs);
#ifdef Z3DEBUG
            push_trail(push_back_trail<context, new_th_eq, false>(m_propagated_th_diseqs));
            m_propagated_th_diseqs.push_back(curr);
#endif
        }
        m_th_diseq_propagation_queue.reset();
    }

    bool context::can_theories_propagate() const {
        for (theory* t : m_theory_set) {
            if (t->can_propagate()) {
                return true;
            }
        }
        return false;
    }

    bool context::can_propagate() const {
        return
            m_qhead != m_assigned_literals.size() ||
            m_relevancy_propagator->can_propagate() ||
            !m_atom_propagation_queue.empty() ||
            m_qmanager->can_propagate() ||
            can_theories_propagate() ||
            !m_eq_propagation_queue.empty() ||
            !m_th_eq_propagation_queue.empty() ||
            !m_th_diseq_propagation_queue.empty();
    }

    bool context::propagate() {
        TRACE("propagate", tout << "propagating... " << m_qhead << ":" << m_assigned_literals.size() << "\n";);
        while (true) {
            if (inconsistent())
                return false;
            unsigned qhead = m_qhead;
            if (!bcp())
                return false;
            if (!propagate_th_case_split(qhead))
                return false;
            if (get_cancel_flag()) {
                m_qhead = qhead;
                return true;
            }
            SASSERT(!inconsistent());
            propagate_relevancy(qhead);
            if (inconsistent())
                return false;
            if (!propagate_atoms())
                return false;
            if (!propagate_eqs())
                return false;
            if (get_cancel_flag()) {
                m_qhead = qhead;
                return true;
            }
            propagate_th_eqs();
            propagate_th_diseqs();
            if (inconsistent())
                return false;
            if (!propagate_theories())
                return false;
            m_qmanager->propagate();
            if (inconsistent())
                return false;
            if (resource_limits_exceeded()) {
                m_qhead = qhead;
                return true;
            }
            if (!can_propagate()) {
                CASSERT("diseq_bug", inconsistent() || check_missing_diseq_conflict());
                CASSERT("eqc_bool", check_eqc_bool_assignment());
                return true;
            }
        }
    }

    void context::set_conflict(const b_justification & js, literal not_l) {
        if (!inconsistent()) {
            TRACE("set_conflict", display_literal_verbose(tout, not_l); display(tout, js); );
            m_conflict = js;
            m_not_l    = not_l;
        }
    }

    void context::assign_quantifier(quantifier * q) {
        TRACE("assumption", tout << mk_pp(q, m_manager) << "\n";);
        m_qmanager->assign_eh(q);
    }

    bool context::contains_instance(quantifier * q, unsigned num_bindings, enode * const * bindings) {
        return m_fingerprints.contains(q, q->get_id(), num_bindings, bindings);
    }

    bool context::add_instance(quantifier * q, app * pat, unsigned num_bindings, enode * const * bindings, expr* def, unsigned max_generation,
                               unsigned min_top_generation, unsigned max_top_generation, vector<std::tuple<enode *, enode *>> & used_enodes) {
        return m_qmanager->add_instance(q, pat, num_bindings, bindings, def, max_generation, min_top_generation, max_top_generation, used_enodes);
    }

    void context::rescale_bool_var_activity() {
        TRACE("case_split", tout << "rescale\n";);        
        svector<double>::iterator it  = m_activity.begin();
        svector<double>::iterator end = m_activity.end();
        for (; it != end; ++it)
            *it *= INV_ACTIVITY_LIMIT;
        m_bvar_inc *= INV_ACTIVITY_LIMIT;
    }

    expr* context::next_decision() {
        bool_var var;
        lbool phase;
        m_case_split_queue->next_case_split(var, phase);
        if (var == null_bool_var) return m_manager.mk_true();
        m_case_split_queue->unassign_var_eh(var);
        return bool_var2expr(var);
    }

    /**
       \brief Execute next clase split, return false if there are no
       more case splits to be performed.
    */
    bool context::decide() {

        if (at_search_level() && !m_tmp_clauses.empty()) {
            switch (decide_clause()) {
            case l_true:  // already satisfied
                break;
            case l_undef: // made a decision
                return true;
            case l_false: // inconsistent
                return false;
            }
        }
        bool_var var;
        lbool phase;
        m_case_split_queue->next_case_split(var, phase);

        if (var == null_bool_var) {
            return false;
        }

        TRACE_CODE({
            static unsigned counter = 0;
            counter++;
            if (counter % 100 == 0) {
                TRACE("activity_profile",
                      for (unsigned i=0; i<get_num_bool_vars(); i++) {
                          tout << get_activity(i) << " ";
                      }
                      tout << "\n";);
            }});

        m_stats.m_num_decisions++;

        push_scope();
        TRACE("decide", tout << "splitting, lvl: " << m_scope_lvl << "\n";);

        TRACE("decide_detail", tout << mk_pp(bool_var2expr(var), m_manager) << "\n";);

        bool is_pos;

        if (is_quantifier(m_bool_var2expr[var])) {
            // Overriding any decision on how to assign the quantifier.
            // assigining a quantifier to false is equivalent to make it irrelevant.
            phase = l_false;
        }

        if (phase != l_undef) {
            is_pos = phase == l_true;
        }
        else {
            bool_var_data & d = m_bdata[var];

            if (d.try_true_first()) {
                is_pos = true;
            }
            else {
                switch (m_fparams.m_phase_selection) {
                case PS_CACHING:
                case PS_CACHING_CONSERVATIVE:
                case PS_CACHING_CONSERVATIVE2:
                    if (m_phase_cache_on && d.m_phase_available) {
                        TRACE("phase_selection", tout << "using cached value, is_pos: " << m_bdata[var].m_phase << ", var: p" << var << "\n";);
                        is_pos = m_bdata[var].m_phase;
                    }
                    else {
                        TRACE("phase_selection", tout << "setting to false\n";);
                        is_pos = m_phase_default;
                    }
                    break;
                case PS_ALWAYS_FALSE:
                    is_pos = false;
                    break;
                case PS_ALWAYS_TRUE:
                    is_pos = true;
                    break;
                case PS_RANDOM:
                    is_pos = (m_random() % 2 == 0);
                    break;
                case PS_OCCURRENCE: {
                    literal l(var);
                    is_pos = m_lit_occs[l.index()].size() > m_lit_occs[(~l).index()].size();
                    break;
                }
                default:
                    is_pos = false;
                    UNREACHABLE();
                }
            }
        }

        TRACE("decide", tout << "case split pos: " << is_pos << " p" << var << "\n"
              << "activity: " << get_activity(var) << "\n";);

        assign(literal(var, !is_pos), b_justification::mk_axiom(), true);
        return true;
    }

    /**
       \brief Update counter that is used to enable/disable phase caching.
    */
    void context::update_phase_cache_counter() {
        m_phase_counter++;
        if (m_phase_cache_on) {
            if (m_phase_counter >= m_fparams.m_phase_caching_on) {
                m_phase_counter  = 0;
                m_phase_cache_on = false;
                if (m_fparams.m_phase_selection == PS_CACHING_CONSERVATIVE2)
                    m_phase_default = !m_phase_default;
            }
        }
        else {
            if (m_phase_counter >= m_fparams.m_phase_caching_off) {
                m_phase_counter  = 0;
                m_phase_cache_on = true;
                if (m_fparams.m_phase_selection == PS_CACHING_CONSERVATIVE2)
                    m_phase_default = !m_phase_default;
            }
        }
    }

    /**
       \brief Create an internal backtracking point
    */
    void context::push_scope() {

        if (m_manager.has_trace_stream())
            m_manager.trace_stream() << "[push] " << m_scope_lvl << "\n";

        m_scope_lvl++;
        m_region.push_scope();
        m_scopes.push_back(scope());
        scope & s = m_scopes.back();

        m_relevancy_propagator->push();
        s.m_assigned_literals_lim    = m_assigned_literals.size();
        s.m_trail_stack_lim          = m_trail_stack.size();
        s.m_aux_clauses_lim          = m_aux_clauses.size();
        s.m_justifications_lim       = m_justifications.size();
        s.m_units_to_reassert_lim    = m_units_to_reassert.size();

        m_qmanager->push();

        m_fingerprints.push_scope();
        m_case_split_queue->push_scope();
        m_asserted_formulas.push_scope();

        for (theory* t : m_theory_set) 
            t->push_scope_eh();
        CASSERT("context", check_invariant());
    }

    /**
       \brief Execute generic undo-objects.
    */
    void context::undo_trail_stack(unsigned old_size) {
        ::undo_trail_stack(*this, m_trail_stack, old_size);
    }

    /**
       \brief Remove watch literal idx from the given clause.

       \pre idx must be 0 or 1.
    */
    void context::remove_watch_literal(clause * cls, unsigned idx) {
        m_watches[(~cls->get_literal(idx)).index()].remove_clause(cls);
    }

    /**
       \brief Remove boolean variable from watch lists.
    */
    void context::remove_watch(bool_var v) {
        literal lit(v);
        m_watches[lit.index()].reset();
        m_watches[(~lit).index()].reset();
    }

    /**
       \brief Update the index used for backward subsumption.
    */
    void context::remove_lit_occs(clause * cls) {
        unsigned num_lits = cls->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal l = cls->get_literal(i);
            m_lit_occs[l.index()].erase(cls);
        }
    }

    void context::remove_cls_occs(clause * cls) {
        remove_watch_literal(cls, 0);
        remove_watch_literal(cls, 1);
        if (lit_occs_enabled())
            remove_lit_occs(cls);
    }

    /**
       \brief Delete the given clause.

       \pre Clause is not in the reinit stack.
    */
    void context::del_clause(clause * cls) {
        SASSERT(m_flushing || !cls->in_reinit_stack());
        if (!cls->deleted())
            remove_cls_occs(cls);
        cls->deallocate(m_manager);
        m_stats.m_num_del_clause++;
    }

    /**
       \brief Delete the clauses in v at locations [old_size .. v.size())
       Reduce the size of v to old_size.
    */
    void context::del_clauses(clause_vector & v, unsigned old_size) {
        SASSERT(old_size <= v.size());
        clause_vector::iterator begin = v.begin() + old_size;
        clause_vector::iterator it    = v.end();
        while (it != begin) {
            --it;
            del_clause(*it);
        }
        v.shrink(old_size);
    }

#if 0
    void context::mark_as_deleted(clause * cls) {
        SASSERT(!cls->deleted());
        remove_cls_occs(cls);
        cls->mark_as_deleted(m_manager);
    }
#endif

    /**
       \brief Undo variable assignments.
    */
    void context::unassign_vars(unsigned old_lim) {
        SASSERT(old_lim <= m_assigned_literals.size());

        unsigned i = m_assigned_literals.size();
        while (i != old_lim) {
            --i;
            literal l                  = m_assigned_literals[i];
            m_assignment[l.index()]    = l_undef;
            m_assignment[(~l).index()] = l_undef;
            bool_var v                 = l.var();
            bool_var_data & d          = get_bdata(v);
            d.set_null_justification();
            m_case_split_queue->unassign_var_eh(v);
        }

        m_assigned_literals.shrink(old_lim);
        m_qhead = old_lim;
        SASSERT(m_qhead == m_assigned_literals.size());
    }

    /**
       \brief Invoke method del_eh for the justification that will be deleted.
       If the method in_region() returns false, then delete operator is invoked.
    */
    void context::del_justifications(ptr_vector<justification> & justifications, unsigned old_lim) {
        SASSERT(old_lim <= justifications.size());
        unsigned i = justifications.size();
        while (i != old_lim) {
            --i;
            justification * js = justifications[i];
            js->del_eh(m_manager);
            if (!js->in_region()) {
                dealloc(js);
            }
            else {
                // If the justification is in a region, then explicitly invoke the destructor.
                // This is needed because some justification objects contains vectors.
                // The destructors of these vectors need to be invoked.
                js->~justification();
            }
        }
        justifications.shrink(old_lim);
    }

    /**
       \brief Return true if all literals of c are assigned to false.
    */
    bool context::is_empty_clause(clause const * c) const {
        unsigned num_lits = c->get_num_literals();
        for(unsigned i = 0; i < num_lits; i++) {
            literal l = c->get_literal(i);
            if (get_assignment(l) != l_false)
                return false;
        }
        return true;
    }

    /**
       \brief Return true if the given clause contains one and only one unassigned literal.
    */
    bool context::is_unit_clause(clause const * c) const {
        bool found        = false;
        unsigned num_lits = c->get_num_literals();
        for(unsigned i = 0; i < num_lits; i++) {
            literal l = c->get_literal(i);
            switch (get_assignment(l)) {
            case l_false:
                break; // skip
            case l_undef:
                if (found)
                    return false;
                else
                    found = true;
                break;
            case l_true:
                return false; // clause is already satisfied.
            }
        }
        return found;
    }

    /**
       \brief When a clause is reinitialized (see reinit_clauses) enodes and literals may
       need to be recreated. When an enode is recreated, I want to use the same generation
       number it had before being deleted. Otherwise the generation will be 0, and will affect
       the loop prevetion heuristics used to control quantifier instantiation.
       Thus, I cache the generation number of enodes that will be deleted during backtracking
       and recreated by reinit_clauses.
    */
    void context::cache_generation(unsigned new_scope_lvl) {
        if (!m_clauses_to_reinit.empty()) {
            unsigned lim = m_scope_lvl;
            if (m_clauses_to_reinit.size() <= lim) {
                SASSERT(!m_clauses_to_reinit.empty());
                lim      = m_clauses_to_reinit.size() - 1;
            }
            for (unsigned i = new_scope_lvl; i <= lim; i++) {
                clause_vector & v = m_clauses_to_reinit[i];
                for (clause* cls : v) {
                    cache_generation(cls, new_scope_lvl);
                }
            }
        }
        if (!m_units_to_reassert.empty()) {
            scope & s   = m_scopes[new_scope_lvl];
            unsigned i  = s.m_units_to_reassert_lim;
            unsigned sz = m_units_to_reassert.size();
            for (; i < sz; i++) {
                expr * unit = m_units_to_reassert.get(i);
                cache_generation(unit, new_scope_lvl);
            }
        }
    }

    /**
       \brief See cache_generation(unsigned new_scope_lvl)
    */
    void context::cache_generation(clause const * cls, unsigned new_scope_lvl) {
        cache_generation(cls->get_num_literals(), cls->begin(), new_scope_lvl);
    }

    /**
       \brief See cache_generation(unsigned new_scope_lvl)
    */
    void context::cache_generation(unsigned num_lits, literal const * lits, unsigned new_scope_lvl) {
        for(unsigned i = 0; i < num_lits; i++) {
            bool_var v          = lits[i].var();
            unsigned ilvl       = get_intern_level(v);
            if (ilvl > new_scope_lvl)
                cache_generation(bool_var2expr(v), new_scope_lvl);
        }
    }

    /**
       \brief See cache_generation(unsigned new_scope_lvl)
    */
    void context::cache_generation(expr * n, unsigned new_scope_lvl) {
        ptr_buffer<expr> todo;
        todo.push_back(n);
        while (!todo.empty()) {
            expr * n = todo.back();
            todo.pop_back();
            if (m_cache_generation_visited.contains(n))
                continue;
            m_cache_generation_visited.insert(n);
            if (is_app(n)) {
                if (e_internalized(n)) {
                    enode * e     = get_enode(n);
                    unsigned ilvl = e->get_iscope_lvl();
                    if (ilvl <= new_scope_lvl)
                        continue; // node and its children will not be recreated during backtracking
                    TRACE("cached_generation", tout << "caching: #" << n->get_id() << " " << e->get_generation() << "\n";);
                    m_cached_generation.insert(n, e->get_generation());
                }
                for (expr * arg : *to_app(n)) {
                    if (is_app(arg) || is_quantifier(arg))
                        todo.push_back(arg);
                }
            }
            else if (is_quantifier(n) && b_internalized(n)) {
                m_cached_generation.insert(n, m_qmanager->get_generation(to_quantifier(n)));
                todo.push_back(to_quantifier(n)->get_expr());
            }
        }
    }

    /**
       \brief See cache_generation(unsigned new_scope_lvl)
    */
    void context::reset_cache_generation() {
        m_cache_generation_visited.reset();
        m_cached_generation.reset();
    }

    /**
       \brief Reinitialize learned clauses (lemmas) that contain boolean variables
       that were deleted during backtracking.

       \remark num_bool_vars contains the number of boolean variables alive
       after backtracking. So, a clause contains a dead variable if it
       contains a literal l where l.var() >= num_bool_vars.
    */
    void context::reinit_clauses(unsigned num_scopes, unsigned num_bool_vars) {
        TRACE("reinit_clauses_bug", display_watch_lists(tout););
        if (m_clauses_to_reinit.empty())
            return;
        unsigned lim = m_scope_lvl + num_scopes;
        if (m_clauses_to_reinit.size() <= lim) {
            SASSERT(!m_clauses_to_reinit.empty());
            lim      = m_clauses_to_reinit.size() - 1;
        }
        for (unsigned i = m_scope_lvl+1; i <= lim; i++) {
            clause_vector & v = m_clauses_to_reinit[i];
            for (clause* cls : v) {
                if (cls->deleted()) {
                    cls->release_atoms(m_manager);
                    cls->m_reinit              = false;
                    cls->m_reinternalize_atoms = false;
                    continue;
                }

                SASSERT(cls->in_reinit_stack());
                bool keep = false;
                if (cls->reinternalize_atoms()) {
                    SASSERT(cls->get_num_atoms() == cls->get_num_literals());
                    for (unsigned j = 0; j < 2; j++) {
                        literal l           = cls->get_literal(j);
                        if (l.var() < static_cast<int>(num_bool_vars)) {
                            // This boolean variable was not deleted during backtracking
                            //
                            // So, it is still a watch literal. I remove the watch, since
                            // the clause may have new watch-literals after reinitialization.
                            remove_watch_literal(cls, j);
                        }
                    }

                    unsigned num        = cls->get_num_literals();

                    if (lit_occs_enabled()) {
                        for (unsigned j = 0; j < num; j++) {
                            literal l           = cls->get_literal(j);
                            if (l.var() < static_cast<int>(num_bool_vars)) {
                                // This boolean variable was not deleted during backtracking
                                //
                                // So, remove it from lit_occs.
                                m_lit_occs[l.index()].erase(cls);
                            }
                        }
                    }

                    unsigned ilvl       = 0;
                    (void)ilvl;
                    for (unsigned j = 0; j < num; j++) {
                        expr * atom     = cls->get_atom(j);
                        bool   sign     = cls->get_atom_sign(j);
                        // Atom can be (NOT foo). This can happen, for example, when
                        // the NOT-application is a child of an uninterpreted function symbol.
                        // So, when reinternalizing the NOT-atom I should set the gate_ctx to false,
                        // and force expression to be reinternalized.
                        // Otherwise I set gate_ctx to true
                        bool gate_ctx = !m_manager.is_not(atom);
                        internalize(atom, gate_ctx);
                        SASSERT(b_internalized(atom));
                        bool_var v      = get_bool_var(atom);
                        DEBUG_CODE({
                            if (get_intern_level(v) > ilvl)
                                ilvl = get_intern_level(v);
                        });
                        literal l(v, sign);
                        cls->set_literal(j, l);
                    }
                    SASSERT(ilvl <= m_scope_lvl);
                    int w1_idx = select_watch_lit(cls, 0);
                    cls->swap_lits(0, w1_idx);
                    int w2_idx = select_watch_lit(cls, 1);
                    cls->swap_lits(1, w2_idx);
                    add_watch_literal(cls, 0);
                    add_watch_literal(cls, 1);

                    if (lit_occs_enabled())
                        add_lit_occs(cls);

                    literal l1 = cls->get_literal(0);
                    literal l2 = cls->get_literal(1);

                    if (get_assignment(l1) == l_false)
                        set_conflict(b_justification(cls));
                    else if (get_assignment(l2) == l_false)
                        assign(l1, b_justification(cls));

                    TRACE("reinit_clauses", tout << "reinit clause:\n"; display_clause_detail(tout, cls); tout << "\n";
                          tout << "activity: " << cls->get_activity() << ", num_bool_vars: " << num_bool_vars << ", scope_lvl: "
                          << m_scope_lvl << "\n";);
                    keep = true;
                }
                else {
                    SASSERT(!cls->reinternalize_atoms());
                    literal l1 = cls->get_literal(0);
                    literal l2 = cls->get_literal(1);
                    if (get_assignment(l1) == l_false && is_empty_clause(cls)) {
                        set_conflict(b_justification(cls));
                        keep = true;
                    }
                    else if (get_assignment(l2) == l_false && get_assignment(l1) == l_undef && is_unit_clause(cls)) {
                        assign(l1, b_justification(cls));
                        keep = true;
                    }
                }

                // SASSERT(!(cls->get_num_literals() == 3 &&
                //          (cls->get_literal(0).index() == 624 || cls->get_literal(0).index() == 103 || cls->get_literal(0).index() == 629) &&
                //          (cls->get_literal(1).index() == 624 || cls->get_literal(1).index() == 103 || cls->get_literal(1).index() == 629) &&
                //          (cls->get_literal(2).index() == 624 || cls->get_literal(2).index() == 103 || cls->get_literal(2).index() == 629)));

                if (keep && m_scope_lvl > m_base_lvl) {
                    m_clauses_to_reinit[m_scope_lvl].push_back(cls);
                }
                else {
                    // clause do not need to be in the reinit stack anymore,
                    // because it will be deleted when the base level is
                    // backtracked.
                    cls->release_atoms(m_manager);
                    cls->m_reinit              = false;
                    cls->m_reinternalize_atoms = false;
                }
            }
            v.reset();
        }
        CASSERT("reinit_clauses", check_clauses(m_lemmas));
        CASSERT("reinit_clauses", check_lit_occs());
        TRACE("reinit_clauses_bug", display_watch_lists(tout););
    }

    void context::reassert_units(unsigned units_to_reassert_lim) {
        unsigned i  = units_to_reassert_lim;
        unsigned sz = m_units_to_reassert.size();
        for (; i < sz; i++) {
            expr * unit   = m_units_to_reassert.get(i);
            bool gate_ctx = true;
            internalize(unit, gate_ctx);
            bool_var v    = get_bool_var(unit);
            bool sign     = m_units_to_reassert_sign[i] != 0;
            literal l(v, sign);
            assign(l, b_justification::mk_axiom());
            TRACE("reassert_units", tout << "reasserting #" << unit->get_id() << " " << sign << " @ " << m_scope_lvl << "\n";);
        }
        if (at_base_level()) {
            m_units_to_reassert.reset();
            m_units_to_reassert_sign.reset();
        }
    }

    /**
       \brief Backtrack 'num_scopes' scope levels. Return the number
       of boolean variables before reinitializing clauses. This value
       is useful because it can be used to detect which boolean variables
       were deleted.

       \warning This method will not invoke reset_cache_generation.
    */
    unsigned context::pop_scope_core(unsigned num_scopes) {

        try {
            if (m_manager.has_trace_stream())
                m_manager.trace_stream() << "[pop] " << num_scopes << " " << m_scope_lvl << "\n";

            TRACE("context", tout << "backtracking: " << num_scopes << " from " << m_scope_lvl << "\n";);
            TRACE("pop_scope_detail", display(tout););
            SASSERT(num_scopes > 0);
            SASSERT(num_scopes <= m_scope_lvl);
            SASSERT(m_scopes.size() == m_scope_lvl);

            unsigned new_lvl = m_scope_lvl - num_scopes;

            cache_generation(new_lvl);
            m_qmanager->pop(num_scopes);
            m_case_split_queue->pop_scope(num_scopes);

            TRACE("pop_scope", tout << "backtracking: " << num_scopes << ", new_lvl: " << new_lvl << "\n";);
            scope & s = m_scopes[new_lvl];
            TRACE("context", tout << "backtracking new_lvl: " << new_lvl << "\n";);

            unsigned units_to_reassert_lim = s.m_units_to_reassert_lim;

            if (new_lvl < m_base_lvl) {
                base_scope & bs = m_base_scopes[new_lvl];
                del_clauses(m_lemmas, bs.m_lemmas_lim);
                m_simp_qhead = bs.m_simp_qhead_lim;
                if (!bs.m_inconsistent) {
                    m_conflict = null_b_justification;
                    m_not_l = null_literal;
                    m_unsat_proof = nullptr;
                }
                m_base_scopes.shrink(new_lvl);
            }
            else {
                m_conflict = null_b_justification;
                m_not_l = null_literal;
            }
            del_clauses(m_aux_clauses, s.m_aux_clauses_lim);

            m_relevancy_propagator->pop(num_scopes);

            m_fingerprints.pop_scope(num_scopes);
            unassign_vars(s.m_assigned_literals_lim);
            undo_trail_stack(s.m_trail_stack_lim);

            for (theory* th : m_theory_set) {
                th->pop_scope_eh(num_scopes);
            }

            del_justifications(m_justifications, s.m_justifications_lim);

            m_asserted_formulas.pop_scope(num_scopes);

            m_eq_propagation_queue.reset();
            m_th_eq_propagation_queue.reset();
            m_th_diseq_propagation_queue.reset();
            m_atom_propagation_queue.reset();

            m_region.pop_scope(num_scopes);
            m_scopes.shrink(new_lvl);

            m_scope_lvl = new_lvl;
            if (new_lvl < m_base_lvl) {
                m_base_lvl = new_lvl;
                m_search_lvl = new_lvl; // Remark: not really necessary
            }

            unsigned num_bool_vars = get_num_bool_vars();
            // any variable >= num_bool_vars was deleted during backtracking.
            reinit_clauses(num_scopes, num_bool_vars);
            reassert_units(units_to_reassert_lim);
            TRACE("pop_scope_detail", tout << "end of pop_scope: \n"; display(tout););
            CASSERT("context", check_invariant());
            return num_bool_vars;
        }
        catch (...) {
            // throwing inside pop is just not cool.
            UNREACHABLE();
            throw;
        }
    }

    void context::pop_scope(unsigned num_scopes) {
        pop_scope_core(num_scopes);
        reset_cache_generation();
    }

    void context::pop_to_base_lvl() {
        SASSERT(m_scope_lvl >= m_base_lvl);
        if (!at_base_level()) {
            unsigned num_lvls = m_scope_lvl - m_base_lvl;
            pop_scope(num_lvls);
        }
        SASSERT(m_scope_lvl == m_base_lvl);
    }

    void context::pop_to_search_lvl() {
        unsigned num_levels = m_scope_lvl - get_search_level();
        if (num_levels > 0) {
            pop_scope(num_levels);
        }
    }

    /**
       \brief Simplify the given clause using the assignment.  Return
       true if the clause was already satisfied, and false otherwise.

       \remark This method should only be invoked if we are at the
       base level.
    */
    bool context::simplify_clause(clause * cls) {
        SASSERT(m_scope_lvl == m_base_lvl);
        unsigned s = cls->get_num_literals();
        if (get_assignment(cls->get_literal(0)) == l_true ||
            get_assignment(cls->get_literal(1)) == l_true) {
            // clause is already satisfied.
            return true;
        }

        literal_buffer simp_lits;

        unsigned i = 2;
        unsigned j = i;
        for(; i < s; i++) {
            literal l = cls->get_literal(i);
            switch(get_assignment(l)) {
            case l_false:
                if (m_manager.proofs_enabled())
                    simp_lits.push_back(~l);
                if (lit_occs_enabled())
                    m_lit_occs[l.index()].erase(cls);
                break;
            case l_undef:
                cls->set_literal(j, l);
                j++;
                break;
            case l_true:
                return true;
            }
        }

        if (j < s) {
            cls->set_num_literals(j);
            SASSERT(j >= 2);
        }

        if (m_manager.proofs_enabled() && !simp_lits.empty()) {
            SASSERT(m_scope_lvl == m_base_lvl);
            justification * js = cls->get_justification();
            justification * new_js = nullptr;
            if (js->in_region())
                new_js = mk_justification(unit_resolution_justification(m_region,
                                                                        js,
                                                                        simp_lits.size(),
                                                                        simp_lits.c_ptr()));
            else
                new_js = alloc(unit_resolution_justification, js, simp_lits.size(), simp_lits.c_ptr());
            cls->set_justification(new_js);
        }
        return false;
    }

    /**
       \brief Simplify the given vector of clauses starting at the given position.
       Return the number of deleted (already satisfied) clauses.
    */
    unsigned context::simplify_clauses(clause_vector & clauses, unsigned starting_at) {
        unsigned num_del_clauses = 0;
        clause_vector::iterator it  = clauses.begin();
        clause_vector::iterator end = clauses.end();
        it += starting_at;
        clause_vector::iterator it2 = it;
        for(; it != end; ++it) {
            clause * cls = *it;
            SASSERT(!cls->in_reinit_stack());
            TRACE("simplify_clauses_bug", display_clause(tout, cls); tout << "\n";);
            if (cls->deleted()) {
                del_clause(cls);
                num_del_clauses++;
            }
            else if (simplify_clause(cls)) {
                for (unsigned idx = 0; idx < 2; idx++) {
                    literal     l0        = cls->get_literal(idx);
                    b_justification l0_js = get_justification(l0.var());
                    if (l0_js != null_b_justification &&
                        l0_js.get_kind() == b_justification::CLAUSE &&
                        l0_js.get_clause() == cls) {
                        // cls is the explanation of l0
                        // it is safe to replace with axiom, we are at the base level.
                        SASSERT(m_scope_lvl == m_base_lvl);
                        bool_var v0 = l0.var();
                        if (m_manager.proofs_enabled()) {
                            SASSERT(m_search_lvl == m_base_lvl);
                            literal_buffer simp_lits;
                            unsigned num_lits = cls->get_num_literals();
                            for(unsigned i = 0; i < num_lits; i++) {
                                if (i != idx) {
                                    literal l = cls->get_literal(i);
                                    SASSERT(l != l0);
                                    simp_lits.push_back(~l);
                                }
                            }
                            justification * cls_js = cls->get_justification();
                            justification * js = nullptr;
                            if (!cls_js || cls_js->in_region()) {
                                // If cls_js is 0 or is allocated in a region, then
                                // we can allocate the new justification in a region too.
                                js = mk_justification(unit_resolution_justification(m_region,
                                                                                    cls_js,
                                                                                    simp_lits.size(),
                                                                                    simp_lits.c_ptr()));
                            }
                            else {
                                js = alloc(unit_resolution_justification, cls_js, simp_lits.size(), simp_lits.c_ptr());
                                // js took ownership of the justification object.
                                cls->set_justification(nullptr);
                                m_justifications.push_back(js);
                            }
                            set_justification(v0, m_bdata[v0], b_justification(js));
                        }
                        else
                            m_bdata[v0].set_axiom();
                    }
                }
                del_clause(cls);
                num_del_clauses++;
            }
            else {
                *it2 = *it;
                ++it2;
                m_simp_counter += cls->get_num_literals();
            }
        }
        clauses.set_end(it2);
        CASSERT("simplify_clauses", check_invariant());
        return num_del_clauses;
    }

    /**
       \brief Simplify the set of clauses if possible (solver is at base level).
    */
    void context::simplify_clauses() {
        // Remark: when assumptions are used m_scope_lvl >= m_search_lvl > m_base_lvl. Therefore, no simplification is performed.
        if (m_scope_lvl > m_base_lvl)
            return;

        unsigned sz = m_assigned_literals.size();
        SASSERT(m_simp_qhead <= sz);

        if (m_simp_qhead == sz || m_simp_counter > 0) {
            TRACE("simplify_clauses", tout << "m_simp_qhead: " << m_simp_qhead << " m_simp_counter: " << m_simp_counter << "\n";);
            return;
        }

        if (m_aux_clauses.empty() && m_lemmas.empty()) {
            TRACE("simplify_clauses", tout << "no clauses to simplify\n";);
            return;
        }

        TRACE("simplify_clauses_detail", tout << "before:\n"; display_clauses(tout, m_lemmas););
        IF_VERBOSE(2, verbose_stream() << "(smt.simplifying-clause-set"; verbose_stream().flush(););

        SASSERT(check_clauses(m_lemmas));
        SASSERT(check_clauses(m_aux_clauses));


        // m_simp_counter is used to balance the cost of simplify_clause.
        //
        // After executing simplify_clauses, the counter will contain
        // an approximation of the cost of executing simplify_clauses again.
        // That is, the number of literals that will need to be visited.
        //
        // The value of the counter is decremented each time we visit
        // a variable during propagation.
        //
        m_simp_counter = 0;
        // the field m_simp_qhead is used to check whether there are
        // new assigned literals at the base level.
        m_simp_qhead = m_assigned_literals.size();

        unsigned num_del_clauses = 0;

        SASSERT(m_scope_lvl == m_base_lvl);
        if (m_base_lvl == 0) {
            num_del_clauses += simplify_clauses(m_aux_clauses, 0);
            num_del_clauses += simplify_clauses(m_lemmas, 0);
        }
        else {
            scope & s       = m_scopes[m_base_lvl - 1];
            base_scope & bs = m_base_scopes[m_base_lvl - 1];
            num_del_clauses += simplify_clauses(m_aux_clauses, s.m_aux_clauses_lim);
            num_del_clauses += simplify_clauses(m_lemmas, bs.m_lemmas_lim);
        }
        TRACE("simp_counter", tout << "simp_counter: " << m_simp_counter << " scope_lvl: " << m_scope_lvl << "\n";);
        IF_VERBOSE(2, verbose_stream() << " :num-deleted-clauses " << num_del_clauses << ")" << std::endl;);
        TRACE("simplify_clauses_detail", tout << "after:\n"; display_clauses(tout, m_lemmas););
        SASSERT(check_clauses(m_lemmas) && check_clauses(m_aux_clauses));
    }

    struct clause_lt {
        bool operator()(clause * cls1, clause * cls2) const { return cls1->get_activity() > cls2->get_activity(); }
    };

    /**
       \brief Delete low activity lemmas
    */
    inline void context::del_inactive_lemmas() {
        if (m_fparams.m_lemma_gc_strategy == LGC_NONE)
            return;
        else if (m_fparams.m_lemma_gc_half)
            del_inactive_lemmas1();
        else
            del_inactive_lemmas2();

        m_num_conflicts_since_lemma_gc = 0;
        if (m_fparams.m_lemma_gc_strategy == LGC_GEOMETRIC)
            m_lemma_gc_threshold = static_cast<unsigned>(m_lemma_gc_threshold * m_fparams.m_lemma_gc_factor);
    }

    /**
       \brief Delete (approx.) half of low activity lemmas
    */
    void context::del_inactive_lemmas1() {
        unsigned sz            = m_lemmas.size();
        unsigned start_at      = m_base_lvl == 0 ? 0 : m_base_scopes[m_base_lvl - 1].m_lemmas_lim;
        SASSERT(start_at <= sz);
        if (start_at + m_fparams.m_recent_lemmas_size >= sz)
            return;
        IF_VERBOSE(2, verbose_stream() << "(smt.delete-inactive-lemmas"; verbose_stream().flush(););
        SASSERT (m_fparams.m_recent_lemmas_size < sz);
        unsigned end_at        = sz - m_fparams.m_recent_lemmas_size;
        SASSERT(start_at < end_at);
        std::stable_sort(m_lemmas.begin() + start_at, m_lemmas.begin() + end_at, clause_lt());
        unsigned start_del_at  = (start_at + end_at) / 2;
        unsigned i             = start_del_at;
        unsigned j             = i;
        unsigned num_del_cls   = 0;
        TRACE("del_inactive_lemmas", tout << "sz: " << sz << ", start_at: " << start_at << ", end_at: " << end_at
              << ", start_del_at: " << start_del_at << "\n";);
        for (; i < end_at; i++) {
            clause * cls = m_lemmas[i];
            if (can_delete(cls)) {
                TRACE("del_inactive_lemmas", tout << "deleting: "; display_clause(tout, cls); tout << ", activity: " <<
                      cls->get_activity() << "\n";);
                del_clause(cls);
                num_del_cls++;
            }
            else {
                m_lemmas[j] = cls;
                j++;
            }
        }
        // keep recent clauses
        for (; i < sz; i++) {
            clause * cls = m_lemmas[i];
            if (cls->deleted() && can_delete(cls)) {
                del_clause(cls);
                num_del_cls++;
            }
            else {
                m_lemmas[j] = cls;
                j++;
            }
        }
        m_lemmas.shrink(j);
        if (m_fparams.m_clause_decay > 1) {
            // rescale activity
            for (i = start_at; i < j; i++) {
                clause * cls = m_lemmas[i];
                cls->set_activity(cls->get_activity() / m_fparams.m_clause_decay);
            }
        }
        IF_VERBOSE(2, verbose_stream() << " :num-deleted-clauses " << num_del_cls << ")" << std::endl;);
    }

    /**
       \brief More sophisticated version of del_inactive_lemmas. Here the lemmas are divided in two
       groups (old and new) based on the value of m_new_old_ratio parameter.
       A clause is deleted/retained based on its activity and relevancy. Clauses with several
       unassigned literals are considered less relevant. The threshold used for activity and relevancy
       depends on which group the clauses is in.
    */
    void context::del_inactive_lemmas2() {
        IF_VERBOSE(2, verbose_stream() << "(smt.delete-inactive-clauses "; verbose_stream().flush(););
        unsigned sz            = m_lemmas.size();
        unsigned start_at      = m_base_lvl == 0 ? 0 : m_base_scopes[m_base_lvl - 1].m_lemmas_lim;
        SASSERT(start_at <= sz);
        unsigned real_sz       = sz - start_at;
        // idx of the first learned clause considered "new"
        unsigned new_first_idx = start_at + (real_sz / m_fparams.m_new_old_ratio) * (m_fparams.m_new_old_ratio - 1);
        SASSERT(new_first_idx <= sz);
        unsigned i             = start_at;
        unsigned j             = i;
        unsigned num_del_cls   = 0;
        for (; i < sz; i++) {
            clause * cls = m_lemmas[i];
            if (can_delete(cls)) {
                if (cls->deleted()) {
                    // clause is already marked for deletion
                    del_clause(cls);
                    num_del_cls++;
                    continue;
                }
                // A clause is deleted if it has low activity and the number of unknowns is greater than a threshold.
                // The activity threshold depends on how old the clause is.
                unsigned act_threshold = m_fparams.m_old_clause_activity -
                    (m_fparams.m_old_clause_activity - m_fparams.m_new_clause_activity) * ((i - start_at) / real_sz);
                if (cls->get_activity() < act_threshold) {
                    unsigned rel_threshold = (i >= new_first_idx ? m_fparams.m_new_clause_relevancy : m_fparams.m_old_clause_relevancy);
                    if (more_than_k_unassigned_literals(cls, rel_threshold)) {
                        del_clause(cls);
                        num_del_cls++;
                        continue;
                    }
                }
            }
            m_lemmas[j] = cls;
            j++;
            cls->set_activity(static_cast<unsigned>(cls->get_activity() / m_fparams.m_inv_clause_decay));
        }
        SASSERT(j <= sz);
        m_lemmas.shrink(j);
        IF_VERBOSE(2, verbose_stream() << " :num-deleted-clauses " << num_del_cls << ")" << std::endl;);
    }

    /**
       \brief Return true if "cls" has more than (or equal to) k unassigned literals.
    */
    bool context::more_than_k_unassigned_literals(clause * cls, unsigned k) {
        SASSERT(k > 0);
        unsigned num_lits = cls->get_num_literals();
        for(unsigned i = 0; i < num_lits; i++) {
            literal l = cls->get_literal(i);
            if (get_assignment(l) == l_undef) {
                k--;
                if (k == 0) {
                    return true;
                }
            }
        }
        return false;
    }


#ifdef Z3DEBUG
    /**
       \brief Return true if a symbol of the given theory was already internalized.
    */
    bool context::already_internalized_theory(theory * th) const {
        return already_internalized_theory_core(th, m_b_internalized_stack) || already_internalized_theory_core(th, m_e_internalized_stack);
    }

    /**
       \brief Auxiliary method for #already_internalized_theory.
    */
    bool context::already_internalized_theory_core(theory * th, expr_ref_vector const & s) const {
        expr_mark visited;
        family_id fid = th->get_id();
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * n = s.get(i);
            if (uses_theory(n, fid, visited))
                return true;
        }
        return false;
    }
#endif

    void context::register_plugin(theory * th) {
        if (m_theories.get_plugin(th->get_family_id()) != nullptr) {
            dealloc(th);
            return; // context already has a theory for the given family id.
        }
        SASSERT(std::find(m_theory_set.begin(), m_theory_set.end(), th) == m_theory_set.end());
        SASSERT(!already_internalized_theory(th));
        th->init(this);
        m_theories.register_plugin(th);
        m_theory_set.push_back(th);
        {
#ifdef Z3DEBUG
            // It is unsafe to invoke push_trail from the method push_scope_eh.
            flet<bool> l(m_trail_enabled, false);
#endif
            for (unsigned i = 0; i < m_scope_lvl; ++i)
                th->push_scope_eh();
        }
    }

    void context::push() {
        TRACE("trigger_bug", tout << "context::push()\n";);
        scoped_suspend_rlimit _suspend_cancel(m_manager.limit());
        pop_to_base_lvl();
        setup_context(false);
        bool was_consistent = !inconsistent();
        internalize_assertions(); // internalize assertions before invoking m_asserted_formulas.push_scope
        propagate();
        if (was_consistent && inconsistent()) {
            // logical context became inconsistent during user PUSH
            VERIFY(!resolve_conflict()); // build the proof
        }
        push_scope();
        m_base_scopes.push_back(base_scope());
        base_scope & bs = m_base_scopes.back();
        bs.m_lemmas_lim = m_lemmas.size();
        bs.m_inconsistent = inconsistent();
        bs.m_simp_qhead_lim = m_simp_qhead;
        m_base_lvl++;
        m_search_lvl++; // Not really necessary. But, it is useful to enforce the invariant m_search_lvl >= m_base_lvl
        SASSERT(m_base_lvl <= m_scope_lvl);
    }

    void context::pop(unsigned num_scopes) {
        SASSERT (num_scopes > 0);
        if (num_scopes > m_scope_lvl) return;
        pop_to_base_lvl();
        pop_scope(num_scopes);
    }

    /**
       \brief Free memory allocated by logical context.
    */
    void context::flush() {
        flet<bool> l1(m_flushing, true);
        TRACE("flush", tout << "m_scope_lvl: " << m_scope_lvl << "\n";);
        m_relevancy_propagator = nullptr;
        m_model_generator->reset();
        for (theory* t : m_theory_set) 
            t->flush_eh();
        undo_trail_stack(0);
        m_qmanager = nullptr;
        del_clauses(m_aux_clauses, 0);
        del_clauses(m_lemmas, 0);
        del_justifications(m_justifications, 0);
        reset_tmp_clauses();
        if (m_is_diseq_tmp) {
            m_is_diseq_tmp->del_eh(m_manager, false);
            m_manager.dec_ref(m_is_diseq_tmp->get_owner());
            enode::del_dummy(m_is_diseq_tmp);
            m_is_diseq_tmp = nullptr;
        }
        std::for_each(m_almost_cg_tables.begin(), m_almost_cg_tables.end(), delete_proc<almost_cg_table>());
    }

    void context::assert_expr_core(expr * e, proof * pr) {
        if (get_cancel_flag()) return;
        SASSERT(is_well_sorted(m_manager, e));
        TRACE("begin_assert_expr", tout << this << " " << mk_pp(e, m_manager) << "\n";);
        TRACE("begin_assert_expr_ll", tout << mk_ll_pp(e, m_manager) << "\n";);
        pop_to_base_lvl();
        if (pr == nullptr)
            m_asserted_formulas.assert_expr(e);
        else
            m_asserted_formulas.assert_expr(e, pr);
        TRACE("end_assert_expr_ll", ast_mark m; m_asserted_formulas.display_ll(tout, m););
    }

    void context::assert_expr(expr * e) {
        assert_expr(e, nullptr);
    }

    void context::assert_expr(expr * e, proof * pr) {
        timeit tt(get_verbosity_level() >= 100, "smt.simplifying");
        assert_expr_core(e, pr);
    }

    class case_split_insert_trail : public trail<context> {
        literal l;
    public:
        case_split_insert_trail(literal l):
            l(l) {
        }
        void undo(context & ctx) override {
            ctx.undo_th_case_split(l);
        }
    };

    void context::mk_th_case_split(unsigned num_lits, literal * lits) {
        TRACE("theory_case_split", display_literals_verbose(tout << "theory case split: ", num_lits, lits); tout << std::endl;);
        // If we don't use the theory case split heuristic,
        // for each pair of literals (l1, l2) we add the clause (~l1 OR ~l2)
        // to enforce the condition that at most one literal can be assigned 'true'.
        if (!m_fparams.m_theory_case_split) {
            for (unsigned i = 0; i < num_lits; ++i) {
                for (unsigned j = i+1; j < num_lits; ++j) {
                    literal l1 = lits[i];
                    literal l2 = lits[j];
                    mk_clause(~l1, ~l2, (justification*) nullptr);
                }
            }
        } else {
            literal_vector new_case_split;
            for (unsigned i = 0; i < num_lits; ++i) {
                literal l = lits[i];
                SASSERT(!m_all_th_case_split_literals.contains(l.index()));
                m_all_th_case_split_literals.insert(l.index());
                push_trail(case_split_insert_trail(l));
                new_case_split.push_back(l);
            }
            m_th_case_split_sets.push_back(new_case_split);
            push_trail(push_back_vector<context, vector<literal_vector> >(m_th_case_split_sets));
            for (unsigned i = 0; i < num_lits; ++i) {
                literal l = lits[i];
                if (!m_literal2casesplitsets.contains(l.index())) {
                    m_literal2casesplitsets.insert(l.index(), vector<literal_vector>());
                }
                m_literal2casesplitsets[l.index()].push_back(new_case_split);
            }
            TRACE("theory_case_split", tout << "tracking case split literal set { ";
                  for (unsigned i = 0; i < num_lits; ++i) {
                      tout << lits[i].index() << " ";
                  }
                  tout << "}" << std::endl;
                  );
        }
    }

    void context::add_theory_aware_branching_info(bool_var v, double priority, lbool phase) {
        m_case_split_queue->add_theory_aware_branching_info(v, priority, phase);
    }

    void context::undo_th_case_split(literal l) {
        m_all_th_case_split_literals.remove(l.index());
        if (m_literal2casesplitsets.contains(l.index())) {
            if (!m_literal2casesplitsets[l.index()].empty()) {
                m_literal2casesplitsets[l.index()].pop_back();
            }
        }
    }

    bool context::propagate_th_case_split(unsigned qhead) {
        if (m_all_th_case_split_literals.empty())
            return true;

        // iterate over all literals assigned since the last time this method was called,
        // not counting any literals that get assigned by this method
        // this relies on bcp() to give us its old m_qhead and therefore
        // bcp() should always be called before this method

        unsigned assigned_literal_end = m_assigned_literals.size();
        for (; qhead < assigned_literal_end; ++qhead) {
            literal l = m_assigned_literals[qhead];
            TRACE("theory_case_split", tout << "check literal " << l.index() << std::endl; display_literal_verbose(tout, l); tout << std::endl;);
            // check if this literal participates in any theory case split
            if (!m_all_th_case_split_literals.contains(l.index())) {
                continue;
            }
            TRACE("theory_case_split", tout << "assigned literal " << l.index() << " is a theory case split literal" << std::endl;);
            // now find the sets of literals which contain l
            vector<literal_vector> const& case_split_sets = m_literal2casesplitsets[l.index()];
            for (vector<literal_vector>::const_iterator it = case_split_sets.begin(); it != case_split_sets.end(); ++it) {
                literal_vector case_split_set = *it;
                TRACE("theory_case_split", tout << "found case split set { ";
                      for(literal_vector::iterator set_it = case_split_set.begin(); set_it != case_split_set.end(); ++set_it) {
                          tout << set_it->index() << " ";
                      }
                      tout << "}" << std::endl;);
                for(literal_vector::iterator set_it = case_split_set.begin(); set_it != case_split_set.end(); ++set_it) {
                    literal l2 = *set_it;
                    if (l2 != l) {
                        b_justification js(l);
                        TRACE("theory_case_split", tout << "case split literal "; l2.display(tout, m_manager, m_bool_var2expr.c_ptr()););
                        assign(~l2, js);
                        if (inconsistent()) {
                            TRACE("theory_case_split", tout << "conflict detected!" << std::endl;);
                            return false;
                        }
                    }
                }
            }
        }
        // if we get here without detecting a conflict, we're fine
        return true;
    }

    bool context::reduce_assertions() {
        if (!m_asserted_formulas.inconsistent()) {
            // SASSERT(at_base_level());
            m_asserted_formulas.reduce();
        }
        return m_asserted_formulas.inconsistent();
    }

    static bool is_valid_assumption(ast_manager & m, expr * assumption) {
        expr* arg;
        if (!m.is_bool(assumption))
            return false;
        if (is_uninterp_const(assumption))
            return true;
        if (m.is_not(assumption, arg) && is_uninterp_const(arg))
            return true;
        if (!is_app(assumption))
            return false;
        if (to_app(assumption)->get_num_args() == 0)
            return true;
        if (m.is_not(assumption, arg) && is_app(arg) && to_app(arg)->get_num_args() == 0)
            return true;
        return false;
    }

    void context::internalize_proxies(expr_ref_vector const& asms, vector<std::pair<expr*,expr_ref>>& asm2proxy) {
        for (expr* e : asms) {
            if (is_valid_assumption(m_manager, e)) {
                asm2proxy.push_back(std::make_pair(e, expr_ref(e, m_manager)));
            }
            else {
                expr_ref proxy(m_manager), fml(m_manager);
                proxy = m_manager.mk_fresh_const("proxy", m_manager.mk_bool_sort());
                fml = m_manager.mk_implies(proxy, e);
                m_asserted_formulas.assert_expr(fml);
                asm2proxy.push_back(std::make_pair(e, proxy));
            }
        }
        // The new assertions are of the form 'proxy => assumption'
        // so clause simplification is sound even as these are removed after pop_scope.
        internalize_assertions();
    }

    void context::internalize_assertions() {
        if (get_cancel_flag()) return;
        TRACE("internalize_assertions", tout << "internalize_assertions()...\n";);
        timeit tt(get_verbosity_level() >= 100, "smt.preprocessing");
        reduce_assertions();
        if (!m_asserted_formulas.inconsistent()) {
            unsigned sz    = m_asserted_formulas.get_num_formulas();
            unsigned qhead = m_asserted_formulas.get_qhead();
            while (qhead < sz) {
                if (get_cancel_flag()) {
                    m_asserted_formulas.commit(qhead);
                    return;
                }
                expr * f   = m_asserted_formulas.get_formula(qhead);
                proof * pr = m_asserted_formulas.get_formula_proof(qhead);
                internalize_assertion(f, pr, 0);
                qhead++;
            }
            m_asserted_formulas.commit();
        }
        if (m_asserted_formulas.inconsistent() && !inconsistent()) {
            proof * pr = m_asserted_formulas.get_inconsistency_proof();
            if (pr == nullptr) {
                set_conflict(b_justification::mk_axiom());
            }
            else {
                set_conflict(mk_justification(justification_proof_wrapper(*this, pr)));
                m_unsat_proof = pr;
            }
        }
        TRACE("internalize_assertions", tout << "after internalize_assertions()...\n";
              tout << "inconsistent: " << inconsistent() << "\n";);
        TRACE("after_internalize_assertions", display(tout););
    }

    /**
       \brief Assumptions must be uninterpreted boolean constants (aka propositional variables).
    */
    bool context::validate_assumptions(expr_ref_vector const& asms) {
        for (expr* a : asms) {
            SASSERT(a);
            if (!is_valid_assumption(m_manager, a)) {
                warning_msg("an assumption must be a propositional variable or the negation of one");
                return false;
            }
        }
        return true;
    }

    void context::init_clause(expr_ref_vector const& _clause) {
        literal_vector lits;
        for (expr* lit : _clause) {
            internalize_formula(lit, true);
            mark_as_relevant(lit);
            lits.push_back(get_literal(lit));
        }
        clause* clausep = nullptr;
        if (lits.size() >= 2) {
            justification* js = nullptr;
            if (m_manager.proofs_enabled()) {
                proof * pr = mk_clause_def_axiom(lits.size(), lits.c_ptr(), nullptr);
                js = mk_justification(justification_proof_wrapper(*this, pr));
            }
            clausep = clause::mk(m_manager, lits.size(), lits.c_ptr(), CLS_AUX, js);
        }
        m_tmp_clauses.push_back(std::make_pair(clausep, lits));
    }

    void context::reset_tmp_clauses() {
        for (auto& p : m_tmp_clauses) {
            if (p.first) del_clause(p.first);
        }
        m_tmp_clauses.reset();
    }

    lbool context::decide_clause() {
        if (m_tmp_clauses.empty()) return l_true;
        for (auto & tmp_clause : m_tmp_clauses) {
            literal_vector& lits = tmp_clause.second;
            literal unassigned = null_literal;
            for (literal l : lits) {
                switch (get_assignment(l)) {
                case l_false:
                    break;
                case l_true:
                    goto next_clause;
                default:
                    unassigned = l;
                }         
            }

            if (unassigned != null_literal) {
                shuffle(lits.size(), lits.c_ptr(), m_random);
                push_scope();
                assign(unassigned, b_justification::mk_axiom(), true);
                return l_undef;
            }

            if (lits.size() == 1) {
                set_conflict(b_justification(), ~lits[0]);
            }
            else {
                set_conflict(b_justification(tmp_clause.first), null_literal);
            }		
            VERIFY(!resolve_conflict());
            return l_false;
        next_clause:
            ;
        }
        return l_true;
    }

    void context::init_assumptions(expr_ref_vector const& asms) {
        reset_assumptions();
        m_literal2assumption.reset();
        m_unsat_core.reset();
        if (!asms.empty()) {
            // We must give a chance to the theories to propagate before we create a new scope...
            propagate();
            // Internal backtracking scopes (created with push_scope()) must only be created when we are
            // in a consistent context.
            if (inconsistent())
                return;
            if (get_cancel_flag())
                return;
            push_scope();
            vector<std::pair<expr*,expr_ref>> asm2proxy;
            internalize_proxies(asms, asm2proxy);
            for (auto const& p: asm2proxy) {
                expr_ref curr_assumption = p.second;
                expr* orig_assumption = p.first;
                if (m_manager.is_true(curr_assumption)) continue;
                SASSERT(is_valid_assumption(m_manager, curr_assumption));
                proof * pr = m_manager.mk_asserted(curr_assumption);
                internalize_assertion(curr_assumption, pr, 0);
                literal l = get_literal(curr_assumption);
                m_literal2assumption.insert(l.index(), orig_assumption);
                // mark_as_relevant(l); <<< not needed
                // internalize_assertion marked l as relevant.
                SASSERT(is_relevant(l));
                TRACE("assumptions", tout << l << ":" << curr_assumption << " " << mk_pp(orig_assumption, m_manager) << "\n";);
                if (m_manager.proofs_enabled())
                    assign(l, mk_justification(justification_proof_wrapper(*this, pr)));
                else
                    assign(l, b_justification::mk_axiom());
                m_assumptions.push_back(l);
                get_bdata(l.var()).m_assumption = true;
            }
        }
        m_search_lvl = m_scope_lvl;
        SASSERT(asms.empty() || m_search_lvl > m_base_lvl);
        SASSERT(!asms.empty() || m_search_lvl == m_base_lvl);
        TRACE("after_internalization", display(tout););
    }

    void context::reset_assumptions() {
        TRACE("unsat_core_bug", tout << "reset " << m_assumptions << "\n";);
        for (literal lit : m_assumptions) 
            get_bdata(lit.var()).m_assumption = false;
        m_assumptions.reset();
    }

    lbool context::mk_unsat_core(lbool r) {        
        if (r != l_false) return r;
        SASSERT(inconsistent());
        if (!tracking_assumptions()) {
            SASSERT(m_assumptions.empty());
            return l_false;
        }
        uint_set already_found_assumptions;
        literal_vector::const_iterator it  = m_conflict_resolution->begin_unsat_core();
        literal_vector::const_iterator end = m_conflict_resolution->end_unsat_core();
        for (; it != end; ++it) {
            literal l = *it;
            TRACE("unsat_core_bug", tout << "answer literal: " << l << "\n";);
            SASSERT(get_bdata(l.var()).m_assumption);
            if (!m_literal2assumption.contains(l.index())) l.neg();
            SASSERT(m_literal2assumption.contains(l.index()));
            if (!already_found_assumptions.contains(l.index())) {
                already_found_assumptions.insert(l.index());
                expr* orig_assumption = m_literal2assumption[l.index()];
                m_unsat_core.push_back(orig_assumption);
                TRACE("assumptions", tout << l << ": " << mk_pp(orig_assumption, m_manager) << "\n";);
            }
        }
        reset_assumptions();
        pop_to_base_lvl(); // undo the push_scope() performed by init_assumptions
        m_search_lvl = m_base_lvl;
        std::sort(m_unsat_core.c_ptr(), m_unsat_core.c_ptr() + m_unsat_core.size(), ast_lt_proc());
        TRACE("unsat_core_bug", tout << "unsat core:\n" << m_unsat_core << "\n";);
        validate_unsat_core();
        // theory validation of unsat core
        for (theory* th : m_theory_set) {
            lbool theory_result = th->validate_unsat_core(m_unsat_core);
            if (theory_result == l_undef) {
                return l_undef;
            }
        }
        return l_false;
    }

    /**
       \brief Make some checks before starting the search.
       Return true if succeeded.
    */
    bool context::check_preamble(bool reset_cancel) {
        if (m_manager.has_trace_stream())
            m_manager.trace_stream() << "[begin-check] " << m_scope_lvl << "\n";

        if (memory::above_high_watermark()) {
            m_last_search_failure = MEMOUT;
            return false;
        }
        reset_tmp_clauses();
        m_unsat_core.reset();
        m_stats.m_num_checks++;
        pop_to_base_lvl();
        return true;
    }

    /**
       \brief Execute some finalization code after performing the search.
    */
    lbool context::check_finalize(lbool r) {
        TRACE("after_search", display(tout << "result: " << r << "\n"););
        display_profile(verbose_stream());
        if (r == l_true && get_cancel_flag()) {
            r = l_undef;
        }
        return r;
    }

    /**
       \brief Setup the logical context based on the current set of
       asserted formulas and execute the check command.

       \remark A logical context can only be configured at scope level 0,
       and before internalizing any formulas.
    */
    lbool context::setup_and_check(bool reset_cancel) {
        if (!check_preamble(reset_cancel)) return l_undef;
        SASSERT(m_scope_lvl == 0);
        SASSERT(!m_setup.already_configured());
        setup_context(m_fparams.m_auto_config);

        expr_ref_vector theory_assumptions(m_manager);
        add_theory_assumptions(theory_assumptions);
        if (!theory_assumptions.empty()) {
            TRACE("search", tout << "Adding theory assumptions to context" << std::endl;);
            return check(theory_assumptions.size(), theory_assumptions.c_ptr(), reset_cancel, true);
        }

        internalize_assertions();
        TRACE("before_search", display(tout););
        lbool r = search();
        r = check_finalize(r);
        return r;
    }

    config_mode context::get_config_mode(bool use_static_features) const {
        if (!m_fparams.m_auto_config)
            return CFG_BASIC;
        if (use_static_features)
            return CFG_AUTO;
        return CFG_LOGIC;
    }

    void context::setup_context(bool use_static_features) {
        if (m_setup.already_configured() || inconsistent())
            return;
        m_setup(get_config_mode(use_static_features));
        setup_components();
#ifndef _EXTERNAL_RELEASE
        if (m_fparams.m_display_installed_theories) {
            std::cout << "(theories";
            for (theory* th : m_theory_set) {
                std::cout << " " << th->get_name();
            }
            std::cout << ")" << std::endl;
        }
#endif
    }

    void context::setup_components() {
        m_asserted_formulas.setup();
        m_random.set_seed(m_fparams.m_random_seed);
        m_dyn_ack_manager.setup();
        m_conflict_resolution->setup();

        if (!relevancy())
            m_fparams.m_relevancy_lemma = false;

        // setup all the theories
        for (theory* th : m_theory_set) 
            th->setup();
    }

    void context::add_theory_assumptions(expr_ref_vector & theory_assumptions) {
        for (theory* th : m_theory_set) {
            th->add_theory_assumptions(theory_assumptions);
        }
    }

    lbool context::check(unsigned num_assumptions, expr * const * assumptions, bool reset_cancel, bool already_did_theory_assumptions) {
        if (!check_preamble(reset_cancel)) return l_undef;
        SASSERT(at_base_level());
        setup_context(false);
        expr_ref_vector asms(m_manager, num_assumptions, assumptions);
        if (!already_did_theory_assumptions) add_theory_assumptions(asms);                
        // introducing proxies: if (!validate_assumptions(asms)) return l_undef;
        TRACE("unsat_core_bug", tout << asms << "\n";);        
        internalize_assertions();
        init_assumptions(asms);
        TRACE("before_search", display(tout););
        lbool r = search();
        r = mk_unsat_core(r);        
        r = check_finalize(r);
        return r;
    }

    lbool context::check(expr_ref_vector const& cube, vector<expr_ref_vector> const& clauses) {
        if (!check_preamble(true)) return l_undef;
        TRACE("before_search", display(tout););
        setup_context(false);
        expr_ref_vector asms(cube);
        add_theory_assumptions(asms);
        // introducing proxies: if (!validate_assumptions(asms)) return l_undef;
        for (auto const& clause : clauses) if (!validate_assumptions(clause)) return l_undef;
        internalize_assertions();
        init_assumptions(asms);
        for (auto const& clause : clauses) init_clause(clause);
        lbool r = search();   
        r = mk_unsat_core(r);             
        r = check_finalize(r);
        return r;           
    }

    void context::init_search() {
        for (theory* th : m_theory_set) {
            th->init_search_eh();
        }
        m_qmanager->init_search_eh();
        m_incomplete_theories.reset();
        m_num_conflicts                = 0;
        m_num_conflicts_since_restart  = 0;
        m_num_conflicts_since_lemma_gc = 0;
        m_num_restarts                 = 0;
        m_restart_threshold            = m_fparams.m_restart_initial;
        m_restart_outer_threshold      = m_fparams.m_restart_initial;
        m_agility                      = 0.0;
        m_luby_idx                     = 1;
        m_lemma_gc_threshold           = m_fparams.m_lemma_gc_initial;
        m_last_search_failure          = OK;
        m_unsat_proof                  = nullptr;
        m_unsat_core                   .reset();
        m_dyn_ack_manager              .init_search_eh();
        m_final_check_idx              = 0;
        m_phase_default                = false;
        m_case_split_queue             ->init_search_eh();
        m_next_progress_sample         = 0;
        TRACE("literal_occ", display_literal_num_occs(tout););
        m_timer.start();
    }

    void context::end_search() {
        m_case_split_queue ->end_search_eh();
    }

    void context::inc_limits() {
        if (m_num_conflicts_since_restart >= m_restart_threshold) {
            switch (m_fparams.m_restart_strategy) {
            case RS_GEOMETRIC:
                m_restart_threshold = static_cast<unsigned>(m_restart_threshold * m_fparams.m_restart_factor);
                break;
            case RS_IN_OUT_GEOMETRIC:
                m_restart_threshold = static_cast<unsigned>(m_restart_threshold * m_fparams.m_restart_factor);
                if (m_restart_threshold > m_restart_outer_threshold) {
                    m_restart_threshold = m_fparams.m_restart_initial;
                    m_restart_outer_threshold = static_cast<unsigned>(m_restart_outer_threshold * m_fparams.m_restart_factor);
                }
                break;
            case RS_LUBY:
                m_luby_idx ++;
                m_restart_threshold = static_cast<unsigned>(get_luby(m_luby_idx) * m_fparams.m_restart_initial);
                break;
            case RS_FIXED:
                break;
            case RS_ARITHMETIC:
                m_restart_threshold = static_cast<unsigned>(m_restart_threshold + m_fparams.m_restart_factor);
                break;
            default:
                break;
            }
        }
        m_num_conflicts_since_restart = 0;
    }


    lbool context::search() {
#ifndef _EXTERNAL_RELEASE
        if (m_fparams.m_abort_after_preproc) {
            exit(1);
        }
#endif
        if (m_asserted_formulas.inconsistent()) 
            return l_false;
        if (inconsistent()) {
            VERIFY(!resolve_conflict());
            return l_false;
        }
        timeit tt(get_verbosity_level() >= 100, "smt.stats");
        scoped_mk_model smk(*this);
        SASSERT(at_search_level());
        TRACE("search", display(tout); display_enodes_lbls(tout););
        TRACE("search_detail", m_asserted_formulas.display(tout););
        init_search();
        flet<bool> l(m_searching, true);
        TRACE("after_init_search", display(tout););
        IF_VERBOSE(2, verbose_stream() << "(smt.searching)\n";);
        TRACE("search_lite", tout << "searching...\n";);
        lbool    status            = l_undef;
        unsigned curr_lvl          = m_scope_lvl;

        while (true) {
            SASSERT(!inconsistent());

            status = bounded_search();
            TRACE("search_bug", tout << "status: " << status << ", inconsistent: " << inconsistent() << "\n";);
            TRACE("assigned_literals_per_lvl", display_num_assigned_literals_per_lvl(tout);
                  tout << ", num_assigned: " << m_assigned_literals.size() << "\n";);

            if (!restart(status, curr_lvl)) {
                break;
            }            
        }

        TRACE("guessed_literals",
              expr_ref_vector guessed_lits(m_manager);
              get_guessed_literals(guessed_lits);
              tout << guessed_lits << "\n";);
        end_search();
        return status;
    }

    bool context::restart(lbool& status, unsigned curr_lvl) {

        if (m_last_search_failure != OK) {
            if (status != l_false) {
                // build candidate model before returning
                mk_proto_model(status);
                // status = l_undef;
            }
            return false;
        }

        if (status == l_false) {
            return false;
        }
        if (status == l_true) {
            SASSERT(!inconsistent());
            mk_proto_model(l_true);
            // possible outcomes   DONE l_true, DONE l_undef, CONTINUE
            quantifier_manager::check_model_result cmr = m_qmanager->check_model(m_proto_model.get(), m_model_generator->get_root2value());
            if (cmr == quantifier_manager::SAT) {
                // done
                status = l_true;
                return false;
            }
            if (cmr == quantifier_manager::UNKNOWN) {
                IF_VERBOSE(2, verbose_stream() << "(smt.giveup quantifiers)\n";);
                // giving up
                m_last_search_failure = QUANTIFIERS;
                status = l_undef;
                return false;
            }
        }
        inc_limits();
        if (status == l_true || !m_fparams.m_restart_adaptive || m_agility < m_fparams.m_restart_agility_threshold) {
            SASSERT(!inconsistent());
            IF_VERBOSE(2, verbose_stream() << "(smt.restarting :propagations " << m_stats.m_num_propagations
                       << " :decisions " << m_stats.m_num_decisions
                       << " :conflicts " << m_stats.m_num_conflicts << " :restart " << m_restart_threshold;
                       if (m_fparams.m_restart_strategy == RS_IN_OUT_GEOMETRIC) {
                           verbose_stream() << " :restart-outer " << m_restart_outer_threshold;
                       }
                       if (m_fparams.m_restart_adaptive) {
                           verbose_stream() << " :agility " << m_agility;
                       }
                       verbose_stream() << ")\n");
            // execute the restart
            m_stats.m_num_restarts++;
            m_num_restarts++;
            if (m_scope_lvl > curr_lvl) {
                pop_scope(m_scope_lvl - curr_lvl);
                SASSERT(at_search_level());
            }
            for (theory* th : m_theory_set) {
                if (!inconsistent()) th->restart_eh();
            }
            TRACE("mbqi_bug_detail", tout << "before instantiating quantifiers...\n";);
            if (!inconsistent()) {
                m_qmanager->restart_eh();
            }
            if (inconsistent()) {
                VERIFY(!resolve_conflict());
                status = l_false;
                return false;
            }
            if (m_num_restarts >= m_fparams.m_restart_max) {
                status = l_undef;
                m_last_search_failure = NUM_CONFLICTS;
                return false;
            }
        }
        if (m_fparams.m_simplify_clauses)
            simplify_clauses();
        if (m_fparams.m_lemma_gc_strategy == LGC_AT_RESTART)
            del_inactive_lemmas();

        status = l_undef;
        return true;
    }

    void context::tick(unsigned & counter) const {
        counter++;
        if (counter > m_fparams.m_tick) {
            IF_VERBOSE(3, verbose_stream() << "(smt.working";
                       verbose_stream() << " :conflicts " << m_num_conflicts;
                       // verbose_stream() << " lemma avg. activity: " << get_lemma_avg_activity();
                       if (m_fparams.m_restart_adaptive)
                       verbose_stream() << " :agility " << m_agility;
                       verbose_stream() << ")" << std::endl; verbose_stream().flush(););
            TRACE("assigned_literals_per_lvl", display_num_assigned_literals_per_lvl(tout); tout << "\n";);
            counter = 0;
        }
    }

    lbool context::bounded_search() {
        unsigned counter = 0;

        TRACE("bounded_search", tout << "starting bounded search...\n";);

        while (true) {
            while (!propagate()) {
                TRACE_CODE({
                    static bool first_propagate = true;
                    if (first_propagate) {
                        first_propagate = false;
                        TRACE("after_first_propagate", display(tout););
                    }
                });

                tick(counter);

                if (!resolve_conflict())
                    return l_false;

                SASSERT(m_scope_lvl >= m_base_lvl);

                if (!inconsistent()) {
                    if (resource_limits_exceeded())
                        return l_undef;

                    if (get_cancel_flag())
                        return l_undef;

                    if (m_num_conflicts_since_restart > m_restart_threshold && m_scope_lvl - m_base_lvl > 2) {
                        TRACE("search_bug", tout << "bounded-search return undef, inconsistent: " << inconsistent() << "\n";);
                        return l_undef; // restart
                    }

                    if (m_num_conflicts > m_fparams.m_max_conflicts) {
                        TRACE("search_bug", tout << "bounded-search return undef, inconsistent: " << inconsistent() << "\n";);
                        m_last_search_failure = NUM_CONFLICTS;
                        return l_undef;
                    }
                }

                if (m_num_conflicts_since_lemma_gc > m_lemma_gc_threshold &&
                    (m_fparams.m_lemma_gc_strategy == LGC_FIXED || m_fparams.m_lemma_gc_strategy == LGC_GEOMETRIC)) {
                    del_inactive_lemmas();
                }

                m_dyn_ack_manager.propagate_eh();
                CASSERT("dyn_ack", check_clauses(m_lemmas) && check_clauses(m_aux_clauses));
            }

            if (resource_limits_exceeded() && !inconsistent()) {
                return l_undef;
            }

            if (get_cancel_flag())
                return l_undef;

            if (m_base_lvl == m_scope_lvl && m_fparams.m_simplify_clauses)
                simplify_clauses();

            if (!decide()) {
                if (inconsistent()) 
                    return l_false;
                final_check_status fcs = final_check();
                TRACE("final_check_result", tout << "fcs: " << fcs << " last_search_failure: " << m_last_search_failure << "\n";);
                switch (fcs) {
                case FC_DONE:
                    return l_true;
                case FC_CONTINUE:
                    break;
                case FC_GIVEUP:
                    return l_undef;
                }
            }

            if (resource_limits_exceeded() && !inconsistent()) {
                m_last_search_failure = RESOURCE_LIMIT;
                return l_undef;
            }
        }
    }

    bool context::resource_limits_exceeded() {
        if (m_searching) {
            // Some of the flags only make sense to check when searching.
            // For example, the timer is only started in init_search().
            if (m_last_search_failure != OK)
                return true;

            if (m_timer.ms_timeout(m_fparams.m_timeout)) {
                m_last_search_failure = TIMEOUT;
                return true;
            }

            if (m_progress_callback) {
                m_progress_callback->fast_progress_sample();
                if (m_fparams.m_progress_sampling_freq > 0 && m_timer.ms_timeout(m_next_progress_sample + 1)) {
                    m_progress_callback->slow_progress_sample();
                    m_next_progress_sample = (unsigned)(m_timer.get_seconds() * 1000) + m_fparams.m_progress_sampling_freq;
                }
            }
        }

        if (get_cancel_flag()) {
            m_last_search_failure = CANCELED;
            return true;
        }

        if (memory::above_high_watermark()) {
            m_last_search_failure = MEMOUT;
            return true;
        }

        return false;
    }

    final_check_status context::final_check() {
        TRACE("final_check", tout << "final_check inconsistent: " << inconsistent() << "\n"; display(tout); display_normalized_enodes(tout););
        CASSERT("relevancy", check_relevancy());

        
        if (m_fparams.m_model_on_final_check) {
            mk_proto_model(l_undef);
            model_pp(std::cout, *m_proto_model);
            std::cout << "END_OF_MODEL\n";
            std::cout.flush();
        }

        m_stats.m_num_final_checks++;
		TRACE("final_check_stats", tout << "m_stats.m_num_final_checks = " << m_stats.m_num_final_checks << "\n";);

        final_check_status ok = m_qmanager->final_check_eh(false);
        if (ok != FC_DONE)
            return ok;

        m_incomplete_theories.reset();

        unsigned old_idx          = m_final_check_idx;
        unsigned num_th           = m_theory_set.size();
        unsigned range            = num_th + 1;
        final_check_status result = FC_DONE;
        failure  f                = OK;

        do {
            TRACE("final_check_step", tout << "processing: " << m_final_check_idx << ", result: " << result << "\n";);
            final_check_status ok;
            if (m_final_check_idx < num_th) {
                theory * th = m_theory_set[m_final_check_idx];
                IF_VERBOSE(100, verbose_stream() << "(smt.final-check \"" << th->get_name() << "\")\n";);
                ok = th->final_check_eh();
                TRACE("final_check_step", tout << "final check '" << th->get_name() << " ok: " << ok << " inconsistent " << inconsistent() << "\n";);
                if (ok == FC_GIVEUP) {
                    f  = THEORY;
                    m_incomplete_theories.push_back(th);
                }
            }
            else {
                ok = m_qmanager->final_check_eh(true);
                TRACE("final_check_step", tout << "quantifier  ok: " << ok << " " << "inconsistent " << inconsistent() << "\n";);
            }

            m_final_check_idx = (m_final_check_idx + 1) % range;
            // IF_VERBOSE(1000, verbose_stream() << "final check status: " << ok << "\n";);

            switch (ok) {
            case FC_DONE:
                break;
            case FC_GIVEUP:
                result = FC_GIVEUP;
                break;
            case FC_CONTINUE:
                return FC_CONTINUE;
                break;
            }
        }
        while (m_final_check_idx != old_idx);

        TRACE("final_check_step", tout << "result: " << result << "\n";);

        if (can_propagate()) {
            TRACE("final_check_step", tout << "can propagate: continue...\n";);
            return FC_CONTINUE;
        }

        SASSERT(result != FC_DONE || check_th_diseq_propagation());
        TRACE("final_check_step", tout << "RESULT final_check: " << result << "\n";);
        if (result == FC_GIVEUP && f != OK)
            m_last_search_failure = f;
        return result;
    }

    void context::check_proof(proof * pr) {
        if (m_manager.proofs_enabled() && m_fparams.m_check_proof) {
            proof_checker pf(m_manager);
            expr_ref_vector side_conditions(m_manager);
            pf.check(pr, side_conditions);
        }
    }

    void context::forget_phase_of_vars_in_current_level() {
        unsigned head = m_scope_lvl == 0 ? 0 : m_scopes[m_scope_lvl - 1].m_assigned_literals_lim;
        unsigned sz   = m_assigned_literals.size();
        for (unsigned i = head; i < sz; i++) {
            literal l  = m_assigned_literals[i];
            bool_var v = l.var();
            TRACE("forget_phase", tout << "forgeting phase of l: " << l << "\n";);
            m_bdata[v].m_phase_available = false;
        }
    }

    bool context::resolve_conflict() {
        m_stats.m_num_conflicts++;
        m_num_conflicts ++;
        m_num_conflicts_since_restart ++;
        m_num_conflicts_since_lemma_gc ++;
        switch (m_conflict.get_kind()) {
        case b_justification::CLAUSE:
        case b_justification::BIN_CLAUSE:
            m_stats.m_num_sat_conflicts++;
            break;
        default:
            break;
        }
        if (m_fparams.m_phase_selection == PS_CACHING_CONSERVATIVE || m_fparams.m_phase_selection == PS_CACHING_CONSERVATIVE2)
            forget_phase_of_vars_in_current_level();
        m_atom_propagation_queue.reset();
        m_eq_propagation_queue.reset();
        m_th_eq_propagation_queue.reset();
        m_th_diseq_propagation_queue.reset();
        if (m_conflict_resolution->resolve(m_conflict, m_not_l)) {
            unsigned new_lvl = m_conflict_resolution->get_new_scope_lvl();
            unsigned num_lits = m_conflict_resolution->get_lemma_num_literals();
            literal * lits    = m_conflict_resolution->get_lemma_literals();

            SASSERT(num_lits > 0);
            unsigned conflict_lvl = get_assign_level(lits[0]);
            SASSERT(conflict_lvl <= m_scope_lvl);

            // When num_lits == 1, then the default behavior is to go
            // to base-level. If the problem has quantifiers, it may be
            // too expensive to do that, since all instances will need to
            // be recreated. If that is the case, I store the assertions in
            // a special vector and keep reasserting whenever I backtrack.
            // Moreover, I backtrack only one level.
            bool delay_forced_restart =
                m_fparams.m_delay_units &&
                internalized_quantifiers() &&
                num_lits == 1 &&
                conflict_lvl > m_search_lvl + 1 &&
                !m_manager.proofs_enabled() &&
                m_units_to_reassert.size() < m_fparams.m_delay_units_threshold;
            if (delay_forced_restart) {
                new_lvl = conflict_lvl - 1;
            }

            // Some of the literals/enodes of the conflict clause will be destroyed during
            // backtracking, and will need to be recreated. However, I want to keep
            // the generation number for enodes that are going to be recreated. See
            // comment in cache_generation(unsigned).
            if (m_conflict_resolution->get_lemma_intern_lvl() > new_lvl)
                cache_generation(num_lits, lits, new_lvl);

            SASSERT(new_lvl < m_scope_lvl);
            TRACE("resolve_conflict_bug",
                  tout << "m_scope_lvl: " << m_scope_lvl << ", new_lvl: " << new_lvl << ", lemma_intern_lvl: " << m_conflict_resolution->get_lemma_intern_lvl() << "\n";
                  tout << "num_lits: " << num_lits << "\n";
                  for (unsigned i = 0; i < num_lits; i++) {
                      literal l = lits[i];
                      tout << l << " ";
                      display_literal(tout, l);
                      tout << ", ilvl: " << get_intern_level(l.var()) << "\n"
                           << mk_pp(bool_var2expr(l.var()), m_manager) << "\n";
                  });

            if (m_manager.has_trace_stream()) {
                m_manager.trace_stream() << "[conflict] ";
                display_literals(m_manager.trace_stream(), num_lits, lits);
                m_manager.trace_stream() << "\n";
            }

#ifdef Z3DEBUG
            expr_ref_vector expr_lits(m_manager);
            svector<bool>   expr_signs;
            for (unsigned i = 0; i < num_lits; i++) {
                literal l = lits[i];
                if (get_assignment(l) != l_false) {
                    std::cout << l << " " << get_assignment(l) << "\n";
                }
                SASSERT(get_assignment(l) == l_false);
                expr_lits.push_back(bool_var2expr(l.var()));
                expr_signs.push_back(l.sign());
            }
#endif
            proof * pr = nullptr;
            if (m_manager.proofs_enabled()) {
                pr = m_conflict_resolution->get_lemma_proof();
                // check_proof(pr);
                TRACE("context_proof", tout << mk_ll_pp(pr, m_manager););
                TRACE("context_proof_hack",
                      static ast_mark visited;
                      ast_ll_pp(tout, m_manager, pr, visited););
            }
            // I invoke pop_scope_core instead of pop_scope because I don't want
            // to reset cached generations... I need them to rebuild the literals
            // of the new conflict clause.
            if (relevancy()) record_relevancy(num_lits, lits);
            unsigned num_bool_vars = pop_scope_core(m_scope_lvl - new_lvl);
            SASSERT(m_scope_lvl == new_lvl);
            // the logical context may still be in conflict after
            // clauses are reinitialized in pop_scope.
            if (m_conflict_resolution->get_lemma_intern_lvl() > m_scope_lvl) {
                expr * * atoms         = m_conflict_resolution->get_lemma_atoms();
                for (unsigned i = 0; i < num_lits; i++) {
                    literal l   = lits[i];
                    if (l.var() >= static_cast<int>(num_bool_vars)) {
                        // This boolean variable was deleted during backtracking, it need to be recreated.
                        // Remark: atom may be a negative literal (not a). Z3 creates Boolean variables for not-gates that
                        // are nested in terms. Example: let f be a uninterpreted function from Bool -> Int.
                        // Then, given the term (f (not a)), Z3 will create a boolean variable for (not a) when internalizing (f (not a)).
                        expr * atom     = atoms[i];
                        internalize(atom, true);
                        // If atom is actually a negative literal (not a), then get_bool_var will return return null_bool_var.
                        // Thus, we must use get_literal instead. This was a bug/crash in Z3 <= 4.0
                        literal new_l = get_literal(atom);
                        if (l.sign())
                            new_l.neg();
                        // For reference, here is the buggy version
                        // BEGIN BUGGY VERSION
                        // bool_var v = get_bool_var(atom);
                        // CTRACE("resolve_conflict_crash", v == null_bool_var, tout << mk_ismt2_pp(atom, m_manager) << "\n";);
                        // SASSERT(v != null_bool_var);
                        // literal new_l   = literal(v, l.sign());
                        // END BUGGY VERSION
                        lits[i]         = new_l;
                    }
                }
            }
            if (relevancy()) restore_relevancy(num_lits, lits);
            // Resetting the cache manually because I did not invoke pop_scope, but pop_scope_core
            reset_cache_generation();
            TRACE("resolve_conflict_bug",
                  tout << "AFTER m_scope_lvl: " << m_scope_lvl << ", new_lvl: " << new_lvl << ", lemma_intern_lvl: " <<
                  m_conflict_resolution->get_lemma_intern_lvl() << "\n";
                  tout << "num_lits: " << num_lits << "\n";
                  for (unsigned i = 0; i < num_lits; i++) {
                      literal l = lits[i];
                      tout << l << " ";
                      display_literal(tout, l);
                      tout << ", ilvl: " << get_intern_level(l.var()) << "\n"
                           << mk_pp(bool_var2expr(l.var()), m_manager) << "\n";
                  });
#ifdef Z3DEBUG
            for (unsigned i = 0; i < num_lits; i++) {
                literal l = lits[i];
                if (expr_signs[i] != l.sign()) {
                    expr* real_atom;
                    VERIFY(m_manager.is_not(expr_lits.get(i), real_atom));
                    // the sign must have flipped when internalizing
                    CTRACE("resolve_conflict_bug", real_atom != bool_var2expr(l.var()), tout << mk_pp(real_atom, m_manager) << "\n" << mk_pp(bool_var2expr(l.var()), m_manager) << "\n";);
                    SASSERT(real_atom == bool_var2expr(l.var()));
                }
                else {
                    SASSERT(expr_lits.get(i) == bool_var2expr(l.var()));
                }
            }
#endif
            justification * js = nullptr;
            if (m_manager.proofs_enabled()) {
                js = alloc(justification_proof_wrapper, *this, pr, false);
            }
#if 0
            {
                static unsigned counter = 0;
                static uint64_t total = 0;
                static unsigned max = 0;
                counter++;
                total += num_lits;
                if (num_lits > max) {
                    max = num_lits;
                }
                if (counter % 1000 == 0) {
                    verbose_stream() << "[sat] avg. clause size: " << ((double) total/(double) counter) << ", max: " << max << std::endl;
                    for (unsigned i = 0; i < num_lits; i++) {
                        literal l = lits[i];
                        verbose_stream() << l.sign() << " " << mk_pp(bool_var2expr(l.var()), m_manager) << "\n";
                    }
                }
            }
#endif
            mk_clause(num_lits, lits, js, CLS_LEARNED);
            if (delay_forced_restart) {
                SASSERT(num_lits == 1);
                expr * unit     = bool_var2expr(lits[0].var());
                bool unit_sign  = lits[0].sign();
                m_units_to_reassert.push_back(unit);
                m_units_to_reassert_sign.push_back(unit_sign);
                TRACE("reassert_units", tout << "asserting #" << unit->get_id() << " " << unit_sign << " @ " << m_scope_lvl << "\n";);
            }

            m_conflict_resolution->release_lemma_atoms();
            TRACE("context_lemma", tout << "new lemma: ";
                  literal_vector v(num_lits, lits);
                  std::sort(v.begin(), v.end());
                  for (unsigned i = 0; i < num_lits; i++) {
                      display_literal(tout, v[i]);
                      tout << "\n";
                      v[i].display(tout, m_manager, m_bool_var2expr.c_ptr());
                      tout << "\n\n";
                  }
                  tout << "\n";);
            decay_bvar_activity();
            update_phase_cache_counter();
            return true;
        }
        else if (m_manager.proofs_enabled()) {
            m_unsat_proof = m_conflict_resolution->get_lemma_proof();
            check_proof(m_unsat_proof);
        }
        return false;
    }

    /*
      \brief we record and restore relevancy information for literals in conflict clauses.
      A literal may have been marked relevant within the scope that gets popped during
      conflict resolution. In this case, the literal is no longer marked as relevant after
      the pop. This can cause quantifier instantiation to miss relevant triggers and thereby
      cause incmpleteness.
     */
    void context::record_relevancy(unsigned n, literal const* lits) {
        m_relevant_conflict_literals.reset();
        for (unsigned i = 0; i < n; ++i) {
            m_relevant_conflict_literals.push_back(is_relevant(lits[i]));
        }
    }

    void context::restore_relevancy(unsigned n, literal const* lits) {
        for (unsigned i = 0; i < n; ++i) {
            if (m_relevant_conflict_literals[i] && !is_relevant(lits[i])) {
                mark_as_relevant(lits[i]);
            }
        }
    }

    void context::get_relevant_labels(expr* cnstr, buffer<symbol> & result) {
        if (m_fparams.m_check_at_labels) {
            check_at_labels checker(m_manager);
            if (cnstr && !checker.check(cnstr)) {
                warning_msg("Boogie generated formula that can require multiple '@' labels in a counter-example");
            }
            else {
                unsigned nf = m_asserted_formulas.get_num_formulas();
                for (unsigned i = 0; i < nf; ++i) {
                    expr* fml = m_asserted_formulas.get_formula(i);
                    if (!checker.check(fml)) {
                        warning_msg("Boogie generated formula that can require multiple '@' labels in a counter-example");
                        break;
                    }
                }
            }
        }

        SASSERT(!inconsistent());
        for (expr * curr : m_b_internalized_stack) { 
            if (is_relevant(curr) && get_assignment(curr) == l_true) {
                // if curr is a label literal, then its tags will be copied to result.
                m_manager.is_label_lit(curr, result);
            }
        }
    }

    /**
       \brief Collect relevant literals that may be used to block the current assignment.
       If at_lbls is true, then only labels that contains '@' are considered. (This is a hack for Boogie).
       This hack is also available in the Simplify theorem prover.
    */
    void context::get_relevant_labeled_literals(bool at_lbls, expr_ref_vector & result) {
        SASSERT(!inconsistent());
        buffer<symbol> lbls;
        for (expr * curr : m_b_internalized_stack) {
            if (is_relevant(curr) && get_assignment(curr) == l_true) {
                lbls.reset();
                if (m_manager.is_label_lit(curr, lbls)) {
                    bool include = false;
                    if (at_lbls) {
                        // include if there is a label with the '@' sign.
                        for (symbol const& s : lbls) {
                            if (s.contains('@')) {
                                include = true;
                                break;
                            }
                        }
                    }
                    else {
                        include = true;
                    }
                    if (include)
                        result.push_back(curr);
                }
            }
        }
    }

    /**
       \brief Store in result the (relevant) literal assigned by the
       logical context.
    */
    void context::get_relevant_literals(expr_ref_vector & result) {
        SASSERT(!inconsistent());
        unsigned sz = m_b_internalized_stack.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * curr = m_b_internalized_stack.get(i);
            if (is_relevant(curr)) {
                switch (get_assignment(curr)) {
                case l_true:
                    result.push_back(curr);
                    break;
                case l_false:
                    result.push_back(m_manager.mk_not(curr));
                    break;
                default:
                    break;
                }
            }
        }
    }

    /**
       \brief Store the current set of guessed literals (i.e., case splits).
    */
    void context::get_guessed_literals(expr_ref_vector & result) {
        // The literals between [m_base_lvl, m_search_lvl) are not guesses but assumptions.
        SASSERT(m_base_lvl <= m_scopes.size());
        if (m_search_lvl == m_scopes.size()) {
            // do nothing... there are guesses...
        }
        for (unsigned i = m_search_lvl; i < m_scope_lvl; i++) {
            // This method assumes the first literal assigned in a non base scope level is a guess.
            scope & s          = m_scopes[i];
            unsigned guess_idx = s.m_assigned_literals_lim;
            literal guess      = m_assigned_literals[guess_idx];
            SASSERT(get_justification(guess.var()).get_kind() == b_justification::AXIOM);
            expr_ref lit(m_manager);
            literal2expr(guess, lit);
            result.push_back(std::move(lit));
        }
    }

    /**
       \brief Undo object for bool var m_true_first field update.
    */
    class set_true_first_trail : public trail<context> {
        bool_var m_var;
    public:
        set_true_first_trail(bool_var v):m_var(v) {}
        void undo(context & ctx) override {
            ctx.m_bdata[m_var].reset_true_first_flag();
        }
    };

    void context::set_true_first_flag(bool_var v) {
        push_trail(set_true_first_trail(v));
        bool_var_data & d = m_bdata[v];
        d.set_true_first_flag();
    }

    bool context::assume_eq(enode * lhs, enode * rhs) {
        if (lhs->get_root() == rhs->get_root())
            return false; // it is not necessary to assume the eq.
        expr * _lhs = lhs->get_owner();
        expr * _rhs = rhs->get_owner();
        expr * eq = mk_eq_atom(_lhs, _rhs);
        TRACE("assume_eq", tout << "creating interface eq:\n" << mk_pp(eq, m_manager) << "\n";);
        if (m_manager.is_false(eq)) {
            return false;
        }
        bool r    = false;
        if (!b_internalized(eq)) {
            // I do not invoke internalize(eq, true), because I want to
            // mark the try_true_first flag before invoking theory::internalize_eq_eh.
            // Reason: Theories like arithmetic should be able to know if the try_true_first flag is
            // marked or not. They use this information to also mark auxiliary atoms such as:
            //  (<= (- x y) 0)
            //  (>= (- y x) 0)
            // for the new equality atom (= x y).
            if (m_manager.is_eq(eq)) {
                internalize_formula_core(to_app(eq), true);
                bool_var v        = get_bool_var(eq);
                bool_var_data & d = get_bdata(v);
                d.set_eq_flag();
                set_true_first_flag(v);
                sort * s    = m_manager.get_sort(to_app(eq)->get_arg(0));
                theory * th = m_theories.get_plugin(s->get_family_id());
                if (th)
                    th->internalize_eq_eh(to_app(eq), v);
            }
            else {
                internalize(eq, true);
            }
            r = true;
            m_stats.m_num_interface_eqs++;
            TRACE("assume_eq", tout << "new internalization.\n";);
        }
        bool_var v        = get_bool_var(eq);
        bool_var_data & d = m_bdata[v];
        if (!d.try_true_first()) {
            set_true_first_flag(v);
            r       = true;
            TRACE("assume_eq", tout << "marked as ieq.\n";);
        }
        if (get_assignment(v) == l_undef) {
            TRACE("assume_eq", tout << "variable is unassigned.\n";);
            r       = true;
        }
        if (relevancy()) {
            if (!is_relevant(eq)) {
                TRACE("assume_eq", tout << "marking eq as relevant.\n";);
                mark_as_relevant(eq);
                r   = true;
            }
        }
        TRACE("assume_eq", tout << "variable value: " << get_assignment(v) << "\n";);
        TRACE("assume_eq", tout << "assume_eq result: " << r << "\n";);
        return r;
    }

    bool context::is_shared(enode * n) const {
        n = n->get_root();
        unsigned num_th_vars = n->get_num_th_vars();
        if (m_manager.is_ite(n->get_owner())) {
            return true;
        }
        switch (num_th_vars) {
        case 0: {
            return false;
        }
        case 1: {
            if (m_qmanager->is_shared(n)) {
                return true;
            }

            // the variabe is shared if the equivalence class of n
            // contains a parent application.

            theory_var_list * l = n->get_th_var_list();
            theory_id th_id     = l->get_th_id();

            for (enode * parent : enode::parents(n)) {
                family_id fid = parent->get_owner()->get_family_id();
                if (fid != th_id && fid != m_manager.get_basic_family_id()) {
                    TRACE("is_shared", tout << mk_pp(n->get_owner(), m_manager) << "\nis shared because of:\n" << mk_pp(parent->get_owner(), m_manager) << "\n";);
                    return true;
                }
            }

            // Some theories implement families of theories. Examples:
            // Arrays and Tuples.  For example, array theory is a
            // parametric theory, that is, it implements several theories:
            // (array int int), (array int (array int int)), ...
            //
            // Example:
            //
            // a : (array int int)
            // b : (array int int)
            // x : int
            // y : int
            // v : int
            // w : int
            // A : (array (array int int) int)
            //
            // assert (= b (store a x v))
            // assert (= b (store a y w))
            // assert (not (= x y))
            // assert (not (select A a))
            // assert (not (select A b))
            // check
            //
            // In the example above, 'a' and 'b' are shared variables between
            // the theories of (array int int) and (array (array int int) int).
            // Remark: The inconsistency is not going to be detected if they are
            // not marked as shared.
            return get_theory(th_id)->is_shared(l->get_th_var());
        }
        default:
            return true;
        }
    }

    bool context::get_value(enode * n, expr_ref & value) {
        sort * s      = m_manager.get_sort(n->get_owner());
        family_id fid = s->get_family_id();
        theory * th   = get_theory(fid);
        if (th == nullptr)
            return false;
        return th->get_value(n, value);
    }

    bool context::update_model(bool refinalize) {
        final_check_status fcs = FC_DONE;
        if (refinalize) {
            fcs = final_check();
        }
        TRACE("opt", tout << (refinalize?"refinalize":"no-op") << " " << fcs << "\n";);
        if (fcs == FC_DONE) {
            mk_proto_model(l_true);
            m_model = m_proto_model->mk_model();
            add_rec_funs_to_model();
        }

        return fcs == FC_DONE;
    }

    void context::mk_proto_model(lbool r) {
        TRACE("get_model",
              display(tout);
              display_normalized_enodes(tout);
              display_enodes_lbls(tout);
              m_fingerprints.display(tout);
              );
        failure fl = get_last_search_failure();
        if (fl == MEMOUT || fl == CANCELED || fl == TIMEOUT || fl == NUM_CONFLICTS || fl == RESOURCE_LIMIT) {
            TRACE("get_model", tout << "last search failure: " << fl << "\n";);
        }
        else if (m_fparams.m_model || m_fparams.m_model_on_final_check || m_qmanager->model_based()) {
            m_model_generator->reset();
            m_proto_model = m_model_generator->mk_model();
            m_qmanager->adjust_model(m_proto_model.get());
            TRACE("mbqi_bug", tout << "before complete_partial_funcs:\n"; model_pp(tout, *m_proto_model););
            m_proto_model->complete_partial_funcs(false);
            TRACE("mbqi_bug", tout << "before cleanup:\n"; model_pp(tout, *m_proto_model););
            m_proto_model->cleanup();
            if (m_fparams.m_model_compact)
                m_proto_model->compress();
            TRACE("mbqi_bug", tout << "after cleanup:\n"; model_pp(tout, *m_proto_model););
            IF_VERBOSE(11, model_pp(verbose_stream(), *m_proto_model););
        }
    }

    proof * context::get_proof() {
        if (!m_manager.proofs_enabled())
            return nullptr;
        return m_unsat_proof;
    }

    void context::get_model(model_ref & m) const {
        if (inconsistent())
            m = nullptr;
        else
            m = const_cast<model*>(m_model.get());
    }

    void context::get_proto_model(proto_model_ref & m) const {
        m = const_cast<proto_model*>(m_proto_model.get());
    }

    failure context::get_last_search_failure() const {
        return m_last_search_failure;
    }

    void context::add_rec_funs_to_model() {
        ast_manager& m = m_manager;
        SASSERT(m_model);
        for (unsigned i = 0; !get_cancel_flag() && i < m_asserted_formulas.get_num_formulas(); ++i) {
            expr* e = m_asserted_formulas.get_formula(i);
            if (is_quantifier(e)) {
                quantifier* q = to_quantifier(e);
                if (!m.is_rec_fun_def(q)) continue;
                TRACE("context", tout << mk_pp(e, m) << "\n";);
                SASSERT(q->get_num_patterns() == 2);
                expr* fn = to_app(q->get_pattern(0))->get_arg(0);
                expr* body = to_app(q->get_pattern(1))->get_arg(0);
                SASSERT(is_app(fn));
                // reverse argument order so that variable 0 starts at the beginning.
                expr_ref_vector subst(m);
                unsigned idx = 0;
                for (expr* arg : *to_app(fn)) {
                    subst.push_back(m.mk_var(idx++, m.get_sort(arg)));
                }
                expr_ref bodyr(m);
                var_subst sub(m, true);
                TRACE("context", tout << expr_ref(q, m) << " " << subst << "\n";);
                bodyr = sub(body, subst.size(), subst.c_ptr());
                func_decl* f = to_app(fn)->get_decl();
                func_interp* fi = alloc(func_interp, m, f->get_arity());
                fi->set_else(bodyr);
                m_model->register_decl(f, fi);
            }
        }
    }

};


#ifdef Z3DEBUG
void pp(smt::context & c) {
    c.display(std::cout);
}
#endif
