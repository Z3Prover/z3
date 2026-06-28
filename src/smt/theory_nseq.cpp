/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_nseq.cpp

Abstract:

    ZIPT string solver theory for Z3.
    Implementation of theory_nseq.

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#include "smt/theory_nseq.h"
#include "smt/smt_context.h"
#include "smt/smt_justification.h"
#include "util/statistics.h"
#include "util/trail.h"

#include <stack>

namespace smt {

    theory_nseq::theory_nseq(context& ctx) :
        theory(ctx, ctx.get_manager().mk_family_id("seq")),
        m_seq(m),
        m_autil(m), 
        m_th_rewriter(m),
        m_rewriter(m),
        m_arith_value(m),
        m_egraph(m),
        m_sg(m, m_egraph),
        m_length_solver(m),
        m_context_solver(ctx, [this](expr* e1, expr* e2) { m_axioms.diseq_axiom(e1, e2); }),
        m_nielsen(m_sg, m_length_solver, m_context_solver),
        m_axioms(m_th_rewriter),
        m_regex(m_sg),
        m_model(m, ctx, m_seq, m_rewriter, m_sg),
        m_relevant_lengths(m)
    {
        std::function<void(expr_ref_vector const&)> add_clause =
            [&](expr_ref_vector const &clause) {
            literal_vector lits;
            for (auto const &e : clause) {
                auto lit = mk_literal(e);
                if (lit == false_literal)
                    continue;
                if (lit == true_literal)
                    return;
                if (ctx.get_assignment(lit) == l_true)
                    return;
                ctx.mark_as_relevant(lit);
                lits.push_back(lit);
            }
            // TODO - add validation, trace axioms
            ctx.mk_th_axiom(get_id(), lits.size(), lits.data());
        };
        std::function < void(expr* e)> set_phase = [&](expr* e) {
            literal lit = mk_literal(e);
            ctx.force_phase(lit);
        };
        std::function < void(void)> ensure_digit_axiom = [this, add_clause]() {
            if (!m_digits_initialized) {
                for (unsigned i = 0; i < 10; ++i) {
                    expr_ref cnst(m_seq.mk_char('0' + i), m);
                    expr_ref_vector clause(m);
                    clause.push_back(m.mk_eq(m_axioms.sk().mk_digit2int(cnst), m_autil.mk_int(i)));
                    add_clause(clause);
                }
                get_context().push_trail(value_trail<bool>(m_digits_initialized));
                m_digits_initialized = true;
            }
        };
        std::function<void(expr *)> mark_no_diseq = [&](expr *e) { 
            m_no_diseq_set.insert(e);
            ctx.push_trail(insert_obj_trail(m_no_diseq_set, e));
        };
        m_axioms.set_add_clause(add_clause);
        m_axioms.set_phase(set_phase);
        m_axioms.set_ensure_digits(ensure_digit_axiom);
        m_axioms.set_mark_no_diseq(mark_no_diseq);

        m_context_solver.m_should_internalize = true; // delete this if using internalize as fallback
       
    }

    // -----------------------------------------------------------------------
    // Initialization
    // -----------------------------------------------------------------------

    void theory_nseq::init() {
        m_arith_value.init(&get_context());
    }

    // -----------------------------------------------------------------------
    // Internalization
    // -----------------------------------------------------------------------

    bool theory_nseq::internalize_atom(app* atom, bool /*gate_ctx*/) {
        // std::cout << "internalize_atom: " << mk_pp(atom, m) << std::endl;
        // str.in_re atoms are boolean predicates: register as bool_var
        // so that assign_eh fires when the SAT solver assigns them.
        // Following theory_seq: create a bool_var directly without an enode
        // for the str.in_re predicate (avoids needing to internalize the regex arg).
        if (m_seq.str.is_in_re(atom)) {
            expr* str_arg = atom->get_arg(0);
            mk_var(ensure_enode(str_arg));
            if (!ctx.b_internalized(atom)) {
                bool_var bv = ctx.mk_bool_var(atom);
                ctx.set_var_theory(bv, get_id());
                ctx.mark_as_relevant(bv);
            }
            get_snode(str_arg);
            return true;
        }
        return internalize_term(atom);
    }

    theory_var theory_nseq::mk_var(enode* n) {
        expr* o = n->get_expr();
        if (!m_seq.is_seq(o) && !m_seq.is_re(o) && !m_seq.str.is_nth_u(o))
            return null_theory_var;
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        theory_var v = theory::mk_var(n);
        get_context().attach_th_var(n, this, v);
        get_context().mark_as_relevant(n);
        return v;
    }

    bool theory_nseq::internalize_term(app* term) {
        // std::cout << "internalize_term: " << mk_pp(term, m) << std::endl;
        // ensure ALL children are internalized (following theory_seq pattern)
        for (auto arg : *term) {
            mk_var(ensure_enode(arg));
        }

        if (ctx.e_internalized(term)) {
            mk_var(ctx.get_enode(term));
            return true;
        }

        if (m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.mark_as_relevant(bv);
        }

        enode* en;
        if (ctx.e_internalized(term))
            en = ctx.get_enode(term);
        else
            en = ctx.mk_enode(term, false, m.is_bool(term), true);
        mk_var(en);

        // register in our private sgraph
        get_snode(term);

        if (m_seq.is_seq(term) && m_axioms.sk().is_skolem(term))
            ensure_length_var(term);

        // track higher-order terms for lazy unfolding
        expr* ho_f = nullptr, *ho_s = nullptr, *ho_b = nullptr, *ho_i = nullptr;
        if (m_seq.str.is_map(term, ho_f, ho_s) ||
            m_seq.str.is_mapi(term, ho_f, ho_i, ho_s) ||
            m_seq.str.is_foldl(term, ho_f, ho_b, ho_s) ||
            m_seq.str.is_foldli(term, ho_f, ho_i, ho_b, ho_s)) {
            ctx.push_trail(restore_vector(m_ho_terms));
            m_ho_terms.push_back(term);
            ensure_length_var(ho_s);
        }
        expr* v;
        if (m_seq.str.is_length(term, v)) {
            ctx.push_trail(restore_vector(m_relevant_lengths));
            m_relevant_lengths.push_back(term);
        }

        return true;
    }

    void theory_nseq::apply_sort_cnstr(enode *n, sort *s) {
        mk_var(n);
    }

    // -----------------------------------------------------------------------
    // Equality / disequality notifications
    // -----------------------------------------------------------------------

    void theory_nseq::new_eq_eh(theory_var v1, theory_var v2) {
        try {
            auto n1 = get_enode(v1);
            auto n2 = get_enode(v2);
            auto e1 = n1->get_expr();
            auto e2 = n2->get_expr();
            TRACE(seq, tout << mk_pp(e1, m) << " == " << mk_pp(e2, m) << "\n");
            //std::cout << mk_pp(e1, m) << " == " << mk_pp(e2, m) << std::endl;
            if (m_seq.is_re(e1)) {
                expr_ref s(m);
                auto r = m_rewriter.mk_symmetric_diff(e1, e2);
                switch (m_rewriter.some_seq_in_re(r, s)) {
                case l_false:
                    // regexes are equivalent: nothing to do
                    return;
                case l_true: {
                    // regexes are disjoint: conflict
                    enode_pair_vector eqs;
                    eqs.push_back({n1, n2});
                    set_conflict(eqs);
                    return;
                }
                default: break;
                }
                push_unhandled_pred();
                return;
            }
            if (!m_seq.is_seq(e1))
                return;
            euf::snode const* s1 = get_snode(e1);
            euf::snode const* s2 = get_snode(e2);
            seq::dep_tracker dep = nullptr;
            ctx.push_trail(restore_vector(m_prop_queue));
            m_prop_queue.push_back(eq_item(s1, s2, get_enode(v1), get_enode(v2), dep));
            m_last_constraint_added = ctx.get_scope_level();
            m_can_hot_restart = false;
            ++m_eager_dirty;
        }
        catch(const std::exception&) {
#ifdef Z3DEBUG
            std::string dot = m_nielsen.to_dot();
#endif
            throw;
        }
    }

    void theory_nseq::new_diseq_eh(theory_var v1, theory_var v2) {
        auto n1 = get_enode(v1);
        auto n2 = get_enode(v2);
        auto e1 = n1->get_expr();
        auto e2 = n2->get_expr();
        TRACE(seq, tout << mk_pp(e1, m) << " != " << mk_pp(e2, m) << "\n");
        if (m_seq.is_re(e1)) {
            expr_ref s(m);
            auto r = m_rewriter.mk_symmetric_diff(e1, e2);            
            switch (m_rewriter.some_seq_in_re(r, s)) {
            case l_false: {
                enode_pair_vector eqs;
                const auto lit = mk_eq(e1, e2, false);
                literal_vector lits;
                lits.push_back(~lit);
                set_conflict(eqs, lits);
                break;
            }
            case l_true: 
                // the regexes are different
                break;
            case l_undef:                
                push_unhandled_pred();
                break;
            }
        }
        else if (m_seq.is_seq(e1) && !m_no_diseq_set.contains(e1) && !m_no_diseq_set.contains(e2)) {
            if (get_fparams().m_nseq_axiomatize_diseq)
                m_axioms.diseq_axiom(e1, e2);
            else {
                euf::snode const* s1 = get_snode(e1);
                euf::snode const* s2 = get_snode(e2);
                const seq::dep_tracker dep = nullptr;
                ctx.push_trail(restore_vector(m_prop_queue));
                const expr_ref eq_expr(m.mk_eq(e1, e2), m);
                m_prop_queue.push_back(deq_item(s1, s2, ~ctx.get_literal(eq_expr), dep));
                m_last_constraint_added = ctx.get_scope_level();
                m_can_hot_restart = false;
                ++m_eager_dirty;
            }
        }
        else
            ;
    }

    // -----------------------------------------------------------------------
    // Boolean assignment notification
    // -----------------------------------------------------------------------

    void theory_nseq::assign_eh(const bool_var v, const bool is_true) {
        try {
            expr* e = ctx.bool_var2expr(v);
            const literal lit(v, !is_true);
            //std::cout << "assigned [" << lit << "] " << mk_pp(e, m) << " = " << is_true << std::endl;
            expr *s = nullptr, *re = nullptr, *a = nullptr, *b = nullptr;
            TRACE(seq, tout << (is_true ? "" : "¬") << mk_bounded_pp(e, m, 3) << "\n";);
            if (m_seq.str.is_in_re(e, s, re)) {
                euf::snode const* sn_str = get_snode(s);
                euf::snode const* sn_re  = get_snode(re);
                const seq::dep_tracker dep = nullptr;
                if (is_true) {
                    ctx.push_trail(restore_vector(m_prop_queue));
                    m_prop_queue.push_back(mem_item(sn_str, sn_re, lit, dep));
                    m_last_constraint_added = ctx.get_scope_level();
                    m_can_hot_restart = false;
                    ++m_eager_dirty;
                }
                else {
                    // ¬(str ∈ R)  ≡  str ∈ complement(R): store as a positive membership
                    // so the Nielsen graph sees it uniformly; the original negative literal
                    // is kept in mem_source for conflict reporting.
                    const expr_ref re_compl(m_seq.re.mk_complement(re), m);
                    euf::snode const* sn_re_compl = get_snode(re_compl.get());
                    ctx.push_trail(restore_vector(m_prop_queue));
                    m_prop_queue.push_back(mem_item(sn_str, sn_re_compl, lit, dep));
                    m_last_constraint_added = ctx.get_scope_level();
                    m_can_hot_restart = false;
                    ++m_eager_dirty;
                }
            }
            else if (m_seq.str.is_prefix(e)) {
                zstring str;
                if (m_seq.str.is_string(to_app(e)->get_arg(0), str)) {
                    // prefix(u, v) with u const => v \in u \Sigma^*
                    const expr_ref pre(m_seq.re.mk_in_re(to_app(e)->get_arg(1), m_seq.re.mk_concat(
                        m_seq.re.mk_to_re(to_app(e)->get_arg(0)),
                        m_seq.re.mk_full_seq(m_seq.re.mk_re(to_app(e)->get_arg(0)->get_sort()))
                        )), m);
                    ctx.internalize(pre, false);
                    literal l = ctx.get_literal(pre);
                    if (!is_true)
                        l = ~l;
                    ctx.mk_th_axiom(get_id(), ~lit, l);
                    return;
                }
                if (is_true)
                    m_axioms.prefix_true_axiom(e);
                else
                    m_axioms.prefix_axiom(e);
            }
            else if (m_seq.str.is_suffix(e)) {
                zstring str;
                if (m_seq.str.is_string(to_app(e)->get_arg(0), str)) {
                    // suffix(u, v) with u const => v \in \Sigma* u
                    const expr_ref suff(m_seq.re.mk_in_re(to_app(e)->get_arg(1), m_seq.re.mk_concat(
                        m_seq.re.mk_full_seq(m_seq.re.mk_re(to_app(e)->get_arg(0)->get_sort())),
                        m_seq.re.mk_to_re(to_app(e)->get_arg(0))
                        )), m);
                    ctx.internalize(suff, false);
                    literal l = ctx.get_literal(suff);
                    if (!is_true)
                        l = ~l;
                    ctx.mk_th_axiom(get_id(), ~lit, l);
                    return;
                }
                if (is_true)
                    m_axioms.suffix_true_axiom(e);
                else
                    m_axioms.suffix_axiom(e);
            }
            else if (m_seq.str.is_contains(e)) {
                zstring str;
                if (m_seq.str.is_string(to_app(e)->get_arg(1), str)) {
                    // contains(u, v) with v const => u \in \Sigma* v \Sigma^*
                    sort* re_sort = m_seq.re.mk_re(to_app(e)->get_arg(0)->get_sort());
                    expr* all = m_seq.re.mk_full_seq(re_sort);
                    const expr_ref con(m_seq.re.mk_in_re(to_app(e)->get_arg(0), m_seq.re.mk_concat(
                        all,
                        m_seq.re.mk_concat(
                            m_seq.re.mk_to_re(to_app(e)->get_arg(1)), all)
                    )), m);
                    ctx.internalize(con, false);
                    literal l = ctx.get_literal(con);
                    if (!is_true)
                        l = ~l;
                    ctx.mk_th_axiom(get_id(), ~lit, l);
                    return;
                }
                if (is_true)
                    m_axioms.contains_true_axiom(e);
                else
                    m_axioms.not_contains_axiom(e);
            }
            else if (m_seq.str.is_lt(e) || m_seq.str.is_le(e)) {
                // axioms added via relevant_eh → dequeue_axiom
            }
            else if (m_axioms.sk().is_eq(e, a, b) && is_true) {
                enode* n1 = ensure_enode(a);
                enode* n2 = ensure_enode(b);
                if (n1->get_root() != n2->get_root()) {
                    const auto v1 = mk_var(n1);
                    const auto v2 = mk_var(n2);
                    const literal l(v, false);
                    ctx.mark_as_relevant(n1);
                    ctx.mark_as_relevant(n2);
                    TRACE(seq, tout << "is-eq " << mk_pp(a, m) << " == " << mk_pp(b, m) << "\n");
                    justification* js = ctx.mk_justification(
                        ext_theory_eq_propagation_justification(
                            get_id(), ctx, 1, &l, 0, nullptr, n1, n2));
                    ctx.assign_eq(n1, n2, eq_justification(js));
                    new_eq_eh(v1, v2);
                }
            }
            else if (m_seq.is_skolem(e) ||
                     m_seq.str.is_nth_i(e) ||
                     m_seq.str.is_nth_u(e) ||
                     m_seq.str.is_is_digit(e) ||
                     m_seq.str.is_foldl(e) ||
                     m_seq.str.is_foldli(e)) {
                // no-op: handled by other mechanisms
                     }
            else if (is_app(e) && to_app(e)->get_family_id() == m_seq.get_family_id())
                push_unhandled_pred();
        }
        catch(const std::exception&) {
#ifdef Z3DEBUG
            std::string dot = m_nielsen.to_dot();
#endif
            throw;
        }
    }

    // -----------------------------------------------------------------------
    // Scope management
    // -----------------------------------------------------------------------

    void theory_nseq::push_scope_eh() {
        theory::push_scope_eh();
        m_sg.push();
        
    }

    void theory_nseq::pop_scope_eh(unsigned num_scopes) {
        try {
            theory::pop_scope_eh(num_scopes);
            m_sg.pop(num_scopes);
            // The sgraph pop released snodes the incremental eager chain references;
            // discard it so the next eager run rebuilds rather than extending a
            // dangling chain (see eager_structural_check).
            m_nielsen.eager_invalidate();
            m_eager_processed = 0;
            // A pop may remove constraints and/or unassign forced Nielsen
            // literals; conservatively invalidate the cached SAT path.
            if (m_can_hot_restart && ctx.get_scope_level() - num_scopes < m_last_constraint_added)
                // we popped one of the constraints used to build the Nielsen graph
                m_can_hot_restart = false;
        }
        catch(const std::exception&) {
#ifdef Z3DEBUG
            std::string dot = m_nielsen.to_dot();
#endif
            throw;
        }
    }

    void theory_nseq::push_unhandled_pred() {
        ctx.push_trail(value_trail<unsigned>(m_num_unhandled_bool));
        ++m_num_unhandled_bool;
    }

    // -----------------------------------------------------------------------
    // Propagation: eager eq/diseq/literal dispatch
    // -----------------------------------------------------------------------

    bool theory_nseq::can_propagate() {
        return m_prop_qhead < m_prop_queue.size();
    }

    void theory_nseq::propagate() {
        try {
            if (m_prop_qhead == m_prop_queue.size())
                return;
            ctx.push_trail(value_trail(m_prop_qhead));
            while (m_prop_qhead < m_prop_queue.size() && !ctx.inconsistent()) {
                auto const& item = m_prop_queue[m_prop_qhead++];
                // don't pass arguments via reference. They might tigger internalization
                // and so the references from the propagation queue might change
                if (std::holds_alternative<eq_item>(item)) {
                    const auto eq = std::get<eq_item>(item);
                    propagate_eq(eq);
                }
                else if (std::holds_alternative<deq_item>(item)) {
                    const auto deq = std::get<deq_item>(item);
                    propagate_deq(deq);
                }
                else if (std::holds_alternative<mem_item>(item)) {
                    const auto mem = std::get<mem_item>(item);
                    propagate_pos_mem(mem);
                }
                else if (std::holds_alternative<axiom_item>(item)) {
                    dequeue_axiom(std::get<axiom_item>(item).e);
                }
                else {
                    UNREACHABLE();
                }
            }

            // Eager structural pruning: once the queue is drained, run a cheap
            // branch-free Nielsen closure over the currently-asserted constraints to
            // surface structural conflicts long before final_check
            if (!ctx.inconsistent())
                eager_structural_check();
        }
        catch(const std::exception&) {
#ifdef Z3DEBUG
            std::string dot = m_nielsen.to_dot();
#endif
            throw;
        }
    }

    // Rebuild-don't-undo, INCREMENTALLY: rather than maintaining the full Nielsen
    // graph along the DPLL(T) trail (the error-prone undo bookkeeping that sank the
    // earlier manual engine), we grow a single deterministic chain in `m_nielsen` as
    // constraints arrive — each new constraint is folded into the current leaf with
    // the chain's accumulated substitution applied (`eager_add_*`), then the chain is
    // extended (`eager_close`).  No per-propagation rebuild.  Any structural UNSAT is
    // a real conflict (subset-monotonicity); we never declare SAT or short-circuit
    // final_check.  The chain is discarded on pop (`eager_invalidate`) and whenever
    // `m_nielsen.reset()` runs (e.g. final_check's `populate_nielsen_graph`), after
    // which it is rebuilt from scratch on the next call.
    void theory_nseq::eager_structural_check() {
        if (!get_fparams().m_nseq_eager)
            return;
        // Only re-run when the Nielsen-relevant constraint set actually grew.
        if (m_eager_dirty == m_eager_seen)
            return;
        m_eager_seen = m_eager_dirty;

        // (Re)start the chain if it was discarded (first call, after a pop, or after
        // final_check reset m_nielsen).
        if (!m_nielsen.eager_active()) {
            m_nielsen.eager_begin();
            m_eager_processed = 0;
            m_can_hot_restart = false; // m_nielsen now holds the eager chain
        }

        // Fold newly-arrived prop-queue items into the current leaf.  Membership
        // handling mirrors populate_nielsen_graph (trivial check, ignored skip,
        // ground-prefix consumption via process_str_mem).
        for (; m_eager_processed < m_prop_queue.size(); ++m_eager_processed) {
            auto const& item = m_prop_queue[m_eager_processed];
            if (std::holds_alternative<eq_item>(item)) {
                auto const& eq = std::get<eq_item>(item);
                m_nielsen.eager_add_str_eq(eq.m_lhs, eq.m_rhs, eq.m_l, eq.m_r);
            }
            else if (std::holds_alternative<deq_item>(item)) {
                auto const& dq = std::get<deq_item>(item);
                m_nielsen.eager_add_str_deq(dq.m_lhs, dq.m_rhs, dq.lit);
            }
            else if (std::holds_alternative<mem_item>(item)) {
                auto const& mem = std::get<mem_item>(item);
                int triv = m_regex.check_trivial(mem);
                if (triv > 0)
                    continue;
                if (triv < 0) {
                    m_nielsen.eager_add_str_mem(mem.m_str, mem.m_regex, mem.lit);
                    continue;
                }
                if (m_ignored_mem.contains(mem.lit))
                    continue;
                vector<seq::str_mem> processed;
                if (!m_regex.process_str_mem(mem, processed)) {
                    m_nielsen.eager_add_str_mem(mem.m_str, mem.m_regex, mem.lit);
                    continue;
                }
                for (auto const& pm : processed)
                    m_nielsen.eager_add_str_mem(pm.m_str, pm.m_regex, mem.lit);
            }
        }

        const auto r = m_nielsen.eager_close();
        if (r == seq::nielsen_graph::search_result::unsat) {
            IF_VERBOSE(1, verbose_stream() << "nseq eager: structural conflict\n";);
            TRACE(seq, tout << "nseq eager: structural conflict\n");
            ++m_num_eager_conflicts;
            explain_nielsen_conflict(); // reads conflict_sources() + root, then sets the conflict
        }
        // Keep the chain for the next propagation (incremental).  It is discarded by
        // pop_scope_eh / final_check's reset, never here.
    }

    void theory_nseq::propagate_eq(tracked_str_eq const &eq) const {
        // When s1 = s2 is learned, ensure len(s1) and len(s2) are
        // internalized so congruence closure propagates len(s1) = len(s2).
        ensure_length_var(eq.m_l->get_expr());
        ensure_length_var(eq.m_r->get_expr());
    }

    void theory_nseq::propagate_deq(tracked_str_deq const& eq) const {
        ensure_length_var(eq.m_lhs->get_expr());
        ensure_length_var(eq.m_rhs->get_expr());
    }

    void theory_nseq::propagate_pos_mem(tracked_str_mem const& mem) {

        SASSERT(mem.well_formed());

        expr* const re = mem.m_regex->get_expr();
        expr* const s = mem.m_str->get_expr();
        //std::cout << "Propagating: " << seq::mem_pp(mem, m) << std::endl;

        if (!mem.m_str->is_empty()) {
            if (mem.m_str->first()->is_char()) {
                euf::snode const* re_node = mem.m_regex;
                euf::snode const* str_node = mem.m_str;
                do {
                    // eliminate leading character by derivatives; derive by the
                    // CURRENT leading char (str_node->first()), not the original
                    // mem.m_str->first() — otherwise a multi-char prefix is derived
                    // by its first char repeatedly (unsound).
                    re_node = m_sg.brzozowski_deriv(re_node, str_node->first());
                    str_node = m_sg.drop_first(str_node);
                } while (!str_node->is_empty() && str_node->first()->is_char());

                if (re_node->is_fail()) {
                    literal_vector lits;
                    lits.push_back(mem.lit);
                    set_conflict(lits);
                    return;
                }
                const expr_ref e(m_seq.re.mk_in_re(str_node->get_expr(), re_node->get_expr()), m);
                ctx.mk_th_axiom(get_id(), ~mem.lit, mk_literal(e));
                m_ignored_mem.insert(mem.lit);
                ctx.push_trail(insert_map(m_ignored_mem, mem.lit));
                return;
            }
        }
        else {
            // check nullability
            if (m_sg.re_nullable(mem.m_regex) == l_true) {
                // empty string in nullable regex → trivially satisfied
                m_ignored_mem.insert(mem.lit);
                ctx.push_trail(insert_map(m_ignored_mem, mem.lit));
                return;
            }
            return;
        }

        if (mem.m_regex->is_full_seq()) {
            // u \in .* can be ignored
            m_ignored_mem.insert(mem.lit);
            ctx.push_trail(insert_map(m_ignored_mem, mem.lit));
            return;
        }

        // try to rewrite into an easier form
        expr_ref simpl(m);
        m_th_rewriter(re, simpl);
        if (simpl != re) {
            // we could simplify; let's propagate it
            const expr_ref e(m_seq.re.mk_in_re(s, simpl), m);
            ctx.mk_th_axiom(get_id(), ~mem.lit, mk_literal(e));
            m_ignored_mem.insert(mem.lit);
            ctx.push_trail(insert_map(m_ignored_mem, mem.lit));
            // std::cout << "Simplified to " << seq::snode_label_html(m_sgraph.mk(simpl), m, false) << std::endl;
            return;
        }

        // regex is ∅ → conflict
        if (m_regex.is_empty_regex(mem.m_regex)) {
            literal_vector lits;
            lits.push_back(mem.lit);
            set_conflict(lits);
            return;
        }

        // empty string in non-nullable regex → conflict
        if (mem.m_str->is_empty() && m_sg.re_nullable(mem.m_regex) == l_false) {
            literal_vector lits;
            lits.push_back(mem.lit);
            set_conflict(lits);
            return;
        }

        if (mem.m_regex->is_to_re()) {
            // u \in v (with v is constant) → u = v
            zstring str;
            const expr_ref arg(to_app(re)->get_arg(0), m);
            if (m_seq.str.is_string(arg, str)) {
                const expr_ref eq(m.mk_eq(s, arg), m);
                ctx.mk_th_axiom(get_id(), ~mem.lit, mk_literal(eq));
                m_ignored_mem.insert(mem.lit);
                ctx.push_trail(insert_map(m_ignored_mem, mem.lit));
                return;
            }
        }

        if (!get_fparams().m_nseq_regex_factorization_threshold)
            return;

        SASSERT(!mem.m_str->is_empty());
        SASSERT(!mem.m_str->first()->is_char());
        if (!mem.m_str->first()->is_var())
            return;

        // Eager sigma factorization (token-level): when enabled, split a non-primitive
        // membership s ∈ r at the boundary between the first concat argument (head) and
        // the rest (tail), using the shared seq_split engine. This mirrors the lazy Nielsen
        // apply_regex_factorization and the paper's Reduce rule for x·u'.
        //   (s ∈ r) → ⋁_{⟨Δ,∇⟩∈σ(r)} ( head ∈ Δ ∧ tail ∈ ∇ )
        // Only fires for a concatenation s (single-variable s is already primitive).
        if (get_fparams().m_nseq_regex_factorization_eager &&
            get_fparams().m_nseq_regex_factorization_threshold > 0 &&
            mem.m_str->is_concat()) {

            const unsigned threshold = get_fparams().m_nseq_regex_factorization_threshold;

            split_set pairs;
            auto [head, tail] = seq::split_membership(mem.m_str, mem.m_regex, m_sg, threshold, pairs);

            if (!head) {
                // gave up
                SASSERT(!tail);
                return;
            }

            SASSERT(tail);

            if (pairs.empty()) {
                literal_vector lits;
                lits.push_back(mem.lit);
                set_conflict(lits);
                return;
            }
            if (pairs.size() <= threshold) {
                TRACE(seq, tout << "eager regex fact: " << mk_pp(s, m) << " in "
                                << mk_pp(re, m) << " -> " << pairs.size() << " splits\n";);

                if (!ctx.e_internalized(head->get_expr()))
                    ctx.internalize(head->get_expr(), false);
                if (!ctx.e_internalized(tail->get_expr()))
                    ctx.internalize(tail->get_expr(), false);

                // forward direction; mk_literal Tseitin-encodes each conjunction
                literal_vector lits;
                lits.push_back(~mem.lit);
                //std::cout << "Decomposing into:\n";
                for (auto const& sp : pairs) {
                    expr_ref mem_head(m_seq.re.mk_in_re(head->get_expr(), sp.m_d), m);
                    expr_ref mem_tail(m_seq.re.mk_in_re(tail->get_expr(), sp.m_n), m);
                    expr_ref conj(m.mk_and(mem_head, mem_tail), m);
                    lits.push_back(mk_literal(conj));
                    //seq::dep_tracker dep = nullptr;
                    //std::cout << seq::mem_pp(seq::str_mem(head, m_sg.mk(sp.m_d), dep), m) << " && " << seq::mem_pp(seq::str_mem(tail, m_sg.mk(sp.m_n), dep), m) << "\n";
                }
                //std::cout << std::endl;
                ctx.mk_th_axiom(get_id(), lits.size(), lits.data());
                m_ignored_mem.insert(mem.lit);
                ctx.push_trail(insert_map(m_ignored_mem, mem.lit));
                return;
            }
        }
    }

    void theory_nseq::ensure_length_var(expr* e) const {
        SASSERT(e && m_seq.is_seq(e));
        const expr_ref len(m_seq.str.mk_length(e), m);
        if (!ctx.e_internalized(len))
            ctx.internalize(len, false);
    }

    // -----------------------------------------------------------------------
    // Axiom enqueue / dequeue (follows theory_seq::enque_axiom / deque_axiom)
    // -----------------------------------------------------------------------

    void theory_nseq::enqueue_axiom(expr* e) {
        if (m_axiom_set.contains(e))
            return;
        m_axiom_set.insert(e);
        ctx.push_trail(insert_obj_trail<expr>(m_axiom_set, e));
        ctx.push_trail(restore_vector(m_prop_queue));
        m_prop_queue.push_back(axiom_item{e});
    }

    void theory_nseq::dequeue_axiom(expr* n) {
        TRACE(seq, tout << "dequeue_axiom: " << mk_bounded_pp(n, m, 2) << "\n";);
        if (m_seq.str.is_length(n))
            m_axioms.length_axiom(n);
        else if (m_seq.str.is_index(n))
            m_axioms.indexof_axiom(n);
        else if (m_seq.str.is_last_index(n))
            m_axioms.last_indexof_axiom(n);
        else if (m_seq.str.is_replace(n))
            m_axioms.replace_axiom(n);
        else if (m_seq.str.is_replace_all(n))
            m_axioms.replace_all_axiom(n);
        else if (m_seq.str.is_extract(n))
            m_axioms.extract_axiom(n);
        else if (m_seq.str.is_at(n))
            m_axioms.at_axiom(n);
        else if (m_seq.str.is_nth_i(n))
            m_axioms.nth_axiom(n);
        else if (m_seq.str.is_itos(n))
            m_axioms.itos_axiom(n);
        else if (m_seq.str.is_stoi(n))
            add_stoi_nseq_axioms(n);
        else if (m_seq.str.is_lt(n))
            m_axioms.lt_axiom(n);
        else if (m_seq.str.is_le(n))
            m_axioms.le_axiom(n);
        else if (m_seq.str.is_unit(n))
            m_axioms.unit_axiom(n);
        else if (m_seq.str.is_is_digit(n))
            m_axioms.is_digit_axiom(n);
        else if (m_seq.str.is_from_code(n))
            m_axioms.str_from_code_axiom(n);
        else if (m_seq.str.is_to_code(n))
            m_axioms.str_to_code_axiom(n);
    }

    void theory_nseq::relevant_eh(expr * n) {
        if (m_seq.str.is_length(n)     ||
            m_seq.str.is_index(n)      ||
            m_seq.str.is_last_index(n) ||
            m_seq.str.is_replace(n)    ||
            m_seq.str.is_replace_all(n)||
            m_seq.str.is_extract(n)    ||
            m_seq.str.is_at(n)         ||
            m_seq.str.is_nth_i(n)      ||
            m_seq.str.is_itos(n)       ||
            m_seq.str.is_stoi(n)       ||
            m_seq.str.is_lt(n)         ||
            m_seq.str.is_le(n)         ||
            m_seq.str.is_unit(n)       ||
            m_seq.str.is_is_digit(n)   ||
            m_seq.str.is_from_code(n)  ||
            m_seq.str.is_to_code(n))
            enqueue_axiom(n);
    }

    // -----------------------------------------------------------------------
    // Final check: build Nielsen graph and search
    // -----------------------------------------------------------------------

    void theory_nseq::populate_nielsen_graph() {
        m_nielsen.reset();
        m_can_hot_restart = true;
        m_nielsen.create_root();

        unsigned num_eqs = 0, num_deqs = 0, num_mems = 0;

        // transfer string equalities and regex memberships from prop_queue to nielsen graph root
        for (auto const& item : m_prop_queue) {
            if (std::holds_alternative<eq_item>(item)) {
                auto const& eq = std::get<eq_item>(item);
                m_nielsen.add_str_eq(eq.m_lhs, eq.m_rhs, eq.m_l, eq.m_r);
                ++num_eqs;
            }
            if (std::holds_alternative<deq_item>(item)) {
                SASSERT(!get_fparams().m_nseq_axiomatize_diseq);
                auto const& deq = std::get<deq_item>(item);
                m_nielsen.add_str_deq(deq.m_lhs, deq.m_rhs, deq.lit);
                ++num_deqs;
            }
            else if (std::holds_alternative<mem_item>(item)) {
                auto const& mem = std::get<mem_item>(item);
                int triv = m_regex.check_trivial(mem);
                if (triv > 0) {
                    ++num_mems;
                    continue;  // trivially satisfied, skip
                }
                if (triv < 0) {
                    // trivially unsat: add anyway so solve() detects conflict
                    m_nielsen.add_str_mem(mem.m_str, mem.m_regex, mem.lit);
                    ++num_mems;
                    continue;
                }
                if (m_ignored_mem.contains(mem.lit))
                    continue; // already handled via Boolean closure, skip
                // pre-process: consume ground prefix characters
                vector<seq::str_mem> processed;
                if (!m_regex.process_str_mem(mem, processed)) {
                    // conflict during ground prefix consumption
                    m_nielsen.add_str_mem(mem.m_str, mem.m_regex, mem.lit);
                    ++num_mems;
                    continue;
                }
                for (auto const& pm : processed)
                    m_nielsen.add_str_mem(pm.m_str, pm.m_regex, mem.lit);
                ++num_mems;
            }
        }

        TRACE(seq, tout << "nseq populate: " << num_eqs << " eqs, "
                        << num_deqs << " diseqs, " << num_mems << " mems -> nielsen root\n");
        IF_VERBOSE(1, verbose_stream() << "nseq final_check: populating graph with "
            << num_eqs << " eqs, " << num_mems << " mems\n";);
    }

    final_check_status theory_nseq::final_check_eh(unsigned /*final_check_round*/) {
        try {
            // Always assert non-negativity for all string theory vars,
            // even when there are no string equations/memberships.
            if (assert_nonneg_for_all_vars()) {
                TRACE(seq, tout << "nseq final_check: nonneg assertions added, FC_CONTINUE\n");
                return FC_CONTINUE;
            }

            // Check if there are any eq/mem items in the propagation queue.
            bool has_eq_or_diseq_or_mem = any_of(m_prop_queue, [](auto const &item) {
                return std::holds_alternative<eq_item>(item) || std::holds_alternative<deq_item>(item) || std::holds_alternative<mem_item>(item);
            });

            // there is nothing to do for the string solver, as there are no string constraints
            if (!has_eq_or_diseq_or_mem && m_ho_terms.empty() && !has_unhandled_preds()) {
                if (!check_stoi_coherence()) {
                    TRACE(seq, tout << "nseq final_check: stoi coherence added axioms, FC_CONTINUE\n");
                    return FC_CONTINUE;
                }
                TRACE(seq, tout << "nseq final_check: empty state+ho, FC_DONE (no solve)\n");
                m_nielsen.reset();
                m_nielsen.create_root();
                m_nielsen.set_sat_node(m_nielsen.root());
                TRACE(seq, display(tout << "empty nielsen\n"));
                return FC_DONE;
            }

            // unfold higher-order terms when sequence structure is known
            if (unfold_ho_terms()) {
                TRACE(seq, tout << "nseq final_check: unfolded ho_terms, FC_CONTINUE\n");
                return FC_CONTINUE;
            }

            if (!has_eq_or_diseq_or_mem && !has_unhandled_preds()) {
                if (!check_stoi_coherence()) {
                    TRACE(seq, tout << "nseq final_check: stoi coherence added axioms, FC_CONTINUE\n");
                    return FC_CONTINUE;
                }
                TRACE(seq, tout << "nseq final_check: empty state (after ho), FC_DONE (no solve)\n");
                m_nielsen.reset();
                m_nielsen.create_root();
                m_nielsen.set_sat_node(m_nielsen.root());
                TRACE(seq, display(tout << "empty nielsen\n"));
                return FC_DONE;
            }

            if (!has_eq_or_diseq_or_mem && has_unhandled_preds()) {
                TRACE(seq, tout << "nielsen root if null\n");
                // this can happen for regex constraint only benchmarks
                // qf_s\20250410-matching\wildcard-matching-regex-67.smt2
                return FC_GIVEUP;
            }

            // Fast path: if no new string eq/mem arrived and no scope was popped
            // since the last successful solve, the Nielsen graph can be (at least)
            // partially be reused
            if (m_can_hot_restart) {
                // SAT leaf are identical to what we would rebuild.  All of the leaf's
                // arithmetic side-constraints are already assigned true by the outer
                // solver, so the model is valid — skip the rebuild and re-solve.
                if (m_nielsen.sat_node() != nullptr &&
                    !m_nielsen_literals.empty() &&
                    all_of(m_nielsen_literals, [&](auto lit) { return l_true == ctx.get_assignment(lit); })) {
                    ++m_num_sat_revalidations;
                    TRACE(seq, tout << "nseq final_check: revalidated cached SAT path, skipping rebuild\n");
                    if (!check_length_coherence()) return FC_CONTINUE;
                    if (!check_stoi_coherence())   return FC_CONTINUE;
                    if (!has_unhandled_preds())    return FC_DONE;
                    return FC_GIVEUP;
                }
                // fall through - no reason to rebuild the Nielsen graph
                // everything that is not a general conflict needs to be recomputed
                // but we can keep the general conflicts (which can be a lot!)
                std::stack<seq::nielsen_node*> to_visit;
                to_visit.push(m_nielsen.root());
                while (!to_visit.empty()) {
                    seq::nielsen_node* node = to_visit.top();
                    to_visit.pop();
                    if (node->is_general_conflict())
                        // all its children are general conflicts as well - nothing to do
                        continue;
                    if (node->reason() == seq::backtrack_reason::children_failed) {
                        SASSERT(!node->is_general_conflict());
                        node->clear_reason();
                    }

                    if (node->is_external_conflict())
                        node->clear_local_conflict();

                    for (auto& child : node->outgoing()) {
                        to_visit.push(child->tgt());
                    }
                }
                m_nielsen.clear_sat_node();
                m_length_solver.reset();
            }
            else {
                // let's rebuild the whole Nielsen graph
                populate_nielsen_graph();

                m_nielsen.set_max_search_depth(get_fparams().m_nseq_max_depth);
                m_nielsen.set_max_nodes(get_fparams().m_nseq_max_nodes);
                m_nielsen.set_parikh_enabled(get_fparams().m_nseq_parikh);
                m_nielsen.set_signature_split(get_fparams().m_nseq_signature);
                m_nielsen.set_regex_factorization_threshold(get_fparams().m_nseq_regex_factorization_threshold);
                m_nielsen.set_regex_factorization_eager(get_fparams().m_nseq_regex_factorization_eager);

                // assert length constraints derived from string equalities
                if (assert_length_constraints()) {
                    TRACE(seq, tout << "nseq final_check: length constraints asserted, FC_CONTINUE\n");
                    return FC_CONTINUE;
                }
                SASSERT(m_nielsen.root());
                m_nielsen.assert_node_side_constraints(m_nielsen.root());
            }

            ++m_num_final_checks;

            SASSERT(!m_nielsen.root()->is_currently_conflict());

            // nseq cannot soundly reason about defined sequence operations (str.replace,
            // str.replace_all, str.replace_re*) inside the Nielsen graph: they are not free
            // variables but are pinned by the recfun/axiom layer.  The modifiers (and the
            // regex pre-check) would treat them as free (e.g. unifying two distinct
            // replace_all applications), silently discarding their definition and yielding
            // invalid models.  When such a rigid term participates in the constraints, defer
            // to the axiom layer and give up.  (Concrete replace_all etc. are folded to
            // literals by seq_rewriter before reaching the sgraph, so only genuinely
            // symbolic occurrences are affected.)  This check precedes the regex pre-check
            // so a rigid term as a membership subject cannot yield a bogus SAT either.
            if (m_nielsen.root()->references_rigid()) {
                IF_VERBOSE(1, verbose_stream() << "nseq final_check: rigid defined op present, FC_GIVEUP\n";);
                TRACE(seq, tout << "nseq final_check: rigid defined op present, FC_GIVEUP\n");
                return FC_GIVEUP;
            }

            // Regex membership pre-check: before running DFS, check intersection
            // emptiness for each variable's regex constraints.  This handles
            // regex-only problems that the DFS cannot efficiently solve.
            if (!m_nielsen.root()->is_currently_conflict() && get_fparams().m_nseq_regex_precheck) {
                switch (check_regex_memberships_precheck()) {
                case l_true:
                    // conflict was asserted inside check_regex_memberships_precheck
                    TRACE(seq, tout << "nseq final_check: regex precheck UNSAT\n");
                    return FC_CONTINUE;
                case l_false:
                    // all regex constraints satisfiable, no word eqs → SAT
                    TRACE(seq, tout << "nseq final_check: regex precheck SAT\n");
                    m_nielsen.set_sat_node(m_nielsen.root());
                    if (!check_length_coherence())
                        return FC_CONTINUE;
                    if (!check_stoi_coherence())
                        return FC_CONTINUE;
                    TRACE(seq, tout << "pre-check done\n");
                    return FC_DONE;
                default:
                    break;
                }
            }

            // std::cout << "[" << m_num_final_checks << "]" << std::endl;
            IF_VERBOSE(1, verbose_stream() << "nseq final_check: calling solve()\n";);

            // here the actual Nielsen solving happens
            auto result = m_nielsen.solve();

#ifdef Z3DEBUG
            // Examining the Nielsen graph is probably the best way of debugging
            std::string dot = m_nielsen.to_dot();
            IF_VERBOSE(1, verbose_stream() << dot << "\n";);
            // std::cout << "Got: " << (result == seq::nielsen_graph::search_result::sat ? "sat" : (result == seq::nielsen_graph::search_result::unsat ? "unsat" : "unknown")) << std::endl;
#endif

            if (result == seq::nielsen_graph::search_result::unsat) {
                IF_VERBOSE(1, verbose_stream() << "nseq final_check: solve UNSAT\n";);
                TRACE(seq, tout << "nseq final_check: solve UNSAT\n");
                explain_nielsen_conflict();
                return FC_CONTINUE;
            }

            if (result == seq::nielsen_graph::search_result::sat) {
                IF_VERBOSE(1, verbose_stream() << "nseq final_check: solve SAT, sat_node="
                    << (m_nielsen.sat_node() ? "set" : "null") << "\n";);
                TRACE(seq, tout << "nseq final_check: solve SAT, sat_node="
                    << (m_nielsen.sat_node() ? "set" : "null") << "\n");
                // Nielsen found a consistent assignment for positive constraints.
                SASSERT(has_eq_or_diseq_or_mem); // we should have axiomatized them
                if (!check_length_coherence())
                    return FC_CONTINUE;

                if (!check_stoi_coherence())
                    return FC_CONTINUE;

                CTRACE(seq, !has_unhandled_preds(), display(tout << "done\n"));

                bool all_sat = add_nielsen_assumptions();

                if (!all_sat)
                    return FC_CONTINUE;

                if (!has_unhandled_preds())
                    return FC_DONE;
            }

            TRACE(seq, display(tout << "unknown\n"));
            IF_VERBOSE(1, verbose_stream() << "nseq final_check: solve UNKNOWN, FC_GIVEUP\n";);
            return FC_GIVEUP;
        }
        catch(const std::exception&) {
#ifdef Z3DEBUG
            std::string dot = m_nielsen.to_dot();
#endif
            throw;
        }
    }


    bool theory_nseq::add_nielsen_assumptions() {
        m_nielsen_literals.reset();
        struct reset_vector : public trail {
            sat::literal_vector &v;
            reset_vector(sat::literal_vector &v) : v(v) {}
            void undo() override {
                v.reset();
            }
        };
        //std::cout << "Nielsen assumptions:\n";
        bool all_sat = true;
        ctx.push_trail(reset_vector(m_nielsen_literals));
        for (const auto& c : m_nielsen.sat_node()->constraints()) {
            // std::cout << "Assumption: " << mk_pp(c.fml, m) << std::endl;
            auto lit = mk_literal(c.fml);   
            m_nielsen_literals.push_back(lit);
            // Ensure Nielsen assumptions participate in SAT search instead of
            // remaining permanently undefined under pure phase hints.
            ctx.mark_as_relevant(lit);
            // std::cout << "Assumption: " << mk_pp(c.fml, m) << std::endl;
            switch (ctx.get_assignment(lit)) { 
            case l_true: 
                break;
            case l_undef:
                // std::cout << "Undef [" << lit << "]: " << mk_pp(c.fml, m) << std::endl;
                // Commit the chosen Nielsen assumption to the SAT core so it
                // cannot remain permanently undefined in a partial model.
                ctx.privileged_split(lit);
                all_sat = false;
                IF_VERBOSE(2, verbose_stream() << 
                    "nseq final_check: adding nielsen assumption " << c.fml << "\n";);
                TRACE(seq, tout << "assign: " << c.fml << "\n");
                break;
            case l_false: 
                // this should not happen because nielsen checks for this before returning a satisfying path.
                TRACE(seq, tout << "nseq final_check: nielsen assumption " << c.fml << " is false; internalized - " << ctx.e_internalized(c.fml) << "\n");
                all_sat = false;
                std::cout << "False [" << lit << "]: " << mk_pp(c.fml, m) << std::endl;
                ctx.push_trail(value_trail(m_context_solver.m_should_internalize));
                m_context_solver.m_should_internalize = true;
                break;
            }
            // use assumptions to bound search
            // "propagate(m_assumption_lit, lit)"; // to force the phase of lit to be true or force a conflict
        }
        return all_sat;
    }

    // -----------------------------------------------------------------------
    // Conflict explanation
    // -----------------------------------------------------------------------

    void theory_nseq::explain_nielsen_conflict() {
        enode_pair_vector eqs;
        literal_vector lits;
        for (seq::dep_source const& d : m_nielsen.conflict_sources()) {
            if (std::holds_alternative<enode_pair>(d))
                eqs.push_back(std::get<enode_pair>(d));
            else if (std::holds_alternative<sat::literal>(d))
                lits.push_back(std::get<sat::literal>(d));
            else
                UNREACHABLE();
        }
        ++m_num_conflicts;
        set_conflict(eqs, lits);

#ifdef Z3DEBUG
#if 0
        // Pass constraints to a subsolver to check correctness modulo legacy solver
        {
            smt_params p;
            p.m_string_solver = "seq";
            kernel kernel(m, p);

            auto model_out = [&]() {
                model_ref model;
                kernel.get_model(model);
                for (unsigned i = 0; i < model->get_num_constants(); i++) {
                    func_decl* f  = model->get_constant(i);
                    expr_ref v(m);
                    VERIFY(model->eval(f, v));
                    std::cout << f->get_name() << ": " << mk_pp(v, m) << std::endl;
                }
                for (unsigned i = 0; i < model->get_num_functions(); i++) {
                    func_decl* f  = model->get_function(i);
                    func_interp* fi = model->get_func_interp(f);
                    auto entries = fi->get_entries();
                    std::cout << f->get_name() << ":\n";
                    for (unsigned j = 0; j < fi->num_entries(); j++) {
                        auto& e = entries[j];
                        auto* args = e->get_args();
                        std::cout << "\n(";
                        for (unsigned k = 0; k < fi->get_arity(); k++) {
                            if (k > 0)
                                std::cout << ", ";
                            std::cout << mk_pp(args[k], m);
                        }
                        std::cout << "): ";
                        expr* r = e->get_result();
                        std::cout << mk_pp(r, m) << std::endl;
                    }
                }
            };

            for (seq::dep_source const& d : m_nielsen.conflict_sources()) {
                if (std::holds_alternative<enode_pair>(d))
                    kernel.assert_expr(
                        m.mk_eq(
                        std::get<enode_pair>(d).first->get_expr(),
                        std::get<enode_pair>(d).second->get_expr()
                            )
                        );
                else if (std::holds_alternative<sat::literal>(d))
                    kernel.assert_expr(ctx.literal2expr(std::get<sat::literal>(d)));
                else {
                    UNREACHABLE();
                }
            }
            auto res = kernel.check();
            if (res == l_true) {
                std::cout << "Conflict is SAT - Insufficient justification:\n";
                for (auto& lit : lits) {
                    std::cout << mk_pp(ctx.literal2expr(lit), m) << "\n-----------\n";
                }
                for (auto& eq : eqs) {
                    std::cout << mk_pp(eq.first->get_expr(), m) << " == " << mk_pp(eq.second->get_expr(), m) << "\n-----------\n";
                }
                auto dot = m_nielsen.to_dot();
                std::cout << std::endl;
                model_out();
                kernel.reset();
                for (auto& eq : m_nielsen.root()->str_eqs()) {
                    kernel.assert_expr(m.mk_eq(eq.m_lhs->get_expr(), eq.m_rhs->get_expr()));
                }
                for (auto& mem : m_nielsen.root()->str_mems()) {
                    kernel.assert_expr(m_seq.re.mk_in_re(mem.m_str->get_expr(), mem.m_regex->get_expr()));
                }
                auto res2 = kernel.check();
                if (res2 == l_true) {
                    std::cout << "Nielsen input is SAT" << std::endl;
                    model_out();
                    kernel.reset();
                    auto& lits = ctx.assigned_literals();
                    for (literal l : lits) {
                        expr* e = ctx.literal2expr(l);
                        if (!ctx.b_internalized(e) || !ctx.is_relevant(e))
                            continue;
                        th_rewriter th(m);
                        expr_ref r(m);
                        th(e, r);
                        kernel.assert_expr(r);
                    }
                    auto res3 = kernel.check();
                    if (res3 == l_true) {
                        // the algorithm is unsound
                        std::cout << "Complete input is SAT" << std::endl;
                        model_out();
                    }
                    else if (res3 == l_false)
                        // the justification is too narrow
                        std::cout << "Complete input is UNSAT" << std::endl;
                    else
                        std::cout << "Complete input is UNKNOWN" << std::endl;
                }
                else if (res2 == l_false)
                    std::cout << "Nielsen input is UNSAT" << std::endl;
                else
                    std::cout << "Nielsen input is UNKNOWN" << std::endl;
            }
            VERIFY(res != l_true);
        }
#else
        for (auto& lit : lits) {
            std::cout << mk_pp(ctx.literal2expr(lit), m) << "\n-----------\n";
        }
        for (auto& eq : eqs) {
            std::cout << mk_pp(eq.first->get_expr(), m) << " == " << mk_pp(eq.second->get_expr(), m) << "\n-----------\n";
        }
#endif
#endif

#ifdef Z3DEBUG
        std::cout << "Conflict with " << lits.size() << " literals and " << eqs.size() << " equalities" << std::endl;
        std::cout << "The root node contained " << m_nielsen.root()->str_mems().size() << " memberships and " << m_nielsen.root()->str_eqs().size() << " equalities" << std::endl;
        unsigned idx = 0;
        for (auto& eq : m_nielsen.root()->str_eqs()) {
            std::cout << "[" << (idx++) << "]: " << seq::eq_pp(eq, m) << "\n";
        }
        idx = 0;
        for (auto& mem : m_nielsen.root()->str_mems()) {
            std::cout << "[" << (idx++) << "]: " << seq::mem_pp(mem, m) << "\n";
        }
        std::flush(std::cout);
#endif
    }

    void theory_nseq::set_conflict(enode_pair_vector const& eqs, literal_vector const& lits) const {
        TRACE(seq, tout << "nseq conflict: " << eqs.size() << " eqs, " << lits.size() << " lits\n";
              for (auto lit : lits) tout << ctx.literal2expr(lit) << "\n";
              for (auto [a, b] : eqs) tout << enode_pp(a, ctx) << " == " << enode_pp(b, ctx) << "\n";
        );

        SASSERT(std::ranges::all_of(eqs, [&](auto& eq) { return eq.first->get_root() == eq.second->get_root(); }));

        SASSERT(all_of(lits, [&](auto lit) { return ctx.get_assignment(lit) == l_true; }));

        ctx.set_conflict(
            ctx.mk_justification(
                ext_theory_conflict_justification(
                    get_id(), ctx, lits.size(), lits.data(), eqs.size(), eqs.data(), 0, nullptr)));
    }

    void theory_nseq::set_propagate(enode_pair_vector const& eqs, literal_vector const& lits, literal p) {
        SASSERT(all_of(eqs, [&](auto eq) { return eq.first->get_root() == eq.second->get_root(); }));

        bool all_true = all_of(lits, [&](auto lit) { return ctx.get_assignment(lit) == l_true; });

        TRACE(seq, tout << "nseq propagation: " << ctx.literal2expr(p) << " (" << eqs.size() << " eqs, "
                        << lits.size() << " lits)\n";
              for (auto lit : lits) tout << "<- " << ctx.literal2expr(lit) << "\n";
              for (auto [a, b] : eqs) tout << "<- " << enode_pp(a, ctx) << " == " << enode_pp(b, ctx) << "\n";);

        ctx.mark_as_relevant(p);

        if (all_true) {
            justification *js = ctx.mk_justification(ext_theory_propagation_justification(
                get_id(), ctx, lits.size(), lits.data(), eqs.size(), eqs.data(), p));
            ctx.assign(p, js);
        }
        else {
            literal_vector clause;
            for (literal lit : lits)
                clause.push_back(~lit);
            for (auto [a, b] : eqs)
                clause.push_back(~mk_eq(a->get_expr(), b->get_expr(), false));
            clause.push_back(p);
            for (auto lit : clause)
                ctx.mark_as_relevant(lit);
            ctx.mk_th_axiom(get_id(), clause.size(), clause.data());
        }
    }

    // -----------------------------------------------------------------------
    // Model generation
    // -----------------------------------------------------------------------

    void theory_nseq::init_model(model_generator& mg) {
        m_model.init(mg, m_nielsen);
    }

    model_value_proc* theory_nseq::mk_value(enode* n, model_generator& mg) {
        return m_model.mk_value(n, mg);
    }

    void theory_nseq::finalize_model(model_generator& mg) {
        m_model.finalize(mg);
    }

    void theory_nseq::validate_model(proto_model& mdl) {
        for (auto const& item : m_prop_queue)
            if (std::holds_alternative<mem_item>(item))
                m_model.validate_regex(std::get<mem_item>(item), mdl);
    }

    // -----------------------------------------------------------------------
    // Statistics / display
    // -----------------------------------------------------------------------

    void theory_nseq::collect_statistics(::statistics& st) const {
        st.update("nseq conflicts",         m_num_conflicts);
        st.update("nseq eager conflicts",   m_num_eager_conflicts);
        st.update("nseq final checks",      m_num_final_checks);
        st.update("nseq sat revalidations", m_num_sat_revalidations);
        st.update("nseq length axioms",     m_num_length_axioms);
        st.update("nseq ho unfolds",      m_num_ho_unfolds);
        m_nielsen.collect_statistics(st);
    }

    void theory_nseq::display(std::ostream& out) const {
        unsigned num_eqs = 0, num_mems = 0;
        for (auto const& item : m_prop_queue) {
            if (std::holds_alternative<eq_item>(item)) ++num_eqs;
            else if (std::holds_alternative<mem_item>(item)) ++num_mems;
        }
        out << "theory_nseq\n";
        out << "  str_eqs:    " << num_eqs << "\n";
        out << "  str_mems:   " << num_mems << "\n";
        out << "  prop_queue: " << m_prop_qhead << "/" << m_prop_queue.size() << "\n";
        out << "  ho_terms:   " << m_ho_terms.size() << "\n";
        for (auto const &item : m_prop_queue) {
            if (std::holds_alternative<eq_item>(item)) {
                auto const& eq = std::get<eq_item>(item);
                out << "    eq: " << mk_bounded_pp(eq.m_l->get_expr(), m, 3)
                    << " = " << mk_bounded_pp(eq.m_r->get_expr(), m, 3) << "\n";
            }
            else if (std::holds_alternative<mem_item>(item)) {
                auto const& mem = std::get<mem_item>(item);
                out << "    mem: " << mk_bounded_pp(mem.m_str->get_expr(), m, 3)
                    << " in " << mk_bounded_pp(mem.m_regex->get_expr(), m, 3)
                    << " (lit: " << mem.lit << ")\n";
            }
            else if (std::holds_alternative<axiom_item>(item)) {
                auto const& ax = std::get<axiom_item>(item);
                out << "    axiom: " << mk_bounded_pp(ax.e, m, 3) << "\n";
            }
        }
        m_nielsen.display(out);
    }

    // -----------------------------------------------------------------------
    // Factory / clone
    // -----------------------------------------------------------------------

    theory* theory_nseq::mk_fresh(context* ctx) {
        return alloc(theory_nseq, *ctx);
    }

    // -----------------------------------------------------------------------
    // Higher-order term unfolding (seq.map, seq.foldl, etc.)
    // -----------------------------------------------------------------------

    bool theory_nseq::unfold_ho_terms() {
        if (m_ho_terms.empty())
            return false;

        bool progress = false;

        for (app* term : m_ho_terms) {
            expr* f = nullptr, *s = nullptr, *b = nullptr, *idx = nullptr;

            if (!m_seq.str.is_map(term, f, s) &&
                !m_seq.str.is_mapi(term, f, idx, s) &&
                !m_seq.str.is_foldl(term, f, b, s) &&
                !m_seq.str.is_foldli(term, f, idx, b, s))
                continue;

            if (!ctx.e_internalized(s))
                continue;

            // Find a structural representative in s's equivalence class
            enode* s_root = ctx.get_enode(s)->get_root();
            expr* repr = nullptr;
            enode* curr = s_root;
            do {
                expr* e = curr->get_expr();
                expr *a1, *a2;
                if (m_seq.str.is_empty(e) ||
                    m_seq.str.is_unit(e, a1) ||
                    m_seq.str.is_concat(e, a1, a2)) {
                    repr = e;
                    break;
                }
                curr = curr->get_next();
            } while (curr != s_root);

            if (!repr)
                continue;

            // Build ho_term with structural seq arg, then rewrite
            expr_ref ho_repr(m);
            if (m_seq.str.is_map(term))
                ho_repr = m_seq.str.mk_map(f, repr);
            else if (m_seq.str.is_mapi(term))
                ho_repr = m_seq.str.mk_mapi(f, idx, repr);
            else if (m_seq.str.is_foldl(term))
                ho_repr = m_seq.str.mk_foldl(f, b, repr);
            else
                ho_repr = m_seq.str.mk_foldli(f, idx, b, repr);

            expr_ref rewritten(m);
            br_status st = m_rewriter.mk_app_core(
                to_app(ho_repr)->get_decl(),
                to_app(ho_repr)->get_num_args(),
                to_app(ho_repr)->get_args(),
                rewritten);

            if (st == BR_FAILED)
                continue;

            // Internalize both the structural ho_term and its rewrite
            if (!ctx.e_internalized(ho_repr))
                ctx.internalize(ho_repr, false);
            if (!ctx.e_internalized(rewritten))
                ctx.internalize(rewritten, false);

            enode* ho_en = ctx.get_enode(ho_repr);
            enode* res_en = ctx.get_enode(rewritten);

            if (ho_en->get_root() == res_en->get_root())
                continue;

            // Assert tautological axiom: ho_repr = rewritten
            // Congruence closure merges map(f,s) with map(f,repr)
            // since s = repr in the E-graph.
            expr_ref eq_expr(m.mk_eq(ho_repr, rewritten), m);
            if (!ctx.b_internalized(eq_expr))
                ctx.internalize(eq_expr, true);
            literal eq_lit = ctx.get_literal(eq_expr);
            if (ctx.get_assignment(eq_lit) != l_true) {
                ctx.mk_th_axiom(get_id(), 1, &eq_lit);
                TRACE(seq, tout << "nseq ho unfold: "
                                << mk_bounded_pp(ho_repr, m, 3) << " = "
                                << mk_bounded_pp(rewritten, m, 3) << "\n";);
                ++m_num_ho_unfolds;
                progress = true;
            }
        }

        // For map/mapi: propagate length preservation
        for (app* term : m_ho_terms) {
            expr* f = nullptr, *s = nullptr, *idx = nullptr;
            bool is_map = m_seq.str.is_map(term, f, s);
            bool is_mapi = !is_map && m_seq.str.is_mapi(term, f, idx, s);
            if (!is_map && !is_mapi)
                continue;
            if (!m_seq.is_seq(term))
                continue;

            // len(map(f, s)) = len(s)
            expr_ref len_map(m_seq.str.mk_length(term), m);
            expr_ref len_s(m_seq.str.mk_length(s), m);
            expr_ref len_eq(m.mk_eq(len_map, len_s), m);
            if (!ctx.b_internalized(len_eq))
                ctx.internalize(len_eq, true);
            literal len_lit = ctx.get_literal(len_eq);
            if (ctx.get_assignment(len_lit) != l_true) {
                ctx.mk_th_axiom(get_id(), 1, &len_lit);
                ++m_num_length_axioms;
                progress = true;
            }
        }

        return progress;
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    euf::snode const* theory_nseq::get_snode(expr* e) {
        return m_sg.mk(e);
    }

    // -----------------------------------------------------------------------
    // Arithmetic value queries
    // -----------------------------------------------------------------------

    bool theory_nseq::get_num_value(expr* e, rational& val) const {
        // In QF_SLIA mode theory_lra does not register numeral constants as LP
        // variables, so get_value_equiv misses cases where a term is only known
        // through an EUF equality with a numeral (e.g. (str.len w) = 5).
        // Walk the equivalence class directly first.
        if (get_context().e_internalized(e)) {
            enode* root = get_context().get_enode(e);
            enode* it = root;
            do {
                if (m_autil.is_numeral(it->get_expr(), val) && val.is_int())
                    return true;
                it = it->get_next();
            } while (it != root);
        }
        return m_arith_value.get_value_equiv(e, val) && val.is_int();
    }

    bool theory_nseq::lower_bound(expr* e, rational& lo) const {
        bool is_strict = true;
        return m_arith_value.get_lo(e, lo, is_strict) && !is_strict && lo.is_int();
    }

    bool theory_nseq::upper_bound(expr* e, rational& hi) const {
        bool is_strict = true;
        return m_arith_value.get_up(e, hi, is_strict) && !is_strict && hi.is_int();
    }

    bool theory_nseq::get_length(expr* e, rational& val) const {
        rational val1;
        expr* e1 = nullptr;
        expr* e2 = nullptr;
        ptr_vector<expr> todo;
        todo.push_back(e);
        val.reset();
        zstring s;
        while (!todo.empty()) {
            expr* c = todo.back();
            todo.pop_back();
            if (m_seq.str.is_concat(c, e1, e2)) {
                todo.push_back(e1);
                todo.push_back(e2);
            }
            else if (m_seq.str.is_unit(c))
                val += rational(1);
            else if (m_seq.str.is_empty(c))
                continue;
            else if (m_seq.str.is_string(c, s))
                val += rational(s.length());
            else {
                expr_ref len(m_seq.str.mk_length(c), m);
                if (m_arith_value.get_value(len, val1) && !val1.is_neg())
                    val += val1;
                else
                    return false;
            }
        }
        return val.is_int();
    }

    void theory_nseq::add_length_axiom(literal lit) {
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
        ++m_num_length_axioms;
    }

    bool theory_nseq::propagate_length_lemma(literal lit, seq::length_constraint const& lc) {
        // unconditional constraints: assert as theory axiom
        if (lc.m_kind == seq::length_kind::nonneg) {
            add_length_axiom(lit);
            return true;
        }

        // conditional constraints: propagate with justification from dep_tracker
        enode_pair_vector eqs;
        literal_vector lits;
        seq::deps_to_lits(m_nielsen.dep_mgr(), lc.m_dep, eqs, lits);

        set_propagate(eqs, lits, lit);

        ++m_num_length_axioms;
        return true;
    }

    bool theory_nseq::assert_nonneg_for_all_vars() {
        arith_util arith(m);
        bool new_axiom = false;
        unsigned nv = get_num_vars();
        for (unsigned v = 0; v < nv; ++v) {
            expr* e = get_enode(v)->get_expr();
            if (!m_seq.is_seq(e))
                continue;
            expr_ref len_var(m_seq.str.mk_length(e), m);
            expr_ref ge_zero(arith.mk_ge(len_var, arith.mk_int(0)), m);
            if (!ctx.b_internalized(ge_zero))
                ctx.internalize(ge_zero, true);
            literal lit = ctx.get_literal(ge_zero);
            if (ctx.get_assignment(lit) != l_true) {
                add_length_axiom(lit);
                new_axiom = true;
            }
        }
        return new_axiom;
    }

    bool theory_nseq::assert_length_constraints() {
        vector<seq::length_constraint> constraints;
        m_nielsen.generate_length_constraints(constraints);

        bool new_axiom = false;
        for (auto const& lc : constraints) {
            expr* e = lc.m_expr;
            if (!ctx.b_internalized(e))
                ctx.internalize(e, true);
            literal lit = ctx.get_literal(e);
            if (ctx.get_assignment(lit) != l_true) {
                propagate_length_lemma(lit, lc);
                new_axiom = true;
            }
        }
        return new_axiom;
    }

    // -----------------------------------------------------------------------
    // Regex membership pre-check
    // For each variable with regex membership constraints, check intersection
    // emptiness before DFS.  Mirrors ZIPT's per-variable regex evaluation.
    //
    // Returns:
    //   l_true  — conflict asserted (empty intersection for some variable)
    //   l_false — all variables satisfiable and no word eqs/diseqs → SAT
    //   l_undef — inconclusive, proceed to DFS
    // -----------------------------------------------------------------------

    lbool theory_nseq::check_regex_memberships_precheck() {
        // Collect mem items from the propagation queue into a local pointer array
        // so that indices into the array remain stable during this function.
        ptr_vector<tracked_str_mem const> mems;
        for (auto const& item : m_prop_queue) {
            if (std::holds_alternative<mem_item>(item))
                mems.push_back(&std::get<mem_item>(item));
        }

        if (mems.empty())
            return l_undef;

        // Group membership indices by variable snode id.
        // Only consider memberships whose string snode is a plain variable (s_var).
        u_map<unsigned_vector> var_to_mems;
        bool all_primitive = true;

        for (unsigned i = 0; i < mems.size(); ++i) {
            auto const& mem = *mems[i];
            SASSERT(mem.well_formed());
            if (mem.is_primitive()) {
                auto& vec = var_to_mems.insert_if_not_there(mem.m_str->id(), unsigned_vector());
                vec.push_back(i);
            }
            else
                all_primitive = false;
        }

        if (var_to_mems.empty())
            return l_undef;

        // Check if there are any eq items in the queue (needed for SAT condition below).
        bool has_eqs = any_of(m_prop_queue, [](auto p) { return std::holds_alternative<eq_item>(p) || std::holds_alternative<deq_item>(p); });

        bool any_undef = false;

        // Check intersection emptiness for each variable.
        for (auto &[var_id, mem_indices] : var_to_mems) {

            euf::snode_vector regexes;
            for (const unsigned i : mem_indices) {
                euf::snode const* re = mems[i]->m_regex;
                SASSERT(re);
                regexes.push_back(re);
            }
            if (regexes.empty())
                continue;

            // Use a bounded BFS (50 states) for the pre-check to keep it fast.
            // If the BFS times out (l_undef), we fall through to DFS.
            lbool result = m_regex.check_intersection_emptiness(regexes, 50);

            if (result == l_true) {
                // Intersection is empty → the memberships on this variable are
                // jointly unsatisfiable.  Assert a conflict from all their literals.
                literal_vector lits;
                for (const unsigned i : mem_indices) {
                    SASSERT(ctx.get_assignment(mems[i]->lit) == l_true); // we already stored the polarity of the literal
                    lits.push_back(mems[i]->lit);
                }
                TRACE(seq, tout << "nseq regex precheck: empty intersection for var "
                                << var_id << ", conflict with " << lits.size() << " lits\n";);
                set_conflict(lits);
                return l_true;   // conflict asserted
            }
            if (result == l_undef)
                any_undef = true;
            // l_false = non-empty intersection, this variable's constraints are satisfiable
        }

        if (any_undef)
            return l_undef;  // cannot fully determine; let DFS decide

        // All variables' regex intersections are non-empty.
        // If there are no word equations, variables are independent and
        // each can be assigned a witness string → SAT.
        if (all_primitive && !has_eqs && !has_unhandled_preds()) {
            TRACE(seq, tout << "nseq regex precheck: all intersections non-empty, "
                            << "no word eqs → SAT\n";);
            return l_false;  // signals SAT (non-empty / satisfiable)
        }

        return l_undef;  // mixed constraints; let DFS decide
    }

    // -----------------------------------------------------------------------
    // stoi (str.to_int) axiomatization for nseq
    //
    // Basic axioms (added once when the term becomes relevant):
    //   stoi(s) >= -1
    //   stoi("") = -1
    //   stoi(s) >= 0  <=>  s ∈ [0-9]+
    //
    // Inductive coherence (added in final_check once the arith solver has
    // committed to a concrete length k for s):
    //   stoi_axiom(stoi_e, k)  — the position-by-position unfolding from
    //   seq_axioms that computes the exact integer value.
    // -----------------------------------------------------------------------

    void theory_nseq::add_stoi_nseq_axioms(expr* stoi_e) {
        expr* s = nullptr;
        VERIFY(m_seq.str.is_stoi(stoi_e, s));

        // stoi(s) >= -1
        {
            expr_ref ge_m1(m_autil.mk_ge(stoi_e, m_autil.mk_int(-1)), m);
            literal lit = mk_literal(ge_m1);
            ctx.mark_as_relevant(lit);
            ctx.mk_th_axiom(get_id(), 1, &lit);
        }

        // stoi("") = -1
        {
            expr_ref empty_s(m_seq.str.mk_empty(s->get_sort()), m);
            expr_ref stoi_empty(m_seq.str.mk_stoi(empty_s), m);
            expr_ref eq_neg1(m.mk_eq(stoi_empty, m_autil.mk_int(-1)), m);
            literal lit = mk_literal(eq_neg1);
            ctx.mark_as_relevant(lit);
            ctx.mk_th_axiom(get_id(), 1, &lit);
        }

        // stoi(s) >= 0 <=> s ∈ [0-9]+
        {
            expr_ref re_digit(m_seq.re.mk_range(m_seq.str.mk_string("0"), m_seq.str.mk_string("9")), m);
            expr_ref re_plus(m_seq.re.mk_plus(re_digit), m);
            expr_ref in_re(m_seq.re.mk_in_re(s, re_plus), m);
            expr_ref ge0(m_autil.mk_ge(stoi_e, m_autil.mk_int(0)), m);

            literal lit_in  = mk_literal(in_re);
            literal lit_ge0 = mk_literal(ge0);
            ctx.mark_as_relevant(lit_in);
            ctx.mark_as_relevant(lit_ge0);

            // stoi(s) >= 0 => s ∈ [0-9]+
            {
                literal clause[] = { ~lit_ge0, lit_in };
                ctx.mk_th_axiom(get_id(), 2, clause);
            }
            // s ∈ [0-9]+ => stoi(s) >= 0
            {
                literal clause[] = { ~lit_in, lit_ge0 };
                ctx.mk_th_axiom(get_id(), 2, clause);
            }
        }

        // Track for coherence check
        if (!m_stoi_set.contains(stoi_e)) {
            m_stoi_set.insert(stoi_e);
            ctx.push_trail(insert_obj_trail(m_stoi_set, stoi_e));
            ctx.push_trail(restore_vector(m_stoi_terms));
            m_stoi_terms.push_back(stoi_e);
        }
    }

    // Returns true if no new axioms were needed (FC_DONE is safe to return),
    // false if the inductive stoi axiom was instantiated (caller should FC_CONTINUE).
    bool theory_nseq::check_stoi_coherence() {
        if (m_stoi_terms.empty())
            return true;

        bool progress = false;

        for (expr* stoi_e : m_stoi_terms) {
            expr* s = nullptr;
            VERIFY(m_seq.str.is_stoi(stoi_e, s));

            expr_ref len_expr(m_seq.str.mk_length(s), m);
            rational val;
            if (!m_arith_value.get_value(len_expr, val) || !val.is_unsigned())
                continue;

            unsigned k = val.get_unsigned();
            if (k == 0)
                continue;  // empty string: handled by basic axiom stoi("") = -1

            // Only instantiate if we haven't yet done so at this depth
            unsigned prev_k = 0;
            if (m_stoi_depth.contains(stoi_e))
                prev_k = m_stoi_depth[stoi_e];
            if (prev_k >= k)
                continue;

            TRACE(seq, tout << "nseq stoi coherence: instantiating depth " << k
                            << " for " << mk_pp(stoi_e, m) << "\n");
            IF_VERBOSE(1, verbose_stream() << "nseq stoi coherence: instantiating depth "
                                           << k << " for " << mk_pp(stoi_e, m) << "\n";);

            // Positional unfolding: stoi(s, i) = 10*stoi(s, i-1) + digit(s[i])
            m_axioms.stoi_axiom(stoi_e, k);

            // Explicit upper bound: len(s)=k && stoi(s) >= 0 => stoi(s) <= 10^k-1
            // (digit2int for symbolic characters has no arith bounds, so the
            //  positional unfolding alone does not constrain stoi(s) sufficiently)
            {
                rational max_val(1);
                for (unsigned i = 0; i < k; ++i) {
                    max_val *= 10;
                }
                --max_val;  // 10^k - 1
                expr_ref le_max(m_autil.mk_le(stoi_e, m_autil.mk_int(max_val)), m);
                expr_ref ge0(m_autil.mk_ge(stoi_e, m_autil.mk_int(0)), m);
                expr_ref len_eq_k(m.mk_eq(len_expr, m_autil.mk_int(k)), m);

                literal lit_ge0    = mk_literal(ge0);
                literal lit_le_max = mk_literal(le_max);
                literal lit_len_eq = mk_literal(len_eq_k);
                ctx.mark_as_relevant(lit_ge0);
                ctx.mark_as_relevant(lit_le_max);
                ctx.mark_as_relevant(lit_len_eq);

                literal clause[] = { ~lit_len_eq, ~lit_ge0, lit_le_max };
                ctx.mk_th_axiom(get_id(), 3, clause);
            }

            if (m_stoi_depth.contains(stoi_e)) {
                unsigned prev = m_stoi_depth[stoi_e];
                ctx.push_trail(remove_obj_map(m_stoi_depth, stoi_e, prev));
                m_stoi_depth.remove(stoi_e);
            }
            ctx.push_trail(insert_obj_map(m_stoi_depth, stoi_e));
            m_stoi_depth.insert(stoi_e, k);
            progress = true;
        }
        return !progress;
    }

    bool theory_nseq::check_length_coherence() {
        if (m_relevant_lengths.empty())
            // TODO: Make use of this; so far we always introduce lengths always
            return true;

        SASSERT(m_nielsen.sat_node());

        auto const &mems = m_nielsen.sat_node()->str_mems();
        if (mems.empty())
            return true;

        u_map<unsigned_vector> var_to_mems;
        for (unsigned i = 0; i < mems.size(); ++i) {
            auto const &mem = mems[i];
            SASSERT(mem.well_formed());
            SASSERT(mem.is_primitive());
            auto &vec = var_to_mems.insert_if_not_there(mem.m_str->id(), unsigned_vector());
            vec.push_back(i);
        }

        SASSERT(!var_to_mems.empty());

        for (expr* len_expr : m_relevant_lengths) {
            expr* s = nullptr;
            VERIFY(m_seq.str.is_length(len_expr, s));

            euf::snode const* s_node = m_sg.find(s);
            SASSERT(s_node);

            unsigned var_id = s_node->id();
            if (!var_to_mems.contains(var_id))
                continue;

            rational val_l;
            if (!get_num_value(len_expr, val_l))
                continue;

            SASSERT(val_l.is_unsigned());

            // unless we intervene, the integer solver will take this length
            // so check if we really want this value
            const unsigned l = val_l.get_unsigned();

            unsigned_vector const &mem_indices = var_to_mems[var_id];
            euf::snode_vector regexes;
            bool has_view_or_guard = false;
            for (auto i : mem_indices) {
                SASSERT(mems[i].well_formed());
                regexes.push_back(mems[i].m_regex);
                // Synthetic cycle variables carry a stabilizer view / cycle guard
                // (Section 3.3) rather than a real regex; skip length coherence.
                if (!mems[i].is_plain())
                    has_view_or_guard = true;
            }

            // Skip length coherence for synthetic cycle variables constrained by a
            // stabilizer view / cycle guard (x'∈stab(R), noloop(x'',R)) introduced
            // by cycle decomposition: the Σ^l ∩ view gradient does not converge,
            // the benchmark has no real length constraints, and their length
            // consistency is guaranteed by the soundness of the decomposition.
            if (has_view_or_guard)
                continue;

            SASSERT(!regexes.empty());
            sort *ele_sort;
            VERIFY(m_seq.is_seq(m_sg.get_str_sort(), ele_sort));
            unsigned g = 1;
            if (m_gradient_cache.contains(s))
                g = m_gradient_cache[s];
            else
                m_gradient_cache.insert(s, 1);

            expr_ref allchar(m_seq.re.mk_full_char(m_seq.re.mk_re(m_sg.get_str_sort())), m);
            expr_ref l_expr(m_autil.mk_int(l), m);
            expr_ref loop_l(m_seq.re.mk_loop_proper(allchar.get(), l, l), m);

            euf::snode const* sigmal_node = get_snode(loop_l.get());
            regexes.push_back(sigmal_node);
            SASSERT(regexes.size() > 1);

            lbool result = m_regex.check_intersection_emptiness(regexes);

            if (result == l_true) {
                // TODO: Incorporate that we might know the maximum length generated by a regex [in those cases, the
                // gradients will never work] It is empty. Try gradient.
                regexes.pop_back();  // Remove loop_l

                expr_ref loop_g(m_seq.re.mk_loop_proper(allchar.get(), g, g), m);
                expr_ref star_g(m_seq.re.mk_star(loop_g.get()), m);
                expr_ref sigmal_g_expr(m_seq.re.mk_concat(loop_l.get(), star_g.get()), m);

                euf::snode const* sigmal_g_node = get_snode(sigmal_g_expr.get());
                regexes.push_back(sigmal_g_node);

                lbool result_g = m_regex.check_intersection_emptiness(regexes);

                expr_ref prop_expr(m);
                if (result_g == l_true) {
                    // Block the whole gradient
                    expr_ref g_expr(m_autil.mk_int(g), m);
                    expr_ref len_lt_l(m_autil.mk_lt(len_expr, l_expr), m);
                    expr_ref len_minus_l(m_autil.mk_sub(len_expr, l_expr), m);
                    expr_ref not_divides(m.mk_not(m_autil.mk_divides(g_expr, len_minus_l)), m);
                    prop_expr = m.mk_or(len_lt_l, not_divides);
                    m_th_rewriter(prop_expr);  // the divisibility predicate needs to be rewritten as it won't happen
                                               // automatically

                    m_gradient_cache[s] = 1;  // Reset gradient cache
                }
                else {
                    prop_expr = m.mk_not(m.mk_eq(len_expr, l_expr));
                    m_gradient_cache[s] = g + 1;  // Increment gradient cache
                }

                if (!ctx.b_internalized(prop_expr))
                    ctx.internalize(prop_expr, true);
                literal lit_prop = ctx.get_literal(prop_expr);

                enode_pair_vector eqs;
                literal_vector dep_lits;

                for (unsigned idx : mem_indices) {
                    std::cout << seq::mem_pp(mems[idx], m) << std::endl;
                    seq::deps_to_lits(m_nielsen.dep_mgr(), mems[idx].m_dep, eqs, dep_lits);
                }
                

                set_propagate(eqs, dep_lits, lit_prop);

                TRACE(seq, tout << "nseq length coherence check: length " << l << " with gradient " << g
                                << " is incompatible for " << mk_pp(s, m) << ", propagated " << mk_pp(prop_expr, m)
                                << "\n";);
                IF_VERBOSE(1, verbose_stream() << "nseq length coherence check: length " << l << " with gradient " << g
                                               << " is incompatible for " << mk_pp(s, m) << ", propagated "
                                               << mk_pp(prop_expr, m) << "\n";);
                return false;
            }
        }

        return true;
    }

    // -----------------------------------------------------------------------
    // Use theory assumptions to bound search depth and force literal assignments
    // m_assumption_lit gets added as an assumption to the set of existing assumptions.
    // If it is part of a core, a the epoch of the assumption literal is increased
    // such that the current core can be unblocked in the next round of search.
    // 
    // Suppose we would like to force a literal lit_i
    // We would assert:
    //     m_assumption_lit => lit_i
    // If there is an infeasible subset containing m_assumption_lit, one
    // or more of the forced literals is conflicting and have to be relaxed.
    // 
    // A base level scheme for using forced literals can be as follows:
    // We can keep track of the set of forced literals lit_i that were implied by m_assumption_lit
    // in a given round. Then we can selectively force each of these to learn exactly which are
    // part of a core.
    // Say they are lit_1, lit_2, lit_3.
    // Let us mark lit_1 as tabu. 
    // Literals that are marked as tabu will not be forced in subsequent rounds of final_check_eh.
    // 
    // -----------------------------------------------------------------------

    bool theory_nseq::should_research(expr_ref_vector& core) {
        for (auto c : core)
            if (m_axioms.sk().is_max_unfolding(c)) {
                // one or more of the "m_nielsen_literals" cannot be forced.
                ctx.push_trail(value_trail(m_max_unfolding_depth));
                ++m_max_unfolding_depth;                
                return true;
            }
        return false;
    }

    void theory_nseq::add_theory_assumptions(expr_ref_vector& assumptions) {
        if (m_seq.has_seq()) {
            expr_ref dlimit = m_axioms.sk().mk_max_unfolding_depth(m_max_unfolding_depth);
            ctx.push_trail(value_trail(m_assumption_lit));
            m_assumption_lit = mk_literal(dlimit);
            assumptions.push_back(std::move(dlimit));
        }
    }
    
}
  
