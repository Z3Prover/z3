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

namespace smt {

    theory_nseq::theory_nseq(context& ctx) :
        theory(ctx, ctx.get_manager().mk_family_id("seq")),
        m_seq(m),
        m_autil(m),
        m_rewriter(m),
        m_arith_value(m),
        m_egraph(m),
        m_sgraph(m, m_egraph),
        m_context_solver(m),
        m_nielsen(m_sgraph, m_context_solver),
        m_state(),
        m_regex(m_sgraph),
        m_model(m, m_seq, m_rewriter, m_sgraph)
    {}

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

        return true;
    }

    // -----------------------------------------------------------------------
    // Equality / disequality notifications
    // -----------------------------------------------------------------------

    void theory_nseq::new_eq_eh(theory_var v1, theory_var v2) {
        expr* e1 = get_enode(v1)->get_expr();
        expr* e2 = get_enode(v2)->get_expr();
        if (m_seq.is_re(e1)) {
            push_unhandled_pred();
            return;
        }
        if (!m_seq.is_seq(e1) || !m_seq.is_seq(e2))
            return;
        euf::snode* s1 = get_snode(e1);
        euf::snode* s2 = get_snode(e2);
        if (s1 && s2) {
            unsigned idx = m_state.str_eqs().size();
            m_state.add_str_eq(s1, s2, get_enode(v1), get_enode(v2));
            ctx.push_trail(restore_vector(m_prop_queue));
            m_prop_queue.push_back({prop_item::eq_prop, idx});
        }
    }

    void theory_nseq::new_diseq_eh(theory_var v1, theory_var v2) {
        expr* e1 = get_enode(v1)->get_expr();
        expr* e2 = get_enode(v2)->get_expr();
        if (m_seq.is_re(e1)) {
            // regex disequality: nseq cannot verify language non-equivalence
            push_unhandled_pred();
            return;
        }
        if (!m_seq.is_seq(e1) || !m_seq.is_seq(e2))
            return;
        unsigned idx = m_state.diseqs().size();
        m_state.add_diseq(get_enode(v1), get_enode(v2));
        ctx.push_trail(restore_vector(m_prop_queue));
        m_prop_queue.push_back({prop_item::diseq_prop, idx});
    }

    // -----------------------------------------------------------------------
    // Boolean assignment notification
    // -----------------------------------------------------------------------

    void theory_nseq::assign_eh(bool_var v, bool is_true) {
        expr* e = ctx.bool_var2expr(v);
        expr* s = nullptr;
        expr* re = nullptr;
        if (!m_seq.str.is_in_re(e, s, re)) {
            // Track unhandled boolean string predicates (prefixof, contains, etc.)
            if (is_app(e) && to_app(e)->get_family_id() == m_seq.get_family_id())
                push_unhandled_pred();
            return;
        }
        euf::snode* sn_str = get_snode(s);
        euf::snode* sn_re  = get_snode(re);
        if (!sn_str || !sn_re)
            return;

        unsigned idx = m_state.str_mems().size();
        literal lit(v, !is_true);
        if (is_true) {
            m_state.add_str_mem(sn_str, sn_re, lit);
        }
        else {
            // ¬(str ∈ R)  ≡  str ∈ complement(R): store as a positive membership
            // so the Nielsen graph sees it uniformly; the original negative literal
            // is kept in mem_source for conflict reporting.
            expr_ref re_compl(m_seq.re.mk_complement(re), m);
            euf::snode* sn_re_compl = get_snode(re_compl.get());
            m_state.add_str_mem(sn_str, sn_re_compl, lit);
        }
        ctx.push_trail(restore_vector(m_prop_queue));
        m_prop_queue.push_back({prop_item::pos_mem_prop, idx});

        TRACE(seq, tout << "nseq assign_eh: " << (is_true ? "" : "¬")
                        << "str.in_re "
                        << mk_bounded_pp(s, m, 3) << " in "
                        << mk_bounded_pp(re, m, 3) << "\n";);
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
        if (m_prop_qhead == m_prop_queue.size())
            return;
        ctx.push_trail(value_trail(m_prop_qhead));
        while (m_prop_qhead < m_prop_queue.size() && !ctx.inconsistent()) {
            auto [k, idx] = m_prop_queue[m_prop_qhead++];
            switch (k) {
            case prop_item::eq_prop:
                propagate_eq(idx);
                break;
            case prop_item::diseq_prop:
                propagate_diseq(idx);
                break;
            case prop_item::pos_mem_prop:
                propagate_pos_mem(idx);
                break;
            }
        }
    }

    void theory_nseq::propagate_eq(unsigned idx) {
        // When s1 = s2 is learned, ensure len(s1) and len(s2) are
        // internalized so congruence closure propagates len(s1) = len(s2).
        eq_source const& src = m_state.get_eq_source(idx);
        ensure_length_var(src.m_n1->get_expr());
        ensure_length_var(src.m_n2->get_expr());
    }

    void theory_nseq::propagate_diseq(unsigned idx) {
        // Disequalities are recorded for use during final_check.
        // No eager propagation beyond recording.
        TRACE(seq,
            auto const& d = m_state.get_diseq(idx);
            tout << "nseq diseq: "
                 << mk_bounded_pp(d.m_n1->get_expr(), m, 3)
                 << " != "
                 << mk_bounded_pp(d.m_n2->get_expr(), m, 3) << "\n";);
    }

    void theory_nseq::propagate_pos_mem(unsigned idx) {
        auto const& mem = m_state.str_mems()[idx];
        auto const& src = m_state.get_mem_source(idx);

        if (!mem.m_str || !mem.m_regex)
            return;

        // regex is ∅ → conflict
        if (m_regex.is_empty_regex(mem.m_regex)) {
            enode_pair_vector eqs;
            literal_vector lits;
            lits.push_back(src.m_lit);
            set_conflict(eqs, lits);
            return;
        }

        // empty string in non-nullable regex → conflict
        if (mem.m_str->is_empty() && !mem.m_regex->is_nullable()) {
            enode_pair_vector eqs;
            literal_vector lits;
            lits.push_back(src.m_lit);
            set_conflict(eqs, lits);
            return;
        }

        // ensure length term exists for the string argument
        expr* s_expr = mem.m_str->get_expr();
        if (s_expr)
            ensure_length_var(s_expr);
    }

    void theory_nseq::ensure_length_var(expr* e) {
        if (!e || !m_seq.is_seq(e))
            return;
        expr_ref len(m_seq.str.mk_length(e), m);
        if (!ctx.e_internalized(len))
            ctx.internalize(len, false);
    }

    // -----------------------------------------------------------------------
    // Final check: build Nielsen graph and search
    // -----------------------------------------------------------------------

    void theory_nseq::populate_nielsen_graph() {
        m_nielsen.reset();
        m_nielsen_to_state_mem.reset();

        // transfer string equalities from state to nielsen graph root
        for (auto const& eq : m_state.str_eqs()) {
            m_nielsen.add_str_eq(eq.m_lhs, eq.m_rhs);
        }

        // transfer regex memberships, pre-processing through seq_regex
        // to consume ground prefixes via Brzozowski derivatives
        for (unsigned state_idx = 0; state_idx < m_state.str_mems().size(); ++state_idx) {
            auto const& mem = m_state.str_mems()[state_idx];
            int triv = m_regex.check_trivial(mem);
            if (triv > 0)
                continue;  // trivially satisfied, skip
            if (triv < 0) {
                // trivially unsat: add anyway so solve() detects conflict
                m_nielsen.add_str_mem(mem.m_str, mem.m_regex);
                m_nielsen_to_state_mem.push_back(state_idx);
                continue;
            }
            // pre-process: consume ground prefix characters
            vector<seq::str_mem> processed;
            if (!m_regex.process_str_mem(mem, processed)) {
                // conflict during ground prefix consumption
                m_nielsen.add_str_mem(mem.m_str, mem.m_regex);
                m_nielsen_to_state_mem.push_back(state_idx);
                continue;
            }
            for (auto const& pm : processed) {
                m_nielsen.add_str_mem(pm.m_str, pm.m_regex);
                m_nielsen_to_state_mem.push_back(state_idx);
            }
        }

        TRACE(seq, tout << "nseq populate: " << m_state.str_eqs().size() << " eqs, "
                        << m_state.str_mems().size() << " mems -> nielsen root with "
                        << m_nielsen.num_input_eqs() << " eqs, "
                        << m_nielsen.num_input_mems() << " mems\n";);
    }

    final_check_status theory_nseq::final_check_eh(unsigned /*final_check_round*/) {
        // Always assert non-negativity for all string theory vars,
        // even when there are no string equations/memberships.
        if (assert_nonneg_for_all_vars()) {
            IF_VERBOSE(1, verbose_stream() << "nseq final_check: nonneg assertions added, FC_CONTINUE\n";);
            return FC_CONTINUE;
        }

        if (m_state.empty() && m_ho_terms.empty() && !has_unhandled_preds()) {
            IF_VERBOSE(1, verbose_stream() << "nseq final_check: empty state+ho, FC_DONE (no solve)\n";);
            return FC_DONE;
        }

        // unfold higher-order terms when sequence structure is known
        if (unfold_ho_terms()) {
            IF_VERBOSE(1, verbose_stream() << "nseq final_check: unfolded ho_terms, FC_CONTINUE\n";);
            return FC_CONTINUE;
        }

        if (m_state.empty() && !has_unhandled_preds()) {
            IF_VERBOSE(1, verbose_stream() << "nseq final_check: empty state (after ho), FC_DONE (no solve)\n";);
            return FC_DONE;
        }

        IF_VERBOSE(1, verbose_stream() << "nseq final_check: populating graph with "
            << m_state.str_eqs().size() << " eqs, " << m_state.str_mems().size() << " mems\n";);
        populate_nielsen_graph();

        // assert length constraints derived from string equalities
        if (assert_length_constraints()) {
            IF_VERBOSE(1, verbose_stream() << "nseq final_check: length constraints asserted, FC_CONTINUE\n";);
            return FC_CONTINUE;
        }

        ++m_num_final_checks;

        m_nielsen.set_max_search_depth(get_fparams().m_nseq_max_depth);
        m_nielsen.set_max_nodes(get_fparams().m_nseq_max_nodes);
        m_nielsen.set_parikh_enabled(get_fparams().m_nseq_parikh);

        // Regex membership pre-check: before running DFS, check intersection
        // emptiness for each variable's regex constraints.  This handles
        // regex-only problems that the DFS cannot efficiently solve.
        if (get_fparams().m_nseq_regex_precheck) {
            lbool precheck = check_regex_memberships_precheck();
            switch (precheck) { 
            case l_true:
                // conflict was asserted inside check_regex_memberships_precheck
                IF_VERBOSE(1, verbose_stream() << "nseq final_check: regex precheck UNSAT\n";);
                return FC_CONTINUE;
            case l_false:
                // all regex constraints satisfiable, no word eqs/diseqs → SAT
                IF_VERBOSE(1, verbose_stream() << "nseq final_check: regex precheck SAT\n";);
                return FC_DONE;
            default: 
                break;
            }
        }

        IF_VERBOSE(1, verbose_stream() << "nseq final_check: calling solve()\n";);

        // here the actual Nielsen solving happens
        auto result = m_nielsen.solve();

#ifdef Z3DEBUG
        // Examining the Nielsen graph is probably the best way of debugging
        std::string dot = m_nielsen.to_dot();
        IF_VERBOSE(1, verbose_stream() << dot << "\n";);
#endif

        if (result == seq::nielsen_graph::search_result::unsat) {
            IF_VERBOSE(1, verbose_stream() << "nseq final_check: solve UNSAT\n";);
            explain_nielsen_conflict();
            return FC_CONTINUE;
        }

        if (result == seq::nielsen_graph::search_result::sat) {
            IF_VERBOSE(1, verbose_stream() << "nseq final_check: solve SAT, sat_node="
                << (m_nielsen.sat_node() ? "set" : "null") << "\n";);
            // Nielsen found a consistent assignment for positive constraints.
            // If there are disequalities we haven't verified, we cannot soundly declare sat.
            if (!m_state.diseqs().empty())
                return FC_GIVEUP;
            if (!has_unhandled_preds())
                return FC_DONE;
        }

        IF_VERBOSE(1, verbose_stream() << "nseq final_check: solve UNKNOWN, FC_GIVEUP\n";);
        return FC_GIVEUP;
    }

    // -----------------------------------------------------------------------
    // Conflict explanation
    // -----------------------------------------------------------------------

    void theory_nseq::deps_to_lits(seq::dep_tracker const& deps, enode_pair_vector& eqs, literal_vector& lits) {
        vector<seq::dep_source, false> vs;
        m_nielsen.dep_mgr().linearize(deps, vs);
        for (seq::dep_source const& d : vs) {
            if (d.m_kind == seq::dep_source::kind::eq) {
                eq_source const& src = m_state.get_eq_source(d.index);
                if (src.m_n1->get_root() == src.m_n2->get_root())
                    eqs.push_back({src.m_n1, src.m_n2});
            }
            else {
                if (d.index < m_nielsen_to_state_mem.size()) {
                    unsigned state_mem_idx = m_nielsen_to_state_mem[d.index];
                    mem_source const& src = m_state.get_mem_source(state_mem_idx);
                    SASSERT(ctx.get_assignment(src.m_lit) == l_true);
                    lits.push_back(src.m_lit);
                }
            }
        }
    }

    void theory_nseq::add_conflict_clause(seq::dep_tracker const& deps) {
        enode_pair_vector eqs;
        literal_vector lits;
        deps_to_lits(deps, eqs, lits);
        ++m_num_conflicts;
        set_conflict(eqs, lits);
    }

    void theory_nseq::explain_nielsen_conflict() {
        seq::dep_tracker deps = m_nielsen.dep_mgr().mk_empty();
        m_nielsen.collect_conflict_deps(deps);
        add_conflict_clause(deps);
    }

    void theory_nseq::set_conflict(enode_pair_vector const& eqs, literal_vector const& lits) {
        TRACE(seq, tout << "nseq conflict: " << eqs.size() << " eqs, " << lits.size() << " lits\n";);
        ctx.set_conflict(
            ctx.mk_justification(
                ext_theory_conflict_justification(
                    get_id(), ctx, lits.size(), lits.data(), eqs.size(), eqs.data(), 0, nullptr)));
    }

    // -----------------------------------------------------------------------
    // Model generation
    // -----------------------------------------------------------------------

    void theory_nseq::init_model(model_generator& mg) {
        m_model.init(mg, m_nielsen, m_state);
    }

    model_value_proc* theory_nseq::mk_value(enode* n, model_generator& mg) {
        return m_model.mk_value(n, mg);
    }

    void theory_nseq::finalize_model(model_generator& mg) {
        m_model.finalize(mg);
    }

    void theory_nseq::validate_model(proto_model& mdl) {
        m_model.validate_regex(m_state, mdl);
    }

    // -----------------------------------------------------------------------
    // Statistics / display
    // -----------------------------------------------------------------------

    void theory_nseq::collect_statistics(::statistics& st) const {
        st.update("nseq conflicts",       m_num_conflicts);
        st.update("nseq final checks",    m_num_final_checks);
        st.update("nseq length axioms",   m_num_length_axioms);
        st.update("nseq ho unfolds",      m_num_ho_unfolds);
        m_nielsen.collect_statistics(st);
    }

    void theory_nseq::display(std::ostream& out) const {
        out << "theory_nseq\n";
        out << "  str_eqs:    " << m_state.str_eqs().size() << "\n";
        out << "  str_mems:   " << m_state.str_mems().size() << "\n";
        out << "  diseqs:     " << m_state.diseqs().size() << "\n";
        out << "  prop_queue: " << m_prop_qhead << "/" << m_prop_queue.size() << "\n";
        out << "  ho_terms:   " << m_ho_terms.size() << "\n";
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

    euf::snode* theory_nseq::get_snode(expr* e) {
        euf::snode* s = m_sgraph.find(e);
        if (!s)
            s = m_sgraph.mk(e);
        return s;
    }

    // -----------------------------------------------------------------------
    // Arithmetic value queries
    // -----------------------------------------------------------------------

    bool theory_nseq::get_num_value(expr* e, rational& val) const {
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

    bool theory_nseq::get_length(expr* e, rational& val) {
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
        deps_to_lits(lc.m_dep, eqs, lits);

        ctx.mark_as_relevant(lit);
        justification* js = ctx.mk_justification(
            ext_theory_propagation_justification(
                get_id(), ctx,
                lits.size(), lits.data(),
                eqs.size(), eqs.data(),
                lit));
        ctx.assign(lit, js);

        TRACE(seq, tout << "nseq length propagation: " << mk_pp(lc.m_expr, m)
                        << " (" << eqs.size() << " eqs, " << lits.size() << " lits)\n";);
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
                TRACE(seq, tout << "nseq length lemma: " << mk_pp(e, m) << "\n";);
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
        auto const& mems = m_state.str_mems();
        if (mems.empty())
            return l_undef;

        // Group membership indices by variable snode id.
        // Only consider memberships whose string snode is a plain variable (s_var).
        u_map<unsigned_vector> var_to_mems;
        bool all_var_str = true;

        for (unsigned i = 0; i < mems.size(); ++i) {
            auto const& mem = mems[i];
            if (!mem.m_str || !mem.m_regex)
                continue;
            if (mem.m_str->is_var()) {
                auto& vec = var_to_mems.insert_if_not_there(mem.m_str->id(), unsigned_vector());
                vec.push_back(i);
            }
            else
                all_var_str = false;
        }

        if (var_to_mems.empty())
            return l_undef;

        bool any_undef = false;

        // Check intersection emptiness for each variable.
        for (auto& kv : var_to_mems) {
            unsigned var_id = kv.m_key;
            unsigned_vector const& mem_indices = kv.m_value;
            ptr_vector<euf::snode> regexes;
            for (unsigned i : mem_indices) {
                euf::snode* re = mems[i].m_regex;
                if (re)
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
                enode_pair_vector eqs;
                literal_vector lits;
                for (unsigned i : mem_indices) {
                    mem_source const& src = m_state.get_mem_source(i);
                    SASSERT(ctx.get_assignment(src.m_lit) == l_true); // we already stored the polarity of the literal
                    lits.push_back(src.m_lit);
                }
                TRACE(seq, tout << "nseq regex precheck: empty intersection for var "
                                << var_id << ", conflict with " << lits.size() << " lits\n";);
                set_conflict(eqs, lits);
                return l_true;   // conflict asserted
            }
            if (result == l_undef)
                any_undef = true;
            // l_false = non-empty intersection, this variable's constraints are satisfiable
        }

        if (any_undef)
            return l_undef;  // cannot fully determine; let DFS decide

        // All variables' regex intersections are non-empty.
        // If there are no word equations and no disequalities, variables are
        // independent and each can be assigned a witness string → SAT.
        if (all_var_str && m_state.str_eqs().empty() && m_state.diseqs().empty() && !has_unhandled_preds()) {
            TRACE(seq, tout << "nseq regex precheck: all intersections non-empty, "
                            << "no word eqs/diseqs → SAT\n";);
            return l_false;  // signals SAT (non-empty / satisfiable)
        }

        return l_undef;  // mixed constraints; let DFS decide
    }

}
