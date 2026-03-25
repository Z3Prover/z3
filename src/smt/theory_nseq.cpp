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
        m_th_rewriter(m),
        m_rewriter(m),
        m_arith_value(m),
        m_egraph(m),
        m_sgraph(m, m_egraph),
        m_context_solver(m),
        m_nielsen(m_sgraph, m_context_solver),
        m_axioms(m_th_rewriter),
        m_regex(m_sgraph),
        m_model(m, m_seq, m_rewriter, m_sgraph)
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
        // std::cout << mk_pp(e1, m) << " = " << mk_pp(e2, m) << std::endl;
        if (m_seq.is_re(e1)) {
            push_unhandled_pred();
            return;
        }
        if (!m_seq.is_seq(e1) || !m_seq.is_seq(e2))
            return;
        euf::snode* s1 = get_snode(e1);
        euf::snode* s2 = get_snode(e2);
        if (s1 && s2) {
            seq::dep_tracker dep = nullptr;
            ctx.push_trail(restore_vector(m_prop_queue));
            m_prop_queue.push_back(eq_item(s1, s2, get_enode(v1), get_enode(v2), dep));}
    }

    void theory_nseq::new_diseq_eh(theory_var v1, theory_var v2) {
        expr* e1 = get_enode(v1)->get_expr();
        expr* e2 = get_enode(v2)->get_expr();
        TRACE(seq, tout << mk_pp(e1, m) << " != " << mk_pp(e2, m) << "\n");
        if (m_seq.is_re(e1))
            // regex disequality: nseq cannot verify language non-equivalence
            push_unhandled_pred();
        else if (m_seq.is_seq(e1) && !m_no_diseq_set.contains(e1) && !m_no_diseq_set.contains(e2))
            m_axioms.diseq_axiom(e1, e2);
        else
            ;
    }

    // -----------------------------------------------------------------------
    // Boolean assignment notification
    // -----------------------------------------------------------------------

    void theory_nseq::assign_eh(bool_var v, bool is_true) {
        expr* e = ctx.bool_var2expr(v);
        // std::cout << "assigned " << mk_pp(e, m) << " = " << is_true << std::endl;
        expr* s = nullptr, *re = nullptr;
        TRACE(seq, tout << (is_true ? "" : "¬") << mk_bounded_pp(e, m, 3) << "\n";);
        if (m_seq.str.is_in_re(e, s, re)) {
            euf::snode* sn_str = get_snode(s);
            euf::snode* sn_re  = get_snode(re);
            if (!sn_str || !sn_re)
                return;
            literal lit(v, !is_true);
            seq::dep_tracker dep = nullptr;
            if (is_true) {
                ctx.push_trail(restore_vector(m_prop_queue));
                m_prop_queue.push_back(mem_item(sn_str, sn_re, lit, nullptr, m_next_mem_id++, dep));
            }
            else {
                // ¬(str ∈ R)  ≡  str ∈ complement(R): store as a positive membership
                // so the Nielsen graph sees it uniformly; the original negative literal
                // is kept in mem_source for conflict reporting.
                expr_ref re_compl(m_seq.re.mk_complement(re), m);
                euf::snode* sn_re_compl = get_snode(re_compl.get());
                ctx.push_trail(restore_vector(m_prop_queue));
                m_prop_queue.push_back(mem_item(sn_str, sn_re_compl, lit, nullptr, m_next_mem_id++, dep));
            }
        }
        else if (m_seq.str.is_prefix(e)) {
            if (is_true)
                m_axioms.prefix_true_axiom(e);
            else
                m_axioms.prefix_axiom(e);
        }
        else if (m_seq.str.is_suffix(e)) {
            if (is_true)
                m_axioms.suffix_true_axiom(e);
            else
                m_axioms.suffix_axiom(e);
        }
        else if (m_seq.str.is_contains(e)) {
            if (is_true)
                m_axioms.contains_true_axiom(e);
            else
                m_axioms.not_contains_axiom(e);
        }
        else if (m_seq.str.is_lt(e) || m_seq.str.is_le(e)) {
            // axioms added via relevant_eh → dequeue_axiom
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

    // -----------------------------------------------------------------------
    // Scope management
    // -----------------------------------------------------------------------

    void theory_nseq::push_scope_eh() {
        theory::push_scope_eh();
        m_sgraph.push();
        
    }

    void theory_nseq::pop_scope_eh(unsigned num_scopes) {
        theory::pop_scope_eh(num_scopes);
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
            auto const& item = m_prop_queue[m_prop_qhead++];
            if (std::holds_alternative<eq_item>(item))
                propagate_eq(std::get<eq_item>(item));
            else if (std::holds_alternative<mem_item>(item))
                propagate_pos_mem(std::get<mem_item>(item));
            else if (std::holds_alternative<axiom_item>(item))
                dequeue_axiom(std::get<axiom_item>(item).e);
            else {
                UNREACHABLE();
            }
        }
    }

    void theory_nseq::propagate_eq(tracked_str_eq const& eq) {
        // When s1 = s2 is learned, ensure len(s1) and len(s2) are
        // internalized so congruence closure propagates len(s1) = len(s2).
        ensure_length_var(eq.m_l->get_expr());
        ensure_length_var(eq.m_r->get_expr());
    }

    void theory_nseq::propagate_pos_mem(tracked_str_mem const& mem) {

        if (!mem.m_str || !mem.m_regex)
            return;

        // regex is ∅ → conflict
        if (m_regex.is_empty_regex(mem.m_regex)) {
            enode_pair_vector eqs;
            literal_vector lits;
            lits.push_back(mem.lit);
            set_conflict(eqs, lits);
            return;
        }

        // empty string in non-nullable regex → conflict
        if (mem.m_str->is_empty() && !mem.m_regex->is_nullable()) {
            enode_pair_vector eqs;
            literal_vector lits;
            lits.push_back(mem.lit);
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
            m_axioms.stoi_axiom(n);
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

    void theory_nseq::relevant_eh(app* n) {
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

        unsigned num_eqs = 0, num_mems = 0;

        // transfer string equalities and regex memberships from prop_queue to nielsen graph root
        for (auto const& item : m_prop_queue) {
            if (std::holds_alternative<eq_item>(item)) {
                auto const& eq = std::get<eq_item>(item);
                m_nielsen.add_str_eq(eq.m_lhs, eq.m_rhs, eq.m_l, eq.m_r);
                ++num_eqs;
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
                        << num_mems << " mems -> nielsen root\n");
        IF_VERBOSE(1, verbose_stream() << "nseq final_check: populating graph with "
            << num_eqs << " eqs, " << num_mems << " mems\n";);
    }

    final_check_status theory_nseq::final_check_eh(unsigned /*final_check_round*/) {
        // Always assert non-negativity for all string theory vars,
        // even when there are no string equations/memberships.
        if (assert_nonneg_for_all_vars()) {
            IF_VERBOSE(1, verbose_stream() << "nseq final_check: nonneg assertions added, FC_CONTINUE\n";);
            return FC_CONTINUE;
        }

        // Check if there are any eq/mem items in the propagation queue.
        bool has_eq_or_mem = false;
        for (auto const& item : m_prop_queue)
            if (!std::holds_alternative<axiom_item>(item)) { has_eq_or_mem = true; break; }

        // there is nothing to do for the string solver, as there are no string constraints
        if (!has_eq_or_mem && m_ho_terms.empty() && !has_unhandled_preds()) {
            IF_VERBOSE(1, verbose_stream() << "nseq final_check: empty state+ho, FC_DONE (no solve)\n";);
            m_nielsen.reset();
            m_nielsen.create_root();
            m_nielsen.set_sat_node(m_nielsen.root());
            return FC_DONE;
        }

        // unfold higher-order terms when sequence structure is known
        if (unfold_ho_terms()) {
            IF_VERBOSE(1, verbose_stream() << "nseq final_check: unfolded ho_terms, FC_CONTINUE\n";);
            return FC_CONTINUE;
        }

        if (!has_eq_or_mem && !has_unhandled_preds()) {
            IF_VERBOSE(1, verbose_stream() << "nseq final_check: empty state (after ho), FC_DONE (no solve)\n";);
            m_nielsen.reset();
            m_nielsen.create_root();
            m_nielsen.set_sat_node(m_nielsen.root());
            return FC_DONE;
        }

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
        m_nielsen.set_signature_split(get_fparams().m_nseq_signature);

        // Regex membership pre-check: before running DFS, check intersection
        // emptiness for each variable's regex constraints.  This handles     
        // regex-only problems that the DFS cannot efficiently solve.
        if (get_fparams().m_nseq_regex_precheck) {
            switch (check_regex_memberships_precheck()) {
            case l_true:
                // conflict was asserted inside check_regex_memberships_precheck
                IF_VERBOSE(1, verbose_stream() << "nseq final_check: regex precheck UNSAT\n";);
                return FC_CONTINUE;
            case l_false:
                // all regex constraints satisfiable, no word eqs → SAT
                IF_VERBOSE(1, verbose_stream() << "nseq final_check: regex precheck SAT\n";);
                m_nielsen.set_sat_node(m_nielsen.root());
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
        // std::cout << "Got: " << (result == seq::nielsen_graph::search_result::sat ? "sat" : (result == seq::nielsen_graph::search_result::unsat ? "unsat" : "unknown")) << std::endl;
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
            SASSERT(has_eq_or_mem); // we should have axiomatized them
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
        for (seq::dep_source const &d : vs) {
            if (std::holds_alternative<enode_pair>(d))
                eqs.push_back(std::get<enode_pair>(d));
            else
                lits.push_back(std::get<sat::literal>(d));
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
        st.update("nseq conflicts",       m_num_conflicts);
        st.update("nseq final checks",    m_num_final_checks);
        st.update("nseq length axioms",   m_num_length_axioms);
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
        // Collect mem items from the propagation queue into a local pointer array
        // so that indices into the array remain stable during this function.
        ptr_vector<tracked_str_mem const> mems;
        for (auto const& item : m_prop_queue)
            if (std::holds_alternative<mem_item>(item))
                mems.push_back(&std::get<mem_item>(item));

        if (mems.empty())
            return l_undef;

        // Group membership indices by variable snode id.
        // Only consider memberships whose string snode is a plain variable (s_var).
        u_map<unsigned_vector> var_to_mems;
        bool all_primitive = true;

        for (unsigned i = 0; i < mems.size(); ++i) {
            auto const& mem = *mems[i];
            SASSERT(mem.m_str && mem.m_regex);
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
        bool has_eqs = false;
        for (auto const& item : m_prop_queue)
            if (std::holds_alternative<eq_item>(item)) { has_eqs = true; break; }

        bool any_undef = false;

        // Check intersection emptiness for each variable.
        for (auto& kv : var_to_mems) {
            unsigned var_id = kv.m_key;
            unsigned_vector const& mem_indices = kv.m_value;
            ptr_vector<euf::snode> regexes;
            for (unsigned i : mem_indices) {
                euf::snode* re = mems[i]->m_regex;
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
                    SASSERT(ctx.get_assignment(mems[i]->lit) == l_true); // we already stored the polarity of the literal
                    lits.push_back(mems[i]->lit);
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
        // If there are no word equations, variables are independent and
        // each can be assigned a witness string → SAT.
        if (all_primitive && !has_eqs && !has_unhandled_preds()) {
            TRACE(seq, tout << "nseq regex precheck: all intersections non-empty, "
                            << "no word eqs → SAT\n";);
            return l_false;  // signals SAT (non-empty / satisfiable)
        }

        return l_undef;  // mixed constraints; let DFS decide
    }

}
