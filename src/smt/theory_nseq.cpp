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

    namespace {
        literal mk_le_literal(context& ctx, ast_manager& m, arith_util& a, seq::le const& d) {
            SASSERT(d.lhs);
            SASSERT(d.rhs);
            expr_ref le_expr(a.mk_le(d.lhs, d.rhs), m);
            if (!ctx.b_internalized(le_expr))
                ctx.internalize(le_expr, true);
            literal lit = ctx.get_literal(le_expr);
            ctx.mark_as_relevant(lit);
            return lit;
        }
    }

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
        m_core_solver(m),
        m_nielsen(m_sgraph, m_context_solver, m_core_solver),
        m_axioms(m_th_rewriter),
        m_regex(m_sgraph),
        m_model(m, ctx, m_seq, m_rewriter, m_sgraph),
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

        m_should_internalize = true; // delete this if using internalize as fallback
        std::function<sat::literal(expr*)> literal_if_false = [&](expr* e) {
            bool is_not = m.is_not(e, e);
            if (m_should_internalize && !ctx.b_internalized(e)) {
                // it can happen that the element is not internalized, but as soon as we do it, it becomes false.
                // In case we just skip one of those uninternalized expressions,
                // adding the Nielsen assumption later will fail
                // Alternatively, we could just retry Nielsen saturation in case
                // adding the Nielsen assumption yields the assumption being false after internalizing
                ctx.internalize(to_app(e), false);
            }

            if (!ctx.b_internalized(e))
                return sat::null_literal;

            literal lit = ctx.get_literal(e);
            if (is_not)
                lit.neg();
            if (ctx.get_assignment(lit) == l_false) {
                // TRACE(seq, tout << "literal_if_false: " << lit << " " << mk_pp(e, m) << " is assigned false\n");
                return lit;
            }
            // TRACE(seq, tout << "literal_if_false: " << mk_pp(e, m) << " is assigned " << ctx.get_assignment(lit) << "\n");
            return sat::null_literal;
        };

        
        m_nielsen.set_literal_if_false(literal_if_false);
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

    // -----------------------------------------------------------------------
    // Equality / disequality notifications
    // -----------------------------------------------------------------------

    void theory_nseq::new_eq_eh(theory_var v1, theory_var v2) {
        try {
            expr* e1 = get_enode(v1)->get_expr();
            expr* e2 = get_enode(v2)->get_expr();
            TRACE(seq, tout << mk_pp(e1, m) << " == " << mk_pp(e2, m) << "\n");
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
                m_prop_queue.push_back(eq_item(s1, s2, get_enode(v1), get_enode(v2), dep));
            }
        }
        catch(const std::exception&) {
#ifdef Z3DEBUG
            std::string dot = m_nielsen.to_dot();
#endif
            throw;
        }
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
        try {
            expr* e = ctx.bool_var2expr(v);
            // std::cout << "assigned [" << sat::literal(v, is_true) << "] " << mk_pp(e, m) << " = " << is_true << std::endl;
            expr *s = nullptr, *re = nullptr, *a = nullptr, *b = nullptr;
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
                    m_prop_queue.push_back(mem_item(sn_str, sn_re, lit, dep));
                }
                else {
                    // ¬(str ∈ R)  ≡  str ∈ complement(R): store as a positive membership
                    // so the Nielsen graph sees it uniformly; the original negative literal
                    // is kept in mem_source for conflict reporting.
                    expr_ref re_compl(m_seq.re.mk_complement(re), m);
                    euf::snode* sn_re_compl = get_snode(re_compl.get());
                    ctx.push_trail(restore_vector(m_prop_queue));
                    m_prop_queue.push_back(mem_item(sn_str, sn_re_compl, lit, dep));
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
            else if (m_axioms.sk().is_eq(e, a, b) && is_true) {
                enode* n1 = ensure_enode(a);
                enode* n2 = ensure_enode(b);
                auto v1 = mk_var(n1);
                auto v2 = mk_var(n2);
                if (n1->get_root() != n2->get_root()) {
                    literal lit(v, false);
                    ctx.mark_as_relevant(n1);
                    ctx.mark_as_relevant(n2);
                    TRACE(seq, tout << "is-eq " << mk_pp(a, m) << " == " << mk_pp(b, m) << "\n");
                    justification* js = ctx.mk_justification(
                        ext_theory_eq_propagation_justification(
                            get_id(), ctx, 1, &lit, 0, nullptr, n1, n2));
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
        m_sgraph.push();
        
    }

    void theory_nseq::pop_scope_eh(unsigned num_scopes) {
        try {
            theory::pop_scope_eh(num_scopes);
            m_sgraph.pop(num_scopes);
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
        catch(const std::exception&) {
#ifdef Z3DEBUG
            std::string dot = m_nielsen.to_dot();
#endif
            throw;
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
        if (mem.m_str->is_empty() && m_seq.re.get_info(mem.m_regex->get_expr()).nullable == l_false) {
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

        if (!get_fparams().m_nseq_regex_factorization)
            return;

        // Boolean Closure Propagations
        expr* re_expr = mem.m_regex->get_expr();
        if (m_seq.re.is_intersection(re_expr)) {
            for (expr* arg : *to_app(re_expr)) {
                expr_ref in_r(m_seq.re.mk_in_re(s_expr, arg), m);
                literal_vector lits;
                lits.push_back(~mem.lit);
                lits.push_back(mk_literal(in_r));
                ctx.mk_th_axiom(get_id(), lits.size(), lits.data());
            }
        }
        else if (m_seq.re.is_union(re_expr)) {
            literal_vector lits;
            lits.push_back(~mem.lit);
            for (expr* arg : *to_app(re_expr)) {
                expr_ref in_r(m_seq.re.mk_in_re(s_expr, arg), m);
                lits.push_back(mk_literal(in_r));
            }
            ctx.mk_th_axiom(get_id(), lits.size(), lits.data());
        }
        else if (m_seq.re.is_complement(re_expr)) {
            expr* arg = to_app(re_expr)->get_arg(0);
            expr_ref in_r(m_seq.re.mk_in_re(s_expr, arg), m);
            literal_vector lits;
            lits.push_back(~mem.lit);
            lits.push_back(~mk_literal(in_r));
            ctx.mk_th_axiom(get_id(), lits.size(), lits.data());
        }
    }

    void theory_nseq::ensure_length_var(expr* e) {
        SASSERT(e && m_seq.is_seq(e));
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
        try {
            // Always assert non-negativity for all string theory vars,
            // even when there are no string equations/memberships.
            if (assert_nonneg_for_all_vars()) {
                TRACE(seq, tout << "nseq final_check: nonneg assertions added, FC_CONTINUE\n");
                return FC_CONTINUE;
            }

            // Check if there are any eq/mem items in the propagation queue.
            bool has_eq_or_mem = any_of(m_prop_queue, [](auto const &item) {
                return std::holds_alternative<eq_item>(item) || std::holds_alternative<mem_item>(item);
            });

            // there is nothing to do for the string solver, as there are no string constraints
            if (!has_eq_or_mem && m_ho_terms.empty() && !has_unhandled_preds()) {
                TRACE(seq, tout << "nseq final_check: empty state+ho, FC_DONE (no solve)\n");
                m_nielsen.reset();
                m_nielsen.create_root();
                m_nielsen.set_sat_node(m_nielsen.root());
                TRACE(seq, display(tout << "empty nielsen\n"));
                return FC_DONE;
            }

            // All literals that were needed to build a model could be assigned to true.
            // There is an existing nielsen graph with a satisfying assignment.
            if (!m_nielsen_literals.empty() && m_nielsen.sat_node() != nullptr &&
                all_of(m_nielsen_literals, [&](auto lit) { return l_true == ctx.get_assignment(lit); })) {
                TRACE(seq, tout << "nseq final_check: satifiable state revisited\n");
                // Re-run solving/model extraction instead of early exiting on a
                // cached SAT node. This avoids stale sat paths after additional
                // SAT assignments were introduced in prior FC_CONTINUE rounds.
            }

            // unfold higher-order terms when sequence structure is known
            if (unfold_ho_terms()) {
                TRACE(seq, tout << "nseq final_check: unfolded ho_terms, FC_CONTINUE\n");
                return FC_CONTINUE;
            }

            if (!has_eq_or_mem && !has_unhandled_preds()) {
                TRACE(seq, tout << "nseq final_check: empty state (after ho), FC_DONE (no solve)\n");
                m_nielsen.reset();
                m_nielsen.create_root();
                m_nielsen.set_sat_node(m_nielsen.root());
                TRACE(seq, display(tout << "empty nielsen\n"));
                return FC_DONE;
            }

            if (!has_eq_or_mem && has_unhandled_preds()) {
                TRACE(seq, tout << "nielsen root if null\n");
                // this can happen for regex constraint only benchmarks
                // qf_s\20250410-matching\wildcard-matching-regex-67.smt2
                return FC_GIVEUP;
            }

            populate_nielsen_graph();

            // assert length constraints derived from string equalities
            if (assert_length_constraints()) {
                TRACE(seq, tout << "nseq final_check: length constraints asserted, FC_CONTINUE\n");
                return FC_CONTINUE;
            }

            SASSERT(m_nielsen.root());            

            m_nielsen.assert_node_new_int_constraints(m_nielsen.root());

            ++m_num_final_checks;

            m_nielsen.set_max_search_depth(get_fparams().m_nseq_max_depth);
            m_nielsen.set_max_nodes(get_fparams().m_nseq_max_nodes);
            m_nielsen.set_parikh_enabled(get_fparams().m_nseq_parikh);
            m_nielsen.set_signature_split(get_fparams().m_nseq_signature);
            m_nielsen.set_regex_factorization(get_fparams().m_nseq_regex_factorization);

            SASSERT(!m_nielsen.root()->is_currently_conflict());

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
                    TRACE(seq, tout << "pre-check done\n");
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
                SASSERT(has_eq_or_mem); // we should have axiomatized them

                add_nielsen_assumptions();

                if (!check_length_coherence())
                    return FC_CONTINUE;

                CTRACE(seq, !has_unhandled_preds(), display(tout << "done\n"));
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


    void theory_nseq::add_nielsen_assumptions() {
        m_nielsen_literals.reset();
        struct reset_vector : public trail {
            sat::literal_vector &v;
            reset_vector(sat::literal_vector &v) : v(v) {}
            void undo() override {
                v.reset();
            }
        };
        //std::cout << "Nielsen assumptions:\n";
        ctx.push_trail(reset_vector(m_nielsen_literals));
        for (auto const& c : m_nielsen.sat_node()->constraints()) {
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
                ctx.force_phase(lit);
                IF_VERBOSE(2, verbose_stream() << 
                    "nseq final_check: adding nielsen assumption " << c.fml << "\n";);
                TRACE(seq, tout << "assign: " << c.fml << "\n");
                break;
            case l_false: 
                // this should not happen because nielsen checks for this before returning a satisfying path.
                // or maybe it can happen if we have a "le" dependency
                TRACE(seq, tout << "nseq final_check: nielsen assumption " << c.fml << " is false; internalized - " << ctx.e_internalized(c.fml) << "\n");
                std::cout << "False [" << lit << "]: " << mk_pp(c.fml, m) << std::endl;
                ctx.push_trail(value_trail(m_should_internalize));
                m_should_internalize = true;
                break;
            }
        }
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
                lits.push_back(mk_le_literal(ctx, m, m_autil, std::get<seq::le>(d)));
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
                    auto const& p = std::get<seq::le>(d);
                    kernel.assert_expr(m_autil.mk_le(p.lhs, p.rhs));
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
#endif
    }

    void theory_nseq::set_conflict(enode_pair_vector const& eqs, literal_vector const& lits) {
        TRACE(seq, tout << "nseq conflict: " << eqs.size() << " eqs, " << lits.size() << " lits\n";
              for (auto lit : lits) tout << ctx.literal2expr(lit) << "\n";
              for (auto [a, b] : eqs) tout << enode_pp(a, ctx) << " == " << enode_pp(b, ctx) << "\n";
        );

        bool all_true = true;
        literal_vector eq_lits;
        for (literal lit : lits) {
            ctx.mark_as_relevant(lit);
            all_true &= (ctx.get_assignment(lit) == l_true);
        }
        for (auto [a, b] : eqs) {
            literal lit_eq = mk_eq(a->get_expr(), b->get_expr(), false);
            eq_lits.push_back(lit_eq);
            ctx.mark_as_relevant(lit_eq);
            all_true &= (ctx.get_assignment(lit_eq) == l_true);
        }

        if (all_true) {
            ctx.set_conflict(
                ctx.mk_justification(
                    ext_theory_conflict_justification(
                        get_id(), ctx, lits.size(), lits.data(), eqs.size(), eqs.data(), 0, nullptr)));
            return;
        }

        literal_vector clause;
        for (literal lit : lits)
            clause.push_back(~lit);
        for (literal lit : eq_lits)
            clause.push_back(~lit);
        ctx.mk_th_axiom(get_id(), clause.size(), clause.data());
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

    euf::snode* theory_nseq::get_snode(expr* e) {
        return m_sgraph.mk(e);
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
        vector<seq::le, false> les;
        seq::deps_to_lits(lc.m_dep, eqs, lits, les);
        for (auto const& d : les)
            lits.push_back(mk_le_literal(ctx, m, m_autil, d));

        bool all_true = true;
        literal_vector eq_lits;
        for (auto [a, b] : eqs) {
            literal lit_eq = mk_eq(a->get_expr(), b->get_expr(), false);
            eq_lits.push_back(lit_eq);
            ctx.mark_as_relevant(lit_eq);
            all_true &= (ctx.get_assignment(lit_eq) == l_true);
        }
        for (literal dep_lit : lits) {
            ctx.mark_as_relevant(dep_lit);
            all_true &= (ctx.get_assignment(dep_lit) == l_true);
        }

        ctx.mark_as_relevant(lit);
        if (all_true) {
            justification* js = ctx.mk_justification(
                ext_theory_propagation_justification(
                    get_id(), ctx,
                    lits.size(), lits.data(),
                    eqs.size(), eqs.data(),
                    lit));
            ctx.assign(lit, js);
        }
        else {
            literal_vector clause;
            for (literal dep_lit : lits)
                clause.push_back(~dep_lit);
            for (literal lit_eq : eq_lits)
                clause.push_back(~lit_eq);
            clause.push_back(lit);
            ctx.mk_th_axiom(get_id(), clause.size(), clause.data());
        }

        TRACE(seq, tout << "nseq length propagation: " << mk_pp(lc.m_expr, m) << " (" << eqs.size() << " eqs, "
                        << lits.size() << " lits)\n";
              for (auto lit : lits) tout << "<- " << ctx.literal2expr(lit) << "\n";
              for (auto [a, b] : eqs) tout << "<- " << enode_pp(a, ctx) << " == " << enode_pp(b, ctx) << "\n";);
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

    bool theory_nseq::check_length_coherence() {
        if (m_relevant_lengths.empty())
            return true;

        SASSERT(m_nielsen.sat_node());

        auto const& mems = m_nielsen.sat_node()->str_mems();
        if (mems.empty())
            return true;

        u_map<unsigned_vector> var_to_mems;
        for (unsigned i = 0; i < mems.size(); ++i) {
            auto const& mem = mems[i];
            if (mem.is_primitive() && mem.m_str) {
                auto& vec = var_to_mems.insert_if_not_there(mem.m_str->id(), unsigned_vector());
                vec.push_back(i);
            }
        }

        if (var_to_mems.empty())
            return true;

        for (expr* len_expr : m_relevant_lengths) {
            expr* s = nullptr;
            VERIFY(m_seq.str.is_length(len_expr, s));

            euf::snode* s_node = m_sgraph.find(s);
            SASSERT(s_node);

            unsigned var_id = s_node->id();
            if (!var_to_mems.contains(var_id))
                continue;

            rational val_l;
            VERIFY(m_arith_value.get_value(len_expr, val_l));

            SASSERT(val_l.is_unsigned());

            // unless we intervene, the integer solver will take this length
            // so check if we really want this value
            const unsigned l = val_l.get_unsigned();

            unsigned_vector const& mem_indices = var_to_mems[var_id];
            ptr_vector<euf::snode> regexes;
            for (const unsigned i : mem_indices) {
                euf::snode* re = mems[i].m_regex;
                if (re)
                    regexes.push_back(re);
            }

            SASSERT(!regexes.empty());
            sort* ele_sort;
            VERIFY(m_seq.is_seq(m_sgraph.get_str_sort(), ele_sort));
            unsigned g = 1;
            if (m_gradient_cache.contains(s))
                g = m_gradient_cache[s];
            else
                m_gradient_cache.insert(s, 1);

            expr_ref allchar(m_seq.re.mk_full_char(m_seq.re.mk_re(m_sgraph.get_str_sort())), m);
            expr_ref l_expr(m_autil.mk_int(l), m);
            expr_ref loop_l(m_seq.re.mk_loop_proper(allchar.get(), l, l), m);

            euf::snode* sigmal_node = get_snode(loop_l.get());
            regexes.push_back(sigmal_node);
            SASSERT(regexes.size() > 1);

            lbool result = m_regex.check_intersection_emptiness(regexes);

            if (result == l_true) {
                // TODO: Incorporate that we might know the maximum length generated by a regex [in those cases, the gradients will never work]
                // It is empty. Try gradient.
                regexes.pop_back(); // Remove loop_l

                expr_ref loop_g(m_seq.re.mk_loop_proper(allchar.get(), g, g), m);
                expr_ref star_g(m_seq.re.mk_star(loop_g.get()), m);
                expr_ref sigmal_g_expr(m_seq.re.mk_concat(loop_l.get(), star_g.get()), m);

                euf::snode* sigmal_g_node = get_snode(sigmal_g_expr.get());
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
                    m_th_rewriter(prop_expr); // the divisibility predicate needs to be rewritten as it won't happen automatically

                    m_gradient_cache[s] = 1; // Reset gradient cache
                }
                else {
                    prop_expr = m.mk_not(m.mk_eq(len_expr, l_expr));
                    m_gradient_cache[s] = g + 1; // Increment gradient cache
                }

                if (!ctx.b_internalized(prop_expr))
                    ctx.internalize(prop_expr, true);
                literal lit_prop = ctx.get_literal(prop_expr);

                enode_pair_vector eqs;
                literal_vector dep_lits;
                vector<seq::le, false> dep_les;
                for (unsigned idx : mem_indices) {
                    if (mems[idx].m_dep)
                        seq::deps_to_lits(mems[idx].m_dep, eqs, dep_lits, dep_les);
                }
                for (auto const& d : dep_les)
                    dep_lits.push_back(mk_le_literal(ctx, m, m_autil, d));

                bool all_true = true;
                literal_vector eq_lits;
                for (auto [a, b] : eqs) {
                    literal lit_eq = mk_eq(a->get_expr(), b->get_expr(), false);
                    eq_lits.push_back(lit_eq);
                    ctx.mark_as_relevant(lit_eq);
                    all_true &= (ctx.get_assignment(lit_eq) == l_true);
                }
                for (literal dep_lit : dep_lits) {
                    ctx.mark_as_relevant(dep_lit);
                    all_true &= (ctx.get_assignment(dep_lit) == l_true);
                }

                ctx.mark_as_relevant(lit_prop);
                if (all_true) {
                    justification* js = ctx.mk_justification(
                        ext_theory_propagation_justification(
                            get_id(), ctx,
                            dep_lits.size(), dep_lits.data(),
                            eqs.size(), eqs.data(),
                            lit_prop));
                    ctx.assign(lit_prop, js);
                }
                else {
                    literal_vector clause;
                    for (literal dep_lit : dep_lits)
                        clause.push_back(~dep_lit);
                    for (literal lit_eq : eq_lits)
                        clause.push_back(~lit_eq);
                    clause.push_back(lit_prop);
                    ctx.mk_th_axiom(get_id(), clause.size(), clause.data());
                }
                
                TRACE(seq, tout << "nseq length coherence check: length " << l << " with gradient " << g << " is incompatible for " << mk_pp(s, m) << ", propagated " << mk_pp(prop_expr, m) << "\n";);
                IF_VERBOSE(1, verbose_stream() << "nseq length coherence check: length " << l << " with gradient " << g << " is incompatible for " << mk_pp(s, m) << ", propagated " << mk_pp(prop_expr, m) << "\n";);
                return false;
            }
        }

        return true;
    }

}
