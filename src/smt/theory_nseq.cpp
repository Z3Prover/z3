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

#include "ast/ast_pp.h"
#include "ast/ast_trail.h"
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
          m_state(ctx.get_manager(), m_util),
          m_nielsen(ctx.get_manager(), m_seq_rewrite),
          m_find(*this),
          m_has_seq(false),
          m_new_propagation(false),
          m_fresh_values(ctx.get_manager()) {
    }

    theory_nseq::~theory_nseq() {
    }

    void theory_nseq::init() {
        m_arith_value.init(&ctx);
    }

    // -------------------------------------------------------
    // Final check
    // -------------------------------------------------------

    final_check_status theory_nseq::final_check_eh(unsigned) {
        if (!m_has_seq)
            return FC_DONE;

        m_new_propagation = false;
        TRACE(seq, display(tout << "final_check level=" << ctx.get_scope_level() << "\n"););
        IF_VERBOSE(3, verbose_stream() << "nseq final_check level=" << ctx.get_scope_level() << "\n");

        // Process pending axioms
        if (m_state.has_pending_axioms()) {
            unsigned head = m_state.axioms_head();
            auto const& axioms = m_state.axioms();
            for (unsigned i = head; i < axioms.size(); ++i)
                deque_axiom(axioms[i]);
            m_state.set_axioms_head(axioms.size());
            return FC_CONTINUE;
        }

        // Reduce predicates (prefix, suffix, contains) to word equations
        if (reduce_predicates())
            return FC_CONTINUE;

        // Propagate length equalities from equations before solving,
        // so arithmetic bounds are available to guide branching
        if (propagate_length_eqs())
            return FC_CONTINUE;

        // Check zero-length variables before solving (uses arithmetic bounds)
        if (check_zero_length())
            return FC_CONTINUE;

        // Solve word equations using Nielsen transformations
        if (solve_eqs())
            return FC_CONTINUE;

        // Check regex membership constraints
        if (check_regex_memberships())
            return FC_CONTINUE;

        // Check disequalities
        if (check_disequalities())
            return FC_CONTINUE;

        if (all_eqs_solved() && m_state.mems().empty())
            return FC_DONE;

        return FC_GIVEUP;
    }

    // -------------------------------------------------------
    // Internalization
    // -------------------------------------------------------

    bool theory_nseq::internalize_atom(app* a, bool) {
        return internalize_term(a);
    }

    bool theory_nseq::internalize_term(app* term) {
        TRACE(seq, tout << "internalize_term: " << mk_bounded_pp(term, m, 3) << "\n";);
        if (!m_has_seq) {
            ctx.push_trail(value_trail<bool>(m_has_seq));
            m_has_seq = true;
        }

        if (m_util.str.is_in_re(term))
            mk_var(ensure_enode(term->get_arg(0)));

        if (m_util.str.is_length(term))
            mk_var(ensure_enode(term->get_arg(0)));

        // Always ensure theory vars for all seq-type args
        for (auto arg : *term)
            mk_var(ensure_enode(arg));

        if (ctx.e_internalized(term)) {
            mk_var(ctx.get_enode(term));
            return true;
        }

        if (m.is_bool(term) &&
            (m_util.str.is_in_re(term) || m_sk.is_skolem(term))) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.mark_as_relevant(bv);
            return true;
        }

        if (m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.mark_as_relevant(bv);
        }

        enode* e = nullptr;
        if (ctx.e_internalized(term))
            e = ctx.get_enode(term);
        else
            e = ctx.mk_enode(term, false, m.is_bool(term), true);
        mk_var(e);

        if (!ctx.relevancy())
            relevant_eh(term);

        return true;
    }

    void theory_nseq::internalize_eq_eh(app* atom, bool_var v) {
    }

    theory_var theory_nseq::mk_var(enode* n) {
        expr* o = n->get_expr();
        if (!m_util.is_seq(o) && !m_util.is_re(o))
            return null_theory_var;
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        theory_var v = theory::mk_var(n);
        m_find.mk_var();
        ctx.attach_th_var(n, this, v);
        ctx.mark_as_relevant(n);
        return v;
    }

    void theory_nseq::apply_sort_cnstr(enode* n, sort* s) {
        TRACE(seq, tout << "apply_sort_cnstr: " << mk_bounded_pp(n->get_expr(), m, 3) << "\n";);
        mk_var(n);
    }

    // -------------------------------------------------------
    // Equality and disequality callbacks
    // -------------------------------------------------------

    void theory_nseq::new_eq_eh(theory_var v1, theory_var v2) {
        enode* n1 = get_enode(v1);
        enode* n2 = get_enode(v2);
        expr* o1 = n1->get_expr();
        expr* o2 = n2->get_expr();
        if (!m_util.is_seq(o1) && !m_util.is_re(o1))
            return;

        nseq_dependency* dep = m_state.mk_dep(n1, n2);
        if (m_util.is_seq(o1)) {
            if (m_find.find(v1) != m_find.find(v2))
                m_find.merge(v1, v2);
            m_state.add_eq(o1, o2, dep);
            IF_VERBOSE(3, verbose_stream() << "new_eq_eh: " << mk_bounded_pp(o1, m) << " = " << mk_bounded_pp(o2, m)
                  << " (total eqs: " << m_state.eqs().size() << ")\n");
            TRACE(seq, tout << "new eq: " << mk_bounded_pp(o1, m) << " = " << mk_bounded_pp(o2, m) << "\n";);
        }
    }

    void theory_nseq::new_diseq_eh(theory_var v1, theory_var v2) {
        enode* n1 = get_enode(v1);
        enode* n2 = get_enode(v2);
        expr* e1 = n1->get_expr();
        expr* e2 = n2->get_expr();
        if (!m_util.is_seq(e1))
            return;
        if (n1->get_root() == n2->get_root())
            return;

        literal lit = mk_eq(e1, e2, false);
        nseq_dependency* dep = m_state.mk_dep(~lit);
        m_state.add_ne(e1, e2, dep);
        TRACE(seq, tout << "new diseq: " << mk_bounded_pp(e1, m) << " != " << mk_bounded_pp(e2, m) << "\n";);
    }

    // -------------------------------------------------------
    // Assignment callback
    // -------------------------------------------------------

    void theory_nseq::assign_eh(bool_var v, bool is_true) {
        expr* e = ctx.bool_var2expr(v);
        expr* e1 = nullptr, *e2 = nullptr;
        literal lit(v, !is_true);
        TRACE(seq, tout << (is_true ? "" : "not ") << mk_bounded_pp(e, m) << "\n";);

        if (m_util.str.is_prefix(e, e1, e2)) {
            nseq_dependency* dep = m_state.mk_dep(lit);
            m_state.add_pred(NSEQ_PREFIX, e1, e2, is_true, dep);
        }
        else if (m_util.str.is_suffix(e, e1, e2)) {
            nseq_dependency* dep = m_state.mk_dep(lit);
            m_state.add_pred(NSEQ_SUFFIX, e1, e2, is_true, dep);
        }
        else if (m_util.str.is_contains(e, e1, e2)) {
            nseq_dependency* dep = m_state.mk_dep(lit);
            m_state.add_pred(NSEQ_CONTAINS, e1, e2, is_true, dep);
        }
        else if (m_util.str.is_in_re(e, e1, e2)) {
            nseq_dependency* dep = m_state.mk_dep(lit);
            m_state.add_mem(e1, e2, is_true, dep);
        }
    }

    // -------------------------------------------------------
    // Propagation
    // -------------------------------------------------------

    bool theory_nseq::can_propagate() {
        return m_state.has_pending_axioms();
    }

    void theory_nseq::propagate() {
        unsigned head = m_state.axioms_head();
        auto const& axioms = m_state.axioms();
        for (unsigned i = head; i < axioms.size(); ++i)
            deque_axiom(axioms[i]);
        m_state.set_axioms_head(axioms.size());
    }

    // -------------------------------------------------------
    // Scope management
    // -------------------------------------------------------

    void theory_nseq::push_scope_eh() {
        theory::push_scope_eh();
        m_state.push_scope();
    }

    void theory_nseq::pop_scope_eh(unsigned num_scopes) {
        m_state.pop_scope(num_scopes);
        theory::pop_scope_eh(num_scopes);
        m_rewrite.reset();
    }

    void theory_nseq::restart_eh() {
    }

    void theory_nseq::relevant_eh(app* n) {
        if (m_util.str.is_length(n)) {
            add_length(n);
            enque_axiom(n);
        }

        // Enqueue axioms for operations that need reduction
        if (m_util.str.is_index(n)   ||
            m_util.str.is_replace(n) ||
            m_util.str.is_extract(n) ||
            m_util.str.is_at(n)      ||
            m_util.str.is_nth_i(n)   ||
            m_util.str.is_itos(n)    ||
            m_util.str.is_stoi(n)    ||
            m_util.str.is_from_code(n) ||
            m_util.str.is_to_code(n))
            enque_axiom(n);
    }

    // -------------------------------------------------------
    // Axiom management
    // -------------------------------------------------------

    void theory_nseq::enque_axiom(expr* e) {
        m_state.enqueue_axiom(e);
    }

    void theory_nseq::deque_axiom(expr* e) {
        TRACE(seq, tout << "deque axiom: " << mk_bounded_pp(e, m) << "\n";);
        if (m_util.str.is_length(e))
            add_length_axiom(e);
        else
            reduce_op(e);
    }

    void theory_nseq::add_axiom(literal l1, literal l2, literal l3, literal l4, literal l5) {
        literal_vector lits;
        if (l1 != null_literal) lits.push_back(l1);
        if (l2 != null_literal) lits.push_back(l2);
        if (l3 != null_literal) lits.push_back(l3);
        if (l4 != null_literal) lits.push_back(l4);
        if (l5 != null_literal) lits.push_back(l5);
        ctx.mk_th_axiom(get_id(), lits);
        m_state.stats().m_num_axioms++;
    }

    // -------------------------------------------------------
    // Propagation helpers
    // -------------------------------------------------------

    bool theory_nseq::propagate_eq(nseq_dependency* dep, enode* n1, enode* n2) {
        if (n1->get_root() == n2->get_root())
            return false;
        enode_pair_vector eqs;
        literal_vector lits;
        m_state.linearize(dep, eqs, lits);
        TRACE(seq, tout << "propagate eq: " << mk_bounded_pp(n1->get_expr(), m) << " = " << mk_bounded_pp(n2->get_expr(), m) << "\n";);
        IF_VERBOSE(3, verbose_stream() << "  propagate_eq: " << mk_bounded_pp(n1->get_expr(), m) << " = " << mk_bounded_pp(n2->get_expr(), m) << "\n";);
        justification* js = ctx.mk_justification(
            ext_theory_eq_propagation_justification(get_id(), ctx, lits.size(), lits.data(), eqs.size(), eqs.data(), n1, n2));
        ctx.assign_eq(n1, n2, eq_justification(js));
        m_state.stats().m_num_propagations++;
        m_new_propagation = true;
        return true;
    }

    bool theory_nseq::propagate_eq(nseq_dependency* dep, expr* e1, expr* e2, bool add_to_eqs) {
        enode* n1 = ensure_enode(e1);
        enode* n2 = ensure_enode(e2);
        mk_var(n1);
        mk_var(n2);
        bool result = propagate_eq(dep, n1, n2);
        // Explicitly propagate length equality for string terms
        if (result && m_util.is_seq(e1)) {
            expr_ref len1 = mk_len(e1);
            expr_ref len2 = mk_len(e2);
            enode* nl1 = ensure_enode(len1);
            enode* nl2 = ensure_enode(len2);
            if (nl1->get_root() != nl2->get_root())
                propagate_eq(dep, nl1, nl2);
        }
        return result;
    }

    bool theory_nseq::propagate_lit(nseq_dependency* dep, literal lit) {
        if (ctx.get_assignment(lit) == l_true)
            return false;
        enode_pair_vector eqs;
        literal_vector lits;
        m_state.linearize(dep, eqs, lits);
        justification* js = ctx.mk_justification(
            ext_theory_propagation_justification(get_id(), ctx, lits.size(), lits.data(), eqs.size(), eqs.data(), lit));
        ctx.assign(lit, js);
        m_state.stats().m_num_propagations++;
        m_new_propagation = true;
        return true;
    }

    void theory_nseq::set_conflict(nseq_dependency* dep, literal_vector const& extra_lits) {
        enode_pair_vector eqs;
        literal_vector lits;
        lits.append(extra_lits);
        m_state.linearize(dep, eqs, lits);
        TRACE(seq, tout << "conflict: " << lits << "\n";);
        ctx.set_conflict(
            ctx.mk_justification(
                ext_theory_conflict_justification(get_id(), ctx, lits.size(), lits.data(), eqs.size(), eqs.data())));
        m_state.stats().m_num_conflicts++;
    }

    // -------------------------------------------------------
    // Utility helpers
    // -------------------------------------------------------

    void theory_nseq::add_length(expr* l) {
        expr* e = nullptr;
        VERIFY(m_util.str.is_length(l, e));
        m_state.add_length(l, e, m_state.trail());
    }

    literal theory_nseq::mk_literal(expr* e) {
        expr_ref _e(e, m);
        if (!ctx.e_internalized(e))
            ctx.internalize(e, false);
        return ctx.get_literal(e);
    }

    literal theory_nseq::mk_eq_empty(expr* e, bool phase) {
        expr_ref emp(m_util.str.mk_empty(e->get_sort()), m);
        literal lit = mk_eq(e, emp, false);
        ctx.force_phase(phase ? lit : ~lit);
        return lit;
    }

    expr_ref theory_nseq::mk_len(expr* s) {
        return expr_ref(m_util.str.mk_length(s), m);
    }

    // Ensure that a string expression has its length axiom.
    // Called when equation solving creates or uses new string terms.
    void theory_nseq::ensure_length_axiom(expr* e) {
        if (!m_util.is_seq(e))
            return;
        expr_ref len(m_util.str.mk_length(e), m);
        ensure_enode(len);
        if (!m_state.has_length(e)) {
            m_state.add_length(len, e, m_state.trail());
            enque_axiom(len);
        }
        // Recursively ensure subterms have length axioms
        if (m_util.str.is_concat(e)) {
            for (auto arg : *to_app(e))
                ensure_length_axiom(arg);
        }
    }

    expr_ref theory_nseq::mk_concat(expr_ref_vector const& es, sort* s) {
        SASSERT(!es.empty());
        return expr_ref(m_util.str.mk_concat(es.size(), es.data(), s), m);
    }

    // Check if a propagation x = t would create a length inconsistency.
    // If x has a known fixed length that differs from t's length, return true (conflict).
    bool theory_nseq::check_length_conflict(expr* x, expr_ref_vector const& es, nseq_dependency* dep) {
        rational x_lo, x_hi;
        expr_ref x_len = mk_len(x);
        if (!ctx.e_internalized(x_len))
            return false;
        if (!lower_bound(x_len, x_lo) || !upper_bound(x_len, x_hi))
            return false;
        // Compute min and max length of the other side
        rational min_len(0), max_len(0);
        bool max_known = true;
        for (expr* e : es) {
            zstring s;
            if (m_util.str.is_string(e, s)) {
                min_len += rational(s.length());
                max_len += rational(s.length());
            }
            else if (m_util.str.is_unit(e)) {
                min_len += rational(1);
                max_len += rational(1);
            }
            else {
                // Variable or complex term: min is 0, max is unknown
                rational lo, hi;
                expr_ref elen = mk_len(e);
                if (ctx.e_internalized(elen) && lower_bound(elen, lo))
                    min_len += lo;
                if (ctx.e_internalized(elen) && upper_bound(elen, hi))
                    max_len += hi;
                else
                    max_known = false;
            }
        }
        if (x_hi < min_len || (max_known && x_lo > max_len)) {
            set_conflict(dep);
            return true;
        }
        return false;
    }
    // Replaces each element with its canonical representative, decomposing
    // concatenations and string constants as needed.
    bool theory_nseq::canonize(expr_ref_vector const& src, expr_ref_vector& dst,
                                nseq_dependency*& dep) {
        dst.reset();
        // Step 1: structurally decompose each src expression
        expr_ref_vector units(m);
        for (expr* e : src)
            m_util.str.get_concat_units(e, units);
        // Step 2: follow e-graph roots for each atomic component, recursively
        // Repeat until fixpoint to handle chains like a → concat(b, t1), t1 → concat(a, t2)
        bool changed = true;
        while (changed) {
            changed = false;
            expr_ref_vector next(m);
            for (expr* u : units) {
                if (!ctx.e_internalized(u)) {
                    next.push_back(u);
                    continue;
                }
                enode* n = ctx.get_enode(u);
                enode* r = n->get_root();
                expr* re = r->get_expr();
                // If root differs from u, check for the best representative:
                // prefer string constants > empty > units > concat > variables
                if (re != u) {
                    expr* best = re;
                    enode* best_node = r;
                    // If root is a concat or variable, scan for a more concrete repr
                    if (m_util.str.is_concat(re) || m_nielsen.is_var(re)) {
                        for (enode* p = r->get_next(); p != r; p = p->get_next()) {
                            expr* pe = p->get_expr();
                            if (m_util.str.is_string(pe) || m_util.str.is_empty(pe)) {
                                best = pe;
                                best_node = p;
                                break;
                            }
                        }
                    }
                    dep = m_state.mk_join(dep, m_state.mk_dep(n, best_node));
                    unsigned old_sz = next.size();
                    m_util.str.get_concat_units(best, next);
                    if (next.size() != old_sz + 1 || next.back() != u)
                        changed = true;
                    continue;
                }
                // Root == u: if u is a variable, search equivalence class
                // for a concat/string/unit that gives a better decomposition
                if (m_nielsen.is_var(u)) {
                    expr* best = nullptr;
                    enode* best_node = nullptr;
                    // Prefer string > empty > unit > concat
                    for (enode* p = r->get_next(); p != r; p = p->get_next()) {
                        expr* pe = p->get_expr();
                        if (m_util.str.is_string(pe) || m_util.str.is_empty(pe)) {
                            best = pe;
                            best_node = p;
                            break;
                        }
                        if (!best && (m_util.str.is_concat(pe) || m_util.str.is_unit(pe))) {
                            best = pe;
                            best_node = p;
                        }
                    }
                    if (best) {
                        dep = m_state.mk_join(dep, m_state.mk_dep(n, best_node));
                        unsigned old_sz = next.size();
                        m_util.str.get_concat_units(best, next);
                        if (next.size() != old_sz + 1 || next.back() != u)
                            changed = true;
                        continue;
                    }
                }
                next.push_back(u);
            }
            units.swap(next);
        }
        dst.append(units);
        return true;
    }

    // Check if all equations are satisfied in the current e-graph.
    bool theory_nseq::all_eqs_solved() {
        for (auto const& eq : m_state.eqs()) {
            expr_ref_vector lhs(m), rhs(m);
            nseq_dependency* dep = eq.dep();
            if (!canonize(eq.lhs(), lhs, dep))
                return false;
            if (!canonize(eq.rhs(), rhs, dep))
                return false;
            seq::nielsen_result result = m_nielsen.simplify(lhs, rhs);
            if (result != seq::nielsen_result::solved)
                return false;
        }
        return true;
    }

    // -------------------------------------------------------
    // Nielsen equation solving
    // -------------------------------------------------------

    bool theory_nseq::solve_eqs() {
        auto const& eqs = m_state.eqs();
        for (unsigned i = 0; !ctx.inconsistent() && i < eqs.size(); ++i)
            solve_eq(eqs[i]);
        return m_new_propagation || ctx.inconsistent();
    }

    bool theory_nseq::solve_eq(nseq_eq const& eq) {
        expr_ref_vector lhs(m), rhs(m);
        nseq_dependency* dep = eq.dep();

        // Canonize using current e-graph equivalences
        if (!canonize(eq.lhs(), lhs, dep) || !canonize(eq.rhs(), rhs, dep))
            return false;


        TRACE(seq, tout << "solve_eq [" << eq.id() << "]: ";
              for (auto* e : lhs) tout << mk_bounded_pp(e, m, 2) << " ";
              tout << "= ";
              for (auto* e : rhs) tout << mk_bounded_pp(e, m, 2) << " ";
              tout << "\n";);
        IF_VERBOSE(3, verbose_stream() << "solve_eq [" << eq.id() << "]: ";
              for (auto* e : lhs) verbose_stream() << mk_bounded_pp(e, m, 2) << " ";
              verbose_stream() << "= ";
              for (auto* e : rhs) verbose_stream() << mk_bounded_pp(e, m, 2) << " ";
              verbose_stream() << "\n";);

        // Apply Nielsen simplification
        seq::nielsen_result result = m_nielsen.simplify(lhs, rhs);
        IF_VERBOSE(3, verbose_stream() << "  nielsen=" << (int)result;
              if (result != seq::nielsen_result::solved) {
                  verbose_stream() << " reduced: ";
                  for (auto* e : lhs) verbose_stream() << mk_bounded_pp(e, m, 2) << " ";
                  verbose_stream() << "= ";
                  for (auto* e : rhs) verbose_stream() << mk_bounded_pp(e, m, 2) << " ";
              }
              verbose_stream() << "\n";);

        switch (result) {
        case seq::nielsen_result::solved: {
            // Propagate solved form: either both empty, var = empty, or var = ground term
            bool changed = false;
            if (lhs.size() == 1 && m_nielsen.is_var(lhs.get(0)) && !rhs.empty()) {
                if (check_length_conflict(lhs.get(0), rhs, dep))
                    return true;
                sort* s = lhs.get(0)->get_sort();
                expr_ref rhs_concat = mk_concat(rhs, s);
                ensure_enode(rhs_concat);
                ensure_length_axiom(rhs_concat);
                changed = propagate_eq(dep, lhs.get(0), rhs_concat);
            }
            else if (rhs.size() == 1 && m_nielsen.is_var(rhs.get(0)) && !lhs.empty()) {
                if (check_length_conflict(rhs.get(0), lhs, dep))
                    return true;
                sort* s = rhs.get(0)->get_sort();
                expr_ref lhs_concat = mk_concat(lhs, s);
                ensure_enode(lhs_concat);
                ensure_length_axiom(lhs_concat);
                changed = propagate_eq(dep, rhs.get(0), lhs_concat);
            }
            else {
                // All remaining vars must be empty
                for (unsigned i = 0; i < lhs.size(); ++i)
                    if (m_nielsen.is_var(lhs.get(i)))
                        changed |= propagate_eq(dep, lhs.get(i), expr_ref(m_util.str.mk_empty(lhs.get(i)->get_sort()), m));
                for (unsigned i = 0; i < rhs.size(); ++i)
                    if (m_nielsen.is_var(rhs.get(i)))
                        changed |= propagate_eq(dep, rhs.get(i), expr_ref(m_util.str.mk_empty(rhs.get(i)->get_sort()), m));
            }
            TRACE(seq, tout << "solved" << (changed ? " (propagated)" : " (no change)") << "\n";);
            return changed;
        }

        case seq::nielsen_result::conflict:
            TRACE(seq, tout << "conflict\n";);
            IF_VERBOSE(3, verbose_stream() << "  CONFLICT on eq " << eq.id() << "\n";);
            set_conflict(dep);
            return true;

        case seq::nielsen_result::reduced: {
            if (lhs.empty() && rhs.empty())
                return false;
            // If one side is empty, propagate: remaining must be empty
            if (lhs.empty() || rhs.empty()) {
                bool changed = false;
                expr_ref_vector& nonempty = lhs.empty() ? rhs : lhs;
                for (expr* e : nonempty) {
                    if (m_util.is_seq(e)) {
                        expr_ref emp(m_util.str.mk_empty(e->get_sort()), m);
                        changed |= propagate_eq(dep, e, emp);
                    }
                }
                return changed;
            }
            // For single var = ground, propagate
            if (lhs.size() == 1 && m_nielsen.is_var(lhs.get(0))) {
                sort* s = lhs.get(0)->get_sort();
                expr_ref rhs_concat = mk_concat(rhs, s);
                ensure_enode(rhs_concat);
                ensure_length_axiom(rhs_concat);
                bool changed = propagate_eq(dep, lhs.get(0), rhs_concat);
                if (changed) return true;
            }
            else if (rhs.size() == 1 && m_nielsen.is_var(rhs.get(0))) {
                sort* s = rhs.get(0)->get_sort();
                expr_ref lhs_concat = mk_concat(lhs, s);
                ensure_enode(lhs_concat);
                ensure_length_axiom(lhs_concat);
                bool changed = propagate_eq(dep, rhs.get(0), lhs_concat);
                if (changed) return true;
            }
            // Fall through to branch/split on the reduced equation
            break;
        }

        case seq::nielsen_result::split:
        case seq::nielsen_result::unchanged:
            break;
        }

        // Try branching: find a variable and decide x = "" or x ≠ ""
        if (branch_eq(lhs, rhs, dep))
            return true;

        // Try Nielsen splitting: x · α = c · β where x is non-empty variable, c is unit
        return split_variable(lhs, rhs, dep);
    }

    bool theory_nseq::branch_eq(expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                                 nseq_dependency* dep) {
        // Try branching on variables from the LHS first, then RHS
        for (unsigned side = 0; side < 2; ++side) {
            expr_ref_vector const& es = (side == 0) ? lhs : rhs;
            for (expr* e : es) {
                if (!m_nielsen.is_var(e))
                    continue;
                // Check if this variable is already known to be empty
                enode* n = ctx.get_enode(e);
                expr_ref emp(m_util.str.mk_empty(e->get_sort()), m);
                if (ctx.e_internalized(emp)) {
                    enode* n_emp = ctx.get_enode(emp);
                    if (n->get_root() == n_emp->get_root())
                        continue; // already equal to empty, skip
                }

                // Check arithmetic: if len(e) is known to be 0, force empty
                rational lo, hi;
                expr_ref len_e = mk_len(e);
                if (ctx.e_internalized(len_e) &&
                    lower_bound(len_e, lo) && upper_bound(len_e, hi) &&
                    lo.is_zero() && hi.is_zero()) {
                    nseq_dependency* ldep = m_state.mk_join(dep, m_state.mk_dep(mk_eq(len_e, m_autil.mk_int(0), false)));
                    propagate_eq(ldep, e, emp);
                    m_new_propagation = true;
                    return true;
                }

                // Decide: x = "" or x ≠ ""
                literal eq_empty = mk_eq(e, emp, false);
                switch (ctx.get_assignment(eq_empty)) {
                case l_undef:
                    // If lower length bound is already > 0, skip the empty branch
                    if (ctx.e_internalized(len_e) && lower_bound(len_e, lo) && lo > rational(0))
                        break;
                    // Force the empty branch first
                    TRACE(seq, tout << "branch " << mk_bounded_pp(e, m) << " = \"\"\n";);
                    IF_VERBOSE(3, verbose_stream() << "  branch " << mk_bounded_pp(e, m) << " = \"\"\n";);
                    ctx.force_phase(eq_empty);
                    ctx.mark_as_relevant(eq_empty);
                    m_new_propagation = true;
                    m_state.stats().m_num_splits++;
                    return true;
                case l_true:
                    // Variable assigned to empty but EQ not yet merged
                    IF_VERBOSE(3, verbose_stream() << "  branch_eq: " << mk_bounded_pp(e, m) << " eq_empty=l_true, propagating\n";);
                    propagate_eq(dep, e, emp);
                    return true;
                case l_false:
                    IF_VERBOSE(3, verbose_stream() << "  branch_eq: " << mk_bounded_pp(e, m) << " eq_empty=l_false (non-empty)\n";);
                    break;
                }
            }
        }

        // If all variables on one side are decided non-empty,
        // try to match against the other side using prefix enumeration
        return branch_eq_prefix(lhs, rhs, dep);
    }

    bool theory_nseq::branch_eq_prefix(expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                                        nseq_dependency* dep) {
        // Find a leading variable on either side
        if (!lhs.empty() && m_nielsen.is_var(lhs[0]) && !rhs.empty())
            return branch_var_prefix(lhs[0], rhs, dep);
        if (!rhs.empty() && m_nielsen.is_var(rhs[0]) && !lhs.empty())
            return branch_var_prefix(rhs[0], lhs, dep);
        return false;
    }

    bool theory_nseq::branch_var_prefix(expr* x, expr_ref_vector const& other,
                                         nseq_dependency* dep) {
        // For x starting one side, try x = prefix of other side
        // x = "" was already tried (assigned false)
        // Now enumerate: x = other[0], x = other[0]·other[1], ...
        //
        // Only use length when we have PROVEN tight bounds (lo == hi)
        // to avoid suggesting candidates based on tentative arithmetic values
        rational x_len;
        bool has_x_len = false;
        {
            rational lo, hi;
            expr_ref len_x = mk_len(x);
            if (lower_bound(len_x, lo) && upper_bound(len_x, hi) && lo == hi) {
                x_len = lo;
                has_x_len = true;
            }
        }
        // Only enumerate candidates when we know the variable's length
        // Otherwise let split_variable handle it (peel one char at a time)
        if (!has_x_len || x_len.is_zero())
            return false;

        // Find the range of valid prefix lengths
        // Stop before we include x itself (cyclic candidate)
        unsigned max_prefix = other.size();
        enode* x_root = ctx.get_enode(x)->get_root();
        for (unsigned i = 0; i < other.size(); ++i) {
            if (ctx.e_internalized(other[i]) &&
                ctx.get_enode(other[i])->get_root() == x_root) {
                max_prefix = i;
                break;
            }
        }
        if (max_prefix == 0)
            return false;

        expr_ref candidate(m);
        unsigned min_len = 0;
        bool has_var = false;
        for (unsigned len = 1; len <= max_prefix; ++len) {
            min_len += m_util.str.min_length(other[len - 1]);
            has_var = has_var || m_nielsen.is_var(other[len - 1]);
            // Skip if candidate length is incompatible with variable length
            if (has_x_len) {
                if (rational(min_len) > x_len)
                    continue;
                // For ground candidates (no variables), exact length must match
                if (!has_var && rational(min_len) != x_len)
                    continue;
            }
            if (len == 1)
                candidate = other[0];
            else
                candidate = expr_ref(m_util.str.mk_concat(len, other.data(), x->get_sort()), m);
            literal eq = mk_eq(x, candidate, false);
            switch (ctx.get_assignment(eq)) {
            case l_undef:
                TRACE(seq, tout << "branch " << mk_bounded_pp(x, m) << " = " << mk_bounded_pp(candidate, m) << "\n";);
                ensure_length_axiom(candidate);
                ctx.force_phase(eq);
                ctx.mark_as_relevant(eq);
                m_new_propagation = true;
                m_state.stats().m_num_splits++;
                return true;
            case l_true:
                ensure_length_axiom(candidate);
                propagate_eq(dep, x, candidate);
                return true;
            case l_false:
                continue;
            }
        }
        return false;
    }

    // -------------------------------------------------------
    // Nielsen splitting: x · α = c · β → x = c · x_tail
    // -------------------------------------------------------

    bool theory_nseq::split_variable(expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                                      nseq_dependency* dep) {
        if (lhs.empty() || rhs.empty())
            return false;

        // Find: variable on one side facing a unit/constant on the other
        expr* var = nullptr;
        expr* head = nullptr;
        bool var_on_left = false;

        if (m_nielsen.is_var(lhs[0]) && !m_nielsen.is_var(rhs[0])) {
            var = lhs[0];
            head = rhs[0];
            var_on_left = true;
        }
        else if (m_nielsen.is_var(rhs[0]) && !m_nielsen.is_var(lhs[0])) {
            var = rhs[0];
            head = lhs[0];
            var_on_left = false;
        }
        // Also handle var vs var: pick either and peel one character
        if (!var && !head && m_nielsen.is_var(lhs[0]) && m_nielsen.is_var(rhs[0]) && lhs[0] != rhs[0]) {
            var = lhs[0];
            head = rhs[0];
            var_on_left = true;
        }
        if (!var || !head)
            return false;

        // Check that var is known non-empty (branch_eq should have handled empty case)
        expr_ref emp(m_util.str.mk_empty(var->get_sort()), m);
        if (ctx.e_internalized(emp) && ctx.e_internalized(var)) {
            enode* n_var = ctx.get_enode(var);
            enode* n_emp = ctx.get_enode(emp);
            if (n_var->get_root() == n_emp->get_root())
                return false;
        }
        literal eq_empty = mk_eq(var, emp, false);
        if (ctx.get_assignment(eq_empty) != l_false)
            return false;

        // For multi-character string constants, extract only the first character
        // so we peel one character at a time (Nielsen style)
        zstring head_str;
        if (m_util.str.is_string(head, head_str) && head_str.length() > 1) {
            head = m_util.str.mk_unit(m_util.mk_char(head_str[0]));
        }

        // var is non-empty and the equation forces var to start with head.
        // Nielsen split: var = head · var_tail
        expr_ref one(m_autil.mk_int(1), m);
        expr_ref var_tail(m_sk.mk_tail(var, one), m);
        ensure_enode(var_tail);
        mk_var(ctx.get_enode(var_tail));
        ensure_length_axiom(var_tail);

        // Before committing to the split, ensure the tail's emptiness is decided.
        expr_ref tail_emp(m_util.str.mk_empty(var_tail->get_sort()), m);
        literal tail_eq_empty = mk_eq(var_tail, tail_emp, false);
        if (ctx.get_assignment(tail_eq_empty) == l_undef) {
            ctx.force_phase(tail_eq_empty);
            ctx.mark_as_relevant(tail_eq_empty);
            m_new_propagation = true;
            return true;
        }

        expr_ref split_rhs(m_util.str.mk_concat(head, var_tail), m);
        ensure_enode(split_rhs);
        ensure_length_axiom(split_rhs);

        TRACE(seq, tout << "nielsen split: " << mk_bounded_pp(var, m) << " = "
              << mk_bounded_pp(head, m) << " · tail\n";);
        IF_VERBOSE(3, verbose_stream() << "  split " << mk_bounded_pp(var, m) << " = "
              << mk_bounded_pp(head, m) << " · tail\n";);

        bool result = propagate_eq(dep, var, split_rhs);
        if (result)
            m_state.stats().m_num_splits++;
        return result;
    }

    // -------------------------------------------------------
    // Predicate reduction (prefix, suffix, contains → equations)
    // -------------------------------------------------------

    bool theory_nseq::reduce_predicates() {
        bool progress = false;
        unsigned head = m_state.preds_head();
        auto const& preds = m_state.preds();
        for (unsigned i = head; i < preds.size(); ++i) {
            if (reduce_pred(preds[i]))
                progress = true;
            if (ctx.inconsistent())
                break;
        }
        m_state.set_preds_head(preds.size());
        return progress;
    }

    bool theory_nseq::reduce_pred(nseq_pred const& pred) {
        switch (pred.kind()) {
        case NSEQ_PREFIX:
            return reduce_prefix(pred.arg1(), pred.arg2(), pred.sign(), pred.dep());
        case NSEQ_SUFFIX:
            return reduce_suffix(pred.arg1(), pred.arg2(), pred.sign(), pred.dep());
        case NSEQ_CONTAINS:
            return reduce_contains(pred.arg1(), pred.arg2(), pred.sign(), pred.dep());
        }
        UNREACHABLE();
        return false;
    }

    // prefixof(s, t): s is a prefix of t
    // positive: t = s · sk where sk is a fresh suffix variable
    // negative: |s| > |t| or there exists a position where they differ
    bool theory_nseq::reduce_prefix(expr* s, expr* t, bool sign, nseq_dependency* dep) {
        if (sign) {
            // Positive: t = s · z for some z
            expr_ref z(m_sk.mk_prefix_inv(s, t), m);
            expr_ref rhs(m_util.str.mk_concat(s, z), m);
            ensure_enode(z);
            mk_var(ctx.get_enode(z));
            ensure_enode(rhs);
            mk_var(ctx.get_enode(rhs));
            ensure_length_axiom(z);
            ensure_length_axiom(rhs);
            // Add the word equation directly so it's available for solve_eqs
            m_state.add_eq(t, rhs, dep);
            return propagate_eq(dep, t, rhs);
        }
        else {
            // Negative: |s| > |t| ∨ s ≠ extract(t, 0, |s|)
            // Add as a theory axiom: ¬prefix(s,t) → |s| > |t| ∨ extract(t, 0, |s|) ≠ s
            expr_ref len_s = mk_len(s);
            expr_ref len_t = mk_len(t);
            expr_ref zero(m_autil.mk_int(0), m);
            expr_ref extract(m_util.str.mk_substr(t, zero, len_s), m);
            ensure_enode(extract);
            ensure_length_axiom(extract);
            literal s_gt_t = mk_literal(m_autil.mk_ge(m_autil.mk_sub(len_s, len_t), m_autil.mk_int(1)));
            literal neq = ~mk_eq(s, extract, false);
            add_axiom(s_gt_t, neq);
            return true;
        }
    }

    // suffixof(s, t): s is a suffix of t
    // positive: t = z · s for some z
    bool theory_nseq::reduce_suffix(expr* s, expr* t, bool sign, nseq_dependency* dep) {
        if (sign) {
            // Positive: t = z · s for some fresh z
            expr_ref z(m_sk.mk("seq.suffix.sk", s, t), m);
            expr_ref rhs(m_util.str.mk_concat(z, s), m);
            ensure_enode(z);
            mk_var(ctx.get_enode(z));
            ensure_enode(rhs);
            mk_var(ctx.get_enode(rhs));
            ensure_length_axiom(z);
            ensure_length_axiom(rhs);
            m_state.add_eq(t, rhs, dep);
            return propagate_eq(dep, t, rhs);
        }
        else {
            // Negative: |s| > |t| ∨ extract(t, |t|-|s|, |s|) ≠ s
            expr_ref len_s = mk_len(s);
            expr_ref len_t = mk_len(t);
            expr_ref offset(m_autil.mk_sub(len_t, len_s), m);
            expr_ref extract(m_util.str.mk_substr(t, offset, len_s), m);
            ensure_enode(extract);
            ensure_length_axiom(extract);
            literal s_gt_t = mk_literal(m_autil.mk_ge(m_autil.mk_sub(len_s, len_t), m_autil.mk_int(1)));
            literal neq = ~mk_eq(s, extract, false);
            add_axiom(s_gt_t, neq);
            return true;
        }
    }

    // contains(haystack, needle)
    // positive: haystack = u · needle · v for some u, v
    bool theory_nseq::reduce_contains(expr* haystack, expr* needle, bool sign, nseq_dependency* dep) {
        if (sign) {
            // Positive: haystack = left · needle · right
            expr_ref left(m_sk.mk_left(haystack, needle), m);
            expr_ref right(m_sk.mk_right(haystack, needle), m);
            expr_ref rhs(m_util.str.mk_concat(left, m_util.str.mk_concat(needle, right)), m);
            ensure_enode(left);
            mk_var(ctx.get_enode(left));
            ensure_enode(right);
            mk_var(ctx.get_enode(right));
            ensure_enode(rhs);
            mk_var(ctx.get_enode(rhs));
            ensure_length_axiom(left);
            ensure_length_axiom(right);
            ensure_length_axiom(rhs);
            m_state.add_eq(haystack, rhs, dep);
            return propagate_eq(dep, haystack, rhs);
        }
        else {
            // Negative contains: |needle| > |haystack| ∨ not_contains
            // For now, add length constraint and let Nielsen handle the rest
            expr_ref len_h = mk_len(haystack);
            expr_ref len_n = mk_len(needle);
            literal n_gt_h = mk_literal(m_autil.mk_ge(m_autil.mk_sub(len_n, len_h), m_autil.mk_int(1)));
            // Simple case: if needle is longer than haystack, done
            if (ctx.get_assignment(n_gt_h) == l_undef) {
                ctx.mark_as_relevant(n_gt_h);
                m_new_propagation = true;
                return true;
            }
            return false;
        }
    }

    // -------------------------------------------------------
    // Disequality checking
    // -------------------------------------------------------

    bool theory_nseq::check_disequalities() {
        bool progress = false;
        for (auto const& ne : m_state.neqs()) {
            if (check_diseq(ne))
                progress = true;
            if (ctx.inconsistent())
                return true;
        }
        return progress;
    }

    bool theory_nseq::check_diseq(nseq_ne const& ne) {
        expr* l = ne.l();
        expr* r = ne.r();
        nseq_dependency* dep = ne.dep();

        // Canonize both sides
        expr_ref_vector lhs(m), rhs_v(m);
        nseq_dependency* ldep = dep, *rdep = dep;
        canonize(expr_ref_vector(m, 1, &l), lhs, ldep);
        canonize(expr_ref_vector(m, 1, &r), rhs_v, rdep);

        // Check if they are the same after canonization → conflict
        if (lhs.size() == rhs_v.size()) {
            bool all_same = true;
            for (unsigned i = 0; i < lhs.size() && all_same; ++i) {
                if (lhs.get(i) != rhs_v.get(i)) {
                    if (!ctx.e_internalized(lhs.get(i)) || !ctx.e_internalized(rhs_v.get(i)))
                        all_same = false;
                    else if (ctx.get_enode(lhs.get(i))->get_root() != ctx.get_enode(rhs_v.get(i))->get_root())
                        all_same = false;
                }
            }
            if (all_same) {
                // LHS and RHS are equal but we need them different
                nseq_dependency* jdep = m_state.mk_join(ldep, rdep);
                set_conflict(jdep);
                return true;
            }
        }

        // Check if both sides are ground strings and compare
        zstring s1, s2;
        expr_ref lhs_concat(m), rhs_concat(m);
        sort* srt = l->get_sort();
        if (!lhs.empty())
            lhs_concat = mk_concat(lhs, srt);
        else
            lhs_concat = m_util.str.mk_empty(srt);
        if (!rhs_v.empty())
            rhs_concat = mk_concat(rhs_v, srt);
        else
            rhs_concat = m_util.str.mk_empty(srt);

        if (is_ground_string(lhs_concat, s1) && is_ground_string(rhs_concat, s2)) {
            if (s1 == s2) {
                nseq_dependency* jdep = m_state.mk_join(ldep, rdep);
                set_conflict(jdep);
                return true;
            }
            // They are concretely different, disequality is satisfied
            return false;
        }

        // Use length difference to satisfy disequality
        expr_ref len_l = mk_len(lhs_concat);
        expr_ref len_r = mk_len(rhs_concat);
        ensure_enode(len_l);
        ensure_enode(len_r);
        if (ctx.e_internalized(len_l) && ctx.e_internalized(len_r)) {
            enode* nl = ctx.get_enode(len_l);
            enode* nr = ctx.get_enode(len_r);
            if (nl->get_root() != nr->get_root()) {
                // Lengths are different, disequality is satisfied
                return false;
            }
        }

        return false;
    }

    // -------------------------------------------------------
    // String operation reductions
    // -------------------------------------------------------

    void theory_nseq::reduce_op(expr* e) {
        expr_ref result(m);
        // Use the seq_rewriter to reduce the operation
        if (m_util.str.is_index(e))
            reduce_index(e);
        else if (m_util.str.is_replace(e))
            reduce_replace(e);
        else if (m_util.str.is_extract(e))
            reduce_extract(e);
        else if (m_util.str.is_at(e))
            reduce_at(e);
        else if (m_util.str.is_itos(e))
            reduce_itos(e);
        else if (m_util.str.is_stoi(e))
            reduce_stoi(e);
        else if (m_util.str.is_nth_i(e) ||
                 m_util.str.is_from_code(e) ||
                 m_util.str.is_to_code(e)) {
            // For these, add a definitional axiom via the rewriter
            expr_ref r(e, m);
            m_rewrite(r);
            if (r != e) {
                ensure_enode(r);
                add_axiom(mk_eq(e, r, false));
            }
        }
    }

    // str.replace(s, src, dst)
    // if contains(s, src): s = left · src · right ∧ result = left · dst · right
    // else: result = s
    void theory_nseq::reduce_replace(expr* e) {
        expr* s = nullptr, *src = nullptr, *dst = nullptr;
        VERIFY(m_util.str.is_replace(e, s, src, dst));
        expr_ref contains(m_util.str.mk_contains(s, src), m);
        literal contains_lit = mk_literal(contains);
        ctx.mark_as_relevant(contains_lit);

        // ¬contains(s, src) → replace(s, src, dst) = s
        add_axiom(contains_lit, mk_eq(e, s, false));

        // contains(s, src) → s = left · src · right
        expr_ref left(m_sk.mk_left(s, src), m);
        expr_ref right(m_sk.mk_right(s, src), m);
        expr_ref decomp(m_util.str.mk_concat(left, m_util.str.mk_concat(src, right)), m);
        ensure_enode(left);
        mk_var(ctx.get_enode(left));
        ensure_enode(right);
        mk_var(ctx.get_enode(right));
        ensure_enode(decomp);
        ensure_length_axiom(left);
        ensure_length_axiom(right);
        add_axiom(~contains_lit, mk_eq(s, decomp, false));

        // contains(s, src) → replace(s, src, dst) = left · dst · right
        expr_ref result(m_util.str.mk_concat(left, m_util.str.mk_concat(dst, right)), m);
        ensure_enode(result);
        ensure_length_axiom(result);
        add_axiom(~contains_lit, mk_eq(e, result, false));

        // contains(s, src) → ¬contains(left, src)  (first occurrence)
        expr_ref not_in_left(m_util.str.mk_contains(left, src), m);
        add_axiom(~contains_lit, ~mk_literal(not_in_left));
    }

    // str.at(s, i) = extract(s, i, 1)
    void theory_nseq::reduce_at(expr* e) {
        expr* s = nullptr, *i = nullptr;
        VERIFY(m_util.str.is_at(e, s, i));
        expr_ref one(m_autil.mk_int(1), m);
        expr_ref extract(m_util.str.mk_substr(s, i, one), m);
        ensure_enode(extract);
        add_axiom(mk_eq(e, extract, false));
        enque_axiom(extract);
    }

    // str.substr(s, offset, length)
    // offset >= 0 ∧ length >= 0 ∧ offset + length <= |s| → s = pre · result · post
    //   where |pre| = offset, |result| = length
    // offset < 0 ∨ length <= 0 ∨ offset >= |s| → result = ""
    void theory_nseq::reduce_extract(expr* e) {
        expr* s = nullptr, *offset = nullptr, *len = nullptr;
        VERIFY(m_util.str.is_extract(e, s, offset, len));
        expr_ref zero(m_autil.mk_int(0), m);
        expr_ref len_s = mk_len(s);

        expr_ref pre(m_sk.mk_pre(s, offset), m);
        expr_ref post(m_sk.mk_post(s, m_autil.mk_add(offset, len)), m);
        ensure_enode(pre);
        mk_var(ctx.get_enode(pre));
        ensure_enode(post);
        mk_var(ctx.get_enode(post));
        ensure_length_axiom(pre);
        ensure_length_axiom(post);

        // offset >= 0 ∧ len >= 0 ∧ offset + len <= |s| → s = pre · e · post
        literal off_ge_0 = mk_literal(m_autil.mk_ge(offset, zero));
        literal len_ge_0 = mk_literal(m_autil.mk_ge(len, zero));
        literal in_bounds = mk_literal(m_autil.mk_ge(m_autil.mk_sub(len_s, m_autil.mk_add(offset, len)), zero));

        expr_ref decomp(m_util.str.mk_concat(pre, m_util.str.mk_concat(e, post)), m);
        ensure_enode(decomp);
        add_axiom(~off_ge_0, ~len_ge_0, ~in_bounds, mk_eq(s, decomp, false));
        add_axiom(~off_ge_0, ~len_ge_0, ~in_bounds, mk_eq(mk_len(pre), offset, false));
        add_axiom(~off_ge_0, ~len_ge_0, ~in_bounds, mk_eq(mk_len(e), len, false));

        // offset < 0 → result = ""
        expr_ref emp(m_util.str.mk_empty(e->get_sort()), m);
        add_axiom(off_ge_0, mk_eq(e, emp, false));
        // len <= 0 → result = ""
        add_axiom(len_ge_0, mk_eq(e, emp, false));
        // offset >= |s| → result = ""
        literal off_ge_len = mk_literal(m_autil.mk_ge(m_autil.mk_sub(offset, len_s), zero));
        add_axiom(~off_ge_len, mk_eq(e, emp, false));

        // offset + len > |s| ∧ offset < |s| → |result| = |s| - offset
        add_axiom(~off_ge_0, ~len_ge_0, in_bounds, off_ge_len,
                  mk_eq(mk_len(e), expr_ref(m_autil.mk_sub(len_s, offset), m), false));
    }

    // str.indexof(s, t, offset)
    // offset >= 0 ∧ offset <= |s| ∧ contains(extract(s, offset, |s|-offset), t) →
    //   result >= offset ∧ s = pre · t · post ∧ |pre| = result ∧ ¬contains(pre, t)
    // else result = -1
    void theory_nseq::reduce_index(expr* e) {
        expr* s = nullptr, *t = nullptr, *offset = nullptr;
        VERIFY(m_util.str.is_index(e, s, t, offset));
        if (!offset)
            offset = m_autil.mk_int(0);

        expr_ref zero(m_autil.mk_int(0), m);
        expr_ref minus_one(m_autil.mk_int(-1), m);
        expr_ref len_s = mk_len(s);
        expr_ref len_t = mk_len(t);

        // Substr from offset
        expr_ref sub(m_util.str.mk_substr(s, offset, m_autil.mk_sub(len_s, offset)), m);
        expr_ref contains(m_util.str.mk_contains(sub, t), m);
        literal contains_lit = mk_literal(contains);
        ctx.mark_as_relevant(contains_lit);
        literal off_ge_0 = mk_literal(m_autil.mk_ge(offset, zero));
        literal off_le_len = mk_literal(m_autil.mk_ge(m_autil.mk_sub(len_s, offset), zero));

        // ¬contains ∨ offset < 0 ∨ offset > |s| → result = -1
        add_axiom(contains_lit, mk_eq(e, minus_one, false));
        add_axiom(off_ge_0, mk_eq(e, minus_one, false));
        add_axiom(off_le_len, mk_eq(e, minus_one, false));

        // contains → result >= offset ∧ result >= 0
        add_axiom(~contains_lit, ~off_ge_0, ~off_le_len,
                  mk_literal(m_autil.mk_ge(e, offset)));
        // result + |t| <= |s|
        add_axiom(~contains_lit, ~off_ge_0, ~off_le_len,
                  mk_literal(m_autil.mk_ge(m_autil.mk_sub(len_s, m_autil.mk_add(e, len_t)), zero)));
    }

    // str.from_int(i)
    // i < 0 → result = ""
    // i >= 0 → |result| >= 1
    // i = 0 → result = "0"
    void theory_nseq::reduce_itos(expr* e) {
        expr* i = nullptr;
        VERIFY(m_util.str.is_itos(e, i));
        expr_ref zero(m_autil.mk_int(0), m);
        expr_ref emp(m_util.str.mk_empty(e->get_sort()), m);
        literal i_ge_0 = mk_literal(m_autil.mk_ge(i, zero));
        add_axiom(i_ge_0, mk_eq(e, emp, false));
        add_axiom(~i_ge_0, mk_literal(m_autil.mk_ge(mk_len(e), m_autil.mk_int(1))));
        // i = 0 → result = "0"
        literal i_eq_0 = mk_eq(i, zero, false);
        expr_ref str_zero(m_util.str.mk_string(zstring("0")), m);
        add_axiom(~i_eq_0, mk_eq(e, str_zero, false));
    }

    // str.to_int(s)
    // s = "" → result = -1
    // |s| = 0 → result = -1
    void theory_nseq::reduce_stoi(expr* e) {
        expr* s = nullptr;
        VERIFY(m_util.str.is_stoi(e, s));
        expr_ref emp(m_util.str.mk_empty(s->get_sort()), m);
        expr_ref minus_one(m_autil.mk_int(-1), m);
        literal s_empty = mk_eq(s, emp, false);
        add_axiom(~s_empty, mk_eq(e, minus_one, false));
        // result >= -1
        add_axiom(mk_literal(m_autil.mk_ge(e, minus_one)));
    }

    // -------------------------------------------------------
    // Regex membership
    // -------------------------------------------------------

    bool theory_nseq::is_ground_string(expr* e, zstring& s) {
        // Follow e-graph root and check if it's a ground string
        if (!ctx.e_internalized(e))
            return false;
        enode* n = ctx.get_enode(e);
        expr* root = n->get_root()->get_expr();
        if (m_util.str.is_string(root, s))
            return true;
        // Check if root is a concat of units/strings
        expr_ref_vector units(m);
        m_util.str.get_concat_units(root, units);
        s = zstring();
        for (expr* u : units) {
            if (ctx.e_internalized(u)) {
                expr* ur = ctx.get_enode(u)->get_root()->get_expr();
                zstring us;
                if (m_util.str.is_string(ur, us)) {
                    s = s + us;
                    continue;
                }
                unsigned ch;
                expr* arg;
                if (m_util.str.is_unit(ur, arg) &&
                    ctx.e_internalized(arg) &&
                    m_util.is_const_char(ctx.get_enode(arg)->get_root()->get_expr(), ch)) {
                    s = s + zstring(ch);
                    continue;
                }
            }
            return false;
        }
        return true;
    }

    expr_ref theory_nseq::derive_regex(expr* regex, zstring const& prefix) {
        expr_ref r(regex, m);
        for (unsigned i = 0; i < prefix.length(); ++i) {
            expr_ref ch(m_util.mk_char(prefix[i]), m);
            r = m_seq_rewrite.mk_derivative(ch, r);
        }
        return r;
    }

    bool theory_nseq::check_regex_memberships() {
        bool progress = false;
        for (auto const& mem : m_state.mems()) {
            if (check_regex_mem(mem))
                progress = true;
            if (ctx.inconsistent())
                return true;
        }
        return progress;
    }

    bool theory_nseq::check_regex_mem(nseq_mem const& mem) {
        expr* s = mem.str();
        expr* r = mem.regex();
        bool sign = mem.sign();
        nseq_dependency* dep = mem.dep();

        // Try to determine the string value from the e-graph
        zstring sval;
        if (!is_ground_string(s, sval))
            return false;

        // Compute derivatives for the known string
        expr_ref derived = derive_regex(r, sval);

        // Check nullable: does the derived regex accept the empty word?
        expr_ref nullable = m_seq_rewrite.is_nullable(derived);
        m_rewrite(nullable);

        if (sign) {
            // Positive membership: s must be in r
            if (m.is_false(nullable)) {
                // String is fully determined but regex rejects → conflict
                set_conflict(dep);
                return true;
            }
        }
        else {
            // Negative membership: s must NOT be in r
            if (m.is_true(nullable)) {
                // String is fully determined and regex accepts → conflict
                set_conflict(dep);
                return true;
            }
        }

        // Check if the derived regex is the empty set
        if (sign && m_util.re.is_empty(derived)) {
            set_conflict(dep);
            return true;
        }
        return false;
    }

    // -------------------------------------------------------
    // Length reasoning
    // -------------------------------------------------------

    void theory_nseq::add_length_axiom(expr* n) {
        expr* x = nullptr;
        VERIFY(m_util.str.is_length(n, x));
        if (m_util.str.is_concat(x) && to_app(x)->get_num_args() != 0) {
            // len(x1 ++ x2 ++ ...) = len(x1) + len(x2) + ...
            ptr_vector<expr> args;
            for (auto arg : *to_app(x))
                args.push_back(m_util.str.mk_length(arg));
            expr_ref len_sum(m_autil.mk_add(args.size(), args.data()), m);
            add_axiom(mk_eq(len_sum, n, false));
        }
        else if (m_util.str.is_unit(x)) {
            // len(unit(c)) = 1
            add_axiom(mk_eq(n, m_autil.mk_int(1), false));
        }
        else if (m_util.str.is_empty(x)) {
            // len("") = 0
            add_axiom(mk_eq(n, m_autil.mk_int(0), false));
        }
        else {
            zstring s;
            if (m_util.str.is_string(x, s)) {
                // len("abc") = 3
                add_axiom(mk_eq(n, m_autil.mk_int(s.length()), false));
            }
            else {
                // len(x) >= 0
                add_axiom(mk_literal(m_autil.mk_ge(n, m_autil.mk_int(0))));
                // len(x) = 0 ↔ x = ""
                expr_ref emp(m_util.str.mk_empty(x->get_sort()), m);
                literal len_zero = mk_eq(n, m_autil.mk_int(0), false);
                literal x_empty = mk_eq(x, emp, false);
                add_axiom(~len_zero, x_empty);   // len(x) = 0 → x = ""
                add_axiom(len_zero, ~x_empty);    // x = "" → len(x) = 0
            }
        }
    }

    bool theory_nseq::get_length(expr* e, rational& val) {
        expr_ref len = mk_len(e);
        return m_arith_value.get_value(len, val);
    }

    bool theory_nseq::lower_bound(expr* e, rational& lo) {
        bool strict;
        return m_arith_value.get_lo(e, lo, strict) && !strict;
    }

    bool theory_nseq::upper_bound(expr* e, rational& hi) {
        bool strict;
        return m_arith_value.get_up(e, hi, strict) && !strict;
    }

    bool theory_nseq::check_zero_length() {
        bool progress = false;
        for (auto const& [len_app, str_expr] : m_state.length_pairs()) {
            rational lo, hi;
            if (lower_bound(len_app, lo) && upper_bound(len_app, hi) &&
                lo.is_zero() && hi.is_zero()) {
                // len(e) = 0 → e = ""
                expr* e = str_expr;
                expr_ref emp(m_util.str.mk_empty(e->get_sort()), m);
                enode* n = ensure_enode(e);
                enode* n_emp = ensure_enode(emp);
                if (n->get_root() != n_emp->get_root()) {
                    literal len_zero = mk_eq(len_app, m_autil.mk_int(0), false);
                    nseq_dependency* dep = m_state.mk_dep(len_zero);
                    propagate_eq(dep, e, emp);
                    progress = true;
                }
            }
        }
        return progress;
    }

    // Build an arithmetic expression for the sum of lengths of the given string terms.
    // Collapses concrete lengths (units, string constants) to integer numerals,
    // and uses mk_len(e) for variables/complex terms.
    expr_ref theory_nseq::build_length_sum(expr_ref_vector const& es) {
        rational total(0);
        expr_ref_vector var_lens(m);
        for (expr* e : es) {
            zstring s;
            if (m_util.str.is_string(e, s)) {
                total += rational(s.length());
            } else if (m_util.str.is_unit(e)) {
                total += rational(1);
            } else if (m_util.str.is_empty(e)) {
                // contributes 0
            } else {
                ensure_length_axiom(e);
                var_lens.push_back(mk_len(e));
            }
        }
        if (var_lens.empty())
            return expr_ref(m_autil.mk_numeral(total, true), m);
        expr_ref var_sum(m);
        if (var_lens.size() == 1)
            var_sum = expr_ref(var_lens.get(0), m);
        else
            var_sum = expr_ref(m_autil.mk_add(var_lens.size(), var_lens.data()), m);
        if (total.is_zero())
            return var_sum;
        return expr_ref(m_autil.mk_add(var_sum, m_autil.mk_numeral(total, true)), m);
    }

    bool theory_nseq::propagate_length_eqs() {
        bool progress = false;
        for (auto const& eq : m_state.eqs()) {
            expr_ref_vector const& lhs = eq.lhs();
            expr_ref_vector const& rhs = eq.rhs();
            // Build sum of lengths directly, using concrete integer values for
            // units/strings to avoid creating fresh unregistered concat terms.
            expr_ref lhs_sum = build_length_sum(lhs);
            expr_ref rhs_sum = build_length_sum(rhs);
            // Skip if both sums are syntactically identical (trivially equal)
            if (lhs_sum.get() == rhs_sum.get())
                continue;
            literal len_eq = mk_eq(lhs_sum, rhs_sum, false);
            if (ctx.get_assignment(len_eq) != l_true) {
                add_axiom(len_eq);
                progress = true;
            }
        }
        return progress;
    }

    // -------------------------------------------------------
    // Display and statistics
    // -------------------------------------------------------

    void theory_nseq::display(std::ostream& out) const {
        out << "theory_nseq\n";
        m_state.display(out);
    }

    void theory_nseq::collect_statistics(::statistics& st) const {
        auto const& s = m_state.stats();
        st.update("nseq eqs", s.m_num_eqs);
        st.update("nseq neqs", s.m_num_neqs);
        st.update("nseq memberships", s.m_num_memberships);
        st.update("nseq predicates", s.m_num_predicates);
        st.update("nseq conflicts", s.m_num_conflicts);
        st.update("nseq propagations", s.m_num_propagations);
        st.update("nseq splits", s.m_num_splits);
        st.update("nseq axioms", s.m_num_axioms);
    }

    // -------------------------------------------------------
    // Model generation (stub)
    // -------------------------------------------------------

    model_value_proc* theory_nseq::mk_value(enode* n, model_generator& mg) {
        app* e = n->get_expr();

        if (m_util.is_seq(e)) {
            // Walk the equivalence class looking for a concrete string value
            enode* root = n->get_root();
            enode* curr = root;
            do {
                expr* ce = curr->get_expr();
                zstring s;
                if (m_util.str.is_string(ce, s))
                    return alloc(expr_wrapper_proc, to_app(ce));
                if (m_util.str.is_empty(ce))
                    return alloc(expr_wrapper_proc, to_app(ce));
                curr = curr->get_next();
            } while (curr != root);

            // Try to build from concat/unit expressions in equivalence class
            curr = root;
            do {
                zstring result;
                if (eval_string(curr->get_expr(), result)) {
                    expr_ref val(m_util.str.mk_string(result), m);
                    m_fresh_values.push_back(val);
                    return alloc(expr_wrapper_proc, to_app(val));
                }
                curr = curr->get_next();
            } while (curr != root);

            // Try to construct a string of the correct length
            rational len_val;
            if (get_length(e, len_val) && len_val.is_nonneg() && len_val.is_unsigned()) {
                unsigned len = len_val.get_unsigned();
                zstring s;
                for (unsigned i = 0; i < len; i++)
                    s = s + zstring("A");
                expr_ref val(m_util.str.mk_string(s), m);
                m_fresh_values.push_back(val);
                return alloc(expr_wrapper_proc, to_app(val));
            }

            // Fallback: fresh value
            expr_ref val(m);
            val = mg.get_model().get_fresh_value(e->get_sort());
            if (val) {
                m_fresh_values.push_back(val);
                return alloc(expr_wrapper_proc, to_app(val));
            }
            return alloc(expr_wrapper_proc, to_app(m_util.str.mk_empty(e->get_sort())));
        }
        if (m_util.is_re(e)) {
            return alloc(expr_wrapper_proc, to_app(m_util.re.mk_full_seq(e->get_sort())));
        }
        UNREACHABLE();
        return nullptr;
    }

    bool theory_nseq::eval_string(expr* e, zstring& result) {
        zstring s;
        if (m_util.str.is_string(e, s)) {
            result = s;
            return true;
        }
        if (m_util.str.is_empty(e)) {
            result = zstring();
            return true;
        }
        expr* ch;
        if (m_util.str.is_unit(e, ch)) {
            unsigned c;
            if (m_util.is_const_char(ch, c)) {
                result = zstring(c);
                return true;
            }
            return false;
        }
        if (m_util.str.is_concat(e)) {
            result = zstring();
            for (expr* arg : *to_app(e)) {
                zstring sub;
                if (!eval_string_in_eclass(arg, sub))
                    return false;
                result = result + sub;
            }
            return true;
        }
        return false;
    }

    bool theory_nseq::eval_string_in_eclass(expr* e, zstring& result) {
        if (eval_string(e, result))
            return true;
        if (!ctx.e_internalized(e))
            return false;
        enode* root = ctx.get_enode(e)->get_root();
        enode* curr = root;
        do {
            if (eval_string(curr->get_expr(), result))
                return true;
            curr = curr->get_next();
        } while (curr != root);
        // If the expression has a known length, construct a default string
        rational len_val;
        if (get_length(root->get_expr(), len_val) && len_val.is_nonneg() && len_val.is_unsigned()) {
            unsigned len = len_val.get_unsigned();
            result = zstring();
            for (unsigned i = 0; i < len; i++)
                result = result + zstring("A");
            return true;
        }
        return false;
    }

    void theory_nseq::init_model(model_generator& mg) {
        mg.register_factory(alloc(seq_factory, get_manager(), get_family_id(), mg.get_model()));
    }

    void theory_nseq::finalize_model(model_generator& mg) {
        m_fresh_values.reset();
    }
}

