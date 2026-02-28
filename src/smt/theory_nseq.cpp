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

        // Process pending axioms
        if (m_state.has_pending_axioms()) {
            unsigned head = m_state.axioms_head();
            auto const& axioms = m_state.axioms();
            for (unsigned i = head; i < axioms.size(); ++i)
                deque_axiom(axioms[i]);
            m_state.set_axioms_head(axioms.size());
            return FC_CONTINUE;
        }

        // Solve word equations using Nielsen transformations
        if (solve_eqs())
            return FC_CONTINUE;

        // Propagate length equalities from equations
        if (propagate_length_eqs())
            return FC_CONTINUE;

        // Check zero-length variables
        if (check_zero_length())
            return FC_CONTINUE;

        // TODO: implement regex membership checking

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

        for (auto arg : *term)
            mk_var(ensure_enode(arg));

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
        return propagate_eq(dep, n1, n2);
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
    }

    expr_ref theory_nseq::mk_concat(expr_ref_vector const& es, sort* s) {
        SASSERT(!es.empty());
        return expr_ref(m_util.str.mk_concat(es.size(), es.data(), s), m);
    }

    // Check if a propagation x = t would create a length inconsistency.
    // If x has a known fixed length that differs from t's minimum length, return true (conflict).
    bool theory_nseq::check_length_conflict(expr* x, expr_ref_vector const& es, nseq_dependency* dep) {
        rational x_lo, x_hi;
        expr_ref x_len = mk_len(x);
        if (!ctx.e_internalized(x_len))
            return false;
        if (!lower_bound(x_len, x_lo) || !upper_bound(x_len, x_hi))
            return false;
        // Compute minimum length of the other side
        rational min_len(0);
        for (expr* e : es) {
            zstring s;
            if (m_util.str.is_string(e, s))
                min_len += rational(s.length());
            else if (m_util.str.is_unit(e))
                min_len += rational(1);
            // Variables contribute ≥ 0, so min remains unchanged
        }
        if (x_hi < min_len) {
            // x's max length is less than the minimum length of the term
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
        // Step 2: follow e-graph roots for each atomic component
        for (expr* u : units) {
            if (!ctx.e_internalized(u)) {
                dst.push_back(u);
                continue;
            }
            enode* n = ctx.get_enode(u);
            enode* r = n->get_root();
            expr* re = r->get_expr();
            if (re != u)
                dep = m_state.mk_join(dep, m_state.mk_dep(n, r));
            m_util.str.get_concat_units(re, dst);
        }
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

        // Apply Nielsen simplification
        seq::nielsen_result result = m_nielsen.simplify(lhs, rhs);

        switch (result) {
        case seq::nielsen_result::solved: {
            // Propagate solved form: either both empty, var = empty, or var = ground term
            bool changed = false;
            if (lhs.size() == 1 && m_nielsen.is_var(lhs.get(0)) && !rhs.empty()) {
                if (check_length_conflict(lhs.get(0), rhs, dep))
                    return true;
                sort* s = lhs.get(0)->get_sort();
                expr_ref rhs_concat = mk_concat(rhs, s);
                ensure_length_axiom(rhs_concat);
                changed = propagate_eq(dep, lhs.get(0), rhs_concat);
            }
            else if (rhs.size() == 1 && m_nielsen.is_var(rhs.get(0)) && !lhs.empty()) {
                if (check_length_conflict(rhs.get(0), lhs, dep))
                    return true;
                sort* s = rhs.get(0)->get_sort();
                expr_ref lhs_concat = mk_concat(lhs, s);
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
            set_conflict(dep);
            return true;

        case seq::nielsen_result::reduced: {
            if (lhs.empty() && rhs.empty())
                return false; // already equal
            bool changed = false;
            if (!lhs.empty() && !rhs.empty()) {
                sort* s = lhs[0]->get_sort();
                expr_ref l = mk_concat(lhs, s);
                expr_ref r = mk_concat(rhs, s);
                ensure_length_axiom(l);
                ensure_length_axiom(r);
                changed = propagate_eq(dep, l, r);
            }
            else {
                expr_ref_vector& nonempty = lhs.empty() ? rhs : lhs;
                for (expr* e : nonempty) {
                    if (m_util.is_seq(e)) {
                        expr_ref emp(m_util.str.mk_empty(e->get_sort()), m);
                        changed |= propagate_eq(dep, e, emp);
                    }
                }
            }
            TRACE(seq, tout << "reduced" << (changed ? " (propagated)" : " (no change)") << "\n";);
            return changed;
        }

        case seq::nielsen_result::split:
        case seq::nielsen_result::unchanged:
            break;
        }

        // Try branching: find a variable and decide x = "" or x ≠ ""
        return branch_eq(lhs, rhs, dep);
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

                // Decide: x = "" or x ≠ ""
                literal eq_empty = mk_eq(e, emp, false);
                switch (ctx.get_assignment(eq_empty)) {
                case l_undef:
                    // Force the empty branch first
                    TRACE(seq, tout << "branch " << mk_bounded_pp(e, m) << " = \"\"\n";);
                    ctx.force_phase(eq_empty);
                    ctx.mark_as_relevant(eq_empty);
                    m_new_propagation = true;
                    m_state.stats().m_num_splits++;
                    return true;
                case l_true:
                    // Variable assigned to empty but EQ not yet merged
                    // Propagate the equality
                    propagate_eq(dep, e, emp);
                    return true;
                case l_false:
                    // x ≠ "": try to find a prefix from the other side
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
        rational x_len;
        bool has_x_len = get_length(x, x_len);

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

    bool theory_nseq::propagate_length_eqs() {
        bool progress = false;
        for (auto const& eq : m_state.eqs()) {
            expr_ref_vector const& lhs = eq.lhs();
            expr_ref_vector const& rhs = eq.rhs();
            if (lhs.empty() || rhs.empty())
                continue;
            sort* s = lhs[0]->get_sort();
            expr_ref l = mk_concat(lhs, s);
            expr_ref r = mk_concat(rhs, s);
            expr_ref len_l = mk_len(l);
            expr_ref len_r = mk_len(r);
            if (ctx.e_internalized(len_l) && ctx.e_internalized(len_r)) {
                enode* nl = ctx.get_enode(len_l);
                enode* nr = ctx.get_enode(len_r);
                if (nl->get_root() != nr->get_root()) {
                    propagate_eq(eq.dep(), len_l, len_r, false);
                    progress = true;
                }
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
                if (m_util.str.is_string(ce, s)) {
                    return alloc(expr_wrapper_proc, to_app(ce));
                }
                if (m_util.str.is_empty(ce)) {
                    return alloc(expr_wrapper_proc, to_app(ce));
                }
                curr = curr->get_next();
            } while (curr != root);

            // No concrete value found: use seq_factory to get a fresh value
            expr_ref val(m);
            val = mg.get_model().get_fresh_value(e->get_sort());
            if (val) {
                m_fresh_values.push_back(val);
                return alloc(expr_wrapper_proc, to_app(val));
            }
            // Fallback: empty string
            return alloc(expr_wrapper_proc, to_app(m_util.str.mk_empty(e->get_sort())));
        }
        if (m_util.is_re(e)) {
            return alloc(expr_wrapper_proc, to_app(m_util.re.mk_full_seq(e->get_sort())));
        }
        UNREACHABLE();
        return nullptr;
    }

    void theory_nseq::init_model(model_generator& mg) {
        mg.register_factory(alloc(seq_factory, get_manager(), get_family_id(), mg.get_model()));
    }

    void theory_nseq::finalize_model(model_generator& mg) {
        m_fresh_values.reset();
    }
}

