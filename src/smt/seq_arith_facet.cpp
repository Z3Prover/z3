/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_arith_facet.cpp

Abstract:

    See seq_arith_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "smt/seq_arith_facet.h"
#include "smt/smt_solver.h"
#include "solver/solver.h"

namespace seq {

    // -- arith_sub_solver --

    arith_sub_solver::arith_sub_solver(ast_manager& m, arith_util&) : m(m) {
        params_ref p;
        m_solver = mk_smt_solver(m, p, symbol("QF_LIA"));
    }

    arith_sub_solver::~arith_sub_solver() {
        dealloc(m_solver);
    }

    void arith_sub_solver::assert_expr(expr* e) {
        m_solver->assert_expr(e);
    }

    void arith_sub_solver::push() {
        m_solver->push();
    }

    void arith_sub_solver::pop(unsigned n) {
        m_solver->pop(n);
    }

    unsigned arith_sub_solver::get_scope_level() const {
        return m_solver->get_scope_level();
    }

    lbool arith_sub_solver::check() {
        return m_solver->check_sat(0, nullptr);
    }

    // -- arith_facet --

    void arith_facet::add_constraint(expr* c) {
        for (expr* e : m_own)
            if (e == c)
                return; // already recorded (propagate may revisit the same equation across simplify rounds)
        if (!m_scope_pushed) {
            m_trail.push(scope_trail(m_solver));
            m_trail.push(value_trail<bool>(m_scope_pushed));
            m_scope_pushed = true;
        }
        m_trail.push(push_back_ref_trail(m_own));
        m_own.push_back(c);
        m_solver.assert_expr(c);
        m_trail.push(value_trail<bool>(m_conflict));
        m_conflict = (m_solver.check() == l_false);
    }

    void arith_facet::add_length_constraint(expr_ref_vector const& lhs, expr_ref_vector const& rhs) {
        expr_ref lsum(a.mk_int(0), m);
        expr_ref rsum(a.mk_int(0), m);
        for (expr* t : lhs) {
            expr_ref len(is_const_token(u, t) ? (expr*)a.mk_int(1) : (expr*)u.str.mk_length(t), m);
            lsum = a.mk_add(lsum, len);
        }
        for (expr* t : rhs) {
            expr_ref len(is_const_token(u, t) ? (expr*)a.mk_int(1) : (expr*)u.str.mk_length(t), m);
            rsum = a.mk_add(rsum, len);
        }
        add_constraint(m.mk_eq(lsum, rsum));
        for (expr* t : lhs)
            if (!is_const_token(u, t))
                add_constraint(a.mk_ge(u.str.mk_length(t), a.mk_int(0)));
        for (expr* t : rhs)
            if (!is_const_token(u, t))
                add_constraint(a.mk_ge(u.str.mk_length(t), a.mk_int(0)));
    }

    lbool arith_facet::implies(expr* c) const {
        m_solver.push();
        m_solver.assert_expr(m.mk_not(c));
        lbool r = m_solver.check();
        m_solver.pop(1);
        // unsat under the negation means c is implied (l_true); otherwise
        // undecided/not implied (l_undef, or l_false meaning c's negation
        // is itself consistent, i.e. c is not implied - callers treat
        // anything other than l_false-from-negation-check as "not yet
        // known", per facet-ncontains.md §3.3's l_true/l_undef/l_false
        // three-way split on the GATE, not on this helper's own result).
        return r == l_false ? l_true : l_undef;
    }

    stx::facet_i* arith_facet::clone(trail_stack& trail) const {
        arith_facet* f = alloc(arith_facet, trail, m, u, m_solver);
        // A cloned node's *own* constraint set starts empty: this is only
        // used for cold-path snapshots (hot-restart SAT leaf, cache
        // entries) which never re-enter the shared incremental backend's
        // scope stack themselves.
        return f;
    }

    unsigned arith_facet::hash() const {
        unsigned h = m_own.size() * 40503u;
        for (expr* e : m_own)
            h = combine_hash(h, e->get_id());
        return h ? h : 1;
    }

    bool arith_facet::similar(facet_i const& other) const {
        auto const& o = static_cast<arith_facet const&>(other);
        if (m_own.size() != o.m_own.size())
            return false;
        for (unsigned i = 0; i < m_own.size(); ++i)
            if (m_own.get(i) != o.m_own.get(i))
                return false;
        return true;
    }

    // -- arith_propagation --

    stx::simplify_result arith_propagation::propagate(eq_tree::node& n) {
        auto& ef = n.facet_as<eq_facet>(m_eq_id);
        auto& af = n.facet_as<arith_facet>(m_arith_id);
        for (auto const& eq : ef.equations())
            af.add_length_constraint(eq.m_lhs, eq.m_rhs);
        if (af.has_conflict()) {
            n.set_conflict(stx::br_plugin_base, nullptr);
            return stx::simplify_result::conflict;
        }
        return stx::simplify_result::proceed;
    }

} // namespace seq
