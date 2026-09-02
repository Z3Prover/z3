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

    arith_sub_solver::arith_sub_solver(ast_manager& m, arith_util&, eq_tree::dep_manager_t& core_dep_mgr) :
        m(m), m_assump_lits(m), m_core_dep_mgr(core_dep_mgr) {
        params_ref p;
        m_solver = mk_smt_solver(m, p, symbol("QF_LIA"));
    }

    arith_sub_solver::~arith_sub_solver() {
        dealloc(m_solver);
    }

    void arith_sub_solver::assert_expr(expr* e, eq_tree::dep_tracker dep) {
        if (!dep) {
            m_solver->assert_expr(e);
            return;
        }
        expr* l;
        if (m_assump_lits.size() <= m_deps.size()) {
            SASSERT(m_assump_lits.size() == m_deps.size());
            l = m.mk_fresh_const("_arith_a", m.mk_bool_sort());
            m_assump_lit2id.insert(l, m_assump_lits.size());
            m_assump_lits.push_back(l);
        }
        else
            l = m_assump_lits.get(m_deps.size());
        m_solver->assert_expr(m.mk_or(m.mk_not(l), e));
        m_deps.push_back(dep);
    }

    void arith_sub_solver::push() {
        m_solver->push();
        m_frame_bounds.push_back(m_deps.size());
    }

    void arith_sub_solver::pop(unsigned n) {
        SASSERT(n <= m_frame_bounds.size());
        unsigned target = m_frame_bounds[m_frame_bounds.size() - n];
        m_deps.shrink(target);
        for (unsigned i = 0; i < n; i++)
            m_frame_bounds.pop_back();
        m_solver->pop(n);
    }

    unsigned arith_sub_solver::get_scope_level() const {
        return m_solver->get_scope_level();
    }

    lbool arith_sub_solver::check() {
        // do NOT reset m_core_dep_mgr here: the returned dep_tracker tree
        // may outlive this call (e.g. arith_facet::conflict_dep() is read
        // after check() returns); it is only reset by the arena's own
        // owner.
        m_last_core = nullptr;
        lbool r;
        if (m_deps.empty()) {
            r = m_solver->check_sat(0, nullptr);
        }
        else {
            // Only the first m_deps.size() literals are bound to an
            // active (a => e) assertion; the tail of m_assump_lits holds
            // recycled literals from popped frames - passing those as
            // assumptions is pointless and, should one surface in a
            // (non-minimal) unsat core, m_deps[id] below would index
            // past m_deps.size().
            r = m_solver->check_sat(m_deps.size(), m_assump_lits.data());
            if (r == l_false) {
                expr_ref_vector core(m);
                m_solver->get_unsat_core(core);
                for (expr* ce : core) {
                    unsigned id = 0;
                    if (!m_assump_lit2id.find(ce, id))
                        continue; // not one of our assumption literals
                    SASSERT(id < m_deps.size());
                    m_last_core = m_core_dep_mgr.mk_join(m_last_core, m_deps[id]);
                }
            }
        }
        return r;
    }

    // -- arith_facet --

    bool arith_facet::add_constraint(expr* c, eq_tree::dep_tracker dep) {
        for (expr* e : m_own)
            if (e == c)
                return false; // already recorded (propagate may revisit the same equation across simplify rounds)
        if (m_trail.get_num_scopes() != m_pushed_at_scope) {
            unsigned cur_scope = m_trail.get_num_scopes();
            m_trail.push(scope_trail(m_solver, m_pushed_at_scope));
            m_pushed_at_scope = cur_scope;
        }
        m_trail.push(push_back_ref_trail(m_own));
        m_own.push_back(c);
        m_solver.assert_expr(c, dep);
        m_trail.push(value_trail<bool>(m_conflict));
        m_trail.push(value_trail<eq_tree::dep_tracker>(m_conflict_dep));
        m_conflict = (m_solver.check() == l_false);
        m_conflict_dep = m_conflict ? m_solver.unsat_core() : nullptr;
        return true;
    }

    bool arith_facet::add_length_constraint(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep) {
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
        bool changed = add_constraint(m.mk_eq(lsum, rsum), dep);
        // len(v) >= 0 is an unconditional axiom, not contingent on `dep`
        // (the particular equation `v` was seen in) - asserted with a
        // null dep.
        for (expr* t : lhs)
            if (!is_const_token(u, t))
                changed = add_constraint(a.mk_ge(u.str.mk_length(t), a.mk_int(0))) || changed;
        for (expr* t : rhs)
            if (!is_const_token(u, t))
                changed = add_constraint(a.mk_ge(u.str.mk_length(t), a.mk_int(0))) || changed;
        return changed;
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
        bool changed = false;
        for (auto const& eq : ef.equations())
            changed = af.add_length_constraint(eq.m_lhs, eq.m_rhs, eq.m_dep) || changed;
        if (af.has_conflict()) {
            n.set_conflict(stx::br_plugin_base, af.conflict_dep());
            return stx::simplify_result::conflict;
        }
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

} // namespace seq
