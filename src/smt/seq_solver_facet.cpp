/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_solver_facet.cpp

Abstract:

    See seq_solver_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#include "smt/seq_solver_facet.h"
#include "smt/smt_solver.h"
#include "solver/solver.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_safe_replace.h"

namespace seq {

    // -- sub_solver --

    sub_solver::sub_solver(ast_manager& m, arith_util&, eq_tree::dep_manager_t& core_dep_mgr) :
        m(m), m_assump_lits(m), m_core_dep_mgr(core_dep_mgr) {
        params_ref p;
        // This backend only handles arithmetic; keep string theories out.
        p.set_sym("string_solver", symbol("none"));
        // Leave hard arithmetic subproblems unresolved instead of stalling the search.
        p.set_uint("max_conflicts", 100);
        m_solver = mk_smt_solver(m, p, symbol("QF_LIA"));
    }

    sub_solver::~sub_solver() {
        dealloc(m_solver);
    }

    void sub_solver::assert_expr(expr* e, eq_tree::dep_tracker dep) {
        m_dirty = true;
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

    void sub_solver::push() {
        m_dirty = true;
        m_solver->push();
        m_frame_bounds.push_back(m_deps.size());
    }

    void sub_solver::pop(unsigned n) {
        m_dirty = true;
        SASSERT(n <= m_frame_bounds.size());
        unsigned target = m_frame_bounds[m_frame_bounds.size() - n];
        m_deps.shrink(target);
        for (unsigned i = 0; i < n; i++)
            m_frame_bounds.pop_back();
        m_solver->pop(n);
    }

    unsigned sub_solver::get_scope_level() const {
        return m_solver->get_scope_level();
    }

    lbool sub_solver::check() {
        // The returned dep tree may outlive this call, so its arena is
        // reset by the owner, not here.
        if (!m_dirty)
            return m_last_result;
        m_last_core = nullptr;
        lbool r;
        if (m_deps.empty()) {
            r = m_solver->check_sat(0, nullptr);
        }
        else {
            // Only the active assumption literals correspond to live deps.
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
        m_dirty = false;
        m_last_result = r;
        m_model = nullptr;
        return r;
    }

    // -- solver_facet --

    bool solver_facet::add_constraint(expr* c0, eq_tree::dep_tracker dep) {
        expr_ref c(c0, m); // keep fresh terms alive until m_own retains them
        for (expr* e : m_own)
            if (e == c.get())
                return false;
        if (m_trail.get_num_scopes() != m_pushed_at_scope) {
            unsigned cur_scope = m_trail.get_num_scopes();
            m_trail.push(scope_trail(m_solver, m_pushed_at_scope));
            m_pushed_at_scope = cur_scope;
        }
        m_trail.push(push_back_ref_trail(m_own));
        m_own.push_back(c);
        m_solver.assert_expr(c, dep);
        return true;
    }

    bool solver_facet::add_length_constraint(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep) {
        // Raw char tokens contribute no sequence length; only unit(...)
        // tokens count as length 1.
        auto tok_len = [&](expr* t) -> expr* {
            if (u.str.is_unit(t))
                return a.mk_int(1);
            if (u.is_seq(t->get_sort()))
                return u.str.mk_length(t);
            return nullptr;
        };
        expr_ref lsum(a.mk_int(0), m);
        expr_ref rsum(a.mk_int(0), m);
        for (expr* t : lhs)
            if (expr* len = tok_len(t))
                lsum = a.mk_add(lsum, len);
        for (expr* t : rhs)
            if (expr* len = tok_len(t))
                rsum = a.mk_add(rsum, len);
        bool changed = add_constraint(m.mk_eq(lsum, rsum), dep);
        // len(v) >= 0 is unconditional.
        for (expr* t : lhs)
            if (!u.str.is_unit(t) && u.is_seq(t->get_sort()))
                changed = add_constraint(a.mk_ge(u.str.mk_length(t), a.mk_int(0))) || changed;
        for (expr* t : rhs)
            if (!u.str.is_unit(t) && u.is_seq(t->get_sort()))
                changed = add_constraint(a.mk_ge(u.str.mk_length(t), a.mk_int(0))) || changed;
        return changed;
    }

    bool sub_solver::get_model(model_ref& md) {
        if (check() != l_true)
            return false;
        if (!m_model)
            m_solver->get_model(m_model);
        md = m_model;
        return md.get() != nullptr;
    }

    bool solver_facet::value(expr* e, rational& v) const {
        model_ref md = m_model;
        if (!md && !m_solver.get_model(md))
            return false;
        expr_ref r = (*md)(e);
        expr_safe_replace sub(m);
        expr* x, *y;
        for (expr* t : subterms::all(r))
            if (m.is_eq(t, x, y) && x != y && m.is_value(x) && m.is_value(y) && (m.is_model_value(x) || m.is_model_value(y)))
                sub.insert(t, m.mk_false());
        sub(r);
        return a.is_numeral((*md)(r), v);
    }

    lbool solver_facet::implies(expr* c, eq_tree::dep_tracker* core) const {
        expr_ref pin(c, m);
        m_solver.push();
        m_solver.assert_expr(m.mk_not(c));
        lbool r = m_solver.check();
        if (core)
            *core = r == l_false ? m_solver.unsat_core() : nullptr;
        m_solver.pop(1);
        // If `not c` is UNSAT then `c` is implied; otherwise report unknown.
        return r == l_false ? l_true : l_undef;
    }

    stx::facet_i* solver_facet::clone(trail_stack& trail) const {
        solver_facet* f = alloc(solver_facet, trail, m, u, m_solver);
        m_solver.get_model(f->m_model); // the leaf's arithmetic model, for exponent values
        // Snapshot clones do not own any new backend assertions.
        return f;
    }

    std::ostream& solver_facet::display(std::ostream& out) const {
        out << "solver_facet: " << m_own.size() << " own constraint(s)\n";
        for (expr* c : m_own)
            out << "  " << mk_pp(c, m) << "\n";
        return out;
    }

    // -- arith_propagation --

    stx::simplify_result arith_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        auto& ef = ac.eq_facet_ref();
        auto& sf = ac.solver_facet_ref();
        m_stats.m_num_propagate++;
        bool changed = false;
        for (auto const& eq : ef.equations()) {
            if (!eq.active())
                continue;
            changed = sf.add_length_constraint(eq.m_lhs, eq.m_rhs, eq.m_dep) || changed;
        }
        if (sf.has_conflict()) {
            n.set_conflict(stx::br_plugin_base, sf.conflict_dep());
            return stx::simplify_result::conflict;
        }
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

} // namespace seq
