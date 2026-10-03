/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_facet.cpp

Abstract:

    See seq_eq_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#include "ast/seq/seq_eq_facet.h"
#include "ast/seq/seq_solver_facet_i.h"
#include "ast/ast_pp.h"
#include "ast/occurs.h"
#include <algorithm>
#include <cstdlib>
#include <utility>

namespace seq {

    void subst_in(expr_ref_vector& ts, expr* var, expr_ref_vector const& repl) {
        expr_ref_vector orig(ts);
        ts.reset();
        for (unsigned i = 0; i < orig.size(); ++i) {
            if (orig.get(i) == var)
                ts.append(repl);
            else
                ts.push_back(orig.get(i));
        }
    }

    void eq_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        m_subst.push_back(subst_entry(m, var, repl));
        m_trail.push(push_back_trail<subst_entry>(m_subst));
        for (unsigned i = 0; i < m_eqs.size(); ++i) {
            if (!m_eqs[i].active())
                continue;
            bool touched_l = subst_in_trailed(m_trail, m_eqs, i, &equation::m_lhs, var, repl);
            bool touched_r = subst_in_trailed(m_trail, m_eqs, i, &equation::m_rhs, var, repl);
            if ((touched_l || touched_r) && subst_dep) {
                m_trail.push(vector_field_trail<equation, eq_tree::dep_tracker>(m_eqs, i, &equation::m_dep));
                m_eqs[i].m_dep = m_dm.mk_join(m_eqs[i].m_dep, subst_dep);
            }
        }
    }

    stx::facet_i* eq_facet::clone(trail_stack& trail) const {
        eq_facet* f = alloc(eq_facet, trail, m, u, m_dm);
        f->m_eqs.append(m_eqs);
        f->m_subst.append(m_subst);
        return f;
    }

    namespace {

        bool canonical_needs_swap(expr_ref_vector const& lhs, expr_ref_vector const& rhs) {
            if (lhs.size() != rhs.size())
                return lhs.size() > rhs.size();
            unsigned n = lhs.size();
            for (unsigned i = 0; i < n; ++i) {
                if (lhs.get(i) != rhs.get(i))
                    return lhs.get(i)->get_id() > rhs.get(i)->get_id();
            }
            return false;
        }

        uint64_t canonical_pair_hash(uint64_t tag, expr_ref_vector const& lhs, expr_ref_vector const& rhs) {
            bool swap = canonical_needs_swap(lhs, rhs);
            expr_ref_vector const& a = swap ? rhs : lhs;
            expr_ref_vector const& b = swap ? lhs : rhs;
            uint64_t h = stx::stx_hash_tag(tag);
            h = stx::stx_hash_ids(h, a);
            h = stx::stx_hash_ids(h, b);
            return h;
        }
    }

    uint64_t eq_facet::equation::hash() const {
        return canonical_pair_hash(0x6571u, m_lhs, m_rhs); // tag: "eq"
    }

    bool eq_facet::equation::equals(stx::constraint_i const& other) const {
        auto const* o = dynamic_cast<equation const*>(&other);       
        return o && ((m_lhs == o->m_lhs && m_rhs == o->m_rhs) || (m_lhs == o->m_rhs && m_rhs == o->m_lhs));
    }

    void eq_facet::append_constraints(vector<stx::constraint_i const*>& out) const {
        for (auto const& eq : m_eqs)
            if (eq.active())
                out.push_back(&eq);
    }

    bool eq_facet::get_subst(expr* var, expr_ref_vector& out) const {
        for (unsigned i = m_subst.size(); i-- > 0; ) {
            if (m_subst[i].m_var == var) {
                out.reset();
                out.append(m_subst[i].m_repl);
                return true;
            }
        }
        return false;
    }

    void eq_facet::eliminate(expr* e, expr_ref_vector& out) const {
        expr_ref_vector in(m);
        u.str.get_concat_units(e, in);
        eliminate(in, out);
    }

    void eq_facet::eliminate(expr_ref_vector const& in, expr_ref_vector& out) const {
        out.reset();
        ptr_vector<expr> todo;
        obj_hashtable<expr> on_stack;
        auto push_token = [&](expr* t) {
            todo.push_back(t);
            on_stack.insert(t);
        };
        for (unsigned i = in.size(); i-- > 0; )
            push_token(in.get(i));
        while (!todo.empty()) {
            expr* t = todo.back();
            todo.pop_back();
            on_stack.remove(t);
            expr_ref_vector repl(m);
            if (get_subst(t, repl) && !on_stack.contains(t)) {
                for (unsigned i = repl.size(); i-- > 0; )
                    push_token(repl.get(i));
            }
            else {
                out.push_back(t);
            }
        }
    }

    ambient_context_i<eq_tree::dep_tracker>& eq_facet::ambient(eq_tree::node const& n) const {
        if (auto* ac = dynamic_cast<ambient_context_i<eq_tree::dep_tracker>*>(n.ambient()))
            return *ac;
        throw default_exception("no facet");
    }

    ambient_ref<eq_tree::node, eq_tree::dep_tracker> get_ambient(eq_tree::node& n) {
        if (auto* ac = dynamic_cast<ambient_context_i<eq_tree::dep_tracker>*>(n.ambient()))
            return ambient_ref<eq_tree::node, eq_tree::dep_tracker>(n, *ac);
        throw default_exception("no facet");
    }

    ambient_ref<eq_tree::node const, eq_tree::dep_tracker> get_ambient(eq_tree::node const& n) {
        if (auto* ac = dynamic_cast<ambient_context_i<eq_tree::dep_tracker>*>(n.ambient()))
            return ambient_ref<eq_tree::node const, eq_tree::dep_tracker>(n, *ac);
        throw default_exception("no facet");
    }

    std::ostream& eq_facet::display(std::ostream& out) const {
        unsigned num_active = 0;
        for (auto const& eq : m_eqs)
            if (eq.active())
                ++num_active;
        out << "eq_facet: " << num_active << " equation(s) (" << m_eqs.size() << " total incl. inactive)\n";
        for (auto const& eq : m_eqs) {
            if (!eq.active())
                continue;
            out << "  ";
            for (expr* t : eq.m_lhs) out << mk_pp(t, m) << " ";
            out << "= ";
            for (expr* t : eq.m_rhs) out << mk_pp(t, m) << " ";
            out << "\n";
        }
        return out;
    }

    bool eq_facet::simplify_equation(eq_tree::node& n, ambient_context_i<eq_tree::dep_tracker>& ac, unsigned idx, bool& conflict, eq_tree::dep_tracker& conflict_dep, bool& changed) {
        equation& eq = m_eqs[idx];
        eq_tree::dep_tracker parent_dep = eq.m_dep;
        expr_ref_vector L(eq.m_lhs);
        expr_ref_vector R(eq.m_rhs);
        expr_ref_pair_vector new_eqs(m);
        bool eq_changed = false;
        if (!m_rw.reduce_eq(L, R, new_eqs, eq_changed)) {
            conflict = true;
            conflict_dep = eq.m_dep;
            return false;
        }
        // Even if reduce_eq reports no change, later checks still need to
        // handle empty-vs-nonempty states introduced by substitutions.
        if (eq_changed || !new_eqs.empty())
            changed = true;
        m_trail.push(vector_field_trail<equation, expr_ref_vector>(m_eqs, idx, &equation::m_lhs));
        m_trail.push(vector_field_trail<equation, expr_ref_vector>(m_eqs, idx, &equation::m_rhs));
        eq.m_lhs = std::move(L);
        eq.m_rhs = std::move(R);

        // Append newly produced sub-equations as trailed, definitional
        // consequences of the parent equation. Use parent_dep because
        // add_equation may reallocate m_eqs and invalidate `eq`.
        //
        // Unit-vs-unit decompositions may force equality between two
        // character terms. Check whether that equality is already false
        // in the ambient context before recording it as an assumption.
        for (auto const& [l, r] : new_eqs) {
            expr_ref_vector lts(m), rts(m);
            u.str.get_concat_units(l, lts);
            u.str.get_concat_units(r, rts);
            if (lts.size() == 1 && rts.size() == 1 && u.str.is_unit(lts.get(0)) && u.str.is_unit(rts.get(0))) {
                expr* lch = nullptr, *rch = nullptr;
                VERIFY(u.str.is_unit(lts.get(0), lch));
                VERIFY(u.str.is_unit(rts.get(0), rch));
                if (m.are_distinct(lch, rch)) {
                    conflict = true;
                    conflict_dep = parent_dep;
                    return false;
                }
                if (lch != rch) {
                    expr_ref eq_expr(m.mk_eq(lch, rch), m);
                    if (auto false_dep = ac.literal_if_false(eq_expr)) {
                        conflict = true;
                        conflict_dep = m_dm.mk_join(parent_dep, false_dep);
                        return false;
                    }
                    get_ambient(n).add_assumption(eq_expr, parent_dep);
                }
            }
            add_equation(lts, rts, parent_dep);
        }

        // If one side is empty, the other side must reduce to epsilon.
        // Leading variables become forced substitutions; a leading unit
        // is a conflict. Use broadcast_subst so sibling facets stay in sync.
        equation& cur = m_eqs[idx];
        if (cur.m_lhs.empty() != cur.m_rhs.empty()) {
            expr_ref_vector& side = cur.m_lhs.empty() ? cur.m_rhs : cur.m_lhs;
            eq_tree::dep_tracker eq_dep = cur.m_dep;
            while (!side.empty()) {
                expr* tok = side.get(0);
                if (u.str.is_unit(tok)) {
                    conflict = true;
                    conflict_dep = eq_dep;
                    return false;
                }
                expr_ref_vector empty_repl(m);
                broadcast_subst(n, tok, empty_repl, eq_dep);
            }
        }

        if (cur.m_lhs.empty() && cur.m_rhs.empty()) {
            m_trail.push(vector_field_trail<equation, bool>(m_eqs, idx, &equation::m_active));
            m_eqs[idx].m_active = false;
        }

        // If x = t and x does not occur in t, substitute x := t.
        for (int side = 0; side < 2; ++side) {
            expr_ref_vector const& vs = side == 0 ? cur.m_lhs : cur.m_rhs;
            expr_ref_vector def(side == 0 ? cur.m_rhs : cur.m_lhs);
            if (vs.size() != 1 || !ac.is_var(vs.get(0)))
                continue;
            expr_ref x(vs.get(0), m);
            if (any_of(def, [&](expr* t) { return occurs(x, t); }))
                continue;
            broadcast_subst(n, x, def, cur.m_dep);
            changed = true;
            break;
        }
        return true;
    }

    bool eq_facet::simplify(eq_tree::node& n, ambient_context_i<eq_tree::dep_tracker>& ac, bool& conflict, eq_tree::dep_tracker& conflict_dep) {
        conflict = false;
        conflict_dep = nullptr;
        bool changed = false;
        // Append-only: m_eqs never shrinks, so a plain forward scan
        // suffices (new equations appended by simplify_equation are
        // reached in due course without adjusting i).
        for (unsigned i = 0; i < m_eqs.size(); ++i) {
            if (!m_eqs[i].active())
                continue;
            if (!simplify_equation(n, ac, i, conflict, conflict_dep, changed)) {
                SASSERT(conflict);
                return true;
            }
        }
        return changed;
    }

    stx::simplify_result eq_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        auto& f = ac.eq_facet_ref();
        bool conflict = false;
        eq_tree::dep_tracker conflict_dep = nullptr;
        m_stats.m_num_propagate++;
        bool changed = f.simplify(n, ac.context(), conflict, conflict_dep);
        if (changed)
            m_stats.m_num_progress++;
        if (conflict) {
            n.set_conflict(stx::br_plugin_base, conflict_dep);
            return stx::simplify_result::conflict;
        }
        if (!changed)
            return stx::simplify_result::noop;
        return f.is_satisfied() ? stx::simplify_result::satisfied : stx::simplify_result::proceed;
    }

    // Broadcast a substitution to every subst_sink_i facet in the node so
    // token-based facets stay synchronized.
    void broadcast_subst(eq_tree::node& target, expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        for (unsigned id = 0; id < target.num_facets(); ++id) {
            if (!target.has_facet(id))
                continue;
            if (auto* sink = dynamic_cast<subst_sink_i*>(&target.facet(id)))
                sink->apply_subst(var, repl, subst_dep);
        }
        // Also assert the matching length equation for sequence-sorted
        // variables. Character-sorted substitutions have no len().
        auto ac = get_ambient(target);
        auto& sf = ac.solver_facet_ref();
        ast_manager& mgr = sf.get_arith_util().get_manager();
        if (var->get_sort()->get_family_id() != mgr.mk_family_id("seq"))
            return;
        expr_ref_vector lhs(mgr);
        lhs.push_back(var);
        sf.add_length_constraint(lhs, repl, subst_dep);
    }

    bool word_eq_split::iterator::next(eq_tree::edge& out) {
        if (m_pos >= m_pending.size())
            return false;
        auto& a = m_pending[m_pos++];
        broadcast_subst(m_n, a.m_var.get(), a.m_repl, a.m_dep);
        if (a.m_guard.get()) {
            auto ac = get_ambient(m_n);
            ac.solver_facet_ref().add_constraint(a.m_guard.get(), a.m_dep);
        }
        out = eq_tree::edge(a.m_name, a.m_dep, a.m_progress, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> word_eq_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        auto& f = ac.eq_facet_ref();

        for (auto const& eq : f.equations()) {
            if (!eq.active())
                continue;
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue; // fully resolved by propagation; shouldn't occur
            // Try both directions: a substitution may leave an equation
            // stuck only at the tail even if the head already simplifies.
            for (int dir = 0; dir < 2; ++dir) {
                bool fwd = dir == 0;
                expr* lh = fwd ? eq.m_lhs[0] : eq.m_lhs.back();
                expr* rh = fwd ? eq.m_rhs[0] : eq.m_rhs.back();
                bool lu = u.str.is_unit(lh);
                bool ru = u.str.is_unit(rh);
                bool lp = u.str.is_power(lh);
                bool rp = u.str.is_power(rh);
                if (lh == rh)
                    continue;
                if (lp || rp)
                    // Power tokens are handled by power_facet, not by
                    // Nielsen-style substitutions here.
                    continue;
                // A Nielsen-substitutable token is any non-unit, non-power token.
                bool lv = !lu && !lp;
                bool rv = !ru && !rp;
                // For two unit tokens, a distinct pair is a clash; an
                // incomparable symbolic pair is resolved by forcing the
                // tokens to coincide.
                if (lu && ru) {
                    expr* lch = nullptr, *rch = nullptr;
                    VERIFY(u.str.is_unit(lh, lch));
                    VERIFY(u.str.is_unit(rh, rch));
                    if (m.are_distinct(lch, rch))
                        continue;
                    if (lch == rch)
                        continue;
                    eq_tree::dep_tracker eq_dep = eq.m_dep;
                    // If the implied character equality is already false
                    // in the ambient context, report a conflict instead
                    // of substituting.
                    expr_ref eq_expr(m.mk_eq(lch, rch), m);
                    if (auto false_dep = ac.literal_if_false(eq_expr)) {
                        n.set_conflict(stx::br_plugin_base, f.dm().mk_join(eq_dep, false_dep));
                        return nullptr;
                    }
                    has_more = true;
                    // Prefer eliminating the non-constant side; otherwise
                    // eliminate the rhs token.
                    bool elim_lh = !u.is_const_char(lch) && u.is_const_char(rch);
                    expr* var_tok = elim_lh ? lh : rh;
                    expr* val_tok = elim_lh ? rh : lh;
                    expr_ref_vector repl(m);
                    repl.push_back(val_tok);
                    broadcast_subst(n, var_tok, repl, eq_dep);
                    // Record the implied character equality alongside the
                    // substitution.
                    ac.solver_facet_ref().add_constraint(eq_expr, eq_dep);
                    ac.assumption_facet_ref().add_assumption(eq_expr, ac.context());
                    out = eq_tree::edge("char-eq", eq_dep, true, 0);
                    committed = true;
                    m_stats.m_num_splits++;
                    return nullptr;
                }

                // Each alternative below resolves this single equation, so
                // all branches inherit eq_dep directly.
                eq_tree::dep_tracker eq_dep = eq.m_dep;

                if ((lv || !lu) && (rv || !ru)) {
                    // Two variables use the standard five Nielsen cases:
                    // either side is empty, the variables are equal, or
                    // one properly extends the other. The non-empty cases
                    // are guarded by len(v) > 0 to keep branches disjoint.
                    expr* v1 = lh;
                    expr* v2 = rh;
                    sort* s = v1->get_sort();
                    expr* v1p = f.mk_fresh_var(s);
                    expr* v2p = f.mk_fresh_var(s);

                    // The equal/extension branches require the eliminated
                    // variable to be non-empty.
                    expr* v1_pos = nullptr, *v2_pos = nullptr;
                    {
                        arith_util& a = ac.solver_facet_ref().get_arith_util();
                        // Character-sorted variables have no len() and are
                        // already non-empty.
                        if (u.is_seq(v1->get_sort()))
                            v1_pos = a.mk_gt(u.str.mk_length(v1), a.mk_int(0));
                        if (u.is_seq(v2->get_sort()))
                            v2_pos = a.mk_gt(u.str.mk_length(v2), a.mk_int(0));
                    }

                    // Pack the five standard alternatives so they can be
                    // reordered by length-bound feasibility before any of
                    // them is materialized. Index: 0 = v1:=eps, 1 =
                    // v2:=eps, 2 = v1:=v2, 3 = v1-extension, 4 =
                    // v2-extension.
                    struct branch { char const* name; expr* var; expr_ref_vector repl; expr* guard; bool progress; };
                    vector<branch> br;
                    {
                        expr_ref_vector e1(m);
                        br.push_back(branch{ "v1:=eps", v1, e1, nullptr, true });
                    }
                    {
                        expr_ref_vector e2(m);
                        br.push_back(branch{ "v2:=eps", v2, e2, nullptr, true });
                    }
                    {
                        expr_ref_vector repl(m);
                        repl.push_back(v2);
                        br.push_back(branch{ "v1:=v2", v1, repl, v1_pos, true });
                    }
                    {
                        expr_ref_vector repl(m);
                        if (fwd) { repl.push_back(v2); repl.push_back(v1p); }
                        else     { repl.push_back(v1p); repl.push_back(v2); }
                        br.push_back(branch{ fwd ? "v1:=v2.v1'" : "v1:=v1'.v2", v1, repl, v1_pos, false });
                    }
                    {
                        expr_ref_vector repl(m);
                        if (fwd) { repl.push_back(v1); repl.push_back(v2p); }
                        else     { repl.push_back(v2p); repl.push_back(v1); }
                        br.push_back(branch{ fwd ? "v2:=v1.v2'" : "v2:=v2'.v1", v2, repl, v2_pos, false });
                    }

                    // Try the branch that is most consistent with the
                    // ambient context's current length bounds on v1/v2
                    // first; this only reorders exploration (all five
                    // alternatives are still produced), so it cannot
                    // affect soundness or completeness. When bounds don't
                    // discriminate, the order is unchanged from before:
                    // v1:=eps, v2:=eps, v1:=v2, v1-ext, v2-ext.
                    unsigned order[5] = { 0, 1, 2, 3, 4 };
                    {
                        auto len_lo_hi = [&](expr* v, rational& lo, bool& has_hi, rational& hi) {
                            lo = rational::zero();
                            has_hi = false;
                            if (!u.is_seq(v->get_sort())) {
                                // Character-sorted variables have length
                                // exactly 1, never empty.
                                lo = rational::one();
                                has_hi = true;
                                hi = rational::one();
                                return;
                            }
                            eq_tree::dep_tracker dep = nullptr;
                            ac.lower_bound(u.str.mk_length(v), lo, dep);
                            has_hi = ac.upper_bound(u.str.mk_length(v), hi, dep);
                        };
                        rational lo1, hi1, lo2, hi2;
                        bool has_hi1, has_hi2;
                        len_lo_hi(v1, lo1, has_hi1, hi1);
                        len_lo_hi(v2, lo2, has_hi2, hi2);
                        bool v1_eps_ok = lo1.is_zero();
                        bool v2_eps_ok = lo2.is_zero();
                        unsigned pick = 2; // default: try equality first
                        if (has_hi2 && lo1 > hi2)
                            pick = 3; // v1 provably longer than any value v2 can take
                        else if (has_hi1 && lo2 > hi1)
                            pick = 4; // v2 provably longer than any value v1 can take
                        unsigned pos = 0;
                        if (v1_eps_ok)
                            order[pos++] = 0;
                        if (v2_eps_ok)
                            order[pos++] = 1;
                        order[pos++] = pick;
                        for (unsigned k = 2; k <= 4; ++k)
                            if (k != pick)
                                order[pos++] = k;
                        if (!v1_eps_ok)
                            order[pos++] = 0;
                        if (!v2_eps_ok)
                            order[pos++] = 1;
                        SASSERT(pos == 5);
                    }

                    iterator* it = alloc(iterator, n, m, u);
                    for (unsigned i = 1; i < 5; ++i) {
                        branch& b = br[order[i]];
                        it->push_back(b.name, b.var, b.repl, eq_dep, b.guard, b.progress);
                    }

                    // Materialize the chosen first branch now, in the
                    // scope the driver already pushed for this call.
                    branch& first = br[order[0]];
                    broadcast_subst(n, first.var, first.repl, eq_dep);
                    if (first.guard) {
                        auto gc = get_ambient(n);
                        gc.solver_facet_ref().add_constraint(first.guard, eq_dep);
                    }
                    out = eq_tree::edge(first.name, eq_dep, first.progress, 0);
                    committed = true;
                    m_stats.m_num_splits++;
                    return it;
                }

                // One side is a variable, the other a run of unit tokens.
                // Split against the whole block instead of one character
                // per search level.
                bool var_on_lhs = lv || !lu;
                expr* var = var_on_lhs ? lh : rh;
                expr_ref_vector const& var_side = var_on_lhs ? eq.m_lhs : eq.m_rhs;
                expr_ref_vector const& unit_side = var_on_lhs ? eq.m_rhs : eq.m_lhs;
                unsigned cap = ac.fparams().m_seq_block_compression;
                if (cap == 0) cap = UINT_MAX;
                expr_ref_vector block(m); // leading units of unit_side in direction fwd
                for (unsigned i = 0; i < unit_side.size() && block.size() < cap; ++i) {
                    expr* t = fwd ? unit_side[i] : unit_side[unit_side.size() - 1 - i];
                    if (!u.str.is_unit(t))
                        break;
                    block.push_back(t);
                }
                // Build the first k block tokens in natural order, with an optional tail.
                auto prefix_repl = [&](unsigned k, expr* tail) {
                    expr_ref_vector repl(m);
                    if (!fwd && tail) repl.push_back(tail);
                    for (unsigned j = 0; j < k; ++j) repl.push_back(block.get(fwd ? j : k - 1 - j));
                    if (fwd && tail) repl.push_back(tail);
                    return repl;
                };
                expr* var2 = f.mk_fresh_var(var->get_sort());
                expr* next_tok = var_side.size() > 1 ? (fwd ? var_side[1] : var_side[var_side.size() - 2]) : nullptr;

                iterator* it = alloc(iterator, n, m, u);
                for (unsigned k = 1; next_tok && k < block.size(); ++k) {
                    expr* a = nullptr, *b = nullptr;
                    if (u.str.is_unit(next_tok, a) && u.str.is_unit(block.get(k), b) && m.are_distinct(a, b))
                        continue; // the token after v cannot match the block where v would end
                    it->push_back("v:=block-prefix", var, prefix_repl(k, nullptr), eq_dep);
                }
                it->push_back(fwd ? "v:=c.v'" : "v:=v'.c", var, prefix_repl(block.size(), var2), eq_dep, nullptr, false);

                // Materialize the first branch now in the caller's scope.
                expr_ref_vector empty(m);
                broadcast_subst(n, var, empty, eq_dep);
                out = eq_tree::edge("v:=eps", eq_dep, true, 0);
                committed = true;
                m_stats.m_num_splits++;
                return it;
            }
        }
        return nullptr;
    }

    // -- eq_approx_split --

    // Build a concat expression from a token list for seq_eq_approx.
    static expr* eq_approx_tokens_to_expr(seq_util& u, expr_ref_vector const& ts) {
        if (ts.empty())
            return u.str.mk_empty(u.str.mk_string(zstring())->get_sort());
        return u.str.mk_concat(ts.size(), ts.data(), ts[0]->get_sort());
    }

    scoped_ptr<eq_tree::split_iterator_i> eq_approx_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        // Optional refutation pass.
        if (!ac.fparams().m_seq_eq_approx)
            return nullptr;
        auto& f = ac.eq_facet_ref();

        for (auto const& eq : f.equations()) {
            if (!eq.active())
                continue;
            expr_ref lhs(eq_approx_tokens_to_expr(u, eq.m_lhs), m);
            expr_ref rhs(eq_approx_tokens_to_expr(u, eq.m_rhs), m);
            m_stats.m_num_checks++;
            lbool r = m_approx.check(lhs, rhs);
            if (r == l_false) {
                // An empty segment-language intersection refutes the equation.
                m_stats.m_num_refuted++;
                n.set_conflict(stx::br_plugin_base, eq.m_dep);
                return nullptr;
            }
        }
        // No refutation.
        return nullptr;
    }

    // -- eq_split (mid-equation split with padding variable) --

    // Walk both sides, tracking the net variable-token balance and
    // constant-length difference. A valid split is interior on both
    // sides, has zero token balance, and minimizes |const_diff|.
    bool eq_split::find_eq_split_point(seq_util& u, expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                                        unsigned& out_lhs_idx, unsigned& out_rhs_idx, int& out_padding) {
        unsigned lhs_len = lhs.size();
        unsigned rhs_len = rhs.size();
        if (lhs_len <= 1 || rhs_len <= 1)
            return false;

        u_map<int> balance;
        unsigned nz = 0;
        int const_diff = 0;
        unsigned li = 0, ri = 0;
        unsigned lvars = 0, rvars = 0;
        bool seen_variable = false;
        bool has_best = false;
        unsigned best_lhs = 0, best_rhs = 0;
        int best_padding = 0;

        auto bump = [&](expr* tok, int d) {
            int b = 0;
            balance.find(tok->get_id(), b);
            if (b == 0) ++nz;
            b += d;
            if (b == 0) --nz;
            balance.insert(tok->get_id(), b);
        };

        while (true) {
            bool interior = li > 0 && li < lhs_len && ri > 0 && ri < rhs_len;
            if (seen_variable && nz == 0 && interior &&
                (!has_best || std::abs(const_diff) < std::abs(best_padding))) {
                has_best = true;
                best_padding = const_diff;
                best_lhs = li;
                best_rhs = ri;
            }
            bool l_done = li >= lhs_len;
            bool r_done = ri >= rhs_len;
            if (l_done && r_done)
                break;

            bool consume_lhs;
            if (l_done) consume_lhs = false;
            else if (r_done) consume_lhs = true;
            else if (lvars != rvars) consume_lhs = lvars < rvars;
            else consume_lhs = const_diff <= 0;

            expr* tok = consume_lhs ? lhs.get(li++) : rhs.get(ri++);
            // get_concat_units produces unit constants; every other token
            // has variable length.
            if (u.str.is_unit(tok)) {
                const_diff += (consume_lhs ? 1 : -1);
            }
            else {
                bump(tok, consume_lhs ? 1 : -1);
                ++(consume_lhs ? lvars : rvars);
                seen_variable = true;
            }
        }

        if (!has_best)
            return false;
        out_lhs_idx = best_lhs;
        out_rhs_idx = best_rhs;
        out_padding = best_padding;
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> eq_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        auto& f = ac.eq_facet_ref();
        auto& sf = ac.solver_facet_ref();

        for (unsigned idx = 0; idx < f.equations().size(); ++idx) {
            eq_facet::equation const& eq = f.equations()[idx];
            if (!eq.active())
                continue;
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue; // resolved by propagation; not eq_split's business
            unsigned split_lhs = 0, split_rhs = 0;
            int padding = 0;
            if (!find_eq_split_point(u, eq.m_lhs, eq.m_rhs, split_lhs, split_rhs, padding))
                continue;
            has_more = true;

            eq_tree::dep_tracker eq_dep = eq.m_dep;
            expr_ref_vector lhs_prefix(m), lhs_suffix(m), rhs_prefix(m), rhs_suffix(m);
            lhs_prefix.append(split_lhs, eq.m_lhs.data());
            lhs_suffix.append(eq.m_lhs.size() - split_lhs, eq.m_lhs.data() + split_lhs);
            rhs_prefix.append(split_rhs, eq.m_rhs.data());
            rhs_suffix.append(eq.m_rhs.size() - split_rhs, eq.m_rhs.data() + split_rhs);

            expr* pad = padding != 0 ? f.mk_fresh_var(eq.m_lhs[0]->get_sort()) : nullptr;
            expr_ref_vector eq1_lhs(m), eq1_rhs(m), eq2_lhs(m), eq2_rhs(m);
            eq1_lhs.append(lhs_prefix);
            eq1_rhs.append(rhs_prefix);
            eq2_lhs.append(lhs_suffix);
            eq2_rhs.append(rhs_suffix);
            if (pad) {
                if (padding > 0) {
                    // LHS prefix is longer by |padding|.
                    eq1_rhs.push_back(pad);
                    expr_ref_vector new_eq2_lhs(m);
                    new_eq2_lhs.push_back(pad);
                    new_eq2_lhs.append(eq2_lhs);
                    eq2_lhs.reset();
                    eq2_lhs.append(new_eq2_lhs);
                }
                else {
                    // Mirror: RHS prefix is longer by |padding|.
                    eq1_lhs.push_back(pad);
                    expr_ref_vector new_eq2_rhs(m);
                    new_eq2_rhs.push_back(pad);
                    new_eq2_rhs.append(eq2_rhs);
                    eq2_rhs.reset();
                    eq2_rhs.append(new_eq2_rhs);
                }
            }

            f.remove_equation_trailed(idx);
            f.add_equation(eq1_lhs, eq1_rhs, eq_dep);
            f.add_equation(eq2_lhs, eq2_rhs, eq_dep);

            if (pad) {
                expr_ref len_pad(u.str.mk_length(pad), m);
                sf.add_constraint(m.mk_eq(len_pad, sf.get_arith_util().mk_int(std::abs(padding))), eq_dep);
            }
            sf.add_length_constraint(eq1_lhs, eq1_rhs, eq_dep);
            sf.add_length_constraint(eq2_lhs, eq2_rhs, eq_dep);

            out = eq_tree::edge("eq-split", eq_dep, true, 0);
            committed = true;
            m_stats.m_num_splits++;
            return nullptr;
        }
        return nullptr;
    }

    // -- deq_facet --

    void deq_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        for (unsigned i = 0; i < m_diseqs.size(); ++i) {
            if (!m_diseqs[i].active())
                continue;
            bool touched_l = subst_in_trailed(m_trail, m_diseqs, i, &disequation::m_lhs, var, repl);
            bool touched_r = subst_in_trailed(m_trail, m_diseqs, i, &disequation::m_rhs, var, repl);
            if ((touched_l || touched_r) && subst_dep) {
                m_trail.push(vector_field_trail<disequation, eq_tree::dep_tracker>(m_diseqs, i, &disequation::m_dep));
                m_diseqs[i].m_dep = m_dm.mk_join(m_diseqs[i].m_dep, subst_dep);
            }
        }
    }

    stx::facet_i* deq_facet::clone(trail_stack& trail) const {
        deq_facet* f = alloc(deq_facet, trail, m, u, m_dm);
        f->m_diseqs.append(m_diseqs);
        return f;
    }

    uint64_t deq_facet::disequation::hash() const {
        return canonical_pair_hash(0x6465717u, m_lhs, m_rhs); // tag: "deq"
    }

    bool deq_facet::disequation::equals(stx::constraint_i const& other) const {
        auto const* o = dynamic_cast<disequation const*>(&other);
        return o && ((m_lhs == o->m_lhs && m_rhs == o->m_rhs) || (m_lhs == o->m_rhs && m_rhs == o->m_lhs));
    }

    void deq_facet::append_constraints(vector<stx::constraint_i const*>& out) const {
        for (auto const& dq : m_diseqs)
            if (dq.active())
                out.push_back(&dq);
    }

    std::ostream& deq_facet::display(std::ostream& out) const {
        unsigned num_active = 0;
        for (auto const& dq : m_diseqs)
            if (dq.active())
                ++num_active;
        out << "deq_facet: " << num_active << " disequation(s) (" << m_diseqs.size() << " total incl. inactive)\n";
        for (auto const& dq : m_diseqs) {
            if (!dq.active())
                continue;
            out << "  ";
            for (expr* t : dq.m_lhs) out << mk_pp(t, m) << " ";
            out << "!= ";
            for (expr* t : dq.m_rhs) out << mk_pp(t, m) << " ";
            out << "\n";
        }
        return out;
    }

    bool deq_facet::simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep) {
        conflict = false;
        conflict_dep = nullptr;
        bool changed = false;
        // Append-only: m_diseqs never shrinks, so a plain forward scan
        // suffices.
        for (unsigned i = 0; i < m_diseqs.size(); ++i) {
            if (!m_diseqs[i].active())
                continue;
            disequation& dq = m_diseqs[i];
            expr_ref_vector& L = dq.m_lhs;
            expr_ref_vector& R = dq.m_rhs;

            // If the equation is inconsistent, its negation is valid and
            // the disequation is discharged.
            {
                expr_ref_vector eq_lhs(L), eq_rhs(R);
                expr_ref_pair_vector new_eqs(m);
                bool eq_changed = false;
                if (!m_rw.reduce_eq(eq_lhs, eq_rhs, new_eqs, eq_changed)) {
                    m_trail.push(vector_field_trail<disequation, bool>(m_diseqs, i, &disequation::m_active));
                    m_diseqs[i].m_active = false;
                    changed = true;
                    continue;
                }
            }

            // strip a common leading prefix, exactly as eq_facet::simplify.
            unsigned li = 0, ri = 0;
            while (li < L.size() && ri < R.size() && L.get(li) == R.get(ri)) {
                ++li; ++ri;
            }
            if (li > 0 || ri > 0) {
                expr_ref_vector newL(m), newR(m);
                newL.append(L.size() - li, L.data() + li);
                newR.append(R.size() - ri, R.data() + ri);
                m_trail.push(vector_field_trail<disequation, expr_ref_vector>(m_diseqs, i, &disequation::m_lhs));
                m_trail.push(vector_field_trail<disequation, expr_ref_vector>(m_diseqs, i, &disequation::m_rhs));
                L = std::move(newL);
                R = std::move(newR);
                changed = true;
            }

            if (L.empty() && R.empty()) {
                // both sides forced identical: the disequation cannot hold.
                conflict = true;
                conflict_dep = dq.m_dep;
                return true;
            }

            if (!L.empty() && !R.empty()) {
                expr* lh = L.get(0);
                expr* rh = R.get(0);
                if (u.str.is_unit(lh) && u.str.is_unit(rh) && m.are_distinct(lh, rh)) {
                    // distinct leading constants: the two sides can never
                    // be made equal by any future substitution - the
                    // disequation is proved and discharged.
                    m_trail.push(vector_field_trail<disequation, bool>(m_diseqs, i, &disequation::m_active));
                    m_diseqs[i].m_active = false;
                    changed = true;
                    continue;
                }
            }

            // Otherwise stuck: one side is empty with the other led by a
            // variable (not yet resolved to epsilon or not), or the
            // leading tokens are a variable vs. constant / two variables.
            // deq_facet never invents its own substitution (see module
            // comment) - it waits for eq_facet's split to narrow things
            // further and re-broadcast via apply_subst.
        }
        return changed;
    }

    stx::simplify_result deq_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        auto& f = ac.deq_facet_ref();
        bool conflict = false;
        eq_tree::dep_tracker conflict_dep = nullptr;
        m_stats.m_num_propagate++;
        bool changed = f.simplify(conflict, conflict_dep);
        if (conflict) {
            n.set_conflict(stx::br_plugin_base, conflict_dep);
            return stx::simplify_result::conflict;
        }
        if (!changed)
            return stx::simplify_result::noop;
        return f.is_satisfied() ? stx::simplify_result::satisfied : stx::simplify_result::proceed;
    }

    // -- deq_split --

    // Sum the lengths of all tokens on one side.
    static expr_ref mk_side_len(seq_util& u, arith_util& a, ast_manager& m, expr_ref_vector const& toks) {
        expr_ref sum(a.mk_int(0), m);
        for (expr* tok : toks)
            sum = expr_ref(a.mk_add(sum, u.str.is_unit(tok) ? (expr*)a.mk_int(1) : (expr*)u.str.mk_length(tok)), m);
        return sum;
    }

    // Split the first unresolved disequation into two length-order cases
    // and one equal-length decomposition. Branch resumption backtracks to
    // the same node state, so idx remains valid across iterator steps.
    scoped_ptr<eq_tree::split_iterator_i> deq_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        auto& f = ac.deq_facet_ref();

        for (unsigned idx = 0; idx < f.disequations().size(); ++idx) {
            deq_facet::disequation const& dq = f.disequations()[idx];
            if (dq.m_lhs.empty() || dq.m_rhs.empty())
                continue; // resolved by propagation; shouldn't occur
            has_more = true;

            eq_tree::dep_tracker dq_dep = dq.m_dep;
            expr_ref_vector lhs(dq.m_lhs), rhs(dq.m_rhs);
            auto& sf = ac.solver_facet_ref();
            expr_ref len_lhs = mk_side_len(u, sf.get_arith_util(), m, lhs);
            expr_ref len_rhs = mk_side_len(u, sf.get_arith_util(), m, rhs);

            iterator* it = alloc(iterator, n, idx, lhs, rhs, dq_dep, 2, m, u);

            // A strict length mismatch already proves the disequation.
            f.remove_disequation_trailed(idx);
            sf.add_constraint(sf.get_arith_util().mk_lt(len_lhs, len_rhs), dq_dep);
            out = eq_tree::edge("diseq len<", dq_dep, true, 0);
            committed = true;
            m_stats.m_num_splits++;
            return it;
        }
        return nullptr;
    }

    bool deq_split::iterator::next(eq_tree::edge& out) {
        if (m_next_case > 3)
            return false;
        unsigned this_case = m_next_case++;
        auto ac = get_ambient(m_n);
        auto& sf = ac.solver_facet_ref();
        expr_ref len_lhs = mk_side_len(u, sf.get_arith_util(), m, m_lhs);
        expr_ref len_rhs = mk_side_len(u, sf.get_arith_util(), m, m_rhs);
        auto& f = ac.deq_facet_ref();

        if (this_case == 2) {
            // Symmetric length-mismatch branch.
            f.remove_disequation_trailed(m_diseq_idx);
            sf.add_constraint(sf.get_arith_util().mk_lt(len_rhs, len_lhs), m_dep);
            out = eq_tree::edge("diseq len>", m_dep, true, 0);
            return true;
        }

        // Equal-length case: factor out a common prefix and reduce the
        // disequation to a single differing character.
        auto& ef = ac.eq_facet_ref();
        sort* seq_sort = m_lhs[0]->get_sort();
        sort* char_sort = nullptr;
        VERIFY(u.is_seq(seq_sort, char_sort));
        expr* w = m.mk_fresh_const("diseq.w", seq_sort);
        expr* a_ch = m.mk_fresh_const("diseq.a", char_sort);
        expr* b_ch = m.mk_fresh_const("diseq.b", char_sort);
        expr* a_unit = u.str.mk_unit(a_ch);
        expr* b_unit = u.str.mk_unit(b_ch);
        expr* up = m.mk_fresh_const("diseq.u'", seq_sort);
        expr* vp = m.mk_fresh_const("diseq.v'", seq_sort);

        expr_ref_vector u_rhs(m); u_rhs.push_back(w); u_rhs.push_back(a_unit); u_rhs.push_back(up);
        expr_ref_vector v_rhs(m); v_rhs.push_back(w); v_rhs.push_back(b_unit); v_rhs.push_back(vp);
        ef.add_equation(m_lhs, u_rhs, m_dep);
        ef.add_equation(m_rhs, v_rhs, m_dep);

        expr_ref len_up(u.str.mk_length(up), m);
        expr_ref len_vp(u.str.mk_length(vp), m);
        sf.add_constraint(m.mk_eq(len_up, len_vp), m_dep);

        f.remove_disequation_trailed(m_diseq_idx);
        expr_ref_vector a_vec(m); a_vec.push_back(a_unit);
        expr_ref_vector b_vec(m); b_vec.push_back(b_unit);
        f.add_disequation(a_vec, b_vec, m_dep);

        out = eq_tree::edge("diseq split", m_dep, true, 0);
        return true;
    }

} // namespace seq
