/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_facet.cpp

Abstract:

    See seq_eq_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/seq/seq_eq_facet.h"
#include "ast/seq/seq_arith_facet_i.h"
#include <algorithm>
#include <cstdlib>
#include <utility>

namespace seq {

    bool is_const_token(seq_util& u, expr* e) {
        zstring s;
        return u.str.is_string(e, s) && s.length() == 1;
    }

    void flatten(seq_util& u, expr* e, expr_ref_vector& out) {
        expr* a = nullptr, *b = nullptr;
        if (u.str.is_concat(e, a, b)) {
            flatten(u, a, out);
            flatten(u, b, out);
            return;
        }
        zstring s;
        if (u.str.is_string(e, s)) {
            for (unsigned i = 0; i < s.length(); ++i)
                out.push_back(u.str.mk_string(zstring(s[i])));
            return;
        }
        if (u.str.is_empty(e))
            return;
        out.push_back(e);
    }

    static int cmp_tokens(expr_ref_vector const& a, expr_ref_vector const& b) {
        unsigned n = std::min(a.size(), b.size());
        for (unsigned i = 0; i < n; ++i) {
            unsigned ida = a[i]->get_id(), idb = b[i]->get_id();
            if (ida != idb)
                return ida < idb ? -1 : 1;
        }
        if (a.size() != b.size())
            return a.size() < b.size() ? -1 : 1;
        return 0;
    }

    bool eq_facet::equation::operator<(equation const& other) const {
        int c = cmp_tokens(m_lhs, other.m_lhs);
        if (c != 0)
            return c < 0;
        return cmp_tokens(m_rhs, other.m_rhs) < 0;
    }

    bool eq_facet::equation::operator==(equation const& other) const {
        return cmp_tokens(m_lhs, other.m_lhs) == 0 && cmp_tokens(m_rhs, other.m_rhs) == 0;
    }

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
        for (unsigned i = 0; i < m_eqs.size(); ++i) {
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
        return f;
    }

    unsigned eq_facet::hash() const {
        // Order-independent: the equation set is a set, not a sequence, so
        // combine per-equation hashes commutatively (sum) rather than with
        // combine_hash (which is order-sensitive).
        unsigned h = m_eqs.size() * 2654435761u;
        for (auto const& eq : m_eqs) {
            unsigned eh = 1;
            for (expr* t : eq.m_lhs) eh = combine_hash(eh, t->get_id());
            eh = combine_hash(eh, 0x9e3779b9u);
            for (expr* t : eq.m_rhs) eh = combine_hash(eh, t->get_id());
            h += eh;
        }
        return h ? h : 1;
    }

    bool eq_facet::similar(facet_i const& other) const {
        auto const& o = static_cast<eq_facet const&>(other);
        if (m_eqs.size() != o.m_eqs.size())
            return false;
        vector<equation> a = m_eqs, b = o.m_eqs;
        std::sort(a.begin(), a.end());
        std::sort(b.begin(), b.end());
        for (unsigned i = 0; i < a.size(); ++i)
            if (!(a[i] == b[i]))
                return false;
        return true;
    }

    bool eq_facet::simplify_equation(unsigned idx, bool& conflict, eq_tree::dep_tracker& conflict_dep, bool& changed) {
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
        // NOTE: do not early-return here just because reduce_eq itself made
        // no change - L/R may already be in an unresolved empty-vs-nonempty
        // state (e.g. because some other facet's apply_subst just emptied
        // one side directly, without going through reduce_eq at all), and
        // that state must still be checked/resolved below on every call,
        // not only when reduce_eq itself reports a change.
        if (eq_changed || !new_eqs.empty())
            changed = true;
        m_trail.push(vector_field_trail<equation, expr_ref_vector>(m_eqs, idx, &equation::m_lhs));
        m_trail.push(vector_field_trail<equation, expr_ref_vector>(m_eqs, idx, &equation::m_rhs));
        eq.m_lhs = std::move(L);
        eq.m_rhs = std::move(R);

        // reduce_eq strips common prefixes/suffixes and performs other
        // deterministic simplifications, but (unlike the old hand-rolled
        // loop) does not itself force the remaining tokens of a side to
        // epsilon when the other side has already been fully consumed -
        // do that here: pop leading variables as forced (unconditional)
        // substitutions v := epsilon, justified by this equation's own
        // dependency; a leading constant on the nonempty side at this
        // point is a symbol clash (conflict).
        if (eq.m_lhs.empty() != eq.m_rhs.empty()) {
            expr_ref_vector& side = eq.m_lhs.empty() ? eq.m_rhs : eq.m_lhs;
            eq_tree::dep_tracker eq_dep = eq.m_dep;
            while (!side.empty()) {
                expr* tok = side.get(0);
                if (is_const_token(u, tok)) {
                    conflict = true;
                    conflict_dep = eq_dep;
                    return false;
                }
                expr_ref_vector empty_repl(m);
                apply_subst(tok, empty_repl, eq_dep);
            }
        }

        if (eq.m_lhs.empty() && eq.m_rhs.empty()) {
            m_trail.push(vector_erase_trail<equation>(m_eqs, idx));
            m_eqs.erase(m_eqs.begin() + idx);
        }

        // Any newly-produced sub-equations (from unit-vs-unit
        // decomposition, length reasoning, etc.) are appended as fresh
        // equations, trailed. The decomposition is definitional (not an
        // added assumption), so each sub-equation inherits the parent
        // equation's dependency directly rather than joining a fresh leaf.
        // NOTE: `eq` may be a dangling reference at this point if the
        // equation at idx was just erased above (the vector element it
        // referred to has been shifted/removed) - capture the dependency
        // we need (parent_dep) BEFORE the erase, not here.
        for (unsigned i = 0; i < new_eqs.size(); ++i) {
            auto p = new_eqs[i].get();
            expr_ref_vector lts(m), rts(m);
            flatten(u, p.first, lts);
            flatten(u, p.second, rts);
            add_equation_trailed(lts, rts, parent_dep);
        }
        return true;
    }

    bool eq_facet::simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep) {
        conflict = false;
        conflict_dep = nullptr;
        bool changed = false;
        for (unsigned i = 0; i < m_eqs.size(); ) {
            unsigned sz_before = m_eqs.size();
            if (!simplify_equation(i, conflict, conflict_dep, changed)) {
                SASSERT(conflict);
                return true;
            }
            // If the equation at i was erased (set shrunk), stay at i to
            // process the equation that shifted into its place; otherwise
            // advance. New equations are appended at the end, so they are
            // reached in due course without adjusting i.
            if (m_eqs.size() < sz_before)
                continue;
            ++i;
        }
        return changed;
    }

    stx::simplify_result eq_propagation::propagate(eq_tree::node& n) {
        auto& f = n.facet_as<eq_facet>(m_id);
        bool conflict = false;
        eq_tree::dep_tracker conflict_dep = nullptr;
        bool changed = f.simplify(conflict, conflict_dep);
        if (conflict) {
            n.set_conflict(stx::br_plugin_base, conflict_dep);
            return stx::simplify_result::conflict;
        }
        if (f.is_satisfied())
            return stx::simplify_result::satisfied;
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

    // Broadcast a substitution chosen by eq_facet's Nielsen split to every
    // other facet in `target` that implements subst_sink_i (e.g.
    // deq_facet), so their state stays consistent with the branch. `eq_id`
    // is skipped since the caller has already applied the substitution to
    // that facet directly.
    static void broadcast_subst(eq_tree::node& target, stx::facet_id eq_id, expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        for (unsigned id = 0; id < target.num_facets(); ++id) {
            if (id == eq_id || !target.has_facet(id))
                continue;
            if (auto* sink = dynamic_cast<subst_sink_i*>(&target.facet(id)))
                sink->apply_subst(var, repl, subst_dep);
        }
    }

    bool word_eq_split::iterator::next(eq_tree::edge& out) {
        if (m_pos >= m_pending.size())
            return false;
        auto& a = m_pending[m_pos++];
        m_n.facet_as<eq_facet>(m_id).apply_subst(a.m_var, a.m_repl, a.m_dep);
        broadcast_subst(m_n, m_id, a.m_var, a.m_repl, a.m_dep);
        out = eq_tree::edge(a.m_name, a.m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> word_eq_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0)
            return nullptr;
        auto& f = n.facet_as<eq_facet>(m_id);

        for (auto const& eq : f.equations()) {
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue; // fully resolved by propagation; shouldn't occur
            expr* lh = eq.m_lhs[0];
            expr* rh = eq.m_rhs[0];
            bool lc = is_const_token(u, lh);
            bool rc = is_const_token(u, rh);
            if (lc && rc)
                continue; // resolved by propagation
            if (!lc && !rc && lh == rh)
                continue; // resolved by propagation

            // Every alternative below is a case-split on how to unstick
            // this one equation, so all of them (and the immediately
            // materialized first branch) are justified by this
            // equation's own dependency, not a join of several.
            eq_tree::dep_tracker eq_dep = eq.m_dep;

            if (!lc && !rc) {
                // Two distinct variables lh, rh: the classic 4-branch
                // Nielsen transformation for word equations (design doc
                // facet-eq-deq.md section 2.2 / c3 branch's
                // apply_var_nielsen). Since v1, v2 are symbols at the
                // head of each side, exactly one of these must hold in
                // any solution:
                //   (1) v1 := epsilon
                //   (2) v2 := epsilon
                //   (3) v1 := v2 . v1'   (v1 is at least as long as v2)
                //   (4) v2 := v1 . v2'   (v2 is at least as long as v1)
                // Branches (3)/(4) are the "non-progress" cases (they
                // introduce a fresh variable rather than shrinking the
                // equation), but are still required for completeness:
                // without them, any solution where both v1 and v2 are
                // non-empty and neither is a literal prefix of the other
                // one being consumed first is unreachable.
                expr* v1 = lh;
                expr* v2 = rh;
                sort* s = v1->get_sort();
                expr* v1p = f.mk_fresh_var(s);
                expr* v2p = f.mk_fresh_var(s);

                iterator* it = alloc(iterator, n, m_id);
                {
                    expr_ref_vector empty(m);
                    it->push_back("v2:=eps", v2, empty, eq_dep);
                }
                {
                    expr_ref_vector repl(m);
                    repl.push_back(v2);
                    repl.push_back(v1p);
                    it->push_back("v1:=v2.v1'", v1, repl, eq_dep);
                }
                {
                    expr_ref_vector repl(m);
                    repl.push_back(v1);
                    repl.push_back(v2p);
                    it->push_back("v2:=v1.v2'", v2, repl, eq_dep);
                }

                // Materialize the first branch ("v1:=eps") now, in the
                // scope the driver already pushed for this call.
                expr_ref_vector empty(m);
                f.apply_subst(v1, empty, eq_dep);
                broadcast_subst(n, m_id, v1, empty, eq_dep);
                out = eq_tree::edge("v1:=eps", eq_dep, true, 0);
                committed = true;
                return it;
            }

            // one side is a variable, the other a constant
            expr* var = lc ? rh : lh;
            expr* c = lc ? lh : rh;
            sort* s = var->get_sort();
            expr* var2 = f.mk_fresh_var(s);

            iterator* it = alloc(iterator, n, m_id);
            {
                expr_ref_vector repl(m);
                repl.push_back(c);
                repl.push_back(var2);
                it->push_back("v:=c.v'", var, repl, eq_dep);
            }

            // Materialize the first branch ("v:=eps") now, in the scope
            // the driver already pushed for this call.
            expr_ref_vector empty(m);
            f.apply_subst(var, empty, eq_dep);
            broadcast_subst(n, m_id, var, empty, eq_dep);
            out = eq_tree::edge("v:=eps", eq_dep, true, 0);
            committed = true;
            return it;
        }
        return nullptr;
    }

    // -- eq_split (mid-equation split with padding variable) --

    // Ported from the c3 branch's find_eq_split_point
    // (seq_nielsen_modifiers.cpp): walk tokens from each side, tracking a
    // per-token-id signed balance of variable-length tokens consumed on
    // LHS (+1) vs RHS (-1), plus a running net constant-length difference
    // (const_diff). A split point is valid when the balance is entirely
    // zero (nz==0, i.e. the two prefixes consumed the exact same
    // multiset of variable tokens so far, so their symbolic lengths
    // cancel) and interior on both sides (never at an endpoint - an
    // endpoint split degenerates to the original equation with a renamed
    // tail, no progress). Among valid split points, keep the one
    // minimizing |const_diff| (the padding amount).
    //
    // NOTE (preserved from c3 branch history): an earlier version used
    // two booleans ("has a variable-length token been consumed on this
    // side") instead of a per-token signed balance, requiring both false
    // *after* a variable had been seen - unsatisfiable, so that version
    // never fired. The per-token balance above is the correct fix.
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
            // A length-1 string constant is const-length 1 (flatten()'s
            // token model never produces longer constant tokens); every
            // other token (opaque variable, fresh Skolem, etc.) is
            // variable-length.
            if (is_const_token(u, tok)) {
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
        if (cost != 0)
            return nullptr;
        auto& f = n.facet_as<eq_facet>(m_eq_id);
        auto& af = n.facet_as<arith_facet_i>(m_arith_id);

        for (unsigned idx = 0; idx < f.equations().size(); ++idx) {
            eq_facet::equation const& eq = f.equations()[idx];
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue; // resolved by propagation; not eq_split's business
            unsigned split_lhs = 0, split_rhs = 0;
            int padding = 0;
            if (!find_eq_split_point(u, eq.m_lhs, eq.m_rhs, split_lhs, split_rhs, padding))
                continue;
            has_more = true; // an alternative exists at this cost, even if not yet materialized below (loop continues to next equation only on failure)

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
                    // LHS prefix is longer by |padding|: rhs_prefix.pad = lhs_prefix, pad.lhs_suffix = rhs_suffix.
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
            f.add_equation_trailed(eq1_lhs, eq1_rhs, eq_dep);
            f.add_equation_trailed(eq2_lhs, eq2_rhs, eq_dep);

            if (pad) {
                expr_ref len_pad(u.str.mk_length(pad), m);
                af.add_constraint(m.mk_eq(len_pad, af.get_arith_util().mk_int(std::abs(padding))), eq_dep);
            }
            af.add_length_constraint(eq1_lhs, eq1_rhs, eq_dep);
            af.add_length_constraint(eq2_lhs, eq2_rhs, eq_dep);

            out = eq_tree::edge("eq-split", eq_dep, true, 0);
            committed = true;
            return nullptr; // single deterministic progress branch, no resumable iterator
        }
        return nullptr;
    }

    // -- deq_facet --

    bool deq_facet::disequation::operator<(disequation const& other) const {
        int c = cmp_tokens(m_lhs, other.m_lhs);
        if (c != 0)
            return c < 0;
        return cmp_tokens(m_rhs, other.m_rhs) < 0;
    }

    bool deq_facet::disequation::operator==(disequation const& other) const {
        return cmp_tokens(m_lhs, other.m_lhs) == 0 && cmp_tokens(m_rhs, other.m_rhs) == 0;
    }

    void deq_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        for (unsigned i = 0; i < m_diseqs.size(); ++i) {
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

    unsigned deq_facet::hash() const {
        // Order-independent, same rationale as eq_facet::hash.
        unsigned h = m_diseqs.size() * 2246822519u;
        for (auto const& dq : m_diseqs) {
            unsigned dh = 1;
            for (expr* t : dq.m_lhs) dh = combine_hash(dh, t->get_id());
            dh = combine_hash(dh, 0x85ebca6bu);
            for (expr* t : dq.m_rhs) dh = combine_hash(dh, t->get_id());
            h += dh;
        }
        return h ? h : 1;
    }

    bool deq_facet::similar(facet_i const& other) const {
        auto const& o = static_cast<deq_facet const&>(other);
        if (m_diseqs.size() != o.m_diseqs.size())
            return false;
        vector<disequation> a = m_diseqs, b = o.m_diseqs;
        std::sort(a.begin(), a.end());
        std::sort(b.begin(), b.end());
        for (unsigned i = 0; i < a.size(); ++i)
            if (!(a[i] == b[i]))
                return false;
        return true;
    }

    bool deq_facet::simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep) {
        conflict = false;
        conflict_dep = nullptr;
        bool changed = false;
        for (unsigned i = 0; i < m_diseqs.size(); ) {
            disequation& dq = m_diseqs[i];
            expr_ref_vector& L = dq.m_lhs;
            expr_ref_vector& R = dq.m_rhs;

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
                if (is_const_token(u, lh) && is_const_token(u, rh) && lh != rh) {
                    // distinct leading constants: the two sides can never
                    // be made equal by any future substitution - the
                    // disequation is proved and discharged.
                    m_trail.push(vector_erase_trail<disequation>(m_diseqs, i));
                    m_diseqs.erase(m_diseqs.begin() + i);
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
            ++i;
        }
        return changed;
    }

    stx::simplify_result deq_propagation::propagate(eq_tree::node& n) {
        auto& f = n.facet_as<deq_facet>(m_id);
        bool conflict = false;
        eq_tree::dep_tracker conflict_dep = nullptr;
        bool changed = f.simplify(conflict, conflict_dep);
        if (conflict) {
            n.set_conflict(stx::br_plugin_base, conflict_dep);
            return stx::simplify_result::conflict;
        }
        if (f.is_satisfied())
            return stx::simplify_result::satisfied;
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

} // namespace seq
