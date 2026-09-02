/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_facet.cpp

Abstract:

    See seq_eq_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/rewriter/seq_eq_facet.h"
#include <algorithm>
#include <utility>

namespace seq {

    bool is_const_token(seq_util& u, expr* e) {
        zstring s;
        return u.str.is_string(e, s) && s.length() == 1;
    }

    void flatten(seq_util& u, expr* e, token_list& out) {
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

    static int cmp_tokens(token_list const& a, token_list const& b) {
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

    void subst_in(token_list& ts, expr* var, token_list const& repl) {
        token_list orig(ts);
        ts.reset();
        for (unsigned i = 0; i < orig.size(); ++i) {
            if (orig.get(i) == var) {
                for (unsigned j = 0; j < repl.size(); ++j)
                    ts.push_back(repl.get(j));
            }
            else {
                ts.push_back(orig.get(i));
            }
        }
    }

    void eq_facet::apply_subst(expr* var, token_list const& repl) {
        for (unsigned i = 0; i < m_eqs.size(); ++i) {
            subst_in_trailed(m_trail, m_eqs, i, &equation::m_lhs, var, repl);
            subst_in_trailed(m_trail, m_eqs, i, &equation::m_rhs, var, repl);
        }
    }

    stx::facet_i* eq_facet::clone(trail_stack& trail) const {
        eq_facet* f = alloc(eq_facet, trail, m, u);
        for (auto const& eq : m_eqs)
            f->m_eqs.push_back(eq);
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

    bool eq_facet::simplify(bool& conflict) {
        conflict = false;
        bool changed = false;
        for (unsigned i = 0; i < m_eqs.size(); ) {
            equation& eq = m_eqs[i];
            token_list& L = eq.m_lhs;
            token_list& R = eq.m_rhs;

            // strip a common leading prefix (constants are interned by the
            // ast_manager, so pointer equality already captures "same
            // character"; same-identity variables strip the same way).
            unsigned li = 0, ri = 0;
            while (li < L.size() && ri < R.size() && L.get(li) == R.get(ri)) {
                ++li; ++ri;
            }
            if (li > 0 || ri > 0) {
                token_list newL(m), newR(m);
                for (unsigned k = li; k < L.size(); ++k) newL.push_back(L.get(k));
                for (unsigned k = ri; k < R.size(); ++k) newR.push_back(R.get(k));
                // Fine-grained: undo restores just this equation's two
                // token_list fields addressed by (m_eqs, i, member), safe
                // across later erase()/push_back() reallocation - not the
                // whole m_eqs vector.
                m_trail.push(vector_field_trail<equation, token_list>(m_eqs, i, &equation::m_lhs));
                m_trail.push(vector_field_trail<equation, token_list>(m_eqs, i, &equation::m_rhs));
                L = std::move(newL);
                R = std::move(newR);
                changed = true;
            }

            bool lempty = L.empty();
            bool rempty = R.empty();

            if (lempty && rempty) {
                m_trail.push(vector_erase_trail<equation>(m_eqs, i));
                m_eqs.erase(m_eqs.begin() + i);
                changed = true;
                continue;
            }

            if (lempty != rempty) {
                // The empty side forces the nonempty side to be empty too:
                // pop constants -> conflict; pop variables -> forced
                // (unconditional) substitution v := epsilon.
                bool bad = false;
                while (true) {
                    token_list& side = L.empty() ? R : L;
                    if (side.empty())
                        break;
                    expr* tok = side.get(0);
                    if (is_const_token(u, tok)) {
                        bad = true;
                        break;
                    }
                    token_list empty_repl(m);
                    apply_subst(tok, empty_repl);
                    changed = true;
                }
                if (bad) {
                    conflict = true;
                    return true;
                }
                m_trail.push(vector_erase_trail<equation>(m_eqs, i));
                m_eqs.erase(m_eqs.begin() + i);
                changed = true;
                continue;
            }

            // both sides nonempty: check for a symbol clash between two
            // distinct leading constants (equal-value constants would
            // already have been stripped above, since equal-value string
            // constants are the same interned expr*).
            expr* lh = L.get(0);
            expr* rh = R.get(0);
            if (is_const_token(u, lh) && is_const_token(u, rh)) {
                conflict = true;
                return true;
            }
            // otherwise: stuck (variable vs constant, or two distinct
            // variables) - left for the split plugin.
            ++i;
        }
        return changed;
    }

    stx::simplify_result eq_propagation::propagate(eq_tree::node& n) {
        auto& f = n.facet_as<eq_facet>(m_id);
        bool conflict = false;
        f.simplify(conflict);
        if (conflict) {
            n.set_conflict(stx::br_plugin_base, nullptr);
            return stx::simplify_result::conflict;
        }
        if (f.is_satisfied())
            return stx::simplify_result::satisfied;
        return stx::simplify_result::proceed;
    }

    // Broadcast a substitution chosen by eq_facet's Nielsen split to every
    // other facet in `target` that implements subst_sink_i (e.g.
    // deq_facet), so their state stays consistent with the branch. `eq_id`
    // is skipped since the caller has already applied the substitution to
    // that facet directly.
    static void broadcast_subst(eq_tree::node& target, stx::facet_id eq_id, expr* var, token_list const& repl) {
        for (unsigned id = 0; id < target.num_facets(); ++id) {
            if (id == eq_id || !target.has_facet(id))
                continue;
            if (auto* sink = dynamic_cast<subst_sink_i*>(&target.facet(id)))
                sink->apply_subst(var, repl);
        }
    }

    bool word_eq_split::iterator::next(eq_tree::edge& out) {
        if (m_pos >= m_pending.size())
            return false;
        auto& a = m_pending[m_pos++];
        m_n.facet_as<eq_facet>(m_id).push_scope();
        m_n.facet_as<eq_facet>(m_id).apply_subst(a.m_var, a.m_repl);
        broadcast_subst(m_n, m_id, a.m_var, a.m_repl);
        out = eq_tree::edge(a.m_name, nullptr, true, 0);
        return true;
    }

    std::unique_ptr<eq_tree::split_iterator_i> word_eq_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more) {
        has_more = false;
        if (cost != 0)
            return nullptr;
        auto& f = n.facet_as<eq_facet>(m_id);
        seq_util& u = f.get_seq_util();
        ast_manager& m = f.get_manager();

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

            if (!lc && !rc) {
                // two distinct variables lh, rh
                expr* v1 = lh;
                expr* v2 = rh;
                sort* s = v1->get_sort();
                expr* v1p = f.mk_fresh_var(s);

                auto it = std::make_unique<iterator>(n, m_id);
                {
                    token_list empty(m);
                    it->push_back("v2:=eps", v2, empty);
                }
                {
                    token_list repl(m);
                    repl.push_back(v2);
                    repl.push_back(v1p);
                    it->push_back("v1:=v2.v1'", v1, repl);
                }

                // Materialize the first branch ("v1:=eps") now.
                f.push_scope();
                token_list empty(m);
                f.apply_subst(v1, empty);
                broadcast_subst(n, m_id, v1, empty);
                out = eq_tree::edge("v1:=eps", nullptr, true, 0);
                return it;
            }

            // one side is a variable, the other a constant
            expr* var = lc ? rh : lh;
            expr* c = lc ? lh : rh;
            sort* s = var->get_sort();
            expr* var2 = f.mk_fresh_var(s);

            auto it = std::make_unique<iterator>(n, m_id);
            {
                token_list repl(m);
                repl.push_back(c);
                repl.push_back(var2);
                it->push_back("v:=c.v'", var, repl);
            }

            // Materialize the first branch ("v:=eps") now.
            f.push_scope();
            token_list empty(m);
            f.apply_subst(var, empty);
            broadcast_subst(n, m_id, var, empty);
            out = eq_tree::edge("v:=eps", nullptr, true, 0);
            return it;
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

    void deq_facet::apply_subst(expr* var, token_list const& repl) {
        for (unsigned i = 0; i < m_diseqs.size(); ++i) {
            subst_in_trailed(m_trail, m_diseqs, i, &disequation::m_lhs, var, repl);
            subst_in_trailed(m_trail, m_diseqs, i, &disequation::m_rhs, var, repl);
        }
    }

    stx::facet_i* deq_facet::clone(trail_stack& trail) const {
        deq_facet* f = alloc(deq_facet, trail, m, u);
        for (auto const& dq : m_diseqs)
            f->m_diseqs.push_back(dq);
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

    bool deq_facet::simplify(bool& conflict) {
        conflict = false;
        bool changed = false;
        for (unsigned i = 0; i < m_diseqs.size(); ) {
            disequation& dq = m_diseqs[i];
            token_list& L = dq.m_lhs;
            token_list& R = dq.m_rhs;

            // strip a common leading prefix, exactly as eq_facet::simplify.
            unsigned li = 0, ri = 0;
            while (li < L.size() && ri < R.size() && L.get(li) == R.get(ri)) {
                ++li; ++ri;
            }
            if (li > 0 || ri > 0) {
                token_list newL(m), newR(m);
                for (unsigned k = li; k < L.size(); ++k) newL.push_back(L.get(k));
                for (unsigned k = ri; k < R.size(); ++k) newR.push_back(R.get(k));
                m_trail.push(vector_field_trail<disequation, token_list>(m_diseqs, i, &disequation::m_lhs));
                m_trail.push(vector_field_trail<disequation, token_list>(m_diseqs, i, &disequation::m_rhs));
                L = std::move(newL);
                R = std::move(newR);
                changed = true;
            }

            if (L.empty() && R.empty()) {
                // both sides forced identical: the disequation cannot hold.
                conflict = true;
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
        f.simplify(conflict);
        if (conflict) {
            n.set_conflict(stx::br_plugin_base, nullptr);
            return stx::simplify_result::conflict;
        }
        if (f.is_satisfied())
            return stx::simplify_result::satisfied;
        return stx::simplify_result::proceed;
    }

} // namespace seq
