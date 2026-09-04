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
#include "ast/ast_pp.h"
#include <algorithm>
#include <cstdlib>
#include <utility>

namespace seq {

    // NSB code review: remove redundant function
    bool is_const_token(seq_util& u, expr* e) {
        expr* ch = nullptr;
        return u.str.is_unit(e, ch) && u.is_const_char(ch);
    }

    static int cmp_tokens(expr_ref_vector const& a, expr_ref_vector const& b) {
        if (a.size() != b.size())
            return a.size() < b.size() ? -1 : 1;
        for (unsigned i = 0; i < a.size(); ++i) {
            unsigned ida = a[i]->get_id(), idb = b[i]->get_id();
            if (ida != idb)
                return ida < idb ? -1 : 1;
        }
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

    std::ostream& eq_facet::display(std::ostream& out) const {
        out << "eq_facet: " << m_eqs.size() << " equation(s)\n";
        for (auto const& eq : m_eqs) {
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

        // NSB code review: use broadcast_subst instead of apply_subst, so
        // this forced v:=epsilon substitution reaches sibling facets too.
        if (eq.m_lhs.empty() != eq.m_rhs.empty()) {
            expr_ref_vector& side = eq.m_lhs.empty() ? eq.m_rhs : eq.m_lhs;
            eq_tree::dep_tracker eq_dep = eq.m_dep;
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
            u.str.get_concat_units(p.first, lts);
            u.str.get_concat_units(p.second, rts);
            add_equation_trailed(lts, rts, parent_dep);
        }
        return true;
    }

    bool eq_facet::simplify(eq_tree::node& n, ambient_context_i<eq_tree::dep_tracker>& ac, bool& conflict, eq_tree::dep_tracker& conflict_dep) {
        conflict = false;
        conflict_dep = nullptr;
        bool changed = false;
        for (unsigned i = 0; i < m_eqs.size(); ) {
            unsigned sz_before = m_eqs.size();
            if (!simplify_equation(n, ac, i, conflict, conflict_dep, changed)) {
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
        if (f.is_satisfied())
            return stx::simplify_result::satisfied;
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

    // Centralized substitution dispatcher: broadcast the substitution to
    // every subst_sink_i facet in the node (including eq_facet itself,
    // which is one such sink), so all token-based facets stay
    // synchronized.
    void broadcast_subst(eq_tree::node& target, expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        for (unsigned id = 0; id < target.num_facets(); ++id) {
            if (!target.has_facet(id))
                continue;
            if (auto* sink = dynamic_cast<subst_sink_i*>(&target.facet(id)))
                sink->apply_subst(var, repl, subst_dep);
        }
    }

    bool word_eq_split::iterator::next(eq_tree::edge& out) {
        if (m_pos >= m_pending.size())
            return false;
        auto& a = m_pending[m_pos++];
        broadcast_subst(m_n, a.m_var, a.m_repl, a.m_dep);
        out = eq_tree::edge(a.m_name, a.m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> word_eq_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0)
            return nullptr;
        auto ac = get_ambient(n);
        auto& f = ac.eq_facet_ref();

        for (auto const& eq : f.equations()) {
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue; // fully resolved by propagation; shouldn't occur
            // Mirror c3's apply_const_nielsen/apply_var_nielsen: try both
            // directions (fwd=true: leading/prefix tokens, matching
            // reduce_front; fwd=false: trailing/suffix tokens, matching
            // reduce_back) - a two-sided equation can be stuck only at
            // its tail even though its head has already been resolved by
            // propagation (e.g. a substitution narrowed a suffix without
            // touching the still-agreeing prefix).
            for (int dir = 0; dir < 2; ++dir) {
                bool fwd = dir == 0;
                expr* lh = fwd ? eq.m_lhs[0] : eq.m_lhs.back();
                expr* rh = fwd ? eq.m_rhs[0] : eq.m_rhs.back();
                bool lu = u.str.is_unit(lh);
                bool ru = u.str.is_unit(rh);
                bool lp = u.str.is_power(lh) || m.is_ite(lh);
                bool rp = u.str.is_power(rh) || m.is_ite(rh);
                if (lh == rh)
                    continue;
                if (lp || rp)
                    // Power tokens (and, per the token model's is_var
                    // exclusion - README.md section 5.1.1 / this file's
                    // ite_split - `ite` tokens) are neither units nor
                    // Nielsen-substitutable variables - they are owned
                    // exclusively by power_facet's own dedicated rule
                    // family (power_propagation/power_split/
                    // power_fine_wilf/power_num_cmp/power_split_elim; see
                    // facet-eq-deq.md section 2.3) or, for `ite`, by
                    // ite_split's own condition-branching rule below.
                    // Substituting a power token wholesale here (as
                    // v:=epsilon or v:=c.v') would be unsound/redundant with
                    // that machinery, so word_eq_split simply skips any
                    // equation whose head/tail is a power on either side.
                    continue;
                // A token is a Nielsen-substitutable variable precisely when
                // it is neither a unit nor a power (per z3papers/nseq's
                // README.md section 5.1.1 token model - no separate is_var
                // predicate). Computed locally rather than via
                // ambient_context_i::is_var/theory_seq::is_var, which do not
                // exclude power tokens and are kept as-is only for legacy
                // model-construction compatibility (theory_seq::mk_value/
                // init_model).
                bool lv = !lu && !lp;
                bool rv = !ru && !rp;
                // NSB code review: there is a conflict if characters are
                // distinct; if not equal and not distinct, force them to
                // coincide via a term substitution replacing whichever of
                // lh/rh is not already a concrete char value (if both are
                // values yet not equal, m.are_distinct necessarily holds
                // for them, so that case is covered by the conflict arm
                // above and cannot fall through to here).
                //
                // In practice, when lch/rch are both syntactically
                // determined constant chars, `reduce_eq` (run by
                // `eq_propagation` immediately before any split is
                // attempted) already performs this same unit-vs-unit
                // decomposition/symbol-clash check deterministically, so
                // the `are_distinct`/`lch == rch` arms below are a
                // defensive fallback that should not normally trigger;
                // the case this rule exists to resolve is two *symbolic*
                // (non-value) character terms - e.g. from an `ite`/`nth`
                // application - that reduce_eq cannot statically compare,
                // for which forcing the unit tokens to coincide (via the
                // same broadcast_subst token-substitution machinery used
                // by every other Nielsen rule in this file) both resolves
                // the equation's stuck head/tail and is, by itself,
                // sufficient to guarantee lch/rch agree in any model
                // (they become literally the same term everywhere) - no
                // separate arithmetic equality constraint is needed for
                // soundness (word_eq_split has no arith_facet_i handle in
                // any case; see class comment).
                if (lu && ru) {
                    expr* lch = nullptr, *rch = nullptr;
                    VERIFY(u.str.is_unit(lh, lch));
                    VERIFY(u.str.is_unit(rh, rch));
                    if (m.are_distinct(lch, rch))
                        continue;
                    if (lch == rch)
                        continue;
                    has_more = true;
                    eq_tree::dep_tracker eq_dep = eq.m_dep;
                    // Eliminate whichever side is not already a concrete
                    // char value; if neither (or both) is a value,
                    // arbitrarily eliminate the trailing/second side (rh).
                    bool elim_lh = !u.is_const_char(lch) && u.is_const_char(rch);
                    expr* var_tok = elim_lh ? lh : rh;
                    expr* val_tok = elim_lh ? rh : lh;
                    expr_ref_vector repl(m);
                    repl.push_back(val_tok);
                    broadcast_subst(n, var_tok, repl, eq_dep);
                    out = eq_tree::edge("char-eq", eq_dep, true, 0);
                    committed = true;
                    m_stats.m_num_splits++;
                    return nullptr;
                }

                // Every alternative below is a case-split on how to unstick
                // this one equation, so all of them (and the immediately
                // materialized first branch) are justified by this
                // equation's own dependency, not a join of several.
                eq_tree::dep_tracker eq_dep = eq.m_dep;

                if ((lv || !lu) && (rv || !ru)) {
                    // Two distinct variables lh, rh: the classic 4-branch
                    // Nielsen transformation for word equations (design doc
                    // facet-eq-deq.md section 2.2 / c3 branch's
                    // apply_var_nielsen). Since v1, v2 are symbols at the
                    // matching end of each side, exactly one of these must
                    // hold in any solution (mirrored - v'.c instead of c.v' -
                    // when fwd is false, i.e. the variables are at the tail):
                    //   (1) v1 := epsilon
                    //   (2) v2 := epsilon
                    //   (3) v1 := v2 . v1'  / v1' . v2   (v1 at least as long as v2)
                    //   (4) v2 := v1 . v2'  / v2' . v1   (v2 at least as long as v1)
                    // Branches (3)/(4) are the "non-progress" cases (they
                    // introduce a fresh variable rather than shrinking the
                    // equation), but are still required for completeness:
                    // without them, any solution where both v1 and v2 are
                    // non-empty and neither is a literal prefix/suffix of the
                    // other one being consumed first is unreachable.
                    expr* v1 = lh;
                    expr* v2 = rh;
                    sort* s = v1->get_sort();
                    expr* v1p = f.mk_fresh_var(s);
                    expr* v2p = f.mk_fresh_var(s);

                    iterator* it = alloc(iterator, n, m, u);
                    {
                        expr_ref_vector empty(m);
                        it->push_back("v2:=eps", v2, empty, eq_dep);
                    }
                    {
                        expr_ref_vector repl(m);
                        if (fwd) { repl.push_back(v2); repl.push_back(v1p); }
                        else     { repl.push_back(v1p); repl.push_back(v2); }
                        it->push_back(fwd ? "v1:=v2.v1'" : "v1:=v1'.v2", v1, repl, eq_dep);
                    }
                    {
                        expr_ref_vector repl(m);
                        if (fwd) { repl.push_back(v1); repl.push_back(v2p); }
                        else     { repl.push_back(v2p); repl.push_back(v1); }
                        it->push_back(fwd ? "v2:=v1.v2'" : "v2:=v2'.v1", v2, repl, eq_dep);
                    }

                    // Materialize the first branch ("v1:=eps") now, in the
                    // scope the driver already pushed for this call.
                    expr_ref_vector empty(m);
                    broadcast_subst(n, v1, empty, eq_dep);
                    out = eq_tree::edge("v1:=eps", eq_dep, true, 0);
                    committed = true;
                    m_stats.m_num_splits++;
                    return it;
                }

                // one side is a variable, the other a unit token
                expr* var = lv || !lu ? lh : rh;
                expr* c = lv || !lu ? rh : lh;
                sort* s = var->get_sort();
                expr* var2 = f.mk_fresh_var(s);

                iterator* it = alloc(iterator, n, m, u);
                {
                    expr_ref_vector repl(m);
                    if (fwd) { repl.push_back(c); repl.push_back(var2); }
                    else     { repl.push_back(var2); repl.push_back(c); }
                    it->push_back(fwd ? "v:=c.v'" : "v:=v'.c", var, repl, eq_dep);
                }

                // Materialize the first branch ("v:=eps") now, in the scope
                // the driver already pushed for this call.
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
            // A length-1 string constant is const-length 1 (get_concat_units's
            // token model never produces longer constant tokens); every
            // other token (opaque variable, fresh Skolem, etc.) is
            // variable-length.
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
        if (cost != 0)
            return nullptr;
        auto ac = get_ambient(n);
        auto& f = ac.eq_facet_ref();
        auto& af = ac.arith_facet_ref();

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
            m_stats.m_num_splits++;
            return nullptr; // single deterministic progress branch, no resumable iterator
        }
        return nullptr;
    }

    // -- ite_split --

    bool ite_split::iterator::next(eq_tree::edge& out) {
        if (m_done)
            return false;
        m_done = true;
        auto ac = get_ambient(m_n);
        auto& af = ac.arith_facet_ref();
        expr_ref not_cond(m.mk_not(m_cond), m);
        af.add_constraint(not_cond, m_dep);
        broadcast_subst(m_n, m_tok, m_repl2, m_dep);
        out = eq_tree::edge("ite-split-else", m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> ite_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0)
            return nullptr;
        auto ac = get_ambient(n);
        auto& f = ac.eq_facet_ref();
        auto& af = ac.arith_facet_ref();

        for (auto const& eq : f.equations()) {
            expr* tok = nullptr;
            eq_tree::dep_tracker eq_dep = nullptr;
            for (expr* t : eq.m_lhs)
                if (m.is_ite(t)) { tok = t; eq_dep = eq.m_dep; break; }
            if (!tok)
                for (expr* t : eq.m_rhs)
                    if (m.is_ite(t)) { tok = t; eq_dep = eq.m_dep; break; }
            if (!tok)
                continue;

            expr* cond = nullptr, *then_e = nullptr, *else_e = nullptr;
            VERIFY(m.is_ite(tok, cond, then_e, else_e));

            expr_ref_vector repl1(m), repl2(m);
            u.str.get_concat_units(then_e, repl1);
            u.str.get_concat_units(else_e, repl2);

            has_more = true;

            // Branch 1 ("then"): assert `cond` as a hypothesis dependency
            // on arith_facet's incremental backend and substitute the
            // ite token by then_e's token list; mirrors apply_power_epsilon's
            // dependency-tracked disjunction branch (facet-eq-deq.md
            // section 2.3).
            af.add_constraint(cond, eq_dep);
            broadcast_subst(n, tok, repl1, eq_dep);
            out = eq_tree::edge("ite-split-then", eq_dep, true, 0);
            committed = true;
            m_stats.m_num_splits++;

            // Branch 2 ("else"): resumed lazily via the returned iterator,
            // asserting `!cond` and substituting by else_e's token list.
            return alloc(iterator, n, m, u, tok, cond, repl2, eq_dep);
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

    std::ostream& deq_facet::display(std::ostream& out) const {
        out << "deq_facet: " << m_diseqs.size() << " disequation(s)\n";
        for (auto const& dq : m_diseqs) {
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
                if (u.str.is_unit(lh) && u.str.is_unit(rh) && m.are_distinct(lh, rh)) {
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
        if (f.is_satisfied())
            return stx::simplify_result::satisfied;
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

    // -- deq_split --

    // len(toks[0]) + .. + len(toks[n-1]) as a single arithmetic
    // expression, mirroring power_facet.cpp's mk_len_sum (a per-token
    // const-1-or-str.len sum); duplicated locally rather than shared
    // since eq_facet/power_facet intentionally have no header dependency
    // on each other's static helpers.
    static expr_ref mk_side_len(seq_util& u, arith_util& a, ast_manager& m, expr_ref_vector const& toks) {
        expr_ref sum(a.mk_int(0), m);
        for (expr* tok : toks)
            sum = expr_ref(a.mk_add(sum, u.str.is_unit(tok) ? (expr*)a.mk_int(1) : (expr*)u.str.mk_length(tok)), m);
        return sum;
    }

    // Locate the first "stuck" disequation - both sides nonempty (an
    // empty side would already have been resolved/discharged by
    // deq_facet::simplify) - to case-split on. Unlike eq_facet's splits,
    // this rule does not need to inspect the disequation's leading
    // tokens at all: the 3-way branch (length-order x2, equal-length
    // split) applies uniformly regardless of what the heads look like.
    // Since every sibling branch resumes from the very same backtracked
    // node state that split() itself ran in (the driver pops each
    // branch's scope before trying the next, mirroring word_eq_split's
    // iterator), `idx` stays a valid index into f.disequations() for
    // every branch - no content-based re-lookup is needed.
    scoped_ptr<eq_tree::split_iterator_i> deq_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0)
            return nullptr;
        auto ac = get_ambient(n);
        auto& f = ac.deq_facet_ref();

        for (unsigned idx = 0; idx < f.disequations().size(); ++idx) {
            deq_facet::disequation const& dq = f.disequations()[idx];
            if (dq.m_lhs.empty() || dq.m_rhs.empty())
                continue; // resolved by propagation; shouldn't occur
            has_more = true;

            eq_tree::dep_tracker dq_dep = dq.m_dep;
            expr_ref_vector lhs(dq.m_lhs), rhs(dq.m_rhs);
            auto& af = ac.arith_facet_ref();
            expr_ref len_lhs = mk_side_len(u, af.get_arith_util(), m, lhs);
            expr_ref len_rhs = mk_side_len(u, af.get_arith_util(), m, rhs);

            iterator* it = alloc(iterator, n, idx, lhs, rhs, dq_dep, 2, m, u);

            // Materialize branch 1 ("len(u) < len(v)") now, in the scope
            // the driver already pushed for this call: a length mismatch
            // alone already proves the disequation, so it is simply
            // discharged (removed) here - the arith side constraint is
            // what actually justifies the discharge.
            f.remove_disequation_trailed(idx);
            af.add_constraint(af.get_arith_util().mk_lt(len_lhs, len_rhs), dq_dep);
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
        auto& af = ac.arith_facet_ref();
        expr_ref len_lhs = mk_side_len(u, af.get_arith_util(), m, m_lhs);
        expr_ref len_rhs = mk_side_len(u, af.get_arith_util(), m, m_rhs);
        auto& f = ac.deq_facet_ref();

        if (this_case == 2) {
            // Branch 2: len(v) < len(u), symmetric to branch 1.
            f.remove_disequation_trailed(m_diseq_idx);
            af.add_constraint(af.get_arith_util().mk_lt(len_rhs, len_lhs), m_dep);
            out = eq_tree::edge("diseq len>", m_dep, true, 0);
            return true;
        }

        // Branch 3: equal-length split. Fresh skolem terms w (common
        // prefix), a, b (fresh single-char unit terms), u', v' (fresh
        // suffix vars); new equations u = w.a.u', v = w.b.v'; arith
        // constraint len(u')=len(v'); replace the original disequation
        // with the finer a != b - which, together with the two new
        // equalities just asserted, is what actually proves u != v.
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
        ef.add_equation_trailed(m_lhs, u_rhs, m_dep);
        ef.add_equation_trailed(m_rhs, v_rhs, m_dep);

        expr_ref len_up(u.str.mk_length(up), m);
        expr_ref len_vp(u.str.mk_length(vp), m);
        af.add_constraint(m.mk_eq(len_up, len_vp), m_dep);

        f.remove_disequation_trailed(m_diseq_idx);
        expr_ref_vector a_vec(m); a_vec.push_back(a_unit);
        expr_ref_vector b_vec(m); b_vec.push_back(b_unit);
        f.add_disequation_trailed(a_vec, b_vec, m_dep);

        out = eq_tree::edge("diseq split", m_dep, true, 0);
        return true;
    }

} // namespace seq
