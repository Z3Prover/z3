/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_power_facet.cpp

Abstract:

    See seq_power_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/seq/seq_power_facet.h"
#include "ast/seq/seq_arith_facet_i.h"

namespace seq {

    void power_facet::remove(unsigned idx) {
        m_trail.push(vector_erase_trail<str_power>(m_pows, idx));
        m_pows.erase(m_pows.begin() + idx);
    }

    void power_facet::set_axiomatized(unsigned idx) {
        SASSERT(idx < m_pows.size());
        if (m_pows[idx].m_axiomatized)
            return;
        m_trail.push(vector_field_trail<str_power, bool>(m_pows, idx, &str_power::m_axiomatized));
        m_pows[idx].m_axiomatized = true;
    }

    void power_facet::set_fw_marked(unsigned idx) {
        SASSERT(idx < m_pows.size());
        if (m_pows[idx].m_fw_marked)
            return;
        m_trail.push(vector_field_trail<str_power, bool>(m_pows, idx, &str_power::m_fw_marked));
        m_pows[idx].m_fw_marked = true;
    }

    stx::facet_i* power_facet::clone(trail_stack& trail) const {
        power_facet* f = alloc(power_facet, trail, m, u, a, m_dm);
        f->m_pows.append(m_pows);
        f->m_max_unfold = m_max_unfold;
        return f;
    }

    unsigned power_facet::hash() const {
        unsigned h = m_pows.size() * 916213631u;
        for (auto const& p : m_pows) {
            unsigned ph = 1;
            ph = combine_hash(ph, p.m_e.get()->get_id());
            ph = combine_hash(ph, p.m_s.get()->get_id());
            ph = combine_hash(ph, p.m_n.get()->get_id());
            h += ph;
        }
        return h ? h : 1;
    }

    bool power_facet::similar(facet_i const& other) const {
        auto const& o = static_cast<power_facet const&>(other);
        if (m_pows.size() != o.m_pows.size())
            return false;
        // Obligations are registered in a fixed, caller-determined order
        // (unlike eq_facet's equation set, which is permuted by
        // splitting) - order-sensitive comparison suffices here, mirrors
        // arith_facet's own similar().
        for (unsigned i = 0; i < m_pows.size(); ++i) {
            auto const& p = m_pows[i];
            auto const& q = o.m_pows[i];
            if (p.m_e.get() != q.m_e.get() || p.m_s.get() != q.m_s.get() || p.m_n.get() != q.m_n.get())
                return false;
        }
        return true;
    }

    // Build the concatenation of `j` copies of `s` (j >= 1), reusing
    // `flatten`/`u.str.mk_concat` conventions from eq_facet - but since
    // this is destined for eq_facet::add_equation (which itself flattens
    // its arguments), a plain right-nested str.++ chain suffices.
    static expr_ref mk_power_unfold(seq_util& u, ast_manager& m, expr* s, unsigned j) {
        SASSERT(j >= 1);
        expr_ref result(s, m);
        for (unsigned k = 1; k < j; ++k)
            result = expr_ref(u.str.mk_concat(s, result), m);
        return result;
    }

    stx::simplify_result power_propagation::propagate(eq_tree::node& n) {
        auto& f = n.facet_as<power_facet>(m_pow_id);
        auto& ef = n.facet_as<eq_facet>(m_eq_id);
        auto& af = n.facet_as<arith_facet_i>(m_arith_id);

        bool changed = false;
        for (unsigned i = 0; i < f.powers().size(); ) {
            str_power const& p = f.powers()[i];
            rational v;

            // Known exponent (facet-power's mirror of theory_seq's
            // power_unfold_axiom's "known exponent" branch / seq_rewriter's
            // own numeral-power folding): the obligation is fully precise,
            // so unfold it exactly into an eq_facet equation and discharge
            // it here - no need for arith_facet or power_split at all.
            if (a.is_numeral(p.m_n, v)) {
                expr_ref rhs(m);
                if (!v.is_pos())
                    rhs = u.str.mk_empty(p.m_e.get()->get_sort());
                else
                    rhs = mk_power_unfold(u, m, p.m_s.get(), v.get_unsigned());
                expr_ref_vector repl(m);
                flatten(u, rhs.get(), repl);
                broadcast_subst(n, m_eq_id, p.m_e.get(), repl, p.m_dep);
                f.remove(i);
                changed = true;
                continue;
            }

            // Symbolic exponent: assert the length-only consequences of
            // axioms::power_axiom into arith_facet (see module comment) -
            // sound under-approximation, asserted at most once.
            if (!p.m_axiomatized) {
                expr_ref len_e(u.str.mk_length(p.m_e.get()), m);
                expr_ref len_s(u.str.mk_length(p.m_s.get()), m);
                expr_ref emp(u.str.mk_empty(p.m_e.get()->get_sort()), m);
                expr_ref n_ge_1(a.mk_ge(p.m_n.get(), a.mk_int(1)), m);
                expr_ref e_is_emp(m.mk_eq(len_e, a.mk_int(0)), m);
                expr_ref s_is_emp(m.mk_eq(len_s, a.mk_int(0)), m);

                // n <= 0 => len(e) = 0 (stands in for e = epsilon)
                af.add_constraint(m.mk_or(n_ge_1, e_is_emp), p.m_dep);
                // s = epsilon => len(e) = 0
                af.add_constraint(m.mk_or(m.mk_not(s_is_emp), e_is_emp), p.m_dep);
                // n >= 1 => len(e) = n * len(s)
                af.add_constraint(m.mk_or(m.mk_not(n_ge_1), m.mk_eq(len_e, a.mk_mul(p.m_n.get(), len_s))), p.m_dep);
                // n >= 1 & s != epsilon => n <= len(e)
                af.add_constraint(m.mk_or(m.mk_not(n_ge_1), s_is_emp, a.mk_le(p.m_n.get(), len_e)), p.m_dep);
                f.set_axiomatized(i);
                changed = true;
            }
            ++i;
        }
        if (af.has_conflict()) {
            n.set_conflict(stx::br_plugin_base, af.conflict_dep());
            return stx::simplify_result::conflict;
        }
        if (f.is_satisfied())
            return stx::simplify_result::satisfied;
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

    // -- power_fine_wilf --

    // Is `e` a registered power obligation with base `s`, exponent `n`?
    // Thin wrapper around power_facet::find_power for readability at call
    // sites below.
    static bool is_power_token(power_facet const& f, expr* e, unsigned& idx) {
        return f.find_power(e, idx);
    }

    // Scan `side` for the first token that is a registered power
    // obligation (with power_facet index != `exclude_idx`, so `U^n`
    // itself - if it also appears literally inside `side`, which cannot
    // happen here since `side` is the *other* equation side - is never
    // mistaken for `W^m`; the exclude parameter is defensive rather than
    // load-bearing). All tokens strictly before it become `Y`. Returns
    // false if no power token is found in `side` at all, or if the one
    // found has the same base as `u_base` (same-base overlaps are left
    // to ordinary propagation/word_eq_split).
    static bool find_wpow(power_facet const& f, expr_ref_vector const& side, expr* u_base,
                           unsigned& y_len, unsigned& wpow_idx) {
        for (unsigned i = 0; i < side.size(); ++i) {
            unsigned idx;
            if (is_power_token(f, side[i], idx)) {
                if (f.powers()[idx].m_s.get() == u_base)
                    return false; // same base: not this rule's business
                y_len = i;
                wpow_idx = idx;
                return true;
            }
        }
        return false;
    }

    // Locate one Fine & Wilf trigger site among f's obligations / ef's
    // equations, if any. See class comment for the pattern.
    static bool find_fw_trigger(power_facet const& f, eq_facet const& ef, power_fine_wilf::trigger& t) {
        for (unsigned eq_idx = 0; eq_idx < ef.equations().size(); ++eq_idx) {
            eq_facet::equation const& eq = ef.equations()[eq_idx];
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue;
            for (bool pow_on_lhs : {true, false}) {
                expr_ref_vector const& head_side = pow_on_lhs ? eq.m_lhs : eq.m_rhs;
                expr_ref_vector const& other_side = pow_on_lhs ? eq.m_rhs : eq.m_lhs;
                unsigned pow_idx;
                if (!is_power_token(f, head_side[0], pow_idx))
                    continue;
                str_power const& p = f.powers()[pow_idx];
                if (p.m_fw_marked)
                    continue; // case 1 already offered; cases 2/3 are per-branch anyway, but a stable trigger requires *some* undischarged obligation
                unsigned y_len, wpow_idx;
                if (!find_wpow(f, other_side, p.m_s.get(), y_len, wpow_idx))
                    continue;
                t.m_eq_idx = eq_idx;
                t.m_pow_on_lhs = pow_on_lhs;
                t.m_pow_idx = pow_idx;
                t.m_other_pow_idx = wpow_idx;
                t.m_y_len = y_len;
                t.m_dep = eq.m_dep;
                return true;
            }
        }
        return false;
    }

    // len(U^n) = n*len(U) as an expr (both U^n's own str.len and, since
    // power_propagation asserts `len(e)=n*len(s)` into arith_facet only
    // as a *constraint* (not a rewrite), the token's own str.len(e) is
    // the right handle to use here - arith_facet will relate it to
    // n*len(base) on its own via that already-asserted axiom).
    static expr_ref mk_len(seq_util& u, ast_manager& m, expr* e) {
        return expr_ref(u.str.mk_length(e), m);
    }

    static expr_ref mk_len_sum(seq_util& u, arith_util& a, ast_manager& m, expr_ref_vector const& toks, unsigned from, unsigned to) {
        expr_ref sum(a.mk_int(0), m);
        for (unsigned i = from; i < to; ++i)
            sum = expr_ref(a.mk_add(sum, is_const_token(u, toks[i]) ? (expr*)a.mk_int(1) : (expr*)u.str.mk_length(toks[i])), m);
        return sum;
    }

    // Sanity check that the trigger's obligation indices still refer to
    // live power obligations (defensive; see call site comment).
    static bool t_stale(power_facet const& f, power_fine_wilf::trigger const& t) {
        return t.m_pow_idx >= f.powers().size() || t.m_other_pow_idx >= f.powers().size();
    }

    bool power_fine_wilf::iterator::next(eq_tree::edge& out) {
        if (m_next_case > 3)
            return false;
        unsigned this_case = m_next_case++;

        auto& f = m_n.facet_as<power_facet>(m_pow_id);
        auto& ef = m_n.facet_as<eq_facet>(m_eq_id);
        auto& af = m_n.facet_as<arith_facet_i>(m_arith_id);

        // The trigger equation may already have been consumed/replaced
        // by an earlier branch of *this* same alternative set (it hasn't
        // - each branch starts from the pre-pushed fresh scope that
        // reflects the trigger equation still being present - but guard
        // defensively since power obligations can, in principle, also be
        // discharged by an unrelated concurrently-registered plugin
        // before this iterator resumes).
        if (t_stale(f, m_t) || m_t.m_eq_idx >= ef.equations().size())
            return false;

        eq_facet::equation const& eq = ef.equations()[m_t.m_eq_idx];
        expr_ref_vector const& head_side = m_t.m_pow_on_lhs ? eq.m_lhs : eq.m_rhs;
        expr_ref_vector const& other_side = m_t.m_pow_on_lhs ? eq.m_rhs : eq.m_lhs;
        str_power const& p_u = f.powers()[m_t.m_pow_idx];
        str_power const& p_w = f.powers()[m_t.m_other_pow_idx];
        eq_tree::dep_tracker dep = m_t.m_dep;

        expr_ref len_upow = mk_len(u, m, p_u.m_e.get());
        expr_ref len_wpow = mk_len(u, m, p_w.m_e.get());
        expr_ref len_y = mk_len_sum(u, a, m, other_side, 0, m_t.m_y_len);
        expr_ref T(a.mk_add(mk_len(u, m, p_u.m_s.get()).get(), mk_len(u, m, p_w.m_s.get()).get()), m);

        // V, Z: the remainder of each side after U^n / (Y . W^m).
        expr_ref_vector V(m); // remainder of head_side after U^n (index 0)
        V.append(head_side.size() - 1, head_side.data() + 1);
        expr_ref_vector Z(m); // remainder of other_side after Y . W^m
        Z.append(other_side.size() - (m_t.m_y_len + 1), other_side.data() + m_t.m_y_len + 1);
        expr_ref_vector Y(m);
        Y.append(m_t.m_y_len, other_side.data());

        if (this_case == 2) {
            // Case 2: U^n = Y . R1, W^m = R1 . R2, V = R2 . Z.
            expr* r1 = ef.mk_fresh_var(p_u.m_e.get()->get_sort());
            expr* r2 = ef.mk_fresh_var(p_u.m_e.get()->get_sort());
            expr_ref_vector un_lhs(m); un_lhs.push_back(p_u.m_e.get());
            expr_ref_vector un_rhs(m); un_rhs.append(Y); un_rhs.push_back(r1);
            expr_ref_vector wm_lhs(m); wm_lhs.push_back(p_w.m_e.get());
            expr_ref_vector wm_rhs(m); wm_rhs.push_back(r1); wm_rhs.push_back(r2);
            expr_ref_vector v_lhs(m); v_lhs.append(V);
            expr_ref_vector v_rhs(m); v_rhs.push_back(r2); v_rhs.append(Z);

            ef.remove_equation_trailed(m_t.m_eq_idx);
            ef.add_equation_trailed(un_lhs, un_rhs, dep);
            ef.add_equation_trailed(wm_lhs, wm_rhs, dep);
            ef.add_equation_trailed(v_lhs, v_rhs, dep);

            expr_ref len_r1(u.str.mk_length(r1), m);
            expr_ref len_r2(u.str.mk_length(r2), m);
            af.add_constraint(m.mk_eq(a.mk_add(len_y, len_r1), len_upow), dep);
            af.add_constraint(a.mk_ge(len_r1, T), dep);
            af.add_constraint(m.mk_eq(a.mk_add(len_r1, len_r2), len_wpow), dep);
            af.add_constraint(a.mk_ge(len_r2, a.mk_int(0)), dep);

            out = eq_tree::edge("fine-wilf:case2", dep, true, 0);
            return true;
        }
        else {
            // Case 3: U^n = S1 . S2, S1 = Y . W^m, Z = S2 . V.
            expr* s1 = ef.mk_fresh_var(p_u.m_e.get()->get_sort());
            expr* s2 = ef.mk_fresh_var(p_u.m_e.get()->get_sort());
            expr_ref_vector un_lhs(m); un_lhs.push_back(p_u.m_e.get());
            expr_ref_vector un_rhs(m); un_rhs.push_back(s1); un_rhs.push_back(s2);
            expr_ref_vector s1_lhs(m); s1_lhs.push_back(s1);
            expr_ref_vector s1_rhs(m); s1_rhs.append(Y); s1_rhs.push_back(p_w.m_e.get());
            expr_ref_vector z_lhs(m); z_lhs.append(Z);
            expr_ref_vector z_rhs(m); z_rhs.push_back(s2); z_rhs.append(V);

            ef.remove_equation_trailed(m_t.m_eq_idx);
            ef.add_equation_trailed(un_lhs, un_rhs, dep);
            ef.add_equation_trailed(s1_lhs, s1_rhs, dep);
            ef.add_equation_trailed(z_lhs, z_rhs, dep);

            expr_ref len_s1(u.str.mk_length(s1), m);
            expr_ref len_s2(u.str.mk_length(s2), m);
            af.add_constraint(m.mk_eq(len_s1, a.mk_add(len_y, len_wpow)), dep);
            af.add_constraint(a.mk_ge(len_wpow, T), dep);
            af.add_constraint(a.mk_ge(len_s2, a.mk_int(1)), dep);
            af.add_constraint(m.mk_eq(a.mk_add(len_s1, len_s2), len_upow), dep);

            out = eq_tree::edge("fine-wilf:case3", dep, true, 0);
            return true;
        }
    }

    scoped_ptr<eq_tree::split_iterator_i> power_fine_wilf::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0)
            return nullptr;
        auto& f = n.facet_as<power_facet>(m_pow_id);
        auto& ef = n.facet_as<eq_facet>(m_eq_id);
        auto& af = n.facet_as<arith_facet_i>(m_arith_id);

        trigger t;
        if (!find_fw_trigger(f, ef, t))
            return nullptr;
        has_more = true;

        eq_facet::equation const& eq = ef.equations()[t.m_eq_idx];
        expr_ref_vector const& other_side = t.m_pow_on_lhs ? eq.m_rhs : eq.m_lhs;
        str_power const& p_u = f.powers()[t.m_pow_idx];
        str_power const& p_w = f.powers()[t.m_other_pow_idx];
        eq_tree::dep_tracker dep = t.m_dep;

        expr_ref len_upow = mk_len(u, m, p_u.m_e.get());
        expr_ref len_wpow = mk_len(u, m, p_w.m_e.get());
        expr_ref len_y = mk_len_sum(u, a, m, other_side, 0, t.m_y_len);
        expr_ref T(a.mk_add(mk_len(u, m, p_u.m_s.get()).get(), mk_len(u, m, p_w.m_s.get()).get()), m);

        // Case 1 (first, immediately materialized branch): small
        // overlap, arith-only, no string-side progress. Marked so it is
        // never re-offered for this same obligation.
        expr_ref case1(m.mk_or(a.mk_lt(a.mk_sub(len_upow, len_y), T), a.mk_lt(len_wpow, T)), m);
        af.add_constraint(case1, dep);
        f.set_fw_marked(t.m_pow_idx);

        iterator* it = alloc(iterator, n, m_pow_id, m_eq_id, m_arith_id, t, 2u, m, u, a);
        out = eq_tree::edge("fine-wilf:case1", dep, true, 0);
        committed = true;
        return it;
    }


    bool power_split::iterator::next(eq_tree::edge& out) {
        auto& f = m_n.facet_as<power_facet>(m_pow_id);
        if (m_pow_index >= f.powers().size())
            return false; // obligation already discharged by another route
        str_power const& p = f.powers()[m_pow_index];

        if (m_next_j > m_bound)
            return false;

        auto& ef = m_n.facet_as<eq_facet>(m_eq_id);
        auto& af = m_n.facet_as<arith_facet_i>(m_arith_id);
        unsigned j = m_next_j++;
        expr_ref rhs = mk_power_unfold(u, m, p.m_s.get(), j);
        expr_ref_vector repl(m);
        flatten(u, rhs.get(), repl);
        broadcast_subst(m_n, m_eq_id, p.m_e.get(), repl, m_dep);
        af.add_constraint(m.mk_eq(p.m_n.get(), a.mk_int(j)), m_dep);
        f.remove(m_pow_index);

        out = eq_tree::edge("power:n=j", m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0)
            return nullptr;
        auto& f = n.facet_as<power_facet>(m_pow_id);
        auto& ef = n.facet_as<eq_facet>(m_eq_id);
        auto& af = n.facet_as<arith_facet_i>(m_arith_id);

        for (unsigned i = 0; i < f.powers().size(); ++i) {
            str_power const& p = f.powers()[i];
            rational v;
            if (a.is_numeral(p.m_n, v))
                continue; // resolved by power_propagation

            eq_tree::dep_tracker dep = p.m_dep;
            unsigned bound = f.max_unfold();

            // First branch: n <= 0, e := epsilon (the "n <= 0" case of
            // power_axiom/power_unfold_axiom).
            expr_ref_vector empty(m);
            broadcast_subst(n, m_eq_id, p.m_e.get(), empty, dep);
            af.add_constraint(a.mk_le(p.m_n.get(), a.mk_int(0)), dep);
            f.remove(i);

            iterator* it = alloc(iterator, n, m_pow_id, m_eq_id, m_arith_id, i, bound, dep, m, u, a);
            out = eq_tree::edge("power:n<=0", dep, true, 0);
            committed = true;
            return it;
        }
        return nullptr;
    }

    // -- power_num_cmp --

    // Locate a same-base power-vs-power comparison trigger: some
    // eq_facet equation has, at the same directional end (front or
    // back, mirroring c3's fwd/reverse `dir_token` scan) of both sides,
    // a power token, both with the same registered base but distinct
    // obligations (distinct power terms - if they were the same term,
    // ordinary token-equality matching would already have consumed
    // them). See class comment for the two branches this produces.
    static bool find_num_cmp_trigger(power_facet const& f, eq_facet const& ef,
                                      unsigned& eq_idx, bool& at_front,
                                      unsigned& pow_idx_l, unsigned& pow_idx_r,
                                      eq_tree::dep_tracker& dep) {
        for (unsigned i = 0; i < ef.equations().size(); ++i) {
            eq_facet::equation const& eq = ef.equations()[i];
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue;
            for (bool front : {true, false}) {
                expr* lh = front ? eq.m_lhs[0] : eq.m_lhs.back();
                expr* rh = front ? eq.m_rhs[0] : eq.m_rhs.back();
                unsigned lidx, ridx;
                if (!is_power_token(f, lh, lidx) || !is_power_token(f, rh, ridx))
                    continue;
                if (lidx == ridx)
                    continue; // same obligation: nothing to compare
                if (f.powers()[lidx].m_s.get() != f.powers()[ridx].m_s.get())
                    continue; // different bases: power_fine_wilf's territory, not this rule's
                // Exponents already numerals are resolved directly by
                // power_propagation's known-exponent unfold rather than
                // this rule (a constant-vs-constant comparison needs no
                // case split).
                rational vl, vr;
                arith_util const& a2 = f.get_arith_util();
                if (a2.is_numeral(f.powers()[lidx].m_n, vl) && a2.is_numeral(f.powers()[ridx].m_n, vr))
                    continue;
                eq_idx = i;
                at_front = front;
                pow_idx_l = lidx;
                pow_idx_r = ridx;
                dep = eq.m_dep;
                return true;
            }
        }
        return false;
    }

    bool power_num_cmp::iterator::next(eq_tree::edge& out) {
        if (m_done)
            return false;
        m_done = true;
        auto& af = m_n.facet_as<arith_facet_i>(m_arith_id);
        // Branch 2 (the remaining alternative once branch 1 - "n < m",
        // materialized by split() itself - has been offered): m <= n.
        af.add_constraint(a.mk_ge(m_n_exp.get(), m_m_exp.get()), m_dep);
        out = eq_tree::edge("power-cmp:>=", m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_num_cmp::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0)
            return nullptr;
        auto& f = n.facet_as<power_facet>(m_pow_id);
        auto& ef = n.facet_as<eq_facet>(m_eq_id);
        auto& af = n.facet_as<arith_facet_i>(m_arith_id);

        unsigned eq_idx, pow_idx_l, pow_idx_r;
        bool at_front;
        eq_tree::dep_tracker dep;
        if (!find_num_cmp_trigger(f, ef, eq_idx, at_front, pow_idx_l, pow_idx_r, dep))
            return nullptr;
        has_more = true;

        expr* lexp = f.powers()[pow_idx_l].m_n.get();
        expr* rexp = f.powers()[pow_idx_r].m_n.get();

        // Branch 1 (first, immediately materialized): lexp < rexp, i.e.
        // rexp >= lexp + 1.
        expr_ref lexp_plus_1(a.mk_add(lexp, a.mk_int(1)), m);
        af.add_constraint(a.mk_ge(rexp, lexp_plus_1.get()), dep);

        iterator* it = alloc(iterator, n, m_arith_id, lexp, rexp, dep, m, a);
        out = eq_tree::edge("power-cmp:<", dep, true, 0);
        committed = true;
        return it;
    }

    // -- power_split_elim --

    // Ported from c3's `comm_power` (seq_nielsen_simplify.cpp): scan
    // `side`'s directional run (from the front if `fwd`, else from the
    // back) for repeated copies of `base_pattern` (the flattened token
    // pattern of some power's own base `U`), returning how many complete
    // copies were consumed as a symbolic sum expression, plus the number
    // of *tokens* of `side` that participated (0 if no complete copy was
    // ever matched). At each pattern boundary (not mid-pattern, and not
    // at the very first token, mirroring c3's `i > 0` guard that avoids
    // undoing power_split's own `u . u^(n-1)` unwinding), a token that is
    // itself a registered power obligation with exactly the same base
    // token pattern is absorbed whole - its entire exponent is added to
    // the running sum directly, rather than requiring it to be matched
    // token-by-token.
    static bool comm_power(power_facet const& f, expr_ref_vector const& base_pattern,
                            expr_ref_vector const& side, bool fwd, unsigned exclude_idx,
                            ast_manager& m, arith_util& a, seq_util& u,
                            expr_ref& count, unsigned& consumed) {
        unsigned bn = base_pattern.size();
        unsigned sn = side.size();
        consumed = 0;
        if (bn == 0 || sn == 0)
            return false;

        expr* sum = nullptr;
        unsigned pos = 0;
        expr* last_stable_sum = nullptr;
        unsigned last_stable_idx = 0;

        unsigned i = 0;
        for (; i < sn; ++i) {
            expr* t = fwd ? side[i] : side[sn - 1 - i];
            if (pos == 0) {
                last_stable_idx = i;
                last_stable_sum = sum;
            }
            // Case 1: direct token match with the base pattern.
            expr* pat = fwd ? base_pattern[pos] : base_pattern[bn - 1 - pos];
            if (pos < bn && t == pat) {
                ++pos;
                if (pos >= bn) {
                    pos = 0;
                    sum = sum ? a.mk_add(sum, a.mk_int(1)) : (expr*)a.mk_int(1);
                }
                continue;
            }
            // Case 2: a power token whose base is the exact same
            // pattern, absorbed whole - only at a pattern boundary
            // (pos==0), and never at the very first token (i>0).
            unsigned pidx;
            if (pos == 0 && i > 0 && f.find_power(t, pidx) && pidx != exclude_idx) {
                str_power const& q = f.powers()[pidx];
                expr_ref_vector qbase(m);
                flatten(u, q.m_s.get(), qbase);
                if (qbase.size() == bn) {
                    bool match = true;
                    for (unsigned j = 0; j < bn && match; ++j)
                        match = (qbase[j] == base_pattern[j]);
                    if (match) {
                        sum = sum ? a.mk_add(sum, q.m_n.get()) : q.m_n.get();
                        continue;
                    }
                }
            }
            break;
        }
        if (pos == 0) {
            last_stable_idx = i;
            last_stable_sum = sum;
        }
        consumed = last_stable_idx;
        if (!last_stable_sum)
            return false;
        count = expr_ref(last_stable_sum, m);
        return true;
    }

    struct elim_trigger {
        unsigned      m_eq_idx = 0;
        bool          m_pow_on_lhs = true;
        bool          m_fwd = true;
        unsigned      m_pow_idx = 0;
        expr_ref      m_count;
        eq_tree::dep_tracker m_dep;
        elim_trigger(ast_manager& m) : m_count(m) {}
    };

    // Locate a power-vs-token-run elimination trigger: some equation has
    // a power term `U^n` at a directional end of one side, whose base
    // pattern `U` recurs (per comm_power, possibly absorbing same-base
    // power tokens at boundaries) along the same directional run of the
    // *other* side. Skipped if the resulting comparison is already
    // resolved (both count and n are numerals).
    static bool find_split_elim_trigger(power_facet const& f, eq_facet const& ef,
                                         ast_manager& m, arith_util& a, seq_util& u,
                                         elim_trigger& t) {
        for (unsigned i = 0; i < ef.equations().size(); ++i) {
            eq_facet::equation const& eq = ef.equations()[i];
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue;
            for (bool pow_on_lhs : {true, false}) {
                expr_ref_vector const& pow_side = pow_on_lhs ? eq.m_lhs : eq.m_rhs;
                expr_ref_vector const& other_side = pow_on_lhs ? eq.m_rhs : eq.m_lhs;
                for (bool fwd : {true, false}) {
                    expr* end_tok = fwd ? pow_side[0] : pow_side.back();
                    unsigned pow_idx;
                    if (!is_power_token(f, end_tok, pow_idx))
                        continue;
                    str_power const& p = f.powers()[pow_idx];
                    expr_ref_vector base_pattern(m);
                    flatten(u, p.m_s.get(), base_pattern);
                    expr_ref count(m);
                    unsigned consumed;
                    if (!comm_power(f, base_pattern, other_side, fwd, pow_idx, m, a, u, count, consumed) || consumed == 0)
                        continue;
                    // Already resolved: no case split needed (mirrors
                    // c3's get_const_power_diff-guard - simplification
                    // is expected to have already discharged this case).
                    rational vc, vp;
                    if (a.is_numeral(count, vc) && a.is_numeral(p.m_n, vp))
                        continue;
                    t.m_eq_idx = i;
                    t.m_pow_on_lhs = pow_on_lhs;
                    t.m_fwd = fwd;
                    t.m_pow_idx = pow_idx;
                    t.m_count = count;
                    t.m_dep = eq.m_dep;
                    return true;
                }
            }
        }
        return false;
    }

    bool power_split_elim::iterator::next(eq_tree::edge& out) {
        if (m_done)
            return false;
        m_done = true;
        auto& af = m_n.facet_as<arith_facet_i>(m_arith_id);
        // Branch 2 (the remaining alternative once branch 1 - "count >
        // pow_exp", materialized by split() itself - has been offered):
        // pow_exp >= count.
        af.add_constraint(a.mk_ge(m_pow_exp.get(), m_count.get()), m_dep);
        out = eq_tree::edge("power-split-elim:<=", m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_split_elim::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0)
            return nullptr;
        auto& f = n.facet_as<power_facet>(m_pow_id);
        auto& ef = n.facet_as<eq_facet>(m_eq_id);
        auto& af = n.facet_as<arith_facet_i>(m_arith_id);

        elim_trigger t(m);
        if (!find_split_elim_trigger(f, ef, m, a, u, t))
            return nullptr;
        has_more = true;

        expr* pow_exp = f.powers()[t.m_pow_idx].m_n.get();
        expr* count = t.m_count.get();
        eq_tree::dep_tracker dep = t.m_dep;

        // Branch 1 (first, immediately materialized): pow_exp < count,
        // i.e. count >= pow_exp + 1.
        expr_ref pow_plus_1(a.mk_add(pow_exp, a.mk_int(1)), m);
        af.add_constraint(a.mk_ge(count, pow_plus_1.get()), dep);

        iterator* it = alloc(iterator, n, m_arith_id, pow_exp, count, dep, m, a);
        out = eq_tree::edge("power-split-elim:>", dep, true, 0);
        committed = true;
        return it;
    }

    // -- power_var_peel --

    // Locate a power-vs-variable peel trigger: some eq_facet equation
    // has, at a matching directional end of both sides, a power token
    // `U^n` opposite a Nielsen-substitutable variable `v` (not a unit,
    // not a power - see class comment). Skipped if `n` is already a
    // resolved numeral (power_propagation's known-exponent branch
    // handles that case directly, with no case split needed).
    static bool find_var_peel_trigger(power_facet const& f, eq_facet const& ef, arith_util& a, seq_util& u,
                                       unsigned& eq_idx, bool& pow_on_lhs, bool& fwd,
                                       unsigned& pow_idx, expr*& var, eq_tree::dep_tracker& dep) {
        for (unsigned i = 0; i < ef.equations().size(); ++i) {
            eq_facet::equation const& eq = ef.equations()[i];
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue;
            for (bool lhs_pow : {true, false}) {
                expr_ref_vector const& pow_side = lhs_pow ? eq.m_lhs : eq.m_rhs;
                expr_ref_vector const& var_side = lhs_pow ? eq.m_rhs : eq.m_lhs;
                for (bool f2 : {true, false}) {
                    expr* pow_tok = f2 ? pow_side[0] : pow_side.back();
                    expr* var_tok = f2 ? var_side[0] : var_side.back();
                    unsigned pidx;
                    if (!is_power_token(f, pow_tok, pidx))
                        continue;
                    bool is_var = !u.str.is_unit(var_tok) && !u.str.is_power(var_tok);
                    if (!is_var)
                        continue;
                    rational v;
                    if (a.is_numeral(f.powers()[pidx].m_n, v))
                        continue; // resolved directly by power_propagation
                    eq_idx = i;
                    pow_on_lhs = lhs_pow;
                    fwd = f2;
                    pow_idx = pidx;
                    var = var_tok;
                    dep = eq.m_dep;
                    return true;
                }
            }
        }
        return false;
    }

    bool power_var_peel::iterator::next(eq_tree::edge& out) {
        if (m_done)
            return false;
        m_done = true;

        auto& f = m_n.facet_as<power_facet>(m_pow_id);
        auto& ef = m_n.facet_as<eq_facet>(m_eq_id);
        auto& af = m_n.facet_as<arith_facet_i>(m_arith_id);
        if (m_pow_idx >= f.powers().size() || m_eq_idx >= ef.equations().size())
            return false; // defensive; obligation/equation discharged by another route

        str_power const& p = f.powers()[m_pow_idx];
        expr* exp_n = p.m_n.get();

        // Branch 2 (the remaining alternative once branch 1 - "n=0",
        // materialized by split() itself - has been offered): n >= 1,
        // peel one copy: U^n -> U . U^(n-1) (nested power, same
        // directional end), and v := U . v' on the other side.
        expr_ref n_minus_1(a.mk_sub(exp_n, a.mk_int(1)), m);
        expr_ref nested_pow(u.str.mk_power(p.m_s.get(), n_minus_1.get()), m);
        expr_ref_vector pow_repl(m);
        if (m_fwd) { pow_repl.push_back(p.m_s.get()); pow_repl.push_back(nested_pow.get()); }
        else       { pow_repl.push_back(nested_pow.get()); pow_repl.push_back(p.m_s.get()); }

        sort* s = m_var.get()->get_sort();
        expr* vp = m.mk_fresh_const("t", s);
        expr_ref_vector var_repl(m);
        if (m_fwd) { var_repl.push_back(p.m_s.get()); var_repl.push_back(vp); }
        else       { var_repl.push_back(vp); var_repl.push_back(p.m_s.get()); }

        broadcast_subst(m_n, m_eq_id, p.m_e.get(), pow_repl, m_dep);
        broadcast_subst(m_n, m_eq_id, m_var.get(), var_repl, m_dep);
        af.add_constraint(a.mk_ge(exp_n, a.mk_int(1)), m_dep);
        f.remove(m_pow_idx);

        out = eq_tree::edge("power-var-peel:n>=1", m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_var_peel::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0)
            return nullptr;
        auto& f = n.facet_as<power_facet>(m_pow_id);
        auto& ef = n.facet_as<eq_facet>(m_eq_id);
        auto& af = n.facet_as<arith_facet_i>(m_arith_id);

        unsigned eq_idx, pow_idx;
        bool pow_on_lhs, fwd;
        expr* var = nullptr;
        eq_tree::dep_tracker dep;
        if (!find_var_peel_trigger(f, ef, a, u, eq_idx, pow_on_lhs, fwd, pow_idx, var, dep))
            return nullptr;
        has_more = true;

        str_power const& p = f.powers()[pow_idx];
        expr* exp_n = p.m_n.get();
        expr* e = p.m_e.get();

        // Branch 1 (first, immediately materialized): n = 0, replace
        // U^n with epsilon (progress).
        expr_ref_vector empty(m);
        broadcast_subst(n, m_eq_id, e, empty, dep);
        af.add_constraint(a.mk_ge(exp_n, a.mk_int(0)), dep);
        af.add_constraint(a.mk_le(exp_n, a.mk_int(0)), dep);
        f.remove(pow_idx);

        iterator* it = alloc(iterator, n, m_pow_id, m_eq_id, m_arith_id, eq_idx, pow_on_lhs, fwd, pow_idx, var, dep, m, u, a);
        out = eq_tree::edge("power-var-peel:n=0", dep, true, 0);
        committed = true;
        return it;
    }

    // -- power_var_decompose --

    expr* power_var_decompose::get_or_create_n_var(expr* var) {
        expr* v = nullptr;
        if (m_n_cache.find(var, v))
            return v;
        v = m.mk_fresh_const("gp-n", a.mk_int());
        m_n_cache.insert(var, v);
        return v;
    }

    expr* power_var_decompose::get_or_create_m_var(expr* var) {
        expr* v = nullptr;
        if (m_m_cache.find(var, v))
            return v;
        v = m.mk_fresh_const("gp-m", a.mk_int());
        m_m_cache.insert(var, v);
        return v;
    }

    // Locate a variable-vs-power decomposition trigger: some eq_facet
    // equation has, at a matching directional end of both sides, a
    // Nielsen-substitutable variable `v` opposite a power token `U^n`,
    // where `U`'s own flattened base has at least one token (an empty
    // base cannot happen for a well-formed power term, but the check is
    // defensive). Skipped if `n` is already a resolved numeral
    // (power_propagation's known-exponent unfold handles that case
    // directly, no case split needed).
    static bool find_var_decompose_trigger(power_facet const& f, eq_facet const& ef, arith_util& a, seq_util& u,
                                            unsigned& pow_idx, expr*& var, bool& fwd, eq_tree::dep_tracker& dep) {
        for (unsigned i = 0; i < ef.equations().size(); ++i) {
            eq_facet::equation const& eq = ef.equations()[i];
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue;
            for (bool lhs_pow : {true, false}) {
                expr_ref_vector const& pow_side = lhs_pow ? eq.m_lhs : eq.m_rhs;
                expr_ref_vector const& var_side = lhs_pow ? eq.m_rhs : eq.m_lhs;
                for (bool f2 : {true, false}) {
                    expr* pow_tok = f2 ? pow_side[0] : pow_side.back();
                    expr* var_tok = f2 ? var_side[0] : var_side.back();
                    unsigned pidx;
                    if (!is_power_token(f, pow_tok, pidx))
                        continue;
                    bool is_var = !u.str.is_unit(var_tok) && !u.str.is_power(var_tok);
                    if (!is_var)
                        continue;
                    rational v;
                    if (a.is_numeral(f.powers()[pidx].m_n, v))
                        continue; // resolved directly by power_propagation
                    pow_idx = pidx;
                    var = var_tok;
                    fwd = f2;
                    dep = eq.m_dep;
                    return true;
                }
            }
        }
        return false;
    }

    bool power_var_decompose::iterator::next(eq_tree::edge& out) {
        auto& ef = m_n.facet_as<eq_facet>(m_eq_id);
        auto& af = m_n.facet_as<arith_facet_i>(m_arith_id);
        auto& f = m_n.facet_as<power_facet>(m_pow_id);

        while (m_pos < m_base_toks.size()) {
            unsigned i = m_pos++;
            expr* tok = m_base_toks[i].get();

            // Skip position i when the *preceding* token is itself a
            // power: that position's own m' range (0<=m'<=inner_exp)
            // already covers this boundary (mirrors c3's `i>0 &&
            // base_toks[i-1]->is_power()` skip guard).
            unsigned prev_pidx;
            if (i > 0 && is_power_token(f, m_base_toks[i - 1].get(), prev_pidx))
                continue;

            // Build the U^m . prefix (or U^m . prefix . w^m') replacement,
            // in the direction v faces U^n: m_base_toks is already
            // stored in that direction (see split()'s construction), so
            // the prefix is simply toks[0..i-1] and the new suffix token
            // (plain-char case) or w^m' (power case) is appended/
            // prepended according to m_fwd.
            expr_ref_vector prefix(m);
            for (unsigned j = 0; j < i; ++j)
                prefix.push_back(m_base_toks[j].get());

            unsigned tok_pidx;
            expr* fresh_inner_m = nullptr;
            expr* inner_exp = nullptr;
            expr_ref suffix_tok(m);
            if (is_power_token(f, tok, tok_pidx)) {
                str_power const& q = f.powers()[tok_pidx];
                inner_exp = q.m_n.get();
                fresh_inner_m = m_owner->get_or_create_m_var(m_var.get());
                suffix_tok = expr_ref(u.str.mk_power(q.m_s.get(), fresh_inner_m), m);
            }
            else
                suffix_tok = expr_ref(tok, m);

            expr_ref_vector repl(m);
            if (m_fwd) {
                repl.push_back(m_pow_e.get());
                for (unsigned j = 0; j < prefix.size(); ++j) repl.push_back(prefix[j].get());
                if (fresh_inner_m) repl.push_back(suffix_tok.get());
            } else {
                if (fresh_inner_m) repl.push_back(suffix_tok.get());
                for (unsigned j = prefix.size(); j-- > 0; ) repl.push_back(prefix[j].get());
                repl.push_back(m_pow_e.get());
            }
            // Plain-char case (no power at position i): the token
            // itself contributes nothing further beyond U^m . prefix
            // (per c3's P(char)=epsilon rule - the char is absorbed into
            // the base pattern's own repetition count, not appended
            // again literally).

            broadcast_subst(m_n, m_eq_id, m_var.get(), repl, m_dep);
            af.add_constraint(a.mk_ge(m_fresh_m.get(), a.mk_int(0)), m_dep);
            if (fresh_inner_m) {
                af.add_constraint(a.mk_ge(fresh_inner_m, a.mk_int(0)), m_dep);
                af.add_constraint(a.mk_ge(inner_exp, fresh_inner_m), m_dep);
            }
            out = eq_tree::edge("power-var-decompose:pos", m_dep, true, 0);
            return true;
        }

        if (!m_extend_done) {
            m_extend_done = true;
            // Final non-progress branch: v extends past the whole power,
            // v := U^n . v' (or v' . U^n if !m_fwd), fresh v', side
            // constraint len(v') >= 0 (trivially true, but matches c3's
            // own explicit branch condition and keeps the constraint
            // symmetric with the other branches' side constraints).
            sort* s = m_var.get()->get_sort();
            expr* vp = m.mk_fresh_const("t", s);
            expr_ref_vector repl(m);
            if (m_fwd) { repl.push_back(m_pow_e.get()); repl.push_back(vp); }
            else       { repl.push_back(vp); repl.push_back(m_pow_e.get()); }
            broadcast_subst(m_n, m_eq_id, m_var.get(), repl, m_dep);
            af.add_constraint(a.mk_ge(u.str.mk_length(vp), a.mk_int(0)), m_dep);
            out = eq_tree::edge("power-var-decompose:extend", m_dep, true, 0);
            return true;
        }
        return false;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_var_decompose::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0)
            return nullptr;
        auto& f = n.facet_as<power_facet>(m_pow_id);
        auto& ef = n.facet_as<eq_facet>(m_eq_id);
        auto& af = n.facet_as<arith_facet_i>(m_arith_id);

        unsigned pow_idx;
        expr* var = nullptr;
        bool fwd;
        eq_tree::dep_tracker dep;
        if (!find_var_decompose_trigger(f, ef, a, u, pow_idx, var, fwd, dep))
            return nullptr;

        str_power const& p = f.powers()[pow_idx];
        expr_ref_vector base_toks(m);
        flatten(u, p.m_s.get(), base_toks);
        if (base_toks.empty())
            return nullptr;
        if (!fwd) {
            // Store base_toks in the direction v faces U^n (reversed,
            // mirroring c3's `collect_tokens_dir(base, fwd, ...)`).
            expr_ref_vector rev(m);
            for (unsigned j = base_toks.size(); j-- > 0; ) rev.push_back(base_toks[j].get());
            base_toks = std::move(rev);
        }

        expr* fresh_m = get_or_create_n_var(var);
        has_more = true;

        iterator* it = alloc(iterator, n, m_pow_id, m_eq_id, m_arith_id, var, p.m_e.get(), base_toks, fresh_m, fwd, dep, m, u, a, this);
        // First branch is offered by the iterator itself (position 0),
        // uniformly with every other decomposition position - unlike
        // power_var_peel/power_split, there is no "cheap" branch to
        // materialize immediately in split() itself here (every
        // decomposition position, including position 0, requires the
        // same shape of substitution), so split() simply hands off to
        // the iterator's first next() call.
        eq_tree::edge first;
        if (!it->next(first)) {
            dealloc(it);
            return nullptr;
        }
        out = first;
        committed = true;
        return it;
    }

    // -- power_gpower_intro --

    expr* power_gpower_intro::get_or_create_n_var(expr* var) {
        expr* v = nullptr;
        if (m_n_cache.find(var, v))
            return v;
        v = m.mk_fresh_const("gp-n", a.mk_int());
        m_n_cache.insert(var, v);
        return v;
    }

    expr* power_gpower_intro::get_or_create_m_var(expr* var) {
        expr* v = nullptr;
        if (m_m_cache.find(var, v))
            return v;
        v = m.mk_fresh_const("gp-m", a.mk_int());
        m_m_cache.insert(var, v);
        return v;
    }

    // Is `e` a Nielsen-substitutable variable token (neither a unit nor
    // a power)? Local predicate, per z3papers/nseq's token model - see
    // word_eq_split's own comment for why this is computed locally
    // rather than via theory_seq::is_var.
    static bool is_gpower_var(seq_util& u, expr* e) {
        return !u.str.is_unit(e) && !u.str.is_power(e);
    }

    // Locate a self-cycle trigger for gpower introduction: some
    // eq_facet equation has, at a directional end of one side, a bare
    // Nielsen-substitutable variable `v`, while the *other* side,
    // scanned from the matching end, is a non-empty run of ground
    // (non-variable) tokens followed by that same variable `v`
    // reappearing. `ground_prefix` is returned in the direction `v`
    // faces the cycle (i.e. nearest-to-farthest from the reappearance
    // point), matching `power_var_decompose`'s own `m_base_toks`
    // convention.
    static bool find_gpower_trigger(eq_facet const& ef, seq_util& u, ast_manager& m,
                                     unsigned& eq_idx, bool& fwd,
                                     expr_ref_vector& ground_prefix, expr*& var, eq_tree::dep_tracker& dep) {
        for (unsigned i = 0; i < ef.equations().size(); ++i) {
            eq_facet::equation const& eq = ef.equations()[i];
            if (eq.m_lhs.empty() || eq.m_rhs.empty())
                continue;
            for (bool f2 : {true, false}) {
                expr* lhead = f2 ? eq.m_lhs[0] : eq.m_lhs.back();
                expr* rhead = f2 ? eq.m_rhs[0] : eq.m_rhs.back();
                bool lhead_is_var = is_gpower_var(u, lhead);
                bool rhead_is_var = is_gpower_var(u, rhead);

                // Orientation 1: rhs directional head is the bare
                // target variable; scan lhs in the same direction for a
                // ground prefix that cycles back to it.
                if (rhead_is_var && !lhead_is_var) {
                    expr_ref_vector prefix(m);
                    expr* target = nullptr;
                    unsigned sz = eq.m_lhs.size();
                    for (unsigned k = 0; k < sz; ++k) {
                        expr* t = f2 ? eq.m_lhs[k] : eq.m_lhs[sz - 1 - k];
                        if (is_gpower_var(u, t)) { target = t; break; }
                        prefix.push_back(t);
                    }
                    if (target && !prefix.empty() && target == rhead) {
                        eq_idx = i;
                        fwd = f2;
                        ground_prefix = std::move(prefix);
                        var = rhead;
                        dep = eq.m_dep;
                        return true;
                    }
                }

                // Orientation 2: symmetric, lhs directional head is the
                // target variable; scan rhs.
                if (lhead_is_var && !rhead_is_var) {
                    expr_ref_vector prefix(m);
                    expr* target = nullptr;
                    unsigned sz = eq.m_rhs.size();
                    for (unsigned k = 0; k < sz; ++k) {
                        expr* t = f2 ? eq.m_rhs[k] : eq.m_rhs[sz - 1 - k];
                        if (is_gpower_var(u, t)) { target = t; break; }
                        prefix.push_back(t);
                    }
                    if (target && !prefix.empty() && target == lhead) {
                        eq_idx = i;
                        fwd = f2;
                        ground_prefix = std::move(prefix);
                        var = lhead;
                        dep = eq.m_dep;
                        return true;
                    }
                }
            }
        }
        return false;
    }

    bool power_gpower_intro::iterator::next(eq_tree::edge& out) {
        auto& af = m_n.facet_as<arith_facet_i>(m_arith_id);
        auto& f = m_n.facet_as<power_facet>(m_pow_id);

        while (m_pos < m_base_toks.size()) {
            unsigned i = m_pos++;
            expr* tok = m_base_toks[i].get();

            // Skip position i when the preceding token is itself a
            // power - its own m' range already covers this boundary
            // (mirrors power_var_decompose's identical skip guard and
            // c3's own).
            unsigned prev_pidx;
            if (i > 0 && is_power_token(f, m_base_toks[i - 1].get(), prev_pidx))
                continue;

            expr_ref_vector prefix(m);
            for (unsigned j = 0; j < i; ++j)
                prefix.push_back(m_base_toks[j].get());

            unsigned tok_pidx;
            expr* fresh_inner_m = nullptr;
            expr* inner_exp = nullptr;
            expr_ref suffix_tok(m);
            if (is_power_token(f, tok, tok_pidx)) {
                str_power const& q = f.powers()[tok_pidx];
                inner_exp = q.m_n.get();
                fresh_inner_m = m_owner->get_or_create_m_var(m_var.get());
                suffix_tok = expr_ref(u.str.mk_power(q.m_s.get(), fresh_inner_m), m);
            }
            else
                suffix_tok = expr_ref(tok, m);

            expr_ref_vector repl(m);
            if (m_fwd) {
                repl.push_back(m_pow_e.get());
                for (unsigned j = 0; j < prefix.size(); ++j) repl.push_back(prefix[j].get());
                if (fresh_inner_m) repl.push_back(suffix_tok.get());
            } else {
                if (fresh_inner_m) repl.push_back(suffix_tok.get());
                for (unsigned j = prefix.size(); j-- > 0; ) repl.push_back(prefix[j].get());
                repl.push_back(m_pow_e.get());
            }

            broadcast_subst(m_n, m_eq_id, m_var.get(), repl, m_dep);
            af.add_constraint(a.mk_ge(m_fresh_n.get(), a.mk_int(0)), m_dep);
            if (fresh_inner_m) {
                af.add_constraint(a.mk_ge(fresh_inner_m, a.mk_int(0)), m_dep);
                af.add_constraint(a.mk_ge(inner_exp, fresh_inner_m), m_dep);
            }
            out = eq_tree::edge("power-gpower-intro:pos", m_dep, true, 0);
            return true;
        }
        return false;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_gpower_intro::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0)
            return nullptr;
        auto& f = n.facet_as<power_facet>(m_pow_id);
        auto& ef = n.facet_as<eq_facet>(m_eq_id);

        unsigned eq_idx;
        bool fwd;
        expr_ref_vector ground_prefix_orig(m);
        expr* var = nullptr;
        eq_tree::dep_tracker dep;
        if (!find_gpower_trigger(ef, u, m, eq_idx, fwd, ground_prefix_orig, var, dep))
            return nullptr;

        // Compress the ground prefix to its minimal repeating period
        // (token-identity match, since flatten() hash-conses identical
        // sub-terms to the same expr*).
        unsigned gn = ground_prefix_orig.size();
        unsigned period = gn;
        for (unsigned p = 1; p <= gn / 2; ++p) {
            if (gn % p != 0)
                continue;
            bool match = true;
            for (unsigned i = p; i < gn && match; ++i)
                match = ground_prefix_orig[i].get() == ground_prefix_orig[i % p].get();
            if (match) { period = p; break; }
        }
        expr_ref_vector compressed(m);
        for (unsigned i = 0; i < period; ++i)
            compressed.push_back(ground_prefix_orig[i].get());

        // If the compressed prefix is a single power token, unwrap it to
        // its own base tokens (natural order), avoiding a nested
        // power-of-power - mirrors c3's own unwrap step.
        if (compressed.size() == 1) {
            unsigned pidx;
            if (is_power_token(f, compressed[0].get(), pidx)) {
                expr_ref_vector inner_base_toks(m);
                flatten(u, f.powers()[pidx].m_s.get(), inner_base_toks);
                if (!inner_base_toks.empty()) {
                    expr_ref_vector rev(m);
                    if (fwd)
                        for (unsigned j = 0; j < inner_base_toks.size(); ++j) rev.push_back(inner_base_toks[j].get());
                    else
                        for (unsigned j = inner_base_toks.size(); j-- > 0; ) rev.push_back(inner_base_toks[j].get());
                    compressed = std::move(rev);
                }
            }
        }
        if (compressed.empty())
            return nullptr;

        // Build the power's base string in natural (left-to-right)
        // order: `compressed` is stored in the direction `var` faces
        // the cycle, which equals natural order when fwd, and is
        // reversed natural order otherwise.
        expr_ref_vector natural(m);
        if (fwd)
            for (unsigned j = 0; j < compressed.size(); ++j) natural.push_back(compressed[j].get());
        else
            for (unsigned j = compressed.size(); j-- > 0; ) natural.push_back(compressed[j].get());

        expr_ref base_str(natural[0].get(), m);
        for (unsigned j = 1; j < natural.size(); ++j)
            base_str = expr_ref(u.str.mk_concat(base_str.get(), natural[j].get()), m);

        expr* fresh_n = get_or_create_n_var(var);
        expr_ref power_expr(u.str.mk_power(base_str.get(), fresh_n), m);

        // Register the fresh power obligation (shared by every branch
        // this call generates - power_propagation will pick it up on
        // the very next round in each resulting branch).
        f.add_power_trailed(power_expr.get(), base_str.get(), fresh_n, dep);
        has_more = true;

        iterator* it = alloc(iterator, n, m_pow_id, m_eq_id, m_arith_id, var, power_expr.get(), compressed, fresh_n, fwd, dep, m, u, a, this);
        eq_tree::edge first;
        if (!it->next(first)) {
            dealloc(it);
            return nullptr;
        }
        out = first;
        committed = true;
        return it;
    }

} // namespace seq
