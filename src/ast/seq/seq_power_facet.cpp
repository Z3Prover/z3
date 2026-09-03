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
                ef.apply_subst(p.m_e.get(), repl, p.m_dep);
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
        ef.apply_subst(p.m_e.get(), repl, m_dep);
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
            ef.apply_subst(p.m_e.get(), empty, dep);
            af.add_constraint(a.mk_le(p.m_n.get(), a.mk_int(0)), dep);
            f.remove(i);

            iterator* it = alloc(iterator, n, m_pow_id, m_eq_id, m_arith_id, i, bound, dep, m, u, a);
            out = eq_tree::edge("power:n<=0", dep, true, 0);
            committed = true;
            return it;
        }
        return nullptr;
    }

} // namespace seq
