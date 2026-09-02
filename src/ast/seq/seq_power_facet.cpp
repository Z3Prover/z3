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
#include "smt/seq_arith_facet.h"

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
        auto& af = n.facet_as<arith_facet>(m_arith_id);

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

    // -- power_split --

    bool power_split::iterator::next(eq_tree::edge& out) {
        auto& f = m_n.facet_as<power_facet>(m_pow_id);
        if (m_pow_index >= f.powers().size())
            return false; // obligation already discharged by another route
        str_power const& p = f.powers()[m_pow_index];

        if (m_next_j > m_bound)
            return false;

        auto& ef = m_n.facet_as<eq_facet>(m_eq_id);
        auto& af = m_n.facet_as<arith_facet>(m_arith_id);
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
        auto& af = n.facet_as<arith_facet>(m_arith_id);

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
