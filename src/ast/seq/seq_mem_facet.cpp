/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_mem_facet.cpp

Abstract:

    See seq_mem_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/seq/seq_mem_facet.h"
#include "ast/ast_pp.h"
#include <algorithm>

namespace seq {

    namespace {
        int cmp_mem(str_mem const& a, str_mem const& b) {
            if (a.m_str.get()->get_id() != b.m_str.get()->get_id())
                return a.m_str.get()->get_id() < b.m_str.get()->get_id() ? -1 : 1;
            auto ak = a.m_view.key(), bk = b.m_view.key();
            if (ak.state != bk.state)
                return ak.state < bk.state ? -1 : 1;
            if (ak.target != bk.target)
                return ak.target < bk.target ? -1 : 1;
            return 0;
        }

        void flatten_to_expr(seq_util& u, expr_ref_vector const& ts, expr_ref& out) {
            ast_manager& m = out.get_manager();
            out = expr_ref(u.str.mk_concat(ts.size(), ts.data(), ts.empty() ? u.str.mk_string_sort() : ts[0]->get_sort()), m);
        }

    }

    void mem_facet::add(str_mem const& sm) {
        m_mems.push_back(sm);
        m_trail.push(push_back_trail<str_mem>(m_mems));
    }

    void mem_facet::narrow(unsigned idx, view const& new_view) {
        SASSERT(idx < m_mems.size());
        if (m_mems[idx].m_view == new_view)
            return;
        m_trail.push(vector_field_trail<str_mem, view>(m_mems, idx, &str_mem::m_view));
        m_mems[idx].m_view = new_view;
    }

    void mem_facet::remove(unsigned idx) {
        SASSERT(idx < m_mems.size());
        m_trail.push(vector_erase_trail<str_mem>(m_mems, idx));
        m_mems.erase(m_mems.begin() + idx);
    }

    void mem_facet::replace(unsigned idx, expr* new_str, eq_tree::dep_tracker dep) {
        SASSERT(idx < m_mems.size());
        m_trail.push(vector_field_trail<str_mem, expr_ref>(m_mems, idx, &str_mem::m_str));
        m_mems[idx].m_str = expr_ref(new_str, m);
        if (dep) {
            m_trail.push(vector_field_trail<str_mem, eq_tree::dep_tracker>(m_mems, idx, &str_mem::m_dep));
            m_mems[idx].m_dep = m_dm.mk_join(m_mems[idx].m_dep, dep);
        }
    }

    void mem_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        expr_ref replacement(m);
        flatten_to_expr(u, repl, replacement);
        for (unsigned i = 0; i < m_mems.size(); ++i) {
            if (m_mems[i].m_str.get() != var)
                continue;
            m_trail.push(vector_field_trail<str_mem, expr_ref>(m_mems, i, &str_mem::m_str));
            m_mems[i].m_str = replacement;
            if (subst_dep) {
                m_trail.push(vector_field_trail<str_mem, eq_tree::dep_tracker>(m_mems, i, &str_mem::m_dep));
                m_mems[i].m_dep = m_dm.mk_join(m_mems[i].m_dep, subst_dep);
            }
        }
    }

    stx::facet_i* mem_facet::clone(trail_stack& trail) const {
        mem_facet* f = alloc(mem_facet, trail, m, u, m_dm);
        f->m_mems.append(m_mems);
        return f;
    }

    unsigned mem_facet::hash() const {
        unsigned h = m_mems.size() * 334214467u;
        for (auto const& sm : m_mems) {
            unsigned mh = combine_hash(sm.m_str->get_id(), sm.m_view.key().state);
            mh = combine_hash(mh, sm.m_view.key().target);
            h += mh;
        }
        return h ? h : 1;
    }

    bool mem_facet::similar(facet_i const& other) const {
        auto const& o = static_cast<mem_facet const&>(other);
        if (m_mems.size() != o.m_mems.size())
            return false;
        vector<str_mem> a = m_mems, b = o.m_mems;
        std::sort(a.begin(), a.end(), [](str_mem const& x, str_mem const& y) { return cmp_mem(x, y) < 0; });
        std::sort(b.begin(), b.end(), [](str_mem const& x, str_mem const& y) { return cmp_mem(x, y) < 0; });
        for (unsigned i = 0; i < a.size(); ++i)
            if (cmp_mem(a[i], b[i]) != 0)
                return false;
        return true;
    }

    std::ostream& mem_facet::display(std::ostream& out) const {
        out << "mem_facet: " << m_mems.size() << " membership(s)\n";
        for (auto const& sm : m_mems) {
            out << "  " << mk_pp(sm.m_str.get(), m) << " in state " << mk_pp(sm.m_view.m_state, m);
            if (sm.m_view.is_reach())
                out << " -> " << mk_pp(sm.m_view.m_target, m);
            out << "\n";
        }
        return out;
    }

    stx::simplify_result mem_propagation::propagate(eq_tree::node& n) {
        auto& f = get_ambient(n, m, u).mem_facet_ref();
        bool changed = false;
        m_stats.m_num_propagate++;
        for (unsigned i = 0; i < f.memberships().size(); ) {
            auto const& sm = f.memberships()[i];
            expr_ref cur(sm.m_view.m_state, m_rw.m());
            expr_ref_vector ts(m);
            u.str.get_concat_units(sm.m_str.get(), ts);
            bool bad = false;
            for (expr* t : ts) {
                if (!is_const_token(u, t)) { bad = true; break; }
                expr* elem = nullptr;
                VERIFY(u.str.is_unit(t, elem));
                cur = m_rw.mk_derivative(elem, cur);
                if (u.re.is_empty(cur)) {
                    n.set_conflict(stx::br_plugin_base, sm.m_dep);
                    return stx::simplify_result::conflict;
                }
            }
            auto live = m_live.reachable_live(sm.m_view.m_state);
            if (!bad && sm.m_view.is_membership()) {
                expr_ref nb = m_rw.is_nullable(cur);
                if (m_rw.m().is_false(nb)) {
                    n.set_conflict(stx::br_plugin_base, sm.m_dep);
                    return stx::simplify_result::conflict;
                }
                if (m_rw.m().is_true(nb)) {
                    f.remove(i);
                    changed = true;
                    continue;
                }
            }
            if (live.is_dead() || seq::is_dead(sm.m_view, m_rw)) {
                n.set_conflict(stx::br_plugin_base, sm.m_dep);
                return stx::simplify_result::conflict;
            }
            lbool a = bad ? seq::accepts(sm.m_view, m_rw) : l_undef;
            if (a == l_false) {
                n.set_conflict(stx::br_plugin_base, sm.m_dep);
                return stx::simplify_result::conflict;
            }
            if (a == l_true) {
                f.remove(i);
                changed = true;
                continue;
            }
            ++i;
        }
        if (f.is_satisfied())
            return stx::simplify_result::satisfied;
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

    bool mem_var_split::iterator::next(eq_tree::edge& out) {
        if (m_done)
            return false;
        m_done = true;
        auto ac = get_ambient(m_n, m, u);
        auto& eq = ac.eq_facet_ref();
        expr_ref_vector repl(eq.get_manager());
        expr* fresh = eq.mk_fresh_var(m_var->get_sort());
        repl.push_back(fresh);
        broadcast_subst(m_n, ac.context(), m_var, repl, m_dep);
        out = eq_tree::edge("mem-v:=v'", nullptr, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> mem_var_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n, m, u);
        if (cost != 0 || !ac.has_eq())
            return nullptr;
        auto& mf = ac.mem_facet_ref();
        for (unsigned i = 0; i < mf.memberships().size(); ++i) {
            expr* s = mf.memberships()[i].m_str.get();
            expr_ref_vector ts(m);
            u.str.get_concat_units(s, ts);
            if (ts.empty() || is_const_token(u, ts.get(0)))
                continue;
            expr* var = ts.get(0);
            eq_tree::dep_tracker dep = mf.memberships()[i].m_dep;
            iterator* it = alloc(iterator, n, i, var, m, u, dep);
            auto& eq = ac.eq_facet_ref();
            expr_ref_vector empty(eq.get_manager());
            broadcast_subst(n, ac.context(), var, empty, dep);
            out = eq_tree::edge("mem-v:=eps", nullptr, true, 0);
            committed = true;
            m_stats.m_num_splits++;
            return it;
        }
        return nullptr;
    }

    mem_monadic_split::iterator::iterator(eq_tree::node& n, seq_rewriter& rw, trail_stack& trail, ast_manager& m, seq_util& u,
                                          vector<str_mem> const& mems) :
        m_n(n), m_mon(rw, trail, transition_mode::brzozowski_tm), m_it(m_mon.iterate(64)), m(m), u(u) {
        m_mon.set_gen_solution(true);
        for (auto const& sm : mems)
            m_mon.add(sm.m_str.get(), sm.m_view.m_state, sm.m_dep);
        obj_map<expr, seq::view_vector> first;
        if (m_it.next(first))
            for (auto const& [var, views] : first)
                m_first.insert(var, views);
    }

    bool mem_monadic_split::iterator::apply_solution(obj_map<expr, seq::view_vector>& sol, eq_tree::edge& out) {
        auto& mf = get_ambient(m_n, m, u).mem_facet_ref();
        bool changed = false;
        for (unsigned i = 0; i < mf.memberships().size(); ++i) {
            auto const& sm = mf.memberships()[i];
            seq::view_vector views;
            if (!sol.find(sm.m_str.get(), views) || views.empty())
                continue;
            mf.narrow(i, views[0]);
            changed = true;
        }
        if (!changed)
            return false;
        out = eq_tree::edge("mem-monadic", nullptr, true, 0);
        return true;
    }

    // Locate a membership-side var-peel trigger: some mem_facet
    // membership's own flattened string has a power token `U^n` at a
    // directional end (front or back). No "opposite side" check is
    // needed, since a membership has only one string operand (see class
    // comment on power_var_peel_mem). Skipped if `n` is already a
    // resolved numeral (power_propagation's known-exponent branch
    // handles that case directly).
    static bool find_var_peel_mem_trigger(power_facet const& f, mem_facet const& mf, arith_util& a,
                                           unsigned& mem_idx, bool& fwd, unsigned& pow_idx,
                                           eq_tree::dep_tracker& dep) {
        for (unsigned i = 0; i < mf.memberships().size(); ++i) {
            str_mem const& sm = mf.memberships()[i];
            expr_ref_vector ts(mf.get_manager());
            mf.get_seq_util().str.get_concat_units(sm.m_str.get(), ts);
            if (ts.empty())
                continue;
            for (bool f2 : {true, false}) {
                expr* tok = f2 ? ts.get(0) : ts.back();
                unsigned pidx;
                if (!f.find_power(tok, pidx))
                    continue;
                rational v;
                if (a.is_numeral(f.powers()[pidx].m_n, v))
                    continue; // resolved directly by power_propagation
                mem_idx = i;
                fwd = f2;
                pow_idx = pidx;
                dep = sm.m_dep;
                return true;
            }
        }
        return false;
    }

    bool power_var_peel_mem::iterator::next(eq_tree::edge& out) {
        if (m_done)
            return false;
        m_done = true;

        auto ac = get_ambient(m_n, m, u);
        auto& f = ac.power_facet_ref();
        auto& mf = ac.mem_facet_ref();
        auto& af = ac.arith_facet_ref();
        if (m_pow_idx >= f.powers().size() || m_mem_idx >= mf.memberships().size())
            return false; // defensive; obligation/membership discharged by another route

        str_power const& p = f.powers()[m_pow_idx];
        expr* exp_n = p.m_n.get();

        // Branch 2 (the remaining alternative once branch 1 - "n=0",
        // materialized by split() itself - has been offered): n >= 1,
        // peel one copy: U^n -> U . U^(n-1) (nested power, same
        // directional end), spliced directly into this membership's
        // own string.
        expr_ref n_minus_1(a.mk_sub(exp_n, a.mk_int(1)), m);
        expr_ref nested_pow(u.str.mk_power(p.m_s.get(), n_minus_1.get()), m);

        expr_ref_vector ts(m);
        u.str.get_concat_units(mf.memberships()[m_mem_idx].m_str.get(), ts);
        SASSERT(!ts.empty());
        expr_ref_vector new_ts(m);
        if (m_fwd) {
            new_ts.push_back(p.m_s.get());
            new_ts.push_back(nested_pow.get());
            for (unsigned i = 1; i < ts.size(); ++i)
                new_ts.push_back(ts[i].get());
        }
        else {
            for (unsigned i = 0; i + 1 < ts.size(); ++i)
                new_ts.push_back(ts[i].get());
            new_ts.push_back(nested_pow.get());
            new_ts.push_back(p.m_s.get());
        }
        expr_ref new_str(u.str.mk_concat(new_ts.size(), new_ts.data(), new_ts[0]->get_sort()), m);

        mf.replace(m_mem_idx, new_str, m_dep);
        af.add_constraint(a.mk_ge(exp_n, a.mk_int(1)), m_dep);
        f.remove(m_pow_idx);

        out = eq_tree::edge("power-var-peel-mem:n>=1", m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_var_peel_mem::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0)
            return nullptr;
        auto ac = get_ambient(n, m, u);
        auto& f = ac.power_facet_ref();
        auto& mf = ac.mem_facet_ref();
        auto& af = ac.arith_facet_ref();

        unsigned mem_idx, pow_idx;
        bool fwd;
        eq_tree::dep_tracker dep;
        if (!find_var_peel_mem_trigger(f, mf, a, mem_idx, fwd, pow_idx, dep))
            return nullptr;
        has_more = true;

        str_power const& p = f.powers()[pow_idx];
        expr* exp_n = p.m_n.get();
        expr* e = p.m_e.get();

        // Branch 1 (first, immediately materialized): n = 0, replace
        // U^n with epsilon (progress). c3's mem-variant asserts a
        // single `n = 0` clause (not the eq-variant's `n>=0 /\ n<=0`
        // pair) - preserved faithfully per rule variant.
        expr_ref_vector ts(m);
        u.str.get_concat_units(mf.memberships()[mem_idx].m_str.get(), ts);
        SASSERT(!ts.empty());
        unsigned drop = fwd ? 0 : ts.size() - 1;
        ts.erase(drop);
        expr_ref new_str(m);
        if (ts.empty())
            new_str = expr_ref(u.str.mk_empty(e->get_sort()), m);
        else
            new_str = expr_ref(u.str.mk_concat(ts.size(), ts.data(), ts.get(0)->get_sort()), m);
        mf.replace(mem_idx, new_str, dep);
        af.add_constraint(m.mk_eq(exp_n, a.mk_int(0)), dep);
        f.remove(pow_idx);

        iterator* it = alloc(iterator, n, mem_idx, fwd, pow_idx, dep, m, u, a);
        out = eq_tree::edge("power-var-peel-mem:n=0", dep, true, 0);
        committed = true;
        m_stats.m_num_splits++;
        return it;
    }

    bool mem_monadic_split::iterator::next(eq_tree::edge& out) {
        obj_map<expr, seq::view_vector> sol;
        if (m_first_pending) {
            m_first_pending = false;
            for (auto const& [var, views] : m_first)
                sol.insert(var, views);
        }
        else if (!m_it.next(sol))
            return false;
        return apply_solution(sol, out);
    }

    scoped_ptr<eq_tree::split_iterator_i> mem_monadic_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0)
            return nullptr;
        auto& mf = get_ambient(n, m, u).mem_facet_ref();
        if (mf.memberships().empty())
            return nullptr;
        bool has_multi = false;
        for (auto const& sm : mf.memberships()) {
            expr_ref_vector ts(m);
            u.str.get_concat_units(sm.m_str.get(), ts);
            unsigned vars = 0;
            for (expr* t : ts)
                if (!is_const_token(u, t))
                    ++vars;
            if (vars >= 2) {
                has_multi = true;
                break;
            }
        }
        if (!has_multi)
            return nullptr;
        scoped_ptr<iterator> it(alloc(iterator, n, m_rw, m_trail, m, u, mf.memberships()));
        if (!it->has_first())
            return nullptr;
        if (!it->next(out))
            return nullptr;
        committed = true;
        m_stats.m_num_splits++;
        has_more = true;
        return it.detach();
    }

}
