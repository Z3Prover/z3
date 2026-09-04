/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_mem_facet.cpp

Abstract:

    See seq_mem_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026


NSB code review:
- we need to check non-emptiness of intersection constraints that are created after split.
  For example if we split xy in R as x in R1, y in R2, and already have x in R0 constraint,
  then check non-emptiness of R1 n R0 using functionality implemented in seq_monadic.
- We need model existence and extraction
  - model existence when all mebership constraints are x_i in R_ij and R_i1 n ... n R_ik is empty
  - model extraction as a side effect.
  - use seq_monadic to encapsulate functionality.

- nice to have: allow reverse live_states from a regex.
  - extend str_mem type to have a "reverse" Boolean flag where regexes are interpreted in a live_states graph that was obtained by reversing a regex.
  - have reversal be decided by the live_states layer to not have it controlled at this level.

  - add regex display function to seq_util that displays regex in resharper format. Easier to read. Use this for display function here.

--*/
#include "ast/seq/seq_mem_facet.h"
#include "ast/ast_pp.h"
#include <algorithm>

namespace seq {

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

    void mem_facet::replace(unsigned idx, expr_ref_vector const& new_str, eq_tree::dep_tracker dep) {
        SASSERT(idx < m_mems.size());
        m_trail.push(vector_field_trail<str_mem, expr_ref_vector>(m_mems, idx, &str_mem::m_str));
        m_mems[idx].m_str.reset();
        m_mems[idx].m_str.append(new_str);
        if (dep) {
            m_trail.push(vector_field_trail<str_mem, eq_tree::dep_tracker>(m_mems, idx, &str_mem::m_dep));
            m_mems[idx].m_dep = m_dm.mk_join(m_mems[idx].m_dep, dep);
        }
    }

    void mem_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        for (unsigned i = 0; i < m_mems.size(); ++i) {
            bool touched = subst_in_trailed(m_trail, m_mems, i, &str_mem::m_str, var, repl);
            if (touched && subst_dep) {
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
            unsigned mh = sm.m_view.key().state;
            for (expr* t : sm.m_str)
                mh = combine_hash(mh, t->get_id());
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
        std::sort(a.begin(), a.end());
        std::sort(b.begin(), b.end());
        for (unsigned i = 0; i < a.size(); ++i)
            if (!(a[i] == b[i]))
                return false;
        return true;
    }

    std::ostream& mem_facet::display(std::ostream& out) const {
        out << "mem_facet: " << m_mems.size() << " membership(s)\n";
        for (auto const& sm : m_mems) {
            out << "  ";
            for (expr* t : sm.m_str)
                out << mk_pp(t, m) << " ";
            out << "in state " << mk_pp(sm.m_view.m_state, m);
            if (sm.m_view.is_reach())
                out << " -> " << mk_pp(sm.m_view.m_target, m);
            out << "\n";
        }
        return out;
    }

    // NSB code review: also strip units from back for membership constraints.
    // you can do this by reversing regex, take derivative and reverse result. 
    // derivative itself can be an if-then-else tree with predicates on characters.
    // we have to handle it by separately splitting on if-then-else for membership constraints
    // membership regexes that are if-then-else should not be propagated on. So disable propagation for those.
    // hoist the ite patterns.
    // consider if co-factor code in ast/rewriter directory already does this.
    stx::simplify_result mem_propagation::propagate(eq_tree::node& n) {
        auto& f = get_ambient(n).mem_facet_ref();
        bool changed = false;
        m_stats.m_num_propagate++;
        for (unsigned i = 0; i < f.memberships().size(); ) {
            auto const& sm = f.memberships()[i];
            expr_ref cur(sm.m_view.m_state, m_rw.m());
            bool bad = false;
            for (expr* t : sm.m_str) {
                if (!u.str.is_unit(t)) { bad = true; break; }
                expr* elem = nullptr;
                VERIFY(u.str.is_unit(t, elem));
                cur = m_rw.mk_derivative(elem, cur);
                if (u.re.is_empty(cur)) {
                    n.set_conflict(stx::br_plugin_base, sm.m_dep);
                    return stx::simplify_result::conflict;
                }
                // NSB code review: 
                // sm.m_str should be updated now to not contain prefix/suffix of units
            }
            // string was all characters
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
            auto live = m_live.reachable_live(sm.m_view.m_state);
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


    // NSB code review: what is this for?
    // it should be removed? It splits x = epsilon | x = x'
    // but then x' can be split again.
    bool mem_var_split::iterator::next(eq_tree::edge& out) {
        if (m_done)
            return false;
        m_done = true;
        auto ac = get_ambient(m_n);
        auto& eq = ac.eq_facet_ref();
        expr_ref_vector repl(eq.get_manager());
        expr* fresh = eq.mk_fresh_var(m_var->get_sort());
        repl.push_back(fresh);
        broadcast_subst(m_n, m_var, repl, m_dep);
        out = eq_tree::edge("mem-v:=v'", nullptr, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> mem_var_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        if (!ac.has_eq())
            return nullptr;
        auto& mf = ac.mem_facet_ref();
        for (unsigned i = 0; i < mf.memberships().size(); ++i) {
            auto const& ts = mf.memberships()[i].m_str;
            if (ts.empty() || u.str.is_unit(ts.get(0)))
                continue;
            expr* var = ts.get(0);
            eq_tree::dep_tracker dep = mf.memberships()[i].m_dep;
            iterator* it = alloc(iterator, n, i, var, m, u, dep);
            auto& eq = ac.eq_facet_ref();
            expr_ref_vector empty(eq.get_manager());
            broadcast_subst(n, var, empty, dep);
            out = eq_tree::edge("mem-v:=eps", nullptr, true, 0);
            committed = true;
            m_stats.m_num_splits++;
            return it;
        }
        return nullptr;
    }

    // NSB code review: this uses the end-game version of seq_monadic. 
    mem_monadic_split::iterator::iterator(eq_tree::node& n, seq_rewriter& rw, trail_stack& trail, ast_manager& m, seq_util& u,
                                          vector<str_mem> const& mems) :
        m_n(n), m_mon(rw, trail, transition_mode::brzozowski_tm), m_it(m_mon.iterate(64)), m(m), u(u) {
        m_mon.set_gen_solution(true);
        for (auto const& sm : mems) {
            // NSB code review: the sort* s can be obtained from sm.m_view.source regex. 
            sort* s = sm.m_str.empty() ? u.str.mk_string_sort() : sm.m_str.get(0)->get_sort();
            expr_ref term(u.str.mk_concat(sm.m_str.size(), sm.m_str.data(), s), m);
            m_mon.add(term, sm.m_view.m_state, sm.m_dep);
        }
        obj_map<expr, seq::view_vector> first;
        if (m_it.next(first))
            for (auto const& [var, views] : first)
                m_first.insert(var, views);
    }

    bool mem_monadic_split::iterator::apply_solution(obj_map<expr, seq::view_vector>& sol, eq_tree::edge& out) {
        auto& mf = get_ambient(m_n).mem_facet_ref();
        bool changed = false;
        for (unsigned i = 0; i < mf.memberships().size(); ++i) {
            auto const& sm = mf.memberships()[i];
             // NSB code review: the sort* s can be obtained from sm.m_view.source regex. 
            sort* s = sm.m_str.empty() ? u.str.mk_string_sort() : sm.m_str.get(0)->get_sort();
            expr_ref term(u.str.mk_concat(sm.m_str.size(), sm.m_str.data(), s), m);
            seq::view_vector views;
            if (!sol.find(term, views) || views.empty())
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
            auto const& ts = sm.m_str;
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

        auto ac = get_ambient(m_n);
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

        expr_ref_vector const& ts = mf.memberships()[m_mem_idx].m_str;
        SASSERT(!ts.empty());
        expr_ref_vector s_units(m);
        u.str.get_concat_units(p.m_s.get(), s_units);
        expr_ref_vector new_ts(m);
        if (m_fwd) {
            new_ts.append(s_units);
            new_ts.push_back(nested_pow.get());
            for (unsigned i = 1; i < ts.size(); ++i)
                new_ts.push_back(ts.get(i));
        }
        else {
            for (unsigned i = 0; i + 1 < ts.size(); ++i)
                new_ts.push_back(ts.get(i));
            new_ts.push_back(nested_pow.get());
            new_ts.append(s_units);
        }

        mf.replace(m_mem_idx, new_ts, m_dep);
        af.add_constraint(a.mk_ge(exp_n, a.mk_int(1)), m_dep);
        f.remove(m_pow_idx);

        out = eq_tree::edge("power-var-peel-mem:n>=1", m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_var_peel_mem::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
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

        // Branch 1 (first, immediately materialized): n = 0, replace
        // U^n with epsilon (progress). c3's mem-variant asserts a
        // single `n = 0` clause (not the eq-variant's `n>=0 /\ n<=0`
        // pair) - preserved faithfully per rule variant.
        expr_ref_vector ts(mf.memberships()[mem_idx].m_str);
        SASSERT(!ts.empty());
        unsigned drop = fwd ? 0 : ts.size() - 1;
        ts.erase(drop);
        mf.replace(mem_idx, ts, dep);
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
        auto& mf = get_ambient(n).mem_facet_ref();
        if (mf.memberships().empty())
            return nullptr;
        bool has_multi = false;
        for (auto const& sm : mf.memberships()) {
            unsigned vars = 0;
            for (expr* t : sm.m_str)
                if (!u.str.is_unit(t))
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
