/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_mem_facet.cpp

Abstract:

    See seq_mem_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/rewriter/seq_mem_facet.h"
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

        void broadcast_subst(eq_tree::node& target, stx::facet_id src_id, expr* var, expr_ref_vector const& repl) {
            for (unsigned id = 0; id < target.num_facets(); ++id) {
                if (id == src_id || !target.has_facet(id))
                    continue;
                if (auto* sink = dynamic_cast<subst_sink_i*>(&target.facet(id)))
                    sink->apply_subst(var, repl);
            }
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

    void mem_facet::apply_subst(expr* var, expr_ref_vector const& repl) {
        expr_ref replacement(m);
        flatten_to_expr(u, repl, replacement);
        for (unsigned i = 0; i < m_mems.size(); ++i) {
            if (m_mems[i].m_str.get() != var)
                continue;
            m_trail.push(vector_field_trail<str_mem, expr_ref>(m_mems, i, &str_mem::m_str));
            m_mems[i].m_str = replacement;
        }
    }

    stx::facet_i* mem_facet::clone(trail_stack& trail) const {
        mem_facet* f = alloc(mem_facet, trail, m, u);
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

    stx::simplify_result mem_propagation::propagate(eq_tree::node& n) {
        auto& f = n.facet_as<mem_facet>(m_mem_id);
        bool changed = false;
        for (unsigned i = 0; i < f.memberships().size(); ) {
            auto const& sm = f.memberships()[i];
            expr_ref cur(sm.m_view.m_state, m_rw.m());
            expr_ref_vector ts(m);
            flatten(u, sm.m_str.get(), ts);
            bool bad = false;
            for (expr* t : ts) {
                if (!is_const_token(u, t)) { bad = true; break; }
                zstring z;
                VERIFY(u.str.is_string(t, z) && z.length() == 1);
                expr_ref elem(u.str.mk_char(z, 0), m_rw.m());
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
        auto& eq = m_n.facet_as<eq_facet>(m_eq_id);
        expr_ref_vector repl(eq.get_manager());
        expr* fresh = eq.mk_fresh_var(m_var->get_sort());
        repl.push_back(fresh);
        eq.apply_subst(m_var, repl);
        broadcast_subst(m_n, m_eq_id, m_var, repl);
        out = eq_tree::edge("mem-v:=v'", nullptr, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> mem_var_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (cost != 0 || !n.has_facet(m_eq_id))
            return nullptr;
        auto& mf = n.facet_as<mem_facet>(m_mem_id);
        for (unsigned i = 0; i < mf.memberships().size(); ++i) {
            expr* s = mf.memberships()[i].m_str.get();
            expr_ref_vector ts(m);
            flatten(u, s, ts);
            if (ts.empty() || is_const_token(u, ts.get(0)))
                continue;
            expr* var = ts.get(0);
            iterator* it = alloc(iterator, n, m_mem_id, m_eq_id, i, var);
            auto& eq = n.facet_as<eq_facet>(m_eq_id);
            expr_ref_vector empty(eq.get_manager());
            eq.apply_subst(var, empty);
            broadcast_subst(n, m_eq_id, var, empty);
            out = eq_tree::edge("mem-v:=eps", nullptr, true, 0);
            committed = true;
            return it;
        }
        return nullptr;
    }

    mem_monadic_split::iterator::iterator(eq_tree::node& n, stx::facet_id mem_id, seq_rewriter& rw, trail_stack& trail,
                                          vector<str_mem> const& mems) :
        m_n(n), m_mem_id(mem_id), m_mon(rw, trail, transition_mode::brzozowski_tm), m_it(m_mon.iterate(64)) {
        m_mon.set_gen_solution(true);
        for (auto const& sm : mems)
            m_mon.add(sm.m_str.get(), sm.m_view.m_state, sm.m_dep);
        obj_map<expr, seq::view_vector> first;
        if (m_it.next(first))
            for (auto const& [var, views] : first)
                m_first.insert(var, views);
    }

    bool mem_monadic_split::iterator::apply_solution(obj_map<expr, seq::view_vector>& sol, eq_tree::edge& out) {
        auto& mf = m_n.facet_as<mem_facet>(m_mem_id);
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
        auto& mf = n.facet_as<mem_facet>(m_mem_id);
        if (mf.memberships().empty())
            return nullptr;
        bool has_multi = false;
        for (auto const& sm : mf.memberships()) {
            expr_ref_vector ts(m);
            flatten(u, sm.m_str.get(), ts);
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
        scoped_ptr<iterator> it(alloc(iterator, n, m_mem_id, m_rw, m_trail, mf.memberships()));
        if (!it->has_first())
            return nullptr;
        if (!it->next(out))
            return nullptr;
        committed = true;
        has_more = true;
        return it.detach();
    }

}
