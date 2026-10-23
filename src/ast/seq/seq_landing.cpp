/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_landing.cpp

Abstract:

    See seq_landing.h.

Author:

    Clemens Eisenhofer 2026

--*/

#include "ast/seq/seq_landing.h"
#include "ast/rewriter/seq_range_collapse.h"
#include <algorithm>
#include <unordered_set>

namespace seq {

    using comp = deriv_graph::comp;
    using side = deriv_graph::side;
    using succ_vector = vector<std::pair<expr*, range_predicate>>;

    static bool is_landing_view(view const& v) {
        return v.is_membership() || v.is_gated();
    }

    // the primitive constraints on x that deriv_graph can step: plain memberships and gated views
    static void var_comps(mem_facet const& mf, expr* x, vector<comp>& comps, eq_tree::dep_tracker& dep) {
        for (auto const& sm : mf.memberships())
            if (sm.active() && mf.is_single_var_plain(sm) && sm.m_str.get(0) == x && is_landing_view(sm.m_view)) {
                comps.push_back(comp(sm.m_view, false));
                dep = mf.dm().mk_join(dep, sm.m_dep);
            }
    }

    // the over-approximation Omega(ts): each variable is replaced by its primitive constraints
    static void mk_side(mem_facet const& mf, seq_util& u, expr_ref_vector const& ts, side& sd, eq_tree::dep_tracker& dep) {
        for (expr* t : ts) {
            deriv_graph::token tok;
            expr* e = nullptr;
            unsigned c;
            if (u.str.is_unit(t, e) && u.is_const_char(e, c)) {
                tok.m_is_char = true;
                tok.m_char = c;
            }
            else if (u.str.is_unit(t)) {
                expr* full = u.re.mk_full_char(u.re.mk_re(t->get_sort()));
                tok.m_comps.push_back(comp(view::membership(full, u.get_manager()), false));
                var_comps(mf, t, tok.m_comps, dep);
            }
            else if (!u.str.is_power(t))
                var_comps(mf, t, tok.m_comps, dep);
            sd.push_back(tok);
        }
    }

    // the characters a symbolic character token may take under its primitive constraints
    static bool char_class(deriv_graph& g, mem_facet const& mf, seq_util& u, expr* tok, range_predicate& cls, eq_tree::dep_tracker& dep) {
        expr* e = nullptr;
        if (!u.str.is_unit(tok, e) || u.is_const_char(e))
            return false;
        cls = range_predicate::top(u.max_char());
        for (auto const& sm : mf.memberships()) {
            if (!sm.active() || sm.m_str.size() != 1 || sm.m_str.get(0) != tok || !is_landing_view(sm.m_view))
                continue;
            succ_vector succ;
            if (!g.successors(sm.m_view.m_state, succ))
                return false;
            range_predicate allowed = range_predicate::empty(u.max_char());
            for (auto const& [t, chars] : succ) {
                lbool a = g.accepts(sm.m_view, t);
                if (a == l_undef)
                    return false;
                if (a == l_true)
                    allowed = allowed | chars;
            }
            cls = cls & allowed;
            dep = mf.dm().mk_join(dep, sm.m_dep);
        }
        return true;
    }

    // the classes of successors of the view v at state s that a character of cls can reach
    static void live_parts(view const& v, expr* s, range_predicate const& cls, succ_vector const& succ, succ_vector& parts) {
        for (auto const& [t, chars] : succ) {
            if (v.is_gated() && !v.m_gate->contains(t))
                continue;
            range_predicate p = chars & cls;
            if (!p.is_empty())
                parts.push_back({ t, p });
        }
    }

    // a token for one character of cls: the character itself, or a fresh symbolic character
    static expr_ref mk_char_token(eq_tree::node& n, seq_util& u, range_predicate const& cls, sort* seq_sort, eq_tree::dep_tracker dep) {
        auto ac = get_ambient(n);
        auto& mf = ac.mem_facet_ref();
        ast_manager& m = u.get_manager();
        unsigned c;
        if (cls.is_singleton(c))
            return expr_ref(u.str.mk_unit(u.mk_char(c)), m);
        expr_ref ch(m.mk_fresh_const("pa", u.mk_char_sort()), m);
        ac.context().add_fresh(ch);
        expr_ref tok(u.str.mk_unit(ch), m);
        expr_ref_vector ts(m);
        ts.push_back(tok);
        mf.add(str_mem(m, ts, view::membership(range_predicate_to_regex(u, cls, seq_sort), m), dep));
        return tok;
    }

    // refine the character classes by every constant of the memberships, and of the equations
    // when they enter a language test
    static void scan_chars(deriv_graph& g, eq_tree::node& n, bool with_equations) {
        auto ac = get_ambient(n);
        for (auto const& sm : ac.mem_facet_ref().memberships()) {
            if (!sm.active())
                continue;
            for (expr* t : sm.m_str)
                g.add_chars(t);
            g.add_chars(sm.m_view.m_state);
            if (sm.m_view.m_target)
                g.add_chars(sm.m_view.m_target);
        }
        if (!with_equations)
            return;
        for (auto const& eq : ac.eq_facet_ref().equations()) {
            if (!eq.active())
                continue;
            for (expr* t : eq.m_lhs)
                g.add_chars(t);
            for (expr* t : eq.m_rhs)
                g.add_chars(t);
        }
    }

    // run a test only if a membership or equation was added since the last run on this branch
    static bool changed_since(eq_tree::node& n, unsigned& mark) {
        auto ac = get_ambient(n);
        unsigned cur = ac.mem_facet_ref().memberships().size() + ac.eq_facet_ref().equations().size();
        if (cur == mark)
            return false;
        ac.trail().push(value_trail<unsigned>(mark));
        mark = cur;
        return true;
    }

    // ---- landing_propagation ------------------------------------------------------------

    // (Conf): Omega(u) /\ r = {}
    // incrementally: only memberships added since the last test, or whose variables got a new primitive constraint
    bool landing_propagation::conflict(eq_tree::node& n) {
        auto ac = get_ambient(n);
        auto& mf = ac.mem_facet_ref();
        unsigned checked = m_checked, num = mf.memberships().size();
        if (checked == num)
            return false;
        ac.trail().push(value_trail<unsigned>(m_checked));
        m_checked = num;
        scan_chars(m_graph, n, false);
        obj_hashtable<expr> fresh;
        for (unsigned i = checked; i < num; ++i)
            if (mf.memberships()[i].active() && mf.is_single_var_plain(mf.memberships()[i]))
                fresh.insert(mf.memberships()[i].m_str.get(0));
        for (unsigned i = 0; i < num; ++i) {
            auto const& sm = mf.memberships()[i];
            if (!sm.active() || mf.is_single_var_plain(sm) || sm.m_str.empty() || !is_landing_view(sm.m_view))
                continue;
            if (i < checked && !any_of(sm.m_str, [&](expr* t) { return fresh.contains(t); }))
                continue;
            vector<side> sides(2);
            eq_tree::dep_tracker dep = sm.m_dep;
            mk_side(mf, u, sm.m_str, sides[0], dep);
            deriv_graph::token tok;
            tok.m_comps.push_back(comp(sm.m_view, false));
            sides[1].push_back(tok);
            if (m_graph.nonempty(sides, 5000) == l_false) {
                m_stats.m_num_conflicts++;
                n.set_conflict(stx::br_plugin_base, dep);
                return true;
            }
        }
        return false;
    }

    stx::simplify_result landing_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        if (!ac.fparams().m_seq_landing)
            return stx::simplify_result::noop;
        auto& mf = ac.mem_facet_ref();
        bool changed = false;
        unsigned head = m_qhead;
        while (head < mf.memberships().size()) {
            unsigned i = head++;
            str_mem const& sm = mf.memberships()[i];
            if (!sm.active() || !is_landing_view(sm.m_view) || (mf.is_single_var_plain(sm) && u.str.is_unit(sm.m_str.get(0))))
                continue;
            view v = sm.m_view;
            eq_tree::dep_tracker dep = sm.m_dep;
            unsigned origin = sm.m_origin;
            expr_ref_vector str(sm.m_str);
            expr_ref s(v.m_state, m);
            // (Der), over concrete characters and over symbolic ones whose class leads to one state
            unsigned k = 0, c;
            expr* e = nullptr;
            bool dead = false;
            while (k < str.size() && u.str.is_unit(str.get(k), e)) {
                expr* t = nullptr;
                if (u.is_const_char(e, c)) {
                    t = m_graph.step(s, c);
                    if (!t)
                        break;
                    if (u.re.is_empty(t) || (v.is_gated() && !v.m_gate->contains(t)))
                        dead = true;
                }
                else {
                    // only characters this solver introduced: anything else is constrained outside the tree too
                    range_predicate cls;
                    eq_tree::dep_tracker cdep = nullptr;
                    succ_vector succ, parts;
                    if (!mf.is_var_token(str.get(k)) || !char_class(m_graph, mf, u, str.get(k), cls, cdep) || !m_graph.successors(s, succ))
                        break;
                    live_parts(v, s, cls, succ, parts);
                    if (parts.size() > 1)
                        break;              // mem_char_split
                    dep = mf.dm().mk_join(dep, cdep);
                    if (parts.empty())
                        dead = true;
                    else {
                        t = parts[0].first;
                        if (parts[0].second != cls) {
                            expr_ref_vector ts(m);
                            ts.push_back(str.get(k));
                            mf.add(str_mem(m, ts, view::membership(range_predicate_to_regex(u, parts[0].second, str.get(k)->get_sort()), m), dep));
                        }
                    }
                }
                if (dead)
                    break;
                if (!v.is_gated())
                    m_graph.record(s, t);
                s = t;
                ++k;
                m_stats.m_num_steps++;
            }
            if (dead || (v.is_gated() && k == str.size() && s != v.m_target)) {
                n.set_conflict(stx::br_plugin_base, dep);
                return stx::simplify_result::conflict;
            }
            if (v.is_gated() && k == str.size()) {
                mf.remove(i);
                changed = true;
                continue;
            }
            if (k > 0) {
                expr_ref_vector rest(m);
                for (unsigned j = k; j < str.size(); ++j)
                    rest.push_back(str.get(j));
                str_mem nm(m, rest, view(s, v.m_target, v.m_gate, m), dep);
                nm.m_origin = origin;
                mf.remove(i);
                mf.add(nm);
                changed = true;
                continue;
            }
            unsigned d = 0, period = 0;
            bool has_len = v.is_gated() && m_graph.length_info(v, d, period);
            if (has_len && ac.fparams().m_seq_landing_length) {
                auto& sf = ac.solver_facet_ref();
                arith_util& a = sf.get_arith_util();
                expr_ref len(a.mk_int(0), m);
                for (expr* t : str)
                    len = a.mk_add(len, u.str.is_unit(t) ? (expr*)a.mk_int(1) : (expr*)u.str.mk_length(t));
                m_stats.m_num_length++;
                if (period == 0)
                    sf.add_constraint(m.mk_eq(len, a.mk_int(d)), dep);
                else {
                    if (d > 0)
                        sf.add_constraint(a.mk_ge(len, a.mk_int(d)), dep);
                    if (period > 1)
                        sf.add_constraint(m.mk_eq(a.mk_mod(a.mk_sub(len, a.mk_int(d)), a.mk_int(period)), a.mk_int(0)), dep);
                }
            }
        }
        // a variable pinned to {epsilon} is substituted away
        for (unsigned i = m_qhead; i < mf.memberships().size(); ++i) {
            str_mem const& sm = mf.memberships()[i];
            if (!sm.active() || sm.m_str.size() != 1 || !is_uninterp(sm.m_str.get(0)) || !is_landing_view(sm.m_view))
                continue;
            unsigned d = 0, period = 0;
            view const& v = sm.m_view;
            if (v.is_gated() ? m_graph.length_info(v, d, period) && d == 0 && period == 0 : u.re.max_length(v.m_state) == 0) {
                expr_ref x(sm.m_str.get(0), m);
                broadcast_subst(n, x, expr_ref_vector(m), sm.m_dep);
                changed = true;
            }
        }
        if (head != m_qhead) {
            ac.trail().push(value_trail<unsigned>(m_qhead));
            m_qhead = head;
            changed = true;
        }
        if (conflict(n))
            return stx::simplify_result::conflict;
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

    // ---- eq_lang_propagation ------------------------------------------------------------

    stx::simplify_result eq_lang_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        if (!ac.fparams().m_seq_landing || !ac.fparams().m_seq_landing_eq_test || !changed_since(n, m_mark))
            return stx::simplify_result::noop;
        auto& mf = ac.mem_facet_ref();
        scan_chars(m_graph, n, true);
        for (auto const& eq : ac.eq_facet_ref().equations()) {
            if (!eq.active())
                continue;
            vector<side> sides(2);
            eq_tree::dep_tracker dep = eq.m_dep;
            mk_side(mf, u, eq.m_lhs, sides[0], dep);
            mk_side(mf, u, eq.m_rhs, sides[1], dep);
            if (m_graph.nonempty(sides, 5000) == l_false) {
                m_num_conflicts++;
                n.set_conflict(stx::br_plugin_base, dep);
                return stx::simplify_result::conflict;
            }
        }
        return stx::simplify_result::noop;
    }

    // ---- mem_char_split -----------------------------------------------------------------

    bool mem_char_split::iterator::next(eq_tree::edge& out) {
        if (m_pos >= m_parts.size())
            return false;
        auto& mf = get_ambient(m_n).mem_facet_ref();
        expr_ref_vector ts(m);
        ts.push_back(m_tok);
        mf.add(str_mem(m, ts, view::membership(range_predicate_to_regex(u, m_parts[m_pos++], m_tok->get_sort()), m), m_dep));
        out = eq_tree::edge("char-split", m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> mem_char_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        if (!ac.fparams().m_seq_landing)
            return nullptr;
        auto& mf = ac.mem_facet_ref();
        for (auto const& sm : mf.memberships()) {
            if (!sm.active() || mf.is_single_var_plain(sm) || sm.m_str.empty() || !is_landing_view(sm.m_view))
                continue;
            expr* tok = sm.m_str.get(0);
            range_predicate cls;
            eq_tree::dep_tracker dep = sm.m_dep;
            succ_vector succ, parts;
            if (!mf.is_var_token(tok) || !char_class(m_graph, mf, u, tok, cls, dep) || !m_graph.successors(sm.m_view.m_state, succ))
                continue;
            live_parts(sm.m_view, sm.m_view.m_state, cls, succ, parts);
            if (parts.size() < 2)
                continue;
            vector<range_predicate> ps;
            for (auto const& [t, p] : parts)
                ps.push_back(p);
            // the characters leading nowhere are excluded by the membership and the class
            n.add_conflict_dep(dep);
            scoped_ptr<iterator> it(alloc(iterator, n, m, u, tok, dep, ps));
            VERIFY(it->next(out));
            has_more = true;
            committed = true;
            m_num_splits++;
            return it.detach();
        }
        return nullptr;
    }

    // ---- mem_landing_split --------------------------------------------------------------

    // the region a member lands in: a fixed gate, the explored region of a head on a cycle, or {r}
    bool mem_landing_split::mk_member(eq_tree::node& n, member& mb, bool cyclic_only) {
        auto& g = m_graph;
        expr* r = mb.m_view.m_state;
        if (!g.supported(r))
            return false;
        if (mb.m_view.is_gated()) {
            mb.m_gate = mb.m_view.m_gate;
            return true;
        }
        g.explore(r, get_ambient(n).fparams().m_seq_landing_explore);
        bool cyclic = g.on_cycle(r);
        if (cyclic_only && !cyclic)
            return false;
        mb.m_gate = cyclic ? g.reach_region(r) : g.singleton(r);
        if (cyclic)
            g.sweep(*mb.m_gate);
        return true;
    }

    // The frontier partition over the product of the members' regions: the tuples a run can land
    // at without any member leaving its region, and per tuple and character class the escapes where
    // a plain member leaves it.  Classes on which a gated member leaves its gate are refuted.
    bool mem_landing_split::product(vector<member> const& ms, vector<ptr_vector<expr>>& lands, vector<std::pair<ptr_vector<expr>, range_predicate>>& escapes) {
        auto& g = m_graph;
        struct key_hash {
            size_t operator()(std::vector<unsigned> const& k) const {
                uint64_t h = 1469598103934665603ull;
                for (unsigned x : k)
                    h = (h ^ x) * 1099511628211ull;
                return static_cast<size_t>(h);
            }
        };
        std::unordered_set<std::vector<unsigned>, key_hash> seen;
        auto push = [&](ptr_vector<expr> const& t) {
            std::vector<unsigned> k;
            for (expr* e : t)
                k.push_back(e->get_id());
            if (seen.insert(k).second)
                lands.push_back(t);
        };
        ptr_vector<expr> start;
        for (auto const& mb : ms)
            start.push_back(mb.m_view.m_state);
        push(start);
        for (unsigned i = 0; i < lands.size(); ++i) {
            if (lands.size() > m_product_budget || !m.inc())
                return false;
            vector<std::pair<ptr_vector<expr>, range_predicate>> combos;
            combos.push_back({ ptr_vector<expr>(), range_predicate::top(u.max_char()) });
            for (unsigned j = 0; j < ms.size(); ++j) {
                succ_vector succ;
                if (!g.successors(lands[i][j], succ))
                    return false;
                vector<std::pair<ptr_vector<expr>, range_predicate>> next;
                for (auto const& [ts, cs] : combos)
                    for (auto const& [t, chars] : succ) {
                        range_predicate c = cs & chars;
                        if (c.is_empty())
                            continue;
                        next.push_back({ ts, c });
                        next.back().first.push_back(t);
                    }
                combos.swap(next);
                if (combos.size() > m_product_budget)
                    return false;
            }
            for (auto const& [ts, cs] : combos) {
                bool inside = true, dead = false;
                for (unsigned j = 0; j < ms.size(); ++j)
                    if (!ms[j].m_gate->contains(ts[j])) {
                        inside = false;
                        dead |= ms[j].m_view.is_gated();
                    }
                if (inside)
                    push(ts);
                else if (!dead)
                    escapes.push_back({ lands[i], cs });
            }
        }
        return true;
    }

    bool mem_landing_split::mk_branches(eq_tree::node& n, unsigned idx, bool cyclic_only, vector<member>& ms, eq_tree::dep_tracker& dep, vector<branch>& bs) {
        auto ac = get_ambient(n);
        auto& mf = ac.mem_facet_ref();
        auto& g = m_graph;
        str_mem const& sm = mf.memberships()[idx];
        expr* x = sm.m_str.get(0);
        ms.push_back(member(idx, sm));
        if (!g.supported(sm.m_view.m_state))
            return false;

        vector<comp> comps;
        eq_tree::dep_tracker xdep = nullptr;
        var_comps(mf, x, comps, xdep);
        auto with_comps = [&](comp const& extra) {
            vector<side> sides(1);
            deriv_graph::token tok;
            tok.m_comps.append(comps);
            tok.m_comps.push_back(extra);
            sides[0].push_back(tok);
            return g.nonempty(sides, 2000);
        };

        // (Sub): every value allowed for x loops at the head within its region
        if (!comps.empty()) {
            expr* r = sm.m_view.m_state;
            region const* q = sm.m_view.is_gated() ? sm.m_view.m_gate : g.reach_region(r);
            if (with_comps(comp(view::gated(r, r, q, m), true)) == l_false) {
                m_stats.m_num_subsumed++;
                dep = mf.dm().mk_join(sm.m_dep, xdep);
                bs.push_back({ branch::subsume });
                return true;
            }
        }

        if (!mk_member(n, ms[0], cyclic_only))
            return false;
        if (!ms[0].m_view.is_gated() && ms[0].m_gate->m_states.size() == 1 && !g.on_cycle(ms[0].m_view.m_state))
            m_stats.m_num_unwind++;
        // the other memberships x leads land together with it
        for (unsigned j = 0; ac.fparams().m_seq_landing_joint && j < mf.memberships().size(); ++j) {
            str_mem const& sm2 = mf.memberships()[j];
            if (j == idx || !sm2.active() || sm2.m_str.size() < 2 || sm2.m_str.get(0) != x || !is_landing_view(sm2.m_view))
                continue;
            member mb(j, sm2);
            if (mk_member(n, mb, false))
                ms.push_back(mb);
        }

        vector<ptr_vector<expr>> lands;
        vector<std::pair<ptr_vector<expr>, range_predicate>> escapes;
        if (!product(ms, lands, escapes)) {
            if (ms.size() == 1)
                return false;
            ms.shrink(1);
            lands.reset();
            escapes.reset();
            if (!product(ms, lands, escapes))
                return false;
        }
        if (ms.size() > 1)
            m_stats.m_num_joint++;
        dep = nullptr;
        for (auto const& mb : ms)
            dep = mf.dm().mk_join(dep, mf.memberships()[mb.m_idx].m_dep);

        // x = epsilon, and x = one character of each of the first two joint classes of the
        // constraints x leads; characters the constraints mention are tried first
        if (ac.fparams().m_seq_landing_probes && !sm.m_view.is_gated()) {
            bs.push_back({ branch::probe, ptr_vector<expr>(), true });
            unsigned_vector cands;
            for (auto const& sm2 : mf.memberships())
                if (sm2.active() && !sm2.m_str.empty() && sm2.m_str.get(0) == x && is_landing_view(sm2.m_view))
                    g.chars_in_order(sm2.m_view.m_state, cands);
            for (unsigned c : g.reps())
                if (!cands.contains(c))
                    cands.push_back(c);
            vector<range_predicate> seen;
            for (unsigned c : cands) {
                if (seen.size() == 2)
                    break;
                range_predicate part = range_predicate::top(u.max_char());
                bool live = true;
                for (auto const& sm2 : mf.memberships()) {
                    if (!live || !sm2.active() || sm2.m_str.empty() || sm2.m_str.get(0) != x || !is_landing_view(sm2.m_view))
                        continue;
                    succ_vector succ;
                    live = g.successors(sm2.m_view.m_state, succ);
                    auto it = std::find_if(succ.begin(), succ.end(), [&](auto const& e) { return e.second.contains(c); });
                    live = live && it != succ.end() && (!sm2.m_view.is_gated() || sm2.m_view.m_gate->contains(it->first));
                    if (live)
                        part = part & it->second;
                }
                if (live && std::find(seen.begin(), seen.end(), part) == seen.end()) {
                    seen.push_back(part);
                    bs.push_back({ branch::probe, ptr_vector<expr>(), false, part });
                }
            }
        }

        // Land at a tuple only if its pins are compatible with the constraints on x and the
        // constant prefix of every rest can be read from its landing state.  Dropped branches and
        // refuted classes are justified by the members and the constraints on x.
        eq_tree::dep_tracker prune_dep = mf.dm().mk_join(dep, xdep);
        unsigned num_probes = bs.size();
        for (auto const& ts : lands) {
            vector<comp> pins;
            for (unsigned j = 0; j < ms.size(); ++j)
                pins.push_back(comp(view::gated(ms[j].m_view.m_state, ts[j], ms[j].m_gate, m), false));
            if (!comps.empty() || ms.size() > 1) {
                vector<side> sides(1);
                deriv_graph::token tok;
                tok.m_comps.append(comps);
                tok.m_comps.append(pins);
                sides[0].push_back(tok);
                if (g.nonempty(sides, 2000) == l_false)
                    continue;
            }
            // the constant prefix of every member's rest must be readable from its landing state
            bool ok = true;
            for (unsigned j = 0; ok && j < ms.size(); ++j) {
                member const& mb = ms[j];
                unsigned c;
                expr* e = nullptr;
                expr* t = ts[j];
                for (unsigned k = 1; ok && t && k < mb.m_str.size() && u.str.is_unit(mb.m_str.get(k), e) && u.is_const_char(e, c); ++k) {
                    t = g.step(t, c);
                    ok = !t || (!u.re.is_empty(t) && (!mb.m_view.is_gated() || mb.m_gate->contains(t)));
                }
            }
            if (ok)
                bs.push_back({ branch::land, ts });
        }
        // every land branch pruned and no escape left: the members are refuted
        if (bs.size() == num_probes && escapes.empty()) {
            n.set_conflict(stx::br_plugin_base, prune_dep);
            return false;
        }
        n.add_conflict_dep(prune_dep);
        for (auto const& [ps, cs] : escapes)
            bs.push_back({ branch::escape, ps, false, cs });
        return true;
    }

    bool mem_landing_split::iterator::next(eq_tree::edge& out) {
        if (m_pos >= m_branches.size())
            return false;
        branch const& b = m_branches[m_pos++];
        auto& mf = get_ambient(m_n).mem_facet_ref();
        expr* x = m_members[0].m_str.get(0);
        auto rest_of = [&](member const& mb) {
            expr_ref_vector rest(m);
            for (unsigned j = 1; j < mb.m_str.size(); ++j)
                rest.push_back(mb.m_str.get(j));
            return rest;
        };
        switch (b.m_kind) {
        case branch::probe: {
            expr_ref_vector repl(m);
            if (!b.m_eps)
                repl.push_back(mk_char_token(m_n, u, b.m_chars, x->get_sort(), m_dep));
            broadcast_subst(m_n, x, repl, m_dep);
            out = eq_tree::edge("landing-probe", m_dep, true, 0);
            out.set_optional();
            break;
        }
        case branch::subsume: {
            member const& mb = m_members[0];
            str_mem nm(m, rest_of(mb), mb.m_view, m_dep);
            nm.m_origin = mb.m_origin;
            mf.remove(mb.m_idx);
            mf.add(nm);
            out = eq_tree::edge("landing-subsume", m_dep, true, 0);
            break;
        }
        case branch::land: {
            expr_ref_vector xs(m);
            xs.push_back(x);
            for (unsigned j = 0; j < m_members.size(); ++j) {
                member const& mb = m_members[j];
                expr* s = b.m_states[j];
                mf.remove(mb.m_idx);
                mf.add(str_mem(m, xs, view::gated(mb.m_view.m_state, s, mb.m_gate, m), m_dep));
                str_mem nm(m, rest_of(mb), mb.m_view.is_gated() ? view::gated(s, mb.m_view.m_target, mb.m_gate, m) : view::membership(s, m), m_dep);
                nm.m_origin = mb.m_origin;
                mf.add(nm);
            }
            out = eq_tree::edge("landing", m_dep, true, 0);
            break;
        }
        case branch::escape: {
            expr_ref x1(m.mk_fresh_const("pa", x->get_sort()), m), x2(m.mk_fresh_const("pa", x->get_sort()), m);
            for (auto const& mb : m_members)
                mf.remove(mb.m_idx);
            expr_ref a = mk_char_token(m_n, u, b.m_chars, x->get_sort(), m_dep);
            expr_ref_vector repl(m), xs(m);
            repl.push_back(x1);
            repl.push_back(a);
            repl.push_back(x2);
            broadcast_subst(m_n, x, repl, m_dep);
            xs.push_back(x1);
            for (unsigned j = 0; j < m_members.size(); ++j) {
                member const& mb = m_members[j];
                expr* p = b.m_states[j];
                expr_ref_vector rest = rest_of(mb), str(m);
                subst_in(rest, x, repl);
                str.push_back(a);
                str.push_back(x2);
                str.append(rest);
                str_mem nm(m, str, mb.m_view.is_gated() ? view::gated(p, mb.m_view.m_target, mb.m_gate, m) : view::membership(p, m), m_dep);
                nm.m_origin = mb.m_origin;
                mf.add(nm);
                mf.add(str_mem(m, xs, view::gated(mb.m_view.m_state, p, mb.m_gate, m), m_dep));
            }
            out = eq_tree::edge("landing-escape", m_dep, false, 0);
            break;
        }
        }
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> mem_landing_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        if (!ac.fparams().m_seq_landing)
            return nullptr;
        auto& mf = ac.mem_facet_ref();
        scan_chars(m_graph, n, false);
        // land at plain heads on a cycle of G, then at gated heads, and unwind only if neither
        // exists; memberships in the order they were asserted, as rewriting appends them
        unsigned_vector order;
        for (unsigned i = 0; i < mf.memberships().size(); ++i)
            if (mf.memberships()[i].active())
                order.push_back(i);
        std::stable_sort(order.begin(), order.end(), [&](unsigned a, unsigned b) { return mf.memberships()[a].m_origin < mf.memberships()[b].m_origin; });
        unsigned num = order.size();
        for (unsigned k = 0; k < 3 * num; ++k) {
            unsigned i = order[k % num], pass = k / num;
            str_mem const& sm = mf.memberships()[i];
            if (!sm.active() || sm.m_str.size() < 2 || !is_landing_view(sm.m_view) || sm.m_view.is_gated() != (pass == 1))
                continue;
            if (!ac.is_var(sm.m_str.get(0)))
                continue;
            vector<member> ms;
            eq_tree::dep_tracker dep = nullptr;
            vector<branch> bs;
            if (!mk_branches(n, i, pass == 0, ms, dep, bs)) {
                if (n.is_conflict())
                    return nullptr;
                continue;
            }
            scoped_ptr<iterator> it(alloc(iterator, n, m, u, ms, dep, bs));
            VERIFY(it->next(out));
            has_more = true;
            committed = true;
            m_stats.m_num_splits++;
            return it.detach();
        }
        return nullptr;
    }

}
