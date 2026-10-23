/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_deriv_graph.cpp

Abstract:

    See seq_deriv_graph.h.

Author:

    Clemens Eisenhofer 2026

--*/

#include "ast/seq/seq_deriv_graph.h"
#include "ast/rewriter/seq_range_collapse.h"
#include "util/rational.h"
#include <algorithm>

namespace seq {

    deriv_graph::deriv_graph(seq_rewriter& rw) :
        m(rw.m()), m_rw(rw), u(rw.u()), m_pin(m), m_rp_cache(m), m_bot(m) {
        m_cuts.insert(0);
    }

    deriv_graph::~deriv_graph() {
        for (auto& kv : m_trans)
            dealloc(kv.m_value);
    }

    void deriv_graph::add_cut(unsigned c) {
        if (c > u.max_char() || m_cuts.count(c))
            return;
        m_cuts.insert(c);
        m_reps_dirty = true;
    }

    unsigned_vector const& deriv_graph::reps() {
        if (m_reps_dirty) {
            m_reps.reset();
            for (unsigned c : m_cuts)
                m_reps.push_back(c);
            m_reps_dirty = false;
        }
        return m_reps;
    }

    void deriv_graph::add_chars(expr* e) {
        if (m_scanned.is_marked(e))
            return;
        m_pin.push_back(e);
        ptr_vector<expr> todo;
        todo.push_back(e);
        while (!todo.empty()) {
            expr* t = todo.back();
            todo.pop_back();
            if (m_scanned.is_marked(t))
                continue;
            m_scanned.mark(t);
            unsigned c;
            zstring s;
            if (u.is_const_char(t, c)) {
                add_cut(c);
                add_cut(c + 1);
            }
            else if (u.str.is_string(t, s)) {
                for (unsigned i = 0; i < s.length(); ++i) {
                    add_cut(s[i]);
                    add_cut(s[i] + 1);
                }
            }
            if (is_app(t))
                for (expr* arg : *to_app(t))
                    todo.push_back(arg);
        }
    }

    void deriv_graph::chars_in_order(expr* e, unsigned_vector& out) {
        expr_mark seen;
        ptr_vector<expr> todo;
        todo.push_back(e);
        auto add = [&](unsigned c) {
            if (!out.contains(c))
                out.push_back(c);
        };
        while (!todo.empty()) {
            expr* t = todo.back();
            todo.pop_back();
            if (seen.is_marked(t))
                continue;
            seen.mark(t);
            unsigned c;
            zstring s;
            if (u.is_const_char(t, c))
                add(c);
            else if (u.str.is_string(t, s))
                for (unsigned i = 0; i < s.length(); ++i)
                    add(s[i]);
            else if (is_app(t))
                for (unsigned i = to_app(t)->get_num_args(); i-- > 0; )
                    todo.push_back(to_app(t)->get_arg(i));
        }
    }

    svector<deriv_graph::tr> const* deriv_graph::trans(expr* r) {
        svector<tr>* t = nullptr;
        if (m_trans.find(r, t))
            return t;
        m_pin.push_back(r);
        sort* seq_sort = nullptr;
        if (u.is_re(r, seq_sort) && u.is_string(seq_sort)) {
            t = alloc(svector<tr>);
            expr_ref v0(m.mk_var(0, u.mk_char_sort()), m);
            for (auto const& [guard, target] : m_rw.get_derive().get_cached_cofactors(transition_mode::brzozowski_tm, r)) {
                if (u.re.is_empty(target))
                    continue;
                range_predicate pred(u.max_char());
                if (!guard_to_range_predicate(u, v0, guard, pred)) {
                    dealloc(t);
                    t = nullptr;
                    break;
                }
                m_pin.push_back(target);
                for (auto const& [lo, hi] : pred.ranges()) {
                    t->push_back({ lo, hi, target });
                    add_cut(lo);
                    add_cut(hi + 1);
                }
            }
        }
        m_trans.insert(r, t);
        return t;
    }

    expr* deriv_graph::step(expr* r, unsigned c) {
        auto const* t = trans(r);
        if (!t)
            return nullptr;
        for (auto const& x : *t)
            if (x.lo <= c && c <= x.hi)
                return x.target;
        if (!m_bot || m_bot->get_sort() != r->get_sort())
            m_bot = u.re.mk_empty(r->get_sort());
        return m_bot;
    }

    bool deriv_graph::successors(expr* r, vector<std::pair<expr*, range_predicate>>& out) {
        auto const* t = trans(r);
        if (!t)
            return false;
        for (auto const& x : *t) {
            range_predicate c = range_predicate::range(x.lo, x.hi, u.max_char());
            auto it = std::find_if(out.begin(), out.end(), [&](auto const& e) { return e.first == x.target; });
            if (it == out.end())
                out.push_back({ x.target, c });
            else
                it->second = it->second | c;
        }
        return true;
    }

    ptr_vector<expr> const& deriv_graph::out(expr* p) {
        static ptr_vector<expr> const empty;
        unsigned i;
        return m_idx.find(p, i) ? m_out[i] : empty;
    }

    void deriv_graph::record(expr* p, expr* q) {
        if (m_edges.contains(std::make_pair(p, q)))
            return;
        pin(p);
        pin(q);
        m_edges.insert(std::make_pair(p, q));
        unsigned i;
        if (!m_idx.find(p, i)) {
            i = m_out.size();
            m_idx.insert(p, i);
            m_out.push_back(ptr_vector<expr>());
        }
        m_out[i].push_back(q);
    }

    void deriv_graph::explore(expr* r, unsigned budget) {
        // eagerly only once per region: what an earlier exploration reached grows lazily
        if (m_explored.contains(r))
            return;
        ptr_vector<expr> todo;
        obj_hashtable<expr> seen;
        todo.push_back(r);
        seen.insert(r);
        for (unsigned i = 0; i < todo.size(); ++i) {
            expr* p = todo[i];
            if (!m_expanded.contains(p)) {
                if (budget == 0)
                    continue;
                --budget;
                auto const* t = trans(p);
                if (!t)
                    continue;
                m_expanded.insert(p);
                for (auto const& x : *t)
                    record(p, x.target);
            }
            for (expr* q : out(p))
                if (!seen.contains(q)) {
                    seen.insert(q);
                    todo.push_back(q);
                }
        }
        for (expr* p : todo) {
            pin(p);
            m_explored.insert(p);
        }
    }

    bool deriv_graph::on_cycle(expr* r) {
        ptr_vector<expr> todo;
        obj_hashtable<expr> seen;
        todo.append(out(r));
        while (!todo.empty()) {
            expr* p = todo.back();
            todo.pop_back();
            if (p == r)
                return true;
            if (seen.contains(p))
                continue;
            seen.insert(p);
            todo.append(out(p));
        }
        return false;
    }

    region const* deriv_graph::mk_region(ptr_vector<expr> const& states) {
        std::vector<unsigned> ids;
        for (expr* s : states)
            ids.push_back(s->get_id());
        std::sort(ids.begin(), ids.end());
        auto it = m_region_ids.find(ids);
        if (it != m_region_ids.end())
            return it->second;
        region* q = alloc(region);
        q->m_id = m_regions.size();
        for (unsigned id : ids)
            q->m_ids.push_back(id);
        q->m_states.append(states);
        m_pin.append(states.size(), (expr* const*)states.data());
        m_regions.push_back(q);
        m_region_ids[ids] = q;
        return q;
    }

    region const* deriv_graph::reach_region(expr* r) {
        ptr_vector<expr> todo;
        obj_hashtable<expr> seen;
        todo.push_back(r);
        seen.insert(r);
        for (unsigned i = 0; i < todo.size(); ++i)
            for (expr* q : out(todo[i]))
                if (!seen.contains(q)) {
                    seen.insert(q);
                    todo.push_back(q);
                }
        return mk_region(todo);
    }

    region const* deriv_graph::singleton(expr* r) {
        ptr_vector<expr> s;
        s.push_back(r);
        return mk_region(s);
    }

    void deriv_graph::sweep(region const& q) {
        for (expr* p : q.m_states)
            if (auto const* t = trans(p))
                for (auto const& x : *t)
                    if (q.contains(x.target))
                        record(p, x.target);
    }

    bool deriv_graph::length_info(view const& v, unsigned& d, unsigned& period) {
        region const* q = v.m_gate;
        if (!q || !v.m_target || !q->contains(v.m_state))
            return false;
        obj_map<expr, unsigned> dist;
        ptr_vector<expr> todo;
        todo.push_back(v.m_state);
        dist.insert(v.m_state, 0);
        for (unsigned i = 0; i < todo.size(); ++i) {
            auto const* t = trans(todo[i]);
            if (!t)
                return false;
            unsigned dp = dist[todo[i]];
            for (auto const& x : *t)
                if (q->contains(x.target) && !dist.contains(x.target)) {
                    dist.insert(x.target, dp + 1);
                    todo.push_back(x.target);
                }
        }
        if (!dist.find(v.m_target, d))
            return false;
        rational g(0);
        for (expr* p : todo)
            for (auto const& x : *trans(p))
                if (q->contains(x.target))
                    g = gcd(g, rational(dist[p] + 1 - dist[x.target]));
        period = g.get_unsigned();
        return true;
    }

    lbool deriv_graph::accepts(comp const& c, expr* s) {
        lbool r;
        if (!s || (c.m_view.m_gate && !c.m_view.m_gate->contains(s)))
            r = l_false;
        else if (c.m_view.m_target)
            r = to_lbool(s == c.m_view.m_target);
        else if (!m_nullable.find(s, r)) {
            r = u.re.get_info(s).nullable;
            if (r == l_undef) {
                expr_ref nb = m_rw.is_nullable(s);
                r = m.is_true(nb) ? l_true : m.is_false(nb) ? l_false : l_undef;
            }
            pin(s);
            m_nullable.insert(s, r);
        }
        return c.m_neg ? ~r : r;
    }

    lbool deriv_graph::nonempty(vector<side> const& sides, unsigned budget) {
        std::vector<unsigned>& id = m_key;
        id.clear();
        for (auto const& sd : sides) {
            id.push_back(UINT_MAX);
            for (auto const& t : sd) {
                id.push_back(t.m_is_char ? t.m_char : UINT_MAX - 1);
                for (auto const& c : t.m_comps) {
                    auto k = c.m_view.key();
                    id.push_back(k.state);
                    id.push_back(k.target);
                    id.push_back(k.gate);
                    id.push_back(c.m_neg);
                }
            }
        }
        auto it = m_nonempty_cache.find(id);
        if (it != m_nonempty_cache.end())
            return it->second;
        // a class split while searching may hide a word: search again with the finer classes
        lbool r;
        unsigned num_cuts;
        do {
            num_cuts = m_cuts.size();
            r = nonempty_core(sides, budget);
        }
        while (r == l_false && num_cuts != m_cuts.size());
        if (r != l_undef || m.inc()) {
            m_nonempty_cache[id] = r;
            for (auto const& sd : sides)
                for (auto const& t : sd)
                    for (auto const& c : t.m_comps) {
                        pin(c.m_view.m_state);
                        if (c.m_view.m_target)
                            pin(c.m_view.m_target);
                    }
        }
        return r;
    }

    lbool deriv_graph::nonempty_core(vector<side> const& sides, unsigned budget) {
        struct cfg { unsigned_vector pos; ptr_vector<expr> st; };
        auto init = [&](side const& sd, unsigned p, ptr_vector<expr>& st) {
            if (p < sd.size() && !sd[p].m_is_char)
                for (auto const& c : sd[p].m_comps) {
                    expr* s = c.m_view.m_state;
                    st.push_back(c.m_view.m_gate && !c.m_view.m_gate->contains(s) ? nullptr : s);
                }
        };
        auto width = [&](unsigned k, unsigned p) {
            return p < sides[k].size() && !sides[k][p].m_is_char ? sides[k][p].m_comps.size() : 0;
        };
        vector<cfg> todo;
        key_set seen;
        auto push = [&](cfg const& c) {
            std::vector<unsigned> key(c.pos.begin(), c.pos.end());
            for (expr* s : c.st)
                key.push_back(s ? s->get_id() : UINT_MAX);
            if (seen.insert(key).second)
                todo.push_back(c);
        };
        cfg start;
        for (auto const& sd : sides) {
            start.pos.push_back(0);
            init(sd, 0, start.st);
        }
        push(start);
        bool undef = false;
        unsigned_vector chars(reps());
        for (unsigned qi = 0; qi < todo.size(); ++qi) {
            if (qi >= budget || !m.inc())
                return l_undef;
            cfg cur = todo[qi];
            bool done = true;
            int forced = -1;
            // leave a variable token whose conjunction accepts
            for (unsigned k = 0, off = 0; k < sides.size(); off += width(k, cur.pos[k]), ++k) {
                unsigned p = cur.pos[k];
                if (p == sides[k].size())
                    continue;
                done = false;
                token const& t = sides[k][p];
                if (t.m_is_char) {
                    if (forced >= 0 && (unsigned)forced != t.m_char)
                        forced = -2;
                    else if (forced == -1)
                        forced = t.m_char;
                    continue;
                }
                bool acc = true;
                for (unsigned j = 0; acc && j < t.m_comps.size(); ++j) {
                    lbool a = accepts(t.m_comps[j], cur.st[off + j]);
                    undef |= a == l_undef;
                    acc = a == l_true;
                }
                if (!acc)
                    continue;
                cfg nxt;
                for (unsigned j = 0, o = 0; j < sides.size(); o += width(j, cur.pos[j]), ++j) {
                    if (j == k) {
                        nxt.pos.push_back(p + 1);
                        init(sides[j], p + 1, nxt.st);
                    }
                    else {
                        nxt.pos.push_back(cur.pos[j]);
                        for (unsigned i = 0; i < width(j, cur.pos[j]); ++i)
                            nxt.st.push_back(cur.st[o + i]);
                    }
                }
                push(nxt);
            }
            if (done)
                return l_true;
            if (forced == -2)
                continue;
            unsigned_vector one;
            if (forced >= 0)
                one.push_back(forced);
            for (unsigned c : forced >= 0 ? one : chars) {
                cfg nxt;
                bool alive = true;
                for (unsigned k = 0, off = 0; alive && k < sides.size(); off += width(k, cur.pos[k]), ++k) {
                    unsigned p = cur.pos[k];
                    if (p == sides[k].size()) {
                        alive = false;
                        break;
                    }
                    token const& t = sides[k][p];
                    if (t.m_is_char) {
                        nxt.pos.push_back(p + 1);
                        init(sides[k], p + 1, nxt.st);
                        continue;
                    }
                    nxt.pos.push_back(p);
                    for (unsigned j = 0; j < t.m_comps.size(); ++j) {
                        auto const& cp = t.m_comps[j];
                        expr* s = cur.st[off + j];
                        if (s) {
                            s = step(s, c);
                            if (!s) {
                                undef = true;
                                alive = false;
                                break;
                            }
                            if ((cp.m_view.m_gate && !cp.m_view.m_gate->contains(s)) || (!cp.m_neg && u.re.is_empty(s)))
                                s = nullptr;
                        }
                        if (!s && !cp.m_neg) {
                            alive = false;
                            break;
                        }
                        nxt.st.push_back(s);
                    }
                }
                if (alive)
                    push(nxt);
            }
        }
        return undef ? l_undef : l_false;
    }

}
