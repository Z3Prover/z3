/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_approx.cpp

Abstract:

    Intersection of two concatenations of views.  See seq_eq_approx.h.

Author:

    Clemens Eisenhofer 2026

--*/

#include "ast/rewriter/seq_eq_approx.h"
#include "ast/ast_pp.h"
#include <functional>
#include <unordered_set>
#include <vector>

namespace {
    struct key_hash {
        size_t operator()(std::vector<unsigned> const& k) const {
            uint64_t h = 1469598103934665603ull;
            for (unsigned x : k)
                h = (h ^ x) * 1099511628211ull;
            return static_cast<size_t>(h);
        }
    };
}  // namespace

void seq_eq_approx::add_view(expr* t, seq::view const& v) {
    seq::view_vector& views = m_views.insert_if_not_there(t, seq::view_vector());
    views.push_back(v);
    m_pin.push_back(t);
    m_pin.push_back(v.m_state);
    if (v.m_target)
        m_pin.push_back(v.m_target);
}

void seq_eq_approx::set_views(expr* t, seq::view_vector const& views) {
    m_views.remove(t);
    for (auto const& v : views) {
        add_view(t, v);
    }
}

void seq_eq_approx::unset_views(expr* t) {
    m_views.remove(t);
}

void seq_eq_approx::reset_views() {
    m_views.reset();
    m_pin.reset();
    m_used.reset();
}

seq::view_vector const* seq_eq_approx::get_views(expr* t) const {
    return m_views.contains(t) ? &m_views[t] : nullptr;
}

lbool seq_eq_approx::nullable(expr* r) {
    // the regex info holds nullability whenever the plugin determined it and is never
    // evicted; the symbolic formula is only for the states it leaves open
    lbool i = re().get_info(r).nullable;
    if (i != l_undef)
        return i;
    expr_ref nb = m_rw.is_nullable(r);
    return m.is_true(nb) ? l_true : m.is_false(nb) ? l_false : l_undef;
}

expr_ref_pair_vector const& seq_eq_approx::cofactors(expr* r) {
    return m_rw.get_derive().get_cached_cofactors(m_mode, r);
}

bool seq_eq_approx::out_of_budget() {
    if (m_budget == 0 || !m.inc())
        return true;
    --m_budget;
    return false;
}

void seq_eq_approx::add_segment(expr* r, segments& out) {
    m_pin.push_back(r);
    seq::view_vector views;
    views.push_back(seq::view::membership(r));
    out.push_back(views);
}

void seq_eq_approx::to_segments(expr* t, segments& out) {
    if (u().str.is_empty(t))
        return;
    if (u().str.is_concat(t)) {
        for (auto arg : *to_app(t))
            to_segments(arg, out);
        return;
    }    
    sort* seq_sort = t->get_sort();
    VERIFY(u().is_seq(seq_sort));    
    sort_ref re_sort(re().mk_re(seq_sort), m);

    seq::view_vector views;
    if (m_views.find(t, views)) {
        DEBUG_CODE(all_of(views, [&](seq::view const& v) { return v.m_state && v.m_state->get_sort() == re_sort; }));
        if (!m_used.contains(t))
            m_used.push_back(t);
        out.push_back(views);
        return;
    }


    zstring s;
    if (u().str.is_string(t, s)) {
        if (s.length() > 0)
            add_segment(re().mk_to_re(t), out);
        return;
    }
    expr* elem = nullptr;
    if (u().str.is_unit(t, elem)) {
        // an unknown element is still exactly one element
        add_segment(m.is_value(elem) ? (expr*)re().mk_to_re(t) : (expr*)re().mk_full_char(re_sort), out);
    }
    else 
        add_segment(re().mk_full_seq(re_sort), out);   // a variable, or a term no view describes
}

lbool seq_eq_approx::segment_done(seq::view_vector const& views, ptr_vector<expr> const& states) {
    for (unsigned i = 0; i < views.size(); ++i) {
        if (views[i].m_target) {
            if (states[i] != views[i].m_target)
                return l_false;                // a reach view ends only at its target
        }
        else {
            lbool nb = nullable(states[i]);
            if (nb != l_true)
                return nb;                     // l_false, or undecided
        }
    }
    return l_true;
}

lbool seq_eq_approx::intersect_nonempty(segments const& lhs, segments const& rhs) {
    m_budget = m_max_states;
    if (lhs.empty() && rhs.empty())
        return l_true;                         // both sides are the empty word

    // every view has to be stated over one and the same regex sort, which also gives
    // the element sort the cofactor guards range over
    expr* probe = nullptr;
    for (auto const* side : { &lhs, &rhs }) {
        for (auto const& seg : *side) {
            if (seg.empty())
                return l_undef;
            for (auto const& v : seg) {
                VERIFY(v.m_state);
                if (!probe)
                    probe = v.m_state;
                VERIFY(v.m_state->get_sort() == probe->get_sort());
            }
        }
    }
    sort* seq_sort = nullptr;
    sort* elem_sort = nullptr;
    if (!probe)
        return l_undef;
    VERIFY(u().is_re(probe, seq_sort));
    VERIFY(u().is_seq(seq_sort, elem_sort));    
    expr_ref v0(m.mk_var(0, elem_sort), m);

    // A node is a cursor per side: the segment the side is inside, plus the state each
    // view of that segment has been driven to.  A side that has ended its last segment
    // sits at index size() with no states.
    struct node {
        unsigned l_seg = 0, r_seg = 0;
        ptr_vector<expr> l_st, r_st;
    };
    vector<node> work;
    std::unordered_set<std::vector<unsigned>, key_hash> visited;

    auto enter = [](segments const& side, unsigned seg, ptr_vector<expr>& out) {
        out.reset();
        if (seg < side.size())
            for (auto const& v : side[seg])
                out.push_back(v.m_state);
    };
    auto push = [&](node const& n) {
        std::vector<unsigned> key;
        key.push_back(n.l_seg);
        key.push_back(n.r_seg);
        for (expr* e : n.l_st)
            key.push_back(e->get_id());
        for (expr* e : n.r_st)
            key.push_back(e->get_id());
        if (visited.insert(key).second)
            work.push_back(n);
    };

    node init;
    enter(lhs, 0, init.l_st);
    enter(rhs, 0, init.r_st);
    push(init);

    ptr_vector<expr> cur_l, cur_r;
    svector<expr_ref_pair_vector const*> branches;
    bool bail = false;

    for (unsigned head = 0; head < work.size(); ++head) {
        if (out_of_budget())
            return l_undef;
        ++m_stats.m_states;
        node const n = work[head];             // work grows below; keep a copy
        bool const l_done = n.l_seg == lhs.size();
        bool const r_done = n.r_seg == rhs.size();
        if (l_done && r_done)
            return l_true;

        // epsilon steps: end the current segment on one side and start the next
        if (!l_done) {
            lbool done = segment_done(lhs[n.l_seg], n.l_st);
            if (done == l_undef)
                return l_undef;
            if (done == l_true) {
                node next = n;
                ++next.l_seg;
                enter(lhs, next.l_seg, next.l_st);
                push(next);
            }
        }
        if (!r_done) {
            lbool done = segment_done(rhs[n.r_seg], n.r_st);
            if (done == l_undef)
                return l_undef;
            if (done == l_true) {
                node next = n;
                ++next.r_seg;
                enter(rhs, next.r_seg, next.r_st);
                push(next);
            }
        }
        // a character is read by both sides at once, so one side being done ends it
        if (l_done || r_done)
            continue;

        // character step: every view of both current segments advances together, over the
        // combinations of cofactor branches whose guards have a common element
        branches.reset();
        for (expr* s : n.l_st)
            branches.push_back(&cofactors(s));
        for (expr* s : n.r_st)
            branches.push_back(&cofactors(s));
        cur_l = n.l_st;
        cur_r = n.r_st;
        unsigned const num_l = n.l_st.size();

        std::function<void(unsigned, guard_set const&)> rec =
            [&](unsigned i, guard_set const& acc) {
                if (bail)
                    return;
                if (i == branches.size()) {
                    node next;
                    next.l_seg = n.l_seg;
                    next.r_seg = n.r_seg;
                    next.l_st = cur_l;
                    next.r_st = cur_r;
                    push(next);
                    return;
                }
                for (auto const& [g, t] : *branches[i]) {
                    if (re().is_empty(t))
                        continue;
                    guard_set joint = acc;
                    joint.conjoin(g);
                    lbool ne = joint.eval(nullptr);
                    if (ne == l_undef) {
                        bail = true;
                        return;
                    }
                    if (ne == l_false)
                        continue;
                    if (i < num_l)
                        cur_l[i] = t;
                    else
                        cur_r[i - num_l] = t;
                    rec(i + 1, joint);
                    if (bail)
                        return;
                }
            };

        guard_set top(m, u(), elem_sort, v0, &m_rp_cache);
        rec(0, top);
        if (bail)
            return l_undef;
    }
    return l_false;
}

lbool seq_eq_approx::check(expr* lhs, expr* rhs) {
    ++m_stats.m_checks;
    m_last_result = l_undef;
    m_used.reset();
    m_rp_cache.maybe_reset(1u << 16);
    segments l, r;
    VERIFY(lhs->get_sort() == rhs->get_sort());
    
    to_segments(lhs, l); 
    to_segments(rhs, r);
    m_last_result = intersect_nonempty(l, r);
    if (m_last_result == l_false)
        ++m_stats.m_refuted;
    if (m_last_result == l_undef)
        ++m_stats.m_giveup;
    return m_last_result;
}

lbool seq_eq_approx::check(expr* eq) {
    expr* lhs = nullptr, *rhs = nullptr;
    if (!m.is_eq(eq, lhs, rhs)) {
        ++m_stats.m_unsupported;
        return l_undef;
    }
    return check(lhs, rhs);
}

void seq_eq_approx::collect_statistics(::statistics& st) const {
    st.update("seq eq approx checks", m_stats.m_checks);
    st.update("seq eq approx refuted", m_stats.m_refuted);
    st.update("seq eq approx unsupported", m_stats.m_unsupported);
    st.update("seq eq approx giveup", m_stats.m_giveup);
    st.update("seq eq approx states", m_stats.m_states);
}

std::ostream& seq_eq_approx::display(std::ostream& out) const {
    auto display_expr = [&](expr* e) {
        if (e)
            out << mk_pp(e, m);
        else
            out << "null";
    };

    out << "(seq-eq-approx\n"
        << "  :last-result " << m_last_result << "\n"
        << "  :max-states " << m_max_states << "\n"
        << "  :views (";
    for (auto const& [t, views] : m_views) {
        out << "\n    ";
        display_expr(t);
        for (auto const& v : views) {
            out << "\n      ";
            display_expr(v.m_state);
            if (v.is_reach()) {
                out << " -> ";
                display_expr(v.m_target);
            }
        }
    }
    if (!m_views.empty())
        out << "\n  ";
    out << ")\n  :used (";
    for (expr* t : m_used) {
        out << "\n    ";
        display_expr(t);
    }
    if (!m_used.empty())
        out << "\n  ";
    out << ")\n  :checks " << m_stats.m_checks
        << "\n  :refuted " << m_stats.m_refuted
        << "\n  :unsupported " << m_stats.m_unsupported
        << "\n  :giveup " << m_stats.m_giveup
        << "\n  :states " << m_stats.m_states
        << ")\n";
    return out;
}
