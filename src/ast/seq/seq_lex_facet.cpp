/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_lex_facet.cpp

Abstract:

    See seq_lex_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

Notes:

    Cycle detection uses an incremental `euf::egraph`, scoped with the
    shared trail. `detect_cycles` registers newly active equations and
    disequations, reports any direct egraph contradiction, then builds a
    DFS graph over egraph roots so semantically equal obligations share a
    node.

--*/
#include "ast/seq/seq_lex_facet.h"
#include "ast/seq/seq_solver_facet_i.h"
#include "ast/ast_pp.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_seq_plugin.h"
#include <algorithm>
#include <functional>

namespace seq {

    lex_facet::lex_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm) :
        facet_i(trail), m(m), u(u), m_dm(dm), m_g(m) {
        m_g.add_plugin(alloc(euf::seq_plugin, m_g));
    }

    void lex_facet::set_sides(unsigned idx, expr_ref_vector const& lhs, expr_ref_vector const& rhs) {
        m_trail.push(vector_field_trail<str_lex, expr_ref_vector>(m_lexs, idx, &str_lex::m_lhs));
        m_trail.push(vector_field_trail<str_lex, expr_ref_vector>(m_lexs, idx, &str_lex::m_rhs));
        m_lexs[idx].m_lhs.reset();
        m_lexs[idx].m_lhs.append(lhs);
        m_lexs[idx].m_rhs.reset();
        m_lexs[idx].m_rhs.append(rhs);
    }

    void lex_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        for (unsigned i = 0; i < m_lexs.size(); ++i) {
            bool touched_l = subst_in_trailed(m_trail, m_lexs, i, &str_lex::m_lhs, var, repl);
            bool touched_r = subst_in_trailed(m_trail, m_lexs, i, &str_lex::m_rhs, var, repl);
            if ((touched_l || touched_r) && subst_dep) {
                m_trail.push(vector_field_trail<str_lex, eq_tree::dep_tracker>(m_lexs, i, &str_lex::m_dep));
                m_lexs[i].m_dep = m_dm.mk_join(m_lexs[i].m_dep, subst_dep);
            }
        }
    }

    stx::facet_i* lex_facet::clone(trail_stack& trail) const {
        lex_facet* f = alloc(lex_facet, trail, m, u, m_dm);
        f->m_lexs.append(m_lexs);
        return f;
    }

    std::ostream& lex_facet::display(std::ostream& out) const {
        out << "lex_facet: " << m_lexs.size() << " obligation(s)\n";
        for (auto const& lx : m_lexs) {
            out << "  [";
            for (expr* t : lx.m_lhs) out << mk_pp(t, m) << " ";
            out << "] " << (lx.m_strict ? "<" : "<=") << " [";
            for (expr* t : lx.m_rhs) out << mk_pp(t, m) << " ";
            out << "]\n";
        }
        return out;
    }

    // Compare two unit tokens carrying constant characters.
    static int cmp_const_chars(seq_util& u, expr* a, expr* b) {
        expr* ca = nullptr, *cb = nullptr;
        VERIFY(u.str.is_unit(a, ca));
        VERIFY(u.str.is_unit(b, cb));
        unsigned na = 0, nb = 0;
        VERIFY(u.is_const_char(ca, na));
        VERIFY(u.is_const_char(cb, nb));
        return na < nb ? -1 : (na == nb ? 0 : 1);
    }

    static bool is_const_char_unit(seq_util& u, expr* tok) {
        expr* c = nullptr;
        return u.str.is_unit(tok, c) && u.is_const_char(c);
    }

    // A token list is guaranteed non-empty only if it contains a unit token.
    static bool contains_unit(seq_util& u, expr_ref_vector const& v) {
        for (expr* t : v)
            if (u.str.is_unit(t))
                return true;
        return false;
    }

    bool lex_facet::simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep) {
        conflict = false;
        conflict_dep = nullptr;
        bool changed = false;
        for (unsigned i = 0; i < m_lexs.size(); ) {
            str_lex& lx = m_lexs[i];
            expr_ref_vector const& L0 = lx.m_lhs;
            expr_ref_vector const& R0 = lx.m_rhs;

            // Strip leading tokens already known equal.
            unsigned li = 0, ri = 0;
            while (li < L0.size() && ri < R0.size()) {
                expr* lh = L0.get(li);
                expr* rh = R0.get(ri);
                bool tok_eq = (lh == rh);
                if (!tok_eq && is_const_char_unit(u, lh) && is_const_char_unit(u, rh))
                    tok_eq = (cmp_const_chars(u, lh, rh) == 0);
                if (!tok_eq)
                    break;
                ++li; ++ri;
            }
            if (li > 0 || ri > 0) {
                expr_ref_vector newL(m), newR(m);
                newL.append(L0.size() - li, L0.data() + li);
                newR.append(R0.size() - ri, R0.data() + ri);
                set_sides(i, newL, newR);
                changed = true;
            }

            expr_ref_vector const& L = m_lexs[i].m_lhs;
            expr_ref_vector const& R = m_lexs[i].m_rhs;

            if (L.empty() && R.empty()) {
                // lhs == rhs: holds iff not strict.
                if (lx.m_strict) {
                    conflict = true;
                    conflict_dep = lx.m_dep;
                    return true;
                }
                remove(i);
                changed = true;
                continue;
            }
            // For a strict comparison, rhs must be provably non-empty.
            if (L.empty() && !R.empty()) {
                if (lx.m_strict && !contains_unit(u, R)) {
                    ++i;
                    continue;
                }
                // lhs is a proper prefix of rhs.
                remove(i);
                changed = true;
                continue;
            }
            // rhs is a proper prefix of lhs only if lhs is provably longer.
            if (!L.empty() && R.empty()) {
                if (!lx.m_strict && !contains_unit(u, L)) {
                    ++i;
                    continue;
                }
                // lhs > rhs, so the obligation fails.
                conflict = true;
                conflict_dep = lx.m_dep;
                return true;
            }
            // Both nonempty, leading tokens neither pointer-equal nor
            // equal constants (else stripped above already).
            expr* lh = L.get(0);
            expr* rh = R.get(0);
            if (is_const_char_unit(u, lh) && is_const_char_unit(u, rh)) {
                // Distinct constants decide the comparison outright.
                int c = cmp_const_chars(u, lh, rh);
                SASSERT(c != 0); // equal case already stripped above
                if (c < 0) {
                    // lhs < rhs.
                    remove(i);
                    changed = true;
                    continue;
                }
                else {
                    // lhs > rhs.
                    conflict = true;
                    conflict_dep = lx.m_dep;
                    return true;
                }
            }
            // Otherwise leave the obligation pending.
            ++i;
        }
        return changed;
    }

    stx::simplify_result lex_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        auto& f = ac.lex_facet_ref();
        bool conflict = false;
        eq_tree::dep_tracker conflict_dep = nullptr;
        m_stats.m_num_propagate++;
        bool changed = f.simplify(conflict, conflict_dep);
        if (conflict) {
            n.set_conflict(stx::br_plugin_base, conflict_dep);
            return stx::simplify_result::conflict;
        }
        if (f.is_satisfied())
            return changed ? stx::simplify_result::satisfied : stx::simplify_result::noop;
        bool cyc_conflict = false;
        eq_tree::dep_tracker cyc_dep = nullptr;
        bool cyc_changed = f.detect_cycles(cyc_conflict, cyc_dep, ac.eq_facet_ref(), ac.deq_facet_ref());
        if (cyc_conflict) {
            n.set_conflict(stx::br_plugin_base, cyc_dep);
            return stx::simplify_result::conflict;
        }
        if (!changed && !cyc_changed)
            return stx::simplify_result::noop;
        return f.is_satisfied() ? stx::simplify_result::satisfied : stx::simplify_result::proceed;
    }

    scoped_ptr<eq_tree::split_iterator_i> lex_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        auto& f = ac.lex_facet_ref();
        if (f.is_satisfied())
            return nullptr;

        str_lex lx = f.lexs()[0];
        scoped_ptr<eq_tree::split_iterator_i> it;
        if (!lx.m_lhs.empty() && !lx.m_rhs.empty())
            it = alloc(iterator, n, lx, m, u);

        sort* s = u.str.mk_string_sort();
        expr_ref lhs(u.str.mk_concat(lx.m_lhs, s), m);
        expr_ref rhs(u.str.mk_concat(lx.m_rhs, s), m);
        expr* tail = ac.mk_fresh_var("lex.tail", s, { lhs, rhs });
        expr_ref_vector prefix(lx.m_lhs);
        prefix.push_back(tail);
        f.remove(0);
        ac.eq_facet_ref().add_equation(lx.m_rhs, prefix, lx.m_dep);
        if (lx.m_strict) {
            auto& sf = ac.solver_facet_ref();
            auto& a = sf.get_arith_util();
            expr_ref len(u.str.mk_length(tail), m);
            expr_ref zero(a.mk_int(0), m);
            sf.add_constraint(a.mk_gt(len, zero), lx.m_dep);
        }
        out = eq_tree::edge("lex prefix", lx.m_dep, true, 0);
        has_more = true;
        committed = true;
        ++m_stats.m_num_splits;
        return it;
    }

    bool lex_split::iterator::next(eq_tree::edge& out) {
        if (m_next_case == 2)
            return false;
        bool at_start = m_next_case++ == 0;
        auto ac = get_ambient(m_n);
        sort* s = u.str.mk_string_sort();
        expr_ref lhs(u.str.mk_concat(m_lhs, s), m);
        expr_ref rhs(u.str.mk_concat(m_rhs, s), m);
        expr_ref prefix(m);
        prefix = at_start ? u.str.mk_empty(s) : ac.mk_fresh_var("lex.prefix", s, { lhs, rhs });
        expr* a = ac.mk_fresh_var("lex.a", u.mk_char_sort(), { lhs, rhs, prefix });
        expr* b = ac.mk_fresh_var("lex.b", u.mk_char_sort(), { lhs, rhs, prefix });
        expr_ref a_unit(u.str.mk_unit(a), m);
        expr_ref b_unit(u.str.mk_unit(b), m);
        expr* lhs_tail = ac.mk_fresh_var("lex.lhs", s, { lhs, rhs, prefix });
        expr* rhs_tail = ac.mk_fresh_var("lex.rhs", s, { lhs, rhs, prefix });
        expr_ref_vector left(m), right(m);
        if (!at_start) {
            left.push_back(prefix);
            right.push_back(prefix);
            auto& sf = ac.solver_facet_ref();
            auto& arith = sf.get_arith_util();
            expr_ref len(u.str.mk_length(prefix), m);
            expr_ref zero(arith.mk_int(0), m);
            sf.add_constraint(arith.mk_gt(len, zero), m_dep);
        }
        left.push_back(a_unit);
        left.push_back(lhs_tail);
        right.push_back(b_unit);
        right.push_back(rhs_tail);
        ac.lex_facet_ref().remove(0);
        ac.eq_facet_ref().add_equation(m_lhs, left, m_dep);
        ac.eq_facet_ref().add_equation(m_rhs, right, m_dep);
        // The arithmetic backend only relaxes character order; the outer
        // character theory must adopt it before accepting this leaf.
        expr_ref less(u.mk_lt(a, b), m);
        ac.add_assumption(less, m_dep);
        out = eq_tree::edge(at_start ? "lex first character" : "lex later difference", m_dep, true, 0);
        return true;
    }

    // Pack/unpack an index into an egraph justification reason pointer.
    static size_t* to_ptr(size_t i) { return reinterpret_cast<size_t*>(i); }
    static unsigned from_ptr(size_t* s) { return (unsigned)reinterpret_cast<size_t>(s); }

    bool lex_facet::sync_egraph(eq_facet& eqf, deq_facet& deqf) {
        bool added = false;

        obj_map<expr, euf::enode*> node_cache;
        std::function<euf::enode*(expr*)> mk_node = [&](expr* e) -> euf::enode* {
            euf::enode* cached = nullptr;
            if (node_cache.find(e, cached))
                return cached;
            if (euf::enode* n = m_g.find(e)) {
                node_cache.insert(e, n);
                return n;
            }
            euf::enode_vector args;
            if (is_app(e))
                for (expr* arg : *to_app(e))
                    args.push_back(mk_node(arg));
            euf::enode* n = m_g.mk(e, 0, args.size(), args.data());
            node_cache.insert(e, n);
            return n;
        };
        auto mk_concat_node = [&](expr_ref_vector const& ts, sort* s) -> euf::enode* {
            expr_ref t(u.str.mk_concat(ts, s), m);
            return mk_node(t);
        };

        // Only the suffix beyond each qhead is new since the last sync.
        vector<eq_facet::equation> const& eqs = eqf.equations();
        for (unsigned i = m_eq_qhead; i < eqs.size(); ++i) {
            eq_facet::equation const& eq = eqs[i];
            if (eq.active() && !(eq.m_lhs.empty() && eq.m_rhs.empty())) {
                sort* s = (eq.m_lhs.empty() ? eq.m_rhs.get(0) : eq.m_lhs.get(0))->get_sort();
                euf::enode* l = mk_concat_node(eq.m_lhs, s);
                euf::enode* r = mk_concat_node(eq.m_rhs, s);
                m_reasons.push_back(eq.m_dep);
                m_trail.push(push_back_trail<eq_tree::dep_tracker>(m_reasons));
                m_g.merge(l, r, to_ptr(m_reasons.size() - 1));
                added = true;
            }
        }
        if (eqs.size() > m_eq_qhead) {
            m_trail.push(value_trail<unsigned>(m_eq_qhead));
            m_eq_qhead = eqs.size();
        }

        vector<deq_facet::disequation> const& des = deqf.disequations();
        for (unsigned i = m_deq_qhead; i < des.size(); ++i) {
            deq_facet::disequation const& de = des[i];
            if (de.active() && !(de.m_lhs.empty() && de.m_rhs.empty())) {
                sort* s = (de.m_lhs.empty() ? de.m_rhs.get(0) : de.m_lhs.get(0))->get_sort();
                euf::enode* l = mk_concat_node(de.m_lhs, s);
                euf::enode* r = mk_concat_node(de.m_rhs, s);
                expr_ref eqe(m.mk_eq(l->get_expr(), r->get_expr()), m);
                euf::enode_vector args;
                args.push_back(l);
                args.push_back(r);
                euf::enode* eqn = m_g.mk(eqe, 0, args.size(), args.data());
                m_reasons.push_back(de.m_dep);
                m_trail.push(push_back_trail<eq_tree::dep_tracker>(m_reasons));
                m_g.new_diseq(eqn, to_ptr(m_reasons.size() - 1));
                added = true;
            }
        }
        if (des.size() > m_deq_qhead) {
            m_trail.push(value_trail<unsigned>(m_deq_qhead));
            m_deq_qhead = des.size();
        }
        return added;
    }

    bool lex_facet::detect_cycles(bool& conflict, eq_tree::dep_tracker& conflict_dep, eq_facet& eqf, deq_facet& deqf) {
        conflict = false;
        conflict_dep = nullptr;

        // New equalities or disequalities may already be contradictory.
        sync_egraph(eqf, deqf);

        obj_map<expr, euf::enode*> node_cache;
        std::function<euf::enode*(expr*)> mk_node = [&](expr* e) -> euf::enode* {
            euf::enode* cached = nullptr;
            if (node_cache.find(e, cached))
                return cached;
            if (euf::enode* n = m_g.find(e)) {
                node_cache.insert(e, n);
                return n;
            }
            euf::enode_vector args;
            if (is_app(e))
                for (expr* arg : *to_app(e))
                    args.push_back(mk_node(arg));
            euf::enode* n = m_g.mk(e, 0, args.size(), args.data());
            node_cache.insert(e, n);
            return n;
        };
        auto mk_concat_node = [&](expr_ref_vector const& ts, sort* s) -> euf::enode* {
            expr_ref t(u.str.mk_concat(ts, s), m);
            return mk_node(t);
        };

        vector<std::pair<euf::enode*, euf::enode*>> nedges;

        // register nodes
        for (unsigned i = 0; i < m_lexs.size(); ++i) {
            str_lex const& lx = m_lexs[i];
            if (lx.m_lhs.empty() && lx.m_rhs.empty())
                continue;
            sort* s = (lx.m_lhs.empty() ? lx.m_rhs.get(0) : lx.m_lhs.get(0))->get_sort();
            auto a = mk_concat_node(lx.m_lhs, s);
            auto b = mk_concat_node(lx.m_rhs, s);
            nedges.push_back({a, b});
        }

        m_g.propagate();
        if (m_g.inconsistent()) {
            // The registered equations and disequations already conflict.
            ptr_vector<size_t> just;
            m_g.begin_explain();
            m_g.explain(just, nullptr);
            m_g.end_explain();
            eq_tree::dep_tracker dep = nullptr;
            for (size_t* j : just)
                dep = m_dm.mk_join(dep, m_reasons[from_ptr(j)]);
            conflict = true;
            conflict_dep = dep;
            return true;
        }

        // No lex obligations produced graph edges.
        if (nedges.empty())
            return false;

        obj_map<expr, unsigned> var_id;
        ptr_vector<expr> vars;
        struct edge { unsigned src, dst; bool strict; unsigned lex_idx; };
        vector<edge> edges;

        // add nodes to graph
        auto get_id = [&](euf::enode* n) {
            expr* root = n->get_root()->get_expr();
            unsigned id;
            if (var_id.find(root, id))
                return id;
            id = vars.size();
            vars.push_back(root);
            var_id.insert(root, id);
            return id;
        };

        for (unsigned i = 0; i < nedges.size(); ++i) {
            auto [l, r] = nedges[i];
            str_lex const& lx = m_lexs[i];
            edges.push_back({ get_id(l), get_id(r), lx.m_strict, i });
        }

        // Build adjacency and look for a cycle, tracking whether any edge is strict.
        vector<vector<unsigned>> adj(vars.size());
        for (unsigned ei = 0; ei < edges.size(); ++ei)
            adj[edges[ei].src].push_back(ei);

        enum class color { white, gray, black };
        vector<color> colors(vars.size(), color::white);
        vector<unsigned> on_path;      // stack of edge indices on current DFS path
        vector<unsigned> path_node;    // stack of node ids on current DFS path

        std::function<bool(unsigned)> dfs = [&](unsigned u_id) -> bool {
            colors[u_id] = color::gray;
            path_node.push_back(u_id);
            for (unsigned ei : adj[u_id]) {
                unsigned v_id = edges[ei].dst;
                on_path.push_back(ei);
                if (colors[v_id] == color::gray) {
                    // Found a cycle: it consists of the suffix of on_path
                    // starting at v_id's first occurrence.
                    unsigned start = 0;
                    while (path_node[start] != v_id) ++start;
                    bool has_strict = false;
                    eq_tree::dep_tracker dep = nullptr;
                    unsigned cycle_len = on_path.size() - start;
                    for (unsigned k = start; k < on_path.size(); ++k) {
                        auto edge_id = on_path[k];
                        edge const& e = edges[edge_id];
                        auto& lx = m_lexs[e.lex_idx];
                        has_strict |= e.strict;
                        dep = m_dm.mk_join(dep, lx.m_dep);
                        // Consecutive obligations may share a root only by
                        // egraph congruence, so explain that equality and
                        // include its dependencies.
                        unsigned next_k = (k + 1 - start) % cycle_len + start;
                        auto next_edge_id = on_path[next_k];
                        auto [l, b] = nedges[edge_id];
                        auto [c, r] = nedges[next_edge_id];
                        (void)l; (void)r;
                        if (b != c) {
                            ptr_vector<size_t> eq_just;
                            m_g.begin_explain();
                            m_g.explain_eq(eq_just, nullptr, b, c);
                            m_g.end_explain();
                            for (size_t* j : eq_just)
                                dep = m_dm.mk_join(dep, m_reasons[from_ptr(j)]);
                        }
                    }
                    if (has_strict) {
                        conflict = true;
                        conflict_dep = dep;
                        return true;
                    }
                    // An all-non-strict cycle forces equality. Re-assert it
                    // as equations and drop the lex obligations.


                    vector<unsigned> to_remove;
                    for (unsigned k = start; k < on_path.size(); ++k)
                        to_remove.push_back(edges[on_path[k]].lex_idx);
                    std::sort(to_remove.begin(), to_remove.end(), std::greater<unsigned>());
                    for (unsigned idx : to_remove) {
                        str_lex const& lx = m_lexs[idx];
                        eqf.add_equation(lx.m_lhs, lx.m_rhs, dep);
                        remove(idx);
                    }
                    return true;
                }
                if (colors[v_id] == color::white && dfs(v_id))
                    return true;
                on_path.pop_back();
            }
            path_node.pop_back();
            colors[u_id] = color::black;
            return false;
        };

        for (unsigned i = 0; i < vars.size(); ++i)
            if (colors[i] == color::white && dfs(i))
                return true;
        return false;
    }

} // namespace seq
