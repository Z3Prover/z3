/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_monadic.cpp

Abstract:

    Whole-language monadic decomposition for regex membership.  See seq_monadic.h.
    Automaton-based (product-reachability); reach(q) is never materialized as a regex, and
    the disjunction produced by the decomposition is never materialized as a DNF: it is
    explored as a depth-first search tree with per-variable emptiness pruning.

    Generic in the element sort.  The decomposition, liveness and product-reachability
    are element-agnostic; only the *guard algebra* over the derivative cofactor guards
    depends on the element sort.  For the character sort it is the exact, compact
    seq::range_predicate; for any other element sort it is a candidate-basis over the
    element values mentioned by the guards (sound and complete for the
    {true,false,=,<=,and,or,not} grammar the derivatives emit).  The same guard algebra
    yields the concrete element used to build a witness sequence.

TODOs:
- create a validation harness: expose certificates for correctness that can be checked.
- take into account shape of terms to prune the search space (e.g., if the term is xax, then retain the effect of 
  intersecting with .*a.*).
- connect to semi-linear pruning, such as xx in (ab)*a is unsat due to parity 
- support units of non-values (element variables).
  Model construction would assign values to the elements.
- make unsat core tracking less naive by tracking dependencies at a finer grain.
- add selective tracing TRACE(seq, ..).
- revisit DFS to select next membership constraint to explore base on the current state.
  In the current state include current set of variable intersection membership constraints.
  The next membership constraint to explore is preferrably for a variable that was just
  explored and we can check the variable intersection membership constraints if the new
  expansion is feasible. Constant characters are consumed at the same time to also prune
  the choice.
- separate out "live-state" and enumerator over reachable live states:
  - make it share live states between callers.
  - make it expose an iterator instead of using vectors of live states to allow on-demand expansion of live states.
  - make use of DFS exploration of derivatives to extract live states without visiting all states up front.
  - use it in seq_regex legacy mode that also has this notion.



Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/

#include "ast/rewriter/seq_monadic.h"
#include "ast/rewriter/guard_set.h"
#include "ast/rewriter/seq_range_collapse.h"
#include <set>
#include <vector>
#include <map>
#include <tuple>
#include <functional>
#include <algorithm>
#include <unordered_set>

namespace {
    char const* mode_name(seq::transition_mode mode) {
        switch (mode) {
        case seq::transition_mode::brzozowski_tm:
            return "brzozowski";
        case seq::transition_mode::light_antimirov_tm:
            return "light-antimirov";
        }
        return "unknown";
    }

    char const* bail_name(unsigned i) {
        static char const* const names[] = {
            "unsupported",
            "state-cap",
            "dnf-cap",
            "budget",
            "resource",
            "nullability",
            "guard"
        };
        return i < std::size(names) ? names[i] : "unknown";
    }

    char const* result_name(lbool r) {
        switch (r) {
        case l_true:  return "sat";
        case l_false: return "unsat";
        default:      return "unknown";
        }
    }
}


expr_ref seq_monadic::der_elem(expr* r, expr* elem) {
    expr* cached = nullptr;
    if (m_der_cache.find(r, elem, cached))
        return expr_ref(cached, m);
    expr_ref d = m_rw.mk_derivative(elem, r);   // mk_derivative(element, regex)
    // Normalize: for a general element sort the derivative by a non-matching constant can
    // leave a ground guard (e.g. (= 1 2)) unfolded; simplifying collapses such dead
    // branches to re.empty so nullability/emptiness stay decidable.
    expr_ref d2(m);
    m_thrw(d, d2);
    m_pin.push_back(r);                        // keep the cache keys and value alive
    m_pin.push_back(elem);
    m_pin.push_back(d2);
    m_der_cache.insert(r, elem, d2);
    return d2;
}

lbool seq_monadic::nullable(expr* r) {
    // Nullability is a structural property, and the seq plugin already computes it as
    // part of the regex info -- cached by expr id and, unlike seq_rewriter's op_cache
    // (capped at 10000 and flushed whole), never evicted.  Use it whenever it is
    // determined; only fall back to building the symbolic nullability formula for the
    // regexes whose info leaves it undetermined.
    lbool i = re().get_info(r).nullable;
    if (i != l_undef)
        return i;
    char v = 0;
    if (m_nullable_cache.find(r, v)) {
        if (v == 1) return l_true;
        if (v == 0) return l_false;
        return l_undef;
    }
    expr_ref nb = m_rw.is_nullable(r);
    lbool res = m.is_true(nb) ? l_true : m.is_false(nb) ? l_false : l_undef;
    m_pin.push_back(r);
    m_nullable_cache.insert(r, res == l_true ? 1 : res == l_false ? 0 : 2);
    return res;
}

expr_ref_pair_vector const& seq_monadic::derivative_cofactors(expr* r) {
    ++m_stats.m_cofactor_calls;
    return m_rw.get_derive().get_cached_cofactors(m_config.m_mode, r);
}

void seq_monadic::reset_ivl_cache() {
    for (auto& kv : m_ivl_cache)
        dealloc(kv.m_value);
    m_ivl_cache.reset();
    m_ivl_pin.reset();
}

// Canonical interval form of r's derivative: the cofactor guards, translated into the
// range algebra, refined into a sorted list of disjoint ranges, each labelled with the
// targets reachable on it.  Adjacent ranges with identical target sets are merged, so the
// result is the minimal ordered-ITE ("t-regex") representation of the transition relation.
// Returns null when some guard falls outside the range algebra.
seq_monadic::ivl_list const* seq_monadic::interval_cofactors(expr* r, expr* v0) {
    ivl_list* res = nullptr;
    if (m_ivl_cache.find(r, res))
        return res && res->ok ? res : nullptr;

    unsigned max_char = u().max_char();
    res = alloc(ivl_list);
    m_ivl_cache.insert(r, res);
    m_ivl_pin.push_back(r);

    // (lo, hi, target) triples, plus the boundary set of this state's own partition.
    struct tr_t { unsigned lo, hi; expr* t; };
    svector<tr_t> tr;
    svector<unsigned> bounds;
    bounds.push_back(0);
    for (auto const& [g, t] : derivative_cofactors(r)) {
        if (re().is_empty(t))
            continue;
        seq::range_predicate* p = nullptr;
        if (!m_rp_cache.find(g, p)) {
            p = m_rp_cache.fresh(max_char);
            if (!seq::guard_to_range_predicate(u(), v0, g, *p)) {
                m_rp_cache.insert(g, nullptr);
                res->ok = false;
                return nullptr;
            }
            m_rp_cache.insert(g, p);
        }
        else if (!p) {
            res->ok = false;
            return nullptr;
        }
        m_ivl_pin.push_back(t);
        for (auto const& rg : p->ranges()) {
            tr.push_back({ rg.first, rg.second, t });
            bounds.push_back(rg.first);
            if (rg.second < max_char)
                bounds.push_back(rg.second + 1);
        }
    }
    if (tr.empty())
        return res;                            // dead state: no outgoing transition

    std::sort(bounds.begin(), bounds.end());
    bounds.shrink((unsigned)(std::unique(bounds.begin(), bounds.end()) - bounds.begin()));

    ptr_vector<expr> hits;
    for (unsigned bi = 0; bi < bounds.size(); ++bi) {
        unsigned lo = bounds[bi];
        unsigned hi = bi + 1 < bounds.size() ? bounds[bi + 1] - 1 : max_char;
        hits.reset();
        for (auto const& e : tr)
            if (e.lo <= lo && lo <= e.hi)
                hits.push_back(e.t);
        if (hits.empty())
            continue;                          // gap: no transition on this range
        // extend the previous range when it carries exactly the same target set
        if (!res->ranges.empty()) {
            ivl_range& prev = res->ranges.back();
            if (prev.hi + 1 == lo && prev.count == hits.size()) {
                bool same = true;
                for (unsigned k = 0; k < hits.size() && same; ++k)
                    same = res->targets[prev.first + k] == hits[k];
                if (same) {
                    prev.hi = hi;
                    continue;
                }
            }
        }
        res->ranges.push_back({ lo, hi, res->targets.size(), hits.size() });
        res->targets.append(hits.size(), hits.data());
    }
    return res;
}

lbool seq_monadic::product_nonempty(svector<component> const& comps, expr_ref* witness_word) {
    unsigned n = comps.size();
    if (n == 0) {
        if (witness_word)
            *witness_word = expr_ref(u().str.mk_empty(m_seq_sort), m);
        return l_true;
    }
    expr_ref var0(m.mk_var(0, m_elem_sort), m);   // the element variable the guards range over

    typedef std::vector<unsigned> key;
    struct key_hash {
        size_t operator()(key const& k) const {
            size_t h = 1469598103934665603ull;
            for (unsigned x : k)
                h = (h ^ x) * 1099511628211ull;
            return h;
        }
    };

    // Product states are held in a flat stack of stride n; `visited` owns one copy of the
    // id-tuple of every discovered state.  Both avoid a per-state heap allocation, which
    // dominated the search when this ran per derivative step of the outer decomposition.
    ptr_vector<expr> work;
    std::unordered_set<key, key_hash> visited;
    key kbuf;
    kbuf.resize(n);

    ptr_vector<expr> st;
    st.resize(n);
    ptr_vector<expr> cur;
    cur.resize(n);

    auto fill_key = [&](ptr_vector<expr> const& s) -> key const& {
        for (unsigned i = 0; i < n; ++i)
            kbuf[i] = s[i]->get_id();
        return kbuf;
    };

    bool undecided = false;
    auto is_accept = [&]() -> bool {
        for (unsigned i = 0; i < n; ++i) {
            if (comps[i].target) {
                if (st[i] != comps[i].target) return false;
            }
            else {
                lbool nb = nullable(st[i]);
                if (nb == l_true) continue;
                if (nb == l_false) return false;
                undecided = true; return false;
            }
        }
        return true;
    };

    // tree of first-discovery edges for witness reconstruction (only built when a
    // witness is requested): child-key -> (parent-key, element read on the edge).
    std::map<key, std::pair<key, expr*>> parent;
    key start_key;
    start_key.resize(n);
    for (unsigned i = 0; i < n; ++i) {
        work.push_back(comps[i].state);
        start_key[i] = comps[i].state->get_id();
    }
    visited.insert(start_key);

    auto reconstruct = [&](key end_key) -> expr_ref {
        ptr_vector<expr> elems;              // collected in accept..start order
        key k = end_key;
        while (k != start_key) {
            auto it = parent.find(k);
            if (it == parent.end()) break;   // safety (should not happen)
            elems.push_back(it->second.second);
            k = it->second.first;
        }
        expr_ref_vector es(m);               // start..accept order
        for (unsigned idx = elems.size(); idx-- > 0; )
            es.push_back(u().str.mk_unit(elems[idx]));
        if (es.empty())
            return expr_ref(u().str.mk_empty(m_seq_sort), m);
        return expr_ref(u().str.mk_concat(es.size(), es.data(), m_seq_sort), m);
    };

    // Hoisted out of the search loop: the per-component cofactor vectors are owned by the
    // cofactor cache and stay valid for the whole search, so they are referenced rather
    // than copied (copying re-materialized every branch as expr_ref pairs on every pop).
    svector<expr_ref_pair_vector const*> branches;
    branches.resize(n);
    key st_key;
    bool bail = false;

    // ---- interval-refinement ("t-regex merge") product --------------------------
    // Over the character sort every cofactor guard denotes a union of ranges, so each
    // component's derivative has a canonical ordered-interval ("t-regex") form, cached
    // per state by interval_cofactors.  The joint transitions are then exactly the cells
    // of the common refinement of those n interval lists, obtained by a cursor merge in
    // O(sum_i intervals_i) -- whereas the cartesian enumeration below tries
    // prod_i(k_i) combinations, almost all of which are pruned as empty.
    bool const sweep_ok = u().is_char(m_elem_sort);
    unsigned const max_char = sweep_ok ? u().max_char() : 0;
    svector<ivl_list const*> sw_lists;
    svector<unsigned> sw_cur, sw_odo;
    sw_lists.resize(n);
    sw_cur.resize(n);
    sw_odo.resize(n);

    // Returns false when some guard falls outside the range algebra, in which case the
    // caller falls back to the cartesian enumeration for this product state.
    auto sweep = [&]() -> bool {
        for (unsigned i = 0; i < n; ++i) {
            sw_lists[i] = interval_cofactors(st[i], var0);
            if (!sw_lists[i])
                return false;
            if (sw_lists[i]->ranges.empty())
                return true;                  // component is stuck: no joint transition
            sw_cur[i] = 0;
        }
        uint64_t b = 0;
        while (b <= max_char) {
            uint64_t next = (uint64_t)max_char + 1;
            bool covered = true, done = false;
            for (unsigned i = 0; i < n; ++i) {
                auto const& rs = sw_lists[i]->ranges;
                unsigned& c = sw_cur[i];
                while (c < rs.size() && rs[c].hi < b)
                    ++c;
                if (c == rs.size()) {         // this component has no transition left
                    done = true;
                    break;
                }
                if (rs[c].lo > b) {           // gap in this component: skip ahead
                    covered = false;
                    next = std::min(next, (uint64_t)rs[c].lo);
                }
                else
                    next = std::min(next, (uint64_t)rs[c].hi + 1);
            }
            if (done)
                break;
            if (covered) {
                // Emit every combination of the targets active on this cell.  The modes
                // whose cofactors partition the domain give exactly one target per
                // component; the antimirov-style modes may give several.
                for (unsigned i = 0; i < n; ++i)
                    sw_odo[i] = 0;
                while (true) {
                    for (unsigned i = 0; i < n; ++i) {
                        auto const& r = sw_lists[i]->ranges[sw_cur[i]];
                        cur[i] = sw_lists[i]->targets[r.first + sw_odo[i]];
                    }
                    key const& ck = fill_key(cur);
                    if (visited.find(ck) == visited.end()) {
                        visited.insert(ck);
                        if (witness_word) {
                            expr* e = u().mk_char((unsigned)b);
                            m_pin.push_back(e);
                            parent[ck] = { st_key, e };
                        }
                        for (unsigned j = 0; j < n; ++j)
                            work.push_back(cur[j]);
                    }
                    unsigned i = n;
                    while (i-- > 0) {
                        if (++sw_odo[i] < sw_lists[i]->ranges[sw_cur[i]].count)
                            break;
                        sw_odo[i] = 0;
                    }
                    if (i == UINT_MAX)
                        break;                // odometer wrapped: cell exhausted
                }
            }
            b = next;
        }
        return true;
    };

    std::function<void(unsigned, guard_set const&)> rec =
        [&](unsigned i, guard_set const& acc) {
            if (bail) return;
            if (i == n) {
                key const& ck = fill_key(cur);
                if (visited.find(ck) == visited.end()) {
                    visited.insert(ck);
                    if (witness_word) {
                        expr_ref e(m);
                        if (acc.eval(&e) == l_true) {
                            m_pin.push_back(e);
                            parent[ck] = { st_key, e.get() };
                        }
                    }
                    for (unsigned j = 0; j < n; ++j)
                        work.push_back(cur[j]);
                }
                return;
            }
            for (auto const& [g, t] : *branches[i]) {
                if (re().is_empty(t)) continue;
                guard_set nacc = acc;
                nacc.conjoin(g);
                lbool ne = nacc.eval(nullptr);
                if (ne == l_undef) {
                    m_stats.inc_bail(bail_reason::guard);
                    bail = true;
                    return;
                }
                if (ne == l_false) continue;                  // empty joint guard: prune
                cur[i] = t;
                rec(i + 1, nacc);
                if (bail) return;
            }
        };

    while (!work.empty()) {
        if (m_budget == 0) {
            m_stats.inc_bail(bail_reason::budget);
            m_giveup = true;
            return l_undef;
        }
        if (!m.inc()) {
            m_stats.inc_bail(bail_reason::resource);
            m_giveup = true;
            return l_undef;
        }
        --m_budget;
        for (unsigned i = n; i-- > 0; ) {
            st[i] = work.back();
            work.pop_back();
        }
        if (is_accept()) {
            if (witness_word)
                *witness_word = reconstruct(fill_key(st));
            return l_true;
        }
        if (undecided) {
            m_stats.inc_bail(bail_reason::nullability);
            return l_undef;
        }

        if (witness_word)
            st_key = fill_key(st);

        if (sweep_ok && sweep())
            continue;

        for (unsigned i = 0; i < n; ++i)
            branches[i] = &derivative_cofactors(st[i]);

        // joint transitions = cartesian product of the branches with the guards
        // conjoined; prune as soon as the accumulated guard is empty, bail on unknown.
        guard_set top(m, u(), m_elem_sort, var0, &m_rp_cache);
        rec(0, top);
        if (bail)
            return l_undef;
    }
    return l_false;
}

bool seq_monadic::parse_term(expr* t, vector<atom>& atoms) {
    if (u().str.is_concat(t))
        return all_of(*to_app(t), [&](expr* arg) { return parse_term(arg, atoms); });
    if (u().str.is_empty(t))
        return true;                              // epsilon: contributes nothing
    zstring s;
    if (u().str.is_string(t, s)) {
        for (unsigned i = 0; i < s.length(); ++i) {
            expr* elem = u().str.mk_char(s, i);
            atoms.push_back(atom(m, false, nullptr, elem));
        }
        return true;
    }
    expr *elem = nullptr;
    if (u().str.is_unit(t, elem) && m.is_value(elem)) {                     // seq.unit of a constant element
        atoms.push_back(atom(m, false, nullptr, elem));
        return true;
    }
    // uninterpreted constant of sequence sort => a sequence variable
    if (is_var(t)) {
        atoms.push_back(atom(m, true, t, nullptr));
        return true;
    }
    return false;
}

unsigned seq_monadic::var_index(expr* v) {
    unsigned vi;
    if (m_var_idx.find(v, vi))
        return vi;
    vi = m_vars.size();
    m_var_idx.insert(v, vi);
    m_vars.push_back(v);
    m_groups.push_back(svector<component>());
    return vi;
}

void seq_monadic::reset_search() {
    m_seq_sort = nullptr;
    m_elem_sort = nullptr;
    m_atoms.reset();
    m_regexes.reset();
    m_vars.reset();
    m_var_idx.reset();
    m_groups.reset();
    m_last_occ.reset();
    m_group_cache.clear();
    m_der_cache.reset();
    m_nullable_cache.reset();
    m_undef_vars = 0;
    m_live_states.reset();
}

bool seq_monadic::prepare(membership_vec const& memberships) {
    reset_search();
    for (auto const& [term, regex, d] : memberships) {
        if (!u().is_re(regex, m_seq_sort)) {
            m_stats.inc_bail(bail_reason::unsupported);
            return false;
        }
        if (!u().is_seq(m_seq_sort, m_elem_sort)) {
            m_stats.inc_bail(bail_reason::unsupported);
            return false;
        }
        vector<atom> atoms;
        if (!parse_term(term, atoms)) {
            m_stats.inc_bail(bail_reason::unsupported);
            return false;
        }
        m_regexes.push_back(regex);
        m_atoms.push_back(atoms);
        m_pin.push_back(regex);
    }
    // A variable's component group is complete once the search passes the variable's
    // last occurrence; positions are compared in search order, i.e. lexicographically
    // on (membership index, atom index).
    for (unsigned mi = 0; mi < m_atoms.size(); ++mi) {
        vector<atom> const& atoms = m_atoms[mi];
        for (unsigned i = 0; i < atoms.size(); ++i) {
            if (!atoms[i].is_var)
                continue;
            expr* v = atoms[i].var.get();
            var_index(v);
            m_last_occ.insert(v, (static_cast<uint64_t>(mi) << 32) | i);
        }
    }
    return true;
}

lbool seq_monadic::group_nonempty(unsigned vi) {
    svector<component> const& g = m_groups[vi];
    group_sig& sig = m_sig_buf;
    sig.clear();
    for (auto const& c : g)
        sig.push_back({ c.state->get_id(), c.target ? c.target->get_id() : UINT_MAX });
    std::sort(sig.begin(), sig.end());
    sig.erase(std::unique(sig.begin(), sig.end()), sig.end());
    auto it = m_group_cache.find(sig);
    if (it != m_group_cache.end())
        return it->second;
    // Collapse duplicated components: they constrain the variable identically, and the
    // product search is exponential in the number of components.
    svector<component> comps;
    if (sig.size() == g.size())
        comps = g;
    else {
        std::set<std::pair<unsigned, unsigned>> seen;
        for (auto const& c : g)
            if (seen.insert({ c.state->get_id(), c.target ? c.target->get_id() : UINT_MAX }).second)
                comps.push_back(c);
    }
    lbool r = product_nonempty(comps, nullptr);
    m_group_cache.emplace(sig, r);            // sig is m_sig_buf; emplace copies it
    return r;
}

lbool seq_monadic::leaf() {
    if (m_undef_vars > 0)
        return l_undef;                           // some variable's emptiness test gave up
    if (!m_config.m_model)
        return l_true;
    m_model.reset();
    for (unsigned vi = 0; vi < m_groups.size(); ++vi) {
        if (m_groups[vi].empty())
            continue;
        expr_ref w(m);
        lbool ne = product_nonempty(m_groups[vi], &w);
        if (ne != l_true) {                       // groups were already shown non-empty;
            m_model.reset();                      // only reachable if the search was cut short
            return ne;
        }
        m_pin.push_back(w);
        m_model.insert(m_vars[vi], w.get());
    }
    return l_true;
}

lbool seq_monadic::dfs_membership(unsigned mi) {
    if (mi == m_atoms.size())
        return leaf();
    return dfs_atoms(mi, 0, m_regexes.get(mi));
}

lbool seq_monadic::dfs_atoms(unsigned mi, unsigned i, expr* R) {
    if (m_giveup)
        return l_undef;                           // unwind the whole search, don't keep branching
    if (m_budget == 0) {
        m_stats.inc_bail(bail_reason::budget);
        m_giveup = true;
        return l_undef;
    }
    if (!m.inc()) {
        m_stats.inc_bail(bail_reason::resource);
        m_giveup = true;
        return l_undef;
    }
    --m_budget;
    vector<atom> const& atoms = m_atoms[mi];
    if (i == atoms.size()) {                      // the rest of this membership is epsilon
        lbool nb = nullable(R);
        if (nb == l_true)
            return dfs_membership(mi + 1);
        if (nb == l_false)
            return l_false;
        m_stats.inc_bail(bail_reason::nullability);
        return l_undef;                           // undecidable nullability
    }
    atom const& a = atoms[i];
    if (!a.is_var) {                              // a constant element is consumed by a derivative
        expr_ref d = der_elem(R, a.elem.get());
        if (re().is_empty(d))
            return l_false;
        m_pin.push_back(d);
        return dfs_atoms(mi, i + 1, d);
    }

    // A variable: the last atom is a plain membership in R, otherwise the variable drives
    // the derivative automaton from R to some live state q, which splits the search.
    bool last_atom = (i + 1 == atoms.size());
    unsigned vi = var_index(a.var.get());
    uint64_t pos = (static_cast<uint64_t>(mi) << 32) | i;
    uint64_t last = 0;
    bool finalize = m_last_occ.find(a.var.get(), last) && last == pos;

    // Explores one split target; the caller stops at the first l_true.
    auto explore = [&](expr* target) -> lbool {
        m_groups[vi].push_back(component{ a.var.get(), R, target });
        // The group's emptiness test has to be run at some point anyway; running it as
        // soon as the group is complete (or as soon as it holds several components, where
        // an inconsistency can first arise) prunes the entire subtree below.
        lbool ne = l_true;
        if (re().is_empty(R))
            ne = l_false;
        else if (finalize || m_groups[vi].size() > 1)
            ne = group_nonempty(vi);
        lbool r;
        if (ne == l_false)
            r = l_false;
        else {
            if (ne == l_undef)
                ++m_undef_vars;
            r = last_atom ? dfs_membership(mi + 1) : dfs_atoms(mi, i + 1, target);
            if (ne == l_undef)
                --m_undef_vars;
        }
        m_groups[vi].pop_back();
        return r;
    };

    if (last_atom)
        return explore(nullptr);

    // The live states are consumed as they are produced, so a satisfying branch under an
    // early state means the rest of the reachable set is never expanded.  That is what
    // makes a root with an exponential live set tractable when a witness is found early.
    bool any_undef = false;
    auto live = m_live_states.reachable_live(R);
    for (expr* q : live) {
        lbool r = explore(q);
        if (r == l_true)
            return l_true;
        if (r == l_undef) {
            if (m_giveup)
                return l_undef;
            any_undef = true;
        }
    }
    // Short of the full reachable set the unexplored split states could still hold a
    // solution, so the l_false the loop would otherwise report is not justified.
    if (live.failed()) {
        m_stats.inc_bail(
            live.failure_reason() == seq::live_states::failure::state_cap ?
            bail_reason::state_cap : bail_reason::resource);
        return l_undef;
    }
    return any_undef ? l_undef : l_false;
}

lbool seq_monadic::decide(membership_vec const& memberships) {
    m_last_search_memberships = memberships;
    m_model.reset();
    reset_search();                               // clear the caches before dropping the
    m_pin.reset();                                // pins that keep their keys alive
    m_rp_cache.maybe_reset(1u << 16);
    reset_ivl_cache();
    m_rw.get_derive().maybe_reset_cached_cofactors(1u << 16);
    m_budget = 1000000;
    m_giveup = false;
    lbool r = l_true;                             // empty conjunction is vacuously true
    if (!memberships.empty() && !prepare(memberships))
        r = l_undef;
    else if (!memberships.empty())
        r = dfs_membership(0);
    if (r != l_true)
        m_model.reset();
    m_last_search_result = r;
    return r;
}

lbool seq_monadic::solve(expr* term, expr* R) {
    m_core.reset();
    membership_vec mv;
    mv.push_back({ expr_ref(term, m), expr_ref(R, m), nullptr });
    m_last_result = decide(mv);
    return m_last_result;
}

void seq_monadic::add(expr* term, expr* regex, void* d) {
    m_memberships.push_back({ expr_ref(term, m), expr_ref(regex, m), d });
    m_undo_trail.push(push_back_vector(m_memberships));
}

namespace {
    // Restores a membership term on backtrack.  The previous term is pinned by this trail
    // object's own expr_ref and released in undo() (the trail region does not run
    // destructors, mirroring obj_ref_trail).
    class set_term_trail : public trail {
        vector<std::tuple<expr_ref, expr_ref, void*>>& m_v;
        unsigned m_idx;
        expr_ref m_old;
    public:
        set_term_trail(vector<std::tuple<expr_ref, expr_ref, void*>>& v, unsigned idx, expr* old, ast_manager& m):
            m_v(v), m_idx(idx), m_old(old, m) {}
        void undo() override {
            std::get<0>(m_v[m_idx]) = m_old;
            m_old.reset();
        }
    };
}

void seq_monadic::set_term(void* d, expr* term) {
    for (unsigned i = 0; i < m_memberships.size(); ++i) {
        if (std::get<2>(m_memberships[i]) != d)
            continue;
        expr_ref& t = std::get<0>(m_memberships[i]);
        if (t.get() == term)
            return;
        m_undo_trail.push(set_term_trail(m_memberships, i, t, m));
        t = term;
        return;
    }
}

bool seq_monadic::can_decide_term(expr* term) {
    vector<atom> atoms;
    return parse_term(term, atoms);
}

void seq_monadic::add_lo(expr* term, unsigned lo, void* d) {
    if (lo == 0)
        return;
    sort* re_sort = re().mk_re(term->get_sort());
    expr_ref all_char(re().mk_full_char(re_sort), m);
    expr_ref prefix(re().mk_loop_proper(all_char, lo, lo), m);
    expr_ref all(re().mk_full_seq(re_sort), m);
    expr_ref regex(re().mk_concat(prefix, all), m);
    add(term, regex, d);
}

void seq_monadic::add_hi(expr* term, unsigned hi, void* d) {
    sort* re_sort = re().mk_re(term->get_sort());
    expr_ref all_char(re().mk_full_char(re_sort), m);
    expr_ref regex(re().mk_loop_proper(all_char, 0, hi), m);
    add(term, regex, d);
}

void seq_monadic::add_len(expr* term, unsigned len, void* d) {
    sort* re_sort = re().mk_re(term->get_sort());
    expr_ref all_char(re().mk_full_char(re_sort), m);
    expr_ref regex(re().mk_loop_proper(all_char, len, len), m);
    add(term, regex, d);
}


void seq_monadic::minimize_core(membership_vec const& memberships) {
    m_core.reset();
    if (!m_config.m_min_core) {
        // No minimization: the core is simply every asserted membership's dependency.
        for (auto const& [term, regex, d] : memberships)
            if (d)
                m_core.push_back(d);
        return;
    }
    // Deletion-based minimization: start from the full unsat set and try to drop each
    // membership; a membership is kept only if removing it makes the set no longer
    // provably unsat.  The result is a minimal unsat subset (relevant constraints only).
    membership_vec keep(memberships);
    for (unsigned i = 0; i < keep.size(); ) {
        membership_vec trial(keep);
        trial.erase(trial.begin() + i);
        if (decide(trial) == l_false)
            keep.swap(trial);                     // membership i is not needed for unsat
        else
            ++i;                                  // membership i is needed; keep it
    }
    for (auto const& [term, regex, d] : keep)
        if (d)
            m_core.push_back(d);
}

lbool seq_monadic::check() {
    m_core.reset();
    lbool r = decide(m_memberships);
    if (r == l_false) {
        minimize_core(m_memberships);
        m_model.reset();
    }
    m_last_result = r;
    return m_last_result;
}

std::ostream& seq_monadic::display(std::ostream& out) const {
    auto display_expr = [&](expr* e) {
        if (e)
            out << mk_pp(e, m);
        else
            out << "null";
    };

    out << "(seq-monadic\n"
        << "  :mode " << mode_name(m_config.m_mode) << "\n"
        << "  :generate-model " << (m_config.m_model ? "true" : "false") << "\n"
        << "  :minimize-core " << (m_config.m_min_core ? "true" : "false") << "\n"
        << "  :last-result " << result_name(m_last_result) << "\n"
        << "  :budget " << m_budget << "\n"
        << "  :giveup " << (m_giveup ? "true" : "false") << "\n"
        << "  :sequence-sort ";
    if (m_seq_sort)
        out << mk_pp(m_seq_sort, m);
    else
        out << "null";
    out << "\n  :element-sort ";
    if (m_elem_sort)
        out << mk_pp(m_elem_sort, m);
    else
        out << "null";

    out << "\n  :memberships (";
    for (unsigned i = 0; i < m_memberships.size(); ++i) {
        auto const& [term, regex, dep] = m_memberships[i];
        out << "\n    [" << i << "] ";
        display_expr(term);
        out << " in ";
        display_expr(regex);
        out << " :dependency " << dep;
    }
    if (!m_memberships.empty())
        out << "\n  ";
    out << ")\n  :model (";
    for (auto const& [var, value] : m_model) {
        out << "\n    ";
        display_expr(var);
        out << " -> ";
        display_expr(value);
    }
    if (!m_model.empty())
        out << "\n  ";
    out << ")\n  :core (";
    for (void* dep : m_core)
        out << " " << dep;
    out << " )";

    out << "\n  :last-internal-search\n"
        << "    (:result " << result_name(m_last_search_result)
        << "\n     :memberships (";
    for (unsigned i = 0; i < m_last_search_memberships.size(); ++i) {
        auto const& [term, regex, dep] = m_last_search_memberships[i];
        out << "\n       [" << i << "] ";
        display_expr(term);
        out << " in ";
        display_expr(regex);
        out << " :dependency " << dep;
    }
    if (!m_last_search_memberships.empty())
        out << "\n     ";
    out << ")\n     :variables (";
    for (expr* var : m_vars) {
        out << " ";
        display_expr(var);
    }
    out << " )\n     :parsed-memberships (";
    for (unsigned mi = 0; mi < m_atoms.size(); ++mi) {
        out << "\n       [" << mi << "] :regex ";
        display_expr(m_regexes.get(mi));
        out << " :atoms (";
        for (atom const& a : m_atoms[mi]) {
            out << " " << (a.is_var ? "var:" : "elem:");
            display_expr(a.is_var ? a.var.get() : a.elem.get());
        }
        out << " )";
    }
    if (!m_atoms.empty())
        out << "\n     ";
    out << ")\n     :groups (";
    for (unsigned vi = 0; vi < m_groups.size(); ++vi) {
        out << "\n       ";
        display_expr(m_vars[vi]);
        out << " (";
        for (component const& c : m_groups[vi]) {
            out << "\n         ";
            display_expr(c.state);
            if (c.target) {
                out << " -> ";
                display_expr(c.target);
            }
            else {
                out << " nullable";
            }
        }
        if (!m_groups[vi].empty())
            out << "\n       ";
        out << ")";
    }
    if (!m_groups.empty())
        out << "\n     ";
    out << ")\n"
        << "     :undefined-variables " << m_undef_vars << "\n"
        << "     :group-cache-size " << m_group_cache.size() << "\n"
        << "     :derivative-cache-size " << m_der_cache.size() << "\n"
        << "     :nullable-cache-size " << m_nullable_cache.size() << "\n"
        << "     :live-cache-size " << m_live_states.num_states() << "\n"
        << "     :pinned-expressions " << m_pin.size() << ")\n";

    out << "  :statistics\n"
        << "    (:cofactor-calls " << m_stats.m_cofactor_calls << "\n"
        << "     :states " << m_stats.m_states;
    for (unsigned i = 0; i < static_cast<unsigned>(bail_reason::num_reasons); ++i)
        out << "\n     :bail-" << bail_name(i) << " " << m_stats.m_bails[i];
    return out << "))\n";
}

void seq_monadic::collect_statistics(::statistics& st) const {
    static char const* const bail_names[] = {
        "seq monadic bail unsupported",
        "seq monadic bail state cap",
        "seq monadic bail dnf cap",
        "seq monadic bail budget",
        "seq monadic bail resource",
        "seq monadic bail nullability",
        "seq monadic bail guard"
    };
    st.update("seq monadic cofactor calls", m_stats.m_cofactor_calls);
    st.update("seq monadic states", m_stats.m_states);
    for (unsigned i = 0; i < static_cast<unsigned>(bail_reason::num_reasons); ++i)
        st.update(bail_names[i], m_stats.m_bails[i]);
}