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
#include "ast/for_each_expr.h"
#include <set>
#include <vector>
#include <map>
#include <tuple>
#include <functional>
#include <algorithm>
#include <unordered_set>

namespace {
    char const *mode_name(seq::transition_mode mode) {
        switch (mode) {
        case seq::transition_mode::brzozowski_tm: return "brzozowski";
        case seq::transition_mode::light_antimirov_tm: return "light-antimirov";
        }
        return "unknown";
    }

    char const *bail_name(unsigned i) {
        static char const *const names[] = {"unsupported", "state-cap",   "budget", "state-expansion",
                                            "resource",    "nullability", "guard",  "not-reversible",
                                            "replay"};
        return i < std::size(names) ? names[i] : "unknown";
    }

    char const *result_name(lbool r) {
        switch (r) {
        case l_true: return "sat";
        case l_false: return "unsat";
        default: return "unknown";
        }
    }

    void dedup_views(seq::view_vector const &g, seq::view_vector &out) {
        std::set<seq::view::sig> seen;
        for (auto const &c : g) {
            if (seen.insert(c.key()).second)
                out.push_back(c);
        }
    }
}  // namespace

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

bool seq_monadic::out_of_budget() {
    if (m_budget == 0) {
        m_stats.inc_bail(bail_reason::budget);
        m_giveup = true;
        return true;
    }
    if (!m.inc()) {
        m_stats.inc_bail(bail_reason::resource);
        m_giveup = true;
        return true;
    }
    --m_budget;
    return false;
}

lbool seq_monadic::product_nonempty(expr* var, seq::view_vector const& comps, expr_ref* witness_word) {
    sort *elem_sort = nullptr;
    auto seq_sort = var->get_sort();
    if (!u().is_seq(seq_sort, elem_sort))
        return l_undef;
    unsigned n = comps.size();
    if (n == 0) {
        if (witness_word)
            *witness_word = expr_ref(u().str.mk_empty(seq_sort), m);
        return l_true;
    }

    expr_ref var0(m.mk_var(0, elem_sort), m);     // the element variable the guards range over
    typedef std::vector<unsigned> key;
    struct key_hash {
        size_t operator()(key const& k) const {
            uint64_t h = 1469598103934665603ull;
            for (unsigned x : k)
                h = (h ^ x) * 1099511628211ull;
            return static_cast<size_t>(h);
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
            if (comps[i].m_target) {
                if (st[i] != comps[i].m_target) return false;
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
        work.push_back(comps[i].m_state);
        start_key[i] = comps[i].m_state->get_id();
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
        return expr_ref(u().str.mk_concat(es.size(), es.data(), seq_sort), m);
    };

    // Hoisted out of the search loop: the per-view cofactor vectors are owned by the
    // cofactor cache and stay valid for the whole search, so they are referenced rather
    // than copied (copying re-materialized every branch as expr_ref pairs on every pop).
    svector<expr_ref_pair_vector const*> branches;
    branches.resize(n);
    key st_key;
    bool bail = false;

    // Bound the work spent expanding a single product state.  The main budget counts
    // product states, so inner loops get a separate cap to preserve the budget's meaning.
    uint64_t const inner_limit = 1u << 16;
    uint64_t inner_steps = 0;
    auto inner_step = [&]() -> bool {
        ++inner_steps;
        if (inner_steps > m_stats.m_max_state_expansion)
            m_stats.m_max_state_expansion = static_cast<unsigned>(inner_steps);
        if (inner_steps <= inner_limit)
            return false;
        m_stats.inc_bail(bail_reason::state_expansion);
        m_giveup = true;
        return true;
    };

    // ---- interval-refinement ("t-regex merge") product --------------------------
    // Over the character sort every cofactor guard denotes a union of ranges, so each
    // view's derivative has a canonical ordered-interval ("t-regex") form, cached
    // per state by interval_cofactors.  The joint transitions are then exactly the cells
    // of the common refinement of those n interval lists, obtained by a cursor merge in
    // O(sum_i intervals_i) -- whereas the cartesian enumeration below tries
    // prod_i(k_i) combinations, almost all of which are pruned as empty.
    bool const sweep_ok = u().is_char(elem_sort);
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
                return true;                  // view is stuck: no joint transition
            sw_cur[i] = 0;
        }
        uint64_t b = 0;
        while (b <= max_char) {
            if (inner_step()) {
                bail = true;
                return true;
            }
            uint64_t next = (uint64_t)max_char + 1;
            bool covered = true, done = false;
            for (unsigned i = 0; i < n; ++i) {
                auto const& rs = sw_lists[i]->ranges;
                unsigned& c = sw_cur[i];
                while (c < rs.size() && rs[c].hi < b)
                    ++c;
                if (c == rs.size()) {         // this view has no transition left
                    done = true;
                    break;
                }
                if (rs[c].lo > b) {           // gap in this view: skip ahead
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
                // view; the antimirov-style modes may give several.
                for (unsigned i = 0; i < n; ++i)
                    sw_odo[i] = 0;
                while (true) {
                    if (inner_step()) {
                        bail = true;
                        return true;
                    }
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
            if (inner_step()) {
                bail = true;
                return;
            }
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
        if (out_of_budget())
            return l_undef;
        inner_steps = 0;                          // each state gets its own expansion allowance
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

        if (sweep_ok) {
            bool const swept = sweep();
            if (bail)
                return l_undef;
            if (swept)
                continue;
        }

        for (unsigned i = 0; i < n; ++i)
            branches[i] = &derivative_cofactors(st[i]);

        // joint transitions = cartesian product of the branches with the guards
        // conjoined; prune as soon as the accumulated guard is empty, bail on unknown.
        guard_set top(m, u(), elem_sort, var0, &m_rp_cache);
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
    m_groups.push_back(seq::view_vector());
    return vi;
}

void seq_monadic::reset_search() {
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
    m_cur_path.reset();
}

lbool seq_monadic::replay_bail() {
    m_stats.inc_bail(bail_reason::replay);
    m_giveup = true;
    return l_undef;
}

bool seq_monadic::reverse_regex(expr* r, expr_ref& result) {
    result = expr_ref(re().mk_reverse(r), m);
    m_thrw(result, result);
    // A remaining re.reverse marks a subterm that seq_rewriter could not push through.
    for (auto e : subterms::ground(result))
        if (re().is_reverse(e))
            return false;
    return true;
}

expr_ref seq_monadic::mk_rev_var(expr* v) {
    if (!m_rev_decl || m_rev_decl->get_range() != v->get_sort()) {
        sort *domain[1] = {v->get_sort()};
        m_rev_decl = m.mk_fresh_func_decl("rev", 1, domain, v->get_sort());
    }
    return expr_ref(m.mk_app(m_rev_decl, v), m);
}

expr* seq_monadic::strip_rev_var(expr* v) const {
    if (m_rev_decl && is_app(v) && to_app(v)->get_decl() == m_rev_decl.get())
        return to_app(v)->get_arg(0);
    return v;
}

bool seq_monadic::prepare(membership_vec const& memberships, bool reversed) {
    reset_search();
    // Reversing has to be all or nothing: a system in which some memberships read forwards
    // and others backwards constrains a mixture of w and rev(w) and is not the original
    // problem.  So the reversed regexes are all built first, and any failure keeps the
    // whole problem forwards.
    m_reversed = reversed;
    expr_ref_vector rev_regexes(m);
    if (m_reversed) {
        for (auto const& [term, regex, d] : memberships) {
            expr_ref rr(m);
            if (!reverse_regex(regex, rr)) {
                m_reversed = false;
                break;
            }
            rev_regexes.push_back(rr);
        }
    }
    unsigned mi = 0;
    for (auto const& [term, regex, d] : memberships) {
        sort* seq_sort = nullptr;
        if (!u().is_re(regex, seq_sort)) {
            m_stats.inc_bail(bail_reason::unsupported);
            return false;
        }
        // Derivative processing assumes the regex denotes a fixed language.
        if (!re().is_ground(regex)) {
            m_stats.inc_bail(bail_reason::unsupported);
            return false;
        }
        if (!u().is_seq(seq_sort)) {
            m_stats.inc_bail(bail_reason::unsupported);
            return false;
        }
        vector<atom> atoms;
        if (!parse_term(term, atoms)) {
            m_stats.inc_bail(bail_reason::unsupported);
            return false;
        }
        expr* R = regex;
        if (m_reversed) {
            R = rev_regexes.get(mi);
            vector<atom> ratoms;                  // rev(a1...ak) = rev(ak)...rev(a1); a single
            for (unsigned i = atoms.size(); i-- > 0; ) {   // element is its own reverse, and a
                atom const& a = atoms[i];         // variable becomes its reversed reading
                if (!a.is_var) {
                    ratoms.push_back(a);
                    continue;
                }
                expr_ref rv = mk_rev_var(a.var.get());
                m_pin.push_back(rv);
                ratoms.push_back(atom(m, true, rv.get(), nullptr));
            }
            atoms = ratoms;
        }
        m_regexes.push_back(R);
        m_atoms.push_back(atoms);
        m_pin.push_back(R);
        ++mi;
    }
    // A variable's view group is complete once the search passes the variable's
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
    seq::view_vector const& g = m_groups[vi];
    group_sig& sig = m_sig_buf;
    sig.clear();
    for (auto const& c : g)
        sig.push_back(c.key());
    std::sort(sig.begin(), sig.end());
    sig.erase(std::unique(sig.begin(), sig.end()), sig.end());
    auto it = m_group_cache.find(sig);
    if (it != m_group_cache.end())
        return it->second;
    seq::view_vector comps;
    if (sig.size() == g.size())
        comps = g;                            // signature already deduplicated
    else
        dedup_views(g, comps);
    lbool r = product_nonempty(m_vars[vi], comps, nullptr);
    m_group_cache.emplace(sig, r);            // sig is m_sig_buf; emplace copies it
    return r;
}

lbool seq_monadic::leaf() {
    if (m_giveup)
        return l_undef;                           // the search was already abandoned
    if (m_in_replay) {
        // The branch the previous pull reported: reject it, and the search continues
        // exactly as if that leaf had failed.  A different depth means a different tree.
        if (m_cur_path.size() != m_resume->size())
            return replay_bail();
        m_in_replay = false;
        return l_false;
    }
    if (m_undef_vars > 0) {
        m_had_undef = true;
        return l_undef;                           // some variable's emptiness test gave up
    }
    if (m_enumerate)
        m_leaf_path = m_cur_path;                 // resume point of the branch reported now
    if (!m_config.m_solution)
        return l_true;
    // Snapshot the branch: dfs_atoms pops m_groups on the way out even on success.
    m_solution.reset();
    for (unsigned vi = 0; vi < m_groups.size(); ++vi) {
        if (m_groups[vi].empty())
            continue;
        for (auto const& v : m_groups[vi]) {      // states must outlive the search
            m_pin.push_back(v.m_state);
            if (v.m_target)
                m_pin.push_back(v.m_target);
        }
        m_solution.insert(m_vars[vi], m_groups[vi]);
    }
    return l_true;
}

lbool seq_monadic::materialize(expr* var, expr_ref& word) {
    // without a completed search there is nothing recorded to collapse
    if (m_last_result != l_true)
        return l_undef;
    return materialize_recorded(var, word);
}

lbool seq_monadic::materialize_recorded(expr* var, expr_ref& word) {
    // without a recorded solution m_solution is empty, and an empty word would pass
    // for a satisfying assignment
    if (!m_config.m_solution)
        return l_undef;
    expr* key = var;
    expr_ref rev_key(m);
    seq::view_vector views;
    bool found = m_solution.find(key, views);
    if (!found && m_reversed) {
        rev_key = mk_rev_var(var);
        key = rev_key.get();
        found = m_solution.find(key, views);
    }
    if (!found) {
        word = u().str.mk_empty(var->get_sort());  // unconstrained: any value will do
        return l_true;
    }
    seq::view_vector comps;
    dedup_views(views, comps);
    expr_ref w(m);
    lbool r = product_nonempty(var, comps, &w);
    if (r == l_true) {
        if (m_reversed && !m_rw.mk_seq_reverse(w, w))  // the search solved rev(term) in rev(R),
            return l_undef;                            // so rev(x)'s witness is x's value backwards
        m_pin.push_back(w);
        word = w;
    }
    return r;
}

lbool seq_monadic::materialize_all(expr_substitution& model) {
    model.reset();
    if (m_last_result != l_true || !m_config.m_solution)
        return l_undef;
    for (auto const& [var, views] : m_solution) {
        expr_ref w(m);
        expr* v = strip_rev_var(var);
        lbool r = materialize_recorded(v, w);  // preconditions already checked above
        if (r != l_true)
            return r;
        model.insert(v, w.get());
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
    if (out_of_budget())
        return l_undef;
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
        m_groups[vi].push_back(seq::view::reach(R, target));
        // The group's emptiness test has to be run at some point anyway; running it as
        // soon as the group is complete (or as soon as it holds several views, where
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
        return explore(nullptr);                   // forced: not a recorded choice

    // Enumeration replay (see `iterator`).  While the branch still follows the path of
    // the one last reported, this level skips to its recorded continuation -- everything
    // before it was reported or refuted by an earlier pull -- descends it, and only then
    // walks the rest normally: "resume as if the reported leaf had just failed".
    unsigned const depth = m_cur_path.size();
    bool const replay = m_in_replay;
    if (replay && (depth >= m_resume->size() || (*m_resume)[depth].mi != mi ||
                   (*m_resume)[depth].state != R))
        return replay_bail();
    expr* const resume_target = replay ? (*m_resume)[depth].target : nullptr;
    bool seen_resume = false;

    // The live states are consumed as they are produced, so a satisfying branch under an
    // early state means the rest of the reachable set is never expanded.  That is what
    // makes a root with an exponential live set tractable when a witness is found early.
    bool any_undef = false;
    auto live = m_live_states.reachable_live(R);
    for (expr* q : live) {
        if (replay && !seen_resume) {
            if (q != resume_target)
                continue;                          // covered by an earlier pull
            seen_resume = true;
        }
        if (m_enumerate)
            m_cur_path.push_back(choice{ mi, R, q });
        lbool r = explore(q);
        if (m_enumerate)
            m_cur_path.pop_back();
        if (replay && seen_resume && m_in_replay)
            return replay_bail();                  // the replay did not reach its leaf
        if (r == l_true) {
            if (any_undef)
                m_had_undef = true;                // passed over, and never revisited
            return l_true;
        }
        if (r == l_undef) {
            if (m_giveup)
                return l_undef;
            any_undef = true;
        }
    }
    if (replay && !seen_resume)
        return replay_bail();                      // the recorded continuation is gone
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

lbool seq_monadic::decide_oriented(membership_vec const& memberships, bool reversed,
                                   unsigned budget) {
    m_solution.reset();
    reset_search();                               // clear the caches before dropping the
    m_pin.reset();                                // pins that keep their keys alive
    m_rp_cache.maybe_reset(1u << 16);
    reset_ivl_cache();
    m_rw.get_derive().maybe_reset_cached_cofactors(1u << 16);
    m_budget = budget;
    m_giveup = false;
    lbool r = l_true;                             // empty conjunction is vacuously true
    if (memberships.empty())
        return r;
    if (!prepare(memberships, reversed))
        r = l_undef;
    else if (reversed && !m_reversed && m_config.m_orientation == orientation::retry) {
        // Under the retry policy the forward search has already run and failed, so a
        // problem whose regexes cannot be reversed has nothing left to offer.  Plain
        // `reversed` mode instead keeps the forward reading prepare() fell back to, which
        // still answers the question.
        m_stats.inc_bail(bail_reason::not_reversible);
        r = l_undef;
    }
    else
        r = dfs_membership(0);
    if (r != l_true)
        m_solution.reset();
    return r;
}

bool seq_monadic::constrains_length(expr* r) {
    return any_of(subterms::ground(expr_ref(r, m)), [&](expr* t) {
        unsigned lo = 0, hi = 0;
        expr* body = nullptr;
        return re().is_loop(t, body, lo, hi) && lo == hi && lo > 1;
    });
}

void seq_monadic::split_conjuncts(expr* r, ptr_vector<expr>& out) {
    if (re().is_intersection(r)) {
        for (expr* arg : *to_app(r))
            split_conjuncts(arg, out);            // re.inter is n-ary and can nest
        return;
    }
    out.push_back(r);
}

bool seq_monadic::instantiate_word(expr* t, ptr_vector<expr>& elems, bool subst) {
    if (u().str.is_concat(t))
        return all_of(*to_app(t), [&](expr* arg) { return instantiate_word(arg, elems, subst); });
    if (u().str.is_empty(t))
        return true;
    zstring s;
    if (u().str.is_string(t, s)) {
        for (unsigned i = 0; i < s.length(); ++i) {
            expr_ref e(u().str.mk_char(s, i), m);
            m_pin.push_back(e);
            elems.push_back(e);
        }
        return true;
    }
    expr* elem = nullptr;
    if (u().str.is_unit(t, elem) && m.is_value(elem)) {
        elems.push_back(elem);
        return true;
    }
    expr* cached = nullptr;
    // A witness is a concrete sequence, so it is instantiated without substituting again --
    // which also stops a self-referential solution from looping.
    if (!subst || !is_var(t))
        return false;
    if (m_split_words.find(t, cached))
        return cached && instantiate_word(cached, elems, false);
    expr_ref w(m);
    if (materialize_recorded(t, w) != l_true) {
        m_split_words.insert(t, nullptr);         // remember the failure too
        return false;
    }
    m_pin.push_back(w);
    m_split_words.insert(t, w);
    return instantiate_word(w, elems, false);
}

lbool seq_monadic::model_accepts(expr* term, expr* r) {
    ptr_vector<expr> elems;
    if (!instantiate_word(term, elems))
        return l_undef;                           // a variable the relaxation never valued
    expr_ref state(r, m);
    for (expr* e : elems) {
        if (re().is_empty(state))
            return l_false;
        state = der_elem(state, e);
        if (!state)
            return l_undef;
    }
    return nullable(state);
}

lbool seq_monadic::decide_split(membership_vec const& memberships, unsigned budget,
                                unsigned allowance) {
    // Normalize top-level intersections into separate memberships.  They remain linked by
    // their term and dependency, while the refinement can select them independently.
    membership_vec conjuncts;
    for (auto const& [term, regex, d] : memberships) {
        ptr_vector<expr> cs;
        split_conjuncts(regex, cs);
        for (expr* r : cs)
            conjuncts.push_back({ term, expr_ref(r, m), d });
    }
    if (conjuncts.size() == memberships.size())
        return l_undef;                           // no membership was an intersection: nothing to decompose

    m_stats.m_split_calls++;

    // The relaxation starts empty, so the first round decides nothing and every conjunct
    // has to earn its place.
    bool_vector selected(conjuncts.size(), false);

    // Cost of one lookahead probe.  It only has to tell an expensive candidate from a cheap
    // one, so it is a fraction of the real budget -- and a probe that refutes within it is
    // an answer to the whole query, not just to the comparison.
    unsigned const probe_budget = std::max(1000u, budget / 8);
    bool const reversed = m_config.m_orientation == orientation::reversed;

    // Cache length-constraining status per conjunct: constrains_length traverses the full
    // expression tree, so computing it once avoids repeated work inside the probe loop.
    bool_vector length_constraining(conjuncts.size());
    for (unsigned i = 0; i < conjuncts.size(); ++i)
        length_constraining[i] = constrains_length(std::get<1>(conjuncts[i]));

    auto relaxation = [&](bool_vector const& sel) {
        membership_vec relaxed;
        for (unsigned i = 0; i < conjuncts.size(); ++i)
            if (sel[i])
                relaxed.push_back(conjuncts[i]);
        return relaxed;
    };

    unsigned_vector violated;
    // Total work the decomposition may spend, over all of its rounds and probes together.
    // It caps the price of failure: a decomposition that gives up has cost no more than the
    // undivided search it is standing in for.
    auto spend = [&](unsigned granted) {
        unsigned const used = granted - std::min(granted, m_budget);
        allowance -= std::min(allowance, used);
        return allowance > 0;
    };

    for (unsigned round = 0; round < m_config.m_split_rounds && allowance > 0; ++round) {
        m_stats.m_split_rounds++;
        membership_vec relaxed = relaxation(selected);
        lbool r = decide_oriented(relaxed, reversed, budget);
        if (r == l_undef)
            return l_undef;                       // the relaxation is already too hard
        if (r == l_false) {
            // Dropping intersected regexes only enlarges the language, so the relaxation is
            // implied by the original: refuting it refutes the original.
            m_stats.m_split_decided++;
            return l_false;
        }
        // Satisfiable, but only of the kept conjuncts.  The model answers the whole query
        // iff every dropped conjunct also accepts it.
        if (!spend(budget))
            return l_undef;
        violated.reset();
        // Collapsing a variable's views runs a product search, so the words are built once
        // per round and shared by every conjunct tested against them.
        m_split_words.reset();
        for (unsigned i = 0; i < conjuncts.size(); ++i)
            if (!selected[i] &&
                model_accepts(std::get<0>(conjuncts[i]), std::get<1>(conjuncts[i])) != l_true)
                violated.push_back(i);
        if (violated.empty()) {
            m_stats.m_split_decided++;
            return l_true;
        }
        IF_VERBOSE(3, verbose_stream() << "(seq-monadic-split :round " << round
                   << " :kept " << relaxed.size() << "/" << memberships.size()
                   << " :violated " << violated.size() << ")\n");
        // Grow the relaxation by one violated conjunct.  Which one decides how fast the
        // loop converges.  Prefer a conjunct that pins word lengths to a residue class:
        // the search refutes a membership set by exhausting the reachable product, and a
        // length constraint shrinks that product across every branch at once, where a
        // conjunct that merely forbids a rare infix leaves it essentially unchanged.
        // Among equals prefer the cheapest, measured by the work its probe left unspent: a
        // candidate that exhausts the probe rebuilds the product this is avoiding.  The
        // probes invalidate m_solution, which is why `violated` is complete by now.
        unsigned best = 0;
        uint64_t best_key = 0;
        for (unsigned k = 0; k < violated.size(); ++k) {
            unsigned i = violated[k];
            selected[i] = true;
            membership_vec trial = relaxation(selected);
            lbool p = decide_oriented(trial, reversed, probe_budget);
            selected[i] = false;
            if (p == l_false) {
                selected[i] = true;
                m_stats.m_split_decided++;
                return l_false;
            }
            bool const affordable = spend(probe_budget);
            if (p == l_undef) {
                if (!affordable)
                    return l_undef;
                continue;
            }
            uint64_t key = m_budget |
                (length_constraining[i] ? 1ull << 40 : 0);
            if (key >= best_key) {
                best = k;
                best_key = key;
            }
            if (!affordable)
                break;
        }
        unsigned bi = violated[best];
        selected[bi] = true;
        IF_VERBOSE(3, verbose_stream() << "(seq-monadic-split :add " << bi
                   << " " << mk_pp(std::get<1>(conjuncts[bi]), m) << ")\n");
    }
    return l_undef;
}

lbool seq_monadic::decide_policy(membership_vec const& memberships, unsigned budget, bool sticky) {
    if (m_config.m_orientation != orientation::retry)
        return decide_oriented(memberships, m_config.m_orientation == orientation::reversed, budget);
    // Read forwards first, with the whole budget: halving it would make retry lose
    // decisions that plain forward solves, and a direction that is about to succeed is
    // not worth interrupting.  Only a search that ran out of work is worth turning
    // around; the other ways of giving up (an unsupported shape, an undecidable
    // nullability, a guard the range solver cannot evaluate) are properties of the
    // problem rather than of the direction it is read in.
    unsigned const before = work_bails();
    lbool r = decide_oriented(memberships, false, budget);
    if (r != l_undef || m_retry_disabled || work_bails() == before)
        return r;
    r = decide_oriented(memberships, true, budget);
    // A bail is not in itself bad: it hands the problem back to the caller, which has its
    // own way of making progress.  Reversing spends a second full budget instead, so a
    // reversed attempt that also fails is evidence that this query's regexes are no cheaper
    // backwards -- and the same regexes recur at every decision, so stop paying for it.
    // Only a full-budget attempt is evidence of that; a probe was never given the chance.
    if (r == l_undef && sticky)
        m_retry_disabled = true;
    return r;
}

lbool seq_monadic::decide(membership_vec const& memberships) {
    m_last_search_memberships = memberships;
    unsigned const limit = m_config.m_budget_limit;
    lbool r = l_undef;
    if (m_config.m_split_rounds > 0 && !m_split_disabled) {
        // Decomposing an intersection is only worth it for a decision the undivided search
        // cannot make, and the cheapest way to find that out is to give the undivided
        // search a fraction of its budget first: a decision it reaches within that fraction
        // is one the decomposition could only have slowed down.  Nothing is lost when the
        // decomposition fails -- the fraction is then re-spent as the prefix of the full
        // attempt below.  Relaxations get a larger share, since each is a smaller problem
        // than the one that just ran out, but still well short of the undivided budget: a
        // relaxation that needs all of it has rebuilt the product this is meant to avoid.
        // The decomposition as a whole is held to one undivided budget, so a query it
        // cannot decide costs no more than the search it stands in for.
        unsigned const probe_budget = std::max(1000u, limit / 128);
        unsigned const before = work_bails();
        r = decide_policy(memberships, probe_budget, false);
        if (r == l_undef && work_bails() > before)
            r = decide_split(memberships, std::max(1000u, limit / 16), limit);
    }
    if (r == l_undef)
        r = decide_policy(memberships, limit, true);
    m_last_search_result = r;
    return r;
}

lbool seq_monadic::enumerate(membership_vec const& memberships, svector<choice> const& resume,
                             bool has_resume) {
    m_enumerate = true;
    m_resume = &resume;
    m_in_replay = has_resume;
    m_had_undef = false;
    m_leaf_path.reset();
    // Forward only: a reversed reading reports views over the reversed regexes, and the
    // retry policy would run two searches -- neither is a branch of the problem the
    // caller asked about.
    lbool r = decide_oriented(memberships, false, m_config.m_budget_limit);
    m_enumerate = false;
    m_resume = nullptr;
    m_in_replay = false;
    m_last_search_memberships = memberships;
    m_last_search_result = r;
    m_last_result = r;    // a reported branch is materialize()-able, a drained one is not
    return r;
}

seq_monadic::iterator::iterator(seq_monadic& engine, membership_vec const& memberships,
                                unsigned limit) :
    m_engine(engine), m_memberships(memberships), m_path_pin(engine.m), m_limit(limit) {}

bool seq_monadic::iterator::next(obj_map<expr, seq::view_vector>& solution) {
    solution.reset();
    if (m_done)
        return false;
    // An empty conjunction has no search to resume.
    if (m_memberships.empty() || m_count >= m_limit) {
        m_giveup = true;
        m_done = true;
        return false;
    }
    const bool gen = m_engine.gen_solution();
    m_engine.set_gen_solution(true);
    const lbool r = m_engine.enumerate(m_memberships, m_path, m_started);
    m_engine.set_gen_solution(gen);
    // A branch passed over undecided is one this enumeration will never report, so its
    // end no longer refutes anything.
    if (m_engine.m_had_undef || r == l_undef)
        m_giveup = true;
    if (r != l_true) {
        m_done = true;
        return false;
    }
    // Resume point of the branch just found.  Pinned here: the engine drops its own pins
    // on the next query from anybody else.
    m_path = m_engine.m_leaf_path;
    m_path_pin.reset();
    for (auto const& c : m_path) {
        m_path_pin.push_back(c.state);
        if (c.target)
            m_path_pin.push_back(c.target);
    }
    for (auto const& [var, views] : m_engine.solution())
        solution.insert(var, views);
    m_started = true;
    ++m_count;
    return true;
}

seq_monadic::iterator seq_monadic::iterate(unsigned limit) {
    return iterator(*this, m_memberships, limit);
}

lbool seq_monadic::solve(expr* term, expr* R) {
    m_core.reset();
    m_retry_disabled = false;
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
    // The intersection decomposition stays off here: it would run a refinement loop per
    // trial, and a trial it cannot decide only leaves more memberships in the core.
    flet<bool> _split(m_split_disabled, true);
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
    m_retry_disabled = false;
    lbool r = decide(m_memberships);
    if (r == l_false) {
        minimize_core(m_memberships);
        m_solution.reset();
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
        << "  :minimize-core " << (m_config.m_min_core ? "true" : "false") << "\n"
        << "  :last-result " << result_name(m_last_result) << "\n"
        << "  :budget " << m_budget << "\n"
        << "  :giveup " << (m_giveup ? "true" : "false") << "\n"
        << "  :sequence-sort ";

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
    out << ")\n  :solution (";
    for (auto const& [var, views] : m_solution) {
        out << "\n    ";
        display_expr(var);
        for (auto const& v : views) {
            out << "\n      ";
            display_expr(v.m_state);
            if (v.is_reach()) { out << " -> "; display_expr(v.m_target); }
            else out << " nullable";
        }
    }
    if (!m_solution.empty())
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
        for (seq::view const& c : m_groups[vi]) {
            out << "\n         ";
            display_expr(c.m_state);
            if (c.is_reach()) {
                out << " -> ";
                display_expr(c.m_target);
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
        "seq monadic bail budget",
        "seq monadic bail state expansion",
        "seq monadic bail resource",
        "seq monadic bail nullability",
        "seq monadic bail guard",
        "seq monadic bail not reversible",
        "seq monadic bail replay"
    };
    static_assert(sizeof(bail_names) / sizeof(bail_names[0]) ==
                  static_cast<unsigned>(bail_reason::num_reasons),
                  "bail_names must list every bail_reason");
    st.update("seq monadic cofactor calls", m_stats.m_cofactor_calls);
    st.update("seq monadic states", m_stats.m_states);
    st.update("seq monadic max state expansion", m_stats.m_max_state_expansion);
    st.update("seq monadic split calls", m_stats.m_split_calls);
    st.update("seq monadic split rounds", m_stats.m_split_rounds);
    st.update("seq monadic split decided", m_stats.m_split_decided);
    for (unsigned i = 0; i < static_cast<unsigned>(bail_reason::num_reasons); ++i)
        st.update(bail_names[i], m_stats.m_bails[i]);
}
