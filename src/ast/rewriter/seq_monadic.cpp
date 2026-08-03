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
- consider using expr_ref as alternative to pinned expressions
- revisit parse_term and "the_var" condition. A sequence of units should be allowed 
  even though a good solver will apply derivatives directly.
- optimize for cases where the same term is member of multiple regex constraints.
  - coallesce the membership constraints into a single regex membership constraint of the intersection of regexes.
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
#include <set>
#include <vector>
#include <map>
#include <tuple>
#include <functional>
#include <algorithm>
#include <unordered_set>


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
    if (m_nullable_cache.find(r, v))
        return v == 1 ? l_true : v == 0 ? l_false : l_undef;
    expr_ref nb = m_rw.is_nullable(r);
    lbool res = m.is_true(nb) ? l_true : m.is_false(nb) ? l_false : l_undef;
    m_pin.push_back(r);
    m_nullable_cache.insert(r, res == l_true ? 1 : res == l_false ? 0 : 2);
    return res;
}

expr_ref_pair_vector const& seq_monadic::derivative_cofactors(expr* r) {
    ++m_stats.m_cofactor_calls;
    expr_ref_pair_vector* v = nullptr;
    if (m_cofactors.find(r, v))
        return *v;
    ++m_stats.m_states;
    v = alloc(expr_ref_pair_vector, m);
    if (m_config.m_mode == transition_mode::light_antimirov)
        m_rw.light_ant_derivative_cofactors(r, *v);
    else
        m_rw.brz_derivative_cofactors(r, *v);
    m_cofactors.insert(r, v);              // takes ownership of v and pins the key r
    return *v;
}

bool seq_monadic::live_states(expr* R, expr_ref_vector& out) {
    obj_map<expr, unsigned> id;
    expr_ref_vector states(m);
    vector<svector<unsigned>> succ;
    bool_vector maybe_null;
    auto intern = [&](expr* s) -> unsigned {
        unsigned k;
        if (id.find(s, k)) return k;
        k = states.size();
        id.insert(s, k);
        states.push_back(s);
        succ.push_back(svector<unsigned>());
        maybe_null.push_back(nullable(s) != l_false);   // unknown nullability => keep (conservative)
        return k;
    };
    intern(R);
    const unsigned STATE_CAP = 1u << 12;
    for (unsigned i = 0; i < states.size(); ++i) {
        if (states.size() > STATE_CAP) {
            m_stats.inc_bail(bail_reason::state_cap);
            return false;
        }
        if (!m.inc()) {
            m_stats.inc_bail(bail_reason::resource);
            return false;
        }
        expr_ref_pair_vector const& cof = derivative_cofactors(states.get(i));
        for (auto const& [g, t] : cof) {
            if (re().is_empty(t)) continue;
            unsigned k = intern(t);           // MUST precede succ[i] indexing: intern may
            succ[i].push_back(k);             // grow (realloc) succ, invalidating succ[i]&
        }
    }
    unsigned n = states.size();
    bool_vector live;
    live.resize(n, false);
    for (unsigned i = 0; i < n; ++i)
        live[i] = maybe_null[i];
    for (bool ch = true; ch; ) {
        ch = false;
        for (unsigned i = 0; i < n; ++i)
            if (!live[i])
                for (unsigned j : succ[i])
                    if (live[j]) { live[i] = true; ch = true; break; }
    }
    for (unsigned i = 0; i < n; ++i)
        if (live[i]) { out.push_back(states.get(i)); m_pin.push_back(states.get(i)); }
    return true;
}

expr_ref_vector const* seq_monadic::live_states_cached(expr* R) {
    expr_ref_vector* v = nullptr;
    if (m_live_cache.find(R, v))
        return v;                          // may be null: previously gave up on R
    v = alloc(expr_ref_vector, m);
    if (!live_states(R, *v)) {
        dealloc(v);
        v = nullptr;
    }
    m_pin.push_back(R);                    // keep the key alive for the cache's lifetime
    m_live_cache.insert(R, v);
    return v;
}

void seq_monadic::reset_live_cache() {
    for (auto const& [k, v] : m_live_cache)
        dealloc(v);
    m_live_cache.reset();
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

        for (unsigned i = 0; i < n; ++i)
            branches[i] = &derivative_cofactors(st[i]);

        // joint transitions = cartesian product of the branches with the guards
        // conjoined; prune as soon as the accumulated guard is empty, bail on unknown.
        if (witness_word)
            st_key = fill_key(st);
        guard_set top(m, u(), m_elem_sort, var0, &m_rp_cache);
        rec(0, top);
        if (bail)
            return l_undef;
    }
    return l_false;
}

bool seq_monadic::parse_term(expr* t, vector<atom>& atoms, expr*& the_var) {
    if (u().str.is_concat(t))
        return all_of(*to_app(t), [&](expr* arg) { return parse_term(arg, atoms, the_var); });
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
        the_var = t;                              // mark that at least one variable occurs
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
    reset_live_cache();
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
        expr* the_var = nullptr;
        if (!parse_term(term, atoms, the_var)) {
            m_stats.inc_bail(bail_reason::unsupported);
            return false;
        }
        if (!the_var) {
            m_stats.inc_bail(bail_reason::unsupported);
            return false;                         // no variable: ground membership, not our case
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
    ptr_vector<expr> targets;
    if (last_atom)
        targets.push_back(nullptr);
    else {
        expr_ref_vector const* Q = live_states_cached(R);
        if (!Q)
            return l_undef;
        for (expr* q : *Q)
            targets.push_back(q);
    }

    unsigned vi = var_index(a.var.get());
    uint64_t pos = (static_cast<uint64_t>(mi) << 32) | i;
    uint64_t last = 0;
    bool finalize = m_last_occ.find(a.var.get(), last) && last == pos;
    bool any_undef = false;
    for (expr* target : targets) {
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
        if (r == l_true)
            return l_true;
        if (r == l_undef) {
            if (m_giveup)
                return l_undef;
            any_undef = true;
        }
    }
    return any_undef ? l_undef : l_false;
}

lbool seq_monadic::decide(membership_vec const& memberships) {
    m_model.reset();
    if (memberships.empty())
        return l_true;                            // empty conjunction is vacuously true
    reset_search();                               // clear the caches before dropping the
    m_pin.reset();                                // pins that keep their keys alive
    m_cofactors.maybe_reset(1u << 16);            // cofactors persist across calls (own their pins)
    m_rp_cache.maybe_reset(1u << 16);
    m_budget = 200000;
    m_giveup = false;
    if (!prepare(memberships))
        return l_undef;
    lbool r = dfs_membership(0);
    if (r != l_true)
        m_model.reset();
    return r;
}

lbool seq_monadic::solve(expr* term, expr* R) {
    membership_vec mv;
    mv.push_back({ expr_ref(term, m), expr_ref(R, m), nullptr });
    return decide(mv);
}

void seq_monadic::add(expr* term, expr* regex, void* d) {
    m_memberships.push_back({ expr_ref(term, m), expr_ref(regex, m), d });
    m_undo_trail.push(push_back_vector(m_memberships));
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
    if (r == l_false)
        minimize_core(m_memberships);
    return r;
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
