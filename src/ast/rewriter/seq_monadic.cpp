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
    m_cursors.reset();
    m_last_var = UINT_MAX;
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

// ---- state-based search driver ------------------------------------------------------
//
// This is an alternative to the strictly positional dfs_membership/dfs_atoms above.  The
// positional search finishes membership 0 entirely, then membership 1, and so on, so two
// memberships that share a variable only intersect that variable's components deep in the
// tree -- after the first membership's alignment was chosen blindly.  The state-based
// search keeps a *cursor* per membership and, at each step, expands ONE variable across
// ALL memberships whose current head is that variable, intersecting the per-variable
// components (m_groups) immediately.  An infeasible choice for a shared variable is thus
// pruned as soon as it is made, rather than after committing to a full membership.
//
// A search state is:
//   - the set of active (non-complete) cursors      == active membership constraints,
//   - the per-variable component groups (m_groups)  == variable intersection constraints,
//   - the last expanded variable (m_last_var)       == locality hint for the next choice.
// Every non-complete cursor has a variable head (leading constants are eagerly consumed by
// advance_cursor / initial_normalize).  The state is complete when every cursor is
// complete, and accepting when additionally every variable group is non-empty.

lbool seq_monadic::advance_cursor(cursor& c, unsigned mi, expr* target) {
    vector<atom> const& atoms = m_atoms[mi];
    // Step past the head variable.  target == null encodes "the variable is the last atom",
    // i.e. a plain membership component: nothing follows, the cursor is complete.
    if (!target) {
        c.i = atoms.size();
        c.complete = true;
        return l_true;
    }
    c.i += 1;
    c.R = target;
    // Eagerly consume the constant atoms following the variable (mirrors dfs_atoms walking
    // a run of constants via der_elem), so that the cursor again exposes a variable head.
    while (c.i < atoms.size() && !atoms[c.i].is_var) {
        expr_ref d = der_elem(c.R, atoms[c.i].elem.get());
        if (re().is_empty(d))
            return l_false;                       // dead: this continuation is empty
        m_pin.push_back(d);
        c.R = d;
        c.i += 1;
    }
    if (c.i == atoms.size()) {                     // the remaining tail is epsilon
        c.complete = true;
        lbool nb = nullable(c.R);
        if (nb == l_false)
            return l_false;
        if (nb == l_undef) {
            m_stats.inc_bail(bail_reason::nullability);
            return l_undef;                        // tail nullability undecidable
        }
        return l_true;
    }
    c.complete = false;                            // stopped on a variable head
    return l_true;
}

lbool seq_monadic::initial_normalize() {
    for (unsigned mi = 0; mi < m_cursors.size(); ++mi) {
        cursor& c = m_cursors[mi];
        vector<atom> const& atoms = m_atoms[mi];
        while (c.i < atoms.size() && !atoms[c.i].is_var) {
            expr_ref d = der_elem(c.R, atoms[c.i].elem.get());
            if (re().is_empty(d))
                return l_false;                    // this membership is already empty
            m_pin.push_back(d);
            c.R = d;
            c.i += 1;
        }
        // prepare() guarantees every membership has a variable, so c.i now points at a
        // variable head (c.complete stays false).  A membership of only constants would
        // have been rejected by prepare().
        c.complete = (c.i == atoms.size());
        if (c.complete) {
            // Defensive: no variable head (shouldn't happen); require the tail nullable.
            lbool nb = nullable(c.R);
            if (nb == l_false)
                return l_false;
            if (nb == l_undef)
                ++m_undef_vars;
        }
    }
    return l_true;
}

lbool seq_monadic::accept_state() {
    if (m_undef_vars > 0)
        return l_undef;                            // some group / tail nullability gave up
    if (!m_config.m_model)
        return l_true;                             // groups already shown non-empty
    m_model.reset();
    for (unsigned vi = 0; vi < m_groups.size(); ++vi) {
        if (m_groups[vi].empty())
            continue;
        expr_ref w(m);
        lbool ne = product_nonempty(m_groups[vi], &w);
        if (ne != l_true) {
            m_model.reset();
            return ne;
        }
        m_pin.push_back(w);
        m_model.insert(m_vars[vi], w.get());
    }
    return l_true;
}

lbool seq_monadic::search() {
    if (m_giveup)
        return l_undef;
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

    // Gather the head variables of the active cursors and how often each occurs as a head.
    unsigned best_vi = UINT_MAX, best_cnt = 0;
    obj_map<expr, unsigned> head_cnt;
    for (unsigned mi = 0; mi < m_cursors.size(); ++mi) {
        cursor const& c = m_cursors[mi];
        if (c.complete)
            continue;
        expr* v = m_atoms[mi][c.i].var.get();
        unsigned cnt = 0;
        head_cnt.find(v, cnt);
        head_cnt.insert(v, ++cnt);
        unsigned vi = m_var_idx[v];
        // Prefer the most frequent head variable; break ties toward the smallest index so
        // the choice is deterministic.  m_last_var (locality) is applied afterwards.
        if (cnt > best_cnt || (cnt == best_cnt && (best_vi == UINT_MAX || vi < best_vi))) {
            best_cnt = cnt;
            best_vi = vi;
        }
    }
    if (best_vi == UINT_MAX)
        return accept_state();                     // every cursor complete

    // Locality: if the last expanded variable is still an active head, expand it next --
    // its freshly chosen continuation can be checked against the intersection immediately.
    unsigned vi = best_vi;
    if (m_last_var != UINT_MAX && m_last_var < m_vars.size()) {
        unsigned lc = 0;
        if (head_cnt.find(m_vars[m_last_var], lc) && lc > 0)
            vi = m_last_var;
    }

    // All cursors whose current head is variable vi are expanded together at this step.
    svector<unsigned> S;
    expr* vv = m_vars[vi];
    for (unsigned mi = 0; mi < m_cursors.size(); ++mi) {
        cursor const& c = m_cursors[mi];
        if (!c.complete && m_atoms[mi][c.i].var.get() == vv)
            S.push_back(mi);
    }
    return choose_cont(vi, S, 0);
}

lbool seq_monadic::choose_cont(unsigned vi, svector<unsigned> const& S, unsigned k) {
    if (m_giveup)
        return l_undef;
    if (k == S.size()) {
        unsigned saved = m_last_var;
        m_last_var = vi;
        lbool r = search();
        m_last_var = saved;
        return r;
    }
    unsigned mi = S[k];
    cursor& c = m_cursors[mi];
    vector<atom> const& atoms = m_atoms[mi];
    expr* R = c.R;
    uint64_t pos = (static_cast<uint64_t>(mi) << 32) | c.i;
    uint64_t last = 0;
    bool finalize = m_last_occ.find(atoms[c.i].var.get(), last) && last == pos;
    bool last_atom = (c.i + 1 == atoms.size());

    // Enumerate this cursor's continuations for variable vi: a plain membership (null) when
    // the variable is the last atom, otherwise every live reach target of R.
    ptr_vector<expr> targets;
    if (last_atom)
        targets.push_back(nullptr);
    else {
        expr_ref_vector const* Q = live_states_cached(R);
        if (!Q)
            return l_undef;                        // gave up enumerating targets
        for (expr* q : *Q)
            targets.push_back(q);
    }

    bool any_undef = false;
    for (expr* target : targets) {
        m_groups[vi].push_back(component{ atoms[c.i].var.get(), R, target });
        // Intersect immediately: prune as soon as vi's accumulated components are empty.
        // The test is forced once the group is complete (past vi's last occurrence) so the
        // accepting state does not need to re-verify; running it earlier (size > 1) prunes.
        lbool ne;
        if (re().is_empty(R))
            ne = l_false;
        else if (finalize || m_groups[vi].size() > 1)
            ne = group_nonempty(vi);
        else
            ne = l_true;
        if (ne == l_false) {
            m_groups[vi].pop_back();
            continue;                              // infeasible continuation for vi: prune
        }
        cursor saved = c;                          // save/restore cursor across the branch
        lbool adv = advance_cursor(c, mi, target);
        if (adv == l_false) {
            c = saved;
            m_groups[vi].pop_back();
            continue;
        }
        unsigned undef_here = (ne == l_undef ? 1u : 0u) + (adv == l_undef ? 1u : 0u);
        m_undef_vars += undef_here;
        lbool r = choose_cont(vi, S, k + 1);
        m_undef_vars -= undef_here;
        c = saved;
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
    lbool r;
    if (m_config.m_state_search) {
        // Build one cursor per membership at its regex start; initial_normalize consumes
        // leading constants so every active cursor exposes a variable head.
        m_cursors.reset();
        for (unsigned mi = 0; mi < m_atoms.size(); ++mi)
            m_cursors.push_back(cursor{ 0, m_regexes.get(mi), false });
        m_last_var = UINT_MAX;
        lbool norm = initial_normalize();
        r = (norm == l_false) ? l_false : search();
    }
    else
        r = dfs_membership(0);
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
