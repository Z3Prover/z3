/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_monadic.cpp

Abstract:

    Whole-language monadic decomposition for regex membership.  See seq_monadic.h.
    Automaton-based (product-reachability); reach(q) is never materialized as a regex.

    Generic in the element sort.  The decomposition, liveness and product-reachability
    are element-agnostic; only the *guard algebra* over the derivative cofactor guards
    depends on the element sort.  For the character sort it is the exact, compact
    seq::range_predicate; for any other element sort it is a candidate-basis over the
    element values mentioned by the guards (sound and complete for the
    {true,false,=,<=,and,or,not} grammar the derivatives emit).  The same guard algebra
    yields the concrete element used to build a witness sequence.

TODOs:
- if perf suffers: use DFS backtracking search instead of DNF expansion (space overhead)
- create a validation harness: expose certificates for correctness that can be checked.
- consider using expr_ref as alternative to pinned expressions
- revisit parse_term and "the_var" condition. A sequence of units should be allowed 
  even though a good solver will apply derivatives directly.
- optimize for cases where the same term is member of multiple regex constraints.
  - coallesce the membership constraints into a single regex membership constraint of the intersection of regexes.
- take into account shape of terms to prune the search space (e.g., if the term is xax, then retain the effect of 
  intersecting with .*a.*).
- use expr_ref in component and replace svector<component> by vector<component>, save on m_pin.
- support units of non-values (element variables).
  Model construction would assign values to the elements.
- make unsat core tracking less naive by tracking dependencies at a finer grain.
- add statistics and use it from src/smt/seq_regex.cpp when extracting statistics from theory_seq.
- add selective tracing TRACE(seq, ..).



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

expr_ref seq_monadic::der_elem(expr* r, expr* elem) {
    expr_ref d = m_rw.mk_derivative(elem, r);   // mk_derivative(element, regex)
    // Normalize: for a general element sort the derivative by a non-matching constant can
    // leave a ground guard (e.g. (= 1 2)) unfolded; simplifying collapses such dead
    // branches to re.empty so nullability/emptiness stay decidable.
    expr_ref d2(m);
    m_thrw(d, d2);
    return d2;
}

expr_ref_pair_vector const& seq_monadic::derivative_cofactors(expr* r) {
    expr_ref_pair_vector* v = nullptr;
    if (m_cofactors.find(r, v))
        return *v;
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
        expr_ref nb = m_rw.is_nullable(s);
        maybe_null.push_back(!m.is_false(nb));   // unknown nullability => keep (conservative)
        return k;
    };
    intern(R);
    const unsigned STATE_CAP = 1u << 12;
    for (unsigned i = 0; i < states.size(); ++i) {
        if (states.size() > STATE_CAP || !m.inc()) return false;
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

lbool seq_monadic::product_nonempty(svector<component> const& comps, expr_ref* witness_word) {
    unsigned n = comps.size();
    if (n == 0) {
        if (witness_word)
            *witness_word = expr_ref(u().str.mk_empty(m_seq_sort), m);
        return l_true;
    }
    expr_ref var0(m.mk_var(0, m_elem_sort), m);   // the element variable the guards range over

    ptr_vector<expr> start;
    for (auto const& c : comps)
        start.push_back(c.state);

    auto id_key = [&](ptr_vector<expr> const& st) {
        std::vector<unsigned> k;
        k.reserve(st.size());
        for (expr* e : st) k.push_back(e->get_id());
        return k;
    };
    typedef std::vector<unsigned> key;

    bool undecided = false;
    auto is_accept = [&](ptr_vector<expr> const& st) -> bool {
        for (unsigned i = 0; i < n; ++i) {
            if (comps[i].target) {
                if (st[i] != comps[i].target) return false;
            }
            else {
                expr_ref nb = m_rw.is_nullable(st[i]);
                if (m.is_true(nb)) continue;
                if (m.is_false(nb)) return false;
                undecided = true; return false;
            }
        }
        return true;
    };

    std::set<key> visited;
    vector<ptr_vector<expr>> work;
    // tree of first-discovery edges for witness reconstruction (only built when a
    // witness is requested): child-key -> (parent-key, element read on the edge).
    std::map<key, std::pair<key, expr*>> parent;
    key start_key = id_key(start);

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

    work.push_back(start);
    visited.insert(start_key);

    while (!work.empty()) {
        if (m_budget == 0) { m_giveup = true; return l_undef; }
        --m_budget;
        if (!m.inc())
            return l_undef;
        ptr_vector<expr> st = work.back();
        work.pop_back();
        if (is_accept(st)) {
            if (witness_word)
                *witness_word = reconstruct(id_key(st));
            return l_true;
        }
        if (undecided)
            return l_undef;

        // per-component cofactor branches (target, guard); expr_ref keeps both alive
        // beyond the cached `cof` reference.
        vector<vector<std::pair<expr_ref, expr_ref>>> branches;
        branches.resize(n);
        for (unsigned i = 0; i < n; ++i) {
            expr_ref_pair_vector const& cof = derivative_cofactors(st[i]);
            for (auto const& [g, t] : cof) {
                if (re().is_empty(t)) continue;
                branches[i].push_back({ expr_ref(t, m), expr_ref(g, m) });
            }
        }

        // joint transitions = cartesian product of the branches with the guards
        // conjoined; prune as soon as the accumulated guard is empty, bail on unknown.
        ptr_vector<expr> cur;
        cur.resize(n);
        key st_key = id_key(st);
        bool bail = false;
        std::function<void(unsigned, guard_set const&)> rec =
            [&](unsigned i, guard_set const& acc) {
                if (bail) return;
                if (i == n) {
                    key ck = id_key(cur);
                    if (visited.find(ck) == visited.end()) {
                        visited.insert(ck);
                        if (witness_word) {
                            expr_ref e(m);
                            if (acc.eval(&e) == l_true) {
                                m_pin.push_back(e);
                                parent[ck] = { st_key, e.get() };
                            }
                        }
                        work.push_back(cur);
                    }
                    return;
                }
                for (auto const& pr : branches[i]) {
                    guard_set nacc = acc;
                    nacc.conjoin(pr.second);
                    lbool ne = nacc.eval(nullptr);
                    if (ne == l_undef) { bail = true; return; }   // non-range / unknown guard
                    if (ne == l_false) continue;                  // empty joint guard: prune
                    cur[i] = pr.first;
                    rec(i + 1, nacc);
                    if (bail) return;
                }
            };
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

bool seq_monadic::decompose(vector<atom> const& atoms, unsigned i, expr* R,
                            vector<disjunct>& out) {
    if (m_giveup)
        return false;
    m_pin.push_back(R);
    if (i == atoms.size()) {
        expr_ref nb = m_rw.is_nullable(R);
        if (m.is_true(nb))
            out.push_back(disjunct());            // empty conjunction = true
        else if (!m.is_false(nb))
            return false;                         // undecidable nullability => bail
        return true;
    }
    atom const& a = atoms[i];
    if (!a.is_var) {
        expr_ref d = der_elem(R, a.elem.get());
        return decompose(atoms, i + 1, d, out);
    }
    if (i + 1 == atoms.size()) {                  // last atom: membership component  a.var in R
        disjunct D;
        D.push_back(component{ a.var.get(), R, nullptr });
        out.push_back(D);
        return true;
    }
    // a variable with a non-empty rest: split over the live states q of R (midpoints)
    expr_ref_vector Q(m);
    if (!live_states(R, Q))
        return false;
    const unsigned DISJUNCT_CAP = 1u << 13;
    for (expr* q : Q) {
        vector<disjunct> sub;
        if (!decompose(atoms, i + 1, q, sub))
            return false;
        for (disjunct const& sd : sub) {
            if (out.size() > DISJUNCT_CAP || m_budget == 0) { m_giveup = true; return false; }
            --m_budget;
            disjunct D(sd);
            D.push_back(component{ a.var.get(), R, q });   // reach component: a.var drives R -> q
            out.push_back(D);
        }
    }
    simplify_dnf(out);
    return true;
}

void seq_monadic::simplify_dnf(vector<disjunct>& dnf) {
    std::set<std::vector<std::tuple<unsigned, unsigned, unsigned>>> seen;
    vector<disjunct> result;
    for (disjunct const& D : dnf) {
        bool dead = false;
        for (auto const& c : D)
            if (re().is_empty(c.state)) { dead = true; break; }
        if (dead)
            continue;
        std::vector<std::tuple<unsigned, unsigned, unsigned>> sig;
        sig.reserve(D.size());
        for (auto const& c : D)
            sig.push_back(std::make_tuple(c.var->get_id(), c.state->get_id(),
                                          c.target ? c.target->get_id() : UINT_MAX));
        std::sort(sig.begin(), sig.end());
        if (seen.insert(sig).second)
            result.push_back(D);
    }
    dnf.swap(result);
}

lbool seq_monadic::solve(expr* term, expr* R) {
    m_pin.reset();
    m_cofactors.maybe_reset(1u << 16);
    m_rp_cache.maybe_reset(1u << 16);
    m_budget = 200000;                            // global work budget: bail fast on DNF explosion
    m_giveup = false;
    vector<disjunct> dnf;
    if (!build_membership_dnf(term, R, dnf))
        return l_undef;
    return decide_dnf(dnf);
}

bool seq_monadic::build_membership_dnf(expr* term, expr* R, vector<disjunct>& dnf) {
    if (!u().is_re(R, m_seq_sort))
        return false;
    if (!u().is_seq(m_seq_sort, m_elem_sort))
        return false;
    vector<atom> atoms;
    expr* the_var = nullptr;
    if (!parse_term(term, atoms, the_var))
        return false;
    if (!the_var)
        return false;                             // no variable: ground membership, not our case
    m_pin.push_back(R);
    return decompose(atoms, 0, R, dnf);
}

lbool seq_monadic::decide_dnf(vector<disjunct> const& dnf) {
    m_model.reset();
    bool any_undef = false;
    for (disjunct const& D : dnf) {
        // group components by variable
        obj_map<expr, unsigned> idx;
        vector<svector<component>> groups;
        ptr_vector<expr> group_var;
        auto bucket = [&](expr* v) -> unsigned {
            unsigned gi;
            if (idx.find(v, gi)) return gi;
            gi = groups.size(); idx.insert(v, gi);
            groups.push_back(svector<component>());
            group_var.push_back(v);
            return gi;
        };
        for (auto const& c : D)
            groups[bucket(c.var)].push_back(c);

        bool has_empty = false, has_undef = false;
        obj_map<expr, expr*> local;               // var -> witness for this disjunct
        for (unsigned gi = 0; gi < groups.size(); ++gi) {
            expr_ref w(m);
            lbool ne = product_nonempty(groups[gi], m_config.m_model ? &w : nullptr);
            if (ne == l_false) { has_empty = true; break; }   // this variable has no value
            if (ne == l_undef) { has_undef = true; continue; }
            if (m_config.m_model) { m_pin.push_back(w); local.insert(group_var[gi], w.get()); }
        }
        if (has_empty) continue;
        if (has_undef) { any_undef = true; continue; }
        if (m_config.m_model)
            for (auto const& [k, v] : local)
                m_model.insert(k, v);
        return l_true;                            // all variables satisfiable => sat
    }
    return any_undef ? l_undef : l_false;
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

lbool seq_monadic::decide(membership_vec const& memberships) {
    m_model.reset();
    if (memberships.empty())
        return l_true;                            // empty conjunction is vacuously true
    m_pin.reset();
    m_cofactors.maybe_reset(1u << 16);
    m_rp_cache.maybe_reset(1u << 16);
    m_budget = 200000;
    m_giveup = false;
    // Multiply the per-membership DNFs:  combined = { d ++ e : d in combined, e in dnf_i }.
    // A variable shared by several memberships thus gets several components in the same
    // disjunct, which decide_dnf/product_nonempty intersect -- enforcing one consistent
    // value across all memberships (the joint solve the harness could not do per-term).
    vector<disjunct> combined;
    combined.push_back(disjunct());               // { true }
    const unsigned DNF_CAP = 1u << 14;
    for (auto const& [term, regex, d] : memberships) {
        vector<disjunct> dnf_i;
        if (!build_membership_dnf(term, regex, dnf_i))
            return l_undef;
        vector<disjunct> next;
        for (disjunct const& cd : combined) {
            for (disjunct const& e : dnf_i) {
                if (next.size() > DNF_CAP || m_budget == 0) { m_giveup = true; return l_undef; }
                --m_budget;
                disjunct D(cd);
                for (auto const& c : e)
                    D.push_back(c);
                next.push_back(D);
            }
        }
        combined.swap(next);
        simplify_dnf(combined);
        if (combined.empty())
            return l_false;                       // no viable disjunct left => unsat
    }
    return decide_dnf(combined);
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
