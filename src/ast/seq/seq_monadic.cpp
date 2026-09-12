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

#include "ast/seq/seq_monadic.h"
#include "ast/for_each_expr.h"
#include <set>
#include <vector>
#include <tuple>
#include <functional>
#include <algorithm>

namespace {

    char const *bail_name(unsigned i) {
        static char const *const names[] = {"unsupported", "state-cap",   "budget", "state-expansion",
                                            "resource",    "nullability", "guard",  "not-reversible"};
        return i < std::size(names) ? names[i] : "unknown";
    }

    void dedup_views(seq::view_vector const &g, seq::view_vector &out) {
        std::set<seq::view::sig> seen;
        for (auto const &c : g) {
            if (seen.insert(c.key()).second)
                out.push_back(c);
        }
    }
}  // namespace

namespace seq {

expr_ref monadic::der_elem(expr* r, expr* elem) {
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

lbool monadic::nullable(expr* r) {
    return m_view_witness.nullable(r);
}

bool monadic::out_of_budget() {
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

lbool monadic::product_nonempty(expr* var, seq::view_vector const& comps, expr_ref* witness_word) {
    return m_view_witness.product_nonempty(var, comps, witness_word);
}

bool monadic::parse_term(expr* t, vector<atom>& atoms) {
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

unsigned monadic::var_index(expr* v) {
    unsigned vi;
    if (m_var_idx.find(v, vi))
        return vi;
    vi = m_vars.size();
    m_var_idx.insert(v, vi);
    m_vars.push_back(v);
    m_groups.push_back(seq::view_vector());
    return vi;
}

void monadic::reset_search() {
    m_atoms.reset();
    m_regexes.reset();
    m_vars.reset();
    m_var_idx.reset();
    m_groups.reset();
    m_last_occ.reset();
    m_group_cache.clear();
    m_der_cache.reset();
    m_view_witness.reset_cache();
    m_undef_vars = 0;
    m_any_undef = false;
    m_live_states.reset();
    m_stack.reset();
    m_pos_mi = 0;
    m_pos_i = 0;
    m_pos_R = nullptr;
}

bool monadic::reverse_regex(expr* r, expr_ref& result) {
    result = expr_ref(re().mk_reverse(r), m);
    m_thrw(result, result);
    // A remaining re.reverse marks a subterm that seq_rewriter could not push through.
    for (auto e : subterms::ground(result))
        if (re().is_reverse(e))
            return false;
    return true;
}

expr_ref monadic::mk_rev_var(expr* v) {
    if (!m_rev_decl || m_rev_decl->get_range() != v->get_sort()) {
        sort *domain[1] = {v->get_sort()};
        m_rev_decl = m.mk_fresh_func_decl("rev", 1, domain, v->get_sort());
    }
    return expr_ref(m.mk_app(m_rev_decl, v), m);
}

expr* monadic::strip_rev_var(expr* v) const {
    if (m_rev_decl && is_app(v) && to_app(v)->get_decl() == m_rev_decl.get())
        return to_app(v)->get_arg(0);
    return v;
}

bool monadic::prepare(membership_vec const& memberships, bool reversed) {
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

lbool monadic::group_nonempty(unsigned vi) {
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
    if (r == l_undef) {
        switch (m_view_witness.get_failure_reason()) {
        case seq::view_failure_reason::state_expansion:
            m_stats.inc_bail(bail_reason::state_expansion);
            m_giveup = true;
            break;
        case seq::view_failure_reason::nullability:
            m_stats.inc_bail(bail_reason::nullability);
            break;
        case seq::view_failure_reason::guard:
            m_stats.inc_bail(bail_reason::guard);
            break;
        default:
            break;
        }
    }
    m_group_cache.emplace(sig, r);            // sig is m_sig_buf; emplace copies it
    return r;
}

lbool monadic::leaf() {
    if (m_giveup)
        return l_undef;                           // the search was already abandoned
    if (m_undef_vars > 0) {
        m_any_undef = true;
        return l_undef;                           // some variable's emptiness test gave up
    }
    if (!m_config.m_solution)
        return l_true;
    // Snapshot the branch: the next search, or the next pull of an `iterator`, unwinds
    // m_groups again.
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

lbool monadic::materialize(expr* var, expr_ref& word) {
    // without a completed search there is nothing recorded to collapse
    if (m_last_result != l_true)
        return l_undef;
    return materialize_recorded(var, word);
}

lbool monadic::materialize_recorded(expr* var, expr_ref& word, bool allow_unconstrained) {
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
        if (!allow_unconstrained)
            return l_undef;
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

lbool monadic::materialize_all(expr_substitution& model) {
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

void monadic::start_membership(unsigned mi) {
    m_pos_mi = mi;
    m_pos_i = 0;
    m_pos_R = mi == m_atoms.size() ? nullptr : m_regexes.get(mi);
}

lbool monadic::advance_pos() {
    while (true) {
        if (m_pos_mi == m_atoms.size())
            return l_true;
        if (out_of_budget())
            return l_undef;
        vector<atom> const& atoms = m_atoms[m_pos_mi];
        if (m_pos_i == atoms.size()) {
            // the rest of this membership is epsilon
            lbool nb = nullable(m_pos_R);
            if (nb == l_false)
                return l_false;
            if (nb == l_undef) {
                m_stats.inc_bail(bail_reason::nullability);
                return l_undef;
            }
            start_membership(m_pos_mi + 1);
            continue;
        }
        atom const& a = atoms[m_pos_i];
        if (a.is_var)
            return l_true;
        expr_ref d = der_elem(m_pos_R, a.elem.get());
        if (re().is_empty(d))
            return l_false;
        m_pin.push_back(d);
        m_pos_R = d;
        ++m_pos_i;
    }
}

bool monadic::push_frame() {
    if (m_pos_mi == m_atoms.size())
        return false;
    vector<atom> const& atoms = m_atoms[m_pos_mi];
    SASSERT(atoms[m_pos_i].is_var);
    expr* v = atoms[m_pos_i].var.get();
    uint64_t const pos = (static_cast<uint64_t>(m_pos_mi) << 32) | m_pos_i;
    uint64_t last = 0;
    m_stack.push_back(frame{ m_pos_mi, m_pos_i, m_pos_R, var_index(v),
                             m_last_occ.find(v, last) && last == pos,
                             m_pos_i + 1 == atoms.size() });
    return true;
}

bool monadic::commit_next(frame& f) {
    seq::view_vector& g = m_groups[f.vi];
    while (true) {
        expr* target = nullptr;
        if (f.last_atom) {
            if (f.next++ > 0)
                return false;
        }
        else {
            // Live states are consumed as they are produced, so a witness found early
            // leaves the rest of the reachable set unexpanded.
            auto live = m_live_states.reachable_live(seq::membership_view(f.R, m));
            target = live.at(f.next++);
            if (!target) {
                // Short of the full reachable set, running out of states refutes nothing.
                if (live.failed()) {
                    m_stats.inc_bail(
                        live.failure_reason() == seq::live_states::failure::state_cap ?
                        bail_reason::state_cap : bail_reason::resource);
                    m_any_undef = true;
                }
                return false;
            }
        }
        g.push_back(seq::view::reach(f.R, target, m));
        // Testing as soon as the group is complete, or holds several views, prunes the
        // whole subtree below.
        lbool ne;
        if (re().is_empty(f.R))
            ne = l_false;
        else if (f.finalize || g.size() > 1)
            ne = group_nonempty(f.vi);
        else
            ne = l_true;
        if (ne == l_false) {
            g.pop_back();
            continue;
        }
        // A last atom absorbs the rest of its membership, so it moves on to the next one
        // instead of testing the tail for nullability.
        if (f.last_atom)
            start_membership(f.mi + 1);
        else {
            m_pos_mi = f.mi;
            m_pos_i = f.i + 1;
            m_pos_R = target;
        }
        lbool adv = advance_pos();
        if (adv != l_true) {
            if (adv == l_undef)
                m_any_undef = true;
            g.pop_back();
            if (m_giveup)
                return false;
            continue;
        }
        f.undef = (ne == l_undef);
        if (f.undef)
            ++m_undef_vars;
        return true;
    }
}

lbool monadic::run_search(bool resume) {
    bool backtrack = resume;
    while (true) {
        if (m_giveup)
            return l_undef;                       // the tree below is unexplored: it
                                                  // neither proves nor refutes anything
        if (backtrack) {
            if (m_stack.empty())
                return m_any_undef ? l_undef : l_false;
            frame& f = m_stack.back();
            if (f.undef)
                --m_undef_vars;
            f.undef = false;
            m_groups[f.vi].pop_back();
            backtrack = false;                    // commit_next re-seats the position
        }
        else if (!push_frame()) {
            DEBUG_CODE({
                unsigned views = 0;
                for (seq::view_vector const& g : m_groups) {
                    views += g.size();
                }
                SASSERT(views == m_stack.size());   // exactly one view per frame
            });
            lbool r = leaf();
            if (r == l_true)
                return l_true;
            backtrack = true;
            continue;
        }
        if (!commit_next(m_stack.back())) {
            m_stack.pop_back();
            backtrack = true;
        }
    }
}

lbool monadic::decide_oriented(membership_vec const& memberships, bool reversed,
                                   unsigned budget) {
    m_solution.reset();
    ++m_search_gen;                               // any suspended iterator loses its stack
    reset_search();                               // clear the caches before dropping the
    m_pin.reset();                                // pins that keep their keys alive
    m_view_witness.reset_cache();
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
    else {
        // Seat the position on the first variable atom, consuming the leading constants,
        // and let the stack machine take it from there.
        start_membership(0);
        r = advance_pos();
        if (r == l_true)
            r = run_search(false);
    }
    if (r != l_true)
        m_solution.reset();
    return r;
}

bool monadic::constrains_length(expr* r) {
    return any_of(subterms::ground(expr_ref(r, m)), [&](expr* t) {
        unsigned lo = 0, hi = 0;
        expr* body = nullptr;
        return re().is_loop(t, body, lo, hi) && lo == hi && lo > 1;
    });
}

void monadic::split_conjuncts(expr* r, ptr_vector<expr>& out) {
    if (re().is_intersection(r)) {
        for (expr* arg : *to_app(r))
            split_conjuncts(arg, out);            // re.inter is n-ary and can nest
        return;
    }
    out.push_back(r);
}

bool monadic::instantiate_word(expr* t, ptr_vector<expr>& elems, bool subst) {
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
    if (materialize_recorded(t, w, false) != l_true) {
        m_split_words.insert(t, nullptr);         // remember the failure too
        return false;
    }
    m_pin.push_back(w);
    m_split_words.insert(t, w);
    return instantiate_word(w, elems, false);
}

lbool monadic::model_accepts(expr* term, expr* r) {
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

lbool monadic::decide_split(membership_vec const& memberships, unsigned budget,
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

lbool monadic::decide_policy(membership_vec const& memberships, unsigned budget, bool sticky) {
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

lbool monadic::decide(membership_vec const& memberships) {
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

lbool monadic::enumerate(membership_vec const& memberships, bool resume) {
    lbool r;
    if (resume) {
        m_budget = m_config.m_budget_limit;       // each pull gets its own allowance
        m_giveup = false;
        r = run_search(true);
        if (r != l_true)
            m_solution.reset();                   // do not leave the previous branch behind
    }
    else
        // Forward only: a reversed reading reports views over the reversed regexes, and
        // the retry policy would run two searches -- neither is a branch of the problem
        // the caller asked about.
        r = decide_oriented(memberships, false, m_config.m_budget_limit);
    m_last_search_memberships = memberships;
    m_last_search_result = r;
    m_last_result = r;    // a reported branch is materialize()-able, a drained one is not
    return r;
}

monadic::iterator::iterator(monadic& engine, membership_vec const& memberships,
                            unsigned limit) :
    m_engine(engine), m_memberships(memberships), m_limit(limit) {}

bool monadic::iterator::next(obj_map<expr, seq::view_vector>& solution) {
    solution.reset();
    if (m_done)
        return false;
    // An empty conjunction has no search to run, and anybody else's search has taken the
    // stack away.
    if (m_memberships.empty() || m_count >= m_limit ||
        (m_started && m_gen != m_engine.m_search_gen)) {
        m_giveup = true;
        m_done = true;
        return false;
    }
    const bool gen = m_engine.gen_solution();
    m_engine.set_gen_solution(true);
    const lbool r = m_engine.enumerate(m_memberships, m_started);
    m_engine.set_gen_solution(gen);
    // A branch passed over undecided is one this enumeration will never report.
    if (m_engine.m_any_undef || r == l_undef)
        m_giveup = true;
    if (r != l_true) {
        m_done = true;
        return false;
    }
    for (auto const& [var, views] : m_engine.solution())
        solution.insert(var, views);
    m_gen = m_engine.m_search_gen;
    m_started = true;
    ++m_count;
    return true;
}

monadic::iterator monadic::iterate(unsigned limit) {
    return iterator(*this, m_memberships, limit);
}

lbool monadic::solve(expr* term, expr* R) {
    m_core.reset();
    m_retry_disabled = false;
    membership_vec mv;
    mv.push_back({ expr_ref(term, m), expr_ref(R, m), nullptr });
    m_last_result = decide(mv);
    return m_last_result;
}

void monadic::add(expr* term, expr* regex, void* d) {
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

void monadic::set_term(void* d, expr* term) {
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

bool monadic::can_decide_term(expr* term) {
    vector<atom> atoms;
    return parse_term(term, atoms);
}

void monadic::add_lo(expr* term, unsigned lo, void* d) {
    if (lo == 0)
        return;
    sort* re_sort = re().mk_re(term->get_sort());
    expr_ref all_char(re().mk_full_char(re_sort), m);
    expr_ref prefix(re().mk_loop_proper(all_char, lo, lo), m);
    expr_ref all(re().mk_full_seq(re_sort), m);
    expr_ref regex(re().mk_concat(prefix, all), m);
    add(term, regex, d);
}

void monadic::add_hi(expr* term, unsigned hi, void* d) {
    sort* re_sort = re().mk_re(term->get_sort());
    expr_ref all_char(re().mk_full_char(re_sort), m);
    expr_ref regex(re().mk_loop_proper(all_char, 0, hi), m);
    add(term, regex, d);
}

void monadic::add_len(expr* term, unsigned len, void* d) {
    sort* re_sort = re().mk_re(term->get_sort());
    expr_ref all_char(re().mk_full_char(re_sort), m);
    expr_ref regex(re().mk_loop_proper(all_char, len, len), m);
    add(term, regex, d);
}


void monadic::minimize_core(membership_vec const& memberships) {
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

lbool monadic::check() {
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

std::ostream& monadic::display(std::ostream& out) const {
    auto display_expr = [&](expr* e) {
        if (e)
            out << mk_pp(e, m);
        else
            out << "null";
    };

    out << "(seq-monadic\n"
        << "  :mode " << transition_mode_name(m_config.m_mode) << "\n"
        << "  :minimize-core " << (m_config.m_min_core ? "true" : "false") << "\n"
        << "  :last-result " << m_last_result << "\n"
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
        << "    (:result " << m_last_search_result
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
        << "     :live-cache-size " << m_live_states.num_states() << "\n"
        << "     :pinned-expressions " << m_pin.size() << ")\n";

    out << "  :statistics\n"
        << "    (:cofactor-calls " << m_view_witness.cofactor_calls() << "\n"
        << "     :states " << m_stats.m_states + m_view_witness.states();
    for (unsigned i = 0; i < static_cast<unsigned>(bail_reason::num_reasons); ++i)
        out << "\n     :bail-" << bail_name(i) << " " << m_stats.m_bails[i];
    return out << "))\n";
}

void monadic::collect_statistics(::statistics& st) const {
    static char const* const bail_names[] = {
        "seq monadic bail unsupported",
        "seq monadic bail state cap",
        "seq monadic bail budget",
        "seq monadic bail state expansion",
        "seq monadic bail resource",
        "seq monadic bail nullability",
        "seq monadic bail guard",
        "seq monadic bail not reversible"
    };
    static_assert(sizeof(bail_names) / sizeof(bail_names[0]) ==
                  static_cast<unsigned>(bail_reason::num_reasons),
                  "bail_names must list every bail_reason");
    st.update("seq monadic cofactor calls", m_view_witness.cofactor_calls());
    st.update("seq monadic states", m_stats.m_states + m_view_witness.states());
    st.update("seq monadic max state expansion", m_view_witness.max_state_expansion());
    st.update("seq monadic split calls", m_stats.m_split_calls);
    st.update("seq monadic split rounds", m_stats.m_split_rounds);
    st.update("seq monadic split decided", m_stats.m_split_decided);
    for (unsigned i = 0; i < static_cast<unsigned>(bail_reason::num_reasons); ++i){
        st.update(bail_names[i], m_stats.m_bails[i]);
    }
}

}
