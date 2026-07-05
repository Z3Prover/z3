/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_monadic.cpp

Abstract:

    Whole-language monadic decomposition for regex membership.  See seq_monadic.h.
    Automaton-based (product-reachability); minterm-free; reach(q) is never materialized
    as a regex.

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/

#include "ast/rewriter/seq_monadic.h"
#include <set>
#include <vector>
#include <tuple>
#include <functional>
#include <algorithm>

// Cofactor guard `pred` (a Boolean over the character x = (:var 0)) -> the canonical
// range_predicate of the characters satisfying it.  Returns false on a construct outside
// {true,false,and,or,not,=,char.<=} over x (then the product engine bails to l_undef).
static bool guard_to_rp(ast_manager& m, seq_util& sq, expr* x, expr* pred,
                        unsigned maxc, seq::range_predicate& out) {
    expr* a = nullptr, * b = nullptr; unsigned c = 0;
    if (m.is_true(pred))  { out = seq::range_predicate::top(maxc);   return true; }
    if (m.is_false(pred)) { out = seq::range_predicate::empty(maxc); return true; }
    if (m.is_eq(pred, a, b)) {
        if (a == x && sq.is_const_char(b, c)) { out = seq::range_predicate::singleton(c, maxc); return true; }
        if (b == x && sq.is_const_char(a, c)) { out = seq::range_predicate::singleton(c, maxc); return true; }
        return false;
    }
    if (sq.is_char_le(pred, a, b)) {
        if (b == x && sq.is_const_char(a, c)) { out = seq::range_predicate::range(c, maxc, maxc); return true; }
        if (a == x && sq.is_const_char(b, c)) { out = seq::range_predicate::range(0, c, maxc);    return true; }
        return false;
    }
    if (m.is_not(pred, a)) {
        seq::range_predicate s(maxc);
        if (!guard_to_rp(m, sq, x, a, maxc, s)) return false;
        out = ~s; return true;
    }
    if (m.is_and(pred)) {
        out = seq::range_predicate::top(maxc);
        for (expr* arg : *to_app(pred)) {
            seq::range_predicate s(maxc);
            if (!guard_to_rp(m, sq, x, arg, maxc, s)) return false;
            out = out & s;
        }
        return true;
    }
    if (m.is_or(pred)) {
        out = seq::range_predicate::empty(maxc);
        for (expr* arg : *to_app(pred)) {
            seq::range_predicate s(maxc);
            if (!guard_to_rp(m, sq, x, arg, maxc, s)) return false;
            out = out | s;
        }
        return true;
    }
    return false;
}

expr_ref seq_monadic::der_char(expr* r, unsigned ch) {
    expr_ref c(u().mk_char(ch), m);
    return m_rw.mk_derivative(c, r);   // mk_derivative(element, regex)
}

void seq_monadic::live_states(expr* R, ptr_vector<expr>& out, bool& ok) {
    ok = true;
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
        if (states.size() > STATE_CAP || !m.inc()) { ok = false; return; }
        expr_ref_pair_vector cof(m);
        m_rw.brz_derivative_cofactors(states.get(i), cof);
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
}

lbool seq_monadic::product_nonempty(svector<component> const& comps) {
    unsigned n = comps.size();
    if (n == 0)
        return l_true;
    unsigned maxc = u().max_char();
    sort* cs = u().mk_char_sort();
    expr_ref var0(m.mk_var(0, cs), m);       // the character variable the guards range over

    svector<expr*> start;
    for (auto const& c : comps)
        start.push_back(c.state);

    auto id_key = [&](svector<expr*> const& st) {
        std::vector<unsigned> k;
        k.reserve(st.size());
        for (expr* e : st) k.push_back(e->get_id());
        return k;
    };
    bool undecided = false;
    auto is_accept = [&](svector<expr*> const& st) -> bool {
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

    std::set<std::vector<unsigned>> visited;
    std::vector<svector<expr*>> work;
    work.push_back(start);
    visited.insert(id_key(start));

    while (!work.empty()) {
        if (m_budget == 0) { m_giveup = true; return l_undef; }
        --m_budget;
        if (!m.inc())
            return l_undef;
        svector<expr*> st = work.back();
        work.pop_back();
        if (is_accept(st))
            return l_true;
        if (undecided)
            return l_undef;
        // per-component cofactor branches, guards converted to range_predicates
        std::vector<std::vector<std::pair<expr*, seq::range_predicate>>> branches(n);
        for (unsigned i = 0; i < n; ++i) {
            expr_ref_pair_vector cof(m);
            m_rw.brz_derivative_cofactors(st[i], cof);
            for (auto const& [g, t] : cof) {
                if (re().is_empty(t)) continue;
                seq::range_predicate rp(maxc);
                if (!guard_to_rp(m, u(), var0, g, maxc, rp))
                    return l_undef;              // non-range guard: bail (sound)
                m_pin.push_back(t);              // keep the derivative target alive
                branches[i].push_back(std::make_pair((expr*) t, rp));
            }
        }
        // joint transitions = cartesian product of the branches with the guards
        // conjoined; prune as soon as the accumulated guard range is empty.
        svector<expr*> cur;
        cur.resize(n);
        std::function<void(unsigned, seq::range_predicate const&)> rec =
            [&](unsigned i, seq::range_predicate const& acc) {
                if (i == n) {
                    auto k = id_key(cur);
                    if (visited.find(k) == visited.end()) {
                        visited.insert(k);
                        work.push_back(cur);
                    }
                    return;
                }
                for (auto const& pr : branches[i]) {
                    seq::range_predicate nacc = acc & pr.second;
                    if (nacc.is_empty()) continue;
                    cur[i] = pr.first;
                    rec(i + 1, nacc);
                }
            };
        rec(0, seq::range_predicate::top(maxc));
    }
    return l_false;
}

bool seq_monadic::parse_term(expr* t, svector<atom>& atoms, expr*& the_var) {
    if (u().str.is_concat(t)) {
        app* a = to_app(t);
        for (unsigned i = 0; i < a->get_num_args(); ++i)
            if (!parse_term(a->get_arg(i), atoms, the_var))
                return false;
        return true;
    }
    if (u().str.is_empty(t))
        return true;                              // epsilon: contributes nothing
    zstring s;
    if (u().str.is_string(t, s)) {
        for (unsigned i = 0; i < s.length(); ++i)
            atoms.push_back(atom{ false, nullptr, s[i] });
        return true;
    }
    if (u().str.is_unit(t)) {
        expr* ch = to_app(t)->get_arg(0);
        unsigned cv = 0;
        if (u().is_const_char(ch, cv)) {
            atoms.push_back(atom{ false, nullptr, cv });
            return true;
        }
        return false;                             // symbolic (non-constant) unit: unsupported
    }
    // uninterpreted 0-ary constant of sequence sort => a string variable
    if (is_app(t) && to_app(t)->get_num_args() == 0 &&
        to_app(t)->get_family_id() == null_family_id) {
        the_var = t;                              // mark that at least one variable occurs
        atoms.push_back(atom{ true, t, 0 });
        return true;
    }
    return false;
}

void seq_monadic::decompose(svector<atom> const& atoms, unsigned i, expr* R,
                            vector<disjunct>& out, bool& ok) {
    if (!ok)
        return;
    if (m_giveup) { ok = false; return; }
    m_pin.push_back(R);
    if (i == atoms.size()) {
        expr_ref nb = m_rw.is_nullable(R);
        if (m.is_true(nb))
            out.push_back(disjunct());            // empty conjunction = true
        else if (!m.is_false(nb))
            ok = false;                           // undecidable nullability => bail
        return;
    }
    atom const& a = atoms[i];
    if (!a.is_var) {
        expr_ref d = der_char(R, a.ch);
        decompose(atoms, i + 1, d, out, ok);
        return;
    }
    if (i + 1 == atoms.size()) {                  // last atom: membership component  a.var in R
        disjunct D;
        D.push_back(component{ a.var, R, nullptr });
        out.push_back(D);
        return;
    }
    // a variable with a non-empty rest: split over the live states q of R (midpoints)
    ptr_vector<expr> Q;
    live_states(R, Q, ok);
    if (!ok)
        return;
    const unsigned DISJUNCT_CAP = 1u << 13;
    for (expr* q : Q) {
        vector<disjunct> sub;
        decompose(atoms, i + 1, q, sub, ok);
        if (!ok)
            return;
        for (disjunct const& sd : sub) {
            if (out.size() > DISJUNCT_CAP || m_budget == 0) { m_giveup = true; ok = false; return; }
            --m_budget;
            disjunct D(sd);
            D.push_back(component{ a.var, R, q });   // reach component: a.var drives R -> q
            out.push_back(D);
        }
    }
    simplify_dnf(out);
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
    obj_map<expr, expr*> none;
    return solve(term, R, none);
}

lbool seq_monadic::solve(expr* term, expr* R, obj_map<expr, expr*> const& var_extra) {
    if (!u().is_re(R, m_seq_sort))
        return l_undef;
    svector<atom> atoms;
    expr* the_var = nullptr;
    if (!parse_term(term, atoms, the_var))
        return l_undef;
    if (!the_var)
        return l_undef;                           // no variable: ground membership, not our case
    m_pin.reset();
    m_pin.push_back(R);
    m_budget = 200000;                            // global work budget: bail fast on DNF explosion
    m_giveup = false;
    bool ok = true;
    vector<disjunct> dnf;
    decompose(atoms, 0, R, dnf, ok);
    if (!ok)
        return l_undef;

    bool any_undef = false;
    for (disjunct const& D : dnf) {
        // group components by variable, add the extra per-variable constraints
        obj_map<expr, unsigned> idx;
        vector<svector<component>> groups;
        auto bucket = [&](expr* v) -> unsigned {
            unsigned gi;
            if (idx.find(v, gi)) return gi;
            gi = groups.size(); idx.insert(v, gi); groups.push_back(svector<component>());
            return gi;
        };
        for (auto const& c : D)
            groups[bucket(c.var)].push_back(c);
        for (auto const& kv : var_extra)
            groups[bucket(kv.m_key)].push_back(component{ kv.m_key, kv.m_value, nullptr });

        bool has_empty = false, has_undef = false;
        for (auto const& g : groups) {
            lbool ne = product_nonempty(g);
            if (ne == l_false) { has_empty = true; break; }   // this variable has no value
            if (ne == l_undef) has_undef = true;
        }
        if (has_empty) continue;
        if (has_undef) { any_undef = true; continue; }
        return l_true;                            // all variables satisfiable => sat
    }
    return any_undef ? l_undef : l_false;
}
