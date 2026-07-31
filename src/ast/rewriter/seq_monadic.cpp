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
- track unsat cores and expose them as explain functionality
- if perf suffers: use DFS backtracking search instead of DNF expansion (space overhead)
- create a validation harness: expose certificates for correctness that can be checked.
- extend with lower and upper bound constraints
- encapsulate within general interface:
create: undo_trail x dependency_manager x ast_manager -> regex_membership
add_constraint : expr* x expr* x dependency* -> void
add_lo: expr* x unsigned * dependency* -> void
add_hi: expr* x unsigned * dependency* ->void
check: void -> lbool
explain: void -> dependency*
model: void -> (expr* x expr*) vector or value: expr* -> expr* 
perhaps:
substitute: expr* x expr* x dependency* -> void

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/

#include "ast/rewriter/seq_monadic.h"
#include "ast/rewriter/seq_range_collapse.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include <set>
#include <vector>
#include <map>
#include <tuple>
#include <functional>
#include <algorithm>

namespace {

// A conjunction of derivative cofactor guards over the element variable v0 = (:var 0),
// interpreted as the set of element values satisfying it.  Two representations by
// element sort:
//   * character sort:  the exact, compact seq::range_predicate.
//   * any other sort:  the guard predicate kept symbolically and decided by a candidate
//     basis -- the element values mentioned in the guards, plus one fresh value.  This
//     is sound and complete for the {true,false,=,<=,and,or,not} grammar the derivatives
//     emit (over a general element sort only equalities appear).
class guard_set {
    ast_manager&         m;
    seq_util&            u;
    sort*                m_sort;
    expr*                m_v0;
    bool                 m_is_char;
    bool                 m_ok = true;      // false: an unsupported guard was conjoined
    seq::range_predicate m_rp;             // char representation
    expr_ref             m_guard;          // generic representation (conjunction over v0)

    // ---- generic path: candidate basis ----

    // element values compared to v0 by the equalities in `g`.
    void collect_consts(expr* g, ptr_vector<expr>& out) const {
        expr* a = nullptr, * b = nullptr;
        if (m.is_and(g) || m.is_or(g)) {
            for (expr* arg : *to_app(g)) collect_consts(arg, out);
            return;
        }
        if (m.is_not(g, a)) { collect_consts(a, out); return; }
        if (m.is_eq(g, a, b)) {
            if (a == m_v0 && b != m_v0) out.push_back(b);
            else if (b == m_v0 && a != m_v0) out.push_back(a);
        }
    }

    // evaluate `g` at v0 := cand ; l_undef on a construct outside the grammar.
    lbool eval_at(expr* g, expr* cand) const {
        expr* a = nullptr, * b = nullptr;
        if (m.is_true(g))  return l_true;
        if (m.is_false(g)) return l_false;
        if (m.is_not(g, a)) {
            lbool r = eval_at(a, cand);
            return r == l_undef ? l_undef : (r == l_true ? l_false : l_true);
        }
        if (m.is_and(g)) {
            lbool r = l_true;
            for (expr* arg : *to_app(g)) {
                lbool e = eval_at(arg, cand);
                if (e == l_false) return l_false;
                if (e == l_undef) r = l_undef;
            }
            return r;
        }
        if (m.is_or(g)) {
            lbool r = l_false;
            for (expr* arg : *to_app(g)) {
                lbool e = eval_at(arg, cand);
                if (e == l_true) return l_true;
                if (e == l_undef) r = l_undef;
            }
            return r;
        }
        if (m.is_eq(g, a, b)) {
            expr* other = (a == m_v0) ? b : (b == m_v0 ? a : nullptr);
            if (!other) return l_undef;
            if (other == m_v0) return l_true;
            return (cand == other) ? l_true : l_false;   // canonical values: identity == equality
        }
        return l_undef;
    }

    // a value of m_sort distinct from every element of `consts`, if one can be built.
    bool mk_fresh(ptr_vector<expr> const& consts, expr_ref& out) const {
        if (m.is_bool(m_sort)) {
            bool hasT = false, hasF = false;
            for (expr* c : consts) { if (m.is_true(c)) hasT = true; else if (m.is_false(c)) hasF = true; }
            if (!hasT) { out = m.mk_true();  return true; }
            if (!hasF) { out = m.mk_false(); return true; }
            return false;
        }
        arith_util a(m);
        if (a.is_int_real(m_sort)) {
            rational mx(0); bool any = false;
            for (expr* c : consts) {
                rational v;
                if (a.is_numeral(c, v)) { if (!any || v > mx) mx = v; any = true; }
            }
            out = a.mk_numeral(any ? mx + rational(1) : rational(0), a.is_int(m_sort));
            return true;
        }
        bv_util bv(m);
        if (bv.is_bv_sort(m_sort)) {
            unsigned sz = bv.get_bv_size(m_sort);
            for (unsigned k = 0; k <= consts.size(); ++k) {
                rational kv(k);
                bool clash = false;
                for (expr* c : consts) {
                    rational v; unsigned bsz = 0;
                    if (bv.is_numeral(c, v, bsz) && v == kv) { clash = true; break; }
                }
                if (!clash) { out = bv.mk_numeral(kv, sz); return true; }
            }
            return false;
        }
        return false;
    }

    lbool generic_eval(expr_ref* witness) const {
        ptr_vector<expr> consts;
        collect_consts(m_guard, consts);
        bool saw_undef = false;
        for (expr* c : consts) {
            lbool r = eval_at(m_guard, c);
            if (r == l_true) { if (witness) *witness = expr_ref(c, m); return l_true; }
            if (r == l_undef) saw_undef = true;
        }
        expr_ref fresh(m);
        if (mk_fresh(consts, fresh)) {
            lbool r = eval_at(m_guard, fresh);
            if (r == l_true) { if (witness) *witness = fresh; return l_true; }
            if (r == l_undef) saw_undef = true;
        }
        else
            saw_undef = true;   // the "distinct from all mentioned values" region is untested
        return saw_undef ? l_undef : l_false;
    }

public:
    guard_set(ast_manager& _m, seq_util& _u, sort* elem_sort, expr* v0)
        : m(_m), u(_u), m_sort(elem_sort), m_v0(v0),
          m_is_char(_u.is_char(elem_sort)),
          m_rp(_u.max_char()), m_guard(_m) {
        if (m_is_char) m_rp = seq::range_predicate::top(u.max_char());
        else           m_guard = m.mk_true();
    }

    bool ok() const { return m_ok; }

    // AND in a cofactor guard g (a Boolean over v0).
    void conjoin(expr* g) {
        if (!m_ok) return;
        if (m_is_char) {
            seq::range_predicate s(u.max_char());
            if (!seq::guard_to_range_predicate(u, m_v0, g, s)) { m_ok = false; return; }
            m_rp = m_rp & s;
        }
        else
            m_guard = m.mk_and(m_guard, g);
    }

    // l_false = empty, l_true = non-empty (sets *witness if non-null to a concrete
    // element of the set), l_undef = unknown / unsupported guard.
    lbool eval(expr_ref* witness) const {
        if (!m_ok) return l_undef;
        if (m_is_char) {
            if (m_rp.is_empty()) return l_false;
            if (witness) *witness = expr_ref(u.mk_char(m_rp[0].first), m);
            return l_true;
        }
        return generic_eval(witness);
    }
};

}

expr_ref seq_monadic::der_elem(expr* r, expr* elem) {
    expr_ref d = m_rw.mk_derivative(elem, r);   // mk_derivative(element, regex)
    // Normalize: for a general element sort the derivative by a non-matching constant can
    // leave a ground guard (e.g. (= 1 2)) unfolded; simplifying collapses such dead
    // branches to re.empty so nullability/emptiness stay decidable.
    expr_ref d2(m);
    m_thrw(d, d2);
    return d2;
}

void seq_monadic::derivative_cofactors(expr* r, expr_ref_pair_vector& result) {
    if (m_mode == transition_mode::light_antimirov)
        m_rw.light_ant_derivative_cofactors(r, result);
    else
        m_rw.brz_derivative_cofactors(r, result);
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
        derivative_cofactors(states.get(i), cof);
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

lbool seq_monadic::product_nonempty(svector<component> const& comps, expr_ref* witness_word) {
    unsigned n = comps.size();
    if (n == 0) {
        if (witness_word)
            *witness_word = expr_ref(u().str.mk_empty(m_seq_sort), m);
        return l_true;
    }
    expr_ref var0(m.mk_var(0, m_elem_sort), m);   // the element variable the guards range over

    svector<expr*> start;
    for (auto const& c : comps)
        start.push_back(c.state);

    auto id_key = [&](svector<expr*> const& st) {
        std::vector<unsigned> k;
        k.reserve(st.size());
        for (expr* e : st) k.push_back(e->get_id());
        return k;
    };
    typedef std::vector<unsigned> key;

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

    std::set<key> visited;
    std::vector<svector<expr*>> work;
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
        svector<expr*> st = work.back();
        work.pop_back();
        if (is_accept(st)) {
            if (witness_word)
                *witness_word = reconstruct(id_key(st));
            return l_true;
        }
        if (undecided)
            return l_undef;

        // per-component cofactor branches (target, guard); pin both, they outlive `cof`.
        std::vector<std::vector<std::pair<expr*, expr*>>> branches(n);
        for (unsigned i = 0; i < n; ++i) {
            expr_ref_pair_vector cof(m);
            derivative_cofactors(st[i], cof);
            for (auto const& [g, t] : cof) {
                if (re().is_empty(t)) continue;
                m_pin.push_back(t);
                m_pin.push_back(g);
                branches[i].push_back(std::make_pair((expr*) t, (expr*) g));
            }
        }

        // joint transitions = cartesian product of the branches with the guards
        // conjoined; prune as soon as the accumulated guard is empty, bail on unknown.
        svector<expr*> cur;
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
                                parent[ck] = std::make_pair(st_key, e.get());
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
        guard_set top(m, u(), m_elem_sort, var0);
        rec(0, top);
        if (bail)
            return l_undef;
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
        for (unsigned i = 0; i < s.length(); ++i) {
            expr* elem = u().str.mk_char(s, i);
            m_pin.push_back(elem);
            atoms.push_back(atom{ false, nullptr, elem });
        }
        return true;
    }
    if (u().str.is_unit(t)) {                     // seq.unit of a constant element
        expr* elem = to_app(t)->get_arg(0);
        if (m.is_value(elem)) {
            m_pin.push_back(elem);
            atoms.push_back(atom{ false, nullptr, elem });
            return true;
        }
        return false;                             // symbolic (non-constant) unit: unsupported
    }
    // uninterpreted 0-ary constant of sequence sort => a sequence variable
    if (is_app(t) && to_app(t)->get_num_args() == 0 &&
        to_app(t)->get_family_id() == null_family_id) {
        the_var = t;                              // mark that at least one variable occurs
        atoms.push_back(atom{ true, t, nullptr });
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
        expr_ref d = der_elem(R, a.elem);
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
    return solve(term, R, none, nullptr);
}

lbool seq_monadic::solve(expr* term, expr* R, obj_map<expr, expr*> const& var_extra) {
    return solve(term, R, var_extra, nullptr);
}

bool seq_monadic::build_membership_dnf(expr* term, expr* R, vector<disjunct>& dnf) {
    if (!u().is_re(R, m_seq_sort))
        return false;
    if (!u().is_seq(m_seq_sort, m_elem_sort))
        return false;
    svector<atom> atoms;
    expr* the_var = nullptr;
    if (!parse_term(term, atoms, the_var))
        return false;
    if (!the_var)
        return false;                             // no variable: ground membership, not our case
    m_pin.push_back(R);
    bool ok = true;
    decompose(atoms, 0, R, dnf, ok);
    return ok;
}

lbool seq_monadic::decide_dnf(vector<disjunct> const& dnf, obj_map<expr, expr*> const& var_extra,
                              obj_map<expr, expr*>* model) {
    bool any_undef = false;
    for (disjunct const& D : dnf) {
        // group components by variable, add the extra per-variable constraints
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
        for (auto const& kv : var_extra)
            groups[bucket(kv.m_key)].push_back(component{ kv.m_key, kv.m_value, nullptr });

        bool has_empty = false, has_undef = false;
        obj_map<expr, expr*> local;               // var -> witness for this disjunct
        for (unsigned gi = 0; gi < groups.size(); ++gi) {
            expr_ref w(m);
            lbool ne = product_nonempty(groups[gi], model ? &w : nullptr);
            if (ne == l_false) { has_empty = true; break; }   // this variable has no value
            if (ne == l_undef) { has_undef = true; continue; }
            if (model) { m_pin.push_back(w); local.insert(group_var[gi], w.get()); }
        }
        if (has_empty) continue;
        if (has_undef) { any_undef = true; continue; }
        if (model)
            for (auto const& kv : local)
                model->insert(kv.m_key, kv.m_value);
        return l_true;                            // all variables satisfiable => sat
    }
    return any_undef ? l_undef : l_false;
}

lbool seq_monadic::solve(expr* term, expr* R, obj_map<expr, expr*> const& var_extra,
                         obj_map<expr, expr*>* model) {
    m_pin.reset();
    m_budget = 200000;                            // global work budget: bail fast on DNF explosion
    m_giveup = false;
    vector<disjunct> dnf;
    if (!build_membership_dnf(term, R, dnf))
        return l_undef;
    return decide_dnf(dnf, var_extra, model);
}

lbool seq_monadic::solve_and(vector<std::pair<expr*, expr*>> const& mems,
                             obj_map<expr, expr*> const& var_extra, obj_map<expr, expr*>* model) {
    if (mems.empty())
        return l_undef;
    m_pin.reset();
    m_budget = 200000;
    m_giveup = false;
    // Multiply the per-membership DNFs:  combined = { d ++ e : d in combined, e in dnf_i }.
    // A variable shared by several memberships thus gets several components in the same
    // disjunct, which decide_dnf/product_nonempty intersect -- enforcing one consistent
    // value across all memberships (the joint solve the harness could not do per-term).
    vector<disjunct> combined;
    combined.push_back(disjunct());               // { true }
    const unsigned DNF_CAP = 1u << 14;
    for (auto const& tr : mems) {
        vector<disjunct> dnf_i;
        if (!build_membership_dnf(tr.first, tr.second, dnf_i))
            return l_undef;
        vector<disjunct> next;
        for (disjunct const& d : combined) {
            for (disjunct const& e : dnf_i) {
                if (next.size() > DNF_CAP || m_budget == 0) { m_giveup = true; return l_undef; }
                --m_budget;
                disjunct D(d);
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
    return decide_dnf(combined, var_extra, model);
}
