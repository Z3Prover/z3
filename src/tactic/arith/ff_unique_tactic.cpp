/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_unique_tactic.cpp

Abstract:

    Uniqueness propagation for prime-field goals ("ff-unique").

    Circuit determinism and equivalence queries assert two copies of the same
    constraint system with equal inputs and ask whether some output can
    differ. Such queries are decided by functional-dependency reasoning long
    before any Groebner basis is needed:

      * a constraint a*y + r = 0, where y occurs once, linearly, with a
        constant a != 0, defines y := -r/a. Two definitions whose right-hand
        sides coincide once every variable is replaced by its class
        representative (and known constants are substituted) force equal
        left-hand sides, so the classes are merged;
      * a Boolean decomposition sum_i c*2^e_i*b_i + r = 0, with b_i*b_i = b_i,
        distinct e_i and 2^(max e_i + 1) <= p, has no modular wrap-around,
        so each b_i is the e_i-th binary digit of -r/c and is merged the
        same way;
      * a constraint reduced to a single linear occurrence of a class fixes
        its value; a constraint reduced to a non-zero constant, a merge of
        two different values, or an asserted disequality whose two sides
        coincide closes the branch.

    When propagation stalls, the tactic splits on a Boolean class (both
    values), up to a bounded depth and node budget. UNSAT is reported only
    if every branch closes. Otherwise the goal is returned unchanged, plus
    the equalities derived at the root, which are consequences of the goal.

    Every step is a local implication between a few asserted constraints and
    previously derived equalities; this is the shape a certificate checker
    replays (see tests/finite_field/check_unique_certificates.py).

Author:

    Romain Soulat

--*/
#include "tactic/arith/ff_solve_tactic.h"
#include "tactic/tactical.h"
#include "ast/ff_decl_plugin.h"
#include "params/smt_params_helper.hpp"
#include <iterator>
#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

namespace {

    using monomial = std::vector<unsigned>;
    using poly = std::map<monomial, rational>;

    struct exhausted_budget {};

    // One deterministic allowance covers encoding, propagation and all split
    // branches. Exhaustion is inconclusive and never changes the input goal.
    class unique_budget {
        reslimit &lim;
        uint64_t remaining, used = 0;
        unsigned pending = 0;
        uint64_t progress_allowance, until_progress;
        bool tracking_progress = false;
    public:
        bool exhausted = false, stalled = false;
        unique_budget(reslimit &lim, unsigned work)
            : lim(lim), remaining(work), progress_allowance(std::max(1u, work / 10)), until_progress(progress_allowance) {}
        void start_propagation() { tracking_progress = true; }
        void progress() { until_progress = progress_allowance; }
        void charge(uint64_t n = 1) {
            if (n > remaining) {
                exhausted = true;
                throw exhausted_budget();
            }
            // An inexpensive attempt should yield when it discovers no new
            // equality/value, even if one propagation node is very large.
            // Productive chains may use the full allowance, never exceed it.
            if (tracking_progress && n > until_progress) {
                exhausted = stalled = true;
                throw exhausted_budget();
            }
            if (tracking_progress) until_progress -= n;
            remaining -= n;
            used += n;
            // Do not consume the caller's resource limit on local exhaustion.
            // Poll shared cancellation even inside a single propagation node.
            if (n >= 256 || (pending += static_cast<unsigned>(n)) >= 256) {
                pending = 0;
                if (!lim.inc()) {
                    exhausted = true;
                    throw exhausted_budget();
                }
            }
        }
        uint64_t work() const { return used; }
    };

    class unique_solver {
        rational p;
        unique_budget &work;
        std::vector<poly> const &eqs;
        std::vector<poly> const &neqs;
        unsigned m_budget, m_nodes = 0;

        rational inv(rational a) const {
            rational r = p, t(0), s(1);
            a = mod(a, p);
            while (!a.is_zero()) {
                work.charge();
                rational q = div(r, a), nx = r - q * a;
                r = a;
                a = nx;
                nx = t - q * s;
                t = s;
                s = nx;
            }
            return mod(t, p);
        }

    public:
        struct state {
            std::vector<unsigned> parent;
            std::vector<rational> val;
            std::vector<bool> has_val;
            std::vector<bool> is_bool;                  // class contains a Boolean variable
            std::vector<std::vector<unsigned>> members; // valid at representatives
            std::vector<unsigned> touched;              // classes changed since last drained
            unsigned find(unsigned v) {
                while (parent[v] != v) {
                    parent[v] = parent[parent[v]];
                    v = parent[v];
                }
                return v;
            }
            // 0: unchanged, 1: changed, 2: conflict
            int merge(unsigned a, unsigned b) {
                a = find(a);
                b = find(b);
                if (a == b)
                    return 0;
                if (has_val[a] && has_val[b] && val[a] != val[b])
                    return 2;
                unsigned lo = std::min(a, b), hi = std::max(a, b);
                parent[hi] = lo;
                if (!has_val[lo] && has_val[hi]) {
                    has_val[lo] = true;
                    val[lo] = val[hi];
                }
                if (is_bool[hi])
                    is_bool[lo] = true;
                members[lo].insert(members[lo].end(), members[hi].begin(), members[hi].end());
                members[hi].clear();
                touched.push_back(lo);
                return 1;
            }
            int set(unsigned a, rational const &v) {
                a = find(a);
                if (has_val[a])
                    return val[a] == v ? 0 : 2;
                has_val[a] = true;
                val[a] = v;
                touched.push_back(a);
                return 1;
            }
        };

        unsigned m_merges = 0, m_values = 0, m_splits = 0;

        unique_solver(rational const &p, unique_budget &work, std::vector<poly> const &eqs, std::vector<poly> const &neqs,
                      unsigned budget)
            : p(p), work(work), eqs(eqs), neqs(neqs), m_budget(budget) {
            for (unsigned i = 0; i < eqs.size(); ++i)
                for (auto const &[m, c] : eqs[i])
                    for (unsigned v : m) {
                        work.charge();
                        if (occ_eq.size() <= v)
                            occ_eq.resize(v + 1);
                        if (occ_eq[v].empty() || occ_eq[v].back() != i)
                            occ_eq[v].push_back(i);
                    }
        }
        std::vector<std::vector<unsigned>> occ_eq;

        poly canon(state &st, poly const &f) {
            poly r;
            for (auto const &[m, c] : f) {
                work.charge(1 + m.size());
                rational coeff = c;
                monomial mm;
                for (unsigned v : m) {
                    unsigned rv = st.find(v);
                    if (st.has_val[rv])
                        coeff = mod(coeff * st.val[rv], p);
                    else
                        mm.push_back(rv);
                }
                if (coeff.is_zero())
                    continue;
                std::sort(mm.begin(), mm.end());
                auto &slot = r[mm];
                slot = mod(slot + coeff, p);
                if (slot.is_zero())
                    r.erase(mm);
            }
            return r;
        }

        std::string key_of(char tag, unsigned e, poly const &f) {
            std::string k(1, tag);
            k += std::to_string(e);
            k += '|';
            for (auto const &[m, c] : f) {
                work.charge(1 + m.size());
                for (unsigned v : m) {
                    k += std::to_string(v);
                    k += ',';
                }
                k += ':';
                k += c.to_string();
                k += ';';
            }
            return k;
        }

        // Returns true on conflict.
        // Scale a polynomial so that its lead (largest degree, then largest
        // monomial) has coefficient 1. Both sides of the is-zero rule use it.
        poly monic(poly const &S) const {
            work.charge(S.size());
            auto lead = S.begin();
            for (auto it = S.begin(); it != S.end(); ++it)
                if (it->first.size() > lead->first.size() ||
                    (it->first.size() == lead->first.size() && it->first > lead->first))
                    lead = it;
            rational ic = inv(lead->second);
            poly r;
            for (auto const &[m, c] : S)
                r[m] = mod(c * ic, p);
            return r;
        }

        // Worklist propagation: a constraint is revisited only when one of the
        // classes it mentions changed (merge or value). Definitions are keyed by
        // canonical right-hand sides; stale keys stay valid facts.
        bool propagate(state &st) {
            std::unordered_map<std::string, unsigned> defs;
            // is-zero facts (y - d)*S = 0, keyed by "rep(y)#monic(S)", value d
            std::unordered_map<std::string, rational> zs;
            std::set<unsigned> zs_classes;
            std::vector<char> queued(eqs.size(), 1);
            std::vector<unsigned> queue;
            for (unsigned i = eqs.size(); i-- > 0;)
                queue.push_back(i);
            st.touched.clear();
            auto apply = [&](int r) {
                if (r == 1) work.progress();
                return r == 2;
            };
            auto drain = [&]() {
                for (unsigned c : st.touched) {
                    c = st.find(c);
                    for (unsigned v : st.members[c])
                        if (v < occ_eq.size())
                            for (unsigned i : occ_eq[v])
                                if (!queued[i]) {
                                    work.charge();
                                    queued[i] = 1;
                                    queue.push_back(i);
                                }
                }
                st.touched.clear();
            };
            for (;;) {
                drain();
                if (queue.empty())
                    break;
                work.charge();
                unsigned idx = queue.back();
                queue.pop_back();
                queued[idx] = 0;
                {
                    auto const &f = eqs[idx];
                    poly g = canon(st, f);
                    if (g.empty())
                        continue;
                    if (g.size() == 1 && g.begin()->first.empty())
                        return true;
                    std::map<unsigned, unsigned> occ;
                    std::set<unsigned> nonlinear;
                    for (auto const &[m, c] : g) {
                        work.charge(1 + m.size());
                        std::set<unsigned> vs(m.begin(), m.end());
                        if (m.size() > 1) nonlinear.insert(vs.begin(), vs.end());
                        for (unsigned v : vs)
                            ++occ[v];
                    }
                    // Record is-zero facts (y - d)*S = 0 with S free of y.
                    for (unsigned yv : nonlinear) {
                        // For a purely linear occurrence, S is constant: y=d
                        // is already handled below. Only nonconstant S provides
                        // an additional zero-test dependency. This avoids a
                        // quadratic scan of wide affine bit decompositions.
                        poly S, R;
                        bool ok = true;
                        for (auto const &[m, c] : g) {
                            work.charge(1 + m.size());
                            unsigned k = static_cast<unsigned>(std::count(m.begin(), m.end(), yv));
                            if (k == 1) {
                                monomial l;
                                bool removed = false;
                                for (unsigned v : m) {
                                    if (v == yv && !removed) {
                                        removed = true;
                                        continue;
                                    }
                                    l.push_back(v);
                                }
                                S[l] = c;
                            }
                            else if (k == 0)
                                R[m] = c;
                            else {
                                ok = false;
                                break;
                            }
                        }
                        if (!ok || S.empty())
                            continue;
                        rational d(0);
                        if (!R.empty()) {
                            if (R.size() != S.size())
                                continue;
                            poly ms = monic(S), mr = monic(R);
                            if (ms != mr)
                                continue;
                            // R = lambda*S with lambda = R_lead / S_lead; d = -lambda.
                            auto lead = S.begin();
                            for (auto it = S.begin(); it != S.end(); ++it)
                                if (it->first.size() > lead->first.size() ||
                                    (it->first.size() == lead->first.size() && it->first > lead->first))
                                    lead = it;
                            rational lam = mod(R.at(lead->first) * inv(lead->second), p);
                            d = mod(-lam, p);
                        }
                        std::string zk = std::to_string(st.find(yv)) + "#" + key_of('S', 0, monic(S));
                        if (zs.emplace(zk, d).second) {
                            zs_classes.insert(st.find(yv));
                            st.touched.push_back(st.find(yv));
                        }
                    }
                    // Recover canonical digits before building linear definitions.
                    // Once every Boolean term is a digit of the same expression,
                    // copying the whole affine polynomial once per bit adds no
                    // new uniqueness function and costs quadratic space/work.
                    std::set<unsigned> digits;
                    std::vector<std::pair<unsigned, rational>> bterms;
                    for (auto const &[m, c] : g)
                        if (m.size() == 1 && st.is_bool[m[0]] && occ[m[0]] == 1)
                            bterms.push_back({m[0], c});
                    for (unsigned t = 0; bterms.size() >= 2 && t < bterms.size() && t < 3; ++t) {
                        rational ic = inv(bterms[t].second);
                        std::map<unsigned, unsigned> exps;
                        bool ok = true;
                        for (auto const &[b, c] : bterms) {
                            work.charge();
                            rational w = mod(c * ic, p);
                            unsigned e = 0;
                            rational x = w;
                            while (x > rational(1) && mod(x, rational(2)).is_zero()) {
                                work.charge();
                                x = div(x, rational(2));
                                ++e;
                            }
                            if (!x.is_one())
                                continue;
                            if (!exps.emplace(e, b).second) {
                                ok = false;
                                break;
                            }
                        }
                        if (!ok || exps.empty() || rational::power_of_two(exps.rbegin()->first + 1) > p)
                            continue;
                        std::set<unsigned> used;
                        for (auto const &[e, b] : exps)
                            used.insert(b);
                        if (used.size() == bterms.size()) digits = used;
                        poly rest;
                        for (auto const &[mm, cc] : g) {
                            work.charge(1 + mm.size());
                            if (!(mm.size() == 1 && used.count(mm[0])))
                                rest[mm] = mod(-cc * ic, p);
                        }
                        if (rest.empty() || (rest.size() == 1 && rest.begin()->first.empty())) {
                            rational k = rest.empty() ? rational(0) : rest.begin()->second;
                            for (unsigned e = 0; e < k.get_num_bits(); ++e)
                                if (k.get_bit(e) && !exps.count(e))
                                    return true;
                            for (auto const &[e, b] : exps) {
                                ++m_values;
                                if (apply(st.set(b, rational(e < k.get_num_bits() && k.get_bit(e) ? 1 : 0))))
                                    return true;
                            }
                            break;
                        }
                        for (auto const &[e, b] : exps) {
                            auto k = key_of('B', e, rest);
                            auto it = defs.find(k);
                            if (it == defs.end())
                                defs.emplace(k, b);
                            else if (apply(st.merge(it->second, b)))
                                return true;
                        }
                        break;
                    }
                    for (auto const &[m, c] : g) {
                        if (m.size() != 1 || occ[m[0]] != 1 || digits.count(m[0]))
                            continue;
                        unsigned y = m[0];
                        rational ia = inv(c);
                        poly rest;
                        for (auto const &[mm, cc] : g) {
                            work.charge(1 + mm.size());
                            if (mm != m)
                                rest[mm] = mod(-cc * ia, p);
                        }
                        if (rest.empty() || (rest.size() == 1 && rest.begin()->first.empty())) {
                            ++m_values;
                            if (apply(st.set(y, rest.empty() ? rational(0) : rest.begin()->second)))
                                return true;
                            continue;
                        }
                        if (rest.size() == 1 && rest.begin()->first.size() == 1 && rest.begin()->second.is_one()) {
                            if (apply(st.merge(y, rest.begin()->first[0])))
                                return true;
                            continue;
                        }
                        // y = c0 - z*S with (y - d)*S = 0: y = (S == 0 ? c0 : d).
                        if (zs_classes.count(y)) {
                            rational c0(0);
                            poly rp;
                            for (auto const &[mm, cc] : rest) {
                                if (mm.empty())
                                    c0 = cc;
                                else
                                    rp[mm] = cc;
                            }
                            std::set<unsigned> zc;
                            bool first = true;
                            for (auto const &[mm, cc] : rp) {
                                work.charge(1 + mm.size() * mm.size());
                                std::set<unsigned> ones;
                                for (unsigned v : mm)
                                    if (std::count(mm.begin(), mm.end(), v) == 1)
                                        ones.insert(v);
                                if (first)
                                    zc = ones;
                                else {
                                    std::set<unsigned> both;
                                    for (unsigned v : zc)
                                        if (ones.count(v))
                                            both.insert(v);
                                    zc.swap(both);
                                }
                                first = false;
                            }
                            bool hit = false;
                            for (unsigned z : zc) {
                                poly S;
                                for (auto const &[mm, cc] : rp) {
                                    work.charge(1 + mm.size());
                                    monomial l;
                                    bool removed = false;
                                    for (unsigned v : mm) {
                                        if (v == z && !removed) {
                                            removed = true;
                                            continue;
                                        }
                                        l.push_back(v);
                                    }
                                    S[l] = mod(-cc, p);
                                }
                                if (S.empty())
                                    continue;
                                poly msk = monic(S);
                                auto zit = zs.find(std::to_string(y) + "#" + key_of('S', 0, msk));
                                if (zit == zs.end())
                                    continue;
                                poly kp = msk;
                                kp[monomial{~0u}] = c0;   // tag the constants into the key
                                auto k = key_of('Z', 0, kp) + "d" + zit->second.to_string();
                                auto it = defs.find(k);
                                if (it == defs.end())
                                    defs.emplace(k, y);
                                else if (apply(st.merge(it->second, y)))
                                    return true;
                                hit = true;
                                break;
                            }
                            if (hit)
                                continue;
                        }
                        auto k = key_of('L', 0, rest);
                        auto it = defs.find(k);
                        if (it == defs.end())
                            defs.emplace(k, y);
                        else if (apply(st.merge(it->second, y)))
                            return true;
                    }

                }
            }
            for (auto const &f : neqs)
                if (canon(st, f).empty())
                    return true;
            return false;
        }

        // Returns true if every branch closes.
        bool search(state st, unsigned depth) {
            work.charge(st.parent.size());
            if (++m_nodes > m_budget)
                throw exhausted_budget();
            if (propagate(st))
                return true;
            if (depth == 0)
                return false;
            std::map<unsigned, unsigned> score;
            for (auto const &f : eqs) {
                poly g = canon(st, f);
                std::set<unsigned> vs;
                for (auto const &[m, c] : g)
                    vs.insert(m.begin(), m.end());
                for (unsigned v : vs)
                    if (st.is_bool[v])
                        ++score[v];
            }
            if (score.empty())
                return false;
            unsigned best = score.begin()->first;
            for (auto const &[v, s] : score)
                if (s > score[best])
                    best = v;
            ++m_splits;
            for (unsigned value = 0; value < 2; ++value) {
                work.charge(st.parent.size());
                state child = st;
                if (child.set(best, rational(value)) == 2)
                    continue;
                if (!search(child, depth - 1))
                    return false;
            }
            return true;
        }

        unsigned nodes() const { return m_nodes; }
    };

    class ff_unique_tactic : public tactic {
        ast_manager &m;
        params_ref p;
        statistics m_stats;

    public:
        ff_unique_tactic(ast_manager &m, params_ref const &p) : m(m), p(p) {}
        char const *name() const override { return "ff-unique"; }
        tactic *translate(ast_manager &target) override { return alloc(ff_unique_tactic, target, p); }
        void cleanup() override {}
        void collect_statistics(statistics &st) const override { st.copy(m_stats); }
        void reset_statistics() override { m_stats.reset(); }
        void updt_params(params_ref const &q) override { p.append(q); }
        void collect_param_descrs(param_descrs &ds) override {
            ds.insert("ff.unique", CPK_BOOL, "uniqueness propagation with Boolean splits before field solving", "true");
            ds.insert("ff.unique_depth", CPK_UINT, "maximum nested Boolean splits in uniqueness propagation", "16");
            ds.insert("ff.unique_nodes", CPK_UINT, "maximum search nodes in uniqueness propagation", "50000");
            ds.insert("ff.unique_work", CPK_UINT, "local work allowance for the entire uniqueness attempt", "1000000");
            ds.insert("ff.unique_equalities", CPK_BOOL, "add root-level derived equalities to the goal", "false");
        }

        void operator()(goal_ref const &g, goal_ref_buffer &result) override {
            unique_budget budget(m.limit(), smt_params_helper(p).ff_unique_work());
            try { run(g, result, budget); }
            catch (exhausted_budget const &) {
                // No assertion is changed during the speculative computation.
                result.reset();
                result.push_back(g.get());
            }
            m_stats.update("ff unique work", static_cast<double>(budget.work()));
            m_stats.update("ff unique exhausted", budget.exhausted ? 1u : 0u);
            m_stats.update("ff unique stalled", budget.stalled ? 1u : 0u);
        }

        void run(goal_ref const &g, goal_ref_buffer &result, unique_budget &budget) {
            result.reset();
            if (!smt_params_helper(p).ff_unique() || g->proofs_enabled() || g->inconsistent()) {
                result.push_back(g.get());
                return;
            }
            ff_util ff(m);
            sort *field = nullptr;
            std::unordered_map<expr *, unsigned> var_id;
            std::vector<expr *> vars;
            std::vector<poly> eqs, neqs;
            std::set<unsigned> bools;
            rational prime;
            unsigned const max_terms = 256;
            bool unsupported = false;

            std::unordered_map<expr *, poly> memo;
            // Iterative postorder traversal: SMT lets can describe arbitrarily
            // deep DAGs. A memo entry exists only after every operand succeeds.
            auto encode = [&](expr *root, poly &out) -> bool {
                struct frame { expr *e; unsigned next = 0; };
                std::vector<frame> pending{{root}};
                while (!pending.empty()) {
                    budget.charge();
                    expr *e = pending.back().e;
                    if (memo.contains(e)) { pending.pop_back(); continue; }
                    rational v;
                    bool numeral = ff.is_numeral(e, v);
                    bool interpreted = is_app(e) && to_app(e)->get_family_id() == ff.get_fid();
                    if (interpreted && !numeral) {
                        app *a = to_app(e);
                        auto k = a->get_decl_kind();
                        if (k != OP_FF_NEG && k != OP_FF_ADD && k != OP_FF_BITSUM && k != OP_FF_MUL)
                            return false;
                        auto &f = pending.back();
                        if (f.next < a->get_num_args()) {
                            expr *child = a->get_arg(f.next++);
                            if (!memo.contains(child)) pending.push_back({child});
                            continue;
                        }
                    }
                    poly r;
                    if (numeral) {
                        if (!v.is_zero()) r[monomial()] = v;
                    }
                    else if (!interpreted) {
                        auto [it, fresh] = var_id.emplace(e, static_cast<unsigned>(vars.size()));
                        if (fresh) vars.push_back(e);
                        r[monomial{it->second}] = rational(1);
                    }
                    else {
                        app *a = to_app(e);
                        auto k = a->get_decl_kind();
                        if (k == OP_FF_MUL) r[monomial()] = rational(1);
                        rational w(1);
                        for (expr *arg : *a) {
                            poly const &x = memo.at(arg);
                            if (k == OP_FF_MUL) {
                                poly nr;
                                for (auto const &[m1, c1] : r)
                                    for (auto const &[m2, c2] : x) {
                                        // A one-term polynomial can still have
                                        // exponentially growing degree.
                                        if (m1.size() + m2.size() > 1024) return false;
                                        budget.charge(1 + m1.size() + m2.size());
                                        monomial mm;
                                        std::merge(m1.begin(), m1.end(), m2.begin(), m2.end(), std::back_inserter(mm));
                                        auto &slot = nr[mm];
                                        slot = mod(slot + c1 * c2, prime);
                                        if (slot.is_zero()) nr.erase(mm);
                                        if (nr.size() > max_terms) return false;
                                    }
                                r.swap(nr);
                            }
                            else {
                                for (auto const &[mm, c] : x) {
                                    budget.charge(1 + mm.size());
                                    auto &slot = r[mm];
                                    slot = mod(slot + (k == OP_FF_NEG ? -c : w * c), prime);
                                    if (slot.is_zero()) r.erase(mm);
                                    if (r.size() > max_terms) return false;
                                }
                                if (k == OP_FF_BITSUM) w = mod(w * rational(2), prime);
                            }
                        }
                    }
                    memo.emplace(e, std::move(r));
                    pending.pop_back();
                }
                budget.charge(memo.at(root).size());
                out = memo.at(root);
                return true;
            };

            // Collect top-level field equalities and disequalities.
            ptr_vector<expr> todo;
            for (unsigned i = 0; i < g->size(); ++i)
                todo.push_back(g->form(i));
            while (!todo.empty() && !unsupported) {
                budget.charge();
                expr *f = todo.back();
                todo.pop_back();
                expr *a, *b, *n;
                bool positive = true;
                if (m.is_and(f)) {
                    for (expr *arg : *to_app(f))
                        todo.push_back(arg);
                    continue;
                }
                if (m.is_not(f, n)) {
                    positive = false;
                    f = n;
                }
                if (!m.is_eq(f, a, b) || !ff.is_ff(a))
                    continue;
                if (!field) {
                    field = a->get_sort();
                    prime = ff.modulus(field);
                }
                else if (field != a->get_sort()) {
                    unsupported = true;
                    break;
                }
                poly pa, pb;
                if (!encode(a, pa) || !encode(b, pb))
                    continue;
                for (auto &[mm, c] : pb) {
                    auto &slot = pa[mm];
                    slot = mod(slot - c, prime);
                    if (slot.is_zero())
                        pa.erase(mm);
                }
                (positive ? eqs : neqs).push_back(std::move(pa));
            }
            if (unsupported || !field || neqs.empty() || !m.inc()) {
                result.push_back(g.get());
                return;
            }
            for (auto const &f : eqs) {
                if (f.size() != 2)
                    continue;
                auto a = f.begin(), b = std::next(a);
                if (a->first.size() == 1)
                    std::swap(a, b);
                if (a->first.size() == 2 && a->first[0] == a->first[1] && b->first.size() == 1 &&
                    b->first[0] == a->first[0] && mod(a->second + b->second, prime).is_zero())
                    bools.insert(b->first[0]);
            }

            unique_solver solver(prime, budget, eqs, neqs, smt_params_helper(p).ff_unique_nodes());
            unique_solver::state root;
            unsigned n = static_cast<unsigned>(vars.size());
            root.parent.resize(n);
            for (unsigned i = 0; i < n; ++i)
                root.parent[i] = i;
            root.val.resize(n);
            root.has_val.assign(n, false);
            root.is_bool.assign(n, false);
            for (unsigned b : bools)
                root.is_bool[b] = true;
            root.members.resize(n);
            for (unsigned i = 0; i < n; ++i)
                root.members[i] = {i};
            bool closed = false;
            budget.start_propagation();
            try {
                closed = solver.search(root, std::min(64u, smt_params_helper(p).ff_unique_depth()));
            }
            catch (exhausted_budget const &) {
                closed = false;
            }
            m_stats.update("ff unique nodes", solver.nodes());
            m_stats.update("ff unique splits", solver.m_splits);
            if (closed) {
                m_stats.update("ff unique unsat", 1u);
                expr_dependency_ref deps(m);
                for (unsigned i = 0; i < g->size(); ++i)
                    deps = m.mk_join(deps, g->dep(i));
                g->reset();
                g->assert_expr(m.mk_false(), nullptr, deps);
                g->inc_depth();
                result.push_back(g.get());
                return;
            }
            if (smt_params_helper(p).ff_unique_equalities() && m.inc()) {
                // Root-level consequences only (no split assumptions).
                unique_solver::state st = root;
                try {
                    if (solver.propagate(st)) {
                        expr_dependency_ref deps(m);
                        for (unsigned i = 0; i < g->size(); ++i)
                            deps = m.mk_join(deps, g->dep(i));
                        g->reset();
                        g->assert_expr(m.mk_false(), nullptr, deps);
                        result.push_back(g.get());
                        return;
                    }
                    expr_dependency_ref deps(m);
                    for (unsigned i = 0; i < g->size(); ++i)
                        deps = m.mk_join(deps, g->dep(i));
                    unsigned added = 0;
                    for (unsigned v = 0; v < n; ++v) {
                        unsigned r = st.find(v);
                        if (r != v) {
                            g->assert_expr(m.mk_eq(vars[v], vars[r]), nullptr, deps);
                            ++added;
                        }
                        else if (st.has_val[v]) {
                            g->assert_expr(m.mk_eq(vars[v], ff.mk_numeral(st.val[v], field)), nullptr, deps);
                            ++added;
                        }
                    }
                    m_stats.update("ff unique equalities", added);
                }
                catch (exhausted_budget const &) {
                }
            }
            result.push_back(g.get());
        }
    };
}  // namespace

tactic *mk_ff_unique_tactic(ast_manager &m, params_ref const &p) {
    return alloc(ff_unique_tactic, m, p);
}
