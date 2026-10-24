/*++
Copyright (c) 2026

Shared finite-field uniqueness propagation. The tactic and certificate producer
use the same worklist and functional-definition matching. Ring-only recording
is optional and can discharge Boolean-domain branches. Digit and coincident-output
zero-test evidence remain unsupported.
--*/
#pragma once
#include "util/rational.h"
#include "util/rlimit.h"
#include <iterator>
#include <functional>
#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

namespace ff_unique {
    using monomial = std::vector<unsigned>;
    struct poly : std::map<monomial, rational> {
        unsigned derivation = ~0u;
    };

    inline bool boolean_polynomial(poly const &f, rational const &p, unsigned &variable, rational &coefficient) {
        if (f.size() != 2) return false;
        auto a = f.begin(), b = std::next(a);
        if (a->first.size() == 1) std::swap(a, b);
        if (a->first.size() != 2 || a->first[0] != a->first[1] || b->first.size() != 1 ||
            b->first[0] != a->first[0] || !mod(a->second + b->second, p).is_zero()) return false;
        variable = b->first[0]; coefficient = a->second;
        return true;
    }

    // Evidence is emitted by the same propagation used by ff-unique. Unsupported
    // domain/branch rules are disabled when this sink is present, never trusted.
    struct observer {
        virtual ~observer() = default;
        virtual unsigned scale(unsigned id, rational const &c) = 0;
        virtual unsigned sum(unsigned left, unsigned right) = 0;
        virtual unsigned multiply(unsigned id, rational const &c, monomial const &factor) = 0;
        virtual poly substitute(poly const &row, unsigned variable, poly const &definition) = 0;
        virtual void conflict(poly const &constant) = 0;
        virtual unsigned assume(unsigned variable, rational const &value) = 0;
        virtual unsigned branch_result() const = 0;
        virtual void join_branches(unsigned variable, poly const &boolean,
                                   unsigned hypothesis0, unsigned root0, unsigned hypothesis1, unsigned root1) = 0;
    };

    struct exhausted_budget {};

    // One deterministic allowance covers encoding, propagation and all split
    // branches. Exhaustion is inconclusive and never changes the input goal.
    class unique_budget {
        reslimit &lim;
        uint64_t remaining, used = 0;
        unsigned pending = 0;
        uint64_t progress_allowance, until_progress;
        bool tracking_progress = false;
        std::function<void(uint64_t)> shared_charge;
    public:
        bool exhausted = false, stalled = false;
        unique_budget(reslimit &lim, unsigned work, std::function<void(uint64_t)> charge = {})
            : lim(lim), remaining(work), progress_allowance(std::max(1u, work / 10)), until_progress(progress_allowance), shared_charge(std::move(charge)) {}
        void start_propagation() { tracking_progress = true; }
        void stop_propagation() { tracking_progress = false; }
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
            if (shared_charge) shared_charge(n);
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
        observer *proof;

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
            // Edges prove v-parent[v]=0; values prove root-val[root]=0.
            // In recording mode retain edges until their identities are composed.
            std::vector<unsigned> parent_proof, value_proof;
            std::vector<rational> val;
            std::vector<bool> has_val;
            std::vector<bool> is_bool;                  // class contains a Boolean variable
            std::vector<std::vector<unsigned>> members; // valid at representatives
            std::vector<unsigned> touched;              // classes changed since last drained
            unsigned find(unsigned v) {
                while (parent[v] != v) {
                    if (parent_proof.empty()) parent[v] = parent[parent[v]];
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
                      unsigned budget, observer *proof = nullptr)
            : p(p), work(work), eqs(eqs), neqs(neqs), m_budget(budget), proof(proof) {
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
            if (proof) {
                poly r = f;
                std::set<unsigned> variables;
                for (auto const &[m, c] : f) {
                    work.charge(1 + m.size());
                    variables.insert(m.begin(), m.end());
                }
                for (unsigned v : variables) {
                    unsigned root = v, id = ~0u;
                    while (st.parent[root] != root) {
                        work.charge();
                        unsigned edge = st.parent_proof[root];
                        id = id == ~0u ? edge : proof->sum(id, edge);
                        root = st.parent[root];
                    }
                    if (st.has_val[root])
                        id = id == ~0u ? st.value_proof[root] : proof->sum(id, st.value_proof[root]);
                    if (root == v && !st.has_val[root]) continue;
                    // Telescoping class edges, followed by the root's value if
                    // known, prove exactly v-root or v-value. Substitution is
                    // expanded into ring identities by the sink.
                    poly definition;
                    definition[{v}] = rational(1);
                    if (st.has_val[root]) {
                        if (!st.val[root].is_zero()) definition[{}] = mod(-st.val[root], p);
                    }
                    else definition[{root}] = p - rational(1);
                    definition.derivation = id;
                    r = proof->substitute(r, v, definition);
                }
                return r;
            }
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

        // Install a proved affine equality after reducing it by existing class
        // edges. This also handles stale definition keys: an old identity stays
        // valid, but its left-hand side may now have a value or a new root.
        int learn(state &st, poly relation) {
            relation = canon(st, relation);
            if (relation.empty()) return 0;
            if (relation.size() == 1 && relation.begin()->first.empty()) {
                proof->conflict(relation);
                return 2;
            }
            std::vector<unsigned> vars;
            for (auto const &[m, c] : relation) {
                work.charge();
                if (!m.empty()) {
                    if (m.size() != 1) throw exhausted_budget();
                    vars.push_back(m[0]);
                }
            }
            if (vars.size() == 1) {
                unsigned v = vars[0];
                rational k = inv(relation.at(monomial{v}));
                auto it = relation.find(monomial{});
                rational value = it == relation.end() ? rational(0) : mod(-it->second * k, p);
                st.value_proof[v] = proof->scale(relation.derivation, k);
                return st.set(v, value);
            }
            if (vars.size() != 2 || relation.size() != 2 ||
                !mod(relation.at(monomial{vars[0]}) + relation.at(monomial{vars[1]}), p).is_zero())
                throw exhausted_budget();
            unsigned hi = std::max(vars[0], vars[1]);
            // The union always points to the smaller representative. Normalizing
            // its coefficient gives hi-lo=0, exactly the stored edge orientation.
            st.parent_proof[hi] = proof->scale(relation.derivation, inv(relation.at(monomial{hi})));
            return st.merge(vars[0], vars[1]);
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
            if (proof) {
                if (!neqs.empty()) throw exhausted_budget();
                if (st.parent_proof.empty()) {
                    st.parent_proof.assign(st.parent.size(), ~0u);
                    st.value_proof.assign(st.parent.size(), ~0u);
                }
            }
            std::unordered_map<std::string, unsigned> defs;
            std::unordered_map<std::string, unsigned> definition_proofs;
            // is-zero facts (y - d)*S = 0, keyed by "rep(y)#monic(S)", value d
            std::unordered_map<std::string, rational> zs;
            std::unordered_map<std::string, unsigned> zero_proofs;
            struct zero_definition { unsigned equation, zero, multiplier; rational coefficient; };
            std::unordered_map<std::string, zero_definition> zero_definitions;
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
                    if (g.size() == 1 && g.begin()->first.empty()) {
                        if (proof) proof->conflict(g);
                        return true;
                    }
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
                        poly ms = monic(S);
                        std::string zk = std::to_string(st.find(yv)) + "#" + key_of('S', 0, ms);
                        if (zs.emplace(zk, d).second) {
                            if (proof) {
                                // g=(y-d)*S; rescale by S's leading coefficient
                                // to prove (y-d)*monic(S), not S=0 by itself.
                                rational k = mod(ms.begin()->second * inv(S.begin()->second), p);
                                zero_proofs.emplace(zk, proof->scale(g.derivation, k));
                            }
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
                    for (unsigned t = 0; !proof && bterms.size() >= 2 && t < bterms.size() && t < 3; ++t) {
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
                            if (apply(proof ? learn(st, g) : st.set(y, rest.empty() ? rational(0) : rest.begin()->second)))
                                return true;
                            continue;
                        }
                        if (rest.size() == 1 && rest.begin()->first.size() == 1 && rest.begin()->second.is_one()) {
                            if (apply(proof ? learn(st, g) : st.merge(y, rest.begin()->first[0])))
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
                                auto zk = std::to_string(y) + "#" + key_of('S', 0, msk);
                                auto zit = zs.find(zk);
                                if (zit == zs.end())
                                    continue;
                                // When both outputs coincide, the consequence is
                                // radical membership, not this ring identity.
                                // Keep that case disabled until finite-field
                                // evidence is available instead of dividing by 0.
                                if (proof && zit->second == c0) continue;
                                poly kp = msk;
                                kp[monomial{~0u}] = c0;   // tag the constants into the key
                                auto k = key_of('Z', 0, kp) + "d" + zit->second.to_string();
                                auto it = defs.find(k);
                                if (it == defs.end()) {
                                    defs.emplace(k, y);
                                    if (proof) {
                                        rational alpha = mod(S.begin()->second * inv(msk.begin()->second), p);
                                        zero_definitions.emplace(k, zero_definition{
                                            proof->scale(g.derivation, ia), zero_proofs.at(zk), z, alpha});
                                    }
                                }
                                else if (proof) {
                                    unsigned t = it->second;
                                    if (t != y) {
                                        auto const &old = zero_definitions.at(k);
                                        rational d = zit->second;
                                        rational alpha = mod(S.begin()->second * inv(msk.begin()->second), p);
                                        unsigned A = proof->scale(g.derivation, ia), B = old.equation;
                                        unsigned C = zero_proofs.at(zk), D = old.zero;
                                        // A=y-c0+alpha*z*M, B=t-c0+beta*w*M,
                                        // C=(y-d)*M, D=(t-d)*M, M=monic(S).
                                        // (y-d)*B-(t-d)*A-beta*w*C+alpha*z*D
                                        // equals (d-c0)*(y-t). All four equations
                                        // are proved, and d!=c0, so y=t follows
                                        // using only PAC additions/multiplications.
                                        unsigned id = proof->multiply(B, rational(1), {y});
                                        if (!d.is_zero()) id = proof->sum(id, proof->scale(B, mod(-d, p)));
                                        id = proof->sum(id, proof->multiply(A, p-rational(1), {t}));
                                        if (!d.is_zero()) id = proof->sum(id, proof->scale(A, d));
                                        id = proof->sum(id, proof->multiply(C, mod(-old.coefficient, p), {old.multiplier}));
                                        id = proof->sum(id, proof->multiply(D, alpha, {z}));
                                        poly equality;
                                        equality[{y}] = rational(1);
                                        equality[{t}] = p-rational(1);
                                        equality.derivation = proof->scale(id, inv(mod(d-c0, p)));
                                        if (apply(learn(st, std::move(equality)))) return true;
                                    }
                                }
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
                        if (it == defs.end()) {
                            defs.emplace(k, y);
                            if (proof) definition_proofs.emplace(k, proof->scale(g.derivation, ia));
                        }
                        else if (proof) {
                            // a*y+r=0 and b*z+s=0 with -r/a=-s/b imply
                            // y-z=(a*y+r)/a-(b*z+s)/b=0. Keep the local
                            // identity instead of expanding a circuit globally.
                            if (it->second == y) continue;
                            poly equality;
                            equality[{y}] = rational(1);
                            equality[{it->second}] = p - rational(1);
                            equality.derivation = proof->sum(proof->scale(g.derivation, ia),
                                proof->scale(definition_proofs.at(k), p - rational(1)));
                            if (apply(learn(st, std::move(equality)))) return true;
                        }
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
            return split(st, depth);
        }

        bool split(state &st, unsigned depth) {
            if (depth == 0)
                return false;
            std::map<unsigned, unsigned> score;
            std::map<unsigned, poly> bit_facts;
            for (auto const &f : eqs) {
                poly g = canon(st, f);
                unsigned variable; rational coefficient;
                if (proof && boolean_polynomial(g, p, variable, coefficient)) {
                    // A class flag is not evidence: retain the actual canonical
                    // equation proving v^2-v=0 at this branch's active scope.
                    g.derivation = proof->scale(g.derivation, inv(coefficient));
                    poly fact;
                    fact[{variable, variable}] = rational(1);
                    fact[{variable}] = p-rational(1);
                    fact.derivation = g.derivation;
                    bit_facts.emplace(variable, std::move(fact));
                }
                std::set<unsigned> vs;
                for (auto const &[m, c] : g)
                    vs.insert(m.begin(), m.end());
                for (unsigned v : vs)
                    if (st.is_bool[v] && !st.has_val[v])
                        ++score[v];
            }
            if (proof) {
                for (auto it = score.begin(); it != score.end();)
                    if (!bit_facts.contains(it->first)) it = score.erase(it); else ++it;
            }
            if (score.empty())
                return false;
            unsigned best = score.begin()->first;
            for (auto const &[v, s] : score)
                if (s > score[best])
                    best = v;
            ++m_splits;
            unsigned hypotheses[2] = {~0u, ~0u}, roots[2] = {~0u, ~0u};
            for (unsigned value = 0; value < 2; ++value) {
                work.charge(st.parent.size());
                state child = st;
                if (proof) child.value_proof[best] = hypotheses[value] = proof->assume(best, rational(value));
                if (child.set(best, rational(value)) == 2) {
                    if (proof) throw exhausted_budget();
                    continue;
                }
                if (!search(child, depth - 1))
                    return false;
                if (proof) roots[value] = proof->branch_result();
            }
            if (proof) proof->join_branches(best, bit_facts.at(best), hypotheses[0], roots[0], hypotheses[1], roots[1]);
            return true;
        }

        unsigned nodes() const { return m_nodes; }
    };

}
