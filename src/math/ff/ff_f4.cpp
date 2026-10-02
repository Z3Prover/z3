/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_f4.cpp

Abstract:

    F4 Groebner bases over fixed-width prime fields, plus zero-dimensional
    model construction (minimal polynomials via Wiedemann/Berlekamp-Massey,
    F_p-root isolation via gcd with X^p - X and Cantor-Zassenhaus splitting).

    See ff_f4.h for the soundness contract.

Author:

    Romain Soulat

--*/
#include "math/ff/ff_f4.h"
#include "math/ff/ff_field.h"
#include <algorithm>
#include <bit>
#include <type_traits>
#include <cstring>
#include <queue>
#include <unordered_map>
#include <unordered_set>

namespace ff {

    void f4_stats::collect(statistics &st) const {
        st.update("ff f4 gb calls", m_gb_calls);
        st.update("ff f4 matrices", m_matrices);
        st.update("ff f4 rows", m_rows);
        st.update("ff f4 new polys", m_new_polys);
        st.update("ff f4 zero reductions", m_zero_reductions);
        st.update("ff f4 splits", m_splits);
        st.update("ff f4 minpolys", m_minpolys);
        st.update("ff f4 roots", m_roots);
        st.update("ff f4 positive dim", m_positive_dim);
        st.update("ff f4 large quotient", m_large_quotient);
        st.update("ff f4 unsupported", m_unsupported);
        st.update("ff f4 field closures", m_field_closures);
        st.update("ff f4 value splits", m_value_splits);
    }

#if Z3_FF_HAS_UINT128
    bool f4_supported(rational const &p) {
        return field64::fits(p) || field256::fits(p);
    }

    namespace {

        // ------------------------------------------------------------------
        // Premise sets as bitsets over a dense renumbering of input premises.
        struct deps {
            std::vector<uint64_t> w;
            void add(unsigned i) {
                if (w.size() <= i / 64)
                    w.resize(i / 64 + 1, 0);
                w[i / 64] |= uint64_t(1) << (i % 64);
            }
            void merge(deps const &o) {
                if (o.w.empty())
                    return;
                if (w.size() < o.w.size())
                    w.resize(o.w.size(), 0);
                for (size_t i = 0; i < o.w.size(); ++i)
                    w[i] |= o.w[i];
            }
            template <class F>
            void for_each(F const &f) const {
                for (size_t i = 0; i < w.size(); ++i)
                    for (uint64_t x = w[i]; x; x &= x - 1)
                        f(static_cast<unsigned>(i * 64 + std::countr_zero(x)));
            }
        };

        // ------------------------------------------------------------------
        // Monomials: interned exponent vectors, graded reverse lexicographic order.
        class mon_table {
            unsigned n, cap, polls = 0;
            std::function<void(unsigned)> const &charge;
            std::vector<uint16_t> ex;
            std::vector<uint32_t> dg;
            std::vector<uint64_t> msk;
            std::vector<uint16_t> scratch;
            static constexpr unsigned SCRATCH = ~0u;

            uint16_t const *raw(unsigned id) const { return id == SCRATCH ? scratch.data() : ex.data() + size_t(id) * n; }
            struct hasher {
                mon_table const *t;
                size_t operator()(unsigned id) const {
                    uint16_t const *e = t->raw(id);
                    uint64_t h = 1469598103934665603ull;
                    for (unsigned i = 0; i < t->n; ++i)
                        h = (h ^ e[i]) * 1099511628211ull;
                    return static_cast<size_t>(h);
                }
            };
            struct equal {
                mon_table const *t;
                bool operator()(unsigned a, unsigned b) const {
                    return std::memcmp(t->raw(a), t->raw(b), sizeof(uint16_t) * t->n) == 0;
                }
            };
            std::unordered_set<unsigned, hasher, equal> set;

        public:
            explicit mon_table(unsigned n, unsigned cap, std::function<void(unsigned)> const &charge)
                : n(n), cap(cap), charge(charge), scratch(n, 0), set(64, hasher{this}, equal{this}) {
                mk_scratch();  // id 0 is the constant monomial 1
            }
            unsigned num_vars() const { return n; }
            unsigned size() const { return static_cast<unsigned>(dg.size()); }
            uint16_t *tmp() { return scratch.data(); }
            unsigned mk_scratch() {
                if ((++polls & 255) == 0) charge(0);
                auto it = set.find(SCRATCH);
                if (it != set.end())
                    return *it;
                // Check before every allocation, including conversion/model
                // construction; matrix admission alone misses those paths.
                if (size() >= cap) throw exhausted();
                unsigned id = size();
                uint32_t d = 0;
                uint64_t m = 0;
                for (unsigned i = 0; i < n; ++i) {
                    if (scratch[i] > 60000)
                        throw exhausted();
                    d += scratch[i];
                    if (scratch[i])
                        m |= uint64_t(1) << (i % 64);
                }
                ex.insert(ex.end(), scratch.begin(), scratch.end());
                dg.push_back(d);
                msk.push_back(m);
                set.insert(id);
                return id;
            }
            uint16_t const *exps(unsigned id) const { return ex.data() + size_t(id) * n; }
            uint32_t deg(unsigned id) const { return dg[id]; }
            unsigned one() const { return 0; }
            // > 0 iff a > b in grevlex.
            int cmp(unsigned a, unsigned b) const {
                if (a == b)
                    return 0;
                if (dg[a] != dg[b])
                    return dg[a] > dg[b] ? 1 : -1;
                uint16_t const *x = exps(a), *y = exps(b);
                for (unsigned i = n; i-- > 0;)
                    if (x[i] != y[i])
                        return x[i] < y[i] ? 1 : -1;
                return 0;
            }
            bool divides(unsigned a, unsigned b) const {
                if ((msk[a] & ~msk[b]) != 0 || dg[a] > dg[b])
                    return false;
                uint16_t const *x = exps(a), *y = exps(b);
                for (unsigned i = 0; i < n; ++i)
                    if (x[i] > y[i])
                        return false;
                return true;
            }
            bool coprime(unsigned a, unsigned b) const {
                if ((msk[a] & msk[b]) == 0)
                    return true;
                uint16_t const *x = exps(a), *y = exps(b);
                for (unsigned i = 0; i < n; ++i)
                    if (x[i] && y[i])
                        return false;
                return true;
            }
            unsigned mul(unsigned a, unsigned b) {
                if (a == 0)
                    return b;
                if (b == 0)
                    return a;
                uint16_t const *x = exps(a), *y = exps(b);
                for (unsigned i = 0; i < n; ++i) {
                    uint32_t s = uint32_t(x[i]) + y[i];
                    if (s > 60000)
                        throw exhausted();
                    scratch[i] = static_cast<uint16_t>(s);
                }
                return mk_scratch();
            }
            unsigned quo(unsigned a, unsigned b) {  // requires b | a
                uint16_t const *x = exps(a), *y = exps(b);
                for (unsigned i = 0; i < n; ++i)
                    scratch[i] = x[i] - y[i];
                return mk_scratch();
            }
            unsigned lcm(unsigned a, unsigned b) {
                uint16_t const *x = exps(a), *y = exps(b);
                for (unsigned i = 0; i < n; ++i)
                    scratch[i] = std::max(x[i], y[i]);
                return mk_scratch();
            }
            unsigned var(unsigned v, unsigned k = 1) {
                if (k > 60000) throw exhausted();
                std::fill(scratch.begin(), scratch.end(), 0);
                scratch[v] = static_cast<uint16_t>(k);
                return mk_scratch();
            }
            // Returns v if the monomial is x_v^k with k >= 1, else -1.
            int pure_var(unsigned id) const {
                if (dg[id] == 0)
                    return -1;
                uint16_t const *x = exps(id);
                int v = -1;
                for (unsigned i = 0; i < n; ++i)
                    if (x[i]) {
                        if (v >= 0)
                            return -1;
                        v = static_cast<int>(i);
                    }
                return v;
            }
        };

        // ------------------------------------------------------------------
        template <class F>
        struct poly {
            using E = typename F::elem;
            std::vector<unsigned> mons;  // strictly decreasing in grevlex
            std::vector<E> coefs;
            deps dep;
            bool empty() const { return mons.empty(); }
            size_t size() const { return mons.size(); }
            unsigned lm() const { return mons[0]; }
        };

        // Dense univariate polynomials, coefficient i is for X^i.
        template <class F>
        class upoly_ops {
            using E = typename F::elem;
            using U = std::vector<E>;
            F const &f;
            std::function<void(unsigned)> const &charge;

        public:
            upoly_ops(F const &f, std::function<void(unsigned)> const &charge) : f(f), charge(charge) {}
            void trim(U &a) const {
                while (!a.empty() && f.is_zero(a.back()))
                    a.pop_back();
            }
            U rem(U a, U const &m) const {
                // m is non-zero with a non-zero leading coefficient.
                trim(a);
                size_t dm = m.size() - 1;
                E li = f.inv(m.back());
                while (a.size() > dm && !a.empty()) {
                    E c = f.mul(a.back(), li);
                    size_t shift = a.size() - 1 - dm;
                    for (size_t i = 0; i <= dm; ++i)
                        a[shift + i] = f.sub(a[shift + i], f.mul(c, m[i]));
                    a.pop_back();
                    trim(a);
                }
                charge(static_cast<unsigned>(1 + dm / 16));
                return a;
            }
            U mulmod(U const &a, U const &b, U const &m) const {
                if (a.empty() || b.empty())
                    return U();
                U r(a.size() + b.size() - 1, f.zero());
                for (size_t i = 0; i < a.size(); ++i) {
                    if (f.is_zero(a[i]))
                        continue;
                    for (size_t j = 0; j < b.size(); ++j)
                        r[i + j] = f.add(r[i + j], f.mul(a[i], b[j]));
                }
                charge(static_cast<unsigned>(1 + (a.size() * b.size()) / 16));
                return rem(std::move(r), m);
            }
            U monic(U a) const {
                trim(a);
                if (a.empty())
                    return a;
                E li = f.inv(a.back());
                for (auto &c : a)
                    c = f.mul(c, li);
                return a;
            }
            U gcd(U a, U b) const {
                trim(a);
                trim(b);
                while (!b.empty()) {
                    U r = rem(a, b);
                    a = std::move(b);
                    b = std::move(r);
                }
                return monic(std::move(a));
            }
            // base^e mod m, e given by its bits (LSB first).
            U powmod(U base, std::vector<bool> const &bits, U const &m) const {
                U r{f.one()};
                r = rem(r, m);
                base = rem(std::move(base), m);
                for (size_t i = bits.size(); i-- > 0;) {
                    r = mulmod(r, r, m);
                    if (bits[i])
                        r = mulmod(r, base, m);
                }
                return r;
            }
            U divexact(U a, U const &d) const {
                trim(a);
                size_t dd = d.size() - 1;
                if (a.size() < d.size())
                    return U();
                U q(a.size() - dd, f.zero());
                E li = f.inv(d.back());
                while (a.size() >= d.size()) {
                    E c = f.mul(a.back(), li);
                    size_t shift = a.size() - 1 - dd;
                    q[shift] = c;
                    for (size_t i = 0; i <= dd; ++i)
                        a[shift + i] = f.sub(a[shift + i], f.mul(c, d[i]));
                    a.pop_back();
                    trim(a);
                    if (a.size() < d.size())
                        break;
                }
                if (!a.empty())
                    throw exhausted();  // not an exact division: never happens for true factors
                return q;
            }
            E eval(U const &a, E x) const {
                E r = f.zero();
                for (size_t i = a.size(); i-- > 0;)
                    r = f.add(f.mul(r, x), a[i]);
                return r;
            }
        };

        // ------------------------------------------------------------------
        template <class F>
        class f4_solver {
            using E = typename F::elem;
            using P = poly<F>;
            using U = std::vector<E>;

            F const &f;
            mon_table &M;
            f4_config const &cfg;
            f4_stats &st;
            std::function<void(unsigned)> const &charge_fn;
            unsigned m_pending = 0;
            // Batch work accounting: one callback (and one resource-limit check)
            // per 256 units instead of one per row operation.
            void charge(unsigned k) {
                m_pending += k;
                if (m_pending >= 256) {
                    unsigned n = m_pending;
                    m_pending = 0;
                    charge_fn(n);
                }
            }
            upoly_ops<F> uops;
            uint64_t rng;
            std::vector<bool> bits_p, bits_half;  // p and (p-1)/2
            bool field_closed = false;           // field equations already adjoined on this branch
            unsigned m_slice_budget = 0;

            uint64_t next_random() {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                return rng;
            }
            E random_elem() {
                if constexpr (std::is_same<F, field64>::value)
                    return f.from_uint(next_random());
                else {
                    rational r(0), base = rational::power_of_two(64);
                    for (unsigned i = 0; i < 5; ++i)
                        r = r * base + rational(next_random(), rational::ui64());
                    return f.from(r);
                }
            }

            // -------------------------------------------------------------- GB state
            struct pair_t {
                unsigned i, j, lcm, deg;
            };
            std::vector<P> G;
            std::vector<char> redundant;
            std::vector<pair_t> pairs;
            int unit = -1;

            void make_monic(P &p) {
                if (p.empty() || f.eq(p.coefs[0], f.one()))
                    return;
                E li = f.inv(p.coefs[0]);
                for (auto &c : p.coefs)
                    c = f.mul(c, li);
            }

            // Gebauer-Moeller installation of a new basis element h = G.back().
            void update(unsigned h) {
                unsigned lh = G[h].lm();
                struct cand {
                    unsigned g, lcm;
                    bool coprime;
                    bool alive;
                };
                std::vector<cand> C;
                for (unsigned g = 0; g < h; ++g)
                    if (!redundant[g])
                        C.push_back({g, M.lcm(G[g].lm(), lh), M.coprime(G[g].lm(), lh), true});
                // D: minimal lcms (Buchberger's chain criterion among new pairs).
                std::vector<unsigned> D;
                for (unsigned k = 0; k < C.size(); ++k) {
                    if ((k & 255) == 0) charge_fn(0);
                    C[k].alive = false;  // removed from C
                    bool keep = C[k].coprime;
                    if (!keep) {
                        keep = true;
                        for (unsigned k2 = k + 1; k2 < C.size() && keep; ++k2)
                            if (M.divides(C[k2].lcm, C[k].lcm))
                                keep = false;
                        for (unsigned d : D)
                            if (keep && M.divides(C[d].lcm, C[k].lcm))
                                keep = false;
                    }
                    if (keep)
                        D.push_back(k);
                }
                // Old pairs removed by the chain criterion through h.
                std::vector<pair_t> kept;
                kept.reserve(pairs.size());
                for (auto const &pr : pairs) {
                    charge(1);
                    if (M.divides(lh, pr.lcm)) {
                        unsigned l1 = M.lcm(G[pr.i].lm(), lh), l2 = M.lcm(G[pr.j].lm(), lh);
                        if (l1 != pr.lcm && l2 != pr.lcm)
                            continue;
                    }
                    kept.push_back(pr);
                }
                pairs.swap(kept);
                // E: new pairs that are not coprime (product criterion).
                for (unsigned d : D)
                    if (!C[d].coprime)
                        pairs.push_back({C[d].g, h, C[d].lcm, M.deg(C[d].lcm)});
                for (unsigned g = 0; g < h; ++g)
                    if (!redundant[g] && M.divides(lh, G[g].lm()))
                        redundant[g] = 1;
            }

            void insert(P p) {
                if (p.empty())
                    return;
                make_monic(p);
                G.push_back(std::move(p));
                redundant.push_back(0);
                unsigned h = static_cast<unsigned>(G.size() - 1);
                if (G[h].lm() == M.one()) {
                    unit = static_cast<int>(h);
                    return;
                }
                if (G.size() > cfg.max_basis)
                    throw exhausted();
                update(h);
            }

            int find_reducer(unsigned m, int exclude = -1) {
                charge(1 + static_cast<unsigned>(G.size() / 32));
                for (unsigned g = 0; g < G.size(); ++g)
                    if (!redundant[g] && static_cast<int>(g) != exclude && M.divides(G[g].lm(), m))
                        return static_cast<int>(g);
                return -1;
            }

            // -------------------------------------------------------------- F4 step
            struct row {
                std::vector<unsigned> cols;
                std::vector<E> coefs;
                deps dep;
            };

            void f4_step(std::vector<pair_t> const &sel) {
                ++st.m_matrices;
                // Row specifications (multiplier, basis index), deduplicated.
                std::vector<std::pair<unsigned, unsigned>> specs;
                {
                    std::unordered_set<uint64_t> seen;
                    for (auto const &pr : sel) {
                        for (unsigned g : {pr.i, pr.j}) {
                            unsigned u = M.quo(pr.lcm, G[g].lm());
                            uint64_t key = (uint64_t(u) << 32) | g;
                            if (seen.insert(key).second)
                                specs.push_back({u, g});
                        }
                    }
                }
                // Materialize rows in monomial ids; pick one pivot per lead.
                std::vector<std::vector<unsigned>> rmons;
                std::vector<unsigned> rsrc;  // basis index of each row
                std::unordered_map<unsigned, unsigned> pivot_of;  // lead monomial -> row
                std::vector<unsigned> to_reduce;
                std::vector<unsigned> queue;
                auto materialize = [&](unsigned u, unsigned g) {
                    std::vector<unsigned> ms;
                    ms.reserve(G[g].size());
                    for (unsigned m : G[g].mons)
                        ms.push_back(M.mul(u, m));
                    // Interning monomials dominates on wide, sparse systems; account for it.
                    charge(1 + static_cast<unsigned>(ms.size() / 4));
                    if (M.size() > cfg.max_monomials)
                        throw exhausted();
                    rmons.push_back(std::move(ms));
                    rsrc.push_back(g);
                    return static_cast<unsigned>(rmons.size() - 1);
                };
                for (auto const &[u, g] : specs) {
                    unsigned r = materialize(u, g);
                    unsigned lead = rmons[r][0];
                    // The first row with a given lead is its pivot; the others are reduced.
                    if (!pivot_of.emplace(lead, r).second)
                        to_reduce.push_back(r);
                    for (size_t k = 1; k < rmons[r].size(); ++k)
                        queue.push_back(rmons[r][k]);
                }
                // Symbolic preprocessing.
                std::unordered_set<unsigned> done;
                for (auto const &[lead, r] : pivot_of)
                    done.insert(lead);
                while (!queue.empty()) {
                    unsigned m = queue.back();
                    queue.pop_back();
                    if (!done.insert(m).second)
                        continue;
                    int g = find_reducer(m);
                    if (g < 0)
                        continue;
                    unsigned r = materialize(M.quo(m, G[g].lm()), static_cast<unsigned>(g));
                    pivot_of.emplace(m, r);
                    for (size_t k = 1; k < rmons[r].size(); ++k)
                        queue.push_back(rmons[r][k]);
                    charge(1);
                }
                // Columns in decreasing monomial order.
                std::vector<unsigned> colmon(done.begin(), done.end());
                std::sort(colmon.begin(), colmon.end(), [&](unsigned a, unsigned b) { return M.cmp(a, b) > 0; });
                std::unordered_map<unsigned, unsigned> col_of;
                col_of.reserve(colmon.size() * 2);
                for (unsigned c = 0; c < colmon.size(); ++c)
                    col_of[colmon[c]] = c;
                size_t ncols = colmon.size();
                st.m_rows += static_cast<unsigned>(rmons.size());

                std::vector<row> rows(rmons.size());
                for (unsigned r = 0; r < rmons.size(); ++r) {
                    auto &R = rows[r];
                    auto const &src = G[rsrc[r]];
                    R.cols.reserve(rmons[r].size());
                    for (unsigned m : rmons[r])
                        R.cols.push_back(col_of.at(m));
                    R.coefs = src.coefs;
                    R.dep = src.dep;
                }
                rmons.clear();
                std::vector<int> pivrow(ncols, -1);
                for (auto const &[lead, r] : pivot_of)
                    pivrow[col_of.at(lead)] = static_cast<int>(r);

                // Reduction with a dense accumulator. Columns are visited in
                // increasing index (decreasing monomial) order: by a linear scan
                // for moderately sized matrices, by a heap of touched columns
                // for very wide, sparse ones.
                std::vector<E> acc(ncols, f.zero());
                std::vector<char> inheap(ncols, 0);
                std::priority_queue<unsigned, std::vector<unsigned>, std::greater<unsigned>> heap;
                bool scan = ncols <= 32768;
                std::vector<unsigned __int128> lacc;
                std::vector<unsigned> fresh;
                for (unsigned r : to_reduce) {
                    auto &R = rows[r];
                    deps d = R.dep;
                    unsigned first = R.cols[0];
                    size_t last = 0;
                    for (size_t k = 0; k < R.cols.size(); ++k) {
                        acc[R.cols[k]] = R.coefs[k];
                        last = std::max<size_t>(last, R.cols[k]);
                        if (!scan) {
                            inheap[R.cols[k]] = 1;
                            heap.push(R.cols[k]);
                        }
                    }
                    std::vector<unsigned> oc;
                    std::vector<E> ov;
                    auto eliminate = [&](unsigned c, E const &v) {
                        int pv = pivrow[c];
                        if (pv < 0) {
                            oc.push_back(c);
                            ov.push_back(v);
                            return;
                        }
                        auto const &Pv = rows[pv];
                        E nv = f.neg(v);
                        size_t sz = Pv.cols.size();
                        for (size_t k = 1; k < sz; ++k) {
                            unsigned cc = Pv.cols[k];
                            acc[cc] = f.add(acc[cc], f.mul(nv, Pv.coefs[k]));
                            if (scan) {
                                if (cc > last)
                                    last = cc;
                            }
                            else if (!inheap[cc]) {
                                inheap[cc] = 1;
                                heap.push(cc);
                            }
                        }
                        d.merge(Pv.dep);
                        charge(1 + static_cast<unsigned>(sz / 16));
                    };
                    bool lazy_done = false;
                    if constexpr (std::is_same<F, field64>::value) {
                        if (scan && f.lazy_ok()) {
                            // Delayed modular reduction: accumulate raw 128-bit
                            // products, reduce once per visited column.
                            if (lacc.size() < ncols)
                                lacc.assign(ncols, 0);
                            for (size_t k = 0; k < R.cols.size(); ++k) {
                                lacc[R.cols[k]] = f.wide(R.coefs[k]);
                                acc[R.cols[k]] = f.zero();
                            }
                            for (size_t c = first; c <= last; ++c) {
                                if (lacc[c] == 0)
                                    continue;
                                E v = f.reduce_wide(lacc[c]);
                                lacc[c] = 0;
                                if (f.is_zero(v))
                                    continue;
                                int pv = pivrow[c];
                                if (pv < 0) {
                                    oc.push_back(static_cast<unsigned>(c));
                                    ov.push_back(v);
                                    continue;
                                }
                                auto const &Pv = rows[pv];
                                E nv = f.neg(v);
                                size_t sz = Pv.cols.size();
                                unsigned const *pc = Pv.cols.data();
                                E const *pk = Pv.coefs.data();
                                for (size_t k = 1; k < sz; ++k)
                                    lacc[pc[k]] += f.wide_mul(nv, pk[k]);
                                if (pc[sz - 1] > last)
                                    last = pc[sz - 1];
                                d.merge(Pv.dep);
                                charge(1 + static_cast<unsigned>(sz / 16));
                            }
                            lazy_done = true;
                        }
                    }
                    if (!lazy_done && scan) {
                        for (size_t c = first; c <= last; ++c) {
                            E v = acc[c];
                            if (f.is_zero(v))
                                continue;
                            acc[c] = f.zero();
                            eliminate(static_cast<unsigned>(c), v);
                        }
                    }
                    else if (!lazy_done) {
                        while (!heap.empty()) {
                            unsigned c = heap.top();
                            heap.pop();
                            inheap[c] = 0;
                            E v = acc[c];
                            acc[c] = f.zero();
                            if (f.is_zero(v))
                                continue;
                            eliminate(c, v);
                        }
                    }
                    if (oc.empty()) {
                        ++st.m_zero_reductions;
                        continue;
                    }
                    E li = f.inv(ov[0]);
                    for (auto &x : ov)
                        x = f.mul(x, li);
                    R.cols = std::move(oc);
                    R.coefs = std::move(ov);
                    R.dep = std::move(d);
                    pivrow[R.cols[0]] = static_cast<int>(r);
                    fresh.push_back(r);
                }
                // New basis elements, smallest leads first. Stable: rows sharing
                // a leading column (should not happen, but keep deterministic
                // if it ever does) retain their original processing order.
                std::stable_sort(fresh.begin(), fresh.end(), [&](unsigned a, unsigned b) { return rows[a].cols[0] > rows[b].cols[0]; });
                for (unsigned r : fresh) {
                    P p;
                    p.mons.reserve(rows[r].cols.size());
                    for (unsigned c : rows[r].cols)
                        p.mons.push_back(colmon[c]);
                    p.coefs = std::move(rows[r].coefs);
                    p.dep = std::move(rows[r].dep);
                    ++st.m_new_polys;
                    insert(std::move(p));
                    if (unit >= 0)
                        return;
                }
            }

        public:
            f4_solver(F const &f, mon_table &M, f4_config const &cfg, f4_stats &st,
                      std::function<void(unsigned)> const &charge)
                : f(f), M(M), cfg(cfg), st(st), charge_fn(charge), uops(f, charge), rng(cfg.seed * 0x9e3779b97f4a7c15ull + 1) {
                m_slice_budget = cfg.slice_budget;
                rational_bits(f.prime(), bits_p);
                rational_bits(div(f.prime() - rational(1), rational(2)), bits_half);
            }

            // Normal form of p modulo the current non-redundant basis (full reduction).
            P nf(P const &p, int exclude = -1) {
                P out;
                out.dep = p.dep;
                struct cmp_lt {
                    mon_table const *M;
                    bool operator()(unsigned a, unsigned b) const { return M->cmp(a, b) < 0; }
                };
                std::priority_queue<unsigned, std::vector<unsigned>, cmp_lt> heap(cmp_lt{&M});
                std::unordered_map<unsigned, E> acc;
                auto add = [&](unsigned m, E const &c) {
                    auto [it, fresh] = acc.emplace(m, c);
                    if (fresh)
                        heap.push(m);
                    else
                        it->second = f.add(it->second, c);
                };
                for (size_t k = 0; k < p.size(); ++k)
                    add(p.mons[k], p.coefs[k]);
                while (!heap.empty()) {
                    unsigned m = heap.top();
                    heap.pop();
                    auto it = acc.find(m);
                    E c = it->second;
                    acc.erase(it);
                    if (f.is_zero(c))
                        continue;
                    int g = find_reducer(m, exclude);
                    if (g < 0) {
                        out.mons.push_back(m);
                        out.coefs.push_back(c);
                        continue;
                    }
                    auto const &Gg = G[g];
                    unsigned q = M.quo(m, Gg.lm());
                    for (size_t k = 1; k < Gg.size(); ++k)
                        add(M.mul(q, Gg.mons[k]), f.neg(f.mul(c, Gg.coefs[k])));
                    out.dep.merge(Gg.dep);
                    charge(1 + static_cast<unsigned>(Gg.size() / 16));
                }
                return out;
            }

            // Computes a reduced Groebner basis of `input`. Returns false if 1 is
            // in the ideal; then `unit_poly` carries the dependencies.
            bool groebner(std::vector<P> input, std::vector<P> &basis, deps &unit_deps) {
                ++st.m_gb_calls;
                G.clear();
                redundant.clear();
                pairs.clear();
                unit = -1;
                // Stable: equations sharing a leading monomial keep their
                // original (caller-supplied) relative order instead of an
                // unspecified tie-break, so reduction/dependency tracking
                // stays deterministic across sort implementations.
                std::stable_sort(input.begin(), input.end(), [&](P const &a, P const &b) {
                    if (a.empty() || b.empty())
                        return !a.empty() && b.empty();
                    return M.cmp(a.lm(), b.lm()) < 0;
                });
                for (auto &p : input) {
                    if (p.empty())
                        continue;
                    // Reduce by the current basis to keep the initial basis small.
                    P r = G.empty() ? std::move(p) : nf(p);
                    insert(std::move(r));
                    if (unit >= 0)
                        break;
                }
                while (unit < 0 && !pairs.empty()) {
                    unsigned d = ~0u;
                    for (auto const &pr : pairs)
                        d = std::min(d, pr.deg);
                    std::vector<pair_t> sel, rest;
                    for (auto const &pr : pairs)
                        (pr.deg == d && sel.size() < cfg.max_pairs_per_step ? sel : rest).push_back(pr);
                    pairs.swap(rest);
                    f4_step(sel);
                }
                if (unit >= 0) {
                    unit_deps = G[unit].dep;
                    return false;
                }
                // Minimal basis: drop elements whose leading monomial is divisible by another's.
                std::vector<unsigned> keep;
                std::vector<unsigned> idx;
                for (unsigned g = 0; g < G.size(); ++g)
                    if (!redundant[g])
                        idx.push_back(g);
                // Stable: basis elements with an identical leading monomial
                // (the case this pass exists to resolve) keep insertion order,
                // so the earliest-derived representative is always kept.
                std::stable_sort(idx.begin(), idx.end(), [&](unsigned a, unsigned b) { return M.cmp(G[a].lm(), G[b].lm()) < 0; });
                for (unsigned g : idx) {
                    bool red = false;
                    for (unsigned k : keep)
                        if (M.divides(G[k].lm(), G[g].lm())) {
                            red = true;
                            break;
                        }
                    if (red)
                        redundant[g] = 1;
                    else
                        keep.push_back(g);
                }
                // Interreduce tails.
                basis.clear();
                for (unsigned g : keep) {
                    P r = nf(G[g], static_cast<int>(g));
                    make_monic(r);
                    basis.push_back(std::move(r));
                }
                // Replace G by the reduced basis so nf() uses reduced reducers.
                G = basis;
                redundant.assign(G.size(), 0);
                return true;
            }

            // -------------------------------------------------------------- roots
            void split_roots(U const &g, std::vector<E> &out, unsigned depth = 0) {
                size_t d = g.size() - 1;
                if (d == 0)
                    return;
                if (d == 1) {
                    out.push_back(f.neg(f.mul(g[0], f.inv(g[1]))));
                    return;
                }
                if (depth > 256)
                    throw exhausted();
                for (unsigned trial = 0; trial < 64; ++trial) {
                    U base{random_elem(), f.one()};
                    U w = uops.powmod(base, bits_half, g);
                    if (w.empty())
                        continue;
                    w[0] = f.sub(w[0], f.one());
                    U h = uops.gcd(g, w);
                    if (h.size() <= 1 || h.size() == g.size())
                        continue;
                    split_roots(h, out, depth + 1);
                    split_roots(uops.divexact(g, h), out, depth + 1);
                    return;
                }
                throw exhausted();
            }

            // All F_p roots of a non-zero univariate polynomial q.
            void roots(U q, std::vector<E> &out) {
                q = uops.monic(std::move(q));
                if (q.size() <= 1)
                    return;
                if constexpr (std::is_same<F, field64>::value) {
                    if (f.prime() <= rational(1 << 16)) {
                        uint64_t p = f.prime().get_uint64();
                        for (uint64_t x = 0; x < p; ++x) {
                            if (f.is_zero(uops.eval(q, f.from_uint(x))))
                                out.push_back(f.from_uint(x));
                            if ((x & 1023) == 0)
                                charge(1 + static_cast<unsigned>(q.size() / 64));
                        }
                        return;
                    }
                }
                U X{f.zero(), f.one()};
                U h = uops.powmod(X, bits_p, q);  // X^p mod q
                if (h.size() < 2)
                    h.resize(2, f.zero());
                h[1] = f.sub(h[1], f.one());
                uops.trim(h);
                U g = uops.gcd(q, h);  // product of (X - r) over the F_p roots of q
                split_roots(g, out);
            }

            // -------------------------------------------------------------- minimal polynomial
            // Minimal polynomial of the multiplication-by-x_v map on the quotient,
            // restricted to the cyclic subspace of 1. Its membership in the ideal is
            // checked before it is returned.
            bool minimal_polynomial(unsigned v, std::vector<unsigned> const &std_mons, U &q) {
                size_t D = std_mons.size();
                std::unordered_map<unsigned, unsigned> index;
                for (unsigned i = 0; i < D; ++i)
                    index[std_mons[i]] = i;
                // Sparse multiplication matrix: column i = NF(x_v * b_i).
                std::vector<std::vector<std::pair<unsigned, E>>> Mx(D);
                unsigned xv = M.var(v);
                for (unsigned i = 0; i < D; ++i) {
                    P t;
                    t.mons.push_back(M.mul(xv, std_mons[i]));
                    t.coefs.push_back(f.one());
                    P r = nf(t);
                    for (size_t k = 0; k < r.size(); ++k) {
                        auto it = index.find(r.mons[k]);
                        if (it == index.end())
                            return false;  // not a standard monomial: basis is not reduced
                        Mx[i].push_back({it->second, r.coefs[k]});
                    }
                }
                auto apply = [&](std::vector<E> const &x) {
                    std::vector<E> y(D, f.zero());
                    for (unsigned i = 0; i < D; ++i) {
                        if (f.is_zero(x[i]))
                            continue;
                        for (auto const &[j, c] : Mx[i])
                            y[j] = f.add(y[j], f.mul(x[i], c));
                    }
                    charge(1 + static_cast<unsigned>(D / 16));
                    return y;
                };
                unsigned one_idx = index.at(M.one());
                for (unsigned attempt = 0; attempt < 4; ++attempt) {
                    // Scalar sequence s_k = u . M^k e_1.
                    std::vector<E> u(D);
                    for (auto &x : u)
                        x = random_elem();
                    std::vector<E> x(D, f.zero());
                    x[one_idx] = f.one();
                    std::vector<E> s;
                    s.reserve(2 * D);
                    for (size_t k = 0; k < 2 * D; ++k) {
                        E acc = f.zero();
                        for (unsigned i = 0; i < D; ++i)
                            if (!f.is_zero(x[i]))
                                acc = f.add(acc, f.mul(u[i], x[i]));
                        s.push_back(acc);
                        if (k + 1 < 2 * D)
                            x = apply(x);
                    }
                    // Berlekamp-Massey.
                    U C{f.one()}, B{f.one()};
                    unsigned L = 0, m = 1;
                    E b = f.one();
                    for (size_t n = 0; n < s.size(); ++n) {
                        E d = s[n];
                        for (unsigned i = 1; i <= L && i < C.size(); ++i)
                            d = f.add(d, f.mul(C[i], s[n - i]));
                        if (f.is_zero(d)) {
                            ++m;
                            continue;
                        }
                        E coef = f.mul(d, f.inv(b));
                        U T = C;
                        if (C.size() < B.size() + m)
                            C.resize(B.size() + m, f.zero());
                        for (size_t i = 0; i < B.size(); ++i)
                            C[i + m] = f.sub(C[i + m], f.mul(coef, B[i]));
                        if (2 * L <= n) {
                            L = static_cast<unsigned>(n + 1 - L);
                            B = std::move(T);
                            b = d;
                            m = 1;
                        }
                        else
                            ++m;
                    }
                    U cand(L + 1, f.zero());
                    for (unsigned i = 0; i <= L; ++i)
                        cand[L - i] = i < C.size() ? C[i] : f.zero();
                    // Check cand(x_v) is in the ideal: cand(Mx) e_1 == 0.
                    std::vector<E> y(D, f.zero());
                    for (size_t i = cand.size(); i-- > 0;) {
                        y = apply(y);
                        y[one_idx] = f.add(y[one_idx], cand[i]);
                    }
                    bool zero = std::all_of(y.begin(), y.end(), [&](E const &e) { return f.is_zero(e); });
                    if (zero && L > 0) {
                        q = std::move(cand);
                        ++st.m_minpolys;
                        return true;
                    }
                }
                return false;
            }

            // Random slicing (SAT only). A positive-dimensional variety over a
            // large field has many F_p points (Lang-Weil); intersecting it with
            // x_v = r for random r keeps an F_p point with fair probability.
            // Failures never justify UNSAT: the caller reports l_undef.
            lbool slice(std::vector<P> const &basis, std::vector<unsigned> const &free_vars,
                        std::vector<E> &vals, unsigned depth) {
                if (m_slice_budget == 0)
                    return l_undef;
                unsigned v = free_vars[0];
                unsigned occ = 0;
                for (unsigned w : free_vars) {
                    unsigned c = 0;
                    for (auto const &g : basis)
                        for (unsigned m : g.mons)
                            c += M.exps(m)[w] ? 1 : 0;
                    if (c > occ) {
                        occ = c;
                        v = w;
                    }
                }
                for (unsigned attempt = 0; attempt < cfg.slice_attempts && m_slice_budget > 0; ++attempt) {
                    --m_slice_budget;
                    ++st.m_slices;
                    E r = attempt == 0 ? f.zero() : (attempt == 1 ? f.one() : random_elem());
                    std::vector<P> input = basis;
                    P lin;
                    lin.mons = {M.var(v), M.one()};
                    lin.coefs = {f.one(), f.neg(r)};
                    if (f.is_zero(r)) {
                        lin.mons.pop_back();
                        lin.coefs.pop_back();
                    }
                    input.push_back(std::move(lin));
                    std::vector<P> nb;
                    deps ud;
                    if (!groebner(std::move(input), nb, ud))
                        continue;
                    deps sub;
                    lbool res = model(nb, vals, sub, depth + 1);
                    if (res == l_true)
                        return l_true;
                }
                return l_undef;
            }

            // -------------------------------------------------------------- model construction
            lbool model(std::vector<P> const &basis, std::vector<E> &vals, deps &conflict, unsigned depth) {
                if (depth > cfg.max_depth)
                    return l_undef;
                unsigned n = M.num_vars();
                std::vector<int> pure_deg(n, 0);
                std::vector<char> active(n, 0);
                deps all;
                for (auto const &g : basis) {
                    all.merge(g.dep);
                    int v = M.pure_var(g.lm());
                    if (v >= 0) {
                        int k = static_cast<int>(M.deg(g.lm()));
                        if (pure_deg[v] == 0 || k < pure_deg[v])
                            pure_deg[v] = k;
                    }
                    for (unsigned m : g.mons) {
                        uint16_t const *e = M.exps(m);
                        for (unsigned i = 0; i < n; ++i)
                            if (e[i])
                                active[i] = 1;
                    }
                }
                bool linear = true;
                std::vector<unsigned> free_vars;
                for (unsigned i = 0; i < n; ++i) {
                    if (!active[i])
                        continue;
                    if (pure_deg[i] == 0)
                        free_vars.push_back(i);
                    else if (pure_deg[i] > 1)
                        linear = false;
                }
                if (!free_vars.empty()) {
                    ++st.m_positive_dim;
                    // Over a small field, adjoin the field equations x^p - x for the
                    // variables without a pure-power leading monomial. They hold at
                    // every F_p point, so the F_p solutions are unchanged, and the
                    // ideal becomes zero-dimensional.
                    if (f.prime() > rational(cfg.max_field_degree) || field_closed)
                        return cfg.slice_attempts ? slice(basis, free_vars, vals, depth) : l_undef;
                    unsigned pd = f.prime().get_unsigned();
                    // Estimated quotient size after closing all free variables.
                    double est = 1;
                    for (unsigned k = 0; k < free_vars.size() && est <= cfg.max_quotient_dim; ++k)
                        est *= pd;
                    if (est <= cfg.max_quotient_dim) {
                        std::vector<P> input = basis;
                        for (unsigned v : free_vars) {
                            P fe;
                            fe.mons = {M.var(v, pd), M.var(v, 1)};
                            fe.coefs = {f.one(), f.neg(f.one())};
                            input.push_back(std::move(fe));
                        }
                        ++st.m_field_closures;
                        std::vector<P> nb;
                        deps ud;
                        if (!groebner(std::move(input), nb, ud)) {
                            conflict = ud;
                            return l_false;
                        }
                        field_closed = true;
                        lbool res = model(nb, vals, conflict, depth + 1);
                        field_closed = false;
                        return res;
                    }
                    if (!cfg.value_split)
                        return cfg.slice_attempts ? slice(basis, free_vars, vals, depth) : l_undef;
                    // Too many free coordinates to close at once: branch on every
                    // value of one of them (exhaustive over F_p, so an UNSAT answer
                    // remains complete), visiting values in a random order so that
                    // satisfiable systems tend to be decided early.
                    unsigned v = free_vars[0];
                    unsigned occ = 0;
                    for (unsigned w : free_vars) {
                        unsigned c = 0;
                        for (auto const &g : basis)
                            for (unsigned m : g.mons)
                                c += M.exps(m)[w] ? 1 : 0;
                        if (c > occ) {
                            occ = c;
                            v = w;
                        }
                    }
                    std::vector<uint64_t> order(pd);
                    for (unsigned k = 0; k < pd; ++k)
                        order[k] = k;
                    for (unsigned k = pd; k-- > 1;)
                        std::swap(order[k], order[next_random() % (k + 1)]);
                    conflict = deps();
                    bool unknown = false;
                    for (uint64_t val : order) {
                        ++st.m_value_splits;
                        std::vector<P> input = basis;
                        P lin;
                        E r = f.from_uint(val);
                        lin.mons = {M.var(v), M.one()};
                        lin.coefs = {f.one(), f.neg(r)};
                        if (val == 0) {
                            lin.mons.pop_back();
                            lin.coefs.pop_back();
                        }
                        input.push_back(std::move(lin));
                        std::vector<P> nb;
                        deps ud;
                        if (!groebner(std::move(input), nb, ud)) {
                            conflict.merge(ud);
                            continue;
                        }
                        deps sub;
                        lbool res = model(nb, vals, sub, depth + 1);
                        if (res == l_true)
                            return l_true;
                        if (res == l_undef)
                            unknown = true;
                        else
                            conflict.merge(sub);
                    }
                    return unknown ? l_undef : l_false;
                }
                if (linear) {
                    // Reduced basis with linear leads: x_i - c_i.
                    std::fill(vals.begin(), vals.end(), f.zero());
                    for (auto const &g : basis) {
                        int v = M.pure_var(g.lm());
                        if (v < 0)
                            return l_undef;
                        E c = g.size() > 1 ? g.coefs[1] : f.zero();
                        if (g.size() > 2 || (g.size() == 2 && g.mons[1] != M.one()))
                            return l_undef;
                        vals[v] = f.neg(c);
                    }
                    return l_true;
                }
                // Standard monomials.
                std::vector<unsigned> std_mons{M.one()};
                std::unordered_set<unsigned> seen{M.one()};
                for (size_t k = 0; k < std_mons.size(); ++k) {
                    for (unsigned i = 0; i < n; ++i) {
                        if (!active[i])
                            continue;
                        unsigned m = M.mul(std_mons[k], M.var(i));
                        if (seen.count(m))
                            continue;
                        bool reducible = false;
                        for (auto const &g : basis)
                            if (M.divides(g.lm(), m)) {
                                reducible = true;
                                break;
                            }
                        if (reducible)
                            continue;
                        seen.insert(m);
                        std_mons.push_back(m);
                        if (std_mons.size() > cfg.max_quotient_dim) {
                            ++st.m_large_quotient;
                            return l_undef;
                        }
                    }
                }
                // Branch variable: largest pure power degree.
                unsigned v = 0;
                int best = 0;
                for (unsigned i = 0; i < n; ++i)
                    if (active[i] && pure_deg[i] > best) {
                        best = pure_deg[i];
                        v = i;
                    }
                // Load `basis` as the reducer set for nf().
                G = basis;
                redundant.assign(G.size(), 0);
                U q;
                if (!minimal_polynomial(v, std_mons, q))
                    return l_undef;
                std::vector<E> rs;
                roots(q, rs);
                st.m_roots += static_cast<unsigned>(rs.size());
                conflict = all;  // q(x_v) is a consequence of the whole basis
                if (rs.empty())
                    return l_false;
                bool unknown = false;
                for (E const &r : rs) {
                    ++st.m_splits;
                    std::vector<P> input = basis;
                    P lin;
                    lin.mons = {M.var(v), M.one()};
                    lin.coefs = {f.one(), f.neg(r)};
                    if (f.is_zero(r)) {
                        lin.mons.pop_back();
                        lin.coefs.pop_back();
                    }
                    input.push_back(std::move(lin));
                    std::vector<P> nb;
                    deps ud;
                    if (!groebner(std::move(input), nb, ud)) {
                        conflict.merge(ud);
                        continue;
                    }
                    deps sub;
                    lbool res = model(nb, vals, sub, depth + 1);
                    if (res == l_true)
                        return l_true;
                    if (res == l_undef)
                        unknown = true;
                    else
                        conflict.merge(sub);
                }
                return unknown ? l_undef : l_false;
            }
        };

        // ------------------------------------------------------------------
        template <class F>
        lbool solve_with(F const &f, std::vector<polynomial> const &eqs, std::vector<polynomial> const &neqs,
                         unsigned num_vars, std::vector<rational> &values, std::set<unsigned> &conflict,
                         f4_config const &cfg, f4_stats &st, std::function<void(unsigned)> const &charge,
                         std::vector<polynomial> *reduced_basis) {
            using E = typename F::elem;
            // Dense renumbering of variables and premises.
            std::unordered_map<unsigned, unsigned> var_index, dep_index;
            std::vector<unsigned> var_of, dep_of;
            auto scan = [&](polynomial const &p) {
                for (auto const &[mon, c] : p)
                    for (unsigned v : mon)
                        if (var_index.emplace(v, static_cast<unsigned>(var_of.size())).second)
                            var_of.push_back(v);
                for (unsigned d : p.dependencies)
                    if (dep_index.emplace(d, static_cast<unsigned>(dep_of.size())).second)
                        dep_of.push_back(d);
            };
            for (auto const &p : eqs)
                scan(p);
            for (auto const &p : neqs)
                scan(p);
            // Variable IDs belong to the declared problem as well as its model buffer.
            for (unsigned v : var_of)
                if (v >= num_vars || v >= values.size())
                    return l_undef;
            if (var_of.size() > cfg.max_vars) {
                ++st.m_unsupported;
                return l_undef;
            }
            // Disequalities introduce real dense coordinates too. Check the
            // sum without overflow before allocating exponent vectors.
            if (neqs.size() > cfg.max_vars - var_of.size()) {
                ++st.m_unsupported;
                return l_undef;
            }
            unsigned n_orig = static_cast<unsigned>(var_of.size());
            unsigned n = n_orig + static_cast<unsigned>(neqs.size());
            if (n == 0)
                n = 1;
            mon_table M(n, cfg.max_monomials, charge);
            f4_solver<F> S(f, M, cfg, st, charge);
            auto convert = [&](polynomial const &p, int rabinowitsch) {
                poly<F> q;
                for (unsigned d : p.dependencies)
                    q.dep.add(dep_index.at(d));
                std::vector<std::pair<unsigned, E>> terms;
                for (auto const &[mon, c] : p) {
                    E e = f.from(c);
                    if (f.is_zero(e))
                        continue;
                    uint16_t *x = M.tmp();
                    std::fill(x, x + n, 0);
                    for (unsigned v : mon) {
                        auto &degree = x[var_index.at(v)];
                        if (degree >= 60000) throw exhausted();
                        ++degree;
                    }
                    if (rabinowitsch >= 0)
                        ++x[rabinowitsch];
                    terms.push_back({M.mk_scratch(), e});
                }
                if (rabinowitsch >= 0)
                    terms.push_back({M.one(), f.neg(f.one())});
                std::sort(terms.begin(), terms.end(), [&](auto const &a, auto const &b) { return M.cmp(a.first, b.first) > 0; });
                for (auto const &[m, c] : terms) {
                    if (!q.mons.empty() && q.mons.back() == m) {
                        q.coefs.back() = f.add(q.coefs.back(), c);
                        if (f.is_zero(q.coefs.back())) {
                            q.mons.pop_back();
                            q.coefs.pop_back();
                        }
                        continue;
                    }
                    q.mons.push_back(m);
                    q.coefs.push_back(c);
                }
                return q;
            };
            std::vector<poly<F>> input;
            for (auto const &p : eqs)
                input.push_back(convert(p, -1));
            for (unsigned i = 0; i < neqs.size(); ++i) {
                // A zero disequality polynomial yields the unit -1, hence UNSAT.
                input.push_back(convert(neqs[i], static_cast<int>(n_orig + i)));
            }
            auto export_deps = [&](deps const &d) {
                d.for_each([&](unsigned i) { conflict.insert(dep_of[i]); });
            };
            std::vector<poly<F>> basis;
            deps ud;
            if (!S.groebner(std::move(input), basis, ud)) {
                conflict.clear();
                export_deps(ud);
                return l_false;
            }
            if (reduced_basis && neqs.empty()) {
                reduced_basis->clear();
                for (auto const &g : basis) {
                    polynomial out;
                    for (size_t k = 0; k < g.size(); ++k) {
                        monomial mon;
                        uint16_t const *e = M.exps(g.mons[k]);
                        for (unsigned i = 0; i < n_orig; ++i)
                            for (unsigned j = 0; j < e[i]; ++j)
                                mon.push_back(var_of[i]);
                        std::sort(mon.begin(), mon.end());
                        out.emplace(std::move(mon), f.to(g.coefs[k]));
                    }
                    g.dep.for_each([&](unsigned i) { out.dependencies.insert(dep_of[i]); });
                    reduced_basis->push_back(std::move(out));
                }
            }
            std::vector<E> vals(n, f.zero());
            deps cd;
            lbool r = S.model(basis, vals, cd, 0);
            if (r == l_false) {
                conflict.clear();
                export_deps(cd);
                return l_false;
            }
            if (r != l_true)
                return l_undef;
            for (unsigned i = 0; i < n_orig; ++i)
                if (var_of[i] < values.size())
                    values[var_of[i]] = f.to(vals[i]);
            // Independent check of the original constraints.
            auto eval = [&](polynomial const &p) {
                rational acc(0);
                for (auto const &[mon, c] : p) {
                    rational t = c;
                    for (unsigned v : mon)
                        t = mod(t * values[v], f.prime());
                    acc = mod(acc + t, f.prime());
                }
                return acc;
            };
            for (auto const &p : eqs)
                if (!eval(p).is_zero())
                    return l_undef;
            for (auto const &p : neqs)
                if (eval(p).is_zero())
                    return l_undef;
            return l_true;
        }
    }  // namespace

    lbool f4_solve(rational const &p, std::vector<polynomial> const &eqs, std::vector<polynomial> const &neqs,
                   unsigned num_vars, std::vector<rational> &values, std::set<unsigned> &conflict,
                   f4_config const &cfg, f4_stats &stats, std::function<void(unsigned)> const &charge,
                   std::vector<polynomial> *reduced_basis) {
        if (field64::fits(p)) {
            field64 f(p);
            return solve_with(f, eqs, neqs, num_vars, values, conflict, cfg, stats, charge, reduced_basis);
        }
        if (field256::fits(p)) {
            field256 f(p);
            // Four-limb arithmetic costs several times a one-limb operation;
            // weigh the work units so budgets track time across fields.
            std::function<void(unsigned)> weighted = [&](unsigned k) { charge(4 * k); };
            return solve_with(f, eqs, neqs, num_vars, values, conflict, cfg, stats, weighted, reduced_basis);
        }
        ++stats.m_unsupported;
        return l_undef;
    }
#else
    bool f4_supported(rational const &) { return false; }

    lbool f4_solve(rational const &, std::vector<polynomial> const &, std::vector<polynomial> const &,
                   unsigned, std::vector<rational> &, std::set<unsigned> &,
                   f4_config const &, f4_stats &stats, std::function<void(unsigned)> const &,
                   std::vector<polynomial> *) {
        ++stats.m_unsupported;
        return l_undef;
    }
#endif
}  // namespace ff
