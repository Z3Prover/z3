/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_tiny.cpp

Abstract:

    Finite-domain search over tiny prime fields. See ff_tiny.h.

Author:

    Romain Soulat

--*/
#include "math/polynomial/ff_tiny.h"
#include <algorithm>
#include <bit>

namespace ff {

    namespace {

        class tiny_solver {
            using mask = uint64_t;
            struct entry {
                uint32_t var;
                mask old;
                bool assign;
            };
            uint32_t p;
            unsigned n;
            std::vector<tiny_constraint> const &cs;
            std::function<void(unsigned)> const &charge;
            tiny_stats &st;
            std::vector<std::vector<uint32_t>> cvars;     // distinct variables per constraint
            std::vector<std::vector<uint32_t>> var_cons;  // constraints per variable
            std::vector<unsigned> maxdeg;                 // max power of one variable per constraint
            std::vector<int> val;
            std::vector<mask> dom;
            std::vector<unsigned> nfree;
            std::vector<entry> trail;
            std::vector<uint32_t> queue;
            std::vector<std::vector<uint32_t>> pw;        // pw[a][k] = a^k mod p
            std::vector<uint64_t> coef;
            unsigned pending = 0;

            void work(unsigned k) {
                pending += k;
                if (pending >= 4096) {
                    unsigned w = pending;
                    pending = 0;
                    charge(w);
                }
            }

            void assign(uint32_t v, uint32_t a) {
                trail.push_back({v, dom[v], true});
                dom[v] = mask(1) << a;
                val[v] = static_cast<int>(a);
                for (uint32_t c : var_cons[v])
                    --nfree[c];
                queue.push_back(v);
            }

            void undo(size_t mark) {
                while (trail.size() > mark) {
                    entry e = trail.back();
                    trail.pop_back();
                    if (e.assign) {
                        val[e.var] = -1;
                        for (uint32_t c : var_cons[e.var])
                            ++nfree[c];
                    }
                    dom[e.var] = e.old;
                }
            }

            // Restrict the domain of the only unassigned variable of c (or check c
            // when all its variables are assigned). Returns false on a conflict.
            bool filter(uint32_t ci) {
                tiny_constraint const &c = cs[ci];
                int u = -1;
                for (uint32_t v : cvars[ci])
                    if (val[v] < 0) {
                        u = static_cast<int>(v);
                        break;
                    }
                ++st.filters;
                unsigned D = maxdeg[ci];
                std::fill(coef.begin(), coef.begin() + D + 1, 0);
                for (auto const &t : c.terms) {
                    work(1 + static_cast<unsigned>(t.vars.size()));
                    uint64_t prod = t.coef;
                    unsigned k = 0;
                    for (uint32_t v : t.vars) {
                        if (static_cast<int>(v) == u)
                            ++k;
                        else
                            prod = prod * static_cast<uint64_t>(val[v]) % p;
                    }
                    coef[k] += prod;
                }

                if (u < 0) {
                    bool zero = coef[0] % p == 0;
                    return c.is_neq ? !zero : zero;
                }
                for (unsigned k = 0; k <= D; ++k)
                    coef[k] %= p;
                mask d = dom[u], nd = 0;
                for (mask r = d; r; r &= r - 1) {
                    unsigned a = static_cast<unsigned>(std::countr_zero(r));
                    uint64_t s = 0;
                    auto const &pa = pw[a];
                    for (unsigned k = 0; k <= D; ++k)
                        s += coef[k] * pa[k];
                    bool zero = s % p == 0;
                    if (zero != c.is_neq)
                        nd |= mask(1) << a;
                }
                work(D + 1);
                if (nd == d)
                    return true;
                if (!nd)
                    return false;
                if ((nd & (nd - 1)) == 0)
                    assign(static_cast<uint32_t>(u), static_cast<uint32_t>(std::countr_zero(nd)));
                else {
                    trail.push_back({static_cast<uint32_t>(u), d, false});
                    dom[u] = nd;
                }
                return true;
            }

            bool propagate() {
                while (!queue.empty()) {
                    uint32_t v = queue.back();
                    queue.pop_back();
                    for (uint32_t c : var_cons[v])
                        if (nfree[c] <= 1 && !filter(c)) {
                            queue.clear();
                            return false;
                        }
                }
                return true;
            }

            bool search() {
                // Explicit choice stack: the number of free variables is not
                // a safe bound on native recursion depth. Trail marks retain
                // exactly the parent domains for each remaining alternative.
                struct choice { uint32_t var; mask remaining; size_t mark; };
                std::vector<choice> choices;
                for (;;) {
                    ++st.nodes;
                    work(1);
                    if (propagate()) {
                        int best = -1;
                        unsigned bs = 65;
                        for (unsigned v = 0; v < n; ++v) {
                            if (val[v] >= 0) continue;
                            unsigned c = static_cast<unsigned>(std::popcount(dom[v]));
                            if (c < bs || (c == bs && var_cons[v].size() > var_cons[best].size())) {
                                bs = c;
                                best = static_cast<int>(v);
                            }
                        }
                        if (best < 0) return true;
                        choices.push_back({static_cast<uint32_t>(best), dom[best], trail.size()});
                    }
                    bool next = false;
                    while (!choices.empty()) {
                        auto &c = choices.back();
                        undo(c.mark);
                        if (c.remaining) {
                            unsigned a = static_cast<unsigned>(std::countr_zero(c.remaining));
                            c.remaining &= c.remaining - 1;
                            assign(c.var, a);
                            next = true;
                            break;
                        }
                        choices.pop_back();
                    }
                    if (!next) return false;
                }
            }

        public:
            tiny_solver(uint32_t p, unsigned n, std::vector<tiny_constraint> const &cs,
                        std::function<void(unsigned)> const &charge, tiny_stats &st)
                : p(p), n(n), cs(cs), charge(charge), st(st) {}

            lbool run(std::vector<uint32_t> &model) {
                charge(0);
                cvars.resize(cs.size());
                var_cons.assign(n, {});
                maxdeg.assign(cs.size(), 0);
                nfree.assign(cs.size(), 0);
                unsigned D = 0;
                for (unsigned i = 0; i < cs.size(); ++i) {
                    for (auto const &t : cs[i].terms) {
                        work(1 + static_cast<unsigned>(t.vars.size()));
                        for (uint32_t v : t.vars)
                            cvars[i].push_back(v);
                        for (size_t j = 0; j < t.vars.size();) {
                            size_t k = j;
                            while (k < t.vars.size() && t.vars[k] == t.vars[j])
                                ++k;
                            maxdeg[i] = std::max<unsigned>(maxdeg[i], static_cast<unsigned>(k - j));
                            j = k;
                        }
                    }
                    std::sort(cvars[i].begin(), cvars[i].end());
                    cvars[i].erase(std::unique(cvars[i].begin(), cvars[i].end()), cvars[i].end());
                    for (uint32_t v : cvars[i])
                        var_cons[v].push_back(i);
                    nfree[i] = static_cast<unsigned>(cvars[i].size());
                    D = std::max(D, maxdeg[i]);
                }
                coef.assign(D + 1, 0);
                pw.assign(p, std::vector<uint32_t>(D + 1, 0));
                for (uint32_t a = 0; a < p; ++a) {
                    uint64_t x = 1;
                    for (unsigned k = 0; k <= D; ++k) {
                        work(1);
                        pw[a][k] = static_cast<uint32_t>(x);
                        x = x * a % p;
                    }
                }
                val.assign(n, -1);
                dom.assign(n, p == 64 ? ~mask(0) : (mask(1) << p) - 1);
                // Ground constraints and univariate constraints are filtered once
                // before the search; later filtering is triggered by assignments.
                for (unsigned i = 0; i < cs.size(); ++i)
                    if (nfree[i] <= 1 && !filter(i))
                        return l_false;
                bool sat = search();
                charge(pending);
                pending = 0;
                if (!sat) return l_false;
                model.assign(n, 0);
                for (unsigned v = 0; v < n; ++v)
                    model[v] = static_cast<uint32_t>(val[v]);
                return l_true;
            }
        };

    }  // namespace

    lbool tiny_search(uint32_t p, unsigned num_vars, std::vector<tiny_constraint> const &cs,
                      std::vector<uint32_t> &model, std::function<void(unsigned)> const &charge,
                      tiny_stats &st) {
        tiny_solver s(p, num_vars, cs, charge, st);
        return s.run(model);
    }

}  // namespace ff
