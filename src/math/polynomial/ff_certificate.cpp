#include "math/polynomial/ff_certificate.h"
#include <algorithm>
#include <queue>
#include <tuple>

namespace ff {
    class certificate_builder {
        engine &e;
        certificate proof;
        unsigned max_nodes;
        size_t bytes = 0;
        struct row { polynomial value; unsigned proof; };
        std::vector<row> basis;
        using pair = std::tuple<unsigned, unsigned, unsigned>;
        std::priority_queue<pair, std::vector<pair>, std::greater<pair>> pairs;

        unsigned record(certificate::node n) {
            e.tick();
            // Bound retained DAG storage, including vector growth and owned
            // coefficient/factor storage. This is an estimate, not process RSS.
            size_t cost = 3 * (sizeof(n) + n.factor.capacity() * sizeof(unsigned) +
                              2 * (e.p.get_num_bits() / 8 + 1));
            if (proof.nodes.size() >= max_nodes || cost > 16 * 1024 * 1024 - bytes)
                throw exhausted();
            bytes += cost;
            unsigned id = proof.nodes.size();
            proof.nodes.push_back(std::move(n));
            return id;
        }
        unsigned multiply(unsigned id, rational const &c, monomial const &m) {
            if (c.is_one() && m.empty()) return id;
            return record({certificate::rule::multiply, id, 0, c, m});
        }
        unsigned add(unsigned a, unsigned b) {
            return record({certificate::rule::add, a, b, rational(1), {}});
        }
        row reduce(row f) {
            polynomial remainder;
            while (!f.value.empty()) {
                e.tick();
                auto [mon, coefficient] = *f.value.begin();
                bool reduced = false;
                for (auto const &b : basis) {
                    e.tick();
                    auto const &lead = b.value.begin()->first;
                    if (!std::includes(mon.begin(), mon.end(), lead.begin(), lead.end())) continue;
                    monomial q;
                    std::set_difference(mon.begin(), mon.end(), lead.begin(), lead.end(), std::back_inserter(q));
                    rational c = mod(-coefficient * e.inverse(b.value.begin()->second), e.p);
                    polynomial multiplier;
                    e.add_term(multiplier, q, c);
                    f.value = e.add(std::move(f.value), e.mul(multiplier, b.value));
                    // Invariant: this ID denotes remainder + f.value. Moving
                    // irreducible terms to remainder changes no polynomial;
                    // subtraction records the exact monomial reducer multiple.
                    f.proof = add(f.proof, multiply(b.proof, c, q));
                    reduced = true;
                    break;
                }
                if (!reduced) {
                    e.add_term(remainder, mon, coefficient);
                    f.value.erase(f.value.begin());
                }
            }
            f.value = std::move(remainder);
            return f;
        }
        bool insert(row f) {
            f = reduce(std::move(f));
            if (f.value.empty()) return false;
            rational c = e.inverse(f.value.begin()->second);
            f.value = e.scale(std::move(f.value), c);
            f.proof = multiply(f.proof, c, {});
            if (f.value.size() == 1 && f.value.begin()->first.empty()) {
                // Normalization makes the derived nonzero constant exactly 1.
                proof.root = f.proof;
                return true;
            }
            if (basis.size() >= 256) throw exhausted();
            auto const &right = f.value.begin()->first;
            for (unsigned j = 0; j < basis.size(); ++j) {
                e.tick();
                auto const &left = basis[j].value.begin()->first;
                monomial lcm;
                std::set_union(left.begin(), left.end(), right.begin(), right.end(), std::back_inserter(lcm));
                // Product pairs cannot help complete a Groebner basis. More
                // importantly, search scheduling is never trusted by the checker:
                // acceptance depends only on an explicit derivation of 1.
                if (lcm.size() != left.size() + right.size())
                    pairs.emplace(lcm.size(), j, basis.size());
            }
            basis.push_back(std::move(f));
            return false;
        }
    public:
        certificate_builder(engine &e, unsigned max_nodes) : e(e), max_nodes(std::min(max_nodes, 100000u)) {}
        bool run(std::vector<polynomial> const &equations, certificate &out, bool linear_first = false) {
            // Linear and sparse equations can eliminate variables before
            // nonlinear input rows create large intermediate polynomials.
            // This only changes search order: input nodes retain their original
            // equation indices, and the checker still replays every multiplier.
            std::vector<std::tuple<unsigned, size_t, unsigned>> order;
            for (unsigned i = 0; i < equations.size(); ++i) {
                unsigned degree = 0;
                if (linear_first) for (auto const &[mon, coefficient] : equations[i]) {
                    e.tick();
                    degree = std::max(degree, static_cast<unsigned>(mon.size()));
                }
                order.emplace_back(degree, equations[i].size(), i);
            }
            if (linear_first) std::sort(order.begin(), order.end());
            for (auto const &[degree, size, i] : order) {
                unsigned id = record({certificate::rule::input, i, 0, rational(1), {}});
                if (insert({equations[i], id})) { out = std::move(proof); return true; }
            }
            while (!pairs.empty()) {
                e.tick();
                auto [degree, a, b] = pairs.top(); pairs.pop();
                auto const &ma = basis[a].value.begin()->first;
                auto const &mb = basis[b].value.begin()->first;
                monomial lcm, qa, qb;
                std::set_union(ma.begin(), ma.end(), mb.begin(), mb.end(), std::back_inserter(lcm));
                std::set_difference(lcm.begin(), lcm.end(), ma.begin(), ma.end(), std::back_inserter(qa));
                std::set_difference(lcm.begin(), lcm.end(), mb.begin(), mb.end(), std::back_inserter(qb));
                polynomial fa, fb;
                e.add_term(fa, qa, rational(1));
                e.add_term(fb, qb, rational(-1));
                auto value = e.add(e.mul(fa, basis[a].value), e.mul(fb, basis[b].value));
                unsigned left = multiply(basis[a].proof, rational(1), qa);
                unsigned right = multiply(basis[b].proof, e.p - rational(1), qb);
                unsigned id = add(left, right);
                if (insert({std::move(value), id})) { out = std::move(proof); return true; }
            }
            return false;
        }
    };
    bool certify(engine &arithmetic, std::vector<polynomial> const &equations,
                 certificate &output, unsigned max_nodes) {
        try {
            // Preserve the original schedule when it succeeds. A different
            // insertion order can help after a basis/storage bound is hit, but
            // is not uniformly better for all systems.
            return certificate_builder(arithmetic, max_nodes).run(equations, output);
        }
        catch (exhausted const &) {
            // The failed builder has been destroyed. Reuse the SAME engine:
            // work already spent, term bounds and cancellation remain charged.
            // Only the discarded search/DAG state starts over, never the budget.
            return certificate_builder(arithmetic, max_nodes).run(equations, output, true);
        }
    }
}
