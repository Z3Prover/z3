/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_certificate.cpp

Abstract:

    Bounded reconstruction of ideal-membership certificates from the
    original polynomial equations. See ff_certificate.h.

Author:

    Romain Soulat

--*/
#include "math/ff/ff_certificate.h"
#include <algorithm>
#include "math/ff/ff_f4.h"
#include "math/ff/ff_unique.h"
#include <queue>
#include <tuple>
#include "util/util.h"

namespace ff {
    class certificate_builder : public elimination_observer, public polynomial_observer, public ff_unique::observer {
        engine &e;
        certificate proof;
        unsigned max_nodes;
        unsigned input_count = 0, zero_proof = ~0u;
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
            if (proof.nodes.size() >= max_nodes) throw exhausted{"proof-nodes"};
            if (cost > 16 * 1024 * 1024 - bytes) throw exhausted{"proof-bytes"};
            bytes += cost;
            unsigned id = proof.nodes.size();
            proof.nodes.push_back(std::move(n));
            return id;
        }
        unsigned multiply(unsigned id, rational const &c, monomial const &m) override {
            if (c.is_one() && m.empty()) return id;
            return record({certificate::rule::multiply, id, 0, c, m});
        }
        unsigned add(unsigned a, unsigned b) override {
            return record({certificate::rule::add, a, b, rational(1), {}});
        }
        void finish_native(certificate &out) {
            // Search may generate valid rows that do not participate in the
            // final contradiction. Export only ancestors of the root; retaining
            // dead rows needlessly makes checking depend on abandoned searches.
            std::vector<bool> live(proof.nodes.size(), false);
            std::vector<unsigned> pending{proof.root}, renamed(proof.nodes.size(), ~0u);
            while (!pending.empty()) {
                e.tick();
                unsigned id = pending.back(); pending.pop_back();
                if (live[id]) continue;
                live[id] = true;
                auto const &n = proof.nodes[id];
                // Local Boolean-branch hypotheses are internal placeholders.
                // Successful export must have discharged every one of them.
                if (n.kind == certificate::rule::input && n.left >= input_count) throw exhausted();
                if (n.kind != certificate::rule::input) pending.push_back(n.left);
                if (n.kind == certificate::rule::add) pending.push_back(n.right);
            }
            certificate compact;
            for (unsigned id = 0; id < proof.nodes.size(); ++id) {
                e.tick();
                if (!live[id]) continue;
                auto n = proof.nodes[id];
                if (n.kind != certificate::rule::input) n.left = renamed[n.left];
                if (n.kind == certificate::rule::add) n.right = renamed[n.right];
                renamed[id] = compact.nodes.size();
                compact.nodes.push_back(std::move(n));
            }
            compact.root = renamed[proof.root];
            out = std::move(compact);
        }
        bool import_f4(certificate const &local, std::vector<polynomial> const &residual) override {
            // F4 numbers its inputs in the residual equation array. Import
            // only the final root's ancestors and replace every local input
            // by the evidence that produced that residual from original inputs.
            std::vector<bool> live(local.nodes.size(), false);
            std::vector<unsigned> pending{local.root}, ids(local.nodes.size(), ~0u);
            while (!pending.empty()) {
                e.tick();
                unsigned id = pending.back(); pending.pop_back();
                if (id >= local.nodes.size()) throw exhausted();
                if (live[id]) continue;
                live[id] = true;
                auto const &n = local.nodes[id];
                if (n.kind != certificate::rule::input) {
                    if (n.left >= id) throw exhausted();
                    pending.push_back(n.left);
                }
                if (n.kind == certificate::rule::add) {
                    if (n.right >= id) throw exhausted();
                    pending.push_back(n.right);
                }
            }
            for (unsigned id = 0; id < local.nodes.size(); ++id) {
                e.tick();
                if (!live[id]) continue;
                auto const &n = local.nodes[id];
                if (n.kind == certificate::rule::input) {
                    if (n.left >= residual.size()) throw exhausted();
                    auto const &f = residual[n.left];
                    ids[id] = f.empty() ? multiply(0, rational(0), {}) : f.derivation;
                    if (ids[id] == ~0u) throw exhausted();
                }
                else if (n.kind == certificate::rule::multiply)
                    ids[id] = multiply(ids[n.left], n.coefficient, n.factor);
                else ids[id] = add(ids[n.left], ids[n.right]);
            }
            proof.root = ids[local.root];
            return true;
        }
        unsigned remaining_nodes() const override { return max_nodes - static_cast<unsigned>(proof.nodes.size()); }
        bool contradiction(polynomial const &f) override {
            if (f.size() != 1 || !f.begin()->first.empty() || f.derivation == ~0u) return false;
            proof.root = multiply(f.derivation, e.inverse(f.begin()->second), {});
            return true;
        }
        std::vector<unsigned> elimination_proofs;
        unsigned substitution(unsigned row, unsigned definition, polynomial const &before,
                          unsigned variable, polynomial const &value,
                          rational const &pivot) override {
            unsigned id = substitute_identity(elimination_proofs[row], elimination_proofs[definition],
                                              before, variable, value, pivot);
            elimination_proofs[row] = id;
            return id;
        }
        unsigned substitute_identity(unsigned id, unsigned definition, polynomial const &before,
                                     unsigned variable, polynomial const &value, rational const &pivot) {
            if (id == ~0u || definition == ~0u) throw exhausted();
            rational factor = mod(-e.inverse(pivot), e.p);
            // For the defining equation d=c*(v-t), record
            // f[v:=t] = f - (d/c)*sum_m a*m*sum_{i=0}^{k-1} v^(k-1-i)*t^i.
            // This is the identity v^k-t^k=(v-t)*sum v^(k-1-i)*t^i;
            // it covers repeated occurrences and nonlinear definitions without
            // expanding a global multiplier or trusting substitution itself.
            for (auto const &[mon, coefficient] : before) {
                e.tick();
                monomial rest;
                unsigned degree = 0;
                for (unsigned v : mon) {
                    if (v == variable) ++degree;
                    else rest.push_back(v);
                }
                if (!degree) continue;
                polynomial power;
                e.add_term(power, rest, mod(coefficient * factor, e.p));
                for (unsigned i = 0; i < degree; ++i) {
                    for (auto const &[m, c] : power) {
                        e.tick();
                        monomial multiplier = m;
                        multiplier.insert(std::upper_bound(multiplier.begin(), multiplier.end(), variable),
                                          degree - 1 - i, variable);
                        id = add(id, multiply(definition, c, multiplier));
                    }
                    if (i + 1 < degree) power = e.mul(power, value);
                }
            }
            return id;
        }
        unsigned scale(unsigned id, rational const &c) override {
            if (id == ~0u) throw exhausted();
            return multiply(id, c, {});
        }
        unsigned sum(unsigned a, unsigned b) override {
            if (a == ~0u || b == ~0u) throw exhausted();
            return add(a, b);
        }
        static polynomial to_polynomial(ff_unique::poly const &f) {
            polynomial r;
            r.insert(f.begin(), f.end());
            r.derivation = f.derivation;
            return r;
        }
        static ff_unique::poly to_unique(polynomial const &f) {
            ff_unique::poly r;
            r.insert(f.begin(), f.end());
            r.derivation = f.derivation;
            return r;
        }
        ff_unique::poly substitute(ff_unique::poly const &row, unsigned variable,
                                   ff_unique::poly const &definition) override {
            polynomial before = to_polynomial(row), value;
            auto pivot = definition.find(monomial{variable});
            if (pivot == definition.end() || !pivot->second.is_one()) throw exhausted();
            for (auto const &[m, c] : definition) {
                if (m == monomial{variable}) continue;
                if (std::find(m.begin(), m.end(), variable) != m.end()) throw exhausted();
                e.add_term(value, m, mod(-c, e.p));
            }
            // No synthetic input is introduced: the normalized definition has
            // an existing proof handle, and the same substitution identity used
            // by wire elimination connects the result to the original row.
            auto result = e.substitute(before, variable, value);
            result.derivation = substitute_identity(row.derivation, definition.derivation,
                                                    before, variable, value, rational(1));
            return to_unique(result);
        }
        void conflict(ff_unique::poly const &f) override {
            if (!contradiction(to_polynomial(f))) throw exhausted();
        }
        unsigned assume(unsigned variable, rational const &value) override {
            // The state records the meaning v-value=0. This out-of-range input
            // is never an exportable axiom; finish_native rejects any survivor.
            (void)variable; (void)value;
            return record({certificate::rule::input, ~0u, 0, rational(1), {}});
        }
        unsigned branch_result() const override { return proof.root; }
        unsigned zero() {
            if (zero_proof == ~0u) zero_proof = add(0, multiply(0, e.p-rational(1), {}));
            return zero_proof;
        }
        // If root proves 1=A+B*h and target proves T=0, return proofs of
        // A=0 and B*T=0. The derivation is linear in its input hypotheses:
        // replace h by zero for A and by target for B*T, with all other inputs
        // zero in the latter traversal. Never expand B as a polynomial.
        std::pair<unsigned, unsigned> discharge(unsigned root, unsigned hypothesis, unsigned target) {
            unsigned count = proof.nodes.size();
            if (root >= count || hypothesis >= count || target >= count) throw exhausted();
            std::vector<bool> live(count, false), affected(count, false);
            std::vector<unsigned> pending{root}, rewritten(count, ~0u), lifted(count, ~0u);
            // ~0u here means the algebraic zero, not a missing premise. It is
            // eliminated by neutral-element rules or materialized by zero().
            auto sum = [&](unsigned a, unsigned b) {
                return a == ~0u ? b : b == ~0u ? a : add(a, b);
            };
            while (!pending.empty()) {
                e.tick();
                unsigned id = pending.back(); pending.pop_back();
                if (id >= count) throw exhausted();
                if (live[id]) continue;
                live[id] = true;
                auto const &n = proof.nodes[id];
                if (n.kind != certificate::rule::input) pending.push_back(n.left);
                if (n.kind == certificate::rule::add) pending.push_back(n.right);
            }
            for (unsigned i = 0; i < count; ++i) {
                e.tick();
                if (!live[i]) continue;
                auto n = proof.nodes[i]; // recording below can reallocate nodes
                rewritten[i] = i;
                if (i == hypothesis) {
                    affected[i] = true;
                    rewritten[i] = ~0u;
                    lifted[i] = target;
                }
                else if (n.kind == certificate::rule::multiply && affected[n.left]) {
                    affected[i] = true;
                    rewritten[i] = rewritten[n.left] == ~0u ? ~0u : multiply(rewritten[n.left], n.coefficient, n.factor);
                    lifted[i] = lifted[n.left] == ~0u ? ~0u : multiply(lifted[n.left], n.coefficient, n.factor);
                }
                else if (n.kind == certificate::rule::add && (affected[n.left] || affected[n.right])) {
                    affected[i] = true;
                    rewritten[i] = sum(rewritten[n.left], rewritten[n.right]);
                    lifted[i] = sum(lifted[n.left], lifted[n.right]);
                }
            }
            return {rewritten[root] == ~0u ? zero() : rewritten[root],
                    lifted[root] == ~0u ? zero() : lifted[root]};
        }
        void join_branches(unsigned variable, ff_unique::poly const &boolean,
                           unsigned hypothesis0, unsigned root0, unsigned hypothesis1, unsigned root1) override {
            // 1=A0+B0*x and 1=A1+B1*(x-1). With the proved q=x*(x-1),
            // A0+B0*(x*A1+B1*q)=1. Compose B1*q and then B0*lifted directly
            // in the proof DAG, preserving sharing in both multipliers. All
            // emitted steps are existing PAC additions and monomial products.
            auto [a1, b1q] = discharge(root1, hypothesis1, boolean.derivation);
            unsigned lifted = add(multiply(a1, rational(1), {variable}), b1q);
            auto [a0, b0lifted] = discharge(root0, hypothesis0, lifted);
            proof.root = add(a0, b0lifted);
        }
        bool unique(std::vector<polynomial> &input, unsigned variables, bool branches) {
            std::vector<ff_unique::poly> equations, disequations;
            for (auto const &f : input) equations.push_back(to_unique(f));
            // Use the native tactic's propagation, with the same local stall
            // policy and shared cancellation/work allowance. The sink disables
            // digit and coincident-output zero-test inferences until they
            // carry checked evidence.
            ff_unique::unique_budget budget(e.limit, std::min(1000000u, (e.max_work - e.steps()) / 4),
                [&](uint64_t n) { for (uint64_t i = 0; i < n; ++i) e.tick(); });
            try {
                ff_unique::unique_solver solver(e.p, budget, equations, disequations, 64, this);
                ff_unique::unique_solver::state st;
                st.parent.resize(variables);
                st.members.resize(variables);
                st.val.resize(variables);
                st.has_val.assign(variables, false);
                st.is_bool.assign(variables, false);
                for (unsigned v = 0; v < variables; ++v) {
                    st.parent[v] = v;
                    st.members[v] = {v};
                }
                for (auto const &f : equations) {
                    unsigned v; rational c;
                    if (ff_unique::boolean_polynomial(f, e.p, v, c)) st.is_bool[v] = true;
                }
                budget.start_propagation();
                if (solver.propagate(st)) return true;
                budget.stop_propagation();
                std::vector<polynomial> residual;
                for (auto const &f : equations) residual.push_back(to_polynomial(solver.canon(st, f)));
                input = std::move(residual);
                if (branches && std::find(st.is_bool.begin(), st.is_bool.end(), true) != st.is_bool.end()) {
                    // Keep a bounded optional branch attempt from consuming the
                    // entire proof store. Failure restores the proved root-scope
                    // equations and DAG; all work/cancellation remains charged.
                    unsigned saved_nodes = proof.nodes.size(), saved_root = proof.root, saved_zero = zero_proof;
                    size_t saved_bytes = bytes;
                    auto restore = [&]() {
                        proof.nodes.resize(saved_nodes); proof.root = saved_root;
                        zero_proof = saved_zero; bytes = saved_bytes;
                    };
                    try {
                        flet<unsigned> bound(max_nodes, saved_nodes + std::min(10000u, (max_nodes-saved_nodes)/2));
                        budget.progress(); budget.start_propagation();
                        if (solver.split(st, 8)) return true;
                    }
                    catch (ff_unique::exhausted_budget const &) {}
                    catch (exhausted const &) {
                        if (e.steps() >= e.max_work || e.limit.is_canceled()) { restore(); throw; }
                    }
                    restore();
                }
            }
            catch (ff_unique::exhausted_budget const &) {
                // Local stall/exhaustion changes no input. Valid but unused proof
                // nodes are discarded when the final root is compacted. Global
                // proof/work exhaustion propagates instead of resetting budgets.
            }
            return false;
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
        lbool run_native(std::vector<polynomial> const &equations, std::vector<rational> &values,
                         certificate &out, bool native_unique, bool native_branches) {
            input_count = equations.size();
            auto input = equations;
            unsigned variables = 0;
            for (unsigned i = 0; i < input.size(); ++i) {
                input[i].derivation = record({certificate::rule::input, i, 0, rational(1), {}});
                for (auto const &[mon, c] : input[i]) for (unsigned v : mon) {
                    e.tick();
                    if (v >= 100000) throw exhausted();
                    variables = std::max(variables, v + 1);
                }
            }
            if (native_unique) {
                auto residual = input;
                if (unique(residual, variables, native_branches)) {
                    finish_native(out);
                    return l_false;
                }
                // Retain original definitions for candidate reconstruction. The
                // uniqueness pass can add consequences but is not a model trail.
                for (unsigned i = 0; i < residual.size(); ++i)
                    if (!residual[i].empty() && residual[i] != input[i])
                        input.push_back(std::move(residual[i]));
            }
            for (auto const &f : input) elimination_proofs.push_back(f.derivation);
            values.resize(std::max(values.size(), size_t(variables)));
            flet<polynomial_observer*> recording(e.m_proof, this);
            flet<elimination_observer*> substitutions(e.m_elimination_proof, this);
            auto result = e.solve(input, {}, values);
            if (result == l_false) finish_native(out);
            return result;
        }
        bool run_f4(std::vector<polynomial> const &equations, certificate &out, unsigned allowance) {
            if (e.steps() >= e.max_work) throw exhausted();
            unsigned variables = 0;
            for (auto const &eq : equations) for (auto const &[mon, c] : eq) for (unsigned v : mon) {
                e.tick();
                if (v >= 4096) return false;
                variables = std::max(variables, v + 1);
            }
            f4_config cfg;
            cfg.max_certificate_nodes = max_nodes;
            f4_stats stats;
            std::vector<rational> values(variables);
            std::set<unsigned> conflict;
            unsigned start = e.steps();
            auto charge = [&](unsigned n) {
                // The local F4 slice and scalar fallback share the same engine
                // allowance and cancellation source; exhaustion cannot reset either.
                for (unsigned i = 0; i < std::max(n, 1u); ++i) {
                    if (e.steps() - start >= allowance) throw exhausted();
                    e.tick();
                }
            };
            return f4_solve(e.p, equations, {}, variables, values, conflict, cfg, stats,
                            charge, nullptr, &out) == l_false;
        }
        bool run(std::vector<polynomial> const &equations, certificate &out, bool linear_first = false, bool native = false, bool native_unique = true, bool native_branches = true) {
            // Linear and sparse equations can eliminate variables before
            // nonlinear input rows create large intermediate polynomials.
            // This only changes search order: input nodes retain their original
            // equation indices, and the checker still replays every multiplier.
            if (native) {
                std::vector<rational> values;
                return run_native(equations, values, out, native_unique, native_branches) == l_false;
            }
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
    lbool solve_with_certificate(engine &arithmetic, std::vector<polynomial> const &equations,
                                 std::vector<rational> &values, certificate &output,
                                 unsigned max_nodes, bool native_unique, bool native_branches) {
        return certificate_builder(arithmetic, max_nodes).run_native(
            equations, values, output, native_unique, native_branches);
    }
    bool certify(engine &arithmetic, std::vector<polynomial> const &equations,
                 certificate &output, unsigned max_nodes, certificate_backend backend, bool native_unique, bool native_branches) {
        if (backend == certificate_backend::automatic) {
            bool scalar_exhausted = false;
            try {
                // Preserve successful scalar traces and their Boolean conflict
                // cores. A different F4 core can change downstream search even
                // when both polynomial derivations are valid.
                if (certify(arithmetic, equations, output, max_nodes, certificate_backend::scalar)) return true;
            }
            catch (exhausted const &) {
                scalar_exhausted = true;
                // Structural/DAG limits may leave work for a different search.
                // run_f4 keeps the SAME engine allowance and cancellation state.
            }
            bool found = certificate_builder(arithmetic, max_nodes).run_f4(equations, output, ~0u);
            if (!found && scalar_exhausted) throw exhausted();
            return found;
        }
        if (backend == certificate_backend::native)
            return certificate_builder(arithmetic, max_nodes).run(equations, output, true, true, native_unique, native_branches);
        if (backend == certificate_backend::f4)
            return certificate_builder(arithmetic, max_nodes).run_f4(equations, output, ~0u);
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
