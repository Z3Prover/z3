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

    The shared core optionally records ring identities for affine propagation
    and zero-test matching with distinct outputs. Digit and branch proofs remain
    unsupported; the ordinary tactic
    still declines proof-enabled goals until all closing paths carry evidence.

Author:

    Romain Soulat

--*/
#include "tactic/ff/ff_solve_tactic.h"
#include "tactic/tactical.h"
#include "ast/ff_decl_plugin.h"
#include "params/smt_params_helper.hpp"
#include "math/ff/ff_unique.h"
#include <iterator>
#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

namespace {

    using namespace ff_unique;

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
            obj_map<expr, unsigned> var_id;
            std::vector<expr *> vars;
            std::vector<poly> eqs, neqs;
            std::set<unsigned> bools;
            rational prime;
            unsigned const max_terms = 256;
            bool unsupported = false;

            obj_map<expr, poly> memo;
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
                    bool interpreted = ff.is_interp(e);
                    if (interpreted && !numeral) {
                        app *a = to_app(e);
                        if (!ff.is_add(e) && !ff.is_mul(e) && !ff.is_neg(e) && !ff.is_bitsum(e))
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
                        bool fresh = !var_id.contains(e);
                        unsigned &id = var_id.insert_if_not_there(e, static_cast<unsigned>(vars.size()));
                        if (fresh) vars.push_back(e);
                        r[monomial{id}] = rational(1);
                    }
                    else {
                        app *a = to_app(e);
                        bool mul = ff.is_mul(e);
                        if (mul) r[monomial()] = rational(1);
                        rational w(1);
                        for (expr *arg : *a) {
                            poly const &x = memo.find(arg);
                            if (mul) {
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
                                    slot = mod(slot + (ff.is_neg(e) ? -c : w * c), prime);
                                    if (slot.is_zero()) r.erase(mm);
                                    if (r.size() > max_terms) return false;
                                }
                                if (ff.is_bitsum(e)) w = mod(w * rational(2), prime);
                            }
                        }
                    }
                    memo.insert(e, std::move(r));
                    pending.pop_back();
                }
                budget.charge(memo.find(root).size());
                out = memo.find(root);
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
