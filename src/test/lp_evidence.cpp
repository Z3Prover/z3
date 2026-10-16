/*++
Copyright (c) 2026 Microsoft Corporation
--*/
#include "math/lp/evidence.h"
#include "math/lp/lar_solver.h"
#include "ast/reg_decl_plugins.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "solver/solver.h"
#include <sstream>

namespace {
    using manager = lp::evidence_manager;

    struct counted_dependencies {
        using value = unsigned;
        static constexpr bool ref_count = true;
        struct value_manager {
            void inc_ref(unsigned) {}
            void dec_ref(unsigned) {}
        };
        struct allocator {
            unsigned live = 0;
            void *allocate(size_t size) {
                ++live;
                return ::operator new(size);
            }
            void deallocate(size_t, void *p) {
                --live;
                ::operator delete(p);
            }
        };
    };

    void test_annotations() {
        counted_dependencies::value_manager values;
        counted_dependencies::allocator allocator;
        dependency_manager<counted_dependencies> m(values, allocator);
        unsigned payload = 7;
        auto *a = m.mk_leaf(0);
        auto *annotation = m.mk_annotation(a, &payload);
        VERIFY(m.get_annotation<unsigned>(annotation) == &payload);
        VERIFY(!m.get_annotation<int>(annotation));
        m.inc_ref(annotation);
        m.dec_ref(annotation);
        VERIFY(allocator.live == 0);
        annotation = m.mk_annotation(nullptr, &payload);
        m.inc_ref(annotation);
        m.dec_ref(annotation);
        VERIFY(allocator.live == 0);
    }

    manager::ref input(manager &m, unsigned ci) {
        auto *result = m.mk_leaf(ci);
        m.set_input_fact(result, manager::fact());
        return result;
    }

    manager::ref linear(manager &m, manager::ref a, lp::mpq const &ca, manager::ref b, lp::mpq const &cb) {
        return m.derive(m.mk_join(a, b), [&] {
            manager::recipe r;
            r.kind = manager::rule::linear;
            r.premises.push_back({a, ca});
            r.premises.push_back({b, cb});
            return r;
        });
    }

    lp::mpq coefficient(vector<std::pair<lp::constraint_index, lp::mpq>> const &cs, unsigned i) {
        for (auto const &[ci, c] : cs)
            if (ci == i)
                return c;
        return lp::mpq(0);
    }

    void test_erasure() {
        static_assert(sizeof(u_dependency) == sizeof(unsigned));
        static_assert(sizeof(manager::ref) == sizeof(void *));
        manager m;
        auto *a = m.mk_leaf(0);
        auto *b = m.mk_leaf(1);
        auto *ab = m.mk_join(a, b);
        bool captured = false;
        VERIFY(m.derive(ab, [&] {
            captured = true;
            return manager::recipe();
        }) == ab);
        VERIFY(!captured);
        VERIFY(!manager::get_recipe(ab));
        VERIFY(m.mk_join(a, a) == a);
        VERIFY(m.mk_join(a, nullptr) == a);
        vector<unsigned, false> support;
        m.linearize(ab, support);
        VERIFY(support.size() == 2);
        VERIFY(m.contains(ab, 0) && m.contains(ab, 1) && !m.contains(ab, 2));
        m.push_scope();
        m.mk_leaf(2);
        m.pop_scope(1);
        support.reset();
        m.linearize(ab, support);
        VERIFY(support.size() == 2);
    }

    void test_shared_weights() {
        manager m(true);
        auto *a = input(m, 0);
        auto *b = input(m, 1);
        auto *ab = linear(m, a, lp::mpq(2), b, lp::mpq(3));
        auto *root = linear(m, ab, lp::mpq(5), a, lp::mpq(7));
        vector<std::pair<lp::constraint_index, lp::mpq>> cs;
        VERIFY(m.linearize_coefficients(root, lp::mpq(1), cs));
        VERIFY(cs.size() == 2);
        VERIFY(coefficient(cs, 0) == lp::mpq(17));
        VERIFY(coefficient(cs, 1) == lp::mpq(15));
        vector<unsigned, false> support;
        m.linearize(root, support);
        VERIFY(support.size() == 2);
        manager::proof_expression p;
        m.reconstruct(root, p);
        VERIFY(p.complete && p.steps.size() == 4 && p.root == 3);
        VERIFY(p.steps[p.root].premises.size() == 2);

        auto *doubled = a;
        for (unsigned i = 0; i < 128; ++i)
            doubled = linear(m, doubled, lp::mpq(1), doubled, lp::mpq(1));
        cs.reset();
        VERIFY(m.linearize_coefficients(doubled, lp::mpq(1), cs));
        VERIFY(coefficient(cs, 0) == power(lp::mpq(2), 128));
        m.reconstruct(doubled, p);
        VERIFY(p.complete && p.steps.size() == 129);
    }

    void test_barriers() {
        manager m(true);
        auto *a = input(m, 0);
        auto *rounded = m.derive(a, [&] {
            manager::recipe r;
            r.kind = manager::rule::integer_tighten;
            r.conclusion.kind = lp::LE;
            r.conclusion.rhs = lp::impq(lp::mpq(1));
            r.premises.push_back({a, lp::mpq(1)});
            return r;
        });
        vector<std::pair<lp::constraint_index, lp::mpq>> cs;
        VERIFY(!m.linearize_coefficients(rounded, lp::mpq(1), cs));
        VERIFY(cs.empty());
        manager::proof_expression p;
        m.reconstruct(rounded, p);
        VERIFY(p.complete && p.steps[p.root].kind == manager::rule::integer_tighten);
        auto *bundle = m.mk_join(a, input(m, 1));
        VERIFY(!m.linearize_coefficients(bundle, lp::mpq(1), cs));
        m.reconstruct(bundle, p);
        VERIFY(!p.complete);
        auto *empty = m.derive(nullptr, [] { return manager::recipe(); });
        vector<unsigned, false> support;
        m.linearize(empty, support);
        VERIFY(support.empty());
        VERIFY(!m.contains(empty, 0));
        unsigned foreign = 0;
        auto *annotation = m.mk_annotation(a, &foreign);
        VERIFY(!manager::get_recipe(annotation));
        m.reconstruct(annotation, p);
        VERIFY(!p.complete && !p.check());
    }

    void test_discharge_lifetime() {
        manager::proof_expression p;
        {
            manager m(true);
            m.register_variable(0, false);
            auto *a = m.mk_leaf(0);
            manager::fact bound;
            bound.lhs.push_back({lp::mpq(1), 0});
            bound.kind = lp::GE;
            bound.rhs = lp::impq(lp::mpq(3));
            m.set_input_fact(a, bound);
            m.push_scope();
            auto *local = m.mk_leaf(1);
            manager::fact local_fact = bound;
            local_fact.kind = lp::LT;
            m.set_input_fact(local, std::move(local_fact));
            auto *body = m.derive(m.mk_join(a, local), [&] {
                manager::recipe r;
                r.kind = manager::rule::linear;
                r.conclusion.contradiction = true;
                r.premises.push_back({a, lp::mpq(1)});
                r.premises.push_back({local, lp::mpq(1)});
                return r;
            });
            m.pop_scope(1);
            auto *discharged = m.derive(a, [&] {
                manager::recipe r;
                r.kind = manager::rule::discharge;
                r.conclusion = bound;
                r.assumption = local;
                r.premises.push_back({body, lp::mpq(1)});
                return r;
            });
            auto *reused = m.mk_leaf(1);
            VERIFY(reused != local);
            manager::fact new_fact;
            new_fact.kind = lp::GE;
            new_fact.rhs = lp::impq(lp::mpq(7));
            m.set_input_fact(reused, std::move(new_fact));
            m.reconstruct(discharged, p);
            VERIFY(p.complete);
            VERIFY(p.check());
            auto const &root = p.steps[p.root];
            VERIFY(root.kind == manager::rule::discharge);
            VERIFY(p.steps[root.assumption].conclusion.kind == lp::LT);
            VERIFY(p.steps[root.assumption].conclusion.rhs.x == lp::mpq(3));
            vector<unsigned, false> support;
            m.linearize(discharged, support);
            VERIFY(support.size() == 1 && support[0] == 0);
        }
        VERIFY(p.steps[p.steps[p.root].assumption].conclusion.rhs.x == lp::mpq(3));
        VERIFY(p.check());
    }

    void test_variable_lifetime() {
        manager m(true);
        m.register_variable(0, true);
        m.push_scope();
        vector<std::pair<lp::mpq, lp::lpvar>> definition;
        definition.push_back({lp::mpq(2), 0});
        m.register_variable(1, true, definition);
        auto *old = m.mk_leaf(0);
        manager::fact f;
        f.lhs.push_back({lp::mpq(1), 1});
        m.set_input_fact(old, f);
        m.pop_scope(1);
        m.register_variable(1, false);
        auto *current = m.mk_leaf(0);
        m.set_input_fact(current, f);
        manager::proof_expression p, q;
        m.reconstruct(old, p);
        m.reconstruct(current, q);
        VERIFY(p.check() && q.check());
        VERIFY(p.steps[p.root].conclusion.lhs[0].second != q.steps[q.root].conclusion.lhs[0].second);
        VERIFY(p.variables[1].is_int && !p.variables[2].is_int);
        m.reset();
        m.register_variable(0, false);
        auto *fresh = input(m, 0);
        m.reconstruct(fresh, q);
        VERIFY(q.steps[q.root].id == 0 && q.variables.size() == 1);
        VERIFY(p.check());
    }

    void test_deep() {
        manager m(true);
        auto *root = input(m, 0);
        for (unsigned i = 0; i < 10000; ++i)
            root = m.derive(root, [root] {
                manager::recipe r;
                r.kind = manager::rule::linear;
                r.premises.push_back({root, lp::mpq(1)});
                return r;
            });
        manager::proof_expression p;
        m.reconstruct(root, p);
        VERIFY(p.complete);
        VERIFY(p.steps.size() == 10001);
    }

    void test_solver() {
        for (bool proofs : {false, true}) {
            lp::lar_solver s(proofs);
            auto x = s.add_var(0, false);
            auto lo = s.add_var_bound(x, lp::GE, lp::mpq(1));
            auto hi = s.add_var_bound(x, lp::LE, lp::mpq(0));
            s.activate(lo);
            s.activate(hi);
            s.find_feasible_solution();
            VERIFY(s.get_status() == lp::lp_status::INFEASIBLE);
            lp::explanation ex;
            s.get_infeasibility_explanation(ex);
            VERIFY(!ex.empty());
            if (proofs) {
                VERIFY(ex.evidence());
                manager::proof_expression p;
                s.dep_manager().reconstruct(ex.evidence(), p);
                VERIFY(p.complete && p.steps[p.root].conclusion.contradiction);
                VERIFY(p.check());
            }
            else
                VERIFY(!ex.evidence());
        }
    }

    void test_integer_calculus() {
        manager m(true);
        for (unsigned i = 0; i < 3; ++i)
            m.register_variable(i, true);
        auto *a = m.mk_leaf(0);
        auto *b = m.mk_leaf(1);
        manager::fact f;
        f.lhs.push_back({lp::mpq(1), 0});
        f.lhs.push_back({lp::mpq(2), 1});
        m.set_input_fact(a, f);
        f.lhs[1].second = 2;
        f.rhs = lp::impq(lp::mpq(1));
        m.set_input_fact(b, f);
        manager::fact difference;
        difference.lhs.push_back({lp::mpq(1), 2});
        difference.lhs.push_back({lp::mpq(-1), 1});
        difference.rhs = lp::impq(lp::mpq(1, 2));
        auto *eq = m.derive(m.mk_join(a, b), [&] {
            manager::recipe r;
            r.kind = manager::rule::linear;
            r.conclusion = difference;
            r.premises.push_back({a, lp::mpq(-1, 2)});
            r.premises.push_back({b, lp::mpq(1, 2)});
            return r;
        });
        auto inequality = [&](bool upper) {
            auto *bound = m.derive(eq, [&] {
                manager::recipe r;
                r.kind = manager::rule::linear;
                r.conclusion = difference;
                r.conclusion.kind = upper ? lp::LE : lp::GE;
                r.premises.push_back({eq, lp::mpq(upper ? 1 : -1)});
                return r;
            });
            return m.derive(bound, [&] {
                manager::recipe r;
                r.kind = manager::rule::integer_tighten;
                r.conclusion = difference;
                r.conclusion.kind = upper ? lp::LE : lp::GE;
                r.conclusion.rhs = lp::impq(lp::mpq(upper ? 0 : 1));
                r.premises.push_back({bound, lp::mpq(1)});
                return r;
            });
        };
        auto *lo = inequality(false);
        auto *hi = inequality(true);
        auto *root = m.derive(m.mk_join(lo, hi), [&] {
            manager::recipe r;
            r.kind = manager::rule::linear;
            r.conclusion.contradiction = true;
            r.premises.push_back({lo, lp::mpq(1)});
            r.premises.push_back({hi, lp::mpq(1)});
            return r;
        });
        manager::proof_expression p;
        m.reconstruct(root, p);
        VERIFY(p.check());
        vector<std::pair<lp::constraint_index, lp::mpq>> cs;
        VERIFY(!m.linearize_coefficients(root, lp::mpq(1), cs));
        p.steps[p.root].coefficients[0] = lp::mpq(2);
        VERIFY(!p.check());
        m.reconstruct(root, p);
        for (auto &s : p.steps)
            if (s.kind == manager::rule::integer_tighten && s.conclusion.kind == lp::LE)
                s.conclusion.rhs = lp::impq(lp::mpq(-1));
        VERIFY(!p.check());
        m.reconstruct(root, p);
        p.variables[1].is_int = false;
        VERIFY(!p.check());
    }

    void test_native_conflict(char const *assertions, char const *expected) {
        ast_manager m(PGM_ENABLED);
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        cmd.set_produce_proofs(true);
        std::istringstream input(assertions);
        VERIFY(parse_smt2_commands(cmd, input));
        params_ref params;
        params.set_uint("arith.solver", 6);
        ref<solver> s = mk_smt2_solver(m, params, symbol::null);
        s->push();
        for (auto *a : cmd.assertions())
            s->assert_expr(a);
        VERIFY(s->check_sat(0, nullptr) == l_false);
        auto *proof = s->get_proof();
        VERIFY(proof);
        ptr_vector<expr> todo;
        expr_mark visited;
        todo.push_back(proof);
        bool found = false;
        while (!todo.empty()) {
            auto *e = todo.back();
            todo.pop_back();
            if (visited.is_marked(e))
                continue;
            visited.mark(e);
            if (!is_app(e))
                continue;
            auto *app = to_app(e);
            auto *decl = app->get_decl();
            if (app->get_decl_kind() == PR_TH_LEMMA && decl->get_num_parameters() >= 2)
                found |= decl->get_parameter(1).get_symbol() == symbol(expected);
            for (auto *arg : *app)
                todo.push_back(arg);
        }
        VERIFY(found);
    }
}  // namespace

void tst_lp_evidence() {
    test_annotations();
    test_erasure();
    test_shared_weights();
    test_barriers();
    test_discharge_lifetime();
    test_variable_lifetime();
    test_deep();
    test_solver();
    test_integer_calculus();
    test_native_conflict("(declare-const x Int)(declare-const y Int)(declare-const z Int)"
                         "(assert (= (+ x (* 2 y)) 0))(assert (= (+ x (* 2 z)) 1))",
                         "unsupported");
    test_native_conflict("(declare-const x Real)(declare-const y Real)(declare-const z Real)"
                         "(assert (= x (* 2 y)))(assert (= y (* 3 z)))(assert (>= z 1))(assert (<= x 5))",
                         "farkas");
}
