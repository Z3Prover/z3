/*++
Copyright (c) 2026 Microsoft Corporation
--*/
#include "math/lp/evidence.h"
#include "math/lp/lar_solver.h"
#include "math/lp/int_solver.h"
#include "math/lp/gomory.h"
#include "math/lp/dioph_eq.h"
#include "math/lp/nla_core.h"
#include "math/lp/monomial_bounds.h"
#include "ast/reg_decl_plugins.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "solver/solver.h"
#include <sstream>
#include <tuple>

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

    void test_native_integer_witnesses() {
        for (unsigned category = 0; category < 7; ++category) {
            std::cout << "integer evidence category " << category << "\n";
            lp::lar_solver s(true);
            params_ref params;
            params.set_bool("lp.dio_run_gcd", false);
            params.set_uint("lp.dio_calls_period", 1);
            params.set_bool("arith.enable_hnf", false);
            s.updt_params(params);
            lp::int_solver integers(s);
            lp::explanation explanation;
            integers.set_expl(&explanation);
            auto x = s.add_var(0, true);
            auto y = s.add_var(1, category != 3 && category != 6);
            auto bound = [&](unsigned j, lp::lconstraint_kind kind, lp::mpq const &value) {
                s.activate(s.add_var_bound(j, kind, value));
            };
            if (category < 2) {
                auto z = s.add_var(2, true);
                vector<std::pair<lp::mpq, lp::lpvar>> a{{lp::mpq(1), x}, {lp::mpq(2), y}};
                vector<std::pair<lp::mpq, lp::lpvar>> b{{lp::mpq(1), x}, {lp::mpq(2), z}};
                auto first = s.add_term(a, UINT_MAX), second = s.add_term(b, UINT_MAX);
                bound(first, lp::LE, lp::mpq(0));
                bound(first, lp::GE, lp::mpq(0));
                bound(second, lp::LE, lp::mpq(1));
                bound(second, lp::GE, lp::mpq(1));
            }
            else {
                vector<std::pair<lp::mpq, lp::lpvar>> coefficients{{lp::mpq(2), x},
                                                                   {lp::mpq(category == 2   ? 2
                                                                            : category == 4 ? 3
                                                                                            : 1),
                                                                    y}};
                auto term = s.add_term(coefficients, UINT_MAX);
                bound(term, lp::GE, lp::mpq(1));
                if (category == 3 || category == 6) {
                    bound(y, lp::LE, lp::mpq(0));
                    bound(y, lp::GE, lp::mpq(0));
                    if (category == 6)
                        bound(term, lp::LE, lp::mpq(1));
                }
                if (category == 4) {
                    bound(x, lp::GE, lp::mpq(0));
                    bound(y, lp::GE, lp::mpq(0));
                    bound(y, lp::LE, lp::mpq(1));
                }
                if (category == 5) {
                    bound(term, lp::LE, lp::mpq(1));
                    coefficients[0].first = lp::mpq(1);
                    coefficients[1].first = lp::mpq(2);
                    auto second = s.add_term(coefficients, UINT_MAX);
                    bound(second, lp::GE, lp::mpq(1));
                    bound(second, lp::LE, lp::mpq(1));
                    coefficients[0].first = lp::mpq(4);
                    bound(s.add_term(coefficients, UINT_MAX), lp::GE, lp::mpq(2));
                }
            }
            s.find_feasible_solution();
            VERIFY(s.is_feasible());
            lp::lia_move result;
            if (category == 0)
                result = lp::int_gcd_test(integers)();
            else if (category == 1)
                result = integers.check(&explanation);
            else if (category == 2 || category == 5)
                result = lp::hnf_cutter(integers).make_hnf_cut();
            else
                result = lp::gomory(integers).get_gomory_cuts(1);
            VERIFY(result != lp::lia_move::undef);
            VERIFY(explanation.evidence());
            manager::proof_expression proof;
            s.dep_manager().reconstruct(explanation.evidence(), proof);
            VERIFY(proof.check());
            lp::explanation copied;
            copied.add_expl(explanation);
            VERIFY(copied.evidence() == explanation.evidence());
            copied.add_expl(lp::explanation());
            VERIFY(copied.evidence() == explanation.evidence());
            copied.add_expl(explanation);
            VERIFY(!copied.evidence());
            if (category < 2 || category == 6)
                VERIFY(proof.steps[proof.root].conclusion.contradiction);
            if (proof.steps[proof.root].conclusion.contradiction)
                proof.steps[proof.root].coefficients[0] = lp::mpq(0);
            else
                proof.steps[proof.root].conclusion.rhs.x += lp::mpq(1);
            VERIFY(!proof.check());
        }
    }

    void test_native_lattice_tightening() {
        lp::lar_solver s(true);
        lp::int_solver integers(s);
        lp::dioph_eq equations(integers);
        s.push();
        auto x = s.add_var(0, true), y = s.add_var(1, true);
        vector<std::pair<lp::mpq, lp::lpvar>> coefficients{{lp::mpq(1), x}, {lp::mpq(-1), y}};
        auto equal = s.add_term(coefficients, UINT_MAX);
        coefficients[1].first = lp::mpq(1);
        auto even = s.add_term(coefficients, UINT_MAX);
        for (auto [j, kind, value] :
             {std::tuple{equal, lp::LE, 0}, {equal, lp::GE, 0}, {even, lp::LE, 3}, {even, lp::GE, 1}})
            s.activate(s.add_var_bound(j, kind, lp::mpq(value)));
        s.find_feasible_solution();
        equations.check();
        bool found = false;
        for (auto *witness : {s.get_column_lower_bound_witness(even), s.get_column_upper_bound_witness(even)}) {
            auto *recipe = manager::get_recipe(witness);
            if (!recipe || recipe->kind != manager::rule::integer_lattice)
                continue;
            manager::proof_expression proof;
            s.dep_manager().reconstruct(witness, proof);
            VERIFY(proof.check());
            proof.steps[proof.root].divisor = lp::mpq(0);
            VERIFY(!proof.check());
            found = true;
        }
        VERIFY(found);
        s.pop();
    }

    void test_native_monomial_witnesses() {
        for (unsigned category = 0; category < 9; ++category) {
            std::cout << "nonlinear evidence category " << category << "\n";
            manager::proof_expression saved;
            {
                lp::lar_solver s(true);
                auto x = s.add_var(0, category == 8);
                auto y = s.add_var(1, category == 8);
                auto product = s.add_var(2, category == 8);
                params_ref params;
                reslimit limit;
                nla::core nonlinear(s, params, limit);
                nla::monomial_bounds bounds(&nonlinear);
                lp::lpvar factors[] = {x, category == 3 || category == 5 || category == 6 ? x : y};
                nonlinear.add_monic(product, 2, factors);
                auto bound = [&](unsigned j, lp::lconstraint_kind kind, int value) {
                    s.activate(s.add_var_bound(j, kind, lp::mpq(value)));
                };
                if (category == 0) {
                    bound(x, lp::GE, 0);
                    bound(x, lp::LE, 0);
                }
                else if (category == 1) {
                    bound(x, lp::GE, -2);
                    bound(x, lp::LE, -2);
                    bound(y, lp::GE, 1);
                }
                else if (category == 2) {
                    bound(x, lp::GE, 1);
                    bound(x, lp::LE, 2);
                    bound(y, lp::GE, 3);
                    bound(y, lp::LE, 4);
                }
                else if (category == 3) {
                    bound(x, lp::GE, -2);
                    bound(x, lp::LE, 3);
                }
                else if (category == 4 || category == 8) {
                    bound(product, lp::GE, category == 4 ? 4 : 1);
                    bound(product, lp::LE, category == 4 ? 8 : 3);
                    bound(y, lp::GE, 2);
                    bound(y, lp::LE, 4);
                }
                else if (category == 5) {
                    bound(product, lp::GE, 4);
                    bound(product, lp::LE, 9);
                    bound(x, lp::LE, 0);
                }
                else if (category == 7) {
                    bound(x, lp::GT, 0);
                    bound(y, lp::GT, 1);
                }
                s.find_feasible_solution();
                VERIFY(s.is_feasible());
                if (category < 2) {
                    VERIFY(bounds.propagate_linear_bounds());
                }
                else {
                    VERIFY(bounds.tighten_lp_bounds());
                }
                unsigned checked = 0;
                for (unsigned j = 0; j < s.A_r().column_count(); ++j)
                    for (bool lower : {false, true}) {
                        if (!(lower ? s.column_has_lower_bound(j) : s.column_has_upper_bound(j)))
                            continue;
                        auto *witness =
                            lower ? s.get_column_lower_bound_witness(j) : s.get_column_upper_bound_witness(j);
                        auto *recipe = manager::get_recipe(witness);
                        if (!recipe || recipe->kind == manager::rule::input)
                            continue;
                        s.dep_manager().reconstruct(witness, saved);
                        VERIFY(saved.check());
                        lp::explanation explanation, copied;
                        s.explain_evidence(witness, lp::mpq(1), explanation);
                        explanation.set_evidence(witness);
                        copied.add_expl(explanation);
                        VERIFY(copied.evidence() == witness);
                        ++checked;
                    }
                VERIFY(checked > 0);
                auto definition = saved.steps[saved.root].definition;
                saved.steps[saved.root].definition = UINT_MAX;
                if (saved.steps[saved.root].kind == manager::rule::monomial_substitute ||
                    saved.steps[saved.root].kind == manager::rule::monomial_interval)
                    VERIFY(!saved.check());
                saved.steps[saved.root].definition = definition;
            }
            VERIFY(saved.check());
        }
    }

    void test_affine_monomial_witness() {
        manager m(true);
        for (unsigned i = 0; i < 3; ++i)
            m.register_variable(i, false);
        vector<std::pair<lp::mpq, lp::lpvar>> term{{lp::mpq(2), 2}, {lp::mpq(3), 1}};
        m.register_variable(3, false, term);
        lp::lpvar factors[] = {0, 1};
        m.register_monomial(2, 2, factors);
        auto bound = [&](unsigned ci, unsigned column, lp::lconstraint_kind kind, lp::mpq const &value) {
            auto *input = m.mk_leaf(ci);
            manager::fact f;
            f.lhs.push_back({lp::mpq(1), column});
            f.kind = kind;
            f.rhs = lp::impq(value);
            m.set_input_fact(input, f);
            return input;
        };
        auto *lo = bound(0, 1, lp::GE, lp::mpq(1));
        auto *hi = bound(1, 1, lp::LE, lp::mpq(2));
        auto *source_lo = bound(2, 3, lp::GE, lp::mpq(8));
        auto *source_hi = bound(3, 3, lp::LE, lp::mpq(20));
        for (bool upper : {false, true}) {
            auto *root = m.derive(m.mk_join(m.mk_join(lo, hi), m.mk_join(source_lo, source_hi)), [&] {
                manager::recipe r;
                r.kind = manager::rule::monomial_interval;
                r.definition = 0;
                r.pivot = 0;
                r.source = 3;
                r.equation.lhs = {{lp::mpq(1), 3}, {lp::mpq(-2), 2}, {lp::mpq(-3), 1}};
                r.conclusion.lhs.push_back({lp::mpq(1), 0});
                r.conclusion.kind = upper ? lp::LE : lp::GE;
                r.conclusion.rhs = lp::impq(lp::mpq(upper ? 17 : 1, 2));
                r.premises = {{lo, lp::mpq(1)}, {hi, lp::mpq(1)}, {source_lo, lp::mpq(1)}, {source_hi, lp::mpq(1)}};
                r.bounds = {{1, 0, 1}, {3, 2, 3}};
                return r;
            });
            manager::proof_expression proof;
            m.reconstruct(root, proof);
            VERIFY(proof.check());
            proof.steps[proof.root].equation.lhs[1].first.neg();
            VERIFY(!proof.check());
        }
        auto *positive = bound(4, 0, lp::GT, lp::mpq(0));
        auto *zero = bound(5, 1, lp::EQ, lp::mpq(0));
        auto *root = m.derive(m.mk_join(positive, zero), [&] {
            manager::recipe r;
            r.kind = manager::rule::monomial_interval;
            r.definition = 0;
            r.pivot = 2;
            r.conclusion.lhs.push_back({lp::mpq(1), 2});
            r.conclusion.kind = lp::GE;
            r.premises = {{positive, lp::mpq(1)}, {zero, lp::mpq(1)}};
            r.bounds = {{0, 0, UINT_MAX}, {1, 1, 1}};
            return r;
        });
        manager::proof_expression proof;
        m.reconstruct(root, proof);
        VERIFY(proof.check());
        proof.steps[proof.root].conclusion.kind = lp::GT;
        VERIFY(!proof.check());
    }

    void test_native_optimized_bound_witnesses() {
        for (unsigned category = 0; category < 4; ++category) {
            bool integral = category >= 2, lower = category % 2 != 0;
            lp::lar_solver s(true);
            auto x = s.add_var(0, integral), y = s.add_var(1, false);
            vector<std::pair<lp::mpq, lp::lpvar>> coefficients{{lp::mpq(integral ? 1 : 2), x},
                                                               {integral ? lp::mpq(1, 2) : lp::mpq(1), y}};
            auto term = s.add_term(coefficients, UINT_MAX);
            for (auto [j, kind, value] :
                 {std::tuple{y, lp::GE, 1}, {y, lp::LE, integral ? 1 : 3}, {term, lp::GE, 2}, {term, lp::LE, 8}})
                s.activate(s.add_var_bound(j, kind, lp::mpq(value)));
            s.find_feasible_solution();
            VERIFY(s.is_feasible());
            params_ref params;
            reslimit limit;
            nla::core nonlinear(s, params, limit);
            nla::monomial_bounds bounds(&nonlinear);
            lp::mpq value;
            auto *witness = bounds.improve_bound(x, lower, value);
            VERIFY(witness);
            VERIFY(value == lp::mpq(integral ? (lower ? 3 : 15) : (lower ? -1 : 7), 2));
            manager::proof_expression proof;
            s.dep_manager().reconstruct(witness, proof);
            VERIFY(proof.check());
            s.update_column_type_and_bound(x, lower ? lp::GE : lp::LE, value, witness);
            witness = lower ? s.get_column_lower_bound_witness(x) : s.get_column_upper_bound_witness(x);
            s.dep_manager().reconstruct(witness, proof);
            VERIFY(proof.check());
            if (integral) {
                VERIFY(proof.steps[proof.root].kind == manager::rule::integer_tighten);
                VERIFY(proof.steps[proof.root].conclusion.rhs.x == lp::mpq(lower ? 2 : 7));
            }
            proof.steps[proof.root].conclusion.rhs.x += lp::mpq(lower ? 1 : -1);
            VERIFY(!proof.check());
        }
    }

    void test_native_nonlinear_conflict_witness() {
        lp::lar_solver s(true);
        auto x = s.add_var(0, false), square = s.add_var(1, false);
        params_ref params;
        reslimit limit;
        nla::core nonlinear(s, params, limit);
        nla::monomial_bounds bounds(&nonlinear);
        lp::lpvar factors[] = {x, x};
        nonlinear.add_monic(square, 2, factors);
        s.activate(s.add_var_bound(square, lp::LT, lp::mpq(0)));
        s.find_feasible_solution();
        VERIFY(s.is_feasible());
        VERIFY(bounds.tighten_lp_bounds());
        VERIFY(s.get_status() == lp::lp_status::INFEASIBLE);
        lp::explanation explanation;
        s.get_infeasibility_explanation(explanation);
        {
            nla::lemma_builder lemma(nonlinear, "nonlinear evidence conflict");
            lemma &= explanation;
        }
        VERIFY(nonlinear.lemmas().size() == 1);
        auto const &lemma = nonlinear.lemmas()[0];
        VERIFY(lemma.is_conflict());
        VERIFY(lemma.expl().evidence());
        manager::proof_expression proof;
        s.dep_manager().reconstruct(lemma.expl().evidence(), proof);
        VERIFY(proof.steps[proof.root].conclusion.contradiction);
        VERIFY(proof.check());
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
    test_native_integer_witnesses();
    test_native_lattice_tightening();
    test_native_monomial_witnesses();
    test_affine_monomial_witness();
    test_native_optimized_bound_witnesses();
    test_native_nonlinear_conflict_witness();
    test_native_conflict("(declare-const x Int)(declare-const y Int)(declare-const z Int)"
                         "(assert (= (+ x (* 2 y)) 0))(assert (= (+ x (* 2 z)) 1))",
                         "unsupported");
    test_native_conflict("(declare-const x Real)(declare-const y Real)(declare-const z Real)"
                         "(assert (= x (* 2 y)))(assert (= y (* 3 z)))(assert (>= z 1))(assert (<= x 5))",
                         "farkas");
}
