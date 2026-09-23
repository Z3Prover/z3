#include "math/polynomial/ff_polynomial.h"
#include "util/debug.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ff_decl_plugin.h"
#include "model/model.h"
#include <algorithm>
#include <iostream>

namespace ff {
    struct test_engine {
        static void minimal_polynomial_provenance() {
            reslimit limit;
            engine builder(rational(5), limit, 1000000, 4096, false, false, false);
            auto x = builder.variable(0), y = builder.variable(1), z = builder.variable(2);
            auto first = builder.add(builder.mul(x, x), y, rational(-1));
            auto second = builder.add(builder.mul(y, y), builder.constant(rational(-1)));
            auto unrelated = builder.add(builder.mul(z, z), z, rational(-1));
            first.dependencies.insert(0);
            second.dependencies.insert(1);
            unrelated.dependencies.insert(2);
            // Pairwise relatively-prime leading powers x^2,y^2,z^2 give a
            // zero-dimensional basis. The x-coordinate has minimal polynomial
            // x^4-1, whose derivation needs the first two equations only.
            std::vector<polynomial> input{first, second, unrelated};
            engine extraction(rational(5), limit, 1000000, 4096, false, false, false);
            auto relation = extraction.minimal_polynomial(0, input);
            ENSURE(!relation.empty() && extraction.m_minpolys == 1);
            ENSURE(relation.dependencies == std::set<unsigned>({0, 1}));
            polynomial expected;
            builder.add_term(expected, {0, 0, 0, 0}, rational(1));
            builder.add_term(expected, {}, rational(-1));
            ENSURE(relation == expected);
            // Independently rebuild a scalar basis using just the reported
            // premises and reversed input order, then check ideal membership.
            engine reference(rational(5), limit, 1000000, 4096, false, false, false);
            std::vector<polynomial> selected{second, first};
            reference.basis(selected);
            ENSURE(reference.reduce(relation, selected).empty());
            // Integer enumeration checks the actual base-field projection and
            // proves both selected premises necessary. An unrelated Boolean
            // equation is retained while dropping each essential premise.
            bool missing_first = false, missing_second = false;
            for (unsigned a = 0; a < 5; ++a) {
                bool projected = false;
                for (unsigned b = 0; b < 5; ++b)
                    for (unsigned c = 0; c < 5; ++c) {
                        bool f = a*a % 5 == b;
                        bool g = b*b % 5 == 1;
                        bool h = c*c % 5 == c;
                        bool q = a*a*a*a % 5 == 1;
                        std::vector<rational> values{rational(a), rational(b), rational(c)};
                        ENSURE(reference.evaluate(relation, values).is_zero() == q);
                        ENSURE(!(f && g && h) || q);
                        missing_first |= g && h && !q;
                        missing_second |= f && h && !q;
                        projected |= f && g && h;
                    }
                ENSURE(projected == (a*a*a*a % 5 == 1));
            }
            ENSURE(missing_first && missing_second);
            std::cout << "Minimal polynomial: exact relation, scalar ideal membership and independently enumerated premise support\n";
        }
        static void minimal_polynomial_guard_budget() {
            reslimit construction;
            engine builder(rational(7), construction);
            auto mixed = builder.add(builder.mul(builder.variable(0), builder.variable(1)),
                                     builder.constant(rational(-1)));
            // This leading ideal is not zero-dimensional. Its guard used to
            // return before any arithmetic tick, ignoring even cancellation.
            reslimit local_limit;
            engine local(rational(7), local_limit, 0);
            bool exhausted = false;
            try { local.minimal_polynomial(0, {mixed}); }
            catch (ff::exhausted const &) { exhausted = true; }
            ENSURE(exhausted && local.steps() == 1 && !local_limit.is_canceled());
            reslimit canceled_limit;
            engine canceled(rational(7), canceled_limit, 100);
            canceled_limit.cancel();
            exhausted = false;
            try { canceled.minimal_polynomial(0, {mixed}); }
            catch (ff::exhausted const &) { exhausted = true; }
            ENSURE(exhausted && canceled_limit.is_canceled());
            std::cout << "Minimal-polynomial dimension guard honors local work and shared cancellation\n";
        }
        static void adaptive_matrix_storage() {
            reslimit limit;
            engine builder(rational(7), limit, 10000000, 4096, false, false, false);
            auto divisor = builder.add(builder.variable(0), builder.constant(rational(-1)));
            divisor.dependencies.insert(0);
            polynomial input, expected;
            input.dependencies.insert(1);
            for (unsigned v = 1; v <= 1100; ++v) {
                builder.add_term(input, {0, v}, rational(1));
                builder.add_term(expected, {v}, rational(1));
            }
            // The old cap must still reject the 1025th reducer. Opting in
            // admits 1100 short reducers with ample storage, for both matrix
            // representations; no pair selection or benchmark shape is involved.
            engine bounded(rational(7), limit, 10000000, 4096, false, true, false);
            bool exhausted = false;
            try { bounded.batch_reduce({input}, {divisor}); }
            catch (ff::exhausted const &) { exhausted = true; }
            ENSURE(exhausted && bounded.m_matrix_exhaustions == 1);
            ENSURE(bounded.m_extra_matrix_reducers == 0);
            for (bool compact : {false, true}) {
                engine extended(rational(7), limit, 10000000, 4096, false, true, false);
                extended.adaptive_matrix = true;
                extended.compact_matrix = compact;
                auto actual = extended.batch_reduce({input}, {divisor});
                ENSURE(actual.size() == 1 && actual.front() == expected);
                ENSURE(extended.m_extra_matrix_reducers == 76);
                ENSURE(actual.front().dependencies == std::set<unsigned>({0, 1}));
                // Independently check both generated ideals using scalar
                // reduction. The matrix row must remain equivalent to the
                // original row in the presence of the retained old basis.
                std::vector<polynomial> before{divisor, input}, after{divisor, actual.front()};
                builder.basis(before);
                builder.basis(after);
                ENSURE(builder.reduce(actual.front(), before).empty());
                ENSURE(builder.reduce(input, after).empty());
                // Neither reported premise can be omitted: x=0,y1=1 makes
                // the input row zero without its reducer; x=1,y1=1 satisfies
                // the reducer without the input row. The output is 1 in both.
                std::vector<rational> point(1101, rational(0));
                point[1] = rational(1);
                ENSURE(builder.evaluate(input, point).is_zero());
                ENSURE(!builder.evaluate(actual.front(), point).is_zero());
                point[0] = rational(1);
                ENSURE(builder.evaluate(divisor, point).is_zero());
                ENSURE(!builder.evaluate(actual.front(), point).is_zero());
            }
            // Many long monomials exceed storage even though the column and
            // polynomial-term limits permit them. This checks that the new
            // bound accounts for monomial copies, not just coefficient counts.
            polynomial wide;
            for (unsigned v = 1; v <= 1100; ++v) {
                monomial mon(513, v);
                mon[0] = 0;
                builder.add_term(wide, mon, rational(1));
            }
            engine storage(rational(7), limit, 10000000, 4096, false, true, false);
            storage.adaptive_matrix = true;
            exhausted = false;
            try { storage.batch_reduce({wide}, {divisor}); }
            catch (ff::exhausted const &) { exhausted = true; }
            ENSURE(exhausted && storage.m_matrix_exhaustions == 1);
            // A failed admission leaves no reusable partial matrix state.
            auto recovered = storage.batch_reduce({input}, {divisor});
            ENSURE(recovered.size() == 1 && recovered.front() == expected);
            std::cout << "Adaptive matrix admission: fixed cap, extra reducers, ideal/provenance and storage recovery checks\n";
        }
    };
}

// Compare independently scheduled bases as ideals, and check Buchberger's
// criterion explicitly. This catches incorrect pair deletion even when ordinary
// SAT tests would be answered by an unrelated fallback or lucky model probe.
static void test_ff_basis_optimizations() {
    unsigned seed = 729391, checked = 0;
    auto random = [&]() { seed = seed * 1664525u + 1013904223u; return seed; };
    for (char const *prime : {"7", "4294967291", "4294967311", "21888242871839275222246405745257275088548364400416034343698204186575808495617"}) {
        for (unsigned trial = 0; trial < 16; ++trial) {
            reslimit lim;
            ff::engine reference(rational(prime), lim, 10000000, 4096, false, false, false);
            std::vector<ff::polynomial> input;
            for (unsigned i = 0; i < 3; ++i) {
                ff::polynomial f;
                for (unsigned j = 0; j < 5; ++j) {
                    ff::monomial m;
                    unsigned degree = random() % 3;
                    for (unsigned k = 0; k < degree; ++k) m.push_back(random() % 3);
                    std::sort(m.begin(), m.end());
                    reference.add_term(f, m, rational(1 + random() % 19));
                }
                f.dependencies.insert(i);
                input.push_back(std::move(f));
            }
            auto expected = input;
            reference.basis(expected);
            for (unsigned mode = 0; mode < 8; ++mode) {
                ff::engine e(rational(prime), lim, 10000000, 4096, false, mode != 7, false);
                e.sugar_pairs = mode == 0 || mode >= 5;
                e.gm_pairs = mode == 1 || mode >= 5;
                e.div_masks = mode == 2 || mode >= 5;
                e.geobucket = mode == 3 || mode >= 5;
                e.small_coefficients = mode == 4 || mode >= 5;
                e.compact_matrix = mode == 6;
                e.adaptive_reduction = mode >= 5;
                auto actual = input;
                e.basis(actual);
                for (auto const &f : input) ENSURE(reference.reduce(f, actual).empty());
                for (auto const &f : actual) {
                    ENSURE(reference.reduce(f, expected).empty());
                    // Rebuild just the reported premises with the reference
                    // algorithm, so dependency tracking is checked independently.
                    std::vector<ff::polynomial> premises;
                    for (unsigned d : f.dependencies) { ENSURE(d < input.size()); premises.push_back(input[d]); }
                    reference.basis(premises);
                    ENSURE(reference.reduce(f, premises).empty());
                }
                for (unsigned i = 0; i < actual.size(); ++i)
                    for (unsigned j = 0; j < i; ++j) {
                        auto const &a = actual[i], &b = actual[j];
                        ENSURE(!a.empty() && !b.empty());
                        ff::monomial lcm, qa, qb;
                        auto const &ma = a.begin()->first, &mb = b.begin()->first;
                        std::set_union(ma.begin(), ma.end(), mb.begin(), mb.end(), std::back_inserter(lcm));
                        std::set_difference(lcm.begin(), lcm.end(), ma.begin(), ma.end(), std::back_inserter(qa));
                        std::set_difference(lcm.begin(), lcm.end(), mb.begin(), mb.end(), std::back_inserter(qb));
                        ff::polynomial pa, pb;
                        reference.add_term(pa, qa, reference.inverse(a.begin()->second));
                        reference.add_term(pb, qb, -reference.inverse(b.begin()->second));
                        ENSURE(reference.reduce(reference.add(reference.mul(pa, a), reference.mul(pb, b)), actual).empty());
                    }
                ++checked;
            }
        }
    }
    std::cout << checked << " basis equivalence, pair-completeness and provenance checks\n";
}

static void test_ff_scalar_recovery() {
    reslimit limit;
    ff::engine e(rational(7), limit, 2000000, 8, false, true, false);
    e.adaptive_reduction = true;
    e.geobucket = true;
    e.div_masks = true;
    std::vector<ff::polynomial> input;
    // Many independent two-equation blocks have tiny scalar remainders but
    // jointly exceed the 32-column matrix budget. IDs also collide in masks.
    for (unsigned i = 0; i < 24; ++i) {
        auto x = e.variable(3*i), y = e.variable(3*i+1), z = e.variable(3*i+2);
        input.push_back(e.add(e.mul(x, y), z));
        input.push_back(e.add(e.mul(x, z), e.constant(rational(1))));
    }
    auto actual = input;
    e.basis(actual);
    statistics st;
    e.collect_statistics(st);
    bool recovered = false;
    for (unsigned i = 0; i < st.size(); ++i)
        if (std::string(st.get_key(i)) == "ff scalar fallbacks") recovered = st.get_uint_value(i) > 0;
    ENSURE(recovered);
    ff::engine reference(rational(7), limit, 10000000, 4096, false, false, false);
    auto expected = input;
    reference.basis(expected);
    for (auto const &f : actual) ENSURE(reference.reduce(f, expected).empty());
    for (auto const &f : expected) ENSURE(reference.reduce(f, actual).empty());
    std::cout << "Matrix overflow recovered by exact scalar reduction; mask collisions checked\n";
}

void tst_finite_field() {
    ff::test_engine::minimal_polynomial_provenance();
    ff::test_engine::minimal_polynomial_guard_budget();
    ff::test_engine::adaptive_matrix_storage();
    test_ff_basis_optimizations();
    test_ff_scalar_recovery();
    {
        ast_manager m;
        reg_decl_plugins(m);
        ff_util ff(m);
        sort_ref s(ff.mk_sort(rational(3)), m);
        model_ref mdl = alloc(model, m);
        expr_ref one(ff.mk_numeral(rational(1), s), m);
        mdl->register_value(one);
        expr_ref a(mdl->get_fresh_value(s), m), b(mdl->get_fresh_value(s), m);
        ENSURE(ff.is_numeral(a) && ff.is_numeral(b));
        ENSURE(a != b && a != one && b != one);
        ENSURE(mdl->get_fresh_value(s) == nullptr);
    }
    for (unsigned prime : {2u, 3u, 5u, 7u, 11u, 17u}) {
        reslimit limit;
        // Exhaustively check quadratic roots and coupled systems, including
        // systems with roots only in extension fields.
        for (unsigned a = 0; a < prime; ++a) {
            ff::engine e(rational(prime), limit, 1000000);
            auto x = e.variable(0), y = e.variable(1);
            auto square = e.add(e.mul(x, x), e.constant(-rational(a)));
            auto sum = e.add(e.add(x, y), e.constant(rational(-1)));
            std::vector<rational> values(2, rational(0));
            bool exists = false;
            for (unsigned v = 0; v < prime; ++v)
                exists |= v * v % prime == a;
            lbool status = e.solve({square, sum}, {}, values);
            ENSURE(status == (exists ? l_true : l_false));
            if (exists) {
                ENSURE(e.evaluate(square, values).is_zero());
                ENSURE(e.evaluate(sum, values).is_zero());
            }
        }
    }
    // A learned theory clause is sound only if its selected input subset is
    // itself inconsistent. Check provenance independently by enumeration.
    for (unsigned prime : {2u, 3u, 5u})
        for (unsigned a = 0; a < prime; ++a)
            for (unsigned b = 0; b < prime; ++b)
                for (unsigned c = 0; c < prime; ++c) {
                    reslimit l;
                    ff::engine algebra(rational(prime), l, 1000000);
                    auto x = algebra.variable(0), y = algebra.variable(1);
                    auto product = algebra.add(algebra.mul(x, y), algebra.constant(-rational(a)));
                    auto sum = algebra.add(algebra.add(x, y), algebra.constant(-rational(b)));
                    auto neq = algebra.add(x, algebra.constant(-rational(c)));
                    product.dependencies.insert(0);
                    sum.dependencies.insert(1);
                    neq.dependencies.insert(2);
                    std::vector<rational> values(2, rational(0));
                    auto status = algebra.solve({product, sum}, {neq}, values);
                    if (status == l_false) {
                        auto const &core = algebra.conflict();
                        for (unsigned u = 0; u < prime; ++u)
                            for (unsigned v = 0; v < prime; ++v)
                                ENSURE(!((!core.contains(0) || u * v % prime == a) &&
                                         (!core.contains(1) || (u + v) % prime == b) && (!core.contains(2) || u != c)));
                    }
                }
    reslimit limit;
    ff::engine e(rational("21888242871839275222246405745257275088548364400416034343698204186575808495617"), limit);
    auto x = e.variable(0), y = e.variable(1);
    // Conflicting polynomial ideals, not just constant propagation.
    auto f = e.add(e.mul(x, y), e.constant(rational(-1)));
    auto g = e.add(e.mul(x, y), e.constant(rational(-2)));
    std::vector<rational> values(2, rational(0));
    ENSURE(e.solve({f, g}, {}, values) == l_false);
    // Algebra resource exhaustion is an explicit fallback request.
    ff::engine bounded(rational(7), limit, 0);
    bool exhausted = false;
    try {
        bounded.variable(0);
    } catch (ff::exhausted const &) {
        exhausted = true;
    }
    ENSURE(exhausted);
}
