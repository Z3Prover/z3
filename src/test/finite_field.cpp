/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    finite_field.cpp

Abstract:

    Unit tests for prime-field polynomial algebra: Groebner-basis reduction,
    certificate reconstruction, the F4/tiny backends, and model evaluation.

Author:

    Romain Soulat

--*/
#include "smt/smt_context.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include <sstream>
#include "math/ff/ff_polynomial.h"
#include "math/ff/ff_certificate.h"
#include "math/ff/ff_f4.h"
#include "math/ff/ff_tiny.h"
#include "math/ff/ff_field.h"

#include "util/debug.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ff_decl_plugin.h"
#include "ast/simplifiers/ff_simplify.h"
#include "model/model.h"
#include <algorithm>
#include <iostream>

namespace ff {
    // Test-only helpers bridging the old set<unsigned>-based fixtures to the
    // pointer-based dependency representation: build/compare leaf sets
    // without requiring every test to hand-roll linearize/sort/compare.
    // Ids are encoded as void* leaf values (v_dependency_manager's key type).
    static void *dep_key(unsigned i) { return reinterpret_cast<void *>(static_cast<uintptr_t>(i)); }
    static unsigned dep_id(void *p) { return static_cast<unsigned>(reinterpret_cast<uintptr_t>(p)); }
    static v_dependency *dep_set(v_dependency_manager &dm, std::initializer_list<unsigned> ids) {
        v_dependency *d = nullptr;
        for (unsigned i : ids) d = dm.mk_join(d, dm.mk_leaf(dep_key(i)));
        return d;
    }
    static void dep_insert(v_dependency_manager &dm, v_dependency *&d, unsigned i) {
        d = dm.mk_join(d, dm.mk_leaf(dep_key(i)));
    }
    static std::set<unsigned> dep_linearize(v_dependency_manager &dm, v_dependency *d) {
        vector<void *, false> ptrs;
        dm.linearize(d, ptrs);
        std::set<unsigned> idxs;
        for (void *p : ptrs) idxs.insert(dep_id(p));
        return idxs;
    }
    static bool dep_eq(v_dependency_manager &dm, v_dependency *a, v_dependency *b) {
        return dep_linearize(dm, a) == dep_linearize(dm, b);
    }
    static bool dep_contains(v_dependency_manager &dm, v_dependency *d, unsigned i) {
        return dm.contains(d, dep_key(i));
    }

    struct test_engine {
        static void adaptive_basis_storage() {
            for (rational const &prime : {rational(7), rational("21888242871839275222246405745257275088548364400416034343698204186575808495617")}) {
                reslimit limit;
                v_dependency_manager deps;
                engine builder(deps, prime, limit, 10000000);
                std::vector<polynomial> input;
                for (unsigned i = 0; i < 300; ++i) {
                    auto f = builder.variable(i); dep_insert(deps, f.dependencies, i); input.push_back(f);
                }
                engine bounded(deps, prime, limit, 10000000);
                auto original = input;
                bool failed = false;
                try { bounded.basis(original); } catch (exhausted const &) { failed = true; }
                ENSURE(failed && bounded.m_active_basis_exhaustions == 1 && original == input);
                for (bool gm : {false, true}) {
                    engine extended(deps, prime, limit, 10000000);
                    extended.adaptive_basis = true; extended.gm_pairs = gm;
                    auto actual = input; extended.basis(actual);
                    // Independent monic variables already form a Groebner basis:
                    // every pair is coprime and the exact ideal is unchanged.
                    ENSURE(actual == input && extended.m_peak_active_basis == 300);
                    ENSURE(extended.m_peak_basis_bytes > 0 && extended.m_basis_exhaustions == 0);
                    for (unsigned i = 0; i < actual.size(); ++i) ENSURE(dep_eq(deps, actual[i].dependencies, input[i].dependencies));
                }
                for (bool pairs : {false, true}) {
                    engine guarded(deps, prime, limit, 1000000);
                    guarded.adaptive_basis = true;
                    if (pairs) guarded.m_pair_storage_limit = 256;
                    else guarded.set_basis_storage_limit(256);
                    std::vector<polynomial> tiny{input[0], input[1], input[2]};
                    auto before = tiny; failed = false;
                    try { guarded.basis(tiny); } catch (exhausted const &) { failed = true; }
                    ENSURE(failed && tiny == before);
                    ENSURE(pairs ? guarded.m_pair_storage_exhaustions == 1 : guarded.m_basis_storage_exhaustions == 1);
                    guarded.set_basis_storage_limit(16 * 1024 * 1024);
                    guarded.m_pair_storage_limit = 16 * 1024 * 1024;
                    guarded.basis(tiny); ENSURE(tiny == before);
                }
                std::vector<polynomial> retirement;
                for (unsigned i = 0; i < 80; ++i) {
                    auto x = builder.variable(i);
                    auto f = builder.add(builder.mul(x, x), x, rational(-1));
                    dep_insert(deps, f.dependencies, i); retirement.push_back(f);
                }
                for (unsigned i = 0; i < 80; ++i) {
                    auto x = builder.variable(i); dep_insert(deps, x.dependencies, 80+i); retirement.push_back(x);
                }
                engine old(deps, prime, limit, 10000000), compact(deps, prime, limit, 10000000);
                compact.adaptive_basis = true;
                auto expected = retirement, actual = retirement;
                old.basis(expected); compact.basis(actual);
                ENSURE(actual == expected);
                ENSURE(compact.m_pair_compactions == (prime.is_unsigned() ? 1u : 0u));
                ENSURE(prime.is_unsigned() ? compact.m_discarded_pairs > 0 : compact.m_discarded_pairs == 0);
                for (unsigned i = 0; i < actual.size(); ++i) ENSURE(dep_eq(deps, actual[i].dependencies, expected[i].dependencies));
                std::cout << "Adaptive basis: 300 rows, independent storage guards/reuse, exact stale-pair compaction\n";
            }
        }
        static void sparse_matrix_selection() {
            reslimit limit;
            v_dependency_manager deps;
            engine reference(deps, rational(7), limit, 10000000, 4096, false, false, false);
            auto x = reference.variable(10), z = reference.variable(20);
            auto dense = reference.add(reference.add(reference.add(x, reference.variable(5)),
                                                     reference.variable(4)), reference.variable(3));
            auto sparse = reference.add(x, reference.variable(0));
            auto tied = reference.add(x, reference.variable(1));
            auto input = reference.mul(x, z);
            dense.dependencies = dep_set(deps, {0}); sparse.dependencies = dep_set(deps, {1});
            input.dependencies = dep_set(deps, {2}); tied.dependencies = dep_set(deps, {3});
            sparse.sugar = 7;
            std::vector<polynomial> bs{dense, sparse, tied};
            // Matrix outputs are made monic after elimination.
            auto expected = reference.mul(reference.variable(0), z);
            for (bool packed : {false, true}) for (bool lazy : {false, true}) {
                engine old(deps, rational(7), limit, 1000000), chosen(deps, rational(7), limit, 1000000);
                old.compact_matrix = chosen.compact_matrix = packed;
                old.lazy_matrix = chosen.lazy_matrix = lazy;
                chosen.sparse_matrix_reducers = true;
                auto before = old.batch_reduce({input}, bs), after = chosen.batch_reduce({input}, bs);
                ENSURE(before.size() == 1 && before.front().size() == 3);
                ENSURE(after.size() == 1 && after.front() == expected);
                ENSURE(dep_linearize(deps, after.front().dependencies) == std::set<unsigned>({1, 2}));
                ENSURE(after.front().sugar == 8 && chosen.m_sparse_matrix_reducers == 1);
                ENSURE(chosen.m_peak_matrix_columns == 2 && old.m_peak_matrix_columns == 4);
                // Choice may change the remainder, but it must preserve the
                // ideal with the retained basis in both directions. Check this
                // using the separate scalar basis/reduction route.
                auto original = bs, transformed = bs;
                original.push_back(input); transformed.push_back(after.front());
                reference.basis(original); reference.basis(transformed);
                ENSURE(reference.reduce(after.front(), original).empty());
                ENSURE(reference.reduce(input, transformed).empty());
                auto premises = std::vector<polynomial>{sparse, input};
                reference.basis(premises);
                ENSURE(reference.reduce(after.front(), premises).empty());
            }
            std::cout << "Sparse matrix selection: smaller closure, stable ties, exact ideals, chosen premises and sugar\n";
        }
        static void fused_reduction_equivalence() {
            for (rational const &prime : {rational(7), rational("4294967291"), rational("18446744073709551629")})
                for (bool small : {false, true}) {
                    reslimit limit;
                    v_dependency_manager deps;
                    engine builder(deps, prime, limit, 10000000);
                    auto x = builder.variable(2), y = builder.variable(1), z = builder.variable(0);
                    std::vector<polynomial> bs{
                        builder.add(builder.scale(builder.mul(x, x), rational(3)), y),
                        builder.add(builder.scale(builder.mul(y, y), rational(2)), z),
                        builder.add(builder.mul(z, z), builder.constant(rational(-1)))};
                    for (unsigned i = 0; i < bs.size(); ++i) { dep_insert(deps, bs[i].dependencies, i); bs[i].sugar += 5; }
                    for (unsigned degree = 2; degree < 12; ++degree) {
                        polynomial f;
                        builder.add_term(f, monomial(degree, 2), prime - rational(1));
                        builder.add_term(f, monomial(degree - 1, 1), prime - rational(2));
                        builder.add_term(f, {0, 1, 2}, rational(3));
                        dep_insert(deps, f.dependencies, 3);
                        engine eager(deps, prime, limit, 10000000), fused(deps, prime, limit, 10000000);
                        eager.small_coefficients = fused.small_coefficients = small;
                        fused.fused_reduction = true;
                        auto expected = eager.reduce(f, bs), actual = fused.reduce(f, bs);
                        ENSURE(actual == expected && dep_eq(deps, actual.dependencies, expected.dependencies));
                        ENSURE(actual.sugar == expected.sugar && fused.m_fused_reductions > 0);
                        ENSURE(fused.steps() < eager.steps());
                    }
                }
            std::cout << "Fused scalar reduction: exact remainders, premises and sugar across three field sizes\n";
        }
        static void work_accounting() {
            reslimit limit;
            v_dependency_manager deps;
            engine e(deps, rational(7), limit, 3);
            e.tick();
            bool failed = false;
            try {
                engine::scoped_work outer(e, engine::pair_work);
                e.tick();
                engine::scoped_work inner(e, engine::scalar_work);
                e.tick();
                e.tick();
            }
            catch (exhausted const &) { failed = true; }
            ENSURE(failed && e.work == 4 && e.m_work_phase == engine::other_work);
            ENSURE(e.m_phase_work[engine::other_work] == 1);
            ENSURE(e.m_phase_work[engine::pair_work] == 1);
            ENSURE(e.m_phase_work[engine::scalar_work] == 2);
            e.max_work = 10;
            e.tick();
            statistics st;
            e.collect_statistics(st);
            unsigned total = 0;
            for (unsigned i = 0; i < st.size(); ++i)
                if (std::string(st.get_key(i)).starts_with("ff work ")) total += st.get_uint_value(i);
            ENSURE(total == e.steps() && total == 5);
            std::cout << "Exclusive work accounting preserves nested scopes, failing ticks and subsequent reuse\n";
        }
        static void minimal_polynomial_provenance() {
            reslimit limit;
            v_dependency_manager deps;
            engine builder(deps, rational(5), limit, 1000000, 4096, false, false, false);
            auto x = builder.variable(0), y = builder.variable(1), z = builder.variable(2);
            auto first = builder.add(builder.mul(x, x), y, rational(-1));
            auto second = builder.add(builder.mul(y, y), builder.constant(rational(-1)));
            auto unrelated = builder.add(builder.mul(z, z), z, rational(-1));
            dep_insert(deps, first.dependencies, 0);
            dep_insert(deps, second.dependencies, 1);
            dep_insert(deps, unrelated.dependencies, 2);
            // Pairwise relatively-prime leading powers x^2,y^2,z^2 give a
            // zero-dimensional basis. The x-coordinate has minimal polynomial
            // x^4-1, whose derivation needs the first two equations only.
            std::vector<polynomial> input{first, second, unrelated};
            engine extraction(deps, rational(5), limit, 1000000, 4096, false, false, false);
            auto relation = extraction.minimal_polynomial(0, input);
            ENSURE(!relation.empty() && extraction.m_minpolys == 1);
            ENSURE(dep_linearize(deps, relation.dependencies) == std::set<unsigned>({0, 1}));
            polynomial expected;
            builder.add_term(expected, {0, 0, 0, 0}, rational(1));
            builder.add_term(expected, {}, rational(-1));
            ENSURE(relation == expected);
            // Independently rebuild a scalar basis using just the reported
            // premises and reversed input order, then check ideal membership.
            engine reference(deps, rational(5), limit, 1000000, 4096, false, false, false);
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
            v_dependency_manager deps;
            engine builder(deps, rational(7), construction);
            auto mixed = builder.add(builder.mul(builder.variable(0), builder.variable(1)),
                                     builder.constant(rational(-1)));
            // This leading ideal is not zero-dimensional. Its guard used to
            // return before any arithmetic tick, ignoring even cancellation.
            reslimit local_limit;
            engine local(deps, rational(7), local_limit, 0);
            bool exhausted = false;
            try { local.minimal_polynomial(0, {mixed}); }
            catch (ff::exhausted const &) { exhausted = true; }
            ENSURE(exhausted && local.steps() == 1 && !local_limit.is_canceled());
            ENSURE(local.m_local_work_exhaustions == 1 && local.m_shared_limit_exhaustions == 0);
            reslimit canceled_limit;
            engine canceled(deps, rational(7), canceled_limit, 100);
            canceled_limit.cancel();
            exhausted = false;
            try { canceled.minimal_polynomial(0, {mixed}); }
            catch (ff::exhausted const &) { exhausted = true; }
            ENSURE(exhausted && canceled_limit.is_canceled());
            ENSURE(canceled.m_shared_limit_exhaustions == 1 && canceled.m_local_work_exhaustions == 0);
            std::cout << "Minimal-polynomial dimension guard honors local work and shared cancellation\n";
        }
        static void lazy_matrix_equivalence() {
            reslimit limit;
            v_dependency_manager deps;
            engine builder(deps, rational(7), limit, 10000000);
            polynomial divisor, input;
            for (unsigned v = 0; v < 20; ++v) builder.add_term(divisor, {v}, rational(1));
            divisor.dependencies = dep_set(deps, {1, 3});
            input.dependencies = dep_set(deps, {2});
            for (unsigned v = 100; v < 150; ++v) builder.add_term(input, {19, v}, rational(1));
            for (bool packed : {false, true}) {
                engine eager(deps, rational(7), limit, 10000000);
                eager.adaptive_matrix = true;
                eager.compact_matrix = packed;
                auto expected = eager.batch_reduce({input}, {divisor});
                engine lazy(deps, rational(7), limit, 10000000);
                lazy.adaptive_matrix = lazy.lazy_matrix = true;
                lazy.compact_matrix = packed;
                auto actual = lazy.batch_reduce({input}, {divisor});
                ENSURE(actual == expected && actual.size() == 1);
                ENSURE(dep_linearize(deps, actual.front().dependencies) == std::set<unsigned>({1, 2, 3}));
                ENSURE(actual.front().sugar == expected.front().sugar);
                ENSURE(lazy.m_peak_matrix_symbolic_bytes < eager.m_peak_matrix_symbolic_bytes);
                ENSURE(lazy.m_peak_matrix_reducers == eager.m_peak_matrix_reducers);
                ENSURE(lazy.m_peak_matrix_columns == eager.m_peak_matrix_columns);
                auto ideal = std::vector<polynomial>{input, divisor};
                builder.basis(ideal);
                ENSURE(builder.reduce(actual.front(), ideal).empty());
                // A descriptor never survives the call: the next batch must
                // use its own basis without stale references.
                auto again = lazy.batch_reduce({divisor}, {});
                ENSURE(again.size() == 1 && again.front() == divisor);
            }
            std::cout << "Lazy matrix reducers: exact rows, sugar, premises and lower symbolic storage\n";
        }
        static void matrix_limit_diagnostics() {
            reslimit limit;
            v_dependency_manager deps;
            engine builder(deps, rational(7), limit, 1000000);
            auto x = builder.variable(4), y = builder.variable(3), z = builder.variable(2);
            auto a = builder.variable(1), b = builder.variable(0);
            // Five symbolic columns exceed 4*max_terms before elimination.
            auto wide = builder.add(builder.add(builder.add(builder.add(x, y), z), a), b);
            engine columns(deps, rational(7), limit, 1000000, 1);
            bool exhausted = false;
            try { columns.batch_reduce({wide}, {}); }
            catch (ff::exhausted const &) { exhausted = true; }
            ENSURE(exhausted && columns.m_matrix_column_exhaustions == 1);
            ENSURE(columns.m_peak_matrix_columns == 5 && columns.m_matrix_exhaustions == 1);
            for (bool compact : {false, true}) {
                // Each input has three terms, but subtracting the first pivot
                // from the second row produces four nonzero terms.
                auto first = builder.add(builder.add(x, y), z);
                auto second = builder.add(builder.add(x, a), b);
                engine growth(deps, rational(7), limit, 1000000, 3);
                growth.compact_matrix = compact;
                exhausted = false;
                try { growth.batch_reduce({first, second}, {}); }
                catch (ff::exhausted const &) { exhausted = true; }
                ENSURE(exhausted && growth.m_matrix_row_exhaustions == 1);
                ENSURE(growth.m_peak_matrix_row_terms == 4 && growth.m_matrix_exhaustions == 1);
                // A short row carrying a widely-supported dependency used to
                // exhaust retained pivot storage through provenance alone.
                auto supported = x;
                for (unsigned i = 0; i < 200; ++i) dep_insert(deps, supported.dependencies, i);
                engine provenance(deps, rational(7), limit, 1000000, 2);
                provenance.compact_matrix = compact;
                // A dependency join is now a single O(1) node charged a fixed
                // 48 bytes, regardless of how many leaves were folded into it
                // (unlike the old set<unsigned>, whose storage scaled with
                // provenance breadth): a single short row carrying a 200-leaf
                // dependency no longer exhausts retained storage by itself.
                auto reduced = provenance.batch_reduce({supported}, {});
                ENSURE(reduced.size() == 1 && dep_linearize(deps, reduced.front().dependencies).size() == 200);
                ENSURE(provenance.m_peak_matrix_dependency_bytes == 48);
                ENSURE(provenance.m_matrix_exhaustions == 0 && provenance.m_matrix_pivot_exhaustions == 0);
            }
            std::cout << "Matrix guard diagnostics: columns, row growth and provenance-dominated storage in both representations\n";
        }
        static void adaptive_matrix_storage() {
            reslimit limit;
            v_dependency_manager deps;
            engine builder(deps, rational(7), limit, 10000000, 4096, false, false, false);
            auto divisor = builder.add(builder.variable(0), builder.constant(rational(-1)));
            dep_insert(deps, divisor.dependencies, 0);
            polynomial input, expected;
            dep_insert(deps, input.dependencies, 1);
            for (unsigned v = 1; v <= 1100; ++v) {
                builder.add_term(input, {0, v}, rational(1));
                builder.add_term(expected, {v}, rational(1));
            }
            // The old cap must still reject the 1025th reducer. Opting in
            // admits 1100 short reducers with ample storage, for both matrix
            // representations; no pair selection or benchmark shape is involved.
            engine bounded(deps, rational(7), limit, 10000000, 4096, false, true, false);
            bool exhausted = false;
            try { bounded.batch_reduce({input}, {divisor}); }
            catch (ff::exhausted const &) { exhausted = true; }
            ENSURE(exhausted && bounded.m_matrix_exhaustions == 1);
            ENSURE(bounded.m_extra_matrix_reducers == 0);
            ENSURE(bounded.m_matrix_reducer_exhaustions == 1 && bounded.m_peak_matrix_reducers == 1025);
            for (bool compact : {false, true}) for (bool lazy : {false, true}) {
                engine extended(deps, rational(7), limit, 10000000, 4096, false, true, false);
                extended.adaptive_matrix = true;
                extended.compact_matrix = compact;
                extended.lazy_matrix = lazy;
                auto actual = extended.batch_reduce({input}, {divisor});
                ENSURE(actual.size() == 1 && actual.front() == expected);
                ENSURE(extended.m_extra_matrix_reducers == 76);
                ENSURE(dep_linearize(deps, actual.front().dependencies) == std::set<unsigned>({0, 1}));
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
            engine storage(deps, rational(7), limit, 10000000, 4096, false, true, false);
            storage.adaptive_matrix = true;
            exhausted = false;
            try { storage.batch_reduce({wide}, {divisor}); }
            catch (ff::exhausted const &) { exhausted = true; }
            ENSURE(exhausted && storage.m_matrix_exhaustions == 1);
            ENSURE(storage.m_matrix_symbolic_exhaustions == 1);
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
                v_dependency_manager deps;
                ff::engine reference(deps, rational(prime), lim, 10000000, 4096, false, false, false);
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
                    ff::dep_insert(deps, f.dependencies, i);
                    input.push_back(std::move(f));
                }
                auto expected = input;
                reference.basis(expected);
                for (unsigned mode = 0; mode < 18; ++mode) {
                    ff::engine e(deps, rational(prime), lim, 10000000, 4096, false, mode != 7, false);
                    e.sugar_pairs = mode == 0 || mode >= 5;
                    e.gm_pairs = mode == 1 || (mode >= 5 && mode != 16);
                    e.div_masks = mode == 2 || mode >= 5;
                    e.geobucket = mode == 3 || mode >= 5;
                    e.small_coefficients = mode == 4 || mode >= 5;
                    e.compact_matrix = mode == 6 || mode == 9 || mode == 11 || mode == 13 || mode == 15;
                    e.lazy_matrix = mode == 8 || mode == 9 || mode >= 14;
                    e.sparse_matrix_reducers = mode >= 12 && mode < 16;
                    e.adaptive_basis = mode >= 16;
                    e.fused_reduction = mode == 10 || mode == 11;
                    e.adaptive_matrix = mode >= 8;
                    e.adaptive_reduction = mode >= 5;
                    auto actual = input;
                    e.basis(actual);
                    for (auto const &f : input) ENSURE(reference.reduce(f, actual).empty());
                    for (auto const &f : actual) {
                        ENSURE(reference.reduce(f, expected).empty());
                        // Rebuild just the reported premises with the reference
                        // algorithm, so dependency tracking is checked independently.
                        std::vector<ff::polynomial> premises;
                        for (unsigned d : ff::dep_linearize(deps, f.dependencies)) { ENSURE(d < input.size()); premises.push_back(input[d]); }
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
    v_dependency_manager deps;
    ff::engine e(deps, rational(7), limit, 2000000, 8, false, true, false);
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
    ff::engine reference(deps, rational(7), limit, 10000000, 4096, false, false, false);
    auto expected = input;
    reference.basis(expected);
    for (auto const &f : actual) ENSURE(reference.reduce(f, expected).empty());
    for (auto const &f : expected) ENSURE(reference.reduce(f, actual).empty());
    std::cout << "Matrix overflow recovered by exact scalar reduction; mask collisions checked\n";
}

static void test_certificates() {
    for (rational const &prime : {rational(2), rational(7), rational("21888242871839275222246405745257275088548364400416034343698204186575808495617")}) {
        reslimit limit;
        v_dependency_manager deps;
        ff::engine e(deps, prime, limit, 1000000);
        auto x = e.variable(0), y = e.variable(1), one = e.constant(rational(1));
        std::vector<ff::polynomial> equations{e.add(e.mul(x, y), one, rational(-1)),
            e.add(e.mul(x, e.add(y, one)), one, rational(-1))};
        auto original = equations;
        ff::certificate proof;
        ENSURE(ff::certify(e, equations, proof));
        ENSURE(equations == original && !proof.nodes.empty());
        auto size = proof.nodes.size();
        unsigned root = proof.root;
        // Failure must leave the caller's previous successful object intact.
        bool exhausted = false;
        try { ff::certify(e, equations, proof, 0); } catch (ff::exhausted const &) { exhausted = true; }
        ENSURE(exhausted && proof.nodes.size() == size && proof.root == root);
        ENSURE(!ff::certify(e, {x}, proof));
        ENSURE(proof.nodes.size() == size && proof.root == root);
        limit.inc_cancel(); exhausted = false;
        try { ff::certify(e, equations, proof); } catch (ff::exhausted const &) { exhausted = true; }
        limit.dec_cancel();
        ENSURE(exhausted && proof.nodes.size() == size && proof.root == root);
        ENSURE(ff::certify(e, equations, proof));
    }
    // More independent rows than the retained basis cap, followed by a
    // contradiction: fallback can change order without changing input IDs.
    reslimit limit;
    v_dependency_manager deps;
    ff::engine maker(deps, rational(7), limit, 1000000);
    std::vector<ff::polynomial> equations;
    for (unsigned i = 0; i < 257; ++i) equations.push_back(maker.variable(i));
    equations.push_back(maker.constant(rational(1)));
    ff::certificate proof;
    ENSURE(ff::certify(maker, equations, proof));
    ENSURE(proof.nodes.size() == 1 && proof.root == 0);
    ENSURE(proof.nodes[0].kind == ff::certificate::rule::input && proof.nodes[0].left == 257);
    // With a fresh budget the fallback could prove this immediately. It must
    // instead retain work spent by the failed original-order attempt.
    ff::engine bounded(deps, rational(7), limit, 1000);
    bool exhausted = false;
    try { ff::certify(bounded, equations, proof); } catch (ff::exhausted const &) { exhausted = true; }
    ENSURE(exhausted && bounded.steps() >= 1000 && bounded.steps() <= 1002);
    ENSURE(proof.nodes.size() == 1 && proof.nodes[0].left == 257);
    std::cout << "Certificate reconstruction: output atomicity, input preservation, budget/cancellation recovery over three fields\n";
}


#if Z3_FF_HAS_UINT128
template <class F>
static void check_field_arithmetic(rational const &p, unsigned rounds) {
    F f(p);
    uint64_t state = 88172645463325252ull;
    auto next = [&]() {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        return state;
    };
    auto sample = [&]() {
        rational r(0);
        for (unsigned i = 0; i < 5; ++i)
            r = r * rational::power_of_two(64) + rational(next(), rational::ui64());
        // Include boundary values.
        switch (next() % 8) {
        case 0: return rational(0);
        case 1: return p - rational(1);
        case 2: return rational(1);
        default: return mod(r, p);
        }
    };
    for (unsigned i = 0; i < rounds; ++i) {
        rational a = sample(), b = sample();
        auto x = f.from(a), y = f.from(b);
        ENSURE(f.to(x) == a && f.to(y) == b);
        ENSURE(f.to(f.add(x, y)) == mod(a + b, p));
        ENSURE(f.to(f.sub(x, y)) == mod(a - b, p));
        ENSURE(f.to(f.mul(x, y)) == mod(a * b, p));
        ENSURE(f.to(f.neg(x)) == mod(-a, p));
        if (!a.is_zero())
            ENSURE(f.to(f.mul(x, f.inv(x))) == rational(1));
    }
}

static void test_ff_f4_guards() {
    reslimit limit;
    v_dependency_manager deps;
    ff::engine e(deps, rational(7), limit);
    auto x = e.variable(0);
    auto eq = e.add(x, e.constant(rational(-1)));
    ff::dep_insert(deps, eq.dependencies, 17);
    ff::f4_config cfg;
    ff::f4_stats stats;
    std::vector<rational> values{rational(42)};
    v_dependency *core = deps.mk_leaf(reinterpret_cast<void *>(static_cast<uintptr_t>(99)));
    auto charge = [](unsigned) {};
    cfg.max_vars = 1;
    ENSURE(ff::f4_solve(deps, rational(7), {}, {x}, 1, values, core, cfg, stats, charge) == l_undef);
    ENSURE(values[0] == rational(42) && ff::dep_linearize(deps, core) == std::set<unsigned>{99});
    cfg.max_vars = 2;
    ENSURE(ff::f4_solve(deps, rational(7), {}, {x}, 1, values, core, cfg, stats, charge) == l_true);
    ENSURE(!values[0].is_zero());
    cfg.max_monomials = 1;
    bool stopped = false;
    try { ff::f4_solve(deps, rational(7), {eq}, {}, 1, values, core, cfg, stats, charge); }
    catch (ff::exhausted const &) { stopped = true; }
    ENSURE(stopped);
    cfg.max_monomials = 1024;
    ENSURE(ff::f4_solve(deps, rational(7), {eq}, {}, 1, values, core, cfg, stats, charge) == l_true);
    ENSURE(values[0].is_one());
    // Do not allow the input conversion to wrap a uint16 exponent to zero:
    // x^65536 = 0 has a solution; truncation would turn it into 1 = 0.
    ff::polynomial high;
    high.emplace(ff::monomial(65536, 0), rational(1));
    stopped = false;
    try { ff::f4_solve(deps, rational(7), {high}, {}, 1, values, core, cfg, stats, charge); }
    catch (ff::exhausted const &) { stopped = true; }
    ENSURE(stopped);
    ff::polynomial many;
    for (unsigned degree = 1; degree <= 300; ++degree)
        many.emplace(ff::monomial(degree, 0), rational(1));
    stopped = false;
    unsigned callbacks = 0;
    try {
        ff::f4_solve(deps, rational(7), {many}, {}, 1, values, core, cfg, stats,
                     [&](unsigned) { ++callbacks; throw ff::exhausted(); });
    }
    catch (ff::exhausted const &) { stopped = true; }
    ENSURE(stopped && callbacks == 1);
    ENSURE(ff::f4_solve(deps, rational(7), {eq}, {}, 1, values, core, cfg, stats, charge) == l_true);
    std::cout << "F4 guards: auxiliary variables, monomial admission, exponent overflow, cancellation and reuse\n";
}

static void test_ff_f4() {
    test_ff_f4_guards();
    // Fixed-width arithmetic, including a modulus whose top limb exceeds
    // 2^63 (general CIOS path) and BN254 / BLS12-381 (no-carry path).
    check_field_arithmetic<ff::field64>(rational(2147483647), 2000);
    check_field_arithmetic<ff::field64>(rational::power_of_two(61) - rational(1), 2000);
    check_field_arithmetic<ff::field64>(rational(7), 200);
    check_field_arithmetic<ff::field256>(
        rational("21888242871839275222246405745257275088548364400416034343698204186575808495617"), 2000);
    check_field_arithmetic<ff::field256>(
        rational("52435875175126190479447740508185965837690552500527637822603658699938581184513"), 2000);
    check_field_arithmetic<ff::field256>(rational::power_of_two(256) - rational(189), 2000);

    // F4 against exhaustive enumeration: SAT answers are models, UNSAT cores
    // exclude every assignment (so the conflict clause is valid).
    for (unsigned prime : {3u, 5u, 7u}) {
        reslimit limit;
        v_dependency_manager deps;
        ff::engine builder(deps, rational(prime), limit, 100000000);
        uint64_t state = 12345 + prime;
        auto next = [&]() {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            return static_cast<unsigned>(state % 1000003);
        };
        for (unsigned round = 0; round < 300; ++round) {
            unsigned nv = 1 + next() % 3, ne = 1 + next() % 3, nn = next() % 2;
            auto random_poly = [&](unsigned dep) {
                ff::polynomial f;
                unsigned terms = 1 + next() % 4;
                for (unsigned t = 0; t < terms; ++t) {
                    ff::monomial mon;
                    unsigned deg = next() % 3;
                    for (unsigned d = 0; d < deg; ++d)
                        mon.push_back(next() % nv);
                    std::sort(mon.begin(), mon.end());
                    builder.add_term(f, mon, rational(next() % prime));
                }
                f.dependencies = deps.mk_join(f.dependencies, deps.mk_leaf(reinterpret_cast<void *>(static_cast<uintptr_t>(dep))));
                return f;
            };
            std::vector<ff::polynomial> eqs, neqs;
            for (unsigned i = 0; i < ne; ++i)
                eqs.push_back(random_poly(i));
            for (unsigned i = 0; i < nn; ++i)
                neqs.push_back(random_poly(ne + i));
            std::vector<rational> values(nv, rational(0));
            v_dependency *core = nullptr;
            ff::f4_config cfg;
            ff::f4_stats st;
            auto charge = [](unsigned) {};
            lbool r = ff::f4_solve(deps, rational(prime), eqs, neqs, nv, values, core, cfg, st, charge);
            auto eval = [&](ff::polynomial const &f, std::vector<rational> const &a) {
                rational acc(0);
                for (auto const &[mon, c] : f) {
                    rational t = c;
                    for (unsigned v : mon)
                        t *= a[v];
                    acc += t;
                }
                return mod(acc, rational(prime));
            };
            bool any = false;
            std::vector<rational> a(nv);
            unsigned total = 1;
            for (unsigned i = 0; i < nv; ++i)
                total *= prime;
            std::set<unsigned> core_idxs = ff::dep_linearize(deps, core);
            for (unsigned code = 0; code < total; ++code) {
                unsigned c = code;
                for (unsigned i = 0; i < nv; ++i, c /= prime)
                    a[i] = rational(c % prime);
                bool ok = true, core_ok = true;
                for (unsigned i = 0; i < eqs.size(); ++i) {
                    bool holds = eval(eqs[i], a).is_zero();
                    ok &= holds;
                    if (core_idxs.contains(i))
                        core_ok &= holds;
                }
                for (unsigned i = 0; i < neqs.size(); ++i) {
                    bool holds = !eval(neqs[i], a).is_zero();
                    ok &= holds;
                    if (core_idxs.contains(ne + i))
                        core_ok &= holds;
                }
                any |= ok;
                if (r == l_false)
                    ENSURE(!core_ok);
            }
            if (r == l_true) {
                ENSURE(any);
                for (auto const &f : eqs)
                    ENSURE(eval(f, values).is_zero());
                for (auto const &f : neqs)
                    ENSURE(!eval(f, values).is_zero());
            }
            if (r == l_false)
                ENSURE(!any);
        }
    }

    // Zero-dimensional model construction over BN254: x*y = 6, x + y = 5.
    {
        rational p("21888242871839275222246405745257275088548364400416034343698204186575808495617");
        reslimit limit;
        v_dependency_manager deps;
        ff::engine e(deps, p, limit);
        auto x = e.variable(0), y = e.variable(1);
        auto f = e.add(e.mul(x, y), e.constant(rational(-6)));
        auto g = e.add(e.add(x, y), e.constant(rational(-5)));
        std::vector<rational> values(2, rational(0));
        v_dependency *core = nullptr;
        ff::f4_config cfg;
        ff::f4_stats st;
        auto charge = [](unsigned) {};
        ENSURE(ff::f4_solve(deps, p, {f, g}, {}, 2, values, core, cfg, st, charge) == l_true);
        ENSURE(mod(values[0] * values[1], p) == rational(6) && mod(values[0] + values[1], p) == rational(5));
        ENSURE(st.m_minpolys >= 1);
        // x^2 = 3 has no root when 3 is a quadratic non-residue; BN254 - 1 is
        // divisible by 3, so use x^2 = -1 * r with r a non-residue found by Euler's test.
        rational r(5);
        while (true) {
            // Euler: r^((p-1)/2) == -1 mod p.
            rational e2 = div(p - rational(1), rational(2)), acc(1), base = r;
            while (e2.is_pos()) {
                if (!mod(e2, rational(2)).is_zero())
                    acc = mod(acc * base, p);
                base = mod(base * base, p);
                e2 = div(e2, rational(2));
            }
            if (acc == p - rational(1))
                break;
            r += rational(1);
        }
        auto h = e.add(e.mul(x, x), e.constant(-r));
        ff::dep_insert(deps, h.dependencies, 7);
        core = nullptr;
        ENSURE(ff::f4_solve(deps, p, {h}, {}, 2, values, core, cfg, st, charge) == l_false);
        ENSURE(ff::dep_linearize(deps, core) == std::set<unsigned>({7}));
    }
}

#else
static void test_ff_f4() {
    ff::f4_config cfg;
    ff::f4_stats stats;
    std::vector<rational> values{rational(42)};
    v_dependency_manager deps;
    v_dependency *core = deps.mk_leaf(reinterpret_cast<void *>(static_cast<uintptr_t>(7)));
    ENSURE(!ff::f4_supported(rational(7)));
    ENSURE(ff::f4_solve(deps, rational(7), {}, {}, 1, values, core, cfg, stats, [](unsigned) {}) == l_undef);
    ENSURE(values[0] == rational(42) && ff::dep_linearize(deps, core) == std::set<unsigned>{7});
    ENSURE(stats.m_unsupported == 1);
}
#endif


// Tiny-field search against exhaustive enumeration: random systems of
// equations and disequations over F_p, p < 64.
static void test_ff_tiny() {
    // Deep finite search uses a heap choice stack, even for independent
    // variables. Re-run after an interrupted attempt to check local cleanup.
    std::vector<uint32_t> model;
    ff::tiny_stats stats;
    bool stopped = false;
    try {
        ff::tiny_search(3, 12000, {}, model, [](unsigned n) { if (n) throw ff::exhausted(); }, stats);
    }
    catch (ff::exhausted const &) { stopped = true; }
    ENSURE(stopped && model.empty());
    ENSURE(ff::tiny_search(3, 12000, {}, model, [](unsigned) {}, stats) == l_true);
    ENSURE(model.size() == 12000 && std::all_of(model.begin(), model.end(), [](unsigned v) { return v == 0; }));
    uint64_t seed = 12345;
    auto rnd = [&](unsigned k) {
        seed = seed * 6364136223846793005ull + 1442695040888963407ull;
        return static_cast<unsigned>((seed >> 33) % k);
    };
    unsigned sat = 0, unsat = 0;
    for (unsigned round = 0; round < 600; ++round) {
        unsigned const primes[] = {2, 3, 5, 7, 13, 61};
        uint32_t p = primes[rnd(6)];
        unsigned n = 1 + rnd(p <= 7 ? 5 : 3);
        std::vector<ff::tiny_constraint> cs(1 + rnd(6));
        for (auto &c : cs) {
            c.is_neq = rnd(4) == 0;
            unsigned terms = 1 + rnd(4);
            for (unsigned t = 0; t < terms; ++t) {
                ff::tiny_term tm;
                tm.coef = rnd(p);
                unsigned d = rnd(4);
                for (unsigned k = 0; k < d; ++k)
                    tm.vars.push_back(rnd(n));
                std::sort(tm.vars.begin(), tm.vars.end());
                c.terms.push_back(tm);
            }
        }
        auto holds = [&](std::vector<uint32_t> const &a) {
            for (auto const &c : cs) {
                uint64_t s = 0;
                for (auto const &t : c.terms) {
                    uint64_t x = t.coef;
                    for (uint32_t v : t.vars)
                        x = x * a[v] % p;
                    s += x;
                }
                if ((s % p == 0) == c.is_neq)
                    return false;
            }
            return true;
        };
        bool exists = false;
        std::vector<uint32_t> a(n, 0);
        for (;;) {
            if (holds(a)) {
                exists = true;
                break;
            }
            unsigned k = 0;
            while (k < n && ++a[k] == p)
                a[k++] = 0;
            if (k == n)
                break;
        }
        std::vector<uint32_t> model;
        ff::tiny_stats st;
        lbool r = ff::tiny_search(p, n, cs, model, [](unsigned) {}, st);
        ENSURE(r == (exists ? l_true : l_false));
        if (r == l_true) {
            ENSURE(holds(model));
            ++sat;
        }
        else
            ++unsat;
    }
    ENSURE(sat > 50 && unsat > 50);
}

static void test_ff_integration() {
    auto stat = [](smt::context &ctx, char const *key) {
        statistics stats; ctx.collect_statistics(stats);
        for (unsigned i = 0; i < stats.size(); ++i)
            if (std::string(stats.get_key(i)) == key)
                return stats.is_uint(i) ? double(stats.get_uint_value(i)) : stats.get_double_value(i);
        return 0.0;
    };
    ast_manager m; reg_decl_plugins(m); ff_util ff(m);
    // An unrelated field sort in the same manager must not install extra
    // theories in a field-free QF_UF context. A logic that does not mention
    // the field theory correctly never learns about it, even if some other
    // context sharing the same ast_manager happens to use it.
    sort_ref field(ff.mk_sort(rational(7)), m);
    smt_params sp;
    smt::context ctx(m, sp); ctx.set_logic(symbol("QF_UF"));
    expr_ref b(m.mk_const("b", m.mk_bool_sort()), m);
    ctx.assert_expr(b); ENSURE(ctx.check() == l_true);
    ENSURE(!ctx.get_theory(ff.get_fid()));
    ENSURE(!ctx.get_theory(m.get_family_id("bv")));
    // Using field terms requires declaring a logic that supports them
    // (QF_FF/QF_FFA); the field theory is then installed as part of the
    // logic's standard setup, same as every other theory.
    smt::context fctx(m, sp); fctx.set_logic(symbol("QF_FF"));
    expr_ref x(m.mk_const("x", field), m), two(ff.mk_numeral(rational(2), field), m);
    expr_ref square(ff.mk_mul(x, x), m);
    expr_ref eq(m.mk_eq(square, two), m);
    params_ref tiny; tiny.set_uint("ff.max_steps", 0); fctx.updt_params(tiny);
    fctx.push();
    fctx.assert_expr(eq); ENSURE(fctx.check() == l_true);
    ENSURE(stat(fctx, "ff bv fallbacks") > 0);
    double checks = stat(fctx, "ff native checks");
    fctx.pop(1);
    ENSURE(stat(fctx, "ff normalization cache entries") == 0);
    params_ref normal; normal.set_uint("ff.max_steps", 2000000); fctx.updt_params(normal);
    fctx.push(); fctx.assert_expr(eq); ENSURE(fctx.check() == l_true);
    ENSURE(stat(fctx, "ff native checks") > checks);
    // No new bridge axioms: the popped bridge did not permanently disable native solving.
    double axioms = stat(fctx, "ff combination axioms");
    fctx.pop(1); fctx.push(); fctx.assert_expr(eq); ENSURE(fctx.check() == l_true);
    ENSURE(stat(fctx, "ff combination axioms") == axioms);
    fctx.pop(1);
    // Algebra remains usable with BV disabled; an inconclusive algebra result
    // must return unknown instead of sending field definitions to a dummy theory.
    smt_params no_bv; no_bv.m_bv_mode = bv_solver_id::BS_NO_BV;
    smt::context disabled(m, no_bv); disabled.set_logic(symbol("QF_FF"));
    disabled.updt_params(tiny); disabled.assert_expr(eq);
    ENSURE(disabled.check() == l_undef);
    for (bool reverse : {false, true}) {
        ast_manager mm; reg_decl_plugins(mm);
        cmd_context commands(false, &mm);
        std::string defs = reverse ? "(define-sort A () (_ FiniteField 3))(define-sort B () (_ FiniteField 7))" :
                                     "(define-sort B () (_ FiniteField 7))(define-sort A () (_ FiniteField 3))";
        std::istringstream input(defs + "(declare-const x A)(declare-const u B)(declare-const v B)"
            "(assert (= (ff.mul x x) (as ff2 A)))"
            "(assert (= (ff.add (ff.mul u v) u v (as ff1 B)) (as ff0 B)))");
        ENSURE(parse_smt2_commands(commands, input));
        smt_params params; smt::context mixed(mm, params);
        params_ref bounded; bounded.set_uint("ff.max_terms", 2); mixed.updt_params(bounded);
        for (expr *a : commands.assertions()) mixed.assert_expr(a);
        ENSURE(mixed.check() == l_false);
        ENSURE(stat(mixed, "ff native conflicts") > 0);
        ENSURE(stat(mixed, "ff combination axioms") < 4);
    }
    std::cout << "FF integration: logic-gated registration, scoped fallback, disabled BV and independent fields\n";
}

// Substituting a wire into another assertion must retain the defining
// equation as a premise, including transitive definitions and shared terms.
static void test_ff_wire_dependencies() {
    ast_manager m;
    reg_decl_plugins(m);
    ff_util ff(m);
    sort_ref field(ff.mk_sort(rational(7)), m);
    expr_ref x(m.mk_const("x", field), m), y(m.mk_const("y", field), m);
    expr_ref z(m.mk_const("z", field), m), zero(ff.mk_numeral(rational(0), field), m);
    expr_ref square(ff.mk_mul(x, x), m);
    expr_ref first(m.mk_eq(y, square), m), second(m.mk_eq(z, ff.mk_add(y, square)), m);
    expr_ref last(m.mk_eq(z, zero), m);
    base_dependent_expr_state state(m);
    for (expr* f : {first.get(), second.get(), last.get()})
        state.add(dependent_expr(m, f, nullptr, m.mk_leaf(f)));
    ff_wire_simplifier pass(m, state);
    pass.reduce();
    ENSURE(!m.is_true(state[2].fml()) && !m.is_false(state[2].fml()));
    ptr_vector<expr> premises;
    m.linearize(state[2].dep(), premises);
    ENSURE(premises.size() == 3 && premises.contains(first) &&
           premises.contains(second) && premises.contains(last));
    smt_params sp;
    smt::context context(m, sp);
    for (expr* f : premises)
        context.assert_expr(f);
    expr_ref counterexample(m.mk_not(state[2].fml()), m);
    context.assert_expr(counterexample);
    ENSURE(context.check() == l_false);
}

// Exercise the zero-test pass before generic rewriting can flatten products.
// Both parenthesizations, n-ary input, and repeated factors must behave alike.
static void test_ff_nested_zero_test() {
    ast_manager m;
    reg_decl_plugins(m);
    ff_util ff(m);
    for (unsigned prime : {2u, 7u, 101u}) {
        sort_ref field(ff.mk_sort(rational(prime)), m);
        expr_ref a(m.mk_const("a", field), m), b(m.mk_const("b", field), m);
        expr_ref z(m.mk_const("z", field), m), u(m.mk_const("u", field), m);
        expr_ref zero(ff.mk_numeral(rational(0), field), m), one(ff.mk_numeral(rational(1), field), m);
        for (unsigned shape = 0; shape < 3; ++shape) {
            auto product = [&](expr_ref_vector const& args) {
                expr_ref r(m);
                if (shape == 0) {
                    r = args[0];
                    for (unsigned i = 1; i < args.size(); ++i)
                        r = ff.mk_mul(r, args[i]);
                }
                else if (shape == 1) {
                    r = args.back();
                    for (unsigned i = args.size() - 1; i-- > 0;)
                        r = ff.mk_mul(args[i], r);
                }
                else
                    r = ff.mk_mul(args);
                return r;
            };
            expr_ref_vector guard_args(m);
            guard_args.push_back(a); guard_args.push_back(z);
            guard_args.push_back(a); guard_args.push_back(b);
            expr_ref guard(m.mk_eq(product(guard_args), zero), m);
            for (bool complete : {false, true}) {
                expr_ref_vector definition_args(m);
                definition_args.push_back(b); definition_args.push_back(u);
                definition_args.push_back(a);
                if (complete)
                    definition_args.push_back(a);
                definition_args.push_back(ff.mk_numeral(rational(prime - 1), field));
                expr_ref rhs(ff.mk_add(one, product(definition_args)), m);
                expr_ref definition(m.mk_eq(z, rhs), m);
                base_dependent_expr_state state(m);
                state.add(dependent_expr(m, guard, nullptr, m.mk_leaf(guard)));
                state.add(dependent_expr(m, definition, nullptr, m.mk_leaf(definition)));
                ff_zero_test_simplifier pass(m, state);
                pass.reduce();
                ENSURE(state.qtail() == (complete ? 3u : 2u));
                if (complete) {
                    ptr_vector<expr> premises;
                    m.linearize(state[2].dep(), premises);
                    ENSURE(premises.size() == 2 && premises.contains(guard) && premises.contains(definition));
                    // Independently ask the SMT context whether the premises
                    // admit a counterexample to the newly derived equality.
                    smt_params params;
                    smt::context context(m, params);
                    context.assert_expr(guard);
                    context.assert_expr(definition);
                    expr_ref counterexample(m.mk_not(state[2].fml()), m);
                    context.assert_expr(counterexample);
                    ENSURE(context.check() == l_false);
                }
            }
        }
    }
}

void tst_finite_field() {
    test_ff_wire_dependencies();
    test_ff_nested_zero_test();
    test_ff_integration();
    test_ff_tiny();
    test_ff_f4();
    test_certificates();
    ff::test_engine::adaptive_basis_storage();
    ff::test_engine::sparse_matrix_selection();
    ff::test_engine::work_accounting();
    ff::test_engine::fused_reduction_equivalence();

    ff::test_engine::minimal_polynomial_provenance();
    ff::test_engine::minimal_polynomial_guard_budget();
    ff::test_engine::lazy_matrix_equivalence();
    ff::test_engine::matrix_limit_diagnostics();
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
            v_dependency_manager deps;
            ff::engine e(deps, rational(prime), limit, 1000000);
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
                    v_dependency_manager deps;
                    auto leaf = [&](unsigned i) { return deps.mk_leaf(reinterpret_cast<void *>(static_cast<uintptr_t>(i))); };
                    ff::engine algebra(deps, rational(prime), l, 1000000);
                    auto x = algebra.variable(0), y = algebra.variable(1);
                    auto product = algebra.add(algebra.mul(x, y), algebra.constant(-rational(a)));
                    auto sum = algebra.add(algebra.add(x, y), algebra.constant(-rational(b)));
                    auto neq = algebra.add(x, algebra.constant(-rational(c)));
                    product.dependencies = deps.mk_join(product.dependencies, leaf(0));
                    sum.dependencies = deps.mk_join(sum.dependencies, leaf(1));
                    neq.dependencies = deps.mk_join(neq.dependencies, leaf(2));
                    std::vector<rational> values(2, rational(0));
                    auto status = algebra.solve({product, sum}, {neq}, values);
                    if (status == l_false) {
                        auto const core = algebra.conflict();
                        auto has = [&](unsigned i) { return deps.contains(core, reinterpret_cast<void *>(static_cast<uintptr_t>(i))); };
                        for (unsigned u = 0; u < prime; ++u)
                            for (unsigned v = 0; v < prime; ++v)
                                ENSURE(!((!has(0) || u * v % prime == a) &&
                                         (!has(1) || (u + v) % prime == b) && (!has(2) || u != c)));
                    }
                }
    reslimit limit;
    v_dependency_manager top_deps;
    ff::engine e(top_deps, rational("21888242871839275222246405745257275088548364400416034343698204186575808495617"), limit);
    auto x = e.variable(0), y = e.variable(1);
    // Conflicting polynomial ideals, not just constant propagation.
    auto f = e.add(e.mul(x, y), e.constant(rational(-1)));
    auto g = e.add(e.mul(x, y), e.constant(rational(-2)));
    std::vector<rational> values(2, rational(0));
    ENSURE(e.solve({f, g}, {}, values) == l_false);
    // Algebra resource exhaustion is an explicit fallback request.
    v_dependency_manager bounded_deps;
    ff::engine bounded(bounded_deps, rational(7), limit, 0);
    bool exhausted = false;
    try {
        bounded.variable(0);
    } catch (ff::exhausted const &) {
        exhausted = true;
    }
    ENSURE(exhausted);
}
