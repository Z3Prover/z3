/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_polynomial.h

Abstract:

    Sparse multivariate polynomial representation (monomial -> rational
    coefficient maps) over Q, with input-constraint provenance tracking,
    used by the Groebner-basis elimination engine for prime fields.

Author:

    Romain Soulat

--*/
#pragma once
#include "util/rational.h"
#include "util/rlimit.h"
#include "util/lbool.h"
#include "util/statistics.h"
#include <map>
#include <vector>
#include <set>

namespace ff {
    using monomial = std::vector<unsigned>;
    struct monomial_order {
        bool operator()(monomial const &a, monomial const &b) const {
            return a.size() != b.size() ? a.size() > b.size() : a > b;
        }
    };
    struct polynomial : public std::map<monomial, rational, monomial_order> {
        // Input-constraint provenance for conflict clauses. This is not a proof:
        // v2 additionally needs the polynomial multipliers witnessing each step.
        std::set<unsigned> dependencies;
        // Degree of the homogenized computation, including cancelled terms.
        // This is scheduling metadata only, never an algebraic premise.
        unsigned sugar = 0;
    };
    struct exhausted {};
    // Exact, bounded memoization of basis computations. Entries contain only
    // polynomial data and numeric premise indices, never context-owned ASTs.
    struct basis_cache {
        struct entry {
            rational prime;
            std::vector<polynomial> input, output;
        };
        std::vector<entry> entries;
        unsigned hits = 0, misses = 0;
        void clear() {
            entries.clear();
        }
    };

    // Backend-independent modular polynomial arithmetic. All transformations below
    // are ideal operations or invertible variable eliminations. A future certificate
    // recorder can attach polynomial-combination witnesses at add_scaled/reduce.
    struct f4_config;
    struct f4_stats;

    class engine {
        // Unit tests exercise bounded matrix admission directly, without an
        // unrelated Groebner pair schedule deciding whether the cap is reached.
        friend struct test_engine;
        friend class certificate_builder;
        rational p;
        reslimit &limit;
        unsigned work = 0, max_work, max_terms;
        unsigned random_state = 17;
        enum work_phase { other_work, scalar_work, insertion_work, pair_work, symbolic_work, matrix_work, num_work_phases };
        unsigned m_phase_work[num_work_phases] = {};
        work_phase m_work_phase = other_work;
        unsigned m_phase_start = 0;
        // Exclusive work attribution: nested scopes charge only their own
        // ticks, including the failing tick on resource exhaustion. Scope
        // transitions do not consume work or alter shared cancellation.
        class scoped_work {
            engine &e;
            work_phase previous;
            void enter(work_phase phase) {
                e.m_phase_work[e.m_work_phase] += e.work - e.m_phase_start;
                e.m_phase_start = e.work;
                e.m_work_phase = phase;
            }
        public:
            scoped_work(engine &e, work_phase phase) : e(e), previous(e.m_work_phase) { enter(phase); }
            ~scoped_work() { enter(previous); }
            scoped_work(scoped_work const &) = delete;
            scoped_work &operator=(scoped_work const &) = delete;
        };
        bool bit_propagation, batch_enabled, sparse_enabled;
        basis_cache *memo = nullptr;
        unsigned m_bit_facts = 0, m_bit_rounds = 0;
        unsigned m_eliminations = 0, m_substitutions = 0, m_substituted_terms = 0;
        unsigned m_basis_calls = 0, m_basis_pairs = 0, m_root_calls = 0;
        unsigned m_chain_skips = 0, m_fused_reductions = 0;
        unsigned m_batches = 0, m_matrix_rows = 0;
        unsigned m_extra_matrix_reducers = 0, m_lazy_matrix_reducers = 0, m_sparse_matrix_reducers = 0;
        unsigned m_sparse_trials = 0, m_sparse_witnesses = 0;
        unsigned m_step_exhaustions = 0, m_term_exhaustions = 0, m_basis_exhaustions = 0, m_matrix_exhaustions = 0;
        // Sub-counters identify the unchanged guard that ended an attempt.
        // Peaks are per engine (not process RSS); wrapper statistics may sum
        // them across independent engine calls rather than take a global max.
        unsigned m_local_work_exhaustions = 0, m_shared_limit_exhaustions = 0;
        unsigned m_polynomial_terms_exhaustions = 0, m_monomial_degree_exhaustions = 0;
        unsigned m_active_basis_exhaustions = 0, m_basis_slots_exhaustions = 0;
        unsigned m_basis_storage_exhaustions = 0, m_pair_storage_exhaustions = 0;
        unsigned m_pair_compactions = 0, m_discarded_pairs = 0;
        size_t m_peak_basis_bytes = 0, m_peak_pair_bytes = 0, m_peak_active_basis = 0;
        size_t m_basis_storage_limit = 16 * 1024 * 1024, m_pair_storage_limit = 16 * 1024 * 1024;
        unsigned m_matrix_symbolic_exhaustions = 0, m_matrix_reducer_exhaustions = 0;
        unsigned m_matrix_column_exhaustions = 0, m_matrix_row_exhaustions = 0, m_matrix_pivot_exhaustions = 0;
        size_t m_peak_matrix_columns = 0, m_peak_matrix_reducers = 0, m_peak_matrix_row_terms = 0;
        size_t m_peak_matrix_symbolic_bytes = 0, m_peak_matrix_coefficient_bytes = 0, m_peak_matrix_dependency_bytes = 0;
        std::vector<polynomial> batch_reduce(std::vector<polynomial> const &rows,
                                             std::vector<polynomial> const &basis);
        std::set<unsigned> m_conflict;
        unsigned m_deferred_eliminations = 0, m_scalar_fallbacks = 0, m_gm_skips = 0, m_mask_skips = 0, m_bucket_reductions = 0, m_small_products = 0;
        rational coefficient_product(rational const &a, rational const &b);
        rational coefficient_residue(rational const &a);
        void configure_probe(engine &probe) const;
        void tick();
        rational random_value();
        polynomial substitute(polynomial const &f, unsigned v, polynomial const &value);
        polynomial remainder(polynomial f, polynomial const &divisor);
        polynomial gcd(polynomial a, polynomial b);
        polynomial power_mod(polynomial a, rational exponent, polynomial const &modulus);
        void split_roots(polynomial const &f, unsigned v, std::vector<rational> &out);
        lbool solve_core(std::vector<polynomial> eqs, std::vector<polynomial> neqs, std::vector<rational> &values,
                         unsigned depth);

        void split_consequences(std::vector<polynomial> &eqs);
        lbool tiny_solve(std::vector<polynomial> const &eqs, std::vector<polynomial> const &neqs,
                         std::vector<rational> &values);
        polynomial minimal_polynomial(unsigned v, std::vector<polynomial> const &bs);
        bool small_quotient(std::vector<polynomial> const &bs, std::set<unsigned> &vars);
        bool quotient_field_basis(std::vector<polynomial> &bs);
        unsigned m_split_facts = 0, m_minpolys = 0, m_model_probes = 0, m_bound_facts = 0;
        unsigned m_quotient_probes = 0, m_quotient_facts = 0, m_quotient_exhaustions = 0;
    public:
        std::set<unsigned> definition_variables;
        bool bounded_elimination = false;
        bool adaptive_reduction = false;
        bool adaptive_matrix = false;
        bool adaptive_basis = false;
        bool lazy_matrix = false;
        bool sparse_matrix_reducers = false;
        bool fused_reduction = false;
        bool sugar_pairs = false, gm_pairs = false, div_masks = false, geobucket = false, small_coefficients = false, compact_encoding = false;
        bool linear_split = false, basis_bits = false, compact_matrix = false, model_search = false, bit_bounds = false;
        bool root_completion = false, quotient_field = false;
        // Fixed-width F4 backend with zero-dimensional model construction.
        bool f4 = true;
        unsigned f4_max_quotient = 1024;
        unsigned f4_budget_factor = 40;  // F4 work units allowed per legacy step (algebraic systems)
        unsigned f4_short_budget = 1;     // same, for circuit-like systems with many Boolean variables
        unsigned f4_bit_heavy = 0;
        bool m_bit_heavy_input = false;
        bool f4_value_split = false;
        unsigned f4_slice = 4;  // random slices per level for positive-dimensional ideals (SAT only)
        // Complete finite-domain search over tiny fields (p < 64).
        bool tiny_search = true;
        unsigned tiny_budget = 200;  // search work units per legacy step
        unsigned tiny_calls = 0, tiny_sat = 0, tiny_unsat = 0, tiny_undef = 0;
        uint64_t tiny_nodes = 0;
        bool f4_handback = false;  // also hand inconclusive F4 bases to the legacy heuristics over small fields
        uint64_t f4_steps = 0;
        unsigned f4_calls = 0, f4_sat = 0, f4_unsat = 0, f4_undef = 0;
        std::vector<unsigned> f4_counters = std::vector<unsigned>(11, 0);
        engine(rational const &p, reslimit &limit, unsigned max_work = 200000, unsigned max_terms = 4096,
               bool bit_propagation = true, bool batch_enabled = true, bool sparse_enabled = true)
            : p(p), limit(limit), max_work(max_work), max_terms(max_terms), bit_propagation(bit_propagation),
              batch_enabled(batch_enabled), sparse_enabled(sparse_enabled) {}
        void add_term(polynomial &f, monomial const &mon, rational const &c);
        polynomial constant(rational const &c);
        polynomial variable(unsigned v);
        polynomial add(polynomial a, polynomial const &b, rational const &scale = rational(1));
        polynomial mul(polynomial const &a, polynomial const &b);
        polynomial scale(polynomial a, rational const &c);
        rational inverse(rational a);
        rational evaluate(polynomial const &a, std::vector<rational> const &values);
        polynomial reduce(polynomial f, std::vector<polynomial> const &basis);
        void basis(std::vector<polynomial> &eqs);
        unsigned propagate_bits(std::vector<polynomial> &eqs);
        void set_basis_storage_limit(unsigned bytes) {
            // Keep accumulation safe on 32-bit hosts, and preserve an absolute
            // bound even when a caller requests the largest unsigned value.
            m_basis_storage_limit = std::min<size_t>(bytes, 1024u * 1024u * 1024u);
        }
        void set_basis_cache(basis_cache *c) {
            memo = c;
        }
        lbool solve(std::vector<polynomial> const &eqs, std::vector<polynomial> const &neqs,
                    std::vector<rational> &values);
        std::set<unsigned> const &conflict() const {
            return m_conflict;
        }
        bool polynomial_limit_hit() const { return m_term_exhaustions != 0; }
        unsigned steps() const {
            return work;
        }
        void collect_statistics(statistics &st) const;
    };
}  // namespace ff
