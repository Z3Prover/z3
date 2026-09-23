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
    class engine {
        // Unit tests exercise bounded matrix admission directly, without an
        // unrelated Groebner pair schedule deciding whether the cap is reached.
        friend struct test_engine;
        rational p;
        reslimit &limit;
        unsigned work = 0, max_work, max_terms;
        unsigned random_state = 17;
        bool bit_propagation, batch_enabled, sparse_enabled;
        basis_cache *memo = nullptr;
        unsigned m_bit_facts = 0, m_bit_rounds = 0;
        unsigned m_eliminations = 0, m_substitutions = 0, m_substituted_terms = 0;
        unsigned m_basis_calls = 0, m_basis_pairs = 0, m_root_calls = 0;
        unsigned m_chain_skips = 0;
        unsigned m_batches = 0, m_matrix_rows = 0;
        unsigned m_extra_matrix_reducers = 0;
        unsigned m_sparse_trials = 0, m_sparse_witnesses = 0;
        unsigned m_step_exhaustions = 0, m_term_exhaustions = 0, m_basis_exhaustions = 0, m_matrix_exhaustions = 0;
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
        bool sugar_pairs = false, gm_pairs = false, div_masks = false, geobucket = false, small_coefficients = false, compact_encoding = false;
        bool linear_split = false, basis_bits = false, compact_matrix = false, model_search = false, bit_bounds = false;
        bool root_completion = false, quotient_field = false;
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
