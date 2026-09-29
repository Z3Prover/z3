#pragma once

#include "math/polynomial/ff_polynomial.h"
#include "params/smt_params_helper.hpp"

namespace ff {
    // Resolve local overrides and the global SMT defaults from one snapshot.
    inline void configure_engine(engine &algebra, smt_params_helper const &options) {
        algebra.linear_split = options.ff_linear_split();
        algebra.basis_bits = options.ff_basis_bits();
        algebra.compact_matrix = options.ff_compact_matrix();
        algebra.model_search = options.ff_model_search();
        algebra.root_completion = options.ff_root_completion();
        algebra.quotient_field = options.ff_quotient_field();
        algebra.bit_bounds = options.ff_bit_bounds();
        algebra.adaptive_reduction = options.ff_adaptive_reduction();
        algebra.adaptive_matrix = options.ff_adaptive_matrix();
        algebra.adaptive_basis = options.ff_adaptive_basis();
        algebra.set_basis_storage_limit(options.ff_basis_max_bytes());
        algebra.lazy_matrix = options.ff_lazy_matrix();
        algebra.sparse_matrix_reducers = options.ff_sparse_matrix_reducers();
        algebra.fused_reduction = options.ff_fused_reduction();
        algebra.bounded_elimination = options.ff_bounded_elimination();
        algebra.sugar_pairs = options.ff_sugar_pairs();
        algebra.gm_pairs = options.ff_gm_pairs();
        algebra.div_masks = options.ff_div_masks();
        algebra.geobucket = options.ff_geobucket();
        algebra.small_coefficients = options.ff_small_coefficients();
        algebra.compact_encoding = options.ff_compact_encoding();
        algebra.f4 = options.ff_f4();
        algebra.f4_max_quotient = options.ff_f4_max_quotient();
        algebra.f4_budget_factor = options.ff_f4_budget();
        algebra.f4_short_budget = options.ff_f4_short_budget();
        algebra.f4_value_split = options.ff_f4_value_split();
        algebra.f4_slice = options.ff_f4_slice();
        algebra.tiny_search = options.ff_tiny();
        algebra.tiny_budget = options.ff_tiny_budget();
    }
}
