# Shadow: src/smt/theory_arith.h

**Language**: C | **Lines**: 1282 | **Last modified**: 2026-07-02

## File-Level

_No discoveries yet._

## `class theory_arith_stats`

### `theory_arith_stats.reset`

_No discoveries yet._

## `R`

_No discoveries yet._

## `class theory_arith`

### `theory_arith.proofs_enabled`

_No discoveries yet._

### `theory_arith.coeffs_enabled`

_No discoveries yet._

## `class linear_monomial`

_No discoveries yet._

## `class row_entry`

### `row_entry.is_dead`

_No discoveries yet._

## `class col_entry`

### `col_entry.is_dead`

_No discoveries yet._

## `class column`

_No discoveries yet._

## `class row`

### `row.size`

_No discoveries yet._

### `row.num_entries`

_No discoveries yet._

### `row.reset`

_No discoveries yet._

### `row.add_row_entry`

_No discoveries yet._

### `row.del_row_entry`

_No discoveries yet._

### `row.compress`

_No discoveries yet._

### `row.compress_if_needed`

_No discoveries yet._

### `row.save_var_pos`

_No discoveries yet._

### `row.reset_var_pos`

_No discoveries yet._

### `row.get_base_var`

_No discoveries yet._

### `row.is_coeff_of`

_No discoveries yet._

### `row.display`

_No discoveries yet._

### `row.get_denominators_lcm`

_No discoveries yet._

### `row.get_idx_of`

_No discoveries yet._

## `class column`

### `column.size`

_No discoveries yet._

### `column.num_entries`

_No discoveries yet._

### `column.reset`

_No discoveries yet._

### `column.compress`

_No discoveries yet._

### `column.compress_if_needed`

_No discoveries yet._

### `column.compress_singleton`

_No discoveries yet._

### `column.add_col_entry`

_No discoveries yet._

### `column.del_col_entry`

_No discoveries yet._

## `class antecedents_t`

### `antecedents_t.empty`

_No discoveries yet._

### `antecedents_t.init`

_No discoveries yet._

### `antecedents_t.reset`

_No discoveries yet._

### `antecedents_t.push_lit`

_No discoveries yet._

### `antecedents_t.push_eq`

_No discoveries yet._

### `antecedents_t.append`

_No discoveries yet._

### `antecedents_t.append`

_No discoveries yet._

### `antecedents_t.num_params`

_No discoveries yet._

### `antecedents_t.params`

_No discoveries yet._

### `antecedents_t.display`

_No discoveries yet._

## `class antecedents`

### `antecedents.push_lit`

_No discoveries yet._

### `antecedents.push_eq`

_No discoveries yet._

### `antecedents.append`

_No discoveries yet._

### `antecedents.append`

_No discoveries yet._

### `antecedents.num_params`

_No discoveries yet._

### `antecedents.params`

_No discoveries yet._

### `antecedents.display`

_No discoveries yet._

## `class gomory_cut_justification`

_No discoveries yet._

## `class bound`

### `bound.get_var`

_No discoveries yet._

### `bound.get_bound_kind`

_No discoveries yet._

### `bound.is_atom`

_No discoveries yet._

### `bound.has_justification`

_No discoveries yet._

### `bound.push_justification`

_No discoveries yet._

### `bound.display`

_No discoveries yet._

## `class atom`

### `atom.get_atom_kind`

_No discoveries yet._

### `atom.get_bool_var`

_No discoveries yet._

### `atom.is_true`

_No discoveries yet._

### `atom.assign_eh`

_No discoveries yet._

### `atom.has_justification`

_No discoveries yet._

### `atom.push_justification`

_No discoveries yet._

### `atom.display`

_No discoveries yet._

## `class eq_bound`

### `eq_bound.has_justification`

_No discoveries yet._

### `eq_bound.push_justification`

_No discoveries yet._

### `eq_bound.display`

_No discoveries yet._

## `class derived_bound`

### `derived_bound.has_justification`

_No discoveries yet._

### `derived_bound.push_justification`

_No discoveries yet._

### `derived_bound.push_lit`

_No discoveries yet._

### `derived_bound.push_eq`

_No discoveries yet._

### `derived_bound.display`

_No discoveries yet._

## `class justified_derived_bound`

### `justified_derived_bound.has_justification`

_No discoveries yet._

### `justified_derived_bound.push_justification`

_No discoveries yet._

### `justified_derived_bound.push_lit`

_No discoveries yet._

### `justified_derived_bound.push_eq`

_No discoveries yet._

## `accumulate_justification`

_No discoveries yet._

## `normalize_bound`

_No discoveries yet._

## `mk_bound_from_row`

_No discoveries yet._

## `class theory_var_lt`

### `theory_var_lt.operator`

_No discoveries yet._

## `class var_data`

### `var_data.kind`

_No discoveries yet._

## `class bound_trail`

### `bound_trail.is_upper`

_No discoveries yet._

### `bound_trail.get_var`

_No discoveries yet._

### `bound_trail.get_old_bound`

_No discoveries yet._

## `class scope`

_No discoveries yet._

## `class var_value_hash`

_No discoveries yet._

## `class var_value_hash`

### `var_value_hash.operator`

_No discoveries yet._

## `class var_value_eq`

_No discoveries yet._

## `class var_value_eq`

### `var_value_eq.operator`

_No discoveries yet._

## `mk_var`

_No discoveries yet._

## `found_unsupported_op`

_No discoveries yet._

## `found_underspecified_op`

_No discoveries yet._

## `has_var`

_No discoveries yet._

## `expr2var`

_No discoveries yet._

## `var2expr`

_No discoveries yet._

## `reflection_enabled`

_No discoveries yet._

## `reflect`

_No discoveries yet._

## `lazy_pivoting_lvl`

_No discoveries yet._

## `propagate_eqs`

_No discoveries yet._

## `propagate_diseqs`

_No discoveries yet._

## `random_initial_value`

_No discoveries yet._

## `random_lower`

_No discoveries yet._

## `random_upper`

_No discoveries yet._

## `blands_rule_threshold`

_No discoveries yet._

## `propagation_mode`

_No discoveries yet._

## `adaptive`

_No discoveries yet._

## `adaptive_assertion_threshold`

_No discoveries yet._

## `max_lemma_size`

_No discoveries yet._

## `small_lemma_size`

_No discoveries yet._

## `relax_bounds`

_No discoveries yet._

## `skip_big_coeffs`

_No discoveries yet._

## `process_atoms`

_No discoveries yet._

## `get_num_conflicts`

_No discoveries yet._

## `get_var_kind`

_No discoveries yet._

## `is_base`

_No discoveries yet._

## `is_quasi_base`

_No discoveries yet._

## `is_non_base`

_No discoveries yet._

## `set_var_kind`

_No discoveries yet._

## `get_var_row`

_No discoveries yet._

## `set_var_row`

_No discoveries yet._

## `is_int_expr`

_No discoveries yet._

## `is_int`

_No discoveries yet._

## `is_int_src`

_No discoveries yet._

## `is_real`

_No discoveries yet._

## `is_real_src`

_No discoveries yet._

## `get_implied_old_value`

_No discoveries yet._

## `get_bound`

_No discoveries yet._

## `lower`

_No discoveries yet._

## `upper`

_No discoveries yet._

## `below_lower`

_No discoveries yet._

## `above_upper`

_No discoveries yet._

## `below_upper`

_No discoveries yet._

## `above_lower`

_No discoveries yet._

## `at_bound`

_No discoveries yet._

## `at_lower`

_No discoveries yet._

## `at_upper`

_No discoveries yet._

## `is_free`

_No discoveries yet._

## `is_non_free`

_No discoveries yet._

## `is_bounded`

_No discoveries yet._

## `is_free`

_No discoveries yet._

## `is_free`

_No discoveries yet._

## `is_fixed`

_No discoveries yet._

## `set_bound_core`

_No discoveries yet._

## `restore_bound`

_No discoveries yet._

## `restore_nl_propagated_flag`

_No discoveries yet._

## `set_bound`

_No discoveries yet._

## `enable_cgc_for`

_No discoveries yet._

## `mk_enode`

_No discoveries yet._

## `mk_enode_if_reflect`

_No discoveries yet._

## `add_row_entry`

_No discoveries yet._

## `row_vars`

_No discoveries yet._

## `class scoped_row_vars`

_No discoveries yet._

## `check_app`

_No discoveries yet._

## `internalize_internal_monomial`

_No discoveries yet._

## `internalize_add`

_No discoveries yet._

## `internalize_sub`

_No discoveries yet._

## `internalize_mul_core`

_No discoveries yet._

## `internalize_mul`

_No discoveries yet._

## `internalize_div`

_No discoveries yet._

## `mk_binary_op`

_No discoveries yet._

## `internalize_idiv`

_No discoveries yet._

## `internalize_mod`

_No discoveries yet._

## `internalize_rem`

_No discoveries yet._

## `internalize_to_real`

_No discoveries yet._

## `internalize_to_int`

_No discoveries yet._

## `internalize_is_int`

_No discoveries yet._

## `internalize_numeral`

_No discoveries yet._

## `internalize_numeral`

_No discoveries yet._

## `internalize_term_core`

_No discoveries yet._

## `mk_axiom`

_No discoveries yet._

## `mk_idiv_mod_axioms`

_No discoveries yet._

## `mk_div_axiom`

_No discoveries yet._

## `mk_rem_axiom`

_No discoveries yet._

## `mk_to_int_axiom`

_No discoveries yet._

## `mk_is_int_axiom`

_No discoveries yet._

## `mk_row`

_No discoveries yet._

## `init_row`

_No discoveries yet._

## `collect_vars`

_No discoveries yet._

## `normalize_quasi_base_row`

_No discoveries yet._

## `quasi_base_row2base_row`

_No discoveries yet._

## `normalize_base_row`

_No discoveries yet._

## `mk_clause`

_No discoveries yet._

## `mk_clause`

_No discoveries yet._

## `mk_bound_axioms`

_No discoveries yet._

## `mk_bound_axiom`

_No discoveries yet._

## `flush_bound_axioms`

_No discoveries yet._

## `class compare_atoms`

### `compare_atoms.operator`

_No discoveries yet._

## `default_internalizer`

_No discoveries yet._

## `internalize_atom`

_No discoveries yet._

## `internalize_term`

_No discoveries yet._

## `internalize_eq_eh`

_No discoveries yet._

## `apply_sort_cnstr`

_No discoveries yet._

## `assign_eh`

_No discoveries yet._

## `new_eq_eh`

_No discoveries yet._

## `use_diseqs`

_No discoveries yet._

## `new_diseq_eh`

_No discoveries yet._

## `push_scope_eh`

_No discoveries yet._

## `pop_scope_eh`

_No discoveries yet._

## `relevant_eh`

_No discoveries yet._

## `restart_eh`

_No discoveries yet._

## `init_search_eh`

_No discoveries yet._

## `initialize_value`

_No discoveries yet._

## `final_check_core`

_No discoveries yet._

## `final_check_eh`

_No discoveries yet._

## `can_propagate`

_No discoveries yet._

## `propagate`

_No discoveries yet._

## `propagate_core`

_No discoveries yet._

## `failed`

_No discoveries yet._

## `flush_eh`

_No discoveries yet._

## `reset_eh`

_No discoveries yet._

## `insert_bv2a`

_No discoveries yet._

## `erase_bv2a`

_No discoveries yet._

## `get_bv2a`

_No discoveries yet._

## `add_row`

_No discoveries yet._

## `add_rows`

_No discoveries yet._

## `save_value`

_No discoveries yet._

## `discard_update_trail`

_No discoveries yet._

## `restore_assignment`

_No discoveries yet._

## `update_value_core`

_No discoveries yet._

## `update_value`

_No discoveries yet._

## `set_value`

_No discoveries yet._

## `pivot`

_No discoveries yet._

## `eliminate`

_No discoveries yet._

## `update_and_pivot`

_No discoveries yet._

## `get_num_non_free_dep_vars`

_No discoveries yet._

## `select_blands_pivot_core`

_No discoveries yet._

## `select_pivot_core`

_No discoveries yet._

## `select_pivot`

_No discoveries yet._

## `make_var_feasible`

_No discoveries yet._

## `select_var_to_fix`

_No discoveries yet._

## `select_lg_error_var`

_No discoveries yet._

## `select_greatest_error_var`

_No discoveries yet._

## `select_least_error_var`

_No discoveries yet._

## `select_smallest_var`

_No discoveries yet._

## `make_feasible`

_No discoveries yet._

## `sign_row_conflict`

_No discoveries yet._

## `assert_lower`

_No discoveries yet._

## `assert_upper`

_No discoveries yet._

## `assert_bound`

_No discoveries yet._

## `sign_bound_conflict`

_No discoveries yet._

## `mark_row_for_bound_prop`

_No discoveries yet._

## `add_column_rows_to_touched_rows`

_No discoveries yet._

## `is_row_useful_for_bound_prop`

_No discoveries yet._

## `imply_bound_for_monomial`

_No discoveries yet._

## `imply_bound_for_all_monomials`

_No discoveries yet._

## `explain_bound`

_No discoveries yet._

## `mk_implied_bound`

_No discoveries yet._

## `assign_bound_literal`

_No discoveries yet._

## `propagate_bounds`

_No discoveries yet._

## `get_freedom_interval`

_No discoveries yet._

## `try_to_imply_eq`

_No discoveries yet._

## `random_update`

_No discoveries yet._

## `mutate_assignment`

_No discoveries yet._

## `assume_eqs`

_No discoveries yet._

## `delayed_assume_eqs`

_No discoveries yet._

## `move_non_base_vars_to_bounds`

_No discoveries yet._

## `has_infeasible_int_var`

_No discoveries yet._

## `find_infeasible_int_base_var`

_No discoveries yet._

## `find_bounded_infeasible_int_base_var`

_No discoveries yet._

## `branch_infeasible_int_var`

_No discoveries yet._

## `branch_infeasible_int_equality`

_No discoveries yet._

## `constrain_free_vars`

_No discoveries yet._

## `is_gomory_cut_target`

_No discoveries yet._

## `mk_gomory_cut`

_No discoveries yet._

## `gcd_test`

_No discoveries yet._

## `ext_gcd_test`

_No discoveries yet._

## `gcd_test`

_No discoveries yet._

## `mk_polynomial_ge`

_No discoveries yet._

## `max_min_infeasible_int_vars`

_No discoveries yet._

## `patch_int_infeasible_vars`

_No discoveries yet._

## `fix_non_base_vars`

_No discoveries yet._

## `check_int_feasibility`

_No discoveries yet._

## `is_equal`

_No discoveries yet._

## `fixed_var_eh`

_No discoveries yet._

## `is_offset_row`

_No discoveries yet._

## `propagate_cheap_eq`

_No discoveries yet._

## `propagate_eq_to_core`

_No discoveries yet._

## `is_shared`

_No discoveries yet._

## `set_conflict`

_No discoveries yet._

## `set_conflict`

_No discoveries yet._

## `set_conflict`

_No discoveries yet._

## `collect_fixed_var_justifications`

_No discoveries yet._

## `push_bound_trail`

_No discoveries yet._

## `push_dec_unassigned_atoms_trail`

_No discoveries yet._

## `restore_bounds`

_No discoveries yet._

## `restore_unassigned_atoms`

_No discoveries yet._

## `del_atoms`

_No discoveries yet._

## `del_bounds`

_No discoveries yet._

## `del_vars`

_No discoveries yet._

## `del_row`

_No discoveries yet._

## `all_coeff_int`

_No discoveries yet._

## `move_unconstrained_to_base`

_No discoveries yet._

## `elim_quasi_base_rows`

_No discoveries yet._

## `remove_fixed_vars_from_base`

_No discoveries yet._

## `try_to_minimize_rational_coeffs`

_No discoveries yet._

## `mk_eq_atom`

_No discoveries yet._

## `add_tmp_row`

_No discoveries yet._

## `is_safe_to_leave`

_No discoveries yet._

## `add_tmp_row_entry`

_No discoveries yet._

## `max_min`

_No discoveries yet._

## `has_interface_equality`

_No discoveries yet._

## `max_min`

_No discoveries yet._

## `max_min`

_No discoveries yet._

## `unbounded_gain`

_No discoveries yet._

## `safe_gain`

_No discoveries yet._

## `normalize_gain`

_No discoveries yet._

## `init_gains`

_No discoveries yet._

## `update_gains`

_No discoveries yet._

## `move_to_bound`

_No discoveries yet._

## `pick_var_to_leave`

_No discoveries yet._

## `class var_num_occs_lt`

_No discoveries yet._

## `is_pure_monomial`

_No discoveries yet._

## `is_pure_monomial`

_No discoveries yet._

## `mark_var`

_No discoveries yet._

## `mark_dependents`

_No discoveries yet._

## `get_non_linear_cluster`

_No discoveries yet._

## `analyze_monomial`

_No discoveries yet._

## `decompose_monomial`

_No discoveries yet._

## `display_monomial`

_No discoveries yet._

## `propagate_nl_upward`

_No discoveries yet._

## `propagate_nl_downward`

_No discoveries yet._

## `mk_interval_for`

_No discoveries yet._

## `mk_interval_for`

_No discoveries yet._

## `mul_bound_of`

_No discoveries yet._

## `evaluate_as_interval`

_No discoveries yet._

## `dependency2new_bound`

_No discoveries yet._

## `mk_derived_nl_bound`

_No discoveries yet._

## `update_bounds_using_interval`

_No discoveries yet._

## `update_bounds_using_interval`

_No discoveries yet._

## `propagate_nl_bounds`

_No discoveries yet._

## `propagate_nl_bounds`

_No discoveries yet._

## `is_problematic_non_linear_row`

_No discoveries yet._

## `is_mixed_real_integer`

_No discoveries yet._

## `is_integer`

_No discoveries yet._

## `get_polynomial_info`

_No discoveries yet._

## `p2expr`

_No discoveries yet._

## `power`

_No discoveries yet._

## `mk_nary_mul`

_No discoveries yet._

## `mk_nary_add`

_No discoveries yet._

## `mk_nary_add`

_No discoveries yet._

## `display_nested_form`

_No discoveries yet._

## `get_degree_of`

_No discoveries yet._

## `get_min_degree`

_No discoveries yet._

## `factor`

_No discoveries yet._

## `in_monovariate_monomials`

_No discoveries yet._

## `horner`

_No discoveries yet._

## `cross_nested`

_No discoveries yet._

## `is_cross_nested_consistent`

_No discoveries yet._

## `is_cross_nested_consistent`

_No discoveries yet._

## `is_cross_nested_consistent`

_No discoveries yet._

## `get_value`

_No discoveries yet._

## `check_monomial_assignment`

_No discoveries yet._

## `check_monomial_assignments`

_No discoveries yet._

## `find_nl_var_for_branching`

_No discoveries yet._

## `branch_nl_int_var`

_No discoveries yet._

## `is_monomial_linear`

_No discoveries yet._

## `get_monomial_fixed_var_product`

_No discoveries yet._

## `get_monomial_non_fixed_var`

_No discoveries yet._

## `propagate_linear_monomial`

_No discoveries yet._

## `propagate_linear_monomials`

_No discoveries yet._

## `mk_gb_monomial`

_No discoveries yet._

## `add_monomial_def_to_gb`

_No discoveries yet._

## `add_row_to_gb`

_No discoveries yet._

## `init_grobner_var_order`

_No discoveries yet._

## `init_grobner`

_No discoveries yet._

## `mk_interval_for`

_No discoveries yet._

## `set_conflict`

_No discoveries yet._

## `is_inconsistent`

_No discoveries yet._

## `is_inconsistent`

_No discoveries yet._

## `is_inconsistent2`

_No discoveries yet._

## `monomial2expr`

_No discoveries yet._

## `internalize_gb_eq`

_No discoveries yet._

## `compute_grobner`

_No discoveries yet._

## `compute_basis_loop`

_No discoveries yet._

## `compute_basis`

_No discoveries yet._

## `update_statistics`

_No discoveries yet._

## `set_gb_exhausted`

_No discoveries yet._

## `get_gb_eqs_and_look_for_conflict`

_No discoveries yet._

## `scan_for_linear`

_No discoveries yet._

## `try_to_modify_eqs`

_No discoveries yet._

## `max_min_nl_vars`

_No discoveries yet._

## `process_non_linear`

_No discoveries yet._

## `mk_fresh`

_No discoveries yet._

## `setup`

_No discoveries yet._

## `get_phase`

_No discoveries yet._

## `update_epsilon`

_No discoveries yet._

## `compute_epsilon`

_No discoveries yet._

## `refine_epsilon`

_No discoveries yet._

## `init_model`

_No discoveries yet._

## `mk_value`

_No discoveries yet._

## `get_value`

_No discoveries yet._

## `include_func_interp`

_No discoveries yet._

## `get_lower`

_No discoveries yet._

## `get_upper`

_No discoveries yet._

## `get_lower`

_No discoveries yet._

## `get_upper`

_No discoveries yet._

## `to_expr`

_No discoveries yet._

## `mk_ge`

_No discoveries yet._

## `add_objective`

_No discoveries yet._

## `enable_record_conflict`

_No discoveries yet._

## `record_conflict`

_No discoveries yet._

## `mk_gt`

_No discoveries yet._

## `get_theory_vars`

_No discoveries yet._

## `collect_statistics`

_No discoveries yet._

## `display`

_No discoveries yet._

## `display_row`

_No discoveries yet._

## `display_row`

_No discoveries yet._

## `display_rows`

_No discoveries yet._

## `display_row_info`

_No discoveries yet._

## `display_row_info`

_No discoveries yet._

## `is_one_minus_one_row`

_No discoveries yet._

## `display_row_shape`

_No discoveries yet._

## `display_rows_shape`

_No discoveries yet._

## `display_rows_stats`

_No discoveries yet._

## `display_rows_bignums`

_No discoveries yet._

## `display_simplified_row`

_No discoveries yet._

## `display_var`

_No discoveries yet._

## `display_vars`

_No discoveries yet._

## `display_bound`

_No discoveries yet._

## `display_atoms`

_No discoveries yet._

## `display_asserted_atoms`

_No discoveries yet._

## `display_atom`

_No discoveries yet._

## `display_bounds_in_smtlib`

_No discoveries yet._

## `display_bounds_in_smtlib`

_No discoveries yet._

## `display_nl_monomials`

_No discoveries yet._

## `display_coeff_exprs`

_No discoveries yet._

## `display_interval`

_No discoveries yet._

## `display_deps`

_No discoveries yet._

## `check_vector_sizes`

_No discoveries yet._

## `check_null_var_pos`

_No discoveries yet._

## `has_var_kind`

_No discoveries yet._

## `wf_row`

_No discoveries yet._

## `wf_rows`

_No discoveries yet._

## `wf_column`

_No discoveries yet._

## `wf_columns`

_No discoveries yet._

## `valid_assignment`

_No discoveries yet._

## `valid_row_assignment`

_No discoveries yet._

## `valid_row_assignment`

_No discoveries yet._

## `satisfy_bounds`

_No discoveries yet._

## `satisfy_integrality`

_No discoveries yet._

## `class mi_ext`

### `mi_ext.fractional_part`

_No discoveries yet._

### `mi_ext.fractional_part`

_No discoveries yet._

### `mi_ext.mk_inf_numeral`

_No discoveries yet._

### `mi_ext.inf_numeral`

_No discoveries yet._

### `mi_ext.is_infinite`

_No discoveries yet._

## `class i_ext`

### `i_ext.fractional_part`

_No discoveries yet._

### `i_ext.mk_inf_numeral`

_No discoveries yet._

### `i_ext.inf_numeral`

_No discoveries yet._

### `i_ext.is_infinite`

_No discoveries yet._

## `class si_ext`

### `si_ext.fractional_part`

_No discoveries yet._

### `si_ext.mk_inf_numeral`

_No discoveries yet._

### `si_ext.inf_numeral`

_No discoveries yet._

### `si_ext.is_infinite`

_No discoveries yet._

## `class smi_ext`

### `smi_ext.fractional_part`

_No discoveries yet._

### `smi_ext.numeral`

_No discoveries yet._

### `smi_ext.fractional_part`

_No discoveries yet._

### `smi_ext.numeral`

_No discoveries yet._

### `smi_ext.mk_inf_numeral`

_No discoveries yet._

### `smi_ext.inf_numeral`

_No discoveries yet._

### `smi_ext.is_infinite`

_No discoveries yet._

## `class inf_ext`

### `inf_ext.fractional_part`

_No discoveries yet._

### `inf_ext.fractional_part`

_No discoveries yet._

### `inf_ext.mk_inf_numeral`

_No discoveries yet._

### `inf_ext.inf_numeral`

_No discoveries yet._

### `inf_ext.is_infinite`

_No discoveries yet._

## Cross-References

_No cross-cutting discoveries yet._
