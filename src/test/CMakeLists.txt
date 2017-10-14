add_subdirectory(fuzzing)
################################################################################
# z3-test executable
################################################################################
set(z3_test_deps api fuzzing simplex)
z3_expand_dependencies(z3_test_expanded_deps ${z3_test_deps})
set (z3_test_extra_object_files "")
foreach (component ${z3_test_expanded_deps})
  list(APPEND z3_test_extra_object_files $<TARGET_OBJECTS:${component}>)
endforeach()
add_executable(test-z3
  EXCLUDE_FROM_ALL
  algebraic.cpp
  api_bug.cpp
  api.cpp
  arith_rewriter.cpp
  arith_simplifier_plugin.cpp
  ast.cpp
  bdd.cpp
  bit_blaster.cpp
  bits.cpp
  bit_vector.cpp
  buffer.cpp
  chashtable.cpp
  check_assumptions.cpp
  cnf_backbones.cpp
  datalog_parser.cpp
  ddnf.cpp
  diff_logic.cpp
  dl_context.cpp
  dl_product_relation.cpp
  dl_query.cpp
  dl_relation.cpp
  dl_table.cpp
  dl_util.cpp
  doc.cpp
  escaped.cpp
  ex.cpp
  expr_rand.cpp
  expr_substitution.cpp
  ext_numeral.cpp
  f2n.cpp
  factor_rewriter.cpp
  fixed_bit_vector.cpp
  for_each_file.cpp
  get_consequences.cpp
  get_implied_equalities.cpp
  "${CMAKE_CURRENT_BINARY_DIR}/gparams_register_modules.cpp"
  hashtable.cpp
  heap.cpp
  heap_trie.cpp
  hilbert_basis.cpp
  horn_subsume_model_converter.cpp
  hwf.cpp
  inf_rational.cpp
  "${CMAKE_CURRENT_BINARY_DIR}/install_tactic.cpp"
  interval.cpp
  karr.cpp
  list.cpp
  main.cpp
  map.cpp
  matcher.cpp
  "${CMAKE_CURRENT_BINARY_DIR}/mem_initializer.cpp"
  memory.cpp
  model2expr.cpp
  model_based_opt.cpp
  model_evaluator.cpp
  model_retrieval.cpp
  mpbq.cpp
  mpf.cpp
  mpff.cpp
  mpfx.cpp
  mpq.cpp
  mpz.cpp
  nlarith_util.cpp
  nlsat.cpp
  no_overflow.cpp
  object_allocator.cpp
  old_interval.cpp
  optional.cpp
  parray.cpp
  pb2bv.cpp
  pdr.cpp
  permutation.cpp
  polynomial.cpp
  polynorm.cpp
  prime_generator.cpp
  proof_checker.cpp
  qe_arith.cpp
  quant_elim.cpp
  quant_solve.cpp
  random.cpp
  rational.cpp
  rcf.cpp
  region.cpp
  sat_local_search.cpp
  sat_lookahead.cpp
  sat_user_scope.cpp
  simple_parser.cpp
  simplex.cpp
  simplifier.cpp
  small_object_allocator.cpp
  smt2print_parse.cpp
  smt_context.cpp
  sorting_network.cpp
  stack.cpp
  string_buffer.cpp
  substitution.cpp
  symbol.cpp
  symbol_table.cpp
  tbv.cpp
  theory_dl.cpp
  theory_pb.cpp
  timeout.cpp
  total_order.cpp
  trigo.cpp
  udoc_relation.cpp
  uint_set.cpp
  upolynomial.cpp
  var_subst.cpp
  vector.cpp
  ${z3_test_extra_object_files}
)
z3_add_install_tactic_rule(${z3_test_deps})
z3_add_memory_initializer_rule(${z3_test_deps})
z3_add_gparams_register_modules_rule(${z3_test_deps})
target_compile_definitions(test-z3 PRIVATE ${Z3_COMPONENT_CXX_DEFINES})
target_compile_options(test-z3 PRIVATE ${Z3_COMPONENT_CXX_FLAGS})
target_link_libraries(test-z3 PRIVATE ${Z3_DEPENDENT_LIBS})
target_include_directories(test-z3 PRIVATE ${Z3_COMPONENT_EXTRA_INCLUDE_DIRS})
z3_append_linker_flag_list_to_target(test-z3 ${Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS})
z3_add_component_dependencies_to_target(test-z3 ${z3_test_expanded_deps})



