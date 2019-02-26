if (EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/z3_version.h")
  message(FATAL_ERROR "\"${CMAKE_CURRENT_SOURCE_DIR}/z3_version.h\""
          ${z3_polluted_tree_msg}
  )
endif()

set(Z3_FULL_VERSION "\"${Z3_FULL_VERSION_STR}\"")
configure_file(z3_version.h.cmake.in ${CMAKE_CURRENT_BINARY_DIR}/z3_version.h)


z3_add_component(util
  SOURCES
    approx_nat.cpp
    approx_set.cpp
    bit_util.cpp
    bit_vector.cpp
    cmd_context_types.cpp
    common_msgs.cpp
    cooperate.cpp
    debug.cpp
    env_params.cpp
    fixed_bit_vector.cpp
    gparams.cpp
    hash.cpp
    hwf.cpp
    inf_int_rational.cpp
    inf_rational.cpp
    inf_s_integer.cpp
    lbool.cpp
    luby.cpp
    memory_manager.cpp
    min_cut.cpp
    mpbq.cpp
    mpf.cpp
    mpff.cpp
    mpfx.cpp
    mpn.cpp
    mpq.cpp
    mpq_inf.cpp
    mpz.cpp
    page.cpp
    params.cpp
    permutation.cpp
    prime_generator.cpp
    rational.cpp
    region.cpp
    rlimit.cpp
    scoped_ctrl_c.cpp
    scoped_timer.cpp
    sexpr.cpp
    s_integer.cpp
    small_object_allocator.cpp
    smt2_util.cpp
    stack.cpp
    statistics.cpp
    symbol.cpp
    timeit.cpp
    timeout.cpp
    trace.cpp
    util.cpp
    warning.cpp
    z3_exception.cpp
  EXTRA_REGISTER_MODULE_HEADERS
    env_params.h
  MEMORY_INIT_FINALIZER_HEADERS
    debug.h
    gparams.h
    prime_generator.h
    rational.h
    symbol.h
    trace.h
)
