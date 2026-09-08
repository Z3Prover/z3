z3_add_component(polynomial
  SOURCES
    algebraic_numbers.cpp
    polynomial_cache.cpp
    polynomial.cpp
    rpolynomial.cpp
    sexpr2upolynomial.cpp
    upolynomial.cpp
    upolynomial_factorization.cpp
  COMPONENT_DEPENDENCIES
    util
  EXTRA_REGISTER_MODULE_HEADERS
    polynomial.h
    algebraic_params.hpp
)

