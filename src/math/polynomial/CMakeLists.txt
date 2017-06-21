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
  PYG_FILES
    algebraic_params.pyg
  EXTRA_REGISTER_MODULE_HEADERS
    polynomial.h
)

