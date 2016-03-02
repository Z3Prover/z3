z3_add_component(polynomial
  SOURCES
    algebraic_numbers.cpp
    polynomial_cache.cpp
    polynomial.cpp
    polynomial_factorization.cpp
    rpolynomial.cpp
    sexpr2upolynomial.cpp
    upolynomial.cpp
    upolynomial_factorization.cpp
  COMPONENT_DEPENDENCIES
    util
  PYG_FILES
    algebraic_params.pyg
)

