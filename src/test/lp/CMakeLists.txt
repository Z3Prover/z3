add_executable(lp_tst
EXCLUDE_FROM_ALL
lp_main.cpp lp.cpp nla_solver_test.cpp)
target_link_libraries(lp_tst PRIVATE
  z3_common util polynomial nlsat lp grobner simplex interval dd ast)
