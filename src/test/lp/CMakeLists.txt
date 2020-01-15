add_executable(lp_tst
EXCLUDE_FROM_ALL
lp_main.cpp lp.cpp nla_solver_test.cpp $<TARGET_OBJECTS:util>
$<TARGET_OBJECTS:polynomial> $<TARGET_OBJECTS:nlsat>
$<TARGET_OBJECTS:lp> $<TARGET_OBJECTS:grobner>  $<TARGET_OBJECTS:simplex>
$<TARGET_OBJECTS:interval> $<TARGET_OBJECTS:dd> $<TARGET_OBJECTS:ast>)
target_compile_definitions(lp_tst PRIVATE ${Z3_COMPONENT_CXX_DEFINES})
target_compile_options(lp_tst PRIVATE ${Z3_COMPONENT_CXX_FLAGS})
target_include_directories(lp_tst PRIVATE ${Z3_COMPONENT_EXTRA_INCLUDE_DIRS})
target_link_libraries(lp_tst PRIVATE ${Z3_DEPENDENT_LIBS})
z3_append_linker_flag_list_to_target(lp_tst ${Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS})
