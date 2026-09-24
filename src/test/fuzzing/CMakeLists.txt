add_library(fuzzing OBJECT expr_delta.cpp expr_rand.cpp)
set_target_properties(fuzzing PROPERTIES
    POSITION_INDEPENDENT_CODE ON
    LINK_LIBRARIES_ONLY_TARGETS ON
    CXX_VISIBILITY_PRESET hidden
    VISIBILITY_INLINES_HIDDEN ON
)

target_link_libraries(fuzzing PRIVATE ast z3_common)
set_property(TARGET fuzzing APPEND PROPERTY INTERFACE_LINK_LIBRARIES_DIRECT ast)
