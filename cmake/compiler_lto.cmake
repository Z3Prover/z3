option(Z3_LINK_TIME_OPTIMIZATION "Use link time optimiziation" OFF)

if (Z3_LINK_TIME_OPTIMIZATION)
  message(STATUS "LTO enabled")
  set(build_types_with_lto RELEASE RELWITHDEBINFO)
  if (Z3_MULTI_CONFIG)
    # Multi configuration generator
    message(STATUS "Note LTO is only enabled for the following configurations: ${build_types_with_lto}")
  else()
    # Single configuration generator
    string(TOUPPER "${CMAKE_BUILD_TYPE}" _build_type_upper)
    list(FIND build_types_with_lto "${_build_type_upper}" _index)
    if ("${_index}" EQUAL -1)
      message(FATAL_ERROR "Configuration ${CMAKE_BUILD_TYPE} does not support LTO."
        "You should set Z3_LINK_TIME_OPTIMIZATION to OFF.")
    endif()
  endif()

  include(CheckIPOSupported)
  check_ipo_supported(RESULT _ipo_supported OUTPUT _ipo_error LANGUAGES CXX)
  if (NOT _ipo_supported)
    message(FATAL_ERROR "Compiler does not support LTO: ${_ipo_error}")
  endif()

  foreach (_config IN LISTS build_types_with_lto)
    set(CMAKE_INTERPROCEDURAL_OPTIMIZATION_${_config} ON)
  endforeach()

else()
  message(STATUS "LTO disabled")
endif()
