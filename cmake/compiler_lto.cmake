option(LINK_TIME_OPTIMIZATION "Use link time optimiziation" OFF)

if (LINK_TIME_OPTIMIZATION)
  message(STATUS "LTO enabled")
  set(build_types_with_lto "RELEASE" "RELWITHDEBINFO")
  if (DEFINED CMAKE_CONFIGURATION_TYPES)
    # Multi configuration generator
    message(STATUS "Note LTO is only enabled for the following configurations: ${build_types_with_lto}")
  else()
    # Single configuration generator
    string(TOUPPER "${CMAKE_BUILD_TYPE}" _build_type_upper)
    list(FIND build_types_with_lto "${_build_type_upper}" _index)
    if ("${_index}" EQUAL -1)
      message(FATAL_ERROR "Configuration ${CMAKE_BUILD_TYPE} does not support LTO."
        "You should set LINK_TIME_OPTIMIZATION to OFF.")
    endif()
  endif()

  set(_lto_compiler_flag "")
  set(_lto_linker_flag "")
  if (("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang") OR
      ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
      set(_lto_compiler_flag "-flto")
      set(_lto_linker_flag "-flto")
  elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
    set(_lto_compiler_flag "/GL")
    set(_lto_linker_flag "/LTCG")
  else()
    message(FATAL_ERROR "Can't enable LTO for compiler \"${CMAKE_CXX_COMPILER_ID}\"."
      "You should set LINK_TIME_OPTIMIZATION to OFF.")
  endif()
  CHECK_CXX_COMPILER_FLAG("${_lto_compiler_flag}" HAS_LTO)
  if (NOT HAS_LTO)
    message(FATAL_ERROR "Compiler does not support LTO")
  endif()

  foreach (_config ${build_types_with_lto})
    # Set flags compiler and linker flags globally rather than using
    # `Z3_COMPONENT_CXX_FLAGS` and `Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS`
    # respectively.  We need per configuration compiler and linker flags. The
    # `LINK_FLAGS` property (which we populate with
    # `Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS`) doesn't seem to support generator
    # expressions so we can't do `$<$<CONFIG:Release>:${_lto_linker_flag}>`.
    set(CMAKE_CXX_FLAGS_${_config} "${CMAKE_CXX_FLAGS_${_config}} ${_lto_compiler_flag}")
    set(CMAKE_EXE_LINKER_FLAGS_${_config} "${CMAKE_EXE_LINKER_FLAGS_${_config}} ${_lto_linker_flag}")
    set(CMAKE_SHARED_LINKER_FLAGS_${_config} "${CMAKE_SHARED_LINKER_FLAGS_${_config}} ${_lto_linker_flag}")
    set(CMAKE_STATIC_LINKER_FLAGS_${_config} "${CMAKE_STATIC_LINKER_FLAGS_${_config}} ${_lto_linker_flag}")
  endforeach()
else()
  message(STATUS "LTO disabled")
endif()
