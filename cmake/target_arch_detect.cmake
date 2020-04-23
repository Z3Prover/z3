###############################################################################
# Target detection
#
# We abuse the compiler preprocessor to work out what target the compiler is
# building for. The nice thing about this approach is that we'll detect the
# right target even if we are using a cross compiler.
###############################################################################
function(detect_target_architecture OUTPUT_VAR)
  try_run(run_result
    compile_result
    "${PROJECT_BINARY_DIR}"
    "${PROJECT_SOURCE_DIR}/cmake/target_arch_detect.cpp"
    COMPILE_OUTPUT_VARIABLE compiler_output
  )
  if (compile_result)
    message(FATAL_ERROR "Expected compile to fail")
  endif()
  string(REGEX MATCH "CMAKE_TARGET_ARCH_([a-zA-Z0-9_]+)" arch "${compiler_output}")
  # Strip out prefix
  string(REPLACE "CMAKE_TARGET_ARCH_" "" arch "${arch}")
  set(${OUTPUT_VAR} "${arch}" PARENT_SCOPE)
endfunction()
