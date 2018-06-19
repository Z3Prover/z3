# Tries to find a working .NET tool chain
#
# Once complete this will define
# DOTNET_TOOLCHAIN_FOUND  : BOOL : System has a .NET toolchain
# DOTNET_CSC_EXECUTABLE - STRING : Path to C# compiler
# DOTNET_GACUTIL_EXECUTABLE - STRING : Path to gacutil
# DOTNET_TOOLCHAIN_IS_MONO : BOOL : True if detected .NET toolchain is Mono
# DOTNET_TOOLCHAIN_IS_WINDOWS : BOOL : True if detected .NET toolchain is native Windows
include(FindPackageHandleStandardArgs)

find_program(
  DOTNET_CSC_EXECUTABLE
  NAMES "csc.exe" "mcs" "dmcs"
)
message(STATUS "DOTNET_CSC_EXECUTABLE: \"${DOTNET_CSC_EXECUTABLE}\"")

find_program(
  DOTNET_GACUTIL_EXECUTABLE
  NAMES "gacutil.exe" "gacutil"
)
message(STATUS "DOTNET_GACUTIL_EXECUTABLE: \"${DOTNET_GACUTIL_EXECUTABLE}\"")

# Try to determine the tool chain vendor
set(DOTNET_DETERMINED_VENDOR FALSE)
if (DOTNET_CSC_EXECUTABLE)
  execute_process(COMMAND "${DOTNET_CSC_EXECUTABLE}" "/help"
    RESULT_VARIABLE CSC_EXIT_CODE
    OUTPUT_VARIABLE CSC_STD_OUT
  )
  if (${CSC_EXIT_CODE} EQUAL 0)
    if ("${CSC_STD_OUT}" MATCHES "^Mono[ ]+C#")
      set(DOTNET_DETERMINED_VENDOR TRUE)
      set(DOTNET_TOOLCHAIN_IS_MONO TRUE)
      set(DOTNET_TOOLCHAIN_IS_WINDOWS FALSE)
      message(STATUS ".NET toolchain is Mono")
    elseif ("${CSC_STD_OUT}" MATCHES "^Turbo[ ]+C#")
      set(DOTNET_DETERMINED_VENDOR TRUE)
      set(DOTNET_TOOLCHAIN_IS_MONO TRUE)
      set(DOTNET_TOOLCHAIN_IS_WINDOWS FALSE)
      message(STATUS ".NET toolchain is Mono")
    elseif ("${CSC_STD_OUT}" MATCHES "^Microsoft.+Visual[ ]+C#")
      set(DOTNET_DETERMINED_VENDOR TRUE)
      set(DOTNET_TOOLCHAIN_IS_MONO FALSE)
      set(DOTNET_TOOLCHAIN_IS_WINDOWS TRUE)
      message(STATUS ".NET toolchain is Windows native")
    else()
      message(STATUS ".NET toolchain is unknown: ${CSC_STD_OUT}")
    endif()
  endif()
endif()

# TODO: Check C# compiler works

find_package_handle_standard_args(DotNetToolChain DEFAULT_MSG
  DOTNET_CSC_EXECUTABLE
  DOTNET_GACUTIL_EXECUTABLE
  DOTNET_DETERMINED_VENDOR
)
