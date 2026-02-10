find_package(JlCxx REQUIRED)

# Check for Windows MSVC + MinGW library compatibility issues
if(WIN32 AND CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
    # Get the JlCxx library path to check its format
    get_target_property(JLCXX_LIB_PATH JlCxx::cxxwrap_julia IMPORTED_LOCATION)
    if(NOT JLCXX_LIB_PATH)
        get_target_property(JLCXX_LIB_PATH JlCxx::cxxwrap_julia IMPORTED_LOCATION_RELEASE)
    endif()
    if(NOT JLCXX_LIB_PATH)
        get_target_property(JLCXX_LIB_PATH JlCxx::cxxwrap_julia IMPORTED_IMPLIB)
    endif()
    if(NOT JLCXX_LIB_PATH)
        get_target_property(JLCXX_LIB_PATH JlCxx::cxxwrap_julia IMPORTED_IMPLIB_RELEASE)
    endif()
    
    if(JLCXX_LIB_PATH AND JLCXX_LIB_PATH MATCHES "\\.dll\\.a$")
        message(FATAL_ERROR 
            "Julia bindings build error: Incompatible CxxWrap library format detected.\n"
            "The found libcxxwrap_julia library (${JLCXX_LIB_PATH}) is a MinGW import library (.dll.a), "
            "but Z3 is being built with MSVC which requires .lib format.\n\n"
            "Solutions:\n"
            "1. Use MinGW/GCC instead of MSVC to build Z3\n"
            "2. Install a MSVC-compatible version of CxxWrap\n"
            "3. Disable Julia bindings with -DZ3_BUILD_JULIA_BINDINGS=OFF\n\n"
            "For more information, see: https://github.com/JuliaInterop/CxxWrap.jl#compiling-the-c-code")
    endif()
endif()

add_library(z3jl SHARED z3jl.cpp)
target_link_libraries(z3jl PRIVATE JlCxx::cxxwrap_julia libz3)
target_include_directories(z3jl PRIVATE
    "${PROJECT_SOURCE_DIR}/src/api"
    "${PROJECT_BINARY_DIR}/src/api"
    "${PROJECT_SOURCE_DIR}/src/api/c++"
)
# Add header padding for macOS to allow install_name_tool to modify the dylib
if (CMAKE_SYSTEM_NAME STREQUAL "Darwin")
  target_link_options(z3jl PRIVATE "-Wl,-headerpad_max_install_names")
endif()

# On macOS, add headerpad for install_name_tool compatibility
if(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
  target_link_options(z3jl PRIVATE "-Wl,-headerpad_max_install_names")
endif()

option(Z3_INSTALL_JULIA_BINDINGS "Install Julia bindings when invoking install target" ON)
if(Z3_INSTALL_JULIA_BINDINGS)
    install(TARGETS z3jl
        LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
        ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}"
        RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}"
    )
endif()