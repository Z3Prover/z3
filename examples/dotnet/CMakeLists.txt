find_package(Dotnet REQUIRED)

if(TARGET_ARCHITECTURE STREQUAL "i686")
    set(Z3_DOTNET_PLATFORM "x86")
else()
    set(Z3_DOTNET_PLATFORM "AnyCPU")
endif()

set(z3_dotnet_project "${CMAKE_CURRENT_BINARY_DIR}/dotnet.csproj")
set(z3_dotnet_program "${CMAKE_CURRENT_BINARY_DIR}/Program.cs")
add_custom_command(
    OUTPUT "${z3_dotnet_project}" "${z3_dotnet_program}"
    COMMAND "${CMAKE_COMMAND}" -E copy_if_different
        "${CMAKE_CURRENT_SOURCE_DIR}/dotnet.csproj" "${z3_dotnet_project}"
    COMMAND "${CMAKE_COMMAND}" -E copy_if_different
        "${CMAKE_CURRENT_SOURCE_DIR}/Program.cs" "${z3_dotnet_program}"
    DEPENDS
        "${CMAKE_CURRENT_SOURCE_DIR}/dotnet.csproj"
        "${CMAKE_CURRENT_SOURCE_DIR}/Program.cs"
    VERBATIM)

ADD_DOTNET("${z3_dotnet_project}"
    PLATFORM ${Z3_DOTNET_PLATFORM}
    NETCOREAPP
    CUSTOM_BUILDPROPS "<Z3_VERSION>${Z3_VERSION_MAJOR}.${Z3_VERSION_MINOR}.${Z3_VERSION_PATCH}</Z3_VERSION>"
    DEPENDS Microsoft.Z3
    SOURCES "${z3_dotnet_project}" "${z3_dotnet_program}")

if(UNIX AND NOT APPLE)
    set(z3_dotnet_native_lib ${PROJECT_BINARY_DIR}/libz3.so)
    set(z3_dotnet_test_manual_copy_deps
        ${PROJECT_BINARY_DIR}/Microsoft.Z3/netstandard2.0/Microsoft.Z3.dll 
        ${z3_dotnet_native_lib}
        )

    add_custom_target(
        z3_dotnet_test_manual_copy_assembly_hack ALL
        COMMAND ${CMAKE_COMMAND} -E copy ${z3_dotnet_test_manual_copy_deps} ${PROJECT_BINARY_DIR}/dotnet/net8.0/
        # hack the libz3 entry in deps so it's easy enough for dotnet to reach it...
        COMMAND sed \"s/runtimes\\/.*libz3\\.so/libz3.so/\" -i ${PROJECT_BINARY_DIR}/dotnet/net8.0/dotnet.deps.json
        )

    add_dependencies(z3_dotnet_test_manual_copy_assembly_hack BUILD_dotnet)
endif()
