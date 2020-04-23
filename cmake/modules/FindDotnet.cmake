#.rst
# FindDotnet
# ----------
# 
# Find DotNet executable, and initialize functions for adding dotnet projects.
# 
# Results are reported in the following variables::
# 
#   DOTNET_FOUND          - True if dotnet executable is found
#   DOTNET_EXE            - Dotnet executable
#   DOTNET_VERSION        - Dotnet version as reported by dotnet executable
#   NUGET_EXE             - Nuget executable (WIN32 only)
#   NUGET_CACHE_PATH      - Nuget package cache path
# 
# The following functions are defined to add dotnet/msbuild projects:
# 
# ADD_DOTNET -- add a project to be built by dotnet.
# 
# ```
# ADD_DOTNET(<project_file> [RELEASE|DEBUG] [X86|X64|ANYCPU] [NETCOREAPP]
#            [CONFIG configuration]
#            [PLATFORM platform]
#            [PACKAGE output_nuget_packages... ]
#            [VERSION nuget_package_version]
#            [DEPENDS depend_nuget_packages... ]
#            [OUTPUT_PATH output_path relative to cmake binary output dir]
#            [CUSTOM_BUILDPROPS <CustomProp>value</CustomProp>....]
#            [SOURCES additional_file_dependencies... ]
#            [ARGUMENTS additional_build_args...]
#            [PACK_ARGUMENTS additional_pack_args...])
# ```
# 
# RUN_DOTNET -- Run a project with `dotnet run`. The `OUTPUT` argument represents artifacts 
#               produced by running the .NET program, and can be consumed from other build steps.
# 
# ```
# RUN_DOTNET(<project_file> [RELEASE|DEBUG] [X86|X64|ANYCPU] [NETCOREAPP]
#            [ARGUMENTS program_args...]
#            [OUTPUT outputs...]
#            [CONFIG configuration]
#            [PLATFORM platform]
#            [DEPENDS depend_nuget_packages... ]
#            [OUTPUT_PATH output_path relative to cmake binary output dir]
#            [CUSTOM_BUILDPROPS <CustomProp>value</CustomProp>....]
#            [SOURCES additional_file_dependencies... ])
# ```
# 
# ADD_MSBUILD -- add a project to be built by msbuild. Windows-only. When building in Unix systems, msbuild targets are skipped.
# 
# ```
# ADD_MSBUILD(<project_file> [RELEASE|DEBUG] [X86|X64|ANYCPU] [NETCOREAPP]
#            [CONFIG configuration]
#            [PLATFORM platform]
#            [PACKAGE output_nuget_packages... ]
#            [DEPENDS depend_nuget_packages... ]
#            [CUSTOM_BUILDPROPS <CustomProp>value</CustomProp>....]
#            [SOURCES additional_file_dependencies... ]
#            [ARGUMENTS additional_build_args...]
#            [PACK_ARGUMENTS additional_pack_args...])
# ```
#
# SMOKETEST_DOTNET -- add a dotnet smoke test project to the build. The project will be run during a build,
# and if the program fails to build or run, the build fails. Currently only .NET Core App framework is supported.
# Multiple smoke tests will be run one-by-one to avoid global resource conflicts.
#
# SMOKETEST_DOTNET(<project_file> [RELEASE|DEBUG] [X86|X64|ANYCPU] [NETCOREAPP]
#                 [ARGUMENTS program_args...]
#                 [CONFIG configuration]
#                 [PLATFORM platform]
#                 [DEPENDS depend_nuget_packages... ]
#                 [OUTPUT_PATH output_path relative to cmake binary output dir]
#                 [CUSTOM_BUILDPROPS <CustomProp>value</CustomProp>....]
#                 [SOURCES additional_file_dependencies... ])
# 
# For all the above functions, `RELEASE|DEBUG` overrides `CONFIG`, `X86|X64|ANYCPU` overrides PLATFORM.
# For Unix systems, the target framework defaults to `netstandard2.0`, unless `NETCOREAPP` is specified.
# For Windows, the project is built as-is, allowing multi-targeting.
#
#
# DOTNET_REGISTER_LOCAL_REPOSITORY -- register a local NuGet package repository.
# 
# ```
# DOTNET_REGISTER_LOCAL_REPOSITORY(repo_name repo_path)
# ```
#
# TEST_DOTNET -- add a dotnet test project to ctest. The project will be run with `dotnet test`,
# and trx test reports will be generated in the build directory. For Windows, all target frameworks
# are tested against. For other platforms, only .NET Core App is tested against.
# Test failures will not fail the build.
# Tests are only run with `ctest -C <config>`, not with `cmake --build ...`
#
# ```
# TEST_DOTNET(<project_file>
#             [ARGUMENTS additional_dotnet_test_args...]
#             [OUTPUT_PATH output_path relative to cmake binary output dir])
# ```
# 
# GEN_DOTNET_PROPS -- Generates a Directory.Build.props file. The created file is populated with MSBuild properties:
#  - DOTNET_PACKAGE_VERSION: a version string that can be referenced in the actual project file as $(DOTNET_PACKAGE_VERSION).
#    The version string value can be set with PACKAGE_VERSION argument, and defaults to '1.0.0'.
#  - XPLAT_LIB_DIR: points to the cmake build root directory.
#  - OutputPath: Points to the cmake binary directory (overridden by OUTPUT_PATH, relatively). Therefore, projects built without cmake will consistently output
#    to the cmake build directory.
#  - Custom properties can be injected with XML_INJECT argument, which injects an arbitrary string into the project XML file.
#
# ```
# GEN_DOTNET_PROPS(<target_props_file>
#                  [PACKAGE_VERSION version]
#                  [XML_INJECT xml_injection])
# ```
# 
# Require 3.5 for batch copy multiple files

cmake_minimum_required(VERSION 3.5.0)

IF(DOTNET_FOUND)
    RETURN()
ENDIF()

SET(NUGET_CACHE_PATH "~/.nuget/packages")
FIND_PROGRAM(DOTNET_EXE dotnet)
SET(DOTNET_MODULE_DIR ${CMAKE_CURRENT_LIST_DIR})

IF(NOT DOTNET_EXE)
    SET(DOTNET_FOUND FALSE)
    IF(Dotnet_FIND_REQUIRED)
        MESSAGE(SEND_ERROR "Command 'dotnet' is not found.")
    ENDIF()
    RETURN()
ENDIF()

EXECUTE_PROCESS(
    COMMAND ${DOTNET_EXE} --version
    OUTPUT_VARIABLE DOTNET_VERSION
    OUTPUT_STRIP_TRAILING_WHITESPACE
)

IF(WIN32)
   FIND_PROGRAM(NUGET_EXE nuget PATHS ${PROJECT_BINARY_DIR}/tools)
   IF(NUGET_EXE)
       MESSAGE("-- Found nuget: ${NUGET_EXE}")
   ELSE()
        SET(NUGET_EXE ${PROJECT_BINARY_DIR}/tools/nuget.exe)
        MESSAGE("-- Downloading nuget...")
        FILE(DOWNLOAD https://dist.nuget.org/win-x86-commandline/latest/nuget.exe ${NUGET_EXE})
        MESSAGE("nuget.exe downloaded and saved to ${NUGET_EXE}")
   ENDIF()
ENDIF()

FUNCTION(DOTNET_REGISTER_LOCAL_REPOSITORY repo_name repo_path)
	MESSAGE("-- Registering NuGet local repository '${repo_name}' at '${repo_path}'.")
    GET_FILENAME_COMPONENT(repo_path ${repo_path} ABSOLUTE)
    IF(WIN32)
        STRING(REPLACE "/" "\\" repo_path ${repo_path})
        EXECUTE_PROCESS(COMMAND ${NUGET_EXE} sources list OUTPUT_QUIET)
        EXECUTE_PROCESS(COMMAND ${NUGET_EXE} sources Remove -Name "${repo_name}" OUTPUT_QUIET ERROR_QUIET)
        EXECUTE_PROCESS(COMMAND ${NUGET_EXE} sources Add -Name "${repo_name}" -Source "${repo_path}")
    ELSE()
        GET_FILENAME_COMPONENT(nuget_config ~/.nuget/NuGet/NuGet.Config ABSOLUTE)
        EXECUTE_PROCESS(COMMAND ${DOTNET_EXE} nuget locals all --list OUTPUT_QUIET)
        EXECUTE_PROCESS(COMMAND sed -i "#${repo_name}#d" "${nuget_config}") 
        EXECUTE_PROCESS(COMMAND sed -i "s#</packageSources>#  <add key=\\\"${repo_name}\\\" value=\\\"${repo_path}\\\" />\\n  </packageSources>#g" "${nuget_config}")
    ENDIF()
ENDFUNCTION()

FUNCTION(DOTNET_GET_DEPS _DN_PROJECT arguments)
    CMAKE_PARSE_ARGUMENTS(
        # prefix
        _DN 
        # options (flags)
        "RELEASE;DEBUG;X86;X64;ANYCPU;NETCOREAPP" 
        # oneValueArgs
        "CONFIG;PLATFORM;VERSION;OUTPUT_PATH" 
        # multiValueArgs
        "PACKAGE;DEPENDS;ARGUMENTS;PACK_ARGUMENTS;OUTPUT;SOURCES;CUSTOM_BUILDPROPS"
        # the input arguments
        ${arguments})

    GET_FILENAME_COMPONENT(_DN_abs_proj "${_DN_PROJECT}" ABSOLUTE)
    GET_FILENAME_COMPONENT(_DN_proj_dir "${_DN_abs_proj}" DIRECTORY)
    GET_FILENAME_COMPONENT(_DN_projname "${_DN_PROJECT}" NAME)
    STRING(REGEX REPLACE "\\.[^.]*$" "" _DN_projname_noext ${_DN_projname})

    FILE(GLOB_RECURSE DOTNET_deps 
        ${_DN_proj_dir}/*.cs
        ${_DN_proj_dir}/*.fs
        ${_DN_proj_dir}/*.vb
        ${_DN_proj_dir}/*.xaml
        ${_DN_proj_dir}/*.resx
        ${_DN_proj_dir}/*.xml
        ${_DN_proj_dir}/*.*proj
        ${_DN_proj_dir}/*.cs
        ${_DN_proj_dir}/*.config)
    LIST(APPEND DOTNET_deps ${_DN_SOURCES})
    SET(_DN_deps "")
    FOREACH(dep ${DOTNET_deps})
        IF(NOT dep MATCHES /obj/ AND NOT dep MATCHES /bin/)
            LIST(APPEND _DN_deps ${dep})
        ENDIF()
    ENDFOREACH()


    IF(_DN_RELEASE)
        SET(_DN_CONFIG Release)
    ELSEIF(_DN_DEBUG)
        SET(_DN_CONFIG Debug)
    ENDIF()

    IF(NOT _DN_CONFIG)
        SET(_DN_CONFIG "$<$<CONFIG:Debug>:Debug>$<$<NOT:$<CONFIG:Debug>>:Release>")
    ENDIF()

    # If platform is not specified, do not pass the Platform property.
    # dotnet will pick the default Platform.

    IF(_DN_X86)
        SET(_DN_PLATFORM x86)
    ELSEIF(_DN_X64)
        SET(_DN_PLATFORM x64)
    ELSEIF(_DN_ANYCPU)
        SET(_DN_PLATFORM "AnyCPU")
    ENDIF()

    # If package version is not set, first fallback to DOTNET_PACKAGE_VERSION
    # If again not set, defaults to 1.0.0
    IF(NOT _DN_VERSION)
        SET(_DN_VERSION ${DOTNET_PACKAGE_VERSION})
    ENDIF()
    IF(NOT _DN_VERSION)
        SET(_DN_VERSION "1.0.0")
    ENDIF()

    # Set the output path to the binary directory.
    # Build outputs in separated output directories prevent overwriting.
    # Later we then copy the outputs to the destination.

    IF(NOT _DN_OUTPUT_PATH)
        SET(_DN_OUTPUT_PATH ${_DN_projname_noext})
    ENDIF()

    GET_FILENAME_COMPONENT(_DN_OUTPUT_PATH ${PROJECT_BINARY_DIR}/${_DN_OUTPUT_PATH} ABSOLUTE)

    # In a cmake build, the XPLAT libraries are always copied over.
    # Set the proper directory for .NET projects.
    SET(_DN_XPLAT_LIB_DIR ${PROJECT_BINARY_DIR})

    SET(DOTNET_PACKAGES ${_DN_PACKAGE}  PARENT_SCOPE)
    SET(DOTNET_CONFIG   ${_DN_CONFIG}   PARENT_SCOPE)
    SET(DOTNET_PLATFORM ${_DN_PLATFORM} PARENT_SCOPE)
    SET(DOTNET_DEPENDS  ${_DN_DEPENDS}  PARENT_SCOPE)
    SET(DOTNET_PROJNAME ${_DN_projname_noext} PARENT_SCOPE)
    SET(DOTNET_PROJPATH ${_DN_abs_proj} PARENT_SCOPE)
    SET(DOTNET_PROJDIR  ${_DN_proj_dir} PARENT_SCOPE)
    SET(DOTNET_ARGUMENTS ${_DN_ARGUMENTS} PARENT_SCOPE)
    SET(DOTNET_RUN_OUTPUT ${_DN_OUTPUT} PARENT_SCOPE)
    SET(DOTNET_PACKAGE_VERSION ${_DN_VERSION} PARENT_SCOPE)
    SET(DOTNET_OUTPUT_PATH ${_DN_OUTPUT_PATH} PARENT_SCOPE)
    SET(DOTNET_deps ${_DN_deps} PARENT_SCOPE)

    IF(_DN_PLATFORM)
        SET(_DN_PLATFORM_PROP "/p:Platform=${_DN_PLATFORM}")
    ENDIF()

    IF(_DN_NETCOREAPP)
        SET(_DN_BUILD_OPTIONS -f netcoreapp2.0)
        SET(_DN_PACK_OPTIONS /p:TargetFrameworks=netcoreapp2.0)
    ELSEIF(UNIX)
        # Unix builds default to netstandard2.0
        SET(_DN_BUILD_OPTIONS -f netstandard2.0)
        SET(_DN_PACK_OPTIONS /p:TargetFrameworks=netstandard2.0)
    ENDIF()

    SET(_DN_IMPORT_PROP ${CMAKE_CURRENT_BINARY_DIR}/${_DN_projname}.imports.props)
    CONFIGURE_FILE(${DOTNET_MODULE_DIR}/DotnetImports.props.in ${_DN_IMPORT_PROP})
    SET(_DN_IMPORT_ARGS "/p:DirectoryBuildPropsPath=${_DN_IMPORT_PROP}")

    SET(DOTNET_IMPORT_PROPERTIES ${_DN_IMPORT_ARGS} PARENT_SCOPE)
    SET(DOTNET_BUILD_PROPERTIES ${_DN_PLATFORM_PROP} ${_DN_IMPORT_ARGS} PARENT_SCOPE)
    SET(DOTNET_BUILD_OPTIONS ${_DN_BUILD_OPTIONS} PARENT_SCOPE)
    SET(DOTNET_PACK_OPTIONS --include-symbols ${_DN_PACK_OPTIONS} ${_DN_PACK_ARGUMENTS} PARENT_SCOPE)

ENDFUNCTION()

MACRO(ADD_DOTNET_DEPENDENCY_TARGETS tgt)
    FOREACH(pkg_dep ${DOTNET_DEPENDS})
        ADD_DEPENDENCIES(${tgt}_${DOTNET_PROJNAME} PKG_${pkg_dep})
        MESSAGE("     ${DOTNET_PROJNAME} <- ${pkg_dep}")
    ENDFOREACH()

    FOREACH(pkg ${DOTNET_PACKAGES})
        STRING(TOLOWER ${pkg} pkg_lowercase)
        GET_FILENAME_COMPONENT(cache_path ${NUGET_CACHE_PATH}/${pkg_lowercase} ABSOLUTE)
        IF(WIN32)
            SET(rm_command powershell -NoLogo -NoProfile -NonInteractive -Command "Remove-Item -Recurse -Force -ErrorAction Ignore '${cache_path}'\; exit 0")
        ELSE()
            SET(rm_command rm -rf ${cache_path})
        ENDIF()
        ADD_CUSTOM_TARGET(
            DOTNET_PURGE_${pkg}
            COMMAND ${CMAKE_COMMAND} -E echo "======= [x] Purging nuget package cache for ${pkg}"
            COMMAND ${rm_command}
            DEPENDS ${DOTNET_deps}
        )
        ADD_DEPENDENCIES(${tgt}_${DOTNET_PROJNAME} DOTNET_PURGE_${pkg})
        # Add a target for the built package -- this can be referenced in
        # another project.
        ADD_CUSTOM_TARGET(PKG_${pkg})
        ADD_DEPENDENCIES(PKG_${pkg} ${tgt}_${DOTNET_PROJNAME})
        MESSAGE("==== ${DOTNET_PROJNAME} -> ${pkg}")
    ENDFOREACH()
ENDMACRO()

MACRO(DOTNET_BUILD_COMMANDS)
    IF(${DOTNET_IS_MSBUILD})
        SET(build_dotnet_cmds 
            COMMAND ${CMAKE_COMMAND} -E echo "======= Building msbuild project ${DOTNET_PROJNAME} [${DOTNET_CONFIG} ${DOTNET_PLATFORM}]"
            COMMAND ${NUGET_EXE} restore -Force ${DOTNET_PROJPATH}
            COMMAND ${DOTNET_EXE} msbuild ${DOTNET_PROJPATH} /t:Clean ${DOTNET_BUILD_PROPERTIES} /p:Configuration="${DOTNET_CONFIG}"
            COMMAND ${DOTNET_EXE} msbuild ${DOTNET_PROJPATH} /t:Build ${DOTNET_BUILD_PROPERTIES} /p:Configuration="${DOTNET_CONFIG}" ${DOTNET_ARGUMENTS})
        SET(build_dotnet_type "msbuild")
    ELSE()
        SET(build_dotnet_cmds 
            COMMAND ${CMAKE_COMMAND} -E echo "======= Building .NET project ${DOTNET_PROJNAME} [${DOTNET_CONFIG} ${DOTNET_PLATFORM}]"
            COMMAND ${DOTNET_EXE} restore ${DOTNET_PROJPATH} ${DOTNET_IMPORT_PROPERTIES}
            COMMAND ${DOTNET_EXE} clean ${DOTNET_PROJPATH} ${DOTNET_BUILD_PROPERTIES}
            COMMAND ${DOTNET_EXE} build --no-restore ${DOTNET_PROJPATH} -c ${DOTNET_CONFIG} ${DOTNET_BUILD_PROPERTIES} ${DOTNET_BUILD_OPTIONS} ${DOTNET_ARGUMENTS})
        SET(build_dotnet_type "dotnet")
    ENDIF()

    # DOTNET_OUTPUTS refer to artifacts produced, that the BUILD_proj_name target depends on.
    SET(DOTNET_OUTPUTS ${CMAKE_CURRENT_BINARY_DIR}/${DOTNET_PROJNAME}.buildtimestamp)
    LIST(APPEND build_dotnet_cmds COMMAND ${CMAKE_COMMAND} -E touch ${DOTNET_OUTPUTS})
    IF(NOT "${DOTNET_PACKAGES}" STREQUAL "")
        MESSAGE("-- Adding ${build_dotnet_type} project ${DOTNET_PROJPATH} (version ${DOTNET_PACKAGE_VERSION})")
        FOREACH(pkg ${DOTNET_PACKAGES})
            LIST(APPEND DOTNET_OUTPUTS ${DOTNET_OUTPUT_PATH}/${pkg}.${DOTNET_PACKAGE_VERSION}.nupkg)
            LIST(APPEND DOTNET_OUTPUTS ${DOTNET_OUTPUT_PATH}/${pkg}.${DOTNET_PACKAGE_VERSION}.symbols.nupkg)
            LIST(APPEND build_dotnet_cmds COMMAND ${CMAKE_COMMAND} -E remove ${DOTNET_OUTPUT_PATH}/${pkg}.${DOTNET_PACKAGE_VERSION}.nupkg)
            LIST(APPEND build_dotnet_cmds COMMAND ${CMAKE_COMMAND} -E remove ${DOTNET_OUTPUT_PATH}/${pkg}.${DOTNET_PACKAGE_VERSION}.symbols.nupkg)
        ENDFOREACH()
        LIST(APPEND build_dotnet_cmds COMMAND ${DOTNET_EXE} pack --no-build --no-restore ${DOTNET_PROJPATH} -c ${DOTNET_CONFIG} ${DOTNET_BUILD_PROPERTIES} ${DOTNET_PACK_OPTIONS})
    ELSE()
        MESSAGE("-- Adding ${build_dotnet_type} project ${DOTNET_PROJPATH} (no nupkg)")
    ENDIF()

    ADD_CUSTOM_COMMAND(
        OUTPUT ${DOTNET_OUTPUTS}
        DEPENDS ${DOTNET_deps}
        ${build_dotnet_cmds}
        )
    ADD_CUSTOM_TARGET(
        BUILD_${DOTNET_PROJNAME} ALL
        DEPENDS ${DOTNET_OUTPUTS})

ENDMACRO()

FUNCTION(ADD_DOTNET DOTNET_PROJECT)
    DOTNET_GET_DEPS(${DOTNET_PROJECT} "${ARGN}")
    SET(DOTNET_IS_MSBUILD FALSE)
    DOTNET_BUILD_COMMANDS()
    ADD_DOTNET_DEPENDENCY_TARGETS(BUILD)
ENDFUNCTION()

FUNCTION(ADD_MSBUILD DOTNET_PROJECT)
    IF(NOT WIN32)
        MESSAGE("-- Building non-Win32, skipping ${DOTNET_PROJECT}")
        RETURN()
    ENDIF()

    DOTNET_GET_DEPS(${DOTNET_PROJECT} "${ARGN}")
    SET(DOTNET_IS_MSBUILD TRUE)
    DOTNET_BUILD_COMMANDS()
    ADD_DOTNET_DEPENDENCY_TARGETS(BUILD)
ENDFUNCTION()

FUNCTION(RUN_DOTNET DOTNET_PROJECT)
    DOTNET_GET_DEPS(${DOTNET_PROJECT} "${ARGN};NETCOREAPP")
    MESSAGE("-- Adding dotnet run project ${DOTNET_PROJECT}")
    FILE(MAKE_DIRECTORY ${DOTNET_OUTPUT_PATH})
    ADD_CUSTOM_COMMAND(
        OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${DOTNET_PROJNAME}.runtimestamp ${DOTNET_RUN_OUTPUT}
        DEPENDS ${DOTNET_deps}
        COMMAND ${DOTNET_EXE} restore ${DOTNET_PROJPATH} ${DOTNET_IMPORT_PROPERTIES}
        COMMAND ${DOTNET_EXE} clean ${DOTNET_PROJPATH} ${DOTNET_BUILD_PROPERTIES}
        COMMAND ${DOTNET_EXE} build --no-restore ${DOTNET_PROJPATH} -c ${DOTNET_CONFIG} ${DOTNET_BUILD_PROPERTIES} ${DOTNET_BUILD_OPTIONS}
        # XXX tfm
        COMMAND ${DOTNET_EXE} ${DOTNET_OUTPUT_PATH}/netcoreapp2.0/${DOTNET_PROJNAME}.dll ${DOTNET_ARGUMENTS}
        COMMAND ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_BINARY_DIR}/${DOTNET_PROJNAME}.runtimestamp
        WORKING_DIRECTORY ${DOTNET_OUTPUT_PATH})
    ADD_CUSTOM_TARGET(
        RUN_${DOTNET_PROJNAME} 
        DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/${DOTNET_PROJNAME}.runtimestamp ${DOTNET_RUN_OUTPUT})
    ADD_DOTNET_DEPENDENCY_TARGETS(RUN)
ENDFUNCTION()

FUNCTION(TEST_DOTNET DOTNET_PROJECT)
    DOTNET_GET_DEPS(${DOTNET_PROJECT} "${ARGN}")
    MESSAGE("-- Adding dotnet test project ${DOTNET_PROJECT}")
    IF(WIN32)
        SET(test_framework_args "")
    ELSE()
        SET(test_framework_args -f netcoreapp2.0)
    ENDIF()

    ADD_TEST(NAME              ${DOTNET_PROJNAME}
             COMMAND           ${DOTNET_EXE} test ${test_framework_args} --results-directory "${PROJECT_BINARY_DIR}" --logger trx ${DOTNET_ARGUMENTS}
             WORKING_DIRECTORY ${DOTNET_OUTPUT_PATH})

ENDFUNCTION()

SET_PROPERTY(GLOBAL PROPERTY DOTNET_LAST_SMOKETEST "")

FUNCTION(SMOKETEST_DOTNET DOTNET_PROJECT)
    MESSAGE("-- Adding dotnet smoke test project ${DOTNET_PROJECT}")
    IF(WIN32)
        RUN_DOTNET(${DOTNET_PROJECT} "${ARGN}")
    ELSE()
        RUN_DOTNET(${DOTNET_PROJECT} "${ARGN}")
    ENDIF()

    DOTNET_GET_DEPS(${DOTNET_PROJECT} "${ARGN}")
    ADD_CUSTOM_TARGET(
        SMOKETEST_${DOTNET_PROJNAME}
        ALL
        DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/${DOTNET_PROJNAME}.runtimestamp)
    ADD_DOTNET_DEPENDENCY_TARGETS(SMOKETEST)
    GET_PROPERTY(_dn_last_smoketest GLOBAL PROPERTY DOTNET_LAST_SMOKETEST)
    IF(_dn_last_smoketest)
        MESSAGE("${_dn_last_smoketest} -> SMOKETEST_${DOTNET_PROJNAME}")
        ADD_DEPENDENCIES(SMOKETEST_${DOTNET_PROJNAME} ${_dn_last_smoketest})
    ENDIF()
    # Chain the smoke tests together so they are executed sequentially
    SET_PROPERTY(GLOBAL PROPERTY DOTNET_LAST_SMOKETEST SMOKETEST_${DOTNET_PROJNAME})

ENDFUNCTION()

SET(DOTNET_IMPORTS_TEMPLATE ${CMAKE_CURRENT_LIST_DIR}/DotnetImports.props.in)

FUNCTION(GEN_DOTNET_PROPS target_props_file)
    CMAKE_PARSE_ARGUMENTS(
        # prefix
        _DNP
        # options (flags)
        "" 
        # oneValueArgs
        "PACKAGE_VERSION;XML_INJECT" 
        # multiValueArgs
        ""
        # the input arguments
        ${ARGN})

    IF(NOT _DNP_PACKAGE_VERSION)
        SET(_DNP_PACKAGE_VERSION 1.0.0)
    ENDIF()

    IF(_DNP_XML_INJECT)
        SET(_DN_CUSTOM_BUILDPROPS ${_DNP_XML_INJECT})
    ENDIF()

    SET(_DN_OUTPUT_PATH ${PROJECT_BINARY_DIR})
    SET(_DN_XPLAT_LIB_DIR ${PROJECT_BINARY_DIR})
    SET(_DN_VERSION ${_DNP_PACKAGE_VERSION})
    CONFIGURE_FILE(${DOTNET_IMPORTS_TEMPLATE} ${target_props_file})
    UNSET(_DN_OUTPUT_PATH)
    UNSET(_DN_XPLAT_LIB_DIR)
    UNSET(_DN_VERSION)
ENDFUNCTION()


MESSAGE("-- Found .NET toolchain: ${DOTNET_EXE} (version ${DOTNET_VERSION})")
SET(DOTNET_FOUND TRUE)
