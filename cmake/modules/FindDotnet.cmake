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
#            [DEPENDS depend_nuget_packages... ])
# ```
# 
# RUN_DOTNET -- Run a project with `dotnet run`. The `OUTPUT` argument represents artifacts 
#               produced by running the .NET program, and can be consumed from other build steps.
# 
# ```
# RUN_DOTNET(<project_file> 
#            [ARGUMENTS program_args...]
#            [OUTPUT outputs...])
# ```
# 
# ADD_MSBUILD -- add a project to be built by msbuild. Windows-only. When building in Unix systems, msbuild targets are skipped.
# 
# ```
# ADD_MSBUILD(<project_file> [RELEASE|DEBUG] [X86|X64|ANYCPU] [NETCOREAPP]
#            [CONFIG configuration]
#            [PLATFORM platform]
#            [PACKAGE output_nuget_packages... ]
#            [DEPENDS depend_nuget_packages... ])
# ```
#
# DOTNET_REGISTER_LOCAL_REPOSITORY -- register a local NuGet package repository.
# 
# ```
# DOTNET_REGISTER_LOCAL_REPOSITORY(repo_name repo_path)
# ```
# 
# For all the above functions, `RELEASE|DEBUG` overrides `CONFIG`, `X86|X64|ANYCPU` overrides PLATFORM.
# For Unix systems, the target framework defaults to `netstandard2.0`, unless `NETCOREAPP` is specified.
# For Windows, the project is built as-is, allowing multi-targeting.
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
   FIND_PROGRAM(NUGET_EXE nuget PATHS ${CMAKE_BINARY_DIR}/tools)
   IF(NUGET_EXE)
       MESSAGE("-- Found nuget: ${NUGET_EXE}")
   ELSE()
        SET(NUGET_EXE ${CMAKE_BINARY_DIR}/tools/nuget.exe)
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
        EXECUTE_PROCESS(COMMAND sed -i "/${repo_name}/d" "${nuget_config}")
        EXECUTE_PROCESS(COMMAND sed -i "s#</packageSources>#  <add key=\\\"${repo_name}\\\" value=\\\"${repo_path}\\\" />\\n  </packageSources>#g" "${nuget_config}")
    ENDIF()
ENDFUNCTION()

FUNCTION(DOTNET_GET_DEPS _DN_PROJECT arguments)
    FILE(GLOB_RECURSE DOTNET_deps *.cs *.fs *.xaml *.csproj *.fsproj *.tsl)
    LIST(FILTER DOTNET_deps EXCLUDE REGEX /obj/)
    CMAKE_PARSE_ARGUMENTS(
        # prefix
        _DN 
        # options (flags)
        "RELEASE;DEBUG;X86;X64;ANYCPU;NETCOREAPP" 
        # oneValueArgs
        "CONFIG;PLATFORM;VERSION" 
        # multiValueArgs
        "PACKAGE;DEPENDS;ARGUMENTS;OUTPUT"
        # the input arguments
        ${arguments})

    GET_FILENAME_COMPONENT(_DN_abs_proj "${_DN_PROJECT}" ABSOLUTE)
    GET_FILENAME_COMPONENT(_DN_proj_dir "${_DN_PROJECT}" DIRECTORY)
    GET_FILENAME_COMPONENT(_DN_projname "${DOTNET_PROJECT}" NAME)
    STRING(REGEX REPLACE "\\.[^.]*$" "" _DN_projname_noext ${_DN_projname})

    IF(_DN_RELEASE)
        SET(_DN_CONFIG Release)
    ELSEIF(_DN_DEBUG)
        SET(_DN_CONFIG Debug)
    ENDIF()

    IF(NOT _DN_CONFIG)
        SET(_DN_CONFIG $<CONFIG>)
        IF(_DN_CONFIG STREQUAL "RelWithDebInfo" OR _DN_CONFIG STREQUAL "RelMinSize" OR NOT _DN_CONFIG)
            SET(_DN_CONFIG "Release")
        ENDIF()
    ENDIF()

    # If platform is not specified, do not pass the Platform property.
    # dotnet will pick the default Platform.

    IF(_DN_X86)
        SET(_DN_PLATFORM x86)
    ELSEIF(_DN_X64)
        SET(_DN_PLATFORM x64)
    ELSEIF(_DN_ANYCPU)
        SET(_DN_PLATFORM "Any CPU")
    ENDIF()

    # If package version is not set, first fallback to DOTNET_PACKAGE_VERSION
    # If again not set, defaults to 1.0.0
    IF(NOT _DN_VERSION)
        SET(_DN_VERSION ${DOTNET_PACKAGE_VERSION})
    ENDIF()
    IF(NOT _DN_VERSION)
        SET(_DN_VERSION "1.0.0")
    ENDIF()

    GET_FILENAME_COMPONENT(_DN_OUTPUT_PATH ${CMAKE_CURRENT_BINARY_DIR}/bin ABSOLUTE)

    SET(DOTNET_PACKAGES ${_DN_PACKAGE}  PARENT_SCOPE)
    SET(DOTNET_CONFIG   ${_DN_CONFIG}   PARENT_SCOPE)
    SET(DOTNET_PLATFORM ${_DN_PLATFORM} PARENT_SCOPE)
    SET(DOTNET_DEPENDS  ${_DN_DEPENDS}  PARENT_SCOPE)
    SET(DOTNET_PROJNAME ${_DN_projname_noext} PARENT_SCOPE)
    SET(DOTNET_PROJPATH ${_DN_abs_proj} PARENT_SCOPE)
    SET(DOTNET_PROJDIR  ${_DN_proj_dir} PARENT_SCOPE)
    SET(DOTNET_RUN_ARGUMENTS ${_DN_ARGUMENTS} PARENT_SCOPE)
    SET(DOTNET_RUN_OUTPUT ${_DN_OUTPUT} PARENT_SCOPE)
    SET(DOTNET_PACKAGE_VERSION ${_DN_VERSION} PARENT_SCOPE)
    SET(DOTNET_OUTPUT_PATH ${_DN_OUTPUT_PATH} PARENT_SCOPE)
    SET(DOTNET_deps ${DOTNET_deps} PARENT_SCOPE)

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

    SET(DOTNET_BUILD_PROPERTIES ${_DN_PLATFORM_PROP} ${_DN_TFMS_PROP} "/p:DirectoryBuildPropsPath=${_DN_IMPORT_PROP}" "/p:DOTNET_PACKAGE_VERSION=${_DN_VERSION}" PARENT_SCOPE)
    SET(DOTNET_BUILD_OPTIONS ${_DN_BUILD_OPTIONS} PARENT_SCOPE)
    SET(DOTNET_PACK_OPTIONS  ${_DN_PACK_OPTIONS} PARENT_SCOPE)

ENDFUNCTION()

MACRO(ADD_DOTNET_DEPENDENCY_TARGETS)
    FOREACH(pkg_dep ${DOTNET_DEPENDS})
        ADD_DEPENDENCIES(BUILD_${DOTNET_PROJNAME} PKG_${pkg_dep})
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
        ADD_DEPENDENCIES(BUILD_${DOTNET_PROJNAME} DOTNET_PURGE_${pkg})
        # Add a target for the built package -- this can be referenced in
        # another project.
        ADD_CUSTOM_TARGET(PKG_${pkg})
        ADD_DEPENDENCIES(PKG_${pkg} BUILD_${DOTNET_PROJNAME})
        MESSAGE("==== ${DOTNET_PROJNAME} -> ${pkg}")
    ENDFOREACH()
ENDMACRO()

MACRO(DOTNET_BUILD_COMMANDS)
    IF(${DOTNET_IS_MSBUILD})
        SET(build_dotnet_cmds 
            COMMAND ${CMAKE_COMMAND} -E echo "=======> Building msbuild project ${DOTNET_PROJNAME} [${DOTNET_CONFIG} ${DOTNET_PLATFORM}]"
            COMMAND ${NUGET_EXE} restore ${DOTNET_PROJPATH}
            COMMAND ${DOTNET_EXE} msbuild ${DOTNET_PROJPATH} /t:Clean /p:Configuration="${DOTNET_CONFIG}"
            COMMAND ${DOTNET_EXE} msbuild ${DOTNET_PROJPATH} /t:Build ${DOTNET_BUILD_PROPERTIES} /p:Configuration="${DOTNET_CONFIG}")
        SET(build_dotnet_type "msbuild")
    ELSE()
        SET(build_dotnet_cmds 
            COMMAND ${CMAKE_COMMAND} -E echo "=======> Building .NET project ${DOTNET_PROJNAME} [${DOTNET_CONFIG} ${DOTNET_PLATFORM}]"
            COMMAND ${DOTNET_EXE} restore ${DOTNET_PROJPATH}
            COMMAND ${DOTNET_EXE} clean ${DOTNET_PROJPATH} ${DOTNET_BUILD_PROPERTIES}
            COMMAND ${DOTNET_EXE} build --no-restore ${DOTNET_PROJPATH} -c ${DOTNET_CONFIG} ${DOTNET_BUILD_PROPERTIES} ${DOTNET_BUILD_OPTIONS})
        SET(build_dotnet_type "dotnet")
    ENDIF()

    IF(NOT "${DOTNET_PACKAGES}" STREQUAL "")
        MESSAGE("-- Adding ${build_dotnet_type} project ${DOTNET_PROJPATH} (version ${DOTNET_PACKAGE_VERSION})")
        SET(_DOTNET_OUTPUTS "")
        FOREACH(pkg ${DOTNET_PACKAGES})
            LIST(APPEND _DOTNET_OUTPUTS ${DOTNET_OUTPUT_PATH}/${pkg}.${DOTNET_PACKAGE_VERSION}.nupkg)
        ENDFOREACH()
        LIST(APPEND build_dotnet_cmds COMMAND ${DOTNET_EXE} pack --no-build --no-restore ${DOTNET_PROJPATH} -c ${DOTNET_CONFIG} ${DOTNET_BUILD_PROPERTIES} ${DOTNET_PACK_OPTIONS})
        LIST(APPEND build_dotnet_cmds COMMAND ${CMAKE_COMMAND} -E copy ${_DOTNET_OUTPUTS} ${CMAKE_BINARY_DIR})
    ELSE()

        MESSAGE("-- Adding ${build_dotnet_type} project ${DOTNET_PROJPATH} (no nupkg)")
        SET(_DOTNET_OUTPUTS ${CMAKE_CURRENT_BINARY_DIR}/${DOTNET_PROJNAME}.buildtimestamp)
        LIST(APPEND build_dotnet_cmds COMMAND ${CMAKE_COMMAND} -E touch ${_DOTNET_OUTPUTS})
    ENDIF()

    ADD_CUSTOM_COMMAND(
        OUTPUT ${_DOTNET_OUTPUTS}
        DEPENDS ${DOTNET_deps}
        ${build_dotnet_cmds}
        )
    ADD_CUSTOM_TARGET(
        BUILD_${DOTNET_PROJNAME} ALL
        DEPENDS ${_DOTNET_OUTPUTS})

ENDMACRO()

FUNCTION(ADD_DOTNET DOTNET_PROJECT)
    DOTNET_GET_DEPS(${DOTNET_PROJECT} "${ARGN}")
    SET(DOTNET_IS_MSBUILD FALSE)
    DOTNET_BUILD_COMMANDS()
    ADD_DOTNET_DEPENDENCY_TARGETS()
ENDFUNCTION()

FUNCTION(ADD_MSBUILD DOTNET_PROJECT)
    IF(NOT WIN32)
        MESSAGE("-- Building non-Win32, skipping ${DOTNET_PROJECT}")
        RETURN()
    ENDIF()

    DOTNET_GET_DEPS(${DOTNET_PROJECT} "${ARGN}")
    SET(DOTNET_IS_MSBUILD TRUE)
    DOTNET_BUILD_COMMANDS()
    ADD_DOTNET_DEPENDENCY_TARGETS()
ENDFUNCTION()

FUNCTION(RUN_DOTNET DOTNET_PROJECT)
    DOTNET_GET_DEPS(${DOTNET_PROJECT} "${ARGN}")
    ADD_CUSTOM_COMMAND(
        OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${DOTNET_PROJNAME}.runtimestamp ${DOTNET_RUN_OUTPUT}
        DEPENDS ${DOTNET_deps}
        COMMAND ${DOTNET_EXE} run ${DOTNET_RUN_ARGUMENTS}
        COMMAND ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_BINARY_DIR}/${DOTNET_PROJNAME}.runtimestamp
        WORKING_DIRECTORY ${DOTNET_PROJDIR})
    ADD_CUSTOM_TARGET(
        RUN_${DOTNET_PROJNAME} 
        DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/${DOTNET_PROJNAME}.runtimestamp ${DOTNET_RUN_OUTPUT})
    ADD_DEPENDENCIES(RUN_${DOTNET_PROJNAME} BUILD_${DOTNET_PROJNAME})
ENDFUNCTION()

MESSAGE("-- Found .NET toolchain: ${DOTNET_EXE} (version ${DOTNET_VERSION})")
SET(DOTNET_FOUND TRUE)
