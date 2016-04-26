find_package(DotNetToolchain REQUIRED)

# Configure AssemblyInfo.cs
set(VER_MAJOR "${Z3_VERSION_MAJOR}")
set(VER_MINOR "${Z3_VERSION_MINOR}")
set(VER_BUILD "${Z3_VERSION_PATCH}")
set(VER_REVISION "${Z3_VERSION_TWEAK}")
set(Z3_DOTNET_ASSEMBLY_INFO_FILE "${CMAKE_CURRENT_BINARY_DIR}/Properties/AssemblyInfo.cs")
configure_file("Properties/AssemblyInfo.cs.in" "${Z3_DOTNET_ASSEMBLY_INFO_FILE}" @ONLY)

# Generate Native.cs
set(Z3_DOTNET_NATIVE_FILE "${CMAKE_CURRENT_BINARY_DIR}/Native.cs")
add_custom_command(OUTPUT "${Z3_DOTNET_NATIVE_FILE}"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${CMAKE_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--dotnet-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${CMAKE_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
    # FIXME: When update_api.py no longer uses ``mk_util`` drop this dependency
    "${CMAKE_SOURCE_DIR}/scripts/mk_util.py"
  COMMENT "Generating ${Z3_DOTNET_NATIVE_FILE}"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)

# Generate Enumerations.cs
set(Z3_DOTNET_CONST_FILE "${CMAKE_CURRENT_BINARY_DIR}/Enumerations.cs")
add_custom_command(OUTPUT "${Z3_DOTNET_CONST_FILE}"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${CMAKE_SOURCE_DIR}/scripts/mk_consts_files.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--dotnet-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${CMAKE_SOURCE_DIR}/scripts/mk_consts_files.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
  COMMENT "Generating ${Z3_DOTNET_CONST_FILE}"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)

set(Z3_DOTNET_ASSEMBLY_SOURCES_IN_SRC_TREE
	AlgebraicNum.cs
	ApplyResult.cs
	ArithExpr.cs
	ArithSort.cs
	ArrayExpr.cs
	ArraySort.cs
	AST.cs
	ASTMap.cs
	ASTVector.cs
	BitVecExpr.cs
	BitVecNum.cs
	BitVecSort.cs
	BoolExpr.cs
	BoolSort.cs
	Constructor.cs
	ConstructorList.cs
	Context.cs
	DatatypeExpr.cs
	DatatypeSort.cs
	Deprecated.cs
	EnumSort.cs
	Expr.cs
	FiniteDomainExpr.cs
	FiniteDomainNum.cs
	FiniteDomainSort.cs
	Fixedpoint.cs
	FPExpr.cs
	FPNum.cs
	FPRMExpr.cs
	FPRMNum.cs
	FPRMSort.cs
	FPSort.cs
	FuncDecl.cs
	FuncInterp.cs
	Global.cs
	Goal.cs
	IDecRefQueue.cs
	InterpolationContext.cs
	IntExpr.cs
	IntNum.cs
	IntSort.cs
	IntSymbol.cs
	ListSort.cs
	Log.cs
	Model.cs
	Optimize.cs
	ParamDescrs.cs
	Params.cs
	Pattern.cs
	Probe.cs
	Quantifier.cs
	RatNum.cs
	RealExpr.cs
	RealSort.cs
	ReExpr.cs
	RelationSort.cs
	ReSort.cs
	SeqExpr.cs
	SeqSort.cs
	SetSort.cs
	Solver.cs
	Sort.cs
	Statistics.cs
	Status.cs
	StringSymbol.cs
	Symbol.cs
	Tactic.cs
	TupleSort.cs
	UninterpretedSort.cs
	Version.cs
	Z3Exception.cs
	Z3Object.cs
)

set(Z3_DOTNET_ASSEMBLY_SOURCES "")
# Make paths to source files absolute
foreach (csfile ${Z3_DOTNET_ASSEMBLY_SOURCES_IN_SRC_TREE})
  list(APPEND Z3_DOTNET_ASSEMBLY_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/${csfile}")
endforeach()

# Add generated files
list(APPEND Z3_DOTNET_ASSEMBLY_SOURCES
  "${Z3_DOTNET_CONST_FILE}"
  "${Z3_DOTNET_NATIVE_FILE}"
  "${Z3_DOTNET_ASSEMBLY_INFO_FILE}"
)

# ``csc.exe`` doesn't like UNIX style paths so convert them
# if necessary first to native paths.
set(Z3_DOTNET_ASSEMBLY_SOURCES_NATIVE_PATH "")
foreach (csfile_path ${Z3_DOTNET_ASSEMBLY_SOURCES})
  file(TO_NATIVE_PATH "${csfile_path}" csfile_path_native)
  list(APPEND Z3_DOTNET_ASSEMBLY_SOURCES_NATIVE_PATH "${csfile_path_native}")
endforeach()

set(CSC_FLAGS "")
if (DOTNET_TOOLCHAIN_IS_WINDOWS)
  # FIXME: Why use these flags?
  # Note these flags have been copied from the Python build system.
  list(APPEND CSC_FLAGS
    "/noconfig"
    "/nostdlib+"
    "/reference:mscorlib.dll"
  )
  # FIXME: This flag only works when the working directory of csc.exe is
  # the directory containing the ``libz3`` target. I can't get this to work
  # correctly with multi-configuration generators (i.e. Visual Studio) so
  # just don't set the flag for now.
  #list(APPEND CSC_FLAGS "/linkresource:$<TARGET_FILE_NAME:libz3>")
elseif (DOTNET_TOOLCHAIN_IS_MONO)
  # We need to give the assembly a strong name so that it can be installed
  # into the GAC.
  list(APPEND CSC_FLAGS
    "/keyfile:${CMAKE_CURRENT_SOURCE_DIR}/Microsoft.Z3.mono.snk"
  )
else()
  message(FATAL_ERROR "Unknown .NET toolchain")
endif()

# Common flags
list(APPEND CSC_FLAGS
  "/unsafe+"
  "/nowarn:1701,1702"
  "/errorreport:prompt"
  "/warn:4"
  "/reference:System.Core.dll"
  "/reference:System.dll"
  "/reference:System.Numerics.dll"
  "/filealign:512" # Why?
  "/target:library"
)

# Set the build type flags. The build type for the assembly roughly corresponds
# with the native code build type.
list(APPEND CSC_FLAGS
  # Debug flags, expands to nothing if we aren't doing a debug build
  "$<$<CONFIG:Debug>:/debug+>"
  "$<$<CONFIG:Debug>:/debug:full>"
  "$<$<CONFIG:Debug>:/optimize->"
  # This has to be quoted otherwise the ``;`` is interpreted as a command separator
  "$<$<CONFIG:Debug>:\"/define:DEBUG$<SEMICOLON>TRACE\">"
  # Release flags, expands to nothing if we are doing a debug build
  "$<$<NOT:$<CONFIG:Debug>>:/optimize+>"
)

# Mono's gacutil crashes when trying to install an assembly if we set the
# platform in some cases, so only set it on Windows.  This bug has been
# reported at https://bugzilla.xamarin.com/show_bug.cgi?id=39955 . However mono
# ignores the platform of an assembly when running it (
# http://lists.ximian.com/pipermail/mono-devel-list/2015-November/043370.html )
# so this shouldn't matter in practice.
if (DOTNET_TOOLCHAIN_IS_WINDOWS)
  # Set platform for assembly
  if ("${TARGET_ARCHITECTURE}" STREQUAL "x86_64")
    list(APPEND CSC_FLAGS "/platform:x64")
  elseif ("${TARGET_ARCHITECTURE}" STREQUAL "i686")
    list(APPEND CSC_FLAGS "/platform:x86")
  endif()
endif()

# FIXME: Ideally we should emit files into a configuration specific directory
# when using multi-configuration generators so that the files generated by each
# configuration don't clobber each other. Unfortunately the ``get_property()``
# command only works correctly for single configuration generators so we can't
# use it. We also can't use ``$<TARGET_FILE_DIR:libz3>`` because the ``OUTPUT``
# argument to ``add_custom_commands()`` won't accept it.
# See http://public.kitware.com/pipermail/cmake/2016-March/063101.html
#
# For now just output file to the root binary directory like the Python build
# system does and emit a warning when appropriate.
if (DEFINED CMAKE_CONFIGURATION_TYPES)
  # Multi-configuration build (e.g. Visual Studio and Xcode).
  message(WARNING "You are using a multi-configuration generator. The build rules for"
    " the \".NET\" bindings currently do not emit files per configuration so previously"
    " generated files for other configurations will be overwritten.")
endif()

set(Z3_DOTNET_ASSEMBLY_OUTPUT_DIR "${CMAKE_BINARY_DIR}")
set(Z3_DOTNET_ASSEMBLY_NAME "Microsoft.Z3.dll")
set(Z3_DOTNET_ASSEMBLY_DLL "${Z3_DOTNET_ASSEMBLY_OUTPUT_DIR}/${Z3_DOTNET_ASSEMBLY_NAME}")
# csc.exe doesn't work with UNIX style paths so convert to native path
file(TO_NATIVE_PATH "${Z3_DOTNET_ASSEMBLY_DLL}" Z3_DOTNET_ASSEMBLY_DLL_NATIVE_PATH)
set(Z3_DOTNET_ASSEMBLY_DLL_DOC "${Z3_DOTNET_ASSEMBLY_OUTPUT_DIR}/Microsoft.Z3.xml")
file(TO_NATIVE_PATH "${Z3_DOTNET_ASSEMBLY_DLL_DOC}" Z3_DOTNET_ASSEMBLY_DLL_DOC_NATIVE_PATH)
add_custom_command(OUTPUT "${Z3_DOTNET_ASSEMBLY_DLL}" "${Z3_DOTNET_ASSEMBLY_DLL_DOC}"
  COMMAND
    "${DOTNET_CSC_EXECUTABLE}"
    ${CSC_FLAGS}
    "/out:${Z3_DOTNET_ASSEMBLY_DLL_NATIVE_PATH}"
    "/doc:${Z3_DOTNET_ASSEMBLY_DLL_DOC_NATIVE_PATH}"
    ${Z3_DOTNET_ASSEMBLY_SOURCES_NATIVE_PATH}
  DEPENDS
    ${Z3_DOTNET_ASSEMBLY_SOURCES}
    libz3
  WORKING_DIRECTORY "${Z3_DOTNET_ASSEMBLY_OUTPUT_DIR}"
  COMMENT "Building \"${Z3_DOTNET_ASSEMBLY_DLL}\""
)

# Convenient top-level target
add_custom_target(build_z3_dotnet_bindings
  ALL
  DEPENDS
    "${Z3_DOTNET_ASSEMBLY_DLL}"
)

###############################################################################
# Install
###############################################################################
option(INSTALL_DOTNET_BINDINGS "Install .NET bindings when invoking install target" ON)
set(GAC_PKG_NAME "Microsoft.Z3.Sharp")
set(PREFIX "${CMAKE_INSTALL_PREFIX}")
set(VERSION "${Z3_VERSION}")
set(Z3_DOTNET_PKGCONFIG_FILE "${CMAKE_CURRENT_BINARY_DIR}/Microsoft.Z3.Sharp.pc")
configure_file("Microsoft.Z3.Sharp.pc.in" "${Z3_DOTNET_PKGCONFIG_FILE}" @ONLY)

if (DOTNET_TOOLCHAIN_IS_MONO)
  message(STATUS "Emitting install rules for .NET bindings")
  # Install pkgconfig file for the assembly. This is needed by Monodevelop
  # to find the assembly
  install(FILES "${Z3_DOTNET_PKGCONFIG_FILE}" DESTINATION "${CMAKE_INSTALL_PKGCONFIGDIR}")

  # Configure the install and uninstall scripts.
  # Note: If multi-configuration generator support is ever fixed then these
  # scripts will be broken.
  configure_file(cmake_install_gac.cmake.in cmake_install_gac.cmake @ONLY)
  configure_file(cmake_uninstall_gac.cmake.in cmake_uninstall_gac.cmake @ONLY)

  # Tell CMake to Invoke a script to install assembly to the GAC during install
  install(SCRIPT "${CMAKE_CURRENT_BINARY_DIR}/cmake_install_gac.cmake")

  # Add custom target to uninstall the assembly from the GAC
  add_custom_target(remove_dotnet_dll_from_gac
    COMMAND "${CMAKE_COMMAND}" "-P" "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall_gac.cmake"
    COMMENT "Uninstalling ${Z3_DOTNET_ASSEMBLY_NAME} from the GAC"
    ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
  )
  add_dependencies(uninstall remove_dotnet_dll_from_gac)

elseif(DOTNET_TOOLCHAIN_IS_WINDOWS)
  # Don't install Z3_DOTNET_ASSEMBLY_DLL into the gac. Instead just copy into
  # installation directory.
  install(FILES "${Z3_DOTNET_ASSEMBLY_DLL}" DESTINATION "${CMAKE_INSTALL_LIBDIR}")
  install(FILES "${Z3_DOTNET_ASSEMBLY_DLL_DOC}" DESTINATION "${CMAKE_INSTALL_LIBDIR}")
else()
  message(FATAL_ERROR "Unknown .NET toolchain")
endif()
