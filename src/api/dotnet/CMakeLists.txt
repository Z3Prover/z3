find_package(Dotnet REQUIRED)

# Configure AssemblyInfo.cs
set(VER_MAJOR "${Z3_VERSION_MAJOR}")
set(VER_MINOR "${Z3_VERSION_MINOR}")
set(VER_BUILD "${Z3_VERSION_PATCH}")
set(VER_TWEAK "${Z3_VERSION_TWEAK}")

# Generate Native.cs
set(Z3_DOTNET_NATIVE_FILE "${CMAKE_CURRENT_BINARY_DIR}/Native.cs")
add_custom_command(OUTPUT "${Z3_DOTNET_NATIVE_FILE}"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--dotnet-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${PROJECT_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
    # FIXME: When update_api.py no longer uses ``mk_util`` drop this dependency
    "${PROJECT_SOURCE_DIR}/scripts/mk_util.py"
  COMMENT "Generating ${Z3_DOTNET_NATIVE_FILE}"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)

# Generate Enumerations.cs
set(Z3_DOTNET_CONST_FILE "${CMAKE_CURRENT_BINARY_DIR}/Enumerations.cs")
add_custom_command(OUTPUT "${Z3_DOTNET_CONST_FILE}"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/mk_consts_files.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--dotnet-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${PROJECT_SOURCE_DIR}/scripts/mk_consts_files.py"
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
    IntExpr.cs
    IntNum.cs
    IntSort.cs
    IntSymbol.cs
    Lambda.cs
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
)


# Generate <Compile Include="files.cs" /> items
set(Z3_DOTNET_COMPILE_ITEMS "")
foreach(csfile ${Z3_DOTNET_ASSEMBLY_SOURCES})
    set(Z3_DOTNET_COMPILE_ITEMS "${Z3_DOTNET_COMPILE_ITEMS}\n    <Compile Include=\"${csfile}\" />")
endforeach()


# FindDotnet.cmake forwards CMake build type to MSBuild.
# And thus we can put the conditional properties in the project file.
# Note, nuget package file names do not have the ${VER_REV} part.

set(Z3_DOTNET_NUPKG_VERSION "${VER_MAJOR}.${VER_MINOR}.${VER_BUILD}")
if(TARGET_ARCHITECTURE STREQUAL "i686")
    set(Z3_DOTNET_PLATFORM "x86")
else()
    set(Z3_DOTNET_PLATFORM "AnyCPU")
endif()

# TODO conditional for signing. we can then enable the ``Release_delaysign`` configuration

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/Microsoft.Z3.csproj.in ${CMAKE_CURRENT_BINARY_DIR}/build/Microsoft.Z3.csproj)
ADD_DOTNET(${CMAKE_CURRENT_BINARY_DIR}/build/Microsoft.Z3.csproj
    VERSION ${Z3_DOTNET_NUPKG_VERSION}
    PLATFORM ${Z3_DOTNET_PLATFORM}
    SOURCES ${CMAKE_CURRENT_SOURCE_DIR}/Microsoft.Z3.csproj.in 
            ${CMAKE_CURRENT_SOURCE_DIR}/Microsoft.Z3.props
            ${CMAKE_CURRENT_SOURCE_DIR}/Microsoft.Z3.targets
            ${Z3_DOTNET_ASSEMBLY_SOURCES}
    PACKAGE Microsoft.Z3
    PACK_ARGUMENTS "/p:_DN_CMAKE_CONFIG=$<CONFIG>"
    )
add_dependencies(BUILD_Microsoft.Z3 libz3)

# Convenient top-level target
add_custom_target(build_z3_dotnet_bindings ALL DEPENDS BUILD_Microsoft.Z3)

# Register the local nupkg repo
set(Z3_DOTNET_LOCALREPO_NAME "Microsoft Z3 Local Repository")
DOTNET_REGISTER_LOCAL_REPOSITORY(${Z3_DOTNET_LOCALREPO_NAME} ${PROJECT_BINARY_DIR})

###############################################################################
# Install: register a local nuget repo and install our package.
#          the build step depends on the 'purge' target, making sure that
#          a user will always restore the freshly-built package.
###############################################################################
option(Z3_INSTALL_DOTNET_BINDINGS "Install .NET bindings when invoking install target" ON)

if(Z3_INSTALL_DOTNET_BINDINGS)
    install(FILES "${PROJECT_BINARY_DIR}/Microsoft.Z3/Microsoft.Z3.${Z3_DOTNET_NUPKG_VERSION}.nupkg" DESTINATION "${CMAKE_INSTALL_LIBDIR}/z3.nuget")
    # move the local repo to the installation directory (cancel the build-time repo)
    install(CODE "include(${CMAKE_CURRENT_LIST_DIR}/../../../cmake/modules/FindDotnet.cmake)\n DOTNET_REGISTER_LOCAL_REPOSITORY(\"${Z3_DOTNET_LOCALREPO_NAME}\" \"${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_LIBDIR}/z3.nuget\")")
    install(FILES "${PROJECT_BINARY_DIR}/Microsoft.Z3/Microsoft.Z3.xml" DESTINATION "${CMAKE_INSTALL_LIBDIR}/z3.nuget")
# TODO GAC?
#  set(GAC_PKG_NAME "Microsoft.Z3.Sharp")
#  set(PREFIX "${CMAKE_INSTALL_PREFIX}")
#  set(VERSION "${Z3_VERSION}")
endif()

