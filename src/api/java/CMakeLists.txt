find_package(Java REQUIRED)
find_package(JNI REQUIRED)
include(UseJava)

# Sanity check for dirty source tree
foreach (file_name "enumerations" "Native.cpp" "Native.java")
  if (EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${file_name}")
    message(FATAL_ERROR "\"${CMAKE_CURRENT_SOURCE_DIR}/${file_name}\""
            ${z3_polluted_tree_msg})
  endif()
endforeach()

set(Z3_JAVA_PACKAGE_NAME "com.microsoft.z3")

# Rule to generate ``Native.java`` and ``Native.cpp``
set(Z3_JAVA_NATIVE_JAVA "${CMAKE_CURRENT_BINARY_DIR}/Native.java")
set(Z3_JAVA_NATIVE_CPP "${CMAKE_CURRENT_BINARY_DIR}/Native.cpp")
add_custom_command(OUTPUT "${Z3_JAVA_NATIVE_JAVA}" "${Z3_JAVA_NATIVE_CPP}"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--java-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
    "--java-package-name"
    ${Z3_JAVA_PACKAGE_NAME}
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${PROJECT_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
    # FIXME: When update_api.py no longer uses ``mk_util`` drop this dependency
    "${PROJECT_SOURCE_DIR}/scripts/mk_util.py"
  COMMENT "Generating \"${Z3_JAVA_NATIVE_JAVA}\" and \"${Z3_JAVA_NATIVE_CPP}\""
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)

# Add rule to build native code that provides a bridge between
# ``Native.java`` and libz3's interfac3.
add_library(z3java SHARED ${Z3_JAVA_NATIVE_CPP})
target_link_libraries(z3java PRIVATE libz3)
# FIXME:
# Not sure if using all the flags used by the Z3 components is really necessary
# here. The Python build system uses all the flags used for building
# Z3's components to build ``Native.cpp`` lets do the same for now.
target_compile_options(z3java PRIVATE ${Z3_COMPONENT_CXX_FLAGS})
target_compile_definitions(z3java PRIVATE ${Z3_COMPONENT_CXX_DEFINES})
target_include_directories(z3java PRIVATE
  "${PROJECT_SOURCE_DIR}/src/api"
  "${PROJECT_BINARY_DIR}/src/api"
  ${JNI_INCLUDE_DIRS}
)
# FIXME: Should this library have SONAME and VERSION set?

# This prevents CMake from automatically defining ``z3java_EXPORTS``
set_property(TARGET z3java PROPERTY DEFINE_SYMBOL "")

# Rule to generate the ``com.microsoft.z3.enumerations`` package
# FIXME: This list of files is fragile
set(Z3_JAVA_ENUMERATION_PACKAGE_FILES
  Z3_ast_kind.java
  Z3_ast_print_mode.java
  Z3_decl_kind.java
  Z3_error_code.java
  Z3_goal_prec.java
  Z3_lbool.java
  Z3_param_kind.java
  Z3_parameter_kind.java
  Z3_sort_kind.java
  Z3_symbol_kind.java
)
set(Z3_JAVA_ENUMERATION_PACKAGE_FILES_FULL_PATH "")
foreach (enum_file ${Z3_JAVA_ENUMERATION_PACKAGE_FILES})
  list(APPEND Z3_JAVA_ENUMERATION_PACKAGE_FILES_FULL_PATH
    "${CMAKE_CURRENT_BINARY_DIR}/enumerations/${enum_file}"
  )
endforeach()
add_custom_command(OUTPUT ${Z3_JAVA_ENUMERATION_PACKAGE_FILES_FULL_PATH}
  COMMAND "${PYTHON_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/mk_consts_files.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--java-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
    "--java-package-name"
    ${Z3_JAVA_PACKAGE_NAME}
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${PROJECT_SOURCE_DIR}/scripts/mk_consts_files.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
  COMMENT "Generating ${Z3_JAVA_PACKAGE_NAME}.enumerations package"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)

set(Z3_JAVA_JAR_SOURCE_FILES
  AlgebraicNum.java
  ApplyResultDecRefQueue.java
  ApplyResult.java
  ArithExpr.java
  ArithSort.java
  ArrayExpr.java
  ArraySort.java
  ASTDecRefQueue.java
  AST.java
  AstMapDecRefQueue.java
  ASTMap.java
  AstVectorDecRefQueue.java
  ASTVector.java
  BitVecExpr.java
  BitVecNum.java
  BitVecSort.java
  BoolExpr.java
  BoolSort.java
  ConstructorDecRefQueue.java
  Constructor.java
  ConstructorListDecRefQueue.java
  ConstructorList.java
  Context.java
  DatatypeExpr.java
  DatatypeSort.java
  EnumSort.java
  Expr.java
  FiniteDomainExpr.java
  FiniteDomainNum.java
  FiniteDomainSort.java
  FixedpointDecRefQueue.java
  Fixedpoint.java
  FPExpr.java
  FPNum.java
  FPRMExpr.java
  FPRMNum.java
  FPRMSort.java
  FPSort.java
  FuncDecl.java
  FuncInterpDecRefQueue.java
  FuncInterpEntryDecRefQueue.java
  FuncInterp.java
  Global.java
  GoalDecRefQueue.java
  Goal.java
  IDecRefQueue.java
  IntExpr.java
  IntNum.java
  IntSort.java
  IntSymbol.java
  Lambda.java
  ListSort.java
  Log.java
  ModelDecRefQueue.java
  Model.java
  OptimizeDecRefQueue.java
  Optimize.java
  ParamDescrsDecRefQueue.java
  ParamDescrs.java
  ParamsDecRefQueue.java
  Params.java
  Pattern.java
  ProbeDecRefQueue.java
  Probe.java
  Quantifier.java
  RatNum.java
  RealExpr.java
  RealSort.java
  ReExpr.java
  RelationSort.java
  ReSort.java
  SeqExpr.java
  SeqSort.java
  SetSort.java
  SolverDecRefQueue.java
  Solver.java
  Sort.java
  StatisticsDecRefQueue.java
  Statistics.java
  Status.java
  StringSymbol.java
  Symbol.java
  TacticDecRefQueue.java
  Tactic.java
  TupleSort.java
  UninterpretedSort.java
  Version.java
  Z3Exception.java
  Z3Object.java
)
set(Z3_JAVA_JAR_SOURCE_FILES_FULL_PATH "")
foreach (java_src_file ${Z3_JAVA_JAR_SOURCE_FILES})
  list(APPEND Z3_JAVA_JAR_SOURCE_FILES_FULL_PATH "${CMAKE_CURRENT_SOURCE_DIR}/${java_src_file}")
endforeach()
# Add generated files to list
list(APPEND Z3_JAVA_JAR_SOURCE_FILES_FULL_PATH
  ${Z3_JAVA_NATIVE_JAVA}
  ${Z3_JAVA_ENUMERATION_PACKAGE_FILES_FULL_PATH}
)

# Convenient top-level target
add_custom_target(build_z3_java_bindings
  ALL
  DEPENDS
    z3java
    z3JavaJar
)

# Rule to build ``com.microsoft.z3.jar``
# TODO: Should we set ``CMAKE_JNI_TARGET`` to ``TRUE``?
add_jar(z3JavaJar
  SOURCES ${Z3_JAVA_JAR_SOURCE_FILES_FULL_PATH}
  OUTPUT_NAME ${Z3_JAVA_PACKAGE_NAME}
  OUTPUT_DIR "${PROJECT_BINARY_DIR}"
  VERSION "${Z3_VERSION}"
)

###############################################################################
# Install
###############################################################################
option(INSTALL_JAVA_BINDINGS "Install Java bindings when invoking install target" ON)
if (INSTALL_JAVA_BINDINGS)
  # Provide cache variables for the install locations that the user can change.
  # This defaults to ``/usr/local/java`` which seems to be the location for ``.jar``
  # files on Linux distributions
  set(Z3_JAVA_JAR_INSTALLDIR
    "${CMAKE_INSTALL_DATAROOTDIR}/java"
    CACHE
    PATH
    "Directory to install Z3 Java jar file relative to install prefix"
  )
  # FIXME: I don't think this the right installation location
  set(Z3_JAVA_JNI_LIB_INSTALLDIR
    "${CMAKE_INSTALL_LIBDIR}"
    CACHE
    PATH
    "Directory to install Z3 Java JNI bridge library relative to install prefix"
  )
  install(TARGETS z3java DESTINATION "${Z3_JAVA_JNI_LIB_INSTALLDIR}")
  # Note: Don't use ``DESTINATION`` here as the version of ``UseJava.cmake`` shipped
  # with CMake 2.8.12.2 handles that incorrectly.
  install_jar(z3JavaJar "${Z3_JAVA_JAR_INSTALLDIR}")
endif()
