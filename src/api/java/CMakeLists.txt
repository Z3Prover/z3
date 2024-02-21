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
  COMMAND "${Python3_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--java-input-dir"
    "${CMAKE_CURRENT_SOURCE_DIR}"
    "--java-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
    "--java-package-name"
    ${Z3_JAVA_PACKAGE_NAME}
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${PROJECT_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
  COMMENT "Generating \"${Z3_JAVA_NATIVE_JAVA}\" and \"${Z3_JAVA_NATIVE_CPP}\""
  USES_TERMINAL
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
  COMMAND "${Python3_EXECUTABLE}"
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
  USES_TERMINAL
)

set(Z3_JAVA_JAR_SOURCE_FILES
  AlgebraicNum.java
  ApplyResult.java
  ArithExpr.java
  ArithSort.java
  ArrayExpr.java
  ArraySort.java
  AST.java
  ASTMap.java
  ASTVector.java
  BitVecExpr.java
  BitVecNum.java
  BitVecSort.java
  BoolExpr.java
  BoolSort.java
  CharSort.java
  Constructor.java
  ConstructorList.java
  Context.java
  DatatypeExpr.java
  DatatypeSort.java
  EnumSort.java
  Expr.java
  FiniteDomainExpr.java
  FiniteDomainNum.java
  FiniteDomainSort.java
  Fixedpoint.java
  FPExpr.java
  FPNum.java
  FPRMExpr.java
  FPRMNum.java
  FPRMSort.java
  FPSort.java
  FuncDecl.java
  FuncInterp.java
  Global.java
  Goal.java
  IntExpr.java
  IntNum.java
  IntSort.java
  IntSymbol.java
  Lambda.java
  ListSort.java
  Log.java
  Model.java
  Optimize.java
  ParamDescrs.java
  Params.java
  Pattern.java
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
  Simplifier.java
  Solver.java
  Sort.java
  Statistics.java
  Status.java
  StringSymbol.java
  Symbol.java
  Tactic.java
  TupleSort.java
  UninterpretedSort.java
  UserPropagatorBase.java
  Version.java
  Z3Exception.java
  Z3Object.java
  Z3ReferenceQueue.java
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
# REMARK: removed VERSION to fix issue with using this to create installations.

add_jar(z3JavaJar
  SOURCES ${Z3_JAVA_JAR_SOURCE_FILES_FULL_PATH}
  OUTPUT_NAME ${Z3_JAVA_PACKAGE_NAME}
  OUTPUT_DIR "${PROJECT_BINARY_DIR}"
# VERSION "${Z3_VERSION}"
)

###############################################################################
# Install
###############################################################################
option(Z3_INSTALL_JAVA_BINDINGS "Install Java bindings when invoking install target" ON)
if (Z3_INSTALL_JAVA_BINDINGS)
  # Provide cache variables for the install locations that the user can change.
  # This defaults to ``/usr/local/java`` which seems to be the location for ``.jar``
  # files on Linux distributions
  if (NOT Z3_JAVA_JAR_INSTALLDIR)
     set(Z3_JAVA_JAR_INSTALLDIR
       "${CMAKE_INSTALL_DATAROOTDIR}/java"
       CACHE
       PATH
       "Directory to install Z3 Java jar file relative to install prefix"
     )
  endif()
  if (NOT Z3_JAVA_JNI_LIB_INSTALLDIR)
    set(Z3_JAVA_JNI_LIB_INSTALLDIR
       "${CMAKE_INSTALL_LIBDIR}"
       CACHE
       PATH
       "Directory to install Z3 Java JNI bridge library relative to install prefix"
     )
  endif()
  install(TARGETS z3java DESTINATION "${Z3_JAVA_JNI_LIB_INSTALLDIR}")
  install_jar(z3JavaJar "${Z3_JAVA_JAR_INSTALLDIR}")
endif()
