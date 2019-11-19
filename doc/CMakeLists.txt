find_package(Doxygen REQUIRED)
message(STATUS "DOXYGEN_EXECUTABLE: \"${DOXYGEN_EXECUTABLE}\"")
message(STATUS "DOXYGEN_VERSION: \"${DOXYGEN_VERSION}\"")

set(DOC_DEST_DIR "${CMAKE_CURRENT_BINARY_DIR}/api")
set(DOC_TEMP_DIR "${CMAKE_CURRENT_BINARY_DIR}/temp")
set(MK_API_DOC_SCRIPT "${CMAKE_CURRENT_SOURCE_DIR}/mk_api_doc.py")

set(PYTHON_API_OPTIONS "")
set(DOTNET_API_OPTIONS "")
set(JAVA_API_OPTIONS "")
SET(DOC_EXTRA_DEPENDS "")

if (BUILD_PYTHON_BINDINGS)
  # FIXME: Don't hard code this path
  list(APPEND PYTHON_API_OPTIONS "--z3py-package-path" "${PROJECT_BINARY_DIR}/python/z3")
  list(APPEND DOC_EXTRA_DEPENDS "build_z3_python_bindings")
else()
  list(APPEND PYTHON_API_OPTIONS "--no-z3py")
endif()

if (BUILD_DOTNET_BINDINGS)
  # FIXME: Don't hard code these paths
  list(APPEND DOTNET_API_OPTIONS "--dotnet-search-paths"
    "${PROJECT_SOURCE_DIR}/src/api/dotnet"
    "${PROJECT_BINARY_DIR}/src/api/dotnet"
  )
  list(APPEND DOC_EXTRA_DEPENDS "build_z3_dotnet_bindings")
else()
  list(APPEND DOTNET_API_OPTIONS "--no-dotnet")
endif()

if (BUILD_JAVA_BINDINGS)
  # FIXME: Don't hard code these paths
  list(APPEND JAVA_API_OPTIONS "--java-search-paths"
    "${PROJECT_SOURCE_DIR}/src/api/java"
    "${PROJECT_BINARY_DIR}/src/api/java"
  )
  list(APPEND DOC_EXTRA_DEPENDS "build_z3_java_bindings")
else()
  list(APPEND JAVA_API_OPTIONS "--no-java")
endif()

option(Z3_ALWAYS_BUILD_DOCS "Always build documentation for API bindings" ON)
if (Z3_ALWAYS_BUILD_DOCS)
  set(ALWAYS_BUILD_DOCS_ARG "ALL")
else()
  set(ALWAYS_BUILD_DOCS_ARG "")
  # FIXME: This sucks but there doesn't seem to be a way to make the top level
  # install target depend on the `api_docs` target.
  message(WARNING "Building documentation for API bindings is not part of the"
    " all target. This may result in stale files being installed when running"
    " the install target. You should run the api_docs target before running"
    " the install target. Alternatively Set Z3_ALWAYS_BUILD_DOCS to ON to"
    " automatically build documentation when running the install target."
  )
endif()

add_custom_target(api_docs ${ALWAYS_BUILD_DOCS_ARG}
  COMMAND
  "${PYTHON_EXECUTABLE}" "${MK_API_DOC_SCRIPT}"
  --build "${PROJECT_BINARY_DIR}"
  --doxygen-executable "${DOXYGEN_EXECUTABLE}"
  --output-dir "${DOC_DEST_DIR}"
  --temp-dir "${DOC_TEMP_DIR}"
  ${PYTHON_API_OPTIONS}
  ${DOTNET_API_OPTIONS}
  ${JAVA_API_OPTIONS}
  DEPENDS
    ${DOC_EXTRA_DEPENDS}
  COMMENT "Generating documentation"
  ${ADD_CUSTOM_TARGET_USES_TERMINAL_ARG}
)

# Remove generated documentation when running `clean` target.
set_property(DIRECTORY APPEND PROPERTY
  ADDITIONAL_MAKE_CLEAN_FILES
  "${DOC_DEST_DIR}"
)

option(Z3_INSTALL_API_BINDINGS_DOCUMENTATION "Install documentation for API bindings" ON)
set(CMAKE_INSTALL_API_BINDINGS_DOC
  "${CMAKE_INSTALL_DOCDIR}"
  CACHE
  PATH
  "Path to install documentation for API bindings"
)
if (Z3_INSTALL_API_BINDINGS_DOCUMENTATION)
  install(
    DIRECTORY "${DOC_DEST_DIR}"
    DESTINATION "${CMAKE_INSTALL_API_BINDINGS_DOC}"
  )
endif()
