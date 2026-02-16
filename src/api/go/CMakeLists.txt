# Z3 Go API

# Note: This CMakeLists.txt is a placeholder for Go binding integration.
# Go bindings use CGO and are typically built using the Go toolchain directly.
# However, we can set up installation targets here.

if(Z3_BUILD_GO_BINDINGS)
    message(STATUS "Z3 Go bindings will be installed")
    
    # Install Go source files
    install(FILES
        ${CMAKE_CURRENT_SOURCE_DIR}/z3.go
        ${CMAKE_CURRENT_SOURCE_DIR}/solver.go
        ${CMAKE_CURRENT_SOURCE_DIR}/go.mod
        ${CMAKE_CURRENT_SOURCE_DIR}/README.md
        DESTINATION "${CMAKE_INSTALL_LIBDIR}/go/src/github.com/Z3Prover/z3/go"
    )
    
    # On Windows, we need to ensure the DLL is accessible
    if(WIN32)
        message(STATUS "Go bindings on Windows require libz3.dll in PATH")
    endif()
    
    # Add a custom target to test Go bindings if Go is available
    find_program(GO_EXECUTABLE go)
    if(GO_EXECUTABLE)
        message(STATUS "Found Go: ${GO_EXECUTABLE}")
        
        # Custom target to build Go bindings
        set(CGO_LDFLAGS_VALUE "-L${CMAKE_BINARY_DIR} -lz3")
        add_custom_target(go-bindings
            COMMAND ${CMAKE_COMMAND} -E env
                CGO_CFLAGS=-I${CMAKE_SOURCE_DIR}/src/api
                CGO_LDFLAGS=${CGO_LDFLAGS_VALUE}
                ${GO_EXECUTABLE} build -v
            WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
            COMMENT "Building Go bindings"
            DEPENDS libz3
            VERBATIM
        )
        
        # Custom target to test Go examples
        add_custom_target(test-go-examples
            COMMAND ${CMAKE_COMMAND} -E env
                CGO_CFLAGS=-I${CMAKE_SOURCE_DIR}/src/api
                CGO_LDFLAGS=${CGO_LDFLAGS_VALUE}
                LD_LIBRARY_PATH=${CMAKE_BINARY_DIR}:$ENV{LD_LIBRARY_PATH}
                PATH=${CMAKE_BINARY_DIR}$<SEMICOLON>$ENV{PATH}
                ${GO_EXECUTABLE} run basic_example.go
            WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/examples/go
            COMMENT "Running Go examples"
            DEPENDS libz3
            VERBATIM
        )
    else()
        message(STATUS "Go not found - Go bindings can be built manually")
    endif()
endif()
