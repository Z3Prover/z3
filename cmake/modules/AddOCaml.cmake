# CMake build rules for the OCaml language.
# Assumes FindOCaml is used.
# http://ocaml.org/
#
# Example usage:
#
# add_ocaml_library(pkg_a OCAML mod_a OCAMLDEP pkg_b C mod_a_stubs PKG ctypes LLVM core)
#
# Unnamed parameters:
#
#   * Library name.
#
# Named parameters:
#
# OCAML     OCaml module names. Imply presence of a corresponding .ml and .mli files.
# OCAML_GEN OCaml module name, implies presence of .ml IN TARGET DIRECTORY
# OCAMLDEP  Names of libraries this library depends on.
# C         C stub sources. Imply presence of a corresponding .c file.
# CFLAGS    Additional arguments passed when compiling C stubs.
# PKG       Names of ocamlfind packages this library depends on.
#

function(add_ocaml_library name)
    CMAKE_PARSE_ARGUMENTS(ARG "" "" "OCAML;OCAMLGEN;OCAMLDEP;C;CFLAGS;PKG" ${ARGN})

    set(src ${CMAKE_CURRENT_SOURCE_DIR})
    set(bin ${CMAKE_CURRENT_BINARY_DIR})

    set(sources)

    set(ocaml_inputs)

    set(ocaml_outputs "${bin}/${name}.cma")
    if( ARG_C )
        list(APPEND ocaml_outputs
             "${bin}/lib${name}${CMAKE_STATIC_LIBRARY_SUFFIX}"
             "${bin}/dll${name}${CMAKE_SHARED_LIBRARY_SUFFIX}")
    endif()
    if( HAVE_OCAMLOPT )
        list(APPEND ocaml_outputs
             "${bin}/${name}.cmxa"
             "${bin}/${name}${CMAKE_STATIC_LIBRARY_SUFFIX}")
    endif()

    set(ocaml_flags)
    foreach( ocaml_pkg ${ARG_PKG} )
        list(APPEND ocaml_flags "-package" "${ocaml_pkg}")
    endforeach()

    foreach( ocaml_dep ${ARG_OCAMLDEP} )
        get_target_property(dep_ocaml_flags "ocaml_${ocaml_dep}" OCAML_FLAGS)
        list(APPEND ocaml_flags ${dep_ocaml_flags})
    endforeach()

    foreach( ocaml_file ${ARG_OCAML} )
        list(APPEND sources "${ocaml_file}.mli" "${ocaml_file}.ml")

        list(APPEND ocaml_inputs "${bin}/${ocaml_file}.mli" "${bin}/${ocaml_file}.ml")

        list(APPEND ocaml_outputs "${bin}/${ocaml_file}.cmi" "${bin}/${ocaml_file}.cmo")
        if( HAVE_OCAMLOPT )
            list(APPEND ocaml_outputs
                 "${bin}/${ocaml_file}.cmx"
                 "${bin}/${ocaml_file}${CMAKE_C_OUTPUT_EXTENSION}")
        endif()
    endforeach()

    foreach( ocaml_file ${ARG_OCAMLGEN} )
        #list(APPEND sources "${ocaml_file}.mli" "${ocaml_file}.ml")

        list(APPEND ocaml_inputs "${bin}/${ocaml_file}.ml")

        list(APPEND ocaml_outputs "${bin}/${ocaml_file}.cmi" "${bin}/${ocaml_file}.cmo")
        if( HAVE_OCAMLOPT )
            list(APPEND ocaml_outputs
                 "${bin}/${ocaml_file}.cmx"
                 "${bin}/${ocaml_file}${CMAKE_C_OUTPUT_EXTENSION}")
        endif()
    endforeach()


    foreach( c_file ${ARG_C} )
        list(APPEND sources "${c_file}.c")

        list(APPEND c_inputs  "${bin}/${c_file}.c")
        list(APPEND c_outputs "${bin}/${c_file}${CMAKE_C_OUTPUT_EXTENSION}")
    endforeach()

    foreach( source ${sources} )
        add_custom_command(
            OUTPUT "${bin}/${source}"
            COMMAND "${CMAKE_COMMAND}" "-E" "copy" "${src}/${source}" "${bin}"
            DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/${source}"
            COMMENT "Copying ${source} to build area"
            VERBATIM)
    endforeach()

    foreach( c_input ${c_inputs} )
        get_filename_component(basename "${c_input}" NAME_WE)
        add_custom_command(
            OUTPUT "${basename}${CMAKE_C_OUTPUT_EXTENSION}"
            COMMAND "${OCAMLFIND}" "ocamlc" "-c" "${c_input}" -ccopt "${ARG_CFLAGS}"
            DEPENDS "${c_input}"
            COMMENT "Building OCaml stub object file ${basename}${CMAKE_C_OUTPUT_EXTENSION}"
            VERBATIM)
    endforeach()

    set(ocaml_params)
    foreach( ocaml_input ${ocaml_inputs} ${c_outputs})
        get_filename_component(filename "${ocaml_input}" NAME)
        list(APPEND ocaml_params "${filename}")
    endforeach()

    add_custom_command(
        OUTPUT ${ocaml_outputs}
        COMMAND "${OCAMLFIND}" "ocamlmklib" "-o" "${name}" ${ocaml_flags} ${ocaml_params}
        DEPENDS ${ocaml_inputs} ${c_outputs}
        COMMENT "Building OCaml library ${name}"
        VERBATIM)

    add_custom_target("ocaml_${name}" ALL DEPENDS ${ocaml_outputs})

    set_target_properties("ocaml_${name}" PROPERTIES
        OCAML_FLAGS "-I;${bin}")

    foreach( ocaml_dep ${ARG_OCAMLDEP} )
        add_dependencies("ocaml_${name}" "ocaml_${ocaml_dep}")
    endforeach()

    set(install_files)
    set(install_shlibs)
    foreach( ocaml_output ${ocaml_outputs} )
        get_filename_component(ext "${ocaml_output}" EXT)

        if( NOT (ext STREQUAL ".cmo" OR
                 ext STREQUAL CMAKE_C_OUTPUT_EXTENSION OR
                 ext STREQUAL CMAKE_SHARED_LIBRARY_SUFFIX) )
            list(APPEND install_files "${ocaml_output}")
        elseif( ext STREQUAL CMAKE_SHARED_LIBRARY_SUFFIX)
            list(APPEND install_shlibs "${ocaml_output}")
        endif()
    endforeach()

    install(FILES ${install_files}
            DESTINATION lib/ocaml)
    install(FILES ${install_shlibs}
            PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE
                        GROUP_READ GROUP_EXECUTE
                        WORLD_READ WORLD_EXECUTE
            DESTINATION lib/ocaml)

    message(STATUS ${CMAKE_SHARED_LIBRARY_SUFFIX})
endfunction()
