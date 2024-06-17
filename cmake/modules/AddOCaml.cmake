# Copied from https://github.com/llvm/llvm-project/tree/main/llvm/cmake/modules/AddOCaml.cmake
# Modified by arbipher at 05/2024
#
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
# OCAMLDEP  Names of libraries this library depends on.
# C         C stub sources. Imply presence of a corresponding .c file.
# INCLUDES  Path for header files for C sources.
# CFLAGS    Additional arguments passed when compiling C stubs.
# PKG       Names of ocamlfind packages this library depends on.
# LLVM      Names of LLVM libraries this library depends on.
# GEN       Generated files. Do not need to copy.
# NOCOPY    Do not automatically copy sources (.c, .ml, .mli) from the source directory,
#           e.g. if they are generated.
#

function(add_ocaml_library name)
  ## Argument Setting ##

  # CMAKE_PARSE_ARGUMENTS(ARG "NOCOPY" "" "OCAML;OCAMLDEP;C;CFLAGS;PKG;LLVM" ${ARGN})
  CMAKE_PARSE_ARGUMENTS(ARG "NOCOPY" "" "OCAML;OCAMLDEP;C;CFLAGS;PKG;GEN" ${ARGN})

  set(src ${CMAKE_CURRENT_SOURCE_DIR})
  set(bin ${CMAKE_CURRENT_BINARY_DIR})

  # TODO: incorrect
  set(ocaml_pkgs)
  foreach( ocaml_pkg ${ARG_PKG} )
    list(APPEND ocaml_pkgs "-package" "${ocaml_pkg}")
  endforeach()

  set(sources)

  set(ocaml_inputs)

  set(ocaml_outputs "${bin}/${name}.cma")
  if( ARG_C )
    list(APPEND ocaml_outputs
         "${bin}/lib${name}${CMAKE_STATIC_LIBRARY_SUFFIX}")
    if ( BUILD_SHARED_LIBS )
      list(APPEND ocaml_outputs
           "${bin}/dll${name}${CMAKE_SHARED_LIBRARY_SUFFIX}")
    endif()
  endif()
  if( HAVE_OCAMLOPT )
    list(APPEND ocaml_outputs
         "${bin}/${name}.cmxa"
         "${bin}/${name}${CMAKE_STATIC_LIBRARY_SUFFIX}")
  endif()

  set(ocaml_flags "-lstdc++" "-ldopt" "-L${LLVM_LIBRARY_DIR}"
                  "-ccopt" "-L\\$CAMLORIGIN/../.."
                  "-ccopt" "-Wl,-rpath,\\$CAMLORIGIN/../.."
                  ${ocaml_pkgs})

  foreach( ocaml_dep ${ARG_OCAMLDEP} )
    get_target_property(dep_ocaml_flags "ocaml_${ocaml_dep}" OCAML_FLAGS)
    list(APPEND ocaml_flags ${dep_ocaml_flags})
  endforeach()

  if( NOT BUILD_SHARED_LIBS )
    list(APPEND ocaml_flags "-custom")
  endif()

  # if(LLVM_LINK_LLVM_DYLIB)
  #   list(APPEND ocaml_flags "-lLLVM")
  # else()
    # explicit_map_components_to_libraries(llvm_libs ${ARG_LLVM})
    # foreach( llvm_lib ${llvm_libs} )
    #   list(APPEND ocaml_flags "-l${llvm_lib}" )
    # endforeach()

    # get_property(system_libs TARGET LLVMSupport PROPERTY LLVM_SYSTEM_LIBS)
    # foreach(system_lib ${system_libs})
    #   if (system_lib MATCHES "^-")
    #     # If it's an option, pass it without changes.
    #     list(APPEND ocaml_flags "${system_lib}" )
    #   else()
    #     # Otherwise assume it's a library name we need to link with.
    #     list(APPEND ocaml_flags "-l${system_lib}" )
    #   endif()
    # endforeach()
  # endif()

  string(REPLACE ";" " " ARG_CFLAGS "${ARG_CFLAGS}")
  set(c_flags "${ARG_CFLAGS} ${LLVM_DEFINITIONS}")
  foreach( include_dir ${LLVM_INCLUDE_DIR} ${LLVM_MAIN_INCLUDE_DIR} )
    set(c_flags "${c_flags} -I${include_dir}")
  endforeach()
  # include -D/-UNDEBUG to match dump function visibility
  # regex from HandleLLVMOptions.cmake
  string(REGEX MATCH "(^| )[/-][UD] *NDEBUG($| )" flag_matches
         "${CMAKE_C_FLAGS_${uppercase_CMAKE_BUILD_TYPE}} ${CMAKE_C_FLAGS}")
  set(c_flags "${c_flags} ${flag_matches}")

  foreach( ocaml_file ${ARG_OCAML} )
    
    if (EXISTS "${bin}/${ocaml_file}.mli")
      list(APPEND sources "${ocaml_file}.mli")
    else()
      add_custom_command(
        OUTPUT "${bin}/${ocaml_file}.mli"
        COMMAND "${OCAMLFIND}" "ocamlc" "${ocaml_pkgs}" "-i" "-I" "${bin}" "-c" "${bin}/${ocaml_file}.ml" ">" "${bin}/${ocaml_file}.mli"
        DEPENDS "${bin}/${ocaml_file}.ml"
        COMMENT "Building OCaml mli file if non-exist"
        VERBATIM)
    endif()

    list(APPEND sources "${ocaml_file}.ml")

    list(APPEND ocaml_inputs "${bin}/${ocaml_file}.mli" "${bin}/${ocaml_file}.ml")

    list(APPEND ocaml_outputs "${bin}/${ocaml_file}.cmi" "${bin}/${ocaml_file}.cmo")

        list(APPEND ocaml_outputs "${bin}/${ocaml_file}.cmti" "${bin}/${ocaml_file}.cmt")

    if( HAVE_OCAMLOPT )
      list(APPEND ocaml_outputs
           "${bin}/${ocaml_file}.cmx"
          #  "${bin}/${ocaml_file}.o"
           )
    endif()

  endforeach()


  ## Compiling ML files ##

  foreach( c_file ${ARG_C} )
    list(APPEND sources "${c_file}.c")

    list(APPEND c_inputs  "${bin}/${c_file}.c")
    list(APPEND c_outputs "${bin}/${c_file}.o")
  endforeach()

  if( NOT ARG_NOCOPY )
    foreach( source ${sources} )
      if (NOT "${bin}/${source}" IN_LIST ARG_GEN)
        add_custom_command(
            OUTPUT "${bin}/${source}"
            COMMAND "${CMAKE_COMMAND}" "-E" "copy" "${src}/${source}" "${bin}"
            DEPENDS "${src}/${source}"
            COMMENT "Copying ${source} to build area")
      endif()
    endforeach()
  endif()

  ## Compiling C Stub ##

  foreach( c_input ${c_inputs} )
    get_filename_component(basename "${c_input}" NAME_WE)
    add_custom_command(
      OUTPUT "${bin}/${basename}.o"
      COMMAND "${OCAMLFIND}" "ocamlc" "-o" "${bin}/${basename}.o" "-c" "${c_input}" -ccopt ${c_flags}
      DEPENDS "${c_input}"
      COMMENT "Building OCaml stub object file ${bin}/${basename}.o"
      VERBATIM)
  endforeach()

  ## Setting linking argument and run mklib ##

  set(ocaml_params)
  foreach( ocaml_input ${ocaml_inputs} ${c_outputs})
    get_filename_component(filename "${ocaml_input}" NAME)
    list(APPEND ocaml_params "${filename}")
  endforeach()

  if( APPLE )
    set(ocaml_rpath "@executable_path/../../../lib${LLVM_LIBDIR_SUFFIX}")
  elseif( UNIX )
    set(ocaml_rpath "\\$ORIGIN/../../../lib${LLVM_LIBDIR_SUFFIX}")
  endif()
  list(APPEND ocaml_flags "-ldopt" "-Wl,-rpath,${ocaml_rpath}")

  add_custom_command(
    OUTPUT ${ocaml_outputs}
    COMMAND "${OCAMLFIND}" "ocamlmklib" "-ocamlcflags" "-bin-annot"
      "-o" "${name}" ${ocaml_flags} ${ocaml_params}
    DEPENDS ${ocaml_inputs} ${c_outputs}
    COMMENT "Building OCaml library ${name}"
    VERBATIM)

  ## Build document

  add_custom_command(
    OUTPUT "${bin}/${name}.odoc"
    COMMAND "${OCAMLFIND}" "ocamldoc"
            "-I" "${bin}"
            "-I" "${LLVM_LIBRARY_DIR}/ocaml/llvm/"
            "-dump" "${bin}/${name}.odoc"
            ${ocaml_pkgs} ${ocaml_inputs}
    DEPENDS ${ocaml_inputs} ${ocaml_outputs}
    COMMENT "Building OCaml documentation for ${name}"
    VERBATIM)

  add_custom_target("ocaml_${name}" ALL DEPENDS ${ocaml_outputs} "${bin}/${name}.odoc")

  set_target_properties("ocaml_${name}" PROPERTIES
    OCAML_FLAGS "-I;${bin}")
  set_target_properties("ocaml_${name}" PROPERTIES
    OCAML_ODOC "${bin}/${name}.odoc")

  ## Setting dependencies

  foreach( ocaml_dep ${ARG_OCAMLDEP} )
    add_dependencies("ocaml_${name}" "ocaml_${ocaml_dep}")
  endforeach()

  if( NOT LLVM_OCAML_OUT_OF_TREE )
    foreach( llvm_lib ${llvm_libs} )
      add_dependencies("ocaml_${name}" "${llvm_lib}")
    endforeach()
  endif()

  ## Configurating installation

  set(install_files)
  set(install_shlibs)
  foreach( ocaml_output ${ocaml_inputs} ${ocaml_outputs} )
    get_filename_component(ext "${ocaml_output}" EXT)

    if( NOT (ext STREQUAL ".cmo" OR
             ext STREQUAL ".ml" OR
             ext STREQUAL ".o" OR
             ext STREQUAL CMAKE_SHARED_LIBRARY_SUFFIX) )
      list(APPEND install_files "${ocaml_output}")
    elseif( ext STREQUAL CMAKE_SHARED_LIBRARY_SUFFIX)
      list(APPEND install_shlibs "${ocaml_output}")
    endif()
  endforeach()

  install(FILES ${install_files}
          DESTINATION "${LLVM_OCAML_INSTALL_PATH}/llvm")
  install(FILES ${install_shlibs}
          PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE
                      GROUP_READ GROUP_EXECUTE
                      WORLD_READ WORLD_EXECUTE
          DESTINATION "${LLVM_OCAML_INSTALL_PATH}/stublibs")

  foreach( install_file ${install_files} ${install_shlibs} )
    get_filename_component(filename "${install_file}" NAME)
    add_custom_command(TARGET "ocaml_${name}" POST_BUILD
      COMMAND "${CMAKE_COMMAND}" "-E" "copy" "${install_file}"
                                             "${LLVM_LIBRARY_DIR}/ocaml/llvm/"
      COMMENT "Copying OCaml library component ${filename} to intermediate area"
      VERBATIM)
    add_dependencies("ocaml_${name}" ocaml_make_directory)
  endforeach()
endfunction()

# add_custom_target(ocaml_make_directory
#   COMMAND "${CMAKE_COMMAND}" "-E" "make_directory" "${LLVM_LIBRARY_DIR}/ocaml/llvm")
add_custom_target("ocaml_make_directory")
# add_custom_target("ocaml_all")
# set_target_properties(ocaml_all PROPERTIES FOLDER "Misc")
# set_target_properties(ocaml_make_directory PROPERTIES FOLDER "Misc")
