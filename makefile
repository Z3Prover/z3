# ${PROJECT_SOURCE_DIR}:       /vendor/z3
# ${PROJECT_BINARY_DIR}:       /vendor/z3/build
# ${CMAKE_CURRENT_SOURCE_DIR}: /vendor/z3/src/api/ml
# ${CMAKE_CURRENT_BINARY_DIR}: /vendor/z3/build/src/api/ml

# TODO: add `-bin-annot` to more `ocamlc`
# Question: who will set `CAMLORIGIN`
# - 	-dllpath $$CAMLORIGIN/../.. \
# Q: is `ocamlmklib -ldopt -Lfoo` the same as `ocamlmklib -Lfoo`
# it doesn't looks right (item 4)
#    https://www.ocaml.org/manual/5.2/runtime.html#s:ocamlrun-dllpath
#
# if external libz3 is given, no files should be build
# 
# find_program(OCAMLFIND
#              NAMES ocamlfind)
# find_library(ocaml)
# include(FindOCaml)
# Todo: use DEPFILE in https://cmake.org/cmake/help/latest/command/add_custom_command.html

# Generate ``z3native.ml`` and ``z3native_stubs.c``

# set(z3ml_generated_files
#   "${z3ml_bin}/z3native.ml"
#   "${z3ml_bin}/z3native_stubs.c"
#   "${z3ml_enums_ml}"
# )

# add_custom_target(ocaml_generated DEPENDS
#   ${z3ml_generated_files}
# )

# add_custom_command(
#   OUTPUT "${z3ml_bin}/z3enums.mli"
#   COMMAND "${OCAMLFIND}" "ocamlc" 
#           "-package" "zarith"
#           "-i" 
#           "-I" "${z3ml_bin}"
#           "-c" "${z3ml_bin}/z3enums.ml"
#           ">" "${z3ml_bin}/z3enums.mli"
#   DEPENDS "${z3ml_enums_ml}"
#   COMMENT "Building z3enums.mli"
#   VERBATIM)

# "-ldopt"
# "-ccopt" "-L\\$CAMLORIGIN/../.."
# "-ccopt" "-Wl,-rpath,\\$CAMLORIGIN/../.."

# add_custom_command(
#   OUTPUT "${z3ml_bin}/z3native.cmx"
#   COMMAND "${OCAMLFIND}" "ocamlopt" 
#           "-package" "zarith"
#           "-I" "${z3ml_bin}"
#           "-c" "${z3ml_bin}/z3native.ml"
#   DEPENDS "${z3ml_bin}/z3enums.cmo"
#           "${z3ml_bin}/z3native.mli"
#           "${z3ml_bin}/z3native.cmi"
#           "${z3ml_bin}/z3native.ml"
#   COMMENT "Building z3native.cmx"
#   VERBATIM)

# add_custom_command(
#   OUTPUT "${z3ml_bin}/z3enums.cmo"
#   COMMAND "${OCAMLFIND}" "ocamlc" 
#           "-package" "zarith"
#           "-I" "${z3ml_bin}"
#           "-c" "${z3ml_bin}/z3enums.ml"
#   DEPENDS "${z3ml_enums_ml}"
#   COMMENT "Building z3enums.cmo"
#   VERBATIM)

# add_custom_command(
#   OUTPUT "${z3ml_bin}/z3native.mli"
#   COMMAND "${OCAMLFIND}" "ocamlc" 
#           "-package" "zarith"
#           "-i" 
#           "-I" "${z3ml_bin}"
#           "-c" "${z3ml_bin}/z3native.ml"
#           ">" "${z3ml_bin}/z3native.mli"
#   DEPENDS "${z3ml_enums_ml}"
#           "${z3ml_bin}/z3enums.cmo"
#           "${z3ml_bin}/z3native.ml"
#   COMMENT "Building z3native.mli"
#   VERBATIM)

# add_custom_command(
#   OUTPUT "${z3ml_bin}/z3.cmx"
#   COMMAND "${OCAMLFIND}" "ocamlopt" ${z3ml_common_flags}
#           "-c" "${z3ml_bin}/z3.ml"  
#   DEPENDS "${z3ml_bin}/z3enums.cmo"
#           "${z3ml_bin}/z3native.cmo"
#           "${z3ml_bin}/z3.ml"
#           "${z3ml_bin}/z3.mli"
#           "${z3ml_bin}/z3.cmi"
#   COMMENT "Building z3.cmx"
#   VERBATIM)

# add_custom_command(
#   OUTPUT "${z3ml_bin}/z3ml.cmxa"
#   COMMAND "${OCAMLFIND}" "ocamlmklib"
#     "-o" z3ml
#     ${ocamlmklib_flags}
#     "-I" "${z3ml_bin}"
#     "${z3ml_bin}/z3enums.cmx"
#     "${z3ml_bin}/z3native.cmx"
#     "${z3ml_bin}/z3native_stubs.o"
#     "${z3ml_bin}/z3.cmx"
#   DEPENDS
#     libz3
#     "${z3ml_bin}/z3enums.cmx"
#     "${z3ml_bin}/z3native.cmx"
#     "${z3ml_bin}/z3native_stubs.o"
#     "${z3ml_bin}/z3.cmx"
#   COMMENT "Building OCaml library ${name}"
#   VERBATIM)
# add_custom_command(
#   OUTPUT "${z3ml_bin}/z3ml.cmxs"
#   COMMAND "${OCAMLFIND}" "ocamlopt" "-linkall" "-shared"
#     "-o" "${z3ml_bin}/z3ml.cmxs"
#     "-I" "."
#     "-I" "${z3ml_bin}"
#     "${z3ml_bin}/z3ml.cmxa"
#   DEPENDS
#     "${z3ml_bin}/z3ml.cmxa"
#   COMMENT "Building OCaml library ${name}"
#   VERBATIM)

#          "${z3ml_bin}/z3enums.cmi"


ml0:
	mkdir -p build
	cd build && cmake -G "Ninja" \
	-DZ3_BUILD_LIBZ3_SHARED=TRUE \
	-DZ3_BUILD_OCAML_BINDINGS=TRUE \
	../

# -DGRAPHVIZ_EXECUTABLES=FALSE \
# -DGRAPHVIZ_INTERFACE_LIBS=FALSE \
# --graphviz=deps.dot \

ml-inner-mk:
	mkdir -p build
	cd build && cmake \
	-DCMAKE_VERBOSE_MAKEFILE=TRUE \
	-DZ3_BUILD_LIBZ3_SHARED=TRUE \
	-DZ3_BUILD_OCAML_BINDINGS=TRUE \
	-DZ3_BUILD_PYTHON_BINDINGS=TRUE \
	--debug-trycompile \
	../

ml-mk:
	mkdir -p build
	cd build && cmake \
	-DCMAKE_VERBOSE_MAKEFILE=TRUE \
	-DZ3_BUILD_LIBZ3_SHARED=TRUE \
	-DZ3_BUILD_OCAML_BINDINGS=TRUE \
	-DZ3_BUILD_OCAML_EXTERNAL_LIBZ3=/home/ex/my_z3 \
	--debug-trycompile \
	../

ml-inner:
	mkdir -p build
	cd build && cmake \
	-G "Ninja" \
	-DCMAKE_VERBOSE_MAKEFILE=TRUE \
	-DZ3_BUILD_LIBZ3_SHARED=TRUE \
	-DZ3_BUILD_OCAML_BINDINGS=TRUE \
	--debug-trycompile \
	../

ml:
	mkdir -p build
	cd build && cmake \
	-G "Ninja" \
	-DCMAKE_VERBOSE_MAKEFILE=TRUE \
	-DZ3_BUILD_LIBZ3_SHARED=TRUE \
	-DZ3_BUILD_OCAML_BINDINGS=TRUE \
	-DZ3_BUILD_OCAML_EXTERNAL_LIBZ3=/home/ex/my_z3 \
	-DZ3_USE_LIB_GMP=TRUE \
	--debug-trycompile \
	../

# LD_LIBRARY_PATH=build ./build/src/api/ml/ml_example

build-all:
	cd build && make -j16

build-mk:
	cd build && make -j16 build_z3_ocaml_bindings
.PHONY:build

# /bin/sh: 1: ocamlfind ocamlc -where: not found
build:
	cd build && ninja build_z3_ocaml_bindings
.PHONY:build-nj

dot:
	cd build && dot -Tpng -o deps.png deps.dot

clean:
	rm -rf build

MKLIB_FLAGS = \
	ocamlfind ocamlmklib \
	-ocamlcflags -bin-annot \
	-package zarith \
	-lz3 -lstdc++ -lpthread\
	-lgmp \
	-L/home/ex/code/ocaml-build-examples/vendor/z3/build \
	-dllpath /home/ex/code/ocaml-build-examples/vendor/z3/build \
	-L/home/ex/.opam/5.1.1/lib/stublibs \
	-dllpath /home/ex/.opam/5.1.1/lib/stublibs \
	-I build/src/api/ml \
	-o build/src/api/ml/z3ml	

om:
	$(MKLIB_FLAGS) \
	build/src/api/ml/z3enums.cmo \
	build/src/api/ml/z3native.cmo \
	build/src/api/ml/z3native_stubs.o \
	build/src/api/ml/z3.cmo

	$(MKLIB_FLAGS) \
	build/src/api/ml/z3enums.cmx \
	build/src/api/ml/z3native.cmx \
	build/src/api/ml/z3native_stubs.o \
	build/src/api/ml/z3.cmx

# why?
# DEPENDS "${z3ml_bin}/z3enums.cmo"

or1:
	ocamlfind ocamlc -verbose \
	-o ml_example.byte \
	-package zarith \
	-I +threads \
	-I /home/ex/code/ocaml-build-examples/vendor/z3/build/src/api/ml \
	-dllpath /home/ex/code/ocaml-build-examples/vendor/z3/build/src/api/ml \
	-I /home/ex/.opam/5.1.1/lib/stublibs \
	-dllpath /home/ex/.opam/5.1.1/lib/stublibs \
	/home/ex/.opam/5.1.1/lib/zarith/zarith.cma \
	/home/ex/code/ocaml-build-examples/vendor/z3/build/src/api/ml/z3ml.cma \
	/home/ex/code/ocaml-build-examples/vendor/z3/build/src/api/ml/ml_example.ml \

# 	-linkpkg \

or2:
	ocamlrun ml_example.byte

# -I /home/ex/.opam/5.1.1/lib/stublibs \
    # "-cclib" "-L${PROJECT_BINARY_DIR}"
    # "-cclib" [[-L. -lpthread -lstdc++ -lz3]]
    # "-linkpkg"
# "-cclib" "-L${PROJECT_BINARY_DIR}"
# "-cclib" [[-L. -lpthread -lstdc++ -lz3]]
    

oc1:
	ocamlfind ocamlopt \
	-I +threads \
	-o ml_example \
	-package zarith \
	-linkpkg \
	-I /home/ex/code/ocaml-build-examples/vendor/z3/build/src/api/ml \
	z3ml.cmxa \
	/home/ex/code/ocaml-build-examples/vendor/z3/build/src/api/ml/ml_example.ml

oc2:
	./ml_example

# must have
# /home/ex/.opam/5.1.1/lib/zarith/zarith.cma 
# -I /home/ex/code/ocaml-build-examples/vendor/z3/build/src/api/ml

# can be removed
# -cclib "-lstdc++ -lz3"
# -cclib "-L. -L/home/ex/.opam/5.1.1/lib/stublibs -L/home/ex/.opam/5.1.1/lib/zarith "
# -L/home/ex/code/ocaml-build-examples/vendor/z3/build
# -package zarith
# -linkpkg
# -lpthread
# -package z3
# -I /home/ex/.opam/5.1.1/lib/zarith 

# must not have
# -custom

# -o /home/ex/code/ocaml-build-examples/vendor/z3/build/src/api/ml/ml_example.byte

# CAML_LD_LIBRARY_PATH=/home/ex/.opam/5.1.1/lib/stublibs:/home/ex/code/ocaml-build-examples/vendor/z3/build:/home/ex/code/ocaml-build-examples/vendor/z3/build/src/api/ml:/home/ex/.opam/5.1.1/lib/zarith

or3:
	ocamlrun -I /home/ex/.opam/5.1.1/lib/zarith -I /home/ex/.opam/5.1.1/lib/stublibs -I /home/ex/.opam/5.1.1/lib/zarith ml_example.byte

# -I /home/ex/.opam/5.1.1/lib/zarith 
# -I /home/ex/.opam/5.1.1/lib/stublibs
# -I /home/ex/code/ocaml-build-examples/vendor/z3/build
# -I /home/ex/code/ocaml-build-examples/vendor/z3/build/src/api/ml
# -t -b


# -cclib "-L. -lpthread -lstdc++ -lz3"

# set (cc_flags "\"-L. -lpthread -lstdc++ -lz3\"")
#"LD_LIBRARY_PATH=${PROJECT_BINARY_DIR}"

# Link libz3 into the python directory so bindings work out of the box
# add_custom_command(OUTPUT "${z3py_bindings_build_dest}/libz3${CMAKE_SHARED_MODULE_SUFFIX}"
#   COMMAND "${CMAKE_COMMAND}" "-E" "${LINK_COMMAND}"
#     "${PROJECT_BINARY_DIR}/libz3${CMAKE_SHARED_MODULE_SUFFIX}"
#     "${z3py_bindings_build_dest}/libz3${CMAKE_SHARED_MODULE_SUFFIX}"
#   DEPENDS libz3
#   COMMENT "Linking libz3 into python directory"
# )

# add_ocaml_library(z3ml
#   OCAML    z3enums z3native z3
#   # OCAMLDEP llvm
#   PKG      zarith
#   C        z3native_stubs
#   CFLAGS   "-I${Z3_C_API_PATH} -I${CMAKE_CURRENT_SOURCE_DIR} -I\$\(ocamlfind ocamlc -where\)"
#   GEN      "${OCAML_GENERATED_FILES}"
#   # -I${CMAKE_CURRENT_SOURCE_DIR}/../llvm
#   # LLVM     IRReader)
# )


# set(z3_c_api_path "${PROJECT_SOURCE_DIR}/src/api")
# target_sources(z3ml PRIVATE
#                 z3native_stubs.h
#                 ${z3_c_api_path})


# message(heads "--${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}")
# message(extra deps "--${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}")

# add_custom_target(z3natives_stubs.c DEPENDS "${Z3_OCAML_NATIVE_STUB_PRE_FILE}")
# target_sources(ocaml_z3 
#               PRIVATE ${Z3_OCAML_NATIVE_FILE} ${Z3_OCAML_NATIVE_STUB_FILE})

# target_include_directories(ocaml_z3
#     PUBLIC ${CMAKE_CURRENT_BINARY_DIR}
# )

# add_custom_target (LibCoreBC DEPENDS libcore.bc)

# target_sources(src/api/ml/z3natives_stubs.c
#                 PUBLIC Z3_OCAML_NATIVE_STUB_FILE)

# add_custom_target(${Z3_OCAML_NATIVE_STUB_FILE} DEPENDS 
#                  ${Z3_OCAML_NATIVE_STUB_PRE_FILE})

# target_precompile_headers(
#   ocaml_z3 PRIVATE
#   z3native_stubs.h
# )

# target_sources(ocaml_z3 PRIVATE
#                 "${PROJECT_SOURCE_DIR}/src/api/ml/z3native.ml"
#                 "${PROJECT_SOURCE_DIR}/src/api/ml/z3native_stubs.c")

# add_dependencies(ocaml_z3
#               "${PROJECT_SOURCE_DIR}/src/api"
#               "${PROJECT_BINARY_DIR}/src/api"
#             )

# find_package(OCaml)
# message("DDDebug ${OCAMLFIND}")
# message("DDDebug ${pkg}")
# find_ocamlfind_package(ctypes)
# # find_ocamlfind_package("nonexist")
# message(small " ${HAVE_OCAML_ctype}")
# message(caps " ${HAVE_OCAML_CTYPES}")
# message(small " ${OCAML_ctype_VERSION}")
# message(caps " ${OCAML_CTYPES_VERSION}")
# find_package(ocaml REQUIRED)

# add_custom_target(ocaml_post_z3enums DEPENDS
#   "${CMAKE_CURRENT_BINARY_DIR}/z3enums.ml"
#   "${CMAKE_CURRENT_BINARY_DIR}/z3enums.mli"
#   "${CMAKE_CURRENT_BINARY_DIR}/z3enums.cmo"
#   "${CMAKE_CURRENT_BINARY_DIR}/z3enums.cmx"
# )
# add_custom_target(z3.ml DEPENDS
#   ocaml_post_z3enums
# )
# add_custom_target(z3native.ml DEPENDS
#   ocaml_post_z3enums
# )
